Require Import Coq.Sets.Ensembles.
Require Import List.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    RuntimeModel
    Events.
Import ListNotations.

Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Local Open Scope map_scope.
(*
The top-level security condition compares traces involving both states (as
in "state" in RuntimeModel.v) and events. This file augments the semantics 
in RuntimeModel.v with rules that also produce labeled Events (in Events.v)
that represent values that are inputs/outputs to/from nodes. It also builds
traces that are sequences of pairs of states and events. In the future,
events will also represent downgrades of values. These events are abstract
objects that are used in the specification of the security condition.

The "input" event during the read is the one that is really strictly needed.
The model of a node does not contain any state corresponding to values.
So a purely state-based security condition would not say anything about values
that are read by a node.

I considered whether traces can be JUST sequences of events
rather than sequences of state/event pairs. I think the answer is no
because then it might be possible to leak information via
the handles a node has. (Even though the call of a node does not contain
informtion because the choice of call is always essentially non-deterministic,
so the call is a piece of state that probably does not matter at the moment)

 When downgrades events are added, a trace might need to be
 list (state * (Ensemble event))                  (Ensembles are sets)
 rather than
 list (state * event)
 since individual calls might produce more than one event. For example,
 when a read call does a declassification it would produce an input event
 and a downgrade event.
*)

Definition trace := list (state * event_l).

Declare Scope aug_scope.
Local Open Scope aug_scope.
Notation "n '--->' msg":= (EvL (OutEv msg) n.(nlbl)) (at level 10) : aug_scope.
Notation "n '<---' msg":= (EvL (InEv msg) n.(nlbl)) (at level 10) : aug_scope.
Notation "n '---'":= (EvL NilEv n.(nlbl)) (at level 10) : aug_scope.


Definition head_st (t: trace) :=
    match t with 
        | nil => None
        | (s', _)::_ => Some s'
    end.

Inductive step_node_ev (id: node_id): call -> state -> state -> event_l -> Prop :=
    | SWriteChanEv s n han msg s':
        s.(nodes) .[?id] = Some n ->
        step_node id (WriteChannel han msg) s s' ->
        step_node_ev id (WriteChannel han msg) s s' (n ---> msg)
    | SReadChanEv s n han chan msg s':
        s.(nodes) .[?id] = Some n ->
        step_node id (ReadChannel han) s s' ->
        msg_is_head chan msg ->
        step_node_ev id (ReadChannel han) s s' (n <--- msg)
    | SCreateChanEv s n lbl s':
            (* It seems clear that no event is needed since nodes only observe
            * contents of channels indirectly via reads *)
        s.(nodes) .[?id] = Some n ->
        step_node id (CreateChannel lbl) s s' ->
        step_node_ev id (CreateChannel lbl) s s' (n --- )
    | SCreateNodeEv s n lbl h s':
            (* model observation that a node is created ?? *)
        s.(nodes) .[?id] = Some n ->
        step_node id (CreateNode lbl h) s s' ->
        step_node_ev id (CreateNode lbl h) s s' (n ---)
    | SInternalEv s n s':
        s.(nodes) .[?id] = Some n ->
        step_node id Internal s s' ->
        step_node_ev id Internal s s' (n ---).


Definition trace_upd_head_state (t: trace) (s: state) :=
    match t with
        | nil => nil
        | (s', e) :: t' => (s, e) :: t'
    end.

Definition head_set_call t id c: trace :=
    match t with 
        | nil => nil (* this case never happens in the 
                context where this is used *)
        | (s, e) :: t' => (s_set_call s id c, e) :: t'
    end.

Inductive step_system_ev: state -> state -> event_l -> Prop :=
    | SytsemEvSkip s ell: step_system_ev s s (EvL NilEv ell)
    | SystemEvStepNode id n c c' s s' e:
        s.(nodes) .[?id] = Some n ->
        n.(ncall) = c ->
        step_node_ev id c s s' e ->
        let s'' := (s_set_call s' id c') in
            (* Here c' is an arbitrary command. The next ABI call
            that the node makes after the one executed here is an arbitrary one
            of that node's choosing *)
        step_system_ev s s'' e.

Inductive step_system_ev_t: trace -> trace -> Prop :=
    | StepTrace t s s' e:
        head_st t = Some s -> 
        step_system_ev s s' e ->
        step_system_ev_t t ((s', e) :: t).

Inductive step_system_ev_multi: trace -> trace -> Prop :=
    | multi_system_ev_refl t t':
        step_system_ev_t t t' ->
        step_system_ev_multi t t'
    | multi_system_ev_tran t1 t2 t3:
        step_system_ev_t t2 t3 ->
        step_system_ev_multi t1 t2 ->
        step_system_ev_multi t1 t3.


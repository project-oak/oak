Require Import Coq.Sets.Ensembles.
Require Import List.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    ModelSemUtils
    RuntimeModelPS
    State
    Events.
Import ListNotations.

Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Local Open Scope map_scope.
Local Open Scope ev_notation.

(*
This is a copy of EvAugSemantics for partially-secret labels.
This version uses RuntimeModelPS in place of RuntimeModel.
*)

(*
The top-level security condition compares traces involving both states (as
in "state" in RuntimeModelPS.v) and events. This file augments the semantics 
in RuntimeModelPS.v with rules that also produce labeled Events (in Events.v)
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

(* This is used for state/event pairs in EvAug. 
* The type is slightly awkward now post refactor *)
Definition head_st (t: trace) :=
    match t with 
        | nil => None
        | (s', _)::_ => Some s'
    end.

Inductive step_node_ev (id: node_id): call -> state -> state -> event_l -> Prop :=
    | SWriteChanEv s nlbl han msg s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (WriteChannel han msg) s s' ->
        step_node_ev id (WriteChannel han msg) s s' (nlbl ---> msg)
        (* The notations used for events on this last line and others
        is in Events.v *)
    | SReadChanEv s nlbl han chan msg s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (ReadChannel han) s s' ->
        msg_is_head chan msg ->
        step_node_ev id (ReadChannel han) s s' (nlbl <--- msg)
    | SCreateChanEv s nlbl clbl s':
        (* It seems clear that no event is needed since nodes only observe
        * contents of channels indirectly via reads *)
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (CreateChannel clbl) s s' ->
        step_node_ev id (CreateChannel clbl) s s' (nlbl --- )
    | SCreateNodeEv s nlbl new_lbl h s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (CreateNode new_lbl h) s s' ->
        step_node_ev id (CreateNode new_lbl h) s s' ( -- nlbl -- )
    | SWaitOnChannelsEv s hs nlbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (WaitOnChannels hs) s s' ->
        step_node_ev id (WaitOnChannels hs) s s' (nlbl ---)
    | SChannelCloseEv s han nlbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (ChannelClose han) s s' ->
        step_node_ev id (ChannelClose han) s s' (nlbl ---)
    | SNodeLabelReadEv s nlbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id NodeLabelRead s s' ->
        step_node_ev id NodeLabelRead s s' (nlbl <--L nlbl)
    | SChannelLabelReadEv s han nlbl clbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        (s.(chans) .[?han]).(lbl) = clbl ->
        step_node id (ChannelLabelRead han) s s' ->
        step_node_ev id (ChannelLabelRead han) s s' (nlbl <--L clbl)
    | SInternalEv s nlbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id Internal s s' ->
        step_node_ev id Internal s s' (nlbl ---).

Inductive step_system_ev: state -> state -> event_l -> Prop :=
    | SytsemEvSkip s ell: step_system_ev s s (ell ---) 
    | SystemEvStepNode id n c c' s s' e:
        (s.(nodes).[?id]).(obj) = Some n ->
        n.(ncall) = c ->
        step_node_ev id c s s' e ->
        let s'' := (s_set_call s' id c') in
            (* Here c' is an arbitrary command. The next ABI call
            that the node makes after the one executed here is an arbitrary one
            of that node's choosing *)
        step_system_ev s s'' e.

(* TODO
    Theorem that proves that step_system_ev is sound/complete for step_system.
    (* should be trivial ? *)

    The reason why there is more than one state transition relation is that the
    'events' are just an abstract concept meant to state the security theorems,
    so it seemed useful to keep them separate from the main specification of 
    behavior.

    Alternatively, we could just decide that actually including events in the
    main specification of behavior is just fine, and then we just replace
    step_sytem with step_system_ev.
*)

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


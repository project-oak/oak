Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    RuntimeModel
    Events.

Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.

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

Notation "s '[' id ']-->' msg":= (EvL (OutEv msg) (s.(nodes) id).(nlbl)) (at level 10).
Notation "s '[' id ']<--' msg":= (EvL (InEv msg) (s.(nodes) id).(nlbl)) (at level 10).
Notation "s '[' id ']_'":= (EvL NilEv (s.(nodes) id).(nlbl)) (at level 10).

Definition msg_is_head (ch: channel)(m: message): Prop :=
    match ch.(ms) with
        | [] => False
        | m' :: ms' => m' = m
    end. 

Inductive step_node_ev: node_id -> call -> state -> trace -> state -> trace -> Prop :=
    | SWriteChan s id han msg s' t:
        step_node id (WriteChannel han msg) s s' ->
        step_node_ev id (WriteChannel han msg) s t s' ((s', s [id]--> msg) :: t)
    | SReadChan s id han chan msg s' t:
        step_node id (ReadChannel han) s s' ->
        msg_is_head chan msg ->
        step_node_ev id (ReadChannel han) s t s' ((s', s [id]<-- msg) :: t)
    | SCreateChan s id lbl s' t:
            (* It seems clear that no event is needed since nodes only observe
            * contents of channels indirectly via reads *)
        step_node id (CreateChannel lbl) s s' ->
        step_node_ev id (CreateChannel lbl) s t s' ((s', s [id]_) :: t)
    | SCreateNode s id lbl h s' t:
            (* model observation that a node is created ?? *)
        step_node id (CreateNode lbl h) s s' ->
        step_node_ev id (CreateNode lbl h) s t s' ((s', s [id]_) :: t)
    | SInternal s id s' t:
        step_node id Internal s s' ->
        step_node_ev id Internal s t s' ((s', s [id]_) :: t).

Inductive step_system_ev: state -> trace -> state -> trace -> Prop :=
    | ValidStep id n c c' s t s' t':
        (s.(nodes) id) = n ->
        n.(ncall) = c ->
        step_node_ev id c s t s' t' ->
        step_system_ev s t (state_upd_call id c' s') t'.

Inductive step_system_ev_multi: state -> trace -> state -> trace -> Prop :=
    | multi_system_ev_refl s t s' t':
        step_system_ev s t s' t' ->
        step_system_ev_multi s t s' t'
    | multi_system_ev_tran s1 t1 s2 t2 s3 t3:
        step_system_ev s1 t1 s2 t2 ->
        step_system_ev_multi s2 t2 s3 t3 ->
        step_system_ev_multi s1 t1 s3 t3.

Require Import OakIFC.Lattice.
Require Import OakIFC.Parameters.
Require Import OakIFC.GenericMap.
Require Import List.
Import ListNotations.
Require Import RuntimeModel.
Require Import OakIFC.Events.
Require Import Coq.Sets.Ensembles.

Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.

Definition msg_is_head (ch: channel)(m: message): Prop :=
    match ch.(ms) with
        | [] => False
        | m' :: ms' => m' = m
    end. 

(* 
I considered whether traces can be JUST sequences of events
rather than sequences of state/event pairs. I think the answer is no
because then it might be possible to leak information via
the handles a node has.
(Even though the call of a node does not contain
informtion because the choice of call is always essentially non-deterministic)
*)

Inductive step_node_ev: node_id -> call -> state -> trace -> state -> trace -> Prop :=
    | SWriteChan s id han msg s' t ev
        (H0: step_node id (WriteChannel han msg) s s')
        (H1: ev = (EvL (OutEv msg) (s.(nodes) id).(nlbl))):
        step_node_ev id (WriteChannel han msg) s t s' ((s', ev) :: t)
    | SReadChan s id han chan msg s' t ev
        (H0: step_node id (ReadChannel han) s s')
        (H1: (msg_is_head chan msg))
        (H2: ev = (EvL (InEv msg) (s.(nodes) id).(nlbl))):
        step_node_ev id (ReadChannel han) s t s' ((s', ev) :: t)
    | SCreateChan s id lbl s' t ev
            (* It seems clear that no event is needed since nodes only observe
            * contents of channels indirectly via reads *)
        (H0: step_node id (CreateChannel lbl) s s')
        (H1: ev = (EvL NilEv (s.(nodes) id).(nlbl))):
        step_node_ev id (CreateChannel lbl) s t s' ((s', ev) :: t)
    | SCreateNode s id lbl h s' t ev
            (* model observation that a node is created ?? *)
        (H0: step_node id (CreateNode lbl h) s s')
        (H1: ev = (EvL NilEv (s.(nodes) id).(nlbl))):
        step_node_ev id (CreateNode lbl h) s t s' ((s', ev) :: t)
    | SInternal s id s' t ev
        (H0: step_node id Internal s s')
        (H1: ev = (EvL NilEv (s.(nodes) id).(nlbl))):
        step_node_ev id Internal s t s ((s', ev) :: t).

Inductive step_system_ev: state -> trace -> state -> trace -> Prop :=
    | ValidStep id n c c' s t s' t'
        (H0: (s.(nodes) id) = n)
        (H1: n.(ncall) = c)
        (H2: step_node_ev id c s t s' t'):
        step_system_ev s t (state_upd_call id c' s') t'.

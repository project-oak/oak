Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    RuntimeModel
    EvAugSemantics
    Events
    LowEquivalences
    NIUtilTheorems.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Local Open Scope map_scope.
(*============================================================================
 Unwinding Theorems
============================================================================*)
(*
This file contains theorems that prove "the unwinding condition" for 
various single pure functions. An unwinding condition is a single step of
noninterference.
*)

(*
It might be better to write them using something like this in the future:

Definition state_unwind (f: state -> state):
    forall ell s1 s2, 
        state_low_eq ell s1 s2 ->
        state_low_eq ell (f s1) (fs 2)

but we have to fix the way the definitions are curried.
*)

Theorem state_upd_node_unwind: forall ell id n1 n2 n1obj n2obj s1 s2,
    node_low_eq ell n1 n2 ->
    n1.(obj) = Some n1obj ->
    n2.(obj) = Some n2obj ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_node id n1obj s1) (state_upd_node id n2obj s2).
Proof.
Admitted. (* WIP // TODO *)

Theorem chan_append_unwind: forall ell ch1 ch2 ch1obj ch2obj msg,
    chan_low_eq ell ch1 ch2 ->
    ch1.(obj) = Some ch1obj ->
    ch2.(obj) = Some ch2obj ->
    chan_low_eq ell 
        (ch1 <| obj := Some (chan_append ch1obj msg) |>)
        (ch2 <| obj := Some (chan_append ch2obj msg) |>).
Proof.
Admitted. (* WIP // TODO *)

Theorem state_upd_chan_unwind: forall ell han ch1 ch2 ch1obj ch2obj s1 s2,
    chan_low_eq ell ch1 ch2 ->
    ch1.(obj) = Some ch1obj ->
    ch2.(obj) = Some ch2obj ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_chan han ch1obj s1) (state_upd_chan han ch2obj s2).
Proof.
Admitted.

Theorem state_upd_node_labeled_unwind: forall ell id n1 n2 s1 s2,
    node_low_eq ell n1 n2 ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_node_labeled id n1 s1) (state_upd_node_labeled id n2 s2).
Proof.
Admitted.

Theorem state_upd_chan_labeled_unwind: forall ell id ch1 ch2 s1 s2,
    chan_low_eq ell ch1 ch2 ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_chan_labeled id ch1 s1) (state_upd_chan_labeled id ch2 s2).
Proof.
Admitted.

Theorem set_call_unwind: forall ell id c s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_eq ell (s_set_call s1 id c) (s_set_call s2 id c).
Proof.
    intros. inversion H; subst.
    unfold s_set_call.
    destruct (s1.(nodes).[? id]) eqn:E1; destruct (s2.(nodes).[? id]) eqn:E2.
Admitted.

Hint Resolve state_upd_chan_unwind chan_append_unwind
                set_call_unwind state_upd_node_unwind
                state_upd_chan_labeled_unwind
                state_upd_node_labeled_unwind
                labeled_low_proj_loweq : unwind.

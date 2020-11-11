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
    Tactics
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
Theorem state_upd_node_unwind : forall ell id n s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_node id n s1) (state_upd_node id n s2).
Proof.
    destruct s1, s2; intros *.
    inversion 1; subst.
    cbv [state_upd_node state_low_eq state_low_proj set] in *.
    cbn [RuntimeModel.nodes RuntimeModel.chans] in *.
    split; try congruence; intros.
    destruct (dec_eq_nid id nid).
    - rewrite e in *. specialize (H0 nid).
    cbv [node_state_low_proj low_proj fnd RuntimeModel.lbl RuntimeModel.obj] in *.
    simpl in *. erewrite upd_eq. erewrite upd_eq.
    destruct (nodes nid), (nodes0 nid).
    pose proof (top_is_top ell).
    pose proof (top_is_top lbl).
    pose proof (top_is_top lbl0).
    destruct (lbl <<? ell), (lbl0 <<? ell); try congruence.
    all:
    inversion H0; subst;
    pose proof (ord_anti ell top ltac:(eauto) ltac:(eauto));
    congruence.
    - specialize (H0 nid).
    cbv [node_state_low_proj low_proj fnd RuntimeModel.lbl 
        RuntimeModel.obj] in *.
    simpl in *. erewrite upd_neq; auto. erewrite upd_neq; auto.
Qed.

Theorem chan_append_unwind: forall ell ch1 ch2 ch1obj ch2obj msg,
    chan_low_eq ell ch1 ch2 ->
    ch1.(obj) = Some ch1obj ->
    ch2.(obj) = Some ch2obj ->
    chan_low_eq ell 
        (ch1 <| obj := Some (chan_append ch1obj msg) |>)
        (ch2 <| obj := Some (chan_append ch2obj msg) |>).
Proof.
Admitted. (* WIP // TODO *)

Theorem state_upd_chan_unwind: forall ell han ch s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_chan han ch s1) (state_upd_chan han ch s2).
Proof.
Admitted.

Theorem state_upd_node_labeled_unwind: forall ell id n1 n2 s1 s2,
    node_low_eq ell n1 n2 ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_node_labeled id n1 s1) (state_upd_node_labeled id n2 s2).
Proof.
Admitted.

Theorem state_upd_chan_labeled_unwind: forall ell h ch1 ch2 s1 s2,
    chan_low_eq ell ch1 ch2 ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_chan_labeled h ch1 s1) (state_upd_chan_labeled h ch2 s2).
Proof.
Admitted.

Theorem state_chan_append_labeled_unwind: forall ell han msg s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_eq ell 
        (state_chan_append_labeled han msg s1)
        (state_chan_append_labeled han msg s2).
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

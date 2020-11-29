Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    State
    Events
    ModelSemUtils
    LowEquivalences
    NIUtilTheorems
    Tactics
    Unfold.
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
    cbn [State.nodes State.chans] in *.
    split; try congruence; intros.
    destruct (dec_eq_nid id nid).
    - rewrite e in *. specialize (H0 nid).
    cbv [node_state_low_proj low_proj fnd State.lbl State.obj] in *.
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
    cbv [node_state_low_proj low_proj fnd State.lbl 
        State.obj] in *.
    simpl in *. erewrite upd_neq; auto. erewrite upd_neq; auto.
Qed.

Ltac label_cases :=
    match goal with
        | l1: level, l2: level, ell: level |- _ =>
            (* l1 not found in environment here ?? *)
            (* (if l1 <<? ell then _ else _) = 
            (if l2 <<? ell then _ else _) => *)
            destruct (l1 <<? ell), (l2 <<? ell)
    end.

Ltac unwind_crush_step2 :=
    lazymatch goal with
        | H: {| obj := _; lbl := _ |} = _ |- _ => inversion H; subst
        | H: Some _ = Some _ |- _ => inversion H
        | _ => idtac
    end.

Ltac unwind_crush :=
    repeat match goal with
        (* | _ => progress label_cases *) (* this causes coq to get stuck *)
        | _ => progress unwind_crush_step2
    end.

Theorem chan_append_unwind: forall ell ch1 ch2 ch1obj ch2obj msg,
    chan_low_eq ell ch1 ch2 ->
    ch1.(obj) = Some ch1obj ->
    ch2.(obj) = Some ch2obj ->
    chan_low_eq ell 
        (ch1 <| obj := Some (chan_append ch1obj msg) |>)
        (ch2 <| obj := Some (chan_append ch2obj msg) |>).
Proof.
    autounfold with loweq; autounfold with semutils; 
    autounfold with structs. simpl. intros.
    destruct ch1, ch2. 
    destruct (lbl <<? ell); destruct (lbl0 <<? ell).
    all: unwind_crush.
    all: congruence.
Qed.

Theorem chan_state_proj_index_assoc: forall ell cs han,
    (chan_state_low_proj ell cs) han = low_proj ell (cs han).
Proof.
    autounfold with loweq. auto.
Qed.

Theorem state_upd_chan_unwind: forall ell han ch s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_chan han ch s1) (state_upd_chan han ch s2).
Proof.
    unfold state_low_eq, state_upd_chan, fnd.
    intros; split; logical_simplify.
    - auto.
    -  cbv [RecordSet.set] in *. destruct s1, s2. cbv [State.chans] in *.
    simpl. intros. do 2 rewrite chan_state_proj_index_assoc. simpl in *.
    destruct (dec_eq_h han0 han). 
        *  (* = *)
        subst. do 2 erewrite upd_eq. eauto.
        specialize (H0 han). autounfold with loweq in *.
        destruct (chans han), (chans0 han). simpl in *. 
        destruct (lbl <<? ell), (lbl0 <<? ell).
        all: unwind_crush; congruence.
        * (* <> *)
        subst. erewrite upd_neq. erewrite upd_neq.
        all: eauto. 
Qed.

Theorem node_state_proj_index_assoc: forall ell ns id,
    (node_state_low_proj ell ns) id = low_proj ell (ns id).
Proof.
    autounfold with loweq. auto.
Qed.

Theorem state_upd_node_labeled_unwind: forall ell id n1 n2 s1 s2,
    node_low_eq ell n1 n2 ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_node_labeled id n1 s1) (state_upd_node_labeled id n2 s2).
Proof.
    unfold state_low_eq, state_upd_node_labeled.
    intros; split; logical_simplify.
    Focus 2. auto.
    destruct s1, s2. cbv [RecordSet.set State.nodes] in *. simpl.
    intros. do 2 rewrite node_state_proj_index_assoc.
    destruct (dec_eq_nid id nid). 
        * (* = *)
            subst. do 2 erewrite upd_eq. eauto. 
        * (* <> *)
            erewrite upd_neq. erewrite upd_neq. all: eauto.
            apply H0.
Qed.

Theorem state_upd_chan_labeled_unwind: forall ell h ch1 ch2 s1 s2,
    chan_low_eq ell ch1 ch2 ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_chan_labeled h ch1 s1) (state_upd_chan_labeled h ch2 s2).
Proof.
    unfold state_low_eq, state_upd_chan_labeled.
    intros; split; logical_simplify. auto.
    destruct s1, s2. cbv [RecordSet.set State.chans] in *. simpl.
    intros. do 2 rewrite chan_state_proj_index_assoc.
    destruct (dec_eq_h h han). 
        * (* = *)
        subst. do 2 erewrite upd_eq. eauto.
        * (* <> *)
        erewrite upd_neq. erewrite upd_neq. all: eauto.
        apply H1.
Qed.


Theorem state_chan_append_labeled_unwind: forall ell han msg s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_eq ell 
        (state_chan_append_labeled han msg s1)
        (state_chan_append_labeled han msg s2).
Proof.
    unfold state_low_eq, state_chan_append_labeled, chan_append_labeled, fnd.
    intros; split; logical_simplify.
    - auto.
    -  cbv [RecordSet.set] in *. destruct s1, s2. cbv [State.chans] in *.
    simpl. intros. do 2 rewrite chan_state_proj_index_assoc. simpl in *.
    destruct (dec_eq_h han0 han). 
        *  (* = *)
        subst. do 2 erewrite upd_eq. eauto.
        specialize (H0 han). autounfold with loweq in *.
        destruct (chans han), (chans0 han). simpl in *. 
        destruct (lbl <<? ell), (lbl0 <<? ell) eqn:E.
        all: unwind_crush. 
        all: try congruence.
        (* not sure what happened here ...*)
        destruct obj; destruct obj0; (rewrite E; auto).
    * (* <> *)
    subst. erewrite upd_neq. erewrite upd_neq.
    all: eauto. 
Qed.

Theorem set_call_unwind: forall ell id c s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_eq ell (s_set_call s1 id c) (s_set_call s2 id c).
Proof.
    unfold s_set_call, fnd. 
Admitted.

Hint Resolve state_upd_chan_unwind chan_append_unwind chan_low_proj_loweq
    chan_low_proj_idempotent state_upd_node_unwind set_call_unwind
    state_upd_chan_unwind state_low_proj_loweq state_upd_chan_labeled_unwind
    state_upd_node_labeled_unwind state_chan_append_labeled_unwind
    labeled_low_proj_loweq: unwind.
Hint Extern 4 (node_low_eq _ _ _) => reflexivity : unwind.
Hint Extern 4 (chan_low_eq _ _ _) => reflexivity : unwind.
(* meant to be case where we have (cleq ch (proj ch) ) and want to swap order *)
Hint Extern 4 (chan_low_eq _ _ (chan_low_proj _ _)) => symmetry : unwind.
Hint Extern 4 (state_low_eq _ _ (state_low_proj _ _)) => symmetry : unwind.
Hint Extern 2 (chan_low_proj _ _ = chan_low_proj _ _)
=> simple eapply chan_low_proj_loweq : unwind.

Hint Resolve state_upd_chan_unwind chan_append_unwind
                set_call_unwind state_upd_node_unwind
                state_upd_chan_labeled_unwind
                state_upd_node_labeled_unwind
                labeled_low_proj_loweq : unwind.

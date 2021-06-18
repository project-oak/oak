Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    State
    Events
    ModelSemUtils
    LowEqPS
    Unfold
    LowProjPS_Thms
    Tactics.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Local Open Scope map_scope.

Hint Unfold state_low_eq chan_state_low_eq node_state_low_eq event_low_eq
    chan_low_eq node_low_eq low_eq state_low_proj chan_state_low_proj
    node_state_low_proj event_low_proj chan_low_proj node_low_proj
    low_proj: loweq.

(*
This is a copy of Unwind but for partially-secret labels.
This version is largely similar to Unwind, but requires an additional
corollary top_is_top_co to prove state_upd_chan_unwind and
state_chan_append_labeled_unwind.
*)

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
    unwind_crush.
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
        unwind_crush.
        (* TODO(mcswiggen): Make this part more concise *)
        { apply top_is_top_co in o. rewrite -> o in n.
        destruct n. apply top_is_top. }
        { apply top_is_top_co in o. rewrite -> o in n.
        destruct n. apply top_is_top. }
        * (* <> *)
        subst. erewrite upd_neq. erewrite upd_neq.
        all: eauto. 
Qed.

Theorem state_upd_node_labeled_unwind: forall ell id n1 n2 s1 s2,
    node_low_eq ell n1 n2 ->
    state_low_eq ell s1 s2 ->
    state_low_eq ell (state_upd_node_labeled id n1 s1) (state_upd_node_labeled id n2 s2).
Proof.
    unfold state_low_eq, state_upd_node_labeled.
    intros; split; logical_simplify.
    2: { auto. }
    destruct s1, s2. cbv [RecordSet.set State.nodes] in *. simpl.
    intros. do 2 rewrite node_state_proj_index_assoc.
    destruct (dec_eq_nid id nid). 
        * (* = *)
            subst. do 2 erewrite upd_eq. eauto. 
        * (* <> *)
            erewrite !upd_neq. all: eauto.
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
        erewrite !upd_neq. all: eauto.
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
    destruct (dec_eq_h han0 han); 
        [ | (* <> *) subst; erewrite !upd_neq by eauto; eauto ].
        *  (* = *)
        subst. do 2 erewrite upd_eq. eauto.
        specialize (H0 han). autounfold with loweq in *.
        destruct (chans han), (chans0 han). simpl in *.
        (* just using unwind_crush here doesn't work *)
        destruct (lbl <<? ell), (lbl0 <<? ell) eqn:E.
        all: unwind_crush.
        (* TODO(mcswiggen): Make this part more concise *)
        { clear E. apply top_is_top_co in o. rewrite -> o in n.
        destruct n. apply top_is_top. }
        { clear E. apply top_is_top_co in o. rewrite -> o in n.
        destruct n. apply top_is_top. }
        {
            destruct obj; destruct obj0; (rewrite E; auto);
            destruct (ord_dec lbl ell).
            all:auto. all:congruence.
        }
Qed.

Theorem set_call_none_is_nop: forall s id c,
    obj ((nodes s) id) = None ->
    s_set_call s id c = s.
Proof.
    autounfold with semutils. unfold fnd. intros.
    rewrite H. congruence.
Qed.

Theorem set_call_unwind: forall ell id c s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_eq ell (s_set_call s1 id c) (s_set_call s2 id c).
Proof.
    unfold s_set_call, fnd. intros.
    pose proof (state_low_eq_implies_node_lookup_eq _ _ _
        ltac:(eauto) ltac:(eauto)).
    unfold fnd in *.
    erewrite !node_state_proj_index_assoc_form2 in *.
    destruct (lbl (nodes s1 id) <<? ell) eqn:E,
        (lbl (nodes s2 id) <<? ell) eqn:E1.
    - destruct (nodes s1 id), (nodes s2 id). simpl in *. 
    rewrite E in H0. rewrite E1 in H0. inversion H0.
    destruct obj; eauto using state_upd_node_unwind.
    - destruct (obj (nodes s2 id)). 
    remember (n0 <| ncall ::= (fun _ : call => c) |>) as n0'.
    pose proof (state_upd_node_unobs _ _ _ ltac:(eauto) ltac:(eauto)).
    destruct (nodes s1 id), (nodes s2 id). simpl in *.
    rewrite E in H0. rewrite E1 in H0. inversion H0.
    eapply (state_low_eq_trans _ s1 s2 (state_upd_node id n0' s2)); eauto.
    destruct (nodes s1 id), (nodes s2 id). simpl in *.
    rewrite E in H0. rewrite E1 in H0. inversion H0. eauto.
    - destruct (obj (nodes s1 id)). 
    remember (n0 <| ncall ::= (fun _ : call => c) |>) as n0'.
    pose proof (state_upd_node_unobs _ _ _ ltac:(eauto) ltac:(eauto)).
    destruct (nodes s1 id), (nodes s2 id). simpl in *.
    rewrite E in H0. rewrite E1 in H0. inversion H0.
    symmetry in H1.
    eapply (state_low_eq_trans _ (state_upd_node id n0' s1) s1 s2); eauto.
    destruct (nodes s1 id), (nodes s2 id). simpl in *.
    rewrite E in H0. rewrite E1 in H0. inversion H0. eauto.
    - destruct (obj (nodes s2 id)), (obj (nodes s1 id)).
    (* both some *)
    remember (n1 <| ncall ::= (fun _ : call => c) |>) as n1'.
    remember (n2 <| ncall ::= (fun _ : call => c) |>) as n2'.
    pose proof (state_upd_node_unobs _ s2 _ n1' ltac:(eauto)).
    pose proof (state_upd_node_unobs _ s1 _ n2' ltac:(eauto)).
    symmetry in H2.
    eapply (state_low_eq_trans ell
        (state_upd_node id n2' s1) s1 (state_upd_node id n1' s2)); eauto.
    eapply (state_low_eq_trans ell s1 s2 (state_upd_node id n1' s2)); eauto.
    (* s2 is some*)
    remember (n1 <| ncall ::= (fun _ : call => c) |>) as n1'.
    pose proof (state_upd_node_unobs _ _ _ ltac:(eauto) ltac:(eauto)).
    eapply (state_low_eq_trans _ s1 s2 (state_upd_node id n1' s2)); eauto.
    (* s1 is some *)
    remember (n1 <| ncall ::= (fun _ : call => c) |>) as n1'.
    pose proof (state_upd_node_unobs _ s1 _ n1' ltac:(eauto)).
    symmetry in H1.
    eapply (state_low_eq_trans _ (state_upd_node id n1' s1) s1 s2); eauto.
    eauto.
Qed.

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

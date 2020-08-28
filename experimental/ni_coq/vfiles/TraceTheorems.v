Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    RuntimeModel
    Parameters
    Events
    EvAugSemantics.

(* In this file 'Theorem's are used in PossibilisticNI.v whereas
   'Lemmas' are just used to prove Theorems or other Lemmas in this file
*)

(* Note: How can this be done more elegantly, or skipped? *)
Theorem nil_cons_rev: forall {A : Type} (x : A) (l : list A), x :: l <> [].
Proof.
    unfold not. intros. symmetry in H. generalize dependent H.
    apply nil_cons.
Qed.

Theorem t_upd_mono_nil: forall t s,
    ~(t = nil) -> ~((trace_upd_head_state t s) = nil).
Proof.
    intros.
    unfold trace_upd_head_state. destruct t. assumption.
    replace (let (_, e) := p in (s, e) :: t) with
        ((let (_, e) := p in (s, e)) :: t).
    apply nil_cons_rev.
    destruct p. reflexivity.
Qed.

Theorem no_steps_to_empty: forall t, 
    ~(step_system_ev_multi t []).
    unfold not. intros.
    remember ([]: trace) as emp eqn:R.
    induction H; subst.
        - (* refl *) inversion H; subst. destruct t'.
            + inversion H2. 
            + apply t_upd_mono_nil in H0. assumption.
            unfold not. intros. generalize dependent H4. apply nil_cons_rev.
        - apply IHstep_system_ev_multi. reflexivity.
Qed.

Theorem step_system_transitive: forall t1 t2 t3,
    step_system_ev_multi t1 t2 ->
    step_system_ev_multi t2 t3 ->
    step_system_ev_multi t1 t3.
Proof.
    intros.
    induction H.
        - apply (multi_system_ev_tran t t' t3); assumption.
        - apply IHstep_system_ev_multi in H0.
        apply (multi_system_ev_tran t1 t2 t3); assumption.
Qed.


Lemma trace_upd_head_preserves_tail: forall t t' a s,
    trace_upd_head_state t s = a :: t' ->
    exists a', t = a' :: t'.
Proof.
    intros. destruct t.
    - inversion H.
    - destruct t'. simpl in H. destruct p. inversion H. subst.
    exists (s0, e). reflexivity.
    - unfold trace_upd_head_state in H. destruct p. inversion H.
    subst. exists (s0, e). reflexivity.
Qed.

Lemma no_node_steps_end_in_one: forall t t' id c,
    length t' = 1 ->
    ~(step_node_ev id c t t').
Proof.
    unfold not. intros. destruct t.
    - inversion H0; inversion H1.
    - inversion H0; subst; inversion H.
Qed.

Lemma state_upd_node_preserves_len: forall t t' s,
    trace_upd_head_state t s = t' ->
    length t = length t'.
Proof.
    intros; destruct t; destruct t'.
    - reflexivity.
    - inversion H.
    - inversion H. destruct p. inversion H1.
    - inversion H. destruct p. inversion H1. subst. reflexivity. 
Qed.

Lemma no_steps_end_in_one: forall t t',
    length t' = 1 ->
    ~ step_system_ev t t'.
Proof.
    intros. unfold not. intros.
    destruct t.
    - inversion H0. inversion H1.
    - destruct t'.
        + inversion H.
        + inversion H. assert (E: t' = []). {
            destruct t'. reflexivity.
            inversion H2.
        }
        inversion H0.
        assert (E1: length t'0 = 1). {
            assert (E': length t'0 = length (p0 :: t'))
                by apply (state_upd_node_preserves_len _ _ _ H1).
            rewrite H in E'. assumption.
        }
        apply (no_node_steps_end_in_one (p::t) t'0 id c E1 H8).
Qed.

Lemma step_system_extends: forall t t' a,
    step_system_ev t (a::t') ->
    step_system_ev t' (a::t').
Proof.
    intros.
    induction t'.
    - exfalso. apply (no_steps_end_in_one t [a]). trivial. assumption.
    - assert (E: t = a0::t'). {
        inversion H; subst.
        assert (E1: exists a', t'0 = a' :: a0 :: t') by
            apply (trace_upd_head_preserves_tail _ _ _ _ H0).
        destruct E1. rewrite H4 in H6.
        inversion H6; subst; reflexivity.
    }
    rewrite E in H. assumption.
Qed.

Theorem step_system_multi_extends: forall t t' a,
    step_system_ev_multi t (a :: t') ->
    step_system_ev t' (a :: t').
Proof.
    intros. remember (a::t') as t1 eqn:Ht1.
    induction H; subst.
        - apply (step_system_extends t t' a); assumption.
        - apply IHstep_system_ev_multi. reflexivity.
Qed.

Theorem step_ev_adds_one: forall t t',
    step_system_ev t t' ->
    exists a, t' = a::t.
Proof.
Admitted. (* WIP *)

Theorem step_system_multi_backwards: forall t t' a,
    step_system_ev_multi t (a :: t') ->
    step_system_ev_multi t t'.
Proof.
Admitted. (* WIP *)



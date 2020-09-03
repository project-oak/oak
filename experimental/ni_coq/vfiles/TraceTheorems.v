Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    RuntimeModel
    Parameters
    Events
    EvAugSemantics.

Theorem nil_cons_rev: forall {A : Type} (x : A) (l : list A), x :: l <> [].
Proof.
    unfold not. intros. inversion H.
Qed.

Lemma head_set_call_preserves_len: forall t t' id c,
    head_set_call t id c = t' ->
    length t = length t'.
Proof.
    intros; destruct t; destruct t'.
    - reflexivity.
    - inversion H.
    - inversion H. destruct p. inversion H1.
    - inversion H. destruct p. inversion H1. subst. reflexivity.
Qed. 

Theorem head_set_call_not_nil: forall t id c,
    t <> nil -> (head_set_call t id c) <> nil.
Proof.
    intros. unfold head_set_call. unfold s_set_call.
    destruct t. assumption.
    destruct p. destruct (finmap.fnd (finmap.ffun_of_fmap (nodes s)) id);
    apply nil_cons_rev.
Qed.

Lemma head_set_call_preserves_tail: forall t id c,
    tl (head_set_call t id c) = tl t.
Proof.
    intros; destruct t; (reflexivity || destruct p; reflexivity).
Qed.

Theorem no_steps_from_empty: forall t,
    ~(step_system_ev [] t).
Proof.
Admitted. (* WIP *)

Theorem node_no_steps_to_empty: forall t id c,
    ~(step_node_ev id c t []).
Proof.
    unfold not. intros. inversion H.
Qed.

Theorem no_steps_to_empty: forall t, 
    ~(step_system_ev_multi t []).
    unfold not. intros.
    remember ([]: trace) as emp eqn:R.
    induction H; subst.
        - (* refl *) inversion H; subst. destruct t'.
            + inversion H2. 
            + apply head_set_call_not_nil in H0. assumption.
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

Lemma no_node_steps_end_in_one: forall t t' id c,
    length t' = 1 ->
    ~(step_node_ev id c t t').
Proof.
    unfold not. intros. destruct t.
    - inversion H0; inversion H1.
    - inversion H0; subst; inversion H.
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
                by apply (head_set_call_preserves_len _ _ _ _ H1).
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
        specialize (head_set_call_preserves_tail t'0 id c') as E.
        rewrite H0 in E. inversion E.
        inversion H6; subst; simpl in E; congruence.
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

Theorem step_system_multi_backwards: forall t t' a,
    step_system_ev_multi t (a :: t') ->
    step_system_ev_multi t t'.
Proof.
Admitted. (* WIP *)



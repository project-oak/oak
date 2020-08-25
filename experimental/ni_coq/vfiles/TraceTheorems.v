Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
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

Lemma step_system_extends: forall t t' a,
    step_system_ev t (a::t') ->
    step_system_ev t' (a::t').
Proof.
Admitted.

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



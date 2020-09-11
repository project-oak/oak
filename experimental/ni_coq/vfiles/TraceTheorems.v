Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    RuntimeModel
    Parameters
    Events
    EvAugSemantics.

(* inner loop of destruct_match *)
Local Ltac destruct_match' e :=
  lazymatch e with
  | context [match ?x with _ => _ end] => destruct_match' x
  | _ => destruct e
  end.
(* Finds the first match it encounters in the goal and destructs the
   most deeply-nested match within it. *)
Local Ltac destruct_match :=
  match goal with
  | |- context [match ?x with _ => _ end] => destruct_match' x
  | H : context [match ?x with _ => _ end] |- _ => destruct_match' x
  end.

(* Runs [inversion] and then clears the original hypothesis, and runs
   [subst], in order to prevent cluttering the context.*)
Ltac invert_clean H :=
  progress (inversion H; clear H); subst.

(* Single step of [crush] *)
Local Ltac crush_step :=
  first [ progress intros
        | progress subst
        | progress cbn [length tl] in *
        | match goal with
          | H : head_st [] = Some _ |- _ =>
            solve [inversion H]
          | H : head_st (_ :: _) = Some _ |- _ =>
            invert_clean H
          | H : _ :: _ = _ :: _ |- _ =>
            invert_clean H
          end
        | congruence
        | destruct_match ].
(* General-purpose tactic that simplifies and solves simple goals. *)
Local Ltac crush := repeat crush_step.

Lemma head_set_call_preserves_len: forall t t' id c,
    head_set_call t id c = t' ->
    length t = length t'.
Proof. cbv [head_set_call]. crush. Qed.

Theorem head_set_call_not_nil: forall t id c,
    t <> nil -> (head_set_call t id c) <> nil.
Proof. cbv [head_set_call]. crush. Qed.

Lemma head_set_call_preserves_tail: forall t id c,
    tl (head_set_call t id c) = tl t.
Proof. cbv [head_set_call]. crush. Qed.

Theorem no_steps_from_empty: forall t,
    ~(step_system_ev [] t).
Proof.
Admitted. (* WIP *)

Theorem node_no_steps_to_empty: forall t id c,
    ~(step_node_ev id c t []).
Proof. inversion 1. Qed.

Lemma system_no_steps_to_empty: forall t,
    ~(step_system_ev t []).
Proof.
  inversion 1; cbv [head_set_call] in *. crush.
Qed.

Theorem no_steps_to_empty: forall t, 
    ~(step_system_ev_multi t []).
Proof.
  inversion 1; subst; eapply system_no_steps_to_empty; eauto.
Qed.

Theorem step_system_transitive: forall t1 t2 t3,
    step_system_ev_multi t1 t2 ->
    step_system_ev_multi t2 t3 ->
    step_system_ev_multi t1 t3.
Proof.
    induction 2; eauto using multi_system_ev_tran.
Qed.

Lemma no_node_steps_end_in_one: forall t t' id c,
    length t' = 1 ->
    ~(step_node_ev id c t t').
Proof.
  destruct t' as [| ? [| ? ? ] ]; crush; [ ].
  inversion 1; crush.
Qed.

Lemma no_steps_end_in_one: forall t t',
    length t' = 1 ->
    ~ step_system_ev t t'.
Proof.
  intros; inversion 1; subst.
  cbv [head_set_call] in *. crush.
  eapply no_node_steps_end_in_one; eauto; [ ].
  cbn [length]. congruence.
Qed.

Theorem step_system_ev_uncons: forall t1 t2,
    step_system_ev t1 t2 ->
    t1 = tl t2.
Proof.
  induction 1; intros; subst.
  let H := lazymatch goal with H : step_node_ev _ _ _ _ |- _ => H end in
  inversion H; subst; reflexivity.
Qed.

Lemma step_system_extends: forall t t' a,
    step_system_ev t (a::t') ->
    step_system_ev t' (a::t').
Proof.
  intros *. intro Hstep. pose proof Hstep.
  eapply step_system_ev_uncons in Hstep; crush.
Qed.

Theorem step_system_multi_extends: forall t t',
    step_system_ev_multi t t' ->
    step_system_ev (tl t') t'.
Proof.
  inversion 1; intros; subst;
    erewrite <-step_system_ev_uncons; eauto.
Qed.

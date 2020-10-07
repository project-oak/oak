Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    RuntimeModel
    Parameters
    Tactics
    Events
    EvAugSemantics.

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

Theorem no_steps_from_empty: forall t,
    ~(step_system_ev_t [] t).
Proof. inversion 1; crush. Qed.

(* This vestige is kept for now
* because it was referenced in the old P..NI.v *)
(*
Theorem node_no_steps_to_empty: forall t id c,
    ~(step_node_ev id c t []).
Proof. inversion 1. Qed.
*)

Lemma system_no_steps_to_empty: forall t,
    ~(step_system_ev_t t []).
Proof. inversion 1. Qed.

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

Lemma no_steps_end_in_one: forall t t',
    length t' = 1 ->
    ~ step_system_ev_t t t'.
Proof.
  intros; inversion 1; subst.
  destruct t. inversion H1. inversion H.
Qed.

Theorem step_system_ev_uncons: forall t1 t2,
    step_system_ev_t t1 t2 ->
    t1 = tl t2.
Proof.
    induction 1; intros; subst. auto.
Qed.

Lemma step_system_extends: forall t t' a,
    step_system_ev_t t (a::t') ->
    step_system_ev_t t' (a::t').
Proof.
  intros *. intro Hstep. pose proof Hstep.
  eapply step_system_ev_uncons in Hstep; crush.
Qed.

Theorem step_system_multi_extends: forall t t',
    step_system_ev_multi t t' ->
    step_system_ev_t (tl t') t'.
Proof.
  inversion 1; intros; subst;
    erewrite <-step_system_ev_uncons; eauto.
Qed.

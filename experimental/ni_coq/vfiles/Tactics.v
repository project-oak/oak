Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    State
    Events
    RuntimeModel
    RuntimeModelPS
    EvAugSemantics
    EvAugSemanticsPS.

(** Generically useful tactics **)

(* inner loop of destruct_match *)
Ltac destruct_match' e :=
  lazymatch e with
  | context [match ?x with _ => _ end] => destruct_match' x
  | _ => destruct e
  end.
(* Finds the first match it encounters in the goal and destructs the
   most deeply-nested match within it. *)
Ltac destruct_match :=
  match goal with
  | |- context [match ?x with _ => _ end] => destruct_match' x
  | H : context [match ?x with _ => _ end] |- _ => destruct_match' x
  end.

(* Runs [inversion] and then clears the original hypothesis, and runs
   [subst], in order to prevent cluttering the context.*)
Ltac invert_clean H := progress (inversion H; clear H); subst.

Ltac logical_simplify :=
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : exists _, _ |- _ => destruct H
         | H1 : ?P, H2 : ?P -> _ |- _ =>
           (* only proceed if P is a Prop; if H1 is a nat, for instance, P
              would be a Type, and we don't want to specialize foralls. *)
           match type of P with Prop => idtac end;
           specialize (H2 H1)
         | H : ?x = ?x |- _ => clear H
         end.

Ltac step_econstruct :=
    repeat match goal with
        | H: _ = ncall _ |- _ => progress rewrite <- H
    end;
    lazymatch goal with
        | |- EvAugSemantics.step_system_ev _ _ _ => econstructor; eauto
        | |- EvAugSemantics.step_node_ev _ _ _ _ _  => econstructor; eauto
        | |- RuntimeModel.step_system _ _ => econstructor; eauto
        | |- RuntimeModel.step_node _ _ _ _ => econstructor; eauto
    end.

Ltac step_econstruct_PS :=
    repeat match goal with
        | H: _ = ncall _ |- _ => progress rewrite <- H
    end;
    lazymatch goal with
        | |- EvAugSemanticsPS.step_system_ev _ _ _ => econstructor; eauto
        | |- EvAugSemanticsPS.step_node_ev _ _ _ _ _  => econstructor; eauto
        | |- RuntimeModelPS.step_system _ _ => econstructor; eauto
        | |- RuntimeModelPS.step_node _ _ _ _ => econstructor; eauto
    end.

(* Single step of [crush] *)
Ltac crush_step :=
  repeat match goal with
         | _ => progress intros
         | _ => progress subst
         | _ => progress logical_simplify
         | _ => progress step_econstruct
         | _ => progress step_econstruct_PS
         | H : Some _ = Some _ |- _ => invert_clean H
         | H1 : ?x = Some _, H2 : ?x = Some _ |- _ =>
           rewrite H2 in H1; invert_clean H1
         | _ => reflexivity
         end.
(* General-purpose tactic that simplifies and solves simple goals for
   possibilistic NI. *)
Ltac crush := repeat crush_step.

Ltac label_cases :=
    match goal with
        | l: level, ell: level |- _ =>
            lazymatch goal with
                | |- context [l <<? ell] =>
                    destruct (l <<? ell)
            end
    end.

Ltac unwind_crush_step2 :=
    lazymatch goal with
        | H: {| obj := _; lbl := _ |} = _ |- _ => inversion H; subst
        | H: Some _ = Some _ |- _ => inversion H
        | _ => idtac
    end.

Ltac unwind_crush :=
    repeat match goal with
        | _ => progress label_cases
        | _ => progress unwind_crush_step2
        | _ => progress try congruence
    end.

Ltac subst_lets :=
  repeat match goal with x := _ |- _ => subst x end.

Ltac split_ands :=
  repeat match goal with |- _ /\ _ => split end.

Ltac apply_all_constructors :=
  lazymatch goal with
  | |- EvAugSemantics.step_system_ev _ _ _ =>
    eapply EvAugSemantics.SystemEvStepNode; apply_all_constructors
  | |- EvAugSemantics.step_node_ev _ _ _ _ _ =>
    econstructor; apply_all_constructors
  | |- RuntimeModel.step_node _ _ _ _ =>
    econstructor; apply_all_constructors
  | _ => idtac (* ignore goals that don't match one of the previous patterns *)
  end.

Ltac apply_all_constructors_PS :=
  lazymatch goal with
  | |- EvAugSemanticsPS.step_system_ev _ _ _ =>
    eapply EvAugSemanticsPS.SystemEvStepNode; apply_all_constructors_PS
  | |- EvAugSemanticsPS.step_node_ev _ _ _ _ _ =>
    econstructor; apply_all_constructors_PS
  | |- RuntimeModelPS.step_node _ _ _ _ =>
    econstructor; apply_all_constructors_PS
  | _ => idtac (* ignore goals that don't match one of the previous patterns *)
  end.

Lemma separate_labeled{A} (o : option A) (l : level) (x : labeled) :
  obj x = o -> lbl x = l -> x = Labeled _ o l.
Proof. destruct x; cbn; congruence. Qed.

Ltac separate_hyp T :=
  repeat match goal with
         | H : ?s = Labeled T ?o ?l |- _ =>
           assert (obj s = o /\ lbl s = l) by (rewrite H; tauto);
           clear H; logical_simplify
         end.
Ltac separate_goal := apply separate_labeled.

(* Tests for [destruct match] *)
Section DestructMatchTests.

  (* simple match *)
  Goal (forall n m : nat, match n with
                   | O => m
                   | S _ => m
                   end = m).
  Proof.
    intros n m.
    destruct_match; [ | ]. (* expect 2 subgoals *)
    all:exact (eq_refl m). (* both subgoals should be m = m *)
  Qed.

  (* nested match: innermost should be destructed first *)
  Goal (forall n m : nat, match (match m with
                          | O => n
                          | S _ => n
                          end) with
                   | O => m
                   | S _ => m
                   end = m).
  Proof.
    intros n m.
    destruct_match; [ | ]. (* expect 2 subgoals *)
    (* we expect that the match on m, not n, was the one destructed,
      so n should still be in context in both goals *)
    1:Check n. 2:Check n.
    1:destruct_match; exact (eq_refl 0).
    1:destruct_match; exact (eq_refl (S m)).
  Qed.

  (* pair-let *)
  Goal (forall (n : nat * nat * nat) (m : nat * nat * nat),
           n = m ->
           let '(a, b, c) := n in
           let '(x, y, z) := m in
           a + b + c = x + y + z).
  Proof.
    intros n m Heq.
    repeat destruct_match.
    (* now n and m should both be fully destructed; we expect Heq to
       say that two destructed 3-tuples are equal *)
    match type of Heq with (_,_,_) = (_,_,_) => idtac end.
    congruence.
  Qed.
End DestructMatchTests.

(* Tests for [invert_clean] *)
Section InvertCleanTests.
  Goal (forall n m,
           S n = S m -> n = m).
  Proof.
    intros n m Hlt.
    invert_clean Hlt.
    (* invert_clean should have completely cleared Hlt and executed
       [subst], so we should now have [m = m] *)

    (* This match will succeed if it can find *any* hypothesis with a
       non-nat type, so we want it to fail (meaning the only thing in
       context is a nat). This ensures that [invert_clean] cleared the
       hypothesis. *)
    Fail
      match goal with
      | H : _ |- _ =>
        lazymatch type of H with
        | nat => fail
        | ?x => idtac "found non-nat hypothesis" H "of type" x
        end
      end.

    exact (eq_refl m).
  Qed.
End InvertCleanTests.

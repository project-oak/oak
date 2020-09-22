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

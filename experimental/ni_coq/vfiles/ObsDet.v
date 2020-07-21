Require Import OakIFC.RuntimeModel.
Require Import OakIFC.Parameters.
Require Import OakIFC.LowEquivalences.
Require Import Coq.Lists.List.
Require Import OakIFC.GenericMap.
Import ListNotations.
Require Import OakIFC.StepUnwind.

Definition observational_determinism: Prop :=
    forall (ell: level) (s1 s2: state) (t1 t2: trace), 
        valid_trace s1 t1 ->
        valid_trace s2 t2 ->
        (state_low_eq ell s1 s2) ->
        (stut_trace_low_eq ell t1 t2).


Theorem od: observational_determinism.
Proof. unfold observational_determinism.
intros.
inversion H. inversion H0.
-  (* t1 = [s1], t2 = [s2] *)
apply SAddBoth. apply SNilEQ. apply H1.
- 
(* t1 = [s1], t2 = (s :: t) *)
(* must be that t2 is taking a "high step", only affecting
* values visible above ell *)
inversion H4. induction t2.
Admitted.


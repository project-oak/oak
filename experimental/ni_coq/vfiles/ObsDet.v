Require Import OakIFC.RuntimeModel.
Require Import OakIFC.Parameters.
Require Import OakIFC.LowEquivalences.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive valid_trace: trace -> Prop :=
    | VTOne s: (valid_trace (s :: nil) )
    | VTAdd s s' t
            (H0: valid_trace  (s :: t) )
            (H1: step_system s s'):
            (valid_trace (s' :: (s :: t))).

Definition observational_determinism: Prop :=
    forall (ell: level) (s1 s2: state) (t1 t2: trace), 
        [s1] = (tl t1) ->
        [s2] = (tl t2) ->
        valid_trace t1 ->
        valid_trace t2 ->
        (state_low_eq ell s1 s2) ->
        (trace_low_eq ell t1 t2).

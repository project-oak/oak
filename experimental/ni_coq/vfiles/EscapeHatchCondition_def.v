Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    ModelTypes
    State
    Events
    LowEquivalences
    ModelTypes
    TraceLowEq.


Definition eh_t := @trace (state * list event_l).
Definition is_init(t: eh_t) := length t = 1.

Definition conjecture_escape_hatch
    (sem: @trace_semanticsT (state * list event_l)) :=
    forall ell t1_init t2_init t1n,
    (trace_low_eq_down ell t1_init t2_init) /\
    (is_init t1_init) /\
    (is_init t2_init) /\
    (sem t1_init t1n) ->
    (exists t2n,
        (sem t2_init t2n) /\
        (trace_low_eq_down ell t1n t2n)).

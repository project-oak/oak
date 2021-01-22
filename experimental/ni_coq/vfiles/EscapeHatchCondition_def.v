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


Definition eh_t := @trace (state * down_l * event_l).
Definition is_init(t: eh_t) := length t = 1.

Inductive list_eq {A: Type}: list A -> list A -> Prop :=
    | LEqBothNil: list_eq [] []
    | LEqAddBoth e1 e2 l1 l2: 
            e1 = e2 ->
            list_eq l1 l2 ->
            list_eq (e1::l1) (e2::l2).

Definition traces_corresp (dt: @trace down_l)(t: eh_t) :=
    list_eq dt (extract_downgrade_trace t).

Definition eh_trace_low_eq: @trace_low_eqT (state * down_l *event_l) := 
    @trace_low_eq_down state_low_eq down_low_eq event_low_eq.

Definition conjecture_escape_hatch
    (sem: @trace_semanticsT (state * down_l * event_l)) :=
    forall ell t1_init t2_init dt1 dt2 t1n,
    (eh_trace_low_eq ell t1_init t2_init) /\
    (down_list_low_eq ell dt1 dt2) /\
    (is_init t1_init) /\
    (is_init t2_init) /\
    (traces_corresp dt1 t1n) /\
    (sem t1_init t1n) ->
    (exists t2n,
        (sem t2_init t2n) /\
        (eh_trace_low_eq ell t1n t2n) /\
        (traces_corresp dt2 t2n)).

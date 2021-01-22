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

Definition d_in_trace_elt d (t_elt: (state * down_l * event_l)) :=
    match t_elt with
        | (_, d, _) => True
        | _ => False
    end.

Inductive traces_corresp: @trace down_l -> eh_t -> Prop :=
    | TCBothNil: traces_corresp [] []
    | TCAddHeads d t_elt dt t: 
        d_in_trace_elt d t_elt ->
        traces_corresp (d::dt) (t_elt::t).

Definition conjecture_escape_hatch
    (sem: @trace_semanticsT (state * list event_l)) :=
    forall ell t1_init t2_init dt1 dt2 t1n,
    (trace_low_eq_down ell t1_init t2_init) /\
    (down_list_low_eq ell dt1 dt2) /\
    (is_init t1_init) /\
    (is_init t2_init) /\
    (traces_corresp dt1 t1n) /\
    (sem t1_init t1n) ->
    (exists t2n,
        (sem t2_init t2n) /\
        (trace_low_eq_down ell t1n t2n) /\
        (traces_corresp dt2 t2n)).

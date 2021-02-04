Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    Lattice
    State
    Events
    ModelTypes
    LowEqPS.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* Ensembles don't have implicit type params and this line fixes that *)
Arguments Ensembles.Empty_set{U}.

(*============================================================================
* Trace Low Equivalences
*===========================================================================*)

(* This is a copy of TraceLowEq but for partially-secret labels.
   This version only replicates the possibilistic NI definition.
*)

(* This is a straightforward definition of trace low-equivalence
    Roughly, it says that 
    t1 =L t2 <-> forall i, t1[i] =L t2[i].
*)

Inductive trace_low_eq {s_leq: @low_eq_t state}{e_leq: @low_eq_t event_l}:
        @trace_low_eqT (state * (@labeled event)) :=
    | NilEQ ell: trace_low_eq ell [] []
    | AddBoth ell xs xe ys ye t1 t2:
        trace_low_eq ell t1 t2 ->
        e_leq ell xe ye ->
        s_leq ell xs ys ->
        trace_low_eq ell ((xs, xe)::t1) ((ys, ye)::t2).

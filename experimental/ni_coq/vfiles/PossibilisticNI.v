Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Parameters
    RuntimeModel
    EvAugSemantics
    Events
    LowEquivalences.

(*
This is the top-level candidate security condition. This is a
"possibilistic security condition". A possibilistic security condition
says that two executions look the same from the perspective of an observer
if all _possible behaviors_ look the same if they begin from initial states
that look the same to the observer.
In other words there is some way to reach an execution trace
that looks the same beginning from the other state.

Trapeze uses a possibilistic definition of security:
https://pdfs.semanticscholar.org/809b/f2702a765b9e7dba4624a1dbc53af11579db.pdf
See also:
https://www.cs.cornell.edu/andru/papers/csfw03.pdf

*)

(* An alternative way of specifying security for
   concurrent systems is observational determinism, which says
   that for any two executions that begin from low-equivalent
   initial states, all actual observed behaviors 
   (by contrast to the possibly observed behaviors)
   _always_ look the same.

    This looks like:
    forall s1 s2 t1 t2,
        (s1 =L s2) /\
        (step_multi s1) => t1 /\
        (step_multi s2) => t2 ->
            t1 =L t2.

    An advantage of observational determinism over possibilistic
    noninterference is that O.D. is preserved by refinement. This does
    not matter in this context since we are not doing a refinement proof.
    
    O.D. also has requirements about data race freedom that are not
    needed to prove a possibilistic security definition. (It may be
    worth looking into whether or not the runtime actually satisfies
    these data race freedom requirements later, though it does not
    seem high priority).

    ***
    These two definitions also crucially require different
    definitions of trace low-equivalence as discussed in Events.v
    ***
*)

Definition conjecture_possibilistic_ni := forall ell s11 s21 s1n t1n,
    (state_low_eq ell s11 s21) /\
    (step_system_ev_multi s11 [] s1n t1n) ->
    (exists s2n t2n,
        (step_system_ev_multi s21 [] s2n t2n) /\
        (trace_low_eq ell t1n t2n)).

Theorem possibilistic_ni_1step: forall ell s11 s21 s12 t12,
    (state_low_eq ell s11 s21) /\
    (step_system_ev s11 [] s12 t12) ->
    (exists s22 t22,
        (step_system_ev s21 [] s22 t22) /\
        (trace_low_eq ell t12 t22)).
Admitted. (* NOTE: work in progress *)

Theorem possibilistic_ni: conjecture_possibilistic_ni. Proof.
unfold conjecture_possibilistic_ni.
intros ell s11 s21 s1n t1n [H1 H2].
remember ([]: trace) as emp eqn:R.
induction H2 as [s11 t s12 t12 | s11 t s1' t1' s1n t1n]; rewrite R in *.
- assert (E: (exists s22 t22,
        (step_system_ev s21 [] s22 t22) /\
        (trace_low_eq ell t12 t22))). {
        apply (possibilistic_ni_1step ell s11 s21 s12 t12). split; assumption.
}
destruct E as [s22 E]. destruct E as [t22 [E1 E2]].
exists s22, t22. split; try constructor; assumption.
- (* no induction hypothesis *)(* induction on trace length instead  ? *)
admit.
(* NOTE: This is only admitted because it is work in progress *)
Admitted.

Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    ModelTypes
    State
    Events
    TraceLowEq.
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

(* PNI is tied to a specific def of traces and of trace low-equivalence *)

Definition pni_t := @trace (state * event_l).
Definition is_init(t: pni_t) := length t = 1.

Definition conjecture_possibilistic_ni 
    (sem: @trace_semanticsT (state * event_l))
    (leq: @trace_low_eqT (state * (@labeled event)))
        := forall ell t1_init t2_init t1n,
    (leq ell t1_init t2_init) /\
    (is_init t1_init) /\
    (is_init t2_init) /\
    (sem t1_init t1n) ->
    (exists t2n,
        (sem t2_init t2n) /\
        (leq ell t1n t2n)).

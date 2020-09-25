Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    RuntimeModel
    EvAugSemantics
    Events
    LowEquivalences
    TraceTheorems
    NIUtilTheorems
    Unwind.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Local Open Scope map_scope.
Local Open Scope aug_scope.

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

Definition is_init(t: trace) := length t = 1.

Definition conjecture_possibilistic_ni := forall ell t1_init t2_init t1n,
    (trace_low_eq ell t1_init t2_init) /\
    (is_init t1_init) /\
    (is_init t2_init) /\
    (step_system_ev_multi t1_init t1n) ->
    (exists t2n,
        (step_system_ev_multi t2_init t2n) /\
        (trace_low_eq ell t1n t2n)).


Theorem n_low_proj_label_preserving: forall ell n,
    (node_low_proj ell n).(nlbl) = n.(nlbl).
Proof.
Admitted.

Theorem state_low_eq_from_substates: forall ell s1 s2,
    (node_state_low_eq ell s1.(nodes) s2.(nodes)) ->
    (chan_state_low_eq ell s1.(chans) s2.(chans)) ->
    (state_low_eq ell s1 s2).
Proof.
Admitted. (* WIP *)

Theorem eq_nodes_have_eq_lbls: forall n1 n2,
    n1 = n2 -> (nlbl n1) = (nlbl n2).
Proof. congruence. Qed.
 
Theorem node_leq_imples_eq_lbls: forall ell n1 n2,
    (node_low_eq ell n1 n2) -> (n1.(nlbl) = n2.(nlbl)).
Proof.
    inversion 1. unfold node_low_proj in H1.
     destruct (n1.(nlbl) <<? ell); destruct (n2.(nlbl) <<? ell).
    - congruence.
    - inversion H1. reflexivity.
    - apply eq_nodes_have_eq_lbls in H1. simpl in H1. congruence.
    - inversion H1. congruence.
Qed.

Theorem step_implies_lowproj_steps_leq: forall ell s1 s1' e1,
    (step_system_ev s1 s1' e1) ->
    (exists s2' e2,
        (step_system_ev (state_low_proj ell s1) s2' e2) /\
        (state_low_eq ell s1' s2') /\
        (event_low_eq ell e1 e2)).
Proof.
Admitted.

Theorem low_proj_steps_implies_leq_step: forall ell s s1' e1,
    (step_system_ev (state_low_proj ell s) s1' e1) ->
    (exists s2' e2,
        (step_system_ev s s2' e2) /\
        (state_low_eq ell s1' s2') /\
        (event_low_eq ell e1 e2)).
Proof.
Admitted.

Theorem possibilistic_ni_1step: forall ell s1 s2 s1' e1,
    (state_low_eq ell s1 s2) ->
    (step_system_ev s1 s1' e1) ->
    (exists s2' e2,
        (step_system_ev s2 s2' e2) /\
        (state_low_eq ell s1' s2') /\
        (event_low_eq ell e1 e2)).
Proof.
    intros ell s1 s2 s1' e1 H_leq_s1_s2 Hstep_s1_s1'.
    specialize (step_implies_lowproj_steps_leq ell s1 s1' e1 Hstep_s1_s1')
        as [s3' [ e3 [Hstep_s1_s3 [H_leq_s1'_s3' H_leq_e1_e3]]]].
    assert (H_s2_proj_s3': (step_system_ev (state_low_proj ell s2) s3' e3)).
        { replace (state_low_proj ell s1) with 
            (state_low_proj ell s2) in Hstep_s1_s3. assumption. }
    specialize (low_proj_steps_implies_leq_step ell s2 s3' e3 H_s2_proj_s3')
        as [s2' [ e2 [Hstep_s2_s2' [H_leq_s3'_s2' H_leq_e3_e2]]]].
    exists s2', e2. split. assumption. split.
    - admit. (* transitivity of state_low_eq *)
    - admit. (* transitivity of event_low_eq *)
Admitted.

Theorem possibilistic_ni_unwind_t: forall ell t1 t2 t1',
(trace_low_eq ell t1 t2) ->
(step_system_ev_t t1 t1') ->
(exists t2',
    (step_system_ev_t t2 t2') /\
    (trace_low_eq ell t1' t2')).
Proof.
    (* Should make use of possibilistic_ni_1step *)
Admitted. (* WIP *)

Theorem possibilistic_ni: conjecture_possibilistic_ni.
Proof.
unfold conjecture_possibilistic_ni.
intros ell t1_init t2_init t1n [Hinit_tleq [Ht1_init [Ht2_init Ht1_mstep_t1n]]].
remember ([]: trace) as emp eqn:R.
induction t1n.
    - (* t1 is empty trace, which is not possible *)
        exfalso. apply (no_steps_to_empty t1_init Ht1_mstep_t1n).
    - (* inductive case *)
    inversion Ht1_mstep_t1n ; subst.
        + specialize (possibilistic_ni_unwind_t ell t1_init t2_init
            (a::t1n) Hinit_tleq H) as [t2n [E1 E2]].
            exists t2n. split. constructor. assumption. assumption.
        + rename Ht1_mstep_t1n into Ht1_mstep_at1n.
          match goal with
            H : _ |- _ =>
            apply step_system_ev_uncons in H end.
          cbn [tl] in *; subst.
          specialize (IHt1n ltac:(assumption))
            as [t2n [Hm_t2_init_t2n Hleq_t1n_t2n]].
        specialize (step_system_multi_extends _ (a::t1n) ltac:(eauto)) as E2.
        specialize (possibilistic_ni_unwind_t ell t1n t2n (a::t1n) Hleq_t1n_t2n E2)
            as [t2n' [Hs_t2n_t2n' Hleq_at1n_t2n']].
        exists t2n'. split.
        apply (step_system_transitive t2_init t2n t2n'). assumption.
        constructor. assumption. assumption.
Qed.

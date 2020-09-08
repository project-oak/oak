Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Parameters
    RuntimeModel
    EvAugSemantics
    Events
    LowEquivalences
    TraceTheorems.
From mathcomp Require Import all_ssreflect finmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.


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

Theorem possibilistic_ni_1step_node: forall ell id t1 t2 s1 s2 n1 n2 t1',
    (head_st t1 = Some s1) ->
    (head_st t2 = Some s2) ->
    (s1.(nodes) .[?id] = Some n1) ->
    (s2.(nodes) .[?id] = Some n2) ->
    (trace_low_eq ell t1 t2) ->
    (step_node_ev id (ncall n1) t1 t1') ->
    (exists t2',
        (step_node_ev id (ncall n2) t2 t2') /\
        (trace_low_eq ell t1' t2')).
Proof.
Admitted. (* WIP *)

Theorem call_havoc_unwind: forall ell id c t1 t2 t1' t2',
    (trace_low_eq ell t1 t2) ->
    (t1' = head_set_call t1 id c) ->
    (t2' = head_set_call t2 id c) ->
    (trace_low_eq ell t1' t2').
Proof.
Admitted. (* WIP *)

Theorem trace_loweq_to_deref_node: forall ell t1 t2 id s1 n1,
(* If two traces are low-equivalent and in the first trace:
    - the head element has some state (it's not an emty trace)
    - and in the head state, id can be dereferenced to some node
    then:
    - there must be some head state in the other trace (s2)
    - and we must be able to also dereference id in s2 to some node 
Mostly, this is just a consequence of the def of trace-low-equivalence.
*)
    (trace_low_eq ell t1 t2) ->
    (head_st t1 = Some s1) ->
    ((nodes s1).[? id] = Some n1) ->
    (exists s2 n2,
        head_st t2 = Some s2 /\ 
        (nodes s2).[? id] = Some n2 ).
Proof.
    intros.
    destruct (head_st t2) eqn:Ht2head.
    - (* some s *)
        destruct (nodes s).[? id] eqn:Hsid.
            + (* some n *)
                exists s. exists n.
                split; (reflexivity || assumption).
            + (* none *)
                inversion H; subst.
                * (* t1 = [] and t2 = [] *) discriminate H0.
                * exfalso. inversion H4; subst. simpl in Ht2head.
                 unfold node_state_low_eq in H5.
                 inversion Ht2head. rewrite H8 in H5. specialize (H5 id).
                 rewrite Hsid in H5. simpl in H0. inversion H0.
                 rewrite H9 in H5. rewrite H1 in H5. assumption.
    - (* none *)
        inversion H; subst. 
            + discriminate H0.
            + inversion Ht2head.
Qed.
 
Theorem possibilistic_ni_1step: forall ell t1 t2 t1',
    (trace_low_eq ell t1 t2) ->
    (step_system_ev t1 t1') ->
    (exists t2',
        (step_system_ev t2 t2') /\
        (trace_low_eq ell t1' t2')).
Proof.
    intros.
    inversion H0; subst.
    rename t' into t1_sn. rename s into s1. rename s' into s1'. rename n into n1.
    specialize (trace_loweq_to_deref_node ell t1 t2 id s1 n1
        H H1 H3) as [s2 [n2 [Ht2s2 Hs2n2]]].
    specialize (possibilistic_ni_1step_node ell id
        t1 t2 s1 s2 n1 n2 t1_sn  H1 Ht2s2 H3 Hs2n2 H H5)
            as [t2_sn [Hnstep2 Hnstep_leq]].
    assert (Hs2': exists s2', head_st t2_sn = Some s2'). {
        (* this assertion is essentially re-stating node_no_steps_to_empty
        in a way that gives us a particular head state of t2_sn *)
        destruct t2_sn; subst.
        - exfalso. apply (node_no_steps_to_empty t2 id (ncall n2)). assumption.
        - exists (fst p). simpl. destruct p. reflexivity.
    }
    destruct Hs2' as [s2' Hs2']. 
    remember (head_set_call t2_sn id c') as t2'.
    exists t2'. split.
    +  (* can step from t2_sn to t2' *)
        subst. apply (ValidStep id n2 (ncall n2) c' s2 t2 s2' t2_sn);
            (assumption || reflexivity).
    + (* low-equiv t1' t2' *)
        remember (head_set_call t1_sn id c') as t1' eqn:Ht1'.
        apply (call_havoc_unwind ell id c' t1_sn t2_sn t1' t2');
            (assumption || reflexivity).
Qed. 

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
        + specialize (possibilistic_ni_1step ell t1_init t2_init
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
        specialize (possibilistic_ni_1step ell t1n t2n (a::t1n) Hleq_t1n_t2n E2)
            as [t2n' [Hs_t2n_t2n' Hleq_at1n_t2n']].
        exists t2n'. split.
        apply (step_system_transitive t2_init t2n t2n'). assumption.
        constructor. assumption. assumption.
Qed.

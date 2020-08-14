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

Definition is_init(t: trace) := length t = 1.

Definition conjecture_possibilistic_ni := forall ell t1_init t2_init t1n,
    (trace_low_eq ell t1_init t2_init) /\
    (is_init t1_init) /\
    (is_init t2_init) /\
    (step_system_ev_multi t1_init t1n) ->
    (exists t2n,
        (step_system_ev_multi t2_init t2n) /\
        (trace_low_eq ell t1n t2n)).

Theorem possibilistic_ni_1step: forall ell t1 t2 t1',
    (trace_low_eq ell t1 t2) ->
    (step_system_ev t1 t1') ->
    (exists t2',
        (step_system_ev t2 t2') /\
        (trace_low_eq ell t1' t2')).
Admitted. (* NOTE: work in progress *)

(* Note: How can this be done more elegantly, or skipped? *)
Theorem nil_cons_rev: forall (A : Type) (x : A) (l : list A), x :: l <> [].
Proof.
    unfold not. intros. symmetry in H. generalize dependent H.
    apply nil_cons.
Qed.

Theorem t_upd_mono_nil: forall t s,
    ~(t = nil) -> ~((trace_upd_head_state t s) = nil).
Proof.
    intros.
    unfold trace_upd_head_state. destruct t. assumption.
    replace (let (_, e) := p in (s, e) :: t) with
        ((let (_, e) := p in (s, e)) :: t).
    apply nil_cons_rev.
    destruct p. reflexivity.
Qed.

Theorem no_steps_to_empty: forall t, 
    ~(step_system_ev_multi t []).
    unfold not. intros.
    remember ([]: trace) as emp eqn:R.
    induction H; subst.
        - (* refl *) inversion H; subst. destruct t'.
            + inversion H2. 
            + apply t_upd_mono_nil in H0. assumption.
            unfold not. intros. generalize dependent H4. apply nil_cons_rev.
        - apply IHstep_system_ev_multi. reflexivity.
Qed.

Theorem step_system_backwards: forall t t' a,
    step_system_ev_multi t (a :: t') ->
    step_system_ev_multi t t'.
Proof.
Admitted.

Theorem step_system_extends: forall t t' a,
    step_system_ev_multi t (a :: t') ->
    step_system_ev t' (a :: t').
Proof.
Admitted.

Theorem step_system_transitive: forall t1 t2 t3,
    step_system_ev_multi t1 t2 ->
    step_system_ev_multi t2 t3 ->
    step_system_ev_multi t1 t3.
Proof.
Admitted.

Theorem possibilistic_ni: conjecture_possibilistic_ni. Proof.
unfold conjecture_possibilistic_ni.
intros ell t1_init t2_init t1n [Hinit_tleq [Ht1_init [Ht2_init Ht1_mstep_t1n]]].
remember ([]: trace) as emp eqn:R.
induction t1n.
    - (* t1 is empty trace, which is not possible *)
        exfalso. apply (no_steps_to_empty t1_init Ht1_mstep_t1n).
    - (* inductive case *)
    inversion Ht1_mstep_t1n ; subst.
        + assert (E: exists t2n,
            (step_system_ev t2_init t2n) /\
            (trace_low_eq ell (a::t1n) t2n)) by
            apply (possibilistic_ni_1step ell t1_init t2_init
                (a::t1n) Hinit_tleq H).
            destruct E as [t2n [E1 E2]].
            exists t2n. split. constructor. assumption. assumption.
        + rename Ht1_mstep_t1n into Ht1_mstep_at1n.
        assert (E: step_system_ev_multi t2 t1n)
            by apply (step_system_backwards t2 t1n a H0).
        assert (H': step_system_ev_multi t1_init t2) by
            (constructor; assumption).
        assert (Ht1_mstep_t1n: step_system_ev_multi t1_init t1n)
            by apply (step_system_transitive t1_init t2 t1n H' E).
        apply IHt1n in Ht1_mstep_t1n as [t2n [Hm_t2_init_t2n Hleq_t1n_t2n]].
        assert (E2: step_system_ev t1n (a::t1n))
            by apply (step_system_extends t2 t1n a H0).
            (*need to get non-multi from E2.  *)
        assert (E3: exists t2n',
            (step_system_ev t2n t2n') /\
            (trace_low_eq ell (a::t1n) t2n')) by
            apply (possibilistic_ni_1step ell t1n t2n (a::t1n) Hleq_t1n_t2n E2).
            destruct E3 as [t2n' [Hs_t2n_t2n' Hleq_at1n_t2n']].
        exists t2n'.
        split.
        + apply (step_system_transitive t2_init t2n t2n'). assumption.
        constructor. assumption. assumption.
Qed.
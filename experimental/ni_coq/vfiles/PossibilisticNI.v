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


Theorem unobservable_node_step: forall ell s s' e id n,
    s.(nodes).[? id] = Some n ->
    step_node_ev id n.(ncall) s s' e ->
    ~(nlbl n <<L ell) ->
    (state_low_eq ell s s') /\ (event_low_eq ell e (empty_event e.(elbl))).
Proof.
Admitted. (* WIP *)

Theorem step_implies_lowproj_steps_leq: forall ell s1 s1' e1,
    (step_system_ev s1 s1' e1) ->
    (exists s2' e2,
        (step_system_ev (state_low_proj ell s1) s2' e2) /\
        (state_low_eq ell s1' s2') /\
        (event_low_eq ell e1 e2)).
Proof.
Admitted. (* WIP *)

Theorem low_proj_steps_implies_leq_step: forall ell s s1' e1,
    (step_system_ev (state_low_proj ell s) s1' e1) ->
    (exists s2' e2,
        (step_system_ev s s2' e2) /\
        (state_low_eq ell s1' s2') /\
        (event_low_eq ell e1 e2)).
Proof.
    intros. inversion H; subst.
    - (* SystemSkip *)
        exists s, (EvL NilEv ell0). split. constructor.
        split. unfold state_low_eq. unfold low_eq.
        rewrite state_low_proj_idempotent. reflexivity.
        reflexivity.
    - (* NodeStep *)
        rename s'' into s1''. rename s' into s1'. rename H2 into H_step_projs_s1'.
        specialize (proj_node_state_to_proj_n ell s id n H0)
            as [n' [Hidx_n' Hproj_n']].
        destruct (n'.(nlbl) <<? ell).
        *
            (* flowsto case*) (* likely by inversion on H_step_projs_s1' *)
            inversion H_step_projs_s1'; assert (n0 = n) by congruence; subst.
            + (* WriteChannel *)
                inversion H3; subst.
                specialize (uncons_proj_chan_s ell s han ch H8)
                    as [ch2 [H_ch'_idx H_ch2_proj]].
                remember (s_set_call (state_upd_chan han (chan_append ch2 msg)
                (state_upd_node id n'0 s)) id c') as s2''.
                exists s2'', ((node_low_proj ell n') ---> msg); repeat try split.
                (* step *)
                rewrite Heqs2''. eapply SystemEvStepNode; eauto; subst. 
                replace (ncall n') with (ncall (node_low_proj ell n')) by
                    (erewrite flows_node_proj; try eassumption; try congruence).
                rewrite <- H1. econstructor. erewrite flows_node_proj; assumption.
                assert (n' = n). { 
                    rewrite H6 in H0. inversion H0. symmetry. eapply flows_node_proj. auto.
                }
                eapply SWriteChan; try congruence; try assumption;
                    try (erewrite <- chan_projection_preserves_lbl; eassumption).
                (* s1'' =L s2'' *)
                (* This part looks tactic-able to me *)
                subst. unfold s1''. eapply set_call_unwind. unfold ch'.
                eapply state_upd_chan_unwind. eapply chan_append_unwind. 
                eapply chan_low_proj_loweq. eapply state_upd_node_unwind.
                reflexivity. eapply state_low_proj_loweq.
            + (* ReadChannel *)
                admit.
            + (* CreateChannel *)
                admit.
            + (* CreateNode *)
                admit.
            + (* Internal *)
                admit.
        (* by cases on the command by n in s *)
        * (* not flowsTo case *)
            rename n0 into Hflows.
            assert ((state_low_eq ell (state_low_proj ell s) s1') /\
                (event_low_eq ell e1 (empty_event e1.(elbl))))
                as [Hustep Huev] by
                repeat (eauto || eapply unobservable_node_step
                    || eapply node_projection_preserves_flowsto).
            exists s, (empty_event (elbl e1));
                repeat try (split || constructor).
            + (* s1'' ={ell} s *)
                apply state_low_eq_sym.
                eapply (state_low_eq_trans _ s s1' s1'').
                eapply (state_low_eq_trans _ s (state_low_proj ell s) s1').
                apply state_low_eq_sym.
                eapply state_low_proj_idempotent. assumption.
                unfold s1''. 
                assert (H_leq_s_s1': state_low_eq ell s s1'). {
                    eapply (state_low_eq_trans _ s
                        (state_low_proj ell s) s1').
                    apply state_low_eq_sym.
                    eapply state_low_proj_idempotent.
                    assumption.
                }
                specialize (state_loweq_to_deref_node ell s s1' id n'
                    Hidx_n' H_leq_s_s1') as [ns1' [Hidx_s1' H_leq_n'_n2]].
                eapply set_call_unobs. eassumption.
                replace (nlbl ns1') with (nlbl n')
                    by (eapply node_low_eq_to_lbl_eq; eassumption).
                auto.
            + (* e1 ={ell} *) assumption.
Admitted. (* WIP *)

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
    - eapply (state_low_eq_trans _ s1' s3' s2'); congruence.
    - eapply (event_low_eq_trans _ e1 e3 e2); congruence.
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

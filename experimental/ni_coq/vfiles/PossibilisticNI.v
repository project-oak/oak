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
    Unwind
    Tactics.
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

(* TODO: maybe move to Tactics.v *)
Local Ltac logical_simplify :=
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : exists _, _ |- _ => destruct H
         | H1 : ?P, H2 : ?P -> _ |- _ =>
           (* only proceed if P is a Prop; if H1 is a nat, for instance, P
              would be a Type, and we don't want to specialize foralls. *)
           match type of P with Prop => idtac end;
           specialize (H2 H1)
         | H : ?x = ?x |- _ => clear H
         end.

(* Single step of [crush] *)
Local Ltac crush_step :=
  repeat match goal with
         | _ => progress intros
         | _ => progress subst
         | _ => progress logical_simplify
         | H : Some _ = Some _ |- _ => invert_clean H
         | H1 : ?x = Some _, H2 : ?x = Some _ |- _ =>
           rewrite H2 in H1; invert_clean H1
         | _ => reflexivity
         end.
(* General-purpose tactic that simplifies and solves simple goals for
   possibilistic NI. *)
Local Ltac crush := repeat crush_step.

Hint Resolve multi_system_ev_refl multi_system_ev_tran : multi.

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
Admitted.

Theorem step_implies_lowproj_steps_leq: forall ell s1 s1' e1,
    (step_system_ev s1 s1' e1) ->
    (exists s2' e2,
        (step_system_ev (state_low_proj ell s1) s2' e2) /\
        (state_low_eq ell s1' s2') /\
        (event_low_eq ell e1 e2)).
Proof.
    intros. inversion H; subst. 
    - (* SystemSkip *)
        exists (state_low_proj ell s1'), (EvL NilEv ell0); repeat try split.
        constructor. symmetry. eapply state_low_proj_loweq.
    - (* NodeSetp *)
        rename s' into s1'. rename s'' into s1''. rename H2 into H_step_s1_s1'.
        destruct (n.(nlbl) <<? ell).
        * (* flowsto case *)
            inversion H_step_s1_s1'; assert (n0 = n ) by congruence; subst.
            + (* WriteChannel *)
                inversion H3; assert (n0 = n) by congruence; subst.
                remember (chan_low_proj ell ch) as ch2.
                remember (chan_append ch2 msg) as ch2'.
                remember (state_low_proj ell s1) as s2.
                remember (state_upd_chan han ch2' (state_upd_node id n' s2)) as s2'.
                remember (s_set_call s2' id c') as s2''.
                exists s2'', (n ---> msg); repeat try split.
                assert (Hnproj: n = (node_low_proj ell n)) by
                    repeat (eapply flows_node_proj || symmetry|| congruence ).
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                (* system step *)
                replace (s2'') with (s_set_call s2' id c').
                econstructor. rewrite Heqs2. eauto. eauto.
                (* node step ev *)
                replace (node_low_proj ell n) with n by auto; auto.
                rewrite <- H1.
                econstructor. congruence.
                (* node step *)
                subst. eapply SWriteChan.
                congruence. congruence. 
                eapply state_hidx_to_proj_state_hidx; eauto.
                replace (clbl (chan_low_proj ell ch)) with (clbl ch)
                    by (symmetry; eapply chan_projection_preserves_lbl).
                eauto. eauto. eauto.
                (* s1'' ={ell} s2'' *)
                unfold s1''.  unfold ch'. subst. 
                eapply set_call_unwind.
                eapply state_upd_chan_unwind.
                eapply chan_append_unwind.
                symmetry. eapply chan_low_proj_loweq.
                eapply state_upd_node_unwind.
                reflexivity.
                symmetry. eapply state_low_proj_loweq.
            + (* ReadChannel *)
                inversion H3. crush.
                assert (Hnproj: n = (node_low_proj ell n)) by
                    repeat (eapply flows_node_proj || symmetry|| congruence ).
                assert (Hcproj: (chan_low_proj ell ch) = ch) by
                    eauto using flows_chan_proj, ord_trans.
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                eexists. exists (n <--- msg).
                split. econstructor.
                eauto. eauto.
                replace (node_low_proj ell n) with n by auto; auto.
                rewrite <- H1. econstructor.
                replace n with (node_low_proj ell n) by auto; auto.
                econstructor. eassumption.
                replace (node_low_proj ell n) with n by auto; auto.
                eapply state_hidx_to_proj_state_hidx; eauto. 
                replace (chan_low_proj ell ch) with ch by eauto.
                eauto. 
                replace (node_low_proj ell n) with n by auto; auto.
                replace (chan_low_proj ell ch) with ch. eauto.
                eauto. eauto. unfold s1''. subst. split.
                eapply set_call_unwind. eapply state_upd_chan_unwind.
                unfold ch'. 
                replace (chan_low_proj ell ch) with ch by eauto. 
                reflexivity. eapply state_upd_node_unwind.
                unfold n'. replace (node_low_proj ell n) with n by auto; auto.
                reflexivity. symmetry. eapply state_low_proj_loweq.
                reflexivity.
            + (* CreateChannel *)
                inversion H3. crush. 
                assert (Hnproj: n = (node_low_proj ell n)) by
                    repeat (eapply flows_node_proj || symmetry|| congruence ).
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                unfold s', s2, s0 in *.
                remember (s_set_call (state_upd_node id (node_add_whan h n)
                    (state_upd_node id (node_add_rhan h n)
                     (state_upd_chan h (new_chan lbl) 
                     (state_low_proj ell s1)))) id c') as s_ex2'.
                     (* s_ex2' is the same as s1'' but replacing s1' with
                     its ell-projection *)
                exists s_ex2', (n ---); repeat split.
                subst. econstructor. eauto.
                replace (node_low_proj ell n) with n by auto; auto.
                rewrite <- H1. econstructor. 
                replace n with (node_low_proj ell n) by auto; auto.
                econstructor. 
                replace n with (node_low_proj ell n) by auto; auto.
                auto.
                replace (handle_fresh (state_low_proj ell s1))
                    with (handle_fresh s1)
                    by (symmetry; eapply proj_pres_handle_fresh); auto.
                unfold s1''. subst.
                eapply set_call_unwind. eapply state_upd_node_unwind.
                reflexivity. eapply state_upd_node_unwind. reflexivity.
                eapply state_upd_chan_unwind. reflexivity.
                symmetry. eapply state_low_proj_loweq.
            + (* CreateNode *)
                inversion H3; crush. 
                assert (Hnproj: n = (node_low_proj ell n)) by
                    repeat (eapply flows_node_proj || symmetry|| congruence ).
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                remember (state_upd_node new_id
                    {|
                        nlbl := lbl;
                        read_handles := Ensembles.Singleton h;
                        write_handles := Ensembles.Empty_set;
                        ncall := Internal
                    |} (state_low_proj ell s1)
                ) as s3_ex2.
                remember (state_upd_node id (node_add_rhan h n) s3_ex2)
                    as s'_ex2.
                remember (s_set_call s'_ex2 id c') as s2''.
                exists s2'', (-- n --); repeat split.
                subst. econstructor. 
                eauto. eauto. 
                replace (node_low_proj ell n) with n by auto; auto.
                rewrite <- H1. econstructor.
                replace n with (node_low_proj ell n) by auto; auto.
                econstructor. 
                replace n with (node_low_proj ell n) by auto; auto.
                auto.
                replace (nid_fresh (state_low_proj ell s1))
                    with (nid_fresh s1)
                    by (symmetry; eapply proj_pres_nid_fresh); auto.
                unfold s1'', s', s3; subst.
                eapply set_call_unwind.
                eapply state_upd_node_unwind. reflexivity.
                eapply state_upd_node_unwind. reflexivity.
                symmetry. eapply state_low_proj_loweq.
            +  (* Internal *)
                inversion H3; crush.
                exists (s_set_call (state_low_proj ell s1') id c'), (n ---);
                    repeat split.
                assert (Hnproj: n = (node_low_proj ell n)) by
                    repeat (eapply flows_node_proj || symmetry|| congruence ).
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                econstructor. eauto. eauto.
                replace (node_low_proj ell n) with n by auto; auto.
                rewrite <- H1. econstructor.
                replace n with (node_low_proj ell n) by auto; auto.
                econstructor. unfold s1''.
                eapply set_call_unwind. 
                symmetry. eapply state_low_proj_loweq.
        * (* not flowsTo case *)
            rename n0 into Hflows.
            assert ((state_low_eq ell s1 s1') /\
                (event_low_eq ell e1 (empty_event e1.(elbl))))
                as [Hustep Huev] by
                repeat (eauto || eapply unobservable_node_step).
            exists (state_low_proj ell s1), (empty_event (elbl e1));
                repeat try split.
            (* step *)
            constructor.
            (* states leq *)
            specialize (state_loweq_to_deref_node ell s1 s1' id n 
                H0 Hustep) as [ns1' [Hns1'idx Hns1'leq]].
            transitivity s1'. unfold s1''. symmetry. eapply set_call_unobs.
            eauto. replace (nlbl ns1') with (nlbl n) by
                (eapply node_low_eq_to_lbl_eq; eauto).
            eauto. 
            assert (E: state_low_eq ell (state_low_proj ell s1) s1) by
                eapply state_low_proj_loweq.
            congruence.
            (* events leq *)
            congruence.
Qed.

(* Hints for [eauto with unwind] *)
Hint Resolve state_upd_chan_unwind chan_append_unwind chan_low_proj_loweq
     state_upd_node_unwind : unwind.
Hint Extern 4 (node_low_eq _ _ _) => reflexivity : unwind.

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
                invert_clean H3.
                specialize (uncons_proj_chan_s ell s han ch H8)
                    as [ch2 [H_ch'_idx H_ch2_proj]].
                remember (s_set_call (state_upd_chan han (chan_append ch2 msg)
                (state_upd_node id n'0 s)) id c') as s2''.
                exists s2'', ((node_low_proj ell n') ---> msg); repeat split.
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
                eauto with unwind.
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
Qed.

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
  unfold conjecture_possibilistic_ni. crush.
  let H := match goal with H : step_system_ev_multi _ _ |- _ => H end in
  induction H; crush.
  all:pose proof (possibilistic_ni_unwind_t
                    _ _ _ _
                    ltac:(eassumption) ltac:(eassumption)).
  all:crush.
  all:eexists; split; crush; [ | eassumption ]; eauto with multi.
Qed.

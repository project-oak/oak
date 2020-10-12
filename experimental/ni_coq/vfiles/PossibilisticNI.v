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


(* Hints for [eauto with unwind] *)
Hint Resolve state_upd_chan_unwind chan_append_unwind chan_low_proj_loweq
    chan_low_proj_idempotent state_upd_node_unwind set_call_unwind 
    state_low_proj_loweq : unwind.
Hint Extern 4 (node_low_eq _ _ _) => reflexivity : unwind.
Hint Extern 4 (chan_low_eq _ _ _) => reflexivity : unwind.
(* meant to be case where we have (cleq ch (proj ch) ) and want to swap order *)
Hint Extern 4 (chan_low_eq _ _ (chan_low_proj _ _)) => symmetry : unwind.
Hint Extern 4 (state_low_eq _ _ (state_low_proj _ _)) => symmetry : unwind.


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
                inversion H3; crush.
                (* is there a more concise way to write this calculation?
                I just want s1'' but with s1 replaced by its low projection *)
                remember (chan_low_proj ell ch) as ch2.
                remember (chan_append ch2 msg) as ch2'.
                remember (state_low_proj ell s1) as s2.
                remember (state_upd_chan han ch2' (state_upd_node id n' s2)) as s2'.
                remember (s_set_call s2' id c') as s2''.
                exists s2'', (n ---> msg); repeat split; crush.
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                rewrite flows_node_proj in *; eauto.
                econstructor; try eauto.
                rewrite <- H1.
                econstructor; try eauto.
                econstructor; try eauto.
                eapply state_hidx_to_proj_state_hidx; eauto.
                    (* note that we can't use flows_chan_proj in this case *)
                rewrite chan_projection_preserves_lbl; eauto.
                (* s1'' ={ell} s2'' *)
                unfold s1''.  unfold ch'.
                eapply set_call_unwind.
                eapply state_upd_chan_unwind.
                eapply chan_append_unwind.
                symmetry.
                (* eauto with unwind can't seem to figure this part out: *)
                eapply chan_low_proj_loweq.
                (* in this spot, could also do:
                eapply chan_low_proj_idempotent.
                 *)
                eauto with unwind.
            + (* ReadChannel *)
                inversion H3; crush.
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                pose proof (state_hidx_to_proj_state_hidx ell _ _ _
                    ltac:(eauto)) as Hch_hidx_s1proj.
                rewrite flows_node_proj in *.
                rewrite flows_chan_proj in *; eauto using ord_trans.
                eexists. exists (n <--- msg).
                split. econstructor; try eauto.
                rewrite <- H1. 
                econstructor; try eauto.
                econstructor; try eauto. 
                unfold s1''. unfold ch'. split.
                eauto with unwind.
                reflexivity. 
                eauto.
            + (* CreateChannel *)
                inversion H3; crush. 
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                rewrite flows_node_proj in *; auto.
                unfold s', s2, s0 in *.
                    (* similar tedious calculation needed here *)
                remember (s_set_call (state_upd_node id (node_add_whan h n)
                    (state_upd_node id (node_add_rhan h n)
                     (state_upd_chan h (new_chan lbl) 
                     (state_low_proj ell s1)))) id c') as s_ex2'.
                     (* s_ex2' is the same as s1'' but replacing s1' with
                     its ell-projection *)
                exists s_ex2', (n ---); repeat split; crush.
                econstructor; eauto.
                rewrite <- H1. 
                econstructor; eauto.
                econstructor; eauto.
                replace (handle_fresh (state_low_proj ell s1))
                    with (handle_fresh s1)
                    by eauto using proj_pres_handle_fresh; auto.
                unfold s1''.
                eauto 6 with unwind.
            + (* CreateNode *)
                inversion H3; crush. 
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                rewrite flows_node_proj in *; auto.
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
                exists s2'', (-- n --); repeat split; crush.
                econstructor; eauto.
                rewrite <- H1.
                econstructor; eauto.
                econstructor; eauto.
                replace (nid_fresh (state_low_proj ell s1))
                    with (nid_fresh s1)
                    by eauto using proj_pres_nid_fresh; eauto.
                unfold s1'', s', s3; subst.
                eauto with unwind.
            +  (* Internal *)
                inversion H3; crush.
                exists (s_set_call (state_low_proj ell s1') id c'), (n ---);
                    repeat split; crush.
                pose proof (state_nidx_to_proj_state_idx ell _ _ _
                    ltac:(eauto)) as Hn_idx_s1proj.
                rewrite flows_node_proj in *; eauto.
                econstructor; eauto.
                rewrite <- H1.
                econstructor; eauto.
                econstructor; eauto.
                unfold s1''.
                eauto with unwind.
        * (* not flowsTo case *)
            rename n0 into Hflows.
            pose proof (unobservable_node_step _ _ _ _ _ _
                ltac:(eauto) H_step_s1_s1' ltac:(eauto))
                as [Hustep Huev].
            exists (state_low_proj ell s1), (empty_event (elbl e1));
                repeat split.
            (* step *)
            constructor.
            (* states leq *)
            pose proof (state_loweq_to_deref_node _ _ _ _ _
                ltac:(eauto) ltac:(eauto)) 
                as [ns1' [Hns1'idx Hns1'leq]].
            unfold s1''. transitivity s1'.
            symmetry. 
            eapply set_call_unobs; eauto.
            erewrite node_low_eq_to_lbl_eq; eauto.
            symmetry; eauto.
            pose proof (state_low_proj_loweq ell s1); congruence.
            (* events leq *)
            congruence.
Qed.

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
                pose proof (uncons_proj_chan_s _ _ _ _ ltac:(eauto))
                    as [ch2 [H_ch'_idx H_ch2_proj]].
                remember (s_set_call (state_upd_chan han (chan_append ch2 msg)
                    (state_upd_node id n'0 s)) id c') as s2''.
                exists s2'', ((node_low_proj ell n') ---> msg); repeat split.
                rewrite flows_node_proj in *; eauto; crush.
                rewrite chan_projection_preserves_lbl in *; eauto.
                (* step *)
                repeat try ((econstructor; eauto) || rewrite <- H1).
                (* s1'' =L s2'' *)
                crush. unfold s1'', ch'. eauto with unwind.
            + (* ReadChannel *)
                inversion H3; crush.
                pose proof (uncons_proj_chan_s _ _ _ _ ltac:(eauto))
                    as [ch2 [H_ch'_idx H_ch2_proj]].
                unfold n'0 in *; crush.
                unfold s1'' in *.
                rewrite flows_node_proj in *; eauto; crush.
                rewrite chan_projection_preserves_lbl in *.
                rewrite flows_chan_proj in *; eauto using ord_trans.
                remember (s_set_call (state_upd_chan han ch'
                   (state_upd_node id (node_get_hans n' msg0)
                    s)) id c') as s2'.
                exists s2'; eexists; repeat split; crush.
                repeat try ((econstructor; eauto) || rewrite <- H1 ||
                    (rewrite flows_chan_proj; eauto using ord_trans)).
                eauto with unwind.
            + (* CreateChannel *)
                inversion H3; crush.
                remember (s_set_call (state_upd_node id (node_add_whan h n')
                    (state_upd_node id (node_add_rhan h n')
                     (state_upd_chan h (new_chan lbl) 
                     s ))) id c') as s2'. 
                unfold s1'', s', s2, s1.
                rewrite flows_node_proj in *; eauto.
                exists s2'; eexists; repeat split; crush.
                repeat try ((econstructor; eauto) || rewrite <- H1).
                erewrite <- proj_pres_handle_fresh; eauto.
                eauto with unwind.
            + (* CreateNode *)
                inversion H3; crush.
                remember (s_set_call
                   (state_upd_node id (node_add_rhan h (node_low_proj ell n'))
                   (state_upd_node new_id
                      {|
                        nlbl := lbl;
                        read_handles := Ensembles.Singleton h;
                        write_handles := Ensembles.Empty_set;
                        ncall := Internal
                      |} s)) id c' ) as s2'.
                unfold s1'', s', s3 in *.
                rewrite flows_node_proj in *; eauto.
                exists s2'; eexists; repeat split; crush.
                repeat try ((econstructor; eauto) || rewrite <- H1).
                erewrite <- proj_pres_nid_fresh; eauto.
                eauto with unwind.
            + (* Internal *)
                inversion H3; crush.
                unfold s1''.
                rewrite flows_node_proj in *; eauto.
                exists (s_set_call s id c'); eexists; repeat split; crush.
                repeat try ((econstructor; eauto) || rewrite <- H1).
                eauto with unwind.
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
Qed.

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
    intros. 
    inversion H; crush.
    -  (* starts from empty trace *)
        exfalso. eapply no_steps_from_empty; eauto.
    - (* non-empty trace *)
        inversion H0; inversion H4; crush.
        pose proof (possibilistic_ni_1step _ s ys s' _
            ltac:(eauto) ltac:(eauto)) as [s2' [e2 [H2step [Hsleq Heleq]]]].
        eexists ((s2', e2) :: (ys, ye) :: t3); repeat split; crush.
        econstructor; crush; eauto. 
        econstructor; crush; eauto.
Qed.

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

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

Local Ltac step_econstruct :=
    repeat match goal with
        | H: _ = ncall _ |- _ => progress rewrite <- H
    end;
    lazymatch goal with
        | |- step_system_ev _ _ _ => econstructor; eauto
        | |- step_node_ev _ _ _ _ _  => econstructor; eauto
        | |- step_system _ _ => econstructor; eauto
        | |- step_node _ _ _ _ => econstructor; eauto
    end.

(* Single step of [crush] *)
Local Ltac crush_step :=
  repeat match goal with
         | _ => progress intros
         | _ => progress subst
         | _ => progress logical_simplify
         | _ => progress step_econstruct
         | H : Some _ = Some _ |- _ => invert_clean H
         | H1 : ?x = Some _, H2 : ?x = Some _ |- _ =>
           rewrite H2 in H1; invert_clean H1
         | _ => reflexivity
         end.
(* General-purpose tactic that simplifies and solves simple goals for
   possibilistic NI. *)
Local Ltac crush := repeat crush_step.

Local Ltac subst_lets :=
  repeat match goal with x := _ |- _ => subst x end.

Local Ltac split_ands :=
  repeat match goal with |- _ /\ _ => split end.

Local Ltac apply_all_constructors :=
  lazymatch goal with
  | |- step_system_ev _ _ _ =>
    eapply SystemEvStepNode; apply_all_constructors
  | |- step_node_ev _ _ _ _ _ =>
    econstructor; apply_all_constructors
  | |- step_node _ _ _ _ =>
    econstructor; apply_all_constructors
  | _ => idtac (* ignore goals that don't match one of the previous patterns *)
  end.

Hint Resolve multi_system_ev_refl multi_system_ev_tran : multi.

(* Hints for [eauto with unwind] *)
Hint Resolve state_upd_chan_unwind chan_append_unwind chan_low_proj_loweq
    chan_low_proj_idempotent state_upd_node_unwind set_call_unwind
    state_upd_chan_unwind state_low_proj_loweq
    state_upd_chan_labeled_unwind
    state_chan_append_labeled_unwind: unwind.
Hint Extern 4 (node_low_eq _ _ _) => reflexivity : unwind.
Hint Extern 4 (chan_low_eq _ _ _) => reflexivity : unwind.
(* meant to be case where we have (cleq ch (proj ch) ) and want to swap order *)
Hint Extern 4 (chan_low_eq _ _ (chan_low_proj _ _)) => symmetry : unwind.
Hint Extern 4 (state_low_eq _ _ (state_low_proj _ _)) => symmetry : unwind.
Hint Extern 2 (chan_low_proj _ _ = chan_low_proj _ _)
=> simple eapply chan_low_proj_loweq : unwind.

Hint Extern 4 (_ <<L lbl (chan_low_proj _ _))
=> (rewrite chan_projection_preserves_lbl) : flowsto.

Definition is_init(t: trace) := length t = 1.

Definition empty_event (ell: level) := Labeled event None ell.

Definition conjecture_possibilistic_ni := forall ell t1_init t2_init t1n,
    (trace_low_eq ell t1_init t2_init) /\
    (is_init t1_init) /\
    (is_init t2_init) /\
    (step_system_ev_multi t1_init t1n) ->
    (exists t2n,
        (step_system_ev_multi t2_init t2n) /\
        (trace_low_eq ell t1n t2n)).

Theorem unobservable_node_step: forall ell s s' e id nl n,
    s.(nodes).[? id] = nl ->
    nl.(obj) = Some n ->
    step_node_ev id n.(ncall) s s' e ->
    ~(lbl nl <<L ell) ->
    (state_low_eq ell s s') /\ (event_low_eq ell e (empty_event e.(lbl))).
Proof.
    intros. inversion H1; (split; [ inversion H5 | ] ); subst_lets; crush.
Admitted.
(*
    - (* WriteChannel; states loweq *) 
        assert ( ~ (lbl (chans s).[? han] <<L ell) ) by eauto using ord_trans.
        eapply state_low_eq_trans.
        eapply (state_upd_node_unobs _ _ _ _ (node_del_rhans (rhs msg) n)
            ltac:(eauto) ltac:(eauto) ltac:(eauto)).
        eapply (state_upd_chan_unobs _
            (state_upd_node id (node_del_rhans (rhs msg) n) s)
            _ _ (chan_append ch msg)
            ltac:(eauto) ltac:(eauto) ltac:(eauto)).
    - (* WriteChannel; events loweq*)
        erewrite <- (nflows_event_proj _ (n ---> msg) ltac:(eauto)).
        unfold event_low_eq. unfold low_eq. 
        erewrite event_low_proj_idempotent. reflexivity.
    - (* ReadChannel; states loweq *)
        pose proof (state_upd_chan_unobs).
        (* This is the part of the proof where
        the label check for destructive updates to the
        channel are needed. See also:
        https://github.com/project-oak/oak/issues/1197#issuecomment-712175755
        *)
        assert ( ~ (clbl ch <<L ell) ) by eauto using ord_trans.
        eapply state_low_eq_trans.
        eapply (state_upd_node_unobs _ _ _ _ (node_get_hans n msg0) 
            ltac:(eauto) ltac:(eauto) ltac:(eauto)).
        eapply state_upd_chan_unobs; eauto.
    - (* ReadChannel; events loweq *)
        erewrite <- (nflows_event_proj _ (n <--- msg) ltac:(eauto)).
        unfold event_low_eq. unfold low_eq.
        erewrite event_low_proj_idempotent. reflexivity.
    -  (* CreateChannel; states loweq *) 
        assert ( ~ (lbl <<L ell) ) by eauto using ord_trans.
        eapply state_low_eq_trans.
        eapply (new_secret_chan_unobs _ _ _ (new_chan lbl) ltac:(eauto)); eauto.
        eapply (state_low_eq_trans _ _ (state_upd_node id (node_add_rhan h n)
            (state_upd_chan h (new_chan lbl) s))).
        eapply state_upd_node_unobs; eauto.
        eapply (state_upd_node_unobs _ _ _ (node_add_rhan h n)); eauto.
        eapply upd_eq.
    - (* CreateNode; states loweq *)
        assert ( ~ (lbl <<L ell) ) by eauto using ord_trans.
        eapply state_low_eq_trans.
        pose proof new_secret_node_unobs.
        eapply (new_secret_node_unobs _ _ new_id
            ( {|
                nlbl := lbl;
                read_handles := Ensembles.Singleton h;
                write_handles := Ensembles.Empty_set;
                ncall := Internal
              |}
            ) ltac:(eauto) ltac:(eauto)).
        eapply state_upd_node_unobs; eauto.
        replace ((nodes
        (state_upd_node new_id
           {|
           nlbl := lbl;
           read_handles := Ensembles.Singleton h;
           write_handles := Ensembles.Empty_set;
           ncall := Internal |} s)).[? id]) with ((nodes s).[? id]).
        eauto. symmetry. eapply upd_neq. 
        destruct (dec_eq_nid new_id id).
            + unfold nid_fresh in *. exfalso. congruence.
            + eauto.
    - (* Internal; events loweq *)
    erewrite <- (nflows_event_proj _ (-- n --) ltac:(eauto)).
    unfold event_low_eq. unfold low_eq.
    erewrite event_low_proj_idempotent. reflexivity.
Qed.
*)



Theorem step_implies_lowproj_steps_leq: forall ell s1 s1' e1,
    (step_system_ev s1 s1' e1) ->
    (exists s2' e2,
        (step_system_ev (state_low_proj ell s1) s2' e2) /\
        (state_low_eq ell s1' s2') /\
        (event_low_eq ell e1 e2)).
Proof.
    intros. inversion H; subst. 
    - (* SystemSkip *)
        exists (state_low_proj ell s1'), (empty_event ell0); repeat try split.
        constructor. all: symmetry; eapply state_low_proj_loweq.
    - (* NodeSetp *)
        rename s' into s1'. rename s'' into s1''. rename H2 into H_step_s1_s1'.
        remember ((nodes s1).[?id]) as nl.
        destruct (nl.(lbl) <<? ell).
        * (* flowsto case *)
            inversion H_step_s1_s1'; crush; remember ((nodes s1).[?id]) as nl;
                pose proof (state_nidx_to_proj_state_idx ell _ _ nl
                    ltac:(eauto)) as Hn_idx_s1proj;
                (erewrite flows_labeled_proj in Hn_idx_s1proj; eauto);
                inversion H3; crush; subst_lets.
                all: try replace n0 with n in * by
                (pose proof (can_split_node_index _ _ _ _ ltac:(eauto));
                    logical_simplify; congruence). 
            (*
                I can't quite get this to work. Coq complains
                about s1 not being found in environment
                all: try rename s1' into s1. 
                    attempt to try SInternal from erroring
                    in following tactic:
                all: try lazymatch goal with
                    | H: (nodes s1).[? id] = _ |- _ =>
                        rewrite H in Hn_idx_s1proj;
                        pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                        logical_simplify
                end.
            *)
            + (* WriteChannel *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                (* step *)
                rewrite H5 in Hn_idx_s1proj;
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                logical_simplify.
                apply_all_constructors; eauto. congruence.
                erewrite state_hidx_to_proj_state_hidx'.
                erewrite low_projection_preserves_lbl.
                eauto.
                (* low-equiv *)
                subst_lets. eauto 7 with unwind.
            + (* ReadChannel *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                (* step *)
                rewrite H5 in Hn_idx_s1proj;
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                logical_simplify.
                apply_all_constructors; eauto. congruence.
                pose proof (state_hidx_to_proj_state_hidx ell _ _ _ ltac:(eauto)).
                assert (nlbl <<L ell) by congruence.  (* the last eauto needs this *)
                rewrite flows_labeled_proj in H12; eauto.
                simpl. eauto using ord_trans.
                (* state low_eq *)
                subst_lets. eauto 6 with unwind.
            + (* CreateChannel *)
                do 2 eexists; split_ands; [ | | reflexivity ]. 
                (* step *)
                rewrite H4 in Hn_idx_s1proj;
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                logical_simplify.
                apply_all_constructors; eauto. congruence.
                (* state loweq *)
                subst_lets. eauto 7 with unwind.
            + (* CreateNode *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                rewrite H5 in Hn_idx_s1proj;
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                logical_simplify.
                apply_all_constructors; eauto. congruence.
                eauto with unwind.
            +  (* Internal *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                eapply SystemEvStepNode; eauto.
                rewrite Hn_idx_s1proj. eauto.
                rewrite <- H1.
                eapply SInternalEv.
                congruence.
                econstructor.
                eauto with unwind.
        * (* not flowsTo case *)
            rename n0 into Hflows.
            pose proof (unobservable_node_step _ _ _ _ _ nl _ ltac:(eauto)
                ltac:(eauto) H_step_s1_s1' ltac:(eauto))
                as [Hustep Huev].
            exists (state_low_proj ell s1), (empty_event (lbl e1)).
            split. crush. split.
            (* states leq *)
            pose proof (state_loweq_to_deref_node _ _ _ _ (nodes s1).[?id]
                ltac:(eauto) ltac:(eauto)) 
                as [ns1' [Hns1'idx Hns1'leq]].
            unfold s1''. transitivity s1'.
            symmetry. 
            eapply set_call_unobs; eauto.
            erewrite node_low_eq_to_lbl_eq; eauto.
            symmetry; eauto.
            erewrite <- Heqnl in Hns1'leq. eapply Hns1'leq.
            pose proof (state_low_proj_loweq ell s1). 
            symmetry. transitivity s1; congruence.
            (* events leq *)
            congruence.
Qed.

Lemma separate_lableled {A} (o : option A) (l : level) (x : labeled) :
  obj x = o -> lbl x = l -> x = Labeled _ o l.
Proof. destruct x; cbn; congruence. Qed.

Ltac separate_hyp T :=
  repeat match goal with
         | H : ?s = Labeled T ?o ?l |- _ =>
           assert (obj s = o /\ lbl s = l) by (rewrite H; tauto);
           clear H; logical_simplify
         end.
Ltac separate_goal := apply separate_lableled.

Lemma invert_chans_state_low_proj_flowsto ell lvl s han :
  lvl <<L ell ->
  lvl <<L (chans (state_low_proj ell s)).[? han].(lbl) ->
  lvl <<L (chans s).[? han].(lbl).
Proof.
  destruct s.
  repeat match goal with
         | _ => progress cbn [state_low_proj
                               RuntimeModel.chans RuntimeModel.lbl ]
         | _ => progress cbv [low_proj chan_state_low_proj fnd]
         | _ => destruct_match
         | _ => tauto
         end.
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
        exists s, (empty_event ell0). split. constructor.
        split. eapply state_low_proj_loweq. reflexivity.
    - (* NodeStep *)
        rename s'' into s1''. rename s' into s1'. rename H2 into H_step_projs_s1'.
        remember ((nodes (state_low_proj ell s)).[? id]) as nl.
        pose proof (uncons_proj_node_s _ _ _ nl ltac:(eauto))
            as [n' [Hidx_n' Hproj_n']].
        destruct (nl.(lbl) <<? ell).
        *
          (* flowsto case*)
            inversion H_step_projs_s1'; inversion H3;
              (rewrite @flows_labeled_proj in *; eauto); crush;
                lazymatch goal with
                | |- _ <<L _ => erewrite <-low_projection_preserves_lbl; rewrite Hproj_n';
                                solve [eauto]
                | _ => idtac
                end.
        + (* WriteChannel *)
          remember (s_set_call (state_chan_append_labeled han msg
                                                          (state_upd_node id n'0 s)) id c') as s2''.
          separate_hyp node.
          eexists s2'', (lbl _ ---> msg). split.
          { crush; try congruence;
              [ separate_goal; eauto; congruence | ].
            rewrite <-Hproj_n' in *.
            eauto using invert_chans_state_low_proj_flowsto. }
          split.
          { crush; subst_lets; eauto with unwind. }
          { crush. congruence. }
        + (* ReadChannel *) admit.
        + (* CreateChannel *) admit.
        + (* CreateNode *) admit.
        + (* Internal *) admit.
          (*
           + (* WriteChannel *)
                pose proof (uncons_proj_chan_s _ _ _ _ ltac:(eauto))
                    as [ch2 [H_ch'_idx H_ch2_proj]].
                remember (s_set_call (state_upd_chan han (chan_append ch2 msg)
                    (state_upd_node id n'0 s)) id c') as s2''.
                exists s2'', (n ---> msg); repeat split.
                crush.
                rewrite chan_projection_preserves_lbl in *; eauto.
                (* s1'' =L s2'' *)
                unfold s1'', ch', n'0. subst. eauto with unwind.
            + (* ReadChannel *)
                pose proof (uncons_proj_chan_s _ _ _ _ ltac:(eauto))
                    as [ch2 [H_ch'_idx H_ch2_proj]].
                remember (s_set_call (state_upd_chan han ch'
                   (state_upd_node id (node_get_hans n msg0)
                    s)) id c') as s2'.
                exists s2'; eexists; repeat split; crush.
                rewrite chan_projection_preserves_lbl in *.
                rewrite flows_chan_proj in *; eauto using ord_trans.
                unfold n'0, s1'' in *.
                eauto with unwind.
            + (* CreateChannel *)
                remember (s_set_call (state_upd_node id (node_add_whan h n)
                    (state_upd_node id (node_add_rhan h n)
                     (state_upd_chan h (new_chan lbl) 
                     s ))) id c') as s2'. 
                exists s2'; eexists; repeat split; crush.
                erewrite <- proj_pres_handle_fresh; eauto.
                unfold s1'', s'0, s3, s2.
                eauto with unwind.
            + (* CreateNode *)
                remember (s_set_call
                   (state_upd_node id (node_add_rhan h n)
                   (state_upd_node new_id
                      {|
                        nlbl := lbl;
                        read_handles := Ensembles.Singleton h;
                        write_handles := Ensembles.Empty_set;
                        ncall := Internal
                      |} s)) id c' ) as s2'.
                exists s2'; eexists; repeat split; crush.
                erewrite <- proj_pres_nid_fresh; eauto.
                unfold s1'', s'0, s4 in *.
                eauto with unwind.
            + (* Internal *)
                unfold s1''.
                exists (s_set_call s id c'); eexists; repeat split; crush.
                eauto with unwind.
        *)
        (* by cases on the command by n in s *)
        * (* not flowsTo case *)
            pose proof (unobservable_node_step _ _ _ _ _ nl _ 
                ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto))
                as [Hustep Huev].
            exists s, (empty_event (lbl e1)); split; [ | split].
            constructor.
            + (* s1'' ={ell} s *)
                apply state_low_eq_sym.
                eapply (state_low_eq_trans _ s s1' s1'').
                eapply (state_low_eq_trans _ s (state_low_proj ell s) s1').
                apply state_low_eq_sym.
                eapply state_low_proj_loweq.
                unfold s1''. 
                subst_lets. congruence.
                assert (H_leq_s_s1': state_low_eq ell s s1'). {
                    eapply (state_low_eq_trans _ s
                        (state_low_proj ell s) s1').
                    apply state_low_eq_sym.
                    eapply state_low_proj_loweq.
                    assumption.
                }
                specialize (state_loweq_to_deref_node ell s s1' id n'
                    Hidx_n' H_leq_s_s1') as [ns1' [Hidx_s1' H_leq_n'_n2]].
                eapply set_call_unobs. eauto.
                replace (lbl ns1') with (lbl n')
                    by (eapply node_low_eq_to_lbl_eq; eassumption).
                admit.
            + (* e1 ={ell} *) assumption.
Admitted.

Theorem state_low_eq_implies_projection_eq: forall ell s1 s2,
    state_low_eq ell s1 s2 ->
    state_low_proj ell s1 = state_low_proj ell s2.
Proof.
    (* Can this be proven without FE ?? *)
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
            (state_low_proj ell s2) in Hstep_s1_s3. assumption. 
            symmetry. eapply state_low_eq_implies_projection_eq; eauto.
            }
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

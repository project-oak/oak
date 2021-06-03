Require Import Coq.Lists.List.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    RuntimeModel
    ModelSemUtils
    EvAugSemantics
    State
    Events
    LowEquivalences
    TraceLowEq
    TraceTheorems
    NIUtilTheorems
    Unwind
    PossibilisticNI_def
    Tactics.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Local Open Scope map_scope.
Local Open Scope ev_notation.

(*
This is a proof that step_system_ev enforces Possibilistic Noninterference
*)

Hint Resolve multi_system_ev_refl multi_system_ev_tran : multi.

(* hints for eauto in event part of the unobservable step proof *)
Hint Extern 4 (low_proj _ _  = _ ) => erewrite nflows_labeled_proj : unobs_ev.
Hint Extern 4 (_  = low_proj _ _ ) => erewrite nflows_labeled_proj : unobs_ev.
Hint Extern 4 (event_low_eq _ _ _) => unfold event_low_eq : unobs_ev.
Hint Extern 4 (low_eq _ _ _) => unfold low_eq : unobs_ev.

Definition empty_event (ell: level) := Labeled event None ell.

Definition trace_low_eq_pni := 
    @trace_low_eq (state_low_eq)(@low_eq event).

Theorem unobservable_node_step: forall ell s s' e id nl n,
    s.(nodes).[? id] = nl ->
    nl.(obj) = Some n ->
    step_node_ev id n.(ncall) s s' e ->
    ~(lbl nl <<L ell) ->
    (state_low_eq ell s s') /\ (event_low_eq ell e (empty_event e.(lbl))).
Proof.
    intros. inversion H1; (split; [ inversion H5 | ] ); subst_lets; crush; 
        eauto with unobs_ev. (* handles all event-low-eq cases: *) 
        all: separate_hyp node; separate_hyp channel.
    - (* WriteChannel *)
        assert (~ nlbl0 <<L ell) by congruence.
        assert ( ~ (lbl (chans s).[? han] <<L ell) ) by eauto using ord_trans.
        eapply state_low_eq_trans.
        eapply state_upd_node_unobs; eauto.
        eapply state_chan_append_labeled_unobs; eauto.
    - (* ReadChannel *)
        assert (~ nlbl0 <<L ell) by congruence.
        assert ( ~ (clbl <<L ell) ) by eauto using ord_trans.
        eapply state_low_eq_trans.
        eapply (state_upd_node_unobs _ _ _  
            (node_get_hans n0 msg0) ltac:(eauto)).
        eapply (state_upd_chan_unobs _ _ _ (chan_pop ch)
            ltac:(eauto)).
        Unshelve. subst. eauto.
    - (* CreateChannel *)
        (* there are no unobservable channel creations, these only happen
        from public *)
        pose proof (bot_is_bot ell).
        rewrite H4 in H2.
        contradiction.
    - (* CreateNode *)
        (* there are no unobservable node creations, these only happen
        from public*)
        pose proof (bot_is_bot ell).
        rewrite H4 in H2.
        contradiction.
    - (* ChannelClose *)
        unfold fnd in *. subst.
        assert (~(lbl (chans s han)) <<L ell) by eauto using ord_trans.
        eapply state_upd_chan_unobs; eauto.
    - (* ChannelLabelRead *)
        inversion H6. subst. reflexivity.
Qed.

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
            inversion H_step_s1_s1'; crush; try remember ((nodes s1).[?id]) as nl;
            pose proof (state_nidx_to_proj_state_idx ell _ _ nl
                ltac:(eauto)) as Hn_idx_s1proj;
            (erewrite flows_labeled_proj in Hn_idx_s1proj; eauto).
            all: lazymatch goal with 
                | H: step_node _ _ _ _ |- _ => inversion H; crush; subst_lets
            end.
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
                eapply proj_labels_increase.
                eauto.
                (* low-equiv *)
                subst_lets. 
                eapply set_call_unwind; eauto.
                eauto 7 with unwind.
            + (* ReadChannel *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                (* step *)
                rewrite H5 in Hn_idx_s1proj.
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj).
                logical_simplify.
                apply_all_constructors; eauto; try congruence.
                pose proof (state_hidx_to_proj_state_hidx ell _ _ _ ltac:(eauto)).
                assert (nlbl <<L ell) by congruence.  (* the last eauto needs this *)
                rewrite flows_labeled_proj in H13; eauto.
                simpl. eauto using ord_trans.
                erewrite <- flows_proj_preserves_channel_valid; eauto.
                separate_hyp node. separate_hyp channel. 
                    (* is there something else I have to do to make 
                    <<? / <<L work better with congruence? *)
                rewrite H16. rewrite H13 in o. eauto using ord_trans.
                (* state low_eq *)
                subst_lets. eauto 6 with unwind.
            + (* CreateChannel *)
                do 2 eexists; split_ands; [ | | reflexivity ]. 
                (* step *)
                rewrite H4 in Hn_idx_s1proj;
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                logical_simplify.
                apply_all_constructors; eauto. congruence.
                erewrite <- proj_preserves_fresh_han; eauto.
                (* state loweq *)
                subst_lets. eauto 7 with unwind.
            + (* CreateNode *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                rewrite H5 in Hn_idx_s1proj;
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                logical_simplify.
                apply_all_constructors; eauto. congruence.
                erewrite <- proj_preserves_fresh_nid; eauto.
                eauto with unwind.
            + (* WaitOnChannels *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                rewrite H4 in Hn_idx_s1proj.
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                logical_simplify.
                (* In this spot apply_all_constructors picks the wrong
                choice of call, so it's a bit manual here *)
                eapply SystemEvStepNode; eauto.
                rewrite <- H1. apply_all_constructors; (eauto; try congruence).
                unfold fnd in *.
                erewrite chan_state_proj_index_assoc2.
                erewrite flows_labeled_proj; eauto.
                pose proof (can_split_chan_index _ _ _ _ ltac:(eauto)).
                logical_simplify. 
                assert (nlbl <<L ell) by congruence.
                unfold fnd in *. rewrite H11. eauto using ord_trans.
                eauto with unwind.
            + (* ChannelClose *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                rewrite H4 in Hn_idx_s1proj.
                pose proof (can_split_node_index _ _ _ _ Hn_idx_s1proj);
                logical_simplify. 
                eapply SystemEvStepNode; eauto.
                rewrite <- H1. apply_all_constructors; (eauto; try congruence).
                erewrite state_hidx_to_proj_state_hidx'.
                eapply proj_labels_increase.
                eauto.
                eauto with unwind.
            + (* NodeLabelRead *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                eapply SystemEvStepNode; (eauto; try congruence).
                rewrite Hn_idx_s1proj. eauto.
                rewrite <- H1. 
                apply_all_constructors; eauto; congruence.
                eauto with unwind.
            +  (* ChannelLabelRead *)
                do 2 eexists; split_ands; [ | | reflexivity ].
                eapply SystemEvStepNode; (eauto; try congruence).
                rewrite Hn_idx_s1proj. eauto.
                rewrite <- H1. 
                apply_all_constructors; (eauto; try congruence).
                unfold fnd. erewrite chan_state_proj_index_assoc2.
                eapply low_projection_preserves_lbl.
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
            rewrite <- Hns1'idx in Hns1'leq.
            eapply low_eq_to_unobs; eauto. 
            congruence.
            pose proof (state_low_proj_loweq ell s1). 
            symmetry. transitivity s1; congruence.
            (* events leq *)
            congruence.
Qed.

Theorem flows_uncons_chan_state_proj: forall ell s han ch,
    lbl (chans (state_low_proj ell s)).[? han] <<L ell ->
    obj (chans (state_low_proj ell s)).[? han] = Some ch ->
    obj (chans s).[? han] = Some ch.
Proof.
    autounfold with loweq. autounfold with structs. simpl.
    intros. destruct_match. destruct (lbl <<? ell);
    (eauto || contradiction).
Qed.

Theorem state_proj_preserves_chan_lbl: forall ell s han,
    lbl (chans (state_low_proj ell s)).[? han] =
    lbl (chans s).[? han].
Proof.
    destruct s. autounfold with loweq. 
    simpl. autounfold with structs.
    intros. destruct_match. 
    destruct (lbl <<? ell); reflexivity.
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
        * (* flowsto case*)
            inversion H_step_projs_s1'; inversion H3.
            all: rewrite @flows_labeled_proj in *; eauto; crush.
            all: erewrite uncons_proj_node_s' in *.
            all: lazymatch goal with
                | H: lbl (low_proj _ _ ) <<L _ |- _ <<L _ =>
                    rewrite <- low_proj_preserves_obs in H; eauto
                | _ => idtac
            end.
            all: separate_hyp node; separate_hyp channel.
            + (* WriteChannel *)
                remember (s_set_call (state_chan_append_labeled han msg
                                        (state_upd_node id n'0 s)) id c') as s2''.
                eexists s2'', (lbl _ ---> msg); split; [ | split].
                { crush; try congruence. 
                    separate_goal; eauto; congruence.
                  rewrite <-Hproj_n' in *.
                  eauto using invert_chans_state_low_proj_flowsto. }
                { crush; subst_lets; eauto with unwind. }
                { crush. congruence. }
            + (* ReadChannel *)
                remember (s_set_call (state_upd_chan han (chan_pop ch)
                   (state_upd_node id (node_get_hans n0 msg0) s)) id c') as s2''.
                eexists s2'', (lbl _ <--- msg).
                split; [ | split].
                subst_lets.
                {
                    crush; try separate_goal; try congruence.
                    all: rewrite <- Hproj_n' in *.
                    all: pose proof (ord_anti _ _ ltac:(eauto) ltac:(eauto)).
                    auto. eapply flows_uncons_chan_state_proj; eauto. congruence.
                    erewrite state_proj_preserves_chan_lbl in *.
                    congruence.
                    erewrite flows_proj_preserves_channel_valid; eauto.
                    erewrite state_hidx_to_proj_state_hidx' in H14.
                    erewrite low_projection_preserves_lbl in H14.
                    eauto using ord_trans.
                }
                { crush; subst_lets; eauto with unwind. }
                { crush. congruence. }
            + (* CreateChannel *)
                subst_lets. rewrite <- Hproj_n' in *.
                remember (s_set_call (state_upd_node id (node_add_whan h n0)
                    (state_upd_node id (node_add_rhan h n0) 
                    (state_upd_chan_labeled h 
                        {| obj := new_chan; lbl := clbl |} s)
                    )) id c') as s2''.
                eexists s2'', (lbl _ ---); split; [| split].
                {
                    crush. separate_goal; eauto. 
                    erewrite proj_preserves_fresh_han; eauto.
                }
                { crush. eauto with unwind. }
                { crush. }
            + (* CreateNode *)
                subst_lets. rewrite <- Hproj_n' in *.
                remember (s_set_call
                    (state_upd_node id (node_add_rhan h n0)
                    (state_upd_node_labeled new_id
                      {| obj := Some
                        {|
                            read_handles := Ensembles.Singleton h;
                            write_handles := Ensembles.Empty_set;
                            ncall := Internal
                        |};
                      lbl := new_lbl 
                      |} s)) id c') as s2''.
                eexists s2'', (-- lbl _ --); split; [| split].
                {
                    crush. separate_goal; eauto.
                    erewrite proj_preserves_fresh_nid; eauto.
                }
                { crush; eauto with unwind. }
                { crush. }
            + (* WaitOnChannels *)
                subst_lets. rewrite <- Hproj_n' in *. 
                eexists (s_set_call s id c'), _; split_ands.
                {
                    crush. separate_goal; eauto.
                    erewrite state_hidx_to_proj_state_hidx' in *.
                    erewrite low_projection_preserves_lbl in *.
                    erewrite flows_labeled_proj in H5.
                    separate_goal. all: eauto using ord_trans.
                }
                { crush; eauto with unwind. }
                { crush. }
            + (* ChannelClose *)
                subst_lets. rewrite <- Hproj_n' in *.
                remember (s_set_call (state_upd_chan han 
                    (chan_close ch) s) id c') as s2''.
                eexists s2'', _; split_ands.
                {
                    crush. separate_goal; eauto.
                    erewrite state_hidx_to_proj_state_hidx' in *.
                    erewrite low_projection_preserves_lbl in H10.
                    eauto.
                }
                { crush; eauto with unwind. }
                { crush. }
            + (* NodeLabelRead *)
                subst_lets. rewrite <- Hproj_n' in *.
                eexists (s_set_call s id c'), _; split_ands.
                all: crush; eauto with unwind.
           + (* ChannelLabelRead *)
                subst_lets. rewrite <- Hproj_n' in *. subst.
                inversion H4; subst.
                eexists (s_set_call s id c'), _; split_ands.
                all: crush; eauto with unwind.
                (* events low-eq: *)
                erewrite state_hidx_to_proj_state_hidx'.
                erewrite low_projection_preserves_lbl.
                reflexivity.
            + (* Internal *)
                subst_lets. rewrite <- Hproj_n' in *.
                eexists (s_set_call s id c'); eexists; split; [| split].
                crush. eauto with unwind. crush.
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
                eapply set_call_unobs.
                rewrite <- Hproj_n' in n0.
                rewrite low_projection_preserves_lbl in n0.
                pose proof (low_eq_to_unobs _ _ _ ltac:(eauto) ltac:(eauto)).
                congruence.
            + (* e1 ={ell} *) assumption.
Qed.

Lemma state_low_equiv_to_proj_chan_fresh ell s1 s2 h :
    state_low_eq ell s1 s2 ->
    fresh_han (state_low_proj ell s2) h ->
    fresh_han (state_low_proj ell s1) h.
Proof.
    unfold fresh_han, fnd, state_low_eq.
    intros. logical_simplify. specialize (H1 h).
    congruence.
Qed.

Lemma state_low_equiv_to_proj_node_fresh ell s1 s2 id :
    state_low_eq ell s1 s2 ->
    fresh_nid (state_low_proj ell s2) id ->
    fresh_nid (state_low_proj ell s1) id.
Proof.
    unfold fresh_nid, fnd, state_low_eq.
    intros. logical_simplify. specialize (H id).
    congruence.
Qed. 

Lemma eq_chan_idx_to_eq_validity: forall s1 s2 han,
    (chans s1).[? han] = (chans s2).[? han] ->
    channel_valid s1 han <-> channel_valid s2 han.
Proof.
    unfold channel_valid. unfold fnd. destruct s1, s2. simpl.
    intros. split. 
    intros. destruct H0 as [ms [lbl H0]].
    eexists. eexists. rewrite <- H. eauto.
    intros. destruct H0 as [ms [lbl H0]].
    eexists. eexists. rewrite H. eauto.
Qed.

Lemma loweq_state_some_chan_validity: forall ell s1 s2 han ch clbl,
    state_low_eq ell s1 s2 ->
    ((chans (state_low_proj ell s1)).[? han] = 
        {| obj := Some ch; lbl := clbl |}) ->
    channel_valid (state_low_proj ell s2) han ->
    channel_valid (state_low_proj ell s1) han.
Proof.
  intros.
  pose proof (state_low_eq_implies_chan_lookup_eq _ _ _ 
  ltac:(eauto) ltac:(eauto)).
  pose proof (eq_chan_idx_to_eq_validity _ _ _ ltac:(eauto)).
  erewrite <-H3. eauto.
Qed.

Lemma step_node_projection ell s1 s2 s3 id c :
  state_low_eq ell s1 s2 ->
  step_node id c (state_low_proj ell s2) s3 ->
  (exists s4, state_low_eq ell s3 s4
         /\ step_node id c (state_low_proj ell s1) s4).
Proof.
  intros Hleq Hstep. pose proof (state_low_eq_sym _ _ _ Hleq).
  invert_clean Hstep; intros.
  all:repeat erewrite (state_low_eq_implies_node_lookup_eq ell s1 s2) in * by eauto.
  all:repeat erewrite (state_low_eq_implies_chan_lookup_eq ell s1 s2) in * by eauto.
  all:eexists; split.
  (* special case for ReadChannel *)
  all:try lazymatch goal with
      | |- step_node _ _ _ _ =>
        econstructor; solve [eauto using 
            state_low_equiv_to_proj_chan_fresh,
            state_low_equiv_to_proj_node_fresh,
            loweq_state_some_chan_validity]
      | _ => subst_lets
      end.
  all:eauto using state_low_eq_projection with unwind.
Qed.

Lemma step_node_ev_projection ell s1 s2 s3 id c e :
  state_low_eq ell s1 s2 ->
  step_node_ev id c (state_low_proj ell s2) s3 e ->
  (exists s4, state_low_eq ell s3 s4
         /\ step_node_ev id c (state_low_proj ell s1) s4 e).
Proof.
  intros Hleq Hstep. invert_clean Hstep; intros.
  all:lazymatch goal with
      | H : step_node _ _ _ _ |- _ =>
        eapply step_node_projection in H; [ | solve [eauto] ]
      end.
  all:logical_simplify.
  all:eexists; split; [ solve [eauto] | econstructor ].
  all:repeat erewrite (state_low_eq_implies_node_lookup_eq ell s1 s2) by eauto.
  all:repeat erewrite (state_low_eq_implies_chan_lookup_eq ell s1 s2) by eauto.
  all:eauto.
Qed.

Lemma step_system_ev_projection ell s1 s2 s3 e :
  state_low_eq ell s1 s2 ->
  step_system_ev (state_low_proj ell s2) s3 e ->
  (exists s4, state_low_eq ell s3 s4
         /\ step_system_ev (state_low_proj ell s1) s4 e).
Proof.
  intros Hleq Hstep. pose proof (state_low_eq_sym _ _ _ Hleq).
  invert_clean Hstep; intros.
  { eexists; split.
    { apply state_low_eq_projection.
      apply state_low_eq_sym; eauto. }
    { econstructor; eauto. } }
  { lazymatch goal with
    | H : step_node_ev _ _ _ _ _ |- _ =>
      eapply step_node_ev_projection in H; [ | solve [eauto] ]
    end.
    logical_simplify. subst_lets.
    eexists; split; eauto; [ | econstructor; eauto ];
      [ solve [eauto with unwind] | ].
    erewrite state_low_eq_implies_node_lookup_eq by eauto.
    eauto. }
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
    eapply step_system_ev_projection in Hstep_s1_s3;
      [ | symmetry; eassumption ].
    logical_simplify.
    match goal with
      | H : step_system_ev (state_low_proj ell s2) _ _ |- _ =>
        apply low_proj_steps_implies_leq_step in H;
          destruct H
          as [s2' [ e2 [Hstep_s2_s2' [H_leq_s3'_s2' H_leq_e3_e2]]]]
    end.
    exists s2', e2. split. assumption. split.
    - eapply state_low_eq_trans; eauto;
        eapply state_low_eq_trans; eauto.
    - eapply event_low_eq_trans; eauto.
Qed.

Theorem possibilistic_ni_unwind_t: forall ell t1 t2 t1',
(trace_low_eq_pni ell t1 t2) ->
(step_system_ev_t t1 t1') ->
(exists t2',
    (step_system_ev_t t2 t2') /\
    (trace_low_eq_pni ell t1' t2')).
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

Theorem possibilistic_ni: (conjecture_possibilistic_ni step_system_ev_multi trace_low_eq_pni).
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

Print Assumptions possibilistic_ni.

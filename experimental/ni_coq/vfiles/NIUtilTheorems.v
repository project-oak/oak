From OakIFC Require Import
        Lattice
        Parameters
        GenericMap
        RuntimeModel
        EvAugSemantics
        Events
        LowEquivalences
        Tactics.
Require Import Coq.Lists.List.
Import ListNotations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* For Transitive, Symmetric *)
Require Import Coq.Classes.RelationClasses.

Local Open Scope map_scope.

Section misc.
Theorem can_split_node_index: forall s id n ell,
    (nodes s).[? id] = {| obj := Some n; lbl := ell |} ->
    (obj (nodes s).[? id] = Some n) /\
    (lbl (nodes s).[? id] = ell).
Proof.
    intros. split; destruct ((nodes s).[? id]).
    - unfold RuntimeModel.obj. inversion H. reflexivity.
    - unfold RuntimeModel.lbl. inversion H. reflexivity.
Qed.

Theorem can_split_chan_index: forall s han ch ell,
    (chans s).[? han] = {| obj := Some ch; lbl := ell|} ->
    (obj (chans s).[? han] = Some ch) /\
    (lbl (chans s).[? han] = ell).
Proof.
  intros. split; destruct ((chans s).[? han]).
  - unfold RuntimeModel.obj. inversion H. reflexivity.
  - unfold RuntimeModel.lbl. inversion H. reflexivity.
Qed.

End misc.

Section low_projection.

Theorem flows_labeled_proj {A: Type}: forall ell (x: @labeled A),
    (lbl x <<L ell) ->
    (low_proj ell x) = x.
Proof.
    intros. destruct x. unfold low_proj. simpl in H.
    destruct (lbl <<? ell); eauto; try contradiction.
Qed.

Theorem nflows_labeled_proj {A: Type}: forall ell (x: @labeled A),
    ~(lbl x <<L ell) ->
    (low_proj ell x) = Labeled A None top.
Proof.
    intros. destruct x. unfold low_proj. simpl in H.
    destruct (lbl <<? ell); eauto; try contradiction.
Qed.

Definition idempotent {A: Type} (f: A -> A) := forall a, f (f a) = f a.

Theorem labeled_low_proj_idempotent {A: Type}:
    forall ell, idempotent (@low_proj A ell).
Proof.
    intros. unfold idempotent. intros x.
    destruct x. unfold low_proj. destruct (lbl <<? ell)  eqn:Hflows.
    rewrite Hflows; eauto. destruct (top <<? ell); reflexivity.
Qed.
  
Definition node_low_proj_idempotent := @labeled_low_proj_idempotent node.
Definition chan_low_proj_idempotent := @labeled_low_proj_idempotent channel.
Definition event_low_proj_idempotent := @labeled_low_proj_idempotent event.

Theorem state_low_proj_idempotent: forall ell, idempotent (state_low_proj ell).
Proof.
Admitted.

Definition low_proj_loweq {A: Type}{a_low_proj: @low_proj_t A}
    {a_low_eq: @low_eq_t A} := forall ell x,
    (a_low_eq ell (a_low_proj ell x) x).

Theorem labeled_low_proj_loweq {A: Type}:
    @low_proj_loweq (@labeled A) low_proj low_eq.
Proof.
    unfold low_proj_loweq. unfold low_eq. unfold low_proj. intros.
    destruct x. destruct (lbl <<? ell) eqn:Hflows.
    rewrite Hflows. reflexivity.
    destruct (top <<? ell); reflexivity.
Qed.

Definition node_low_proj_loweq := @labeled_low_proj_loweq node.
Definition chan_low_proj_loweq := @labeled_low_proj_loweq channel.
Definition event_low_proj_loweq := @labeled_low_proj_loweq event.

Theorem state_low_proj_loweq: 
    @low_proj_loweq state state_low_proj state_low_eq.
Proof.
Admitted.

Theorem proj_labels_increase {A: Type }: forall ell ell' (x: @labeled A),
  ell' <<L x.(lbl) -> ell' <<L (low_proj ell x).(lbl).
  destruct x. cbv [RuntimeModel.lbl]. unfold low_proj. destruct_match.
  intros. eauto. intros. eapply top_is_top.
Qed.

Theorem low_proj_preserves_obs {A: Type}: forall ell (x: @labeled A),
  x.(lbl) <<L ell <-> (low_proj ell x).(lbl) <<L ell.
Proof.
    destruct x. cbv [RuntimeModel.lbl].
    unfold low_proj. split; destruct_match. 
    (* -> *)
    eauto. contradiction.
    (* <- *)
    eauto. intros. pose proof (top_is_top ell).
    replace ell with top by (apply ord_anti; auto).
    apply top_is_top. 
Qed.
    
Theorem uncons_proj_chan_s: forall ell s han ch,
    (chans (state_low_proj ell s)).[? han] = ch ->
    exists ch',
        (chans s).[? han] = ch' /\
        low_proj ell ch' = ch.
Proof.
Admitted.

Theorem uncons_proj_node_s': forall ell s id,
    (nodes (state_low_proj ell s)).[? id] = 
    (low_proj ell (nodes s).[? id]).
Proof.
    unfold state_low_proj. unfold fnd. unfold node_state_low_proj. simpl. intros.
    destruct (lbl (nodes s id) <<? ell); try reflexivity.
Qed.

Theorem uncons_proj_node_s: forall ell s id n,
    (nodes (state_low_proj ell s)).[? id] = n ->
    exists n',
        ((nodes s).[? id] = n') /\
        (low_proj ell n') = n.
Proof.
    intros. rewrite uncons_proj_node_s' in H.
    unfold fnd in *. unfold state_low_proj in *. simpl in *.
    exists (nodes s id); split; eauto.
Qed.

Theorem state_nidx_to_proj_state_idx: forall ell s id n,
    ((nodes s).[? id] = n) ->
    ((nodes (state_low_proj ell s)).[? id] = (low_proj ell n)).
Proof.
Admitted.

Theorem state_hidx_to_proj_state_hidx': forall ell s h,
    (chans (state_low_proj ell s)).[? h] = (low_proj ell (chans s).[?h ]).
Proof.
Admitted.

Theorem state_hidx_to_proj_state_hidx: forall ell s h ch,
    ((chans s).[? h] = ch) ->
    ((chans (state_low_proj ell s)).[? h] = (low_proj ell ch)).
Proof.
Admitted.

(* TODO give better name *)
Theorem proj_node_state_to_proj_n: forall ell s id nl n,
    ((nodes (state_low_proj ell s)).[? id] = nl) ->
    nl.(obj) = Some n ->
    exists nl' n',
        (nodes s).[? id] = nl' /\
        (low_proj ell nl') = nl /\
        nl'.(obj) = Some n'.
Proof.
Admitted.

Theorem proj_preserves_fresh_han: forall ell s h,
    fresh_han s h ->
    fresh_han (state_low_proj ell s) h.
Proof.
    (* depends on concurrent change to def of states, but
    should be true *)
Admitted.

Theorem proj_preserves_fresh_nid: forall ell s id,
    fresh_nid s id ->
    fresh_nid (state_low_proj ell s) id.
Proof.
Admitted.

End low_projection.

Section low_equivalence.

Global Instance node_state_low_eq_refl: forall ell, Reflexive (node_state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance node_state_low_eq_trans: forall ell, Transitive (node_state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance node_state_low_eq_sym: forall ell, Symmetric (node_state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance chan_state_low_eq_refl: forall ell, Reflexive (chan_state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance chan_state_low_eq_trans: forall ell, Transitive (chan_state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance chan_state_low_eq_sym: forall ell, Symmetric (chan_state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance state_low_eq_refl: forall ell, Reflexive (state_low_eq ell) | 10.
Proof. unfold state_low_eq. unfold Reflexive. eauto.  Qed.

Global Instance state_low_eq_trans: forall ell, Transitive (state_low_eq ell) | 10.
Proof. cbv [Transitive state_low_eq]. intros. destruct H, H0. split; congruence. Qed.

Global Instance state_low_eq_sym: forall ell, Symmetric (state_low_eq ell) | 10.
Proof. intros. unfold Symmetric. unfold state_low_eq. intros. destruct H. split; eauto.
Qed.

Global Instance event_low_eq_refl: forall ell, Reflexive (event_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance event_low_eq_trans: forall ell, Transitive (event_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance event_low_eq_sym: forall ell, Symmetric (event_low_eq ell) | 10.
Proof. congruence. Qed.

Theorem state_loweq_from_substates: forall ell s1 s2,
    node_state_low_eq ell (nodes s1) (nodes s2) ->
    chan_state_low_eq ell (chans s1) (chans s2) ->
    state_low_eq ell s1 s2.
Proof.
  intros. unfold state_low_eq. unfold low_eq. unfold state_low_proj. eauto.
Qed.

Theorem state_loweq_to_deref_node: forall ell s1 s2 id n1,
    (nodes s1).[? id] = n1 ->
    (state_low_eq ell s1 s2) ->
    exists n2,
        (nodes s2).[? id] = n2 /\
        (node_low_eq ell n1 n2).
Proof.
    intros. inversion H0. unfold node_state_low_proj in *. 
Admitted. 

Theorem trace_leq_imples_head_st_leq: forall ell t1 t2 s1 s2,
    (head_st t1 = Some s1) ->
    (head_st t2 = Some s2) ->
    (trace_low_eq ell t1 t2) ->
    (state_low_eq ell s1 s2).
Proof.
    inversion 3. 
    - 
        exfalso. rewrite <- H3 in H. inversion H.
    - 
        assert (xs = s1). {
            assert (head_st ((xs, xe) :: t0 ) = Some xs) by reflexivity.
            congruence.
        }

        assert (ys = s2). {
            assert (head_st ((ys, ye) :: t3 ) = Some ys) by reflexivity.
            congruence.
        }
    congruence.
Qed.

End low_equivalence.

Section unobservable.

(* These are theorems that say that when you change a part of a state that is
    not visible to ell the old and new state are ell-equivalent
*)

Theorem set_call_unobs: forall ell s id c,
    ~(lbl (nodes s).[? id] <<L ell) ->
    (state_low_eq ell s (s_set_call s id c)).
Proof.
    intros. unfold fnd in H. split; intros; simpl; subst.
    (* chan_state_low_proj *)
    2: unfold s_set_call, chan_state_low_proj; destruct_match; auto.
    (* node_state_low_proj *)
    unfold node_state_low_proj, s_set_call.
    destruct (dec_eq_nid nid id); subst; destruct_match; try congruence; simpl.
    - (* nid = id, so s_set_call is relevant *)
        rewrite upd_eq. unfold fnd. unfold low_proj.
        destruct_match. simpl. simpl in H0.
        destruct (lbl <<? ell); congruence.
    - (* nid <> id, so s_set_call is irrelevant *)
        rewrite upd_neq; auto.
Qed.

Theorem state_upd_chan_unobs: forall ell s han ch,
    ~(lbl (chans s).[? han] <<L ell) ->
    (state_low_eq ell s (state_upd_chan han ch s)).
Proof.
Admitted.

Theorem state_chan_append_labeled_unobs: forall ell s han msg,
    ~(lbl (chans s).[? han] <<L ell) ->
    (state_low_eq ell s (state_chan_append_labeled han msg s)).
Proof.
Admitted.

Theorem state_upd_node_unobs: forall ell s id n,
    ~(lbl (nodes s).[? id] <<L ell) ->
    (state_low_eq ell s (state_upd_node id n s)).
Proof.
Admitted.
  
End unobservable.

From OakIFC Require Import
        Lattice
        Parameters
        GenericMap
        State
        Events
        ModelSemUtils
        LowEquivalences
        Unfold
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
    intros; split; destruct ((nodes s).[? id]).
    all: autounfold with structs; inversion H; reflexivity.
Qed.

Theorem can_split_chan_index: forall s han ch ell,
    (chans s).[? han] = {| obj := Some ch; lbl := ell|} ->
    (obj (chans s).[? han] = Some ch) /\
    (lbl (chans s).[? han] = ell).
Proof.
  intros; split; destruct ((chans s).[? han]).
  all: autounfold with structs; inversion H; reflexivity.
Qed.

Theorem state_low_eq_parts: forall ell s1 s2,
    node_state_low_eq ell s1.(nodes) s2.(nodes) -> 
    chan_state_low_eq ell s1.(chans) s2.(chans) ->
    state_low_eq ell s1 s2.
Proof.
    autounfold with loweq; intros; eauto.
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
    (low_proj ell x) = Labeled A None (lbl x).
Proof.
    autounfold with loweq. autounfold with structs.
    intros. destruct x. 
    destruct (lbl <<? ell)  eqn:Hflows; congruence.
Qed.

Definition idempotent {A: Type} (f: A -> A) := forall a, f (f a) = f a.

Theorem labeled_low_proj_idempotent {A: Type}:
    forall ell, idempotent (@low_proj A ell).
Proof.
    autounfold with loweq. autounfold with structs. unfold idempotent.
    intros. destruct a. destruct (lbl <<? ell) eqn:Hflows;
    rewrite Hflows; eauto.
Qed.
  
Definition node_low_proj_idempotent := @labeled_low_proj_idempotent node.
Definition chan_low_proj_idempotent := @labeled_low_proj_idempotent channel.
Definition event_low_proj_idempotent := @labeled_low_proj_idempotent event.

(* 
Note that this theorem is not true for the definition where labels are
partially secret
*)
Theorem low_projection_preserves_lbl {A: Type}: forall ell (x: @labeled A),
    (low_proj ell x).(lbl) = x.(lbl).
Proof.
    intros. destruct x. simpl. destruct (lbl <<? ell); auto.
Qed.

Definition node_projection_preserves_lbl :=
    @low_projection_preserves_lbl node.
Definition chan_projection_preserves_lbl := 
    @low_projection_preserves_lbl channel.

Definition low_proj_loweq {A: Type}{a_low_proj: @low_proj_t A}
    {a_low_eq: @low_eq_t A} := forall ell x,
    (a_low_eq ell (a_low_proj ell x) x).

Theorem labeled_low_proj_loweq {A: Type}:
    @low_proj_loweq (@labeled A) low_proj low_eq.
Proof.
    unfold low_proj_loweq. 
    autounfold with loweq. intros.
    destruct x. destruct (lbl <<? ell) eqn:Hflows;
    rewrite Hflows; reflexivity.
Qed.

Definition node_low_proj_loweq := @labeled_low_proj_loweq node.
Definition chan_low_proj_loweq := @labeled_low_proj_loweq channel.
Definition event_low_proj_loweq := @labeled_low_proj_loweq event.

Theorem state_low_proj_loweq: 
    @low_proj_loweq state state_low_proj state_low_eq.
Proof.
    unfold low_proj_loweq.
    autounfold with loweq; autounfold with structs; unfold fnd.
    destruct x. simpl. split. 
    (* node_state *)
    - intros; destruct (nodes nid); destruct (lbl <<? ell) eqn:E;
        (rewrite E; reflexivity).
    (* chan_state *)
    - intros; destruct (chans han); destruct (lbl <<? ell) eqn:E;
        (rewrite E; reflexivity).
Qed.

Theorem proj_labels_increase {A: Type }: forall ell ell' (x: @labeled A),
  ell' <<L x.(lbl) -> ell' <<L (low_proj ell x).(lbl).
  destruct x. cbv [State.lbl]. unfold low_proj. destruct_match.
  intros. eauto. intros. (congruence || eauto with top_is_top).
Qed.

Theorem low_proj_preserves_obs {A: Type}: forall ell (x: @labeled A),
  x.(lbl) <<L ell <-> (low_proj ell x).(lbl) <<L ell.
Proof.
    destruct x. cbv [State.lbl].
    unfold low_proj. split; destruct_match. 
    (* -> *)
    eauto. contradiction.
    (* <- *)
    eauto. intros. pose proof (top_is_top ell).
    (congruence ||   (* label-preserving defs*)
        replace ell with top by (apply ord_anti; auto);  (* partially secret defs *)
        apply top_is_top).
Qed.

Theorem uncons_proj_chan_s': forall ell s han,
    (chans (state_low_proj ell s)).[? han] = 
    (low_proj ell (chans s).[? han]).
Proof.
    autounfold with loweq. unfold fnd. auto.
Qed.
    
Theorem uncons_proj_chan_s: forall ell s han ch,
    (chans (state_low_proj ell s)).[? han] = ch ->
    exists ch',
        (chans s).[? han] = ch' /\
        low_proj ell ch' = ch.
Proof.
    eauto using uncons_proj_chan_s'.
Qed. 

Theorem uncons_proj_node_s': forall ell s id,
    (nodes (state_low_proj ell s)).[? id] = 
    (low_proj ell (nodes s).[? id]).
Proof.
    autounfold with loweq. unfold fnd. auto.
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

Theorem state_nidx_to_proj_state_idx': forall ell s id,
    ((nodes (state_low_proj ell s)).[? id] =
        (low_proj ell (nodes s).[? id])).
Proof.
    autounfold with loweq. autounfold with structs. unfold fnd. auto.
Qed.

Theorem state_nidx_to_proj_state_idx: forall ell s id n,
    ((nodes s).[? id] = n) ->
    ((nodes (state_low_proj ell s)).[? id] = (low_proj ell n)).
Proof.
    intros. rewrite <- H. eapply state_nidx_to_proj_state_idx'.
Qed.

Theorem state_hidx_to_proj_state_hidx': forall ell s h,
    (chans (state_low_proj ell s)).[? h] = (low_proj ell (chans s).[?h ]).
Proof.
    autounfold with loweq.  reflexivity.
Qed.

Theorem state_hidx_to_proj_state_hidx: forall ell s h ch,
    ((chans s).[? h] = ch) ->
    ((chans (state_low_proj ell s)).[? h] = (low_proj ell ch)).
Proof.
    intros. rewrite <- H. eapply state_hidx_to_proj_state_hidx'.
Qed.

Theorem proj_preserves_fresh_han: forall ell s h,
    fresh_han s h <-> 
    fresh_han (state_low_proj ell s) h.
Proof.
    unfold fresh_han. autounfold with loweq. unfold fnd. 
    destruct s. simpl. intros. destruct (chans h).
    split.
    - (* -> *)
        intros. inversion H. destruct (bot <<? ell); reflexivity.
    - (* <- *)
        intros. pose proof (bot_is_bot ell).
        destruct (lbl <<? ell); inversion H; (auto || congruence).
Qed.

Theorem proj_preserves_fresh_nid: forall ell s id,
    fresh_nid s id <->
    fresh_nid (state_low_proj ell s) id.
Proof.
    unfold fresh_nid. autounfold with loweq. unfold fnd.
    destruct s. simpl. intros. destruct (nodes id).
    split.
    - (* -> *)
        intros. inversion H. destruct (bot <<? ell); reflexivity.
    -
        intros. pose proof (bot_is_bot ell).
        destruct (lbl <<? ell); inversion H; (auto || congruence).
Qed.

Theorem flows_proj_preserves_channel_valid: forall ell s h,
    s.(chans).[? h].(lbl) <<L ell ->
    channel_valid s h <-> channel_valid (state_low_proj ell s) h.
Proof.
    unfold channel_valid. autounfold with loweq. unfold fnd. 
    destruct s. intros. simpl in *. destruct (chans h). simpl in *.
    split.
    - (* -> *)
        destruct 1 as [ms [lvl H0]]. inversion H0.
        do 2 eexists. destruct (lvl <<? ell). eauto. congruence.
    - (* <- *)
        destruct 1 as [ms [lvl H0]]. inversion H0.
        do 2 eexists. destruct (lbl <<? ell). eauto. congruence.
Qed.

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

Lemma state_low_eq_implies_node_lookup_eq ell s1 s2 :
  state_low_eq ell s1 s2 ->
  forall id,
    (nodes (state_low_proj ell s2)).[? id]
    = (nodes (state_low_proj ell s1)).[? id].
Proof.
  autounfold with loweq; autounfold with structs; 
  intros; logical_simplify; congruence.
Qed.

Lemma state_low_eq_implies_chan_lookup_eq ell s1 s2 :
  state_low_eq ell s1 s2 ->
  forall han,
    (chans (state_low_proj ell s2)).[? han]
    = (chans (state_low_proj ell s1)).[? han].
Proof.
  autounfold with loweq; autounfold with structs; intros;
  logical_simplify; congruence.
Qed.

Theorem state_loweq_to_deref_node: forall ell s1 s2 id n1,
    (nodes s1).[? id] = n1 ->
    (state_low_eq ell s1 s2) ->
    exists n2,
        (nodes s2).[? id] = n2 /\
        (node_low_eq ell n1 n2).
Proof.
    unfold state_low_eq, node_low_eq. intros. logical_simplify.
    specialize (H0 id). eexists. split.
    eauto using state_low_eq_implies_node_lookup_eq.
    unfold low_eq. rewrite <- H.
    eauto using state_nidx_to_proj_state_idx'.
Qed.

Lemma state_low_eq_projection ell s1 s2 :
  state_low_eq ell s1 s2 ->
  state_low_eq ell (state_low_proj ell s1) (state_low_proj ell s2).
Proof.
  (* I couldn't get autounfold to help here. *)
  cbv [state_low_proj state_low_eq node_state_low_proj chan_state_low_proj fnd].
  cbn [nodes chans]. intros; logical_simplify.
  split; intros; congruence.
Qed.

Lemma invert_chans_state_low_proj_flowsto ell lvl s han :
  lvl <<L ell ->
  lvl <<L (chans (state_low_proj ell s)).[? han].(lbl) ->
  lvl <<L (chans s).[? han].(lbl).
Proof.
  destruct s.
  repeat match goal with
         | _ => progress cbn [state_low_proj
                               State.chans State.lbl ]
         | _ => progress cbv [low_proj chan_state_low_proj fnd]
         | _ => destruct_match
         | _ => tauto
         end.
    (*
    Note: I think this is not true with the low-projection def
    where labels are partially secret
    *)
Qed.

Theorem low_eq_to_unobs {A: Type}: forall ell (x1 x2: @labeled A),
    low_eq ell x1 x2 ->
    ~(x1.(lbl) <<L ell) ->
    ~(x2.(lbl) <<L ell).
Proof.
    destruct x1, x2. cbv [low_eq low_proj State.lbl].
    intros. destruct (lbl <<? ell); destruct (lbl0 <<? ell);
        try eauto; try contradiction. 
    inversion H. unfold not. intros. congruence.
Qed.

Theorem node_state_proj_index_assoc: forall ell ns id,
    (node_state_low_proj ell ns) id = low_proj ell (ns id).
Proof.
    autounfold with loweq. auto.
Qed.

Theorem node_state_proj_index_assoc_form2: forall ell s id,
    nodes (state_low_proj ell s) id = low_proj ell ((nodes s) id).
Proof.
    autounfold with loweq. eauto.
Qed.

Theorem chan_state_proj_index_assoc: forall ell cs han,
    (chan_state_low_proj ell cs) han = low_proj ell (cs han).
Proof.
    autounfold with loweq. auto.
Qed.

Theorem chan_state_proj_index_assoc2: forall ell s han,
    (chans (state_low_proj ell s)) han = low_proj ell ((chans s) han).
Proof.
    autounfold with loweq. auto.
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
        destruct_match. simpl in *.
        destruct (lbl <<? ell); congruence.
    - (* nid <> id, so s_set_call is irrelevant *)
        rewrite upd_neq; auto.
Qed.

Theorem state_upd_chan_unobs: forall ell s han ch,
    ~(lbl (chans s).[? han] <<L ell) ->
    (state_low_eq ell s (state_upd_chan han ch s)).
Proof.
    intros. unfold fnd in H. split; intros; simpl; subst.
    (* node_state_low_proj *) congruence.
    (* chan_state_low_proj *)
    unfold chan_state_low_proj.
    destruct (dec_eq_h han0 han); subst.
    - (* han0 = han *)
        rewrite upd_eq. unfold fnd. unfold low_proj.
        destruct_match. simpl in *.
        destruct (lbl <<? ell); congruence.
    - (* han0 <> han *)
        rewrite upd_neq; auto.
Qed.

Theorem state_chan_append_labeled_unobs: forall ell s han msg,
    ~(lbl (chans s).[? han] <<L ell) ->
    (state_low_eq ell s (state_chan_append_labeled han msg s)).
Proof.
    intros. unfold fnd in H. split; intros; simpl.
    (* node_state_low_proj *) congruence.
    (* chan_state_low_proj *)
    unfold chan_state_low_proj.
    destruct (dec_eq_h han0 han); subst.
    - (* han0 = han *)
        rewrite upd_eq. unfold chan_append_labeled, fnd.
        destruct (chans s han); cbv [State.obj State.lbl] in *.
        destruct_match. simpl. destruct (lbl <<? ell).
        contradiction. congruence. congruence.
    - (* han0 <> han *)
        rewrite upd_neq; auto.
Qed.

Theorem state_upd_node_unobs: forall ell s id n,
    ~(lbl (nodes s).[? id] <<L ell) ->
    (state_low_eq ell s (state_upd_node id n s)).
Proof.
    intros. unfold fnd in H. split; intros; simpl.
    (* chan_state_low_proj *) 2:congruence.
    (* node_state_low_proj *)
    unfold node_state_low_proj.
    destruct (dec_eq_nid nid id); subst.
    - (* nid = id *)
        rewrite upd_eq. unfold fnd, low_proj.
        destruct_match. simpl in *.
        destruct (lbl <<? ell); try congruence.
    - (* nid <> id *)
        rewrite upd_neq; auto.
Qed.

Theorem chan_state_fe: forall ell chs1 chs2,
    (forall h, low_eq ell chs1.[?h] chs2.[?h]) ->
    chan_state_low_eq ell chs1 chs2.
Proof.
    intros. unfold chan_state_low_eq, chan_state_low_proj, low_proj.
    intros. specialize (H han). unfold low_eq in *. 
    unfold low_proj in *. eauto.
Qed.

End unobservable.

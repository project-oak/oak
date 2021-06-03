From OakIFC Require Import
        Lattice
        Parameters
        GenericMap
        State
        Events
        LowEqPS
        ModelSemUtils
        RuntimeModelPS
        Tactics.
Require Import Coq.Lists.List.
Import ListNotations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* For Transitive, Symmetric *)
Require Import Coq.Classes.RelationClasses.

Local Open Scope map_scope.

(*
These are theorems about the low projection definition where labels are
partially secret.
*)

(*
The key difference between what's provable with this definition and the one
in which labels are public is that in the public label definition, we can prove
that low-projection is label preserving. Here that's not true and we rely on
some weaker theorems
    low_proj_preserves_obs
    proj_labels_increase
    low_eq_to_unobs
    ... might be others
*)

(* TODO if these are really both going to live in the code forever, there
must be a better way to refactor these. Lots of redundancy. Might be clearer 
what the differences are when the proofs are really finished *)

Hint Unfold state_low_eq chan_state_low_eq node_state_low_eq event_low_eq
    chan_low_eq node_low_eq low_eq state_low_proj chan_state_low_proj
    node_state_low_proj event_low_proj chan_low_proj node_low_proj
    low_proj: loweq.

Hint Unfold obj lbl fnd: structs.

Section low_projection.

(* These first 3 theorems are weaker than the theorems we can prove
with the other definitions of lowp-proj *)
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

Theorem low_eq_to_unobs {A: Type}: forall ell (x1 x2: @labeled A),
    low_eq ell x1 x2 ->
    ~(x1.(lbl) <<L ell) ->
    ~(x2.(lbl) <<L ell).
Proof.
    destruct x1, x2. cbv [low_eq low_proj State.lbl].
    intros. destruct (lbl <<? ell); destruct (lbl0 <<? ell);
        try eauto; try contradiction. 
    inversion H. unfold not. intros.
    pose proof top_is_top ell. 
    pose proof (ord_anti ell top ltac:(eauto) ltac:(eauto)).
    rewrite H5 in n.
    pose proof top_is_top lbl. contradiction.
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
  destruct x. cbv [State.lbl]. unfold low_proj. destruct_match.
  intros. eauto. intros. eapply top_is_top.
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

Theorem proj_preserves_fresh_han_top: forall ell s h,
    fresh_han_top s h -> (* The normal fresh_han version has <->, but not provable here *)
    fresh_han_top (state_low_proj ell s) h.
Proof.
    unfold fresh_han_top. autounfold with loweq. unfold fnd. 
    destruct s. simpl. intros. destruct (chans h).
    intros. inversion H. destruct (top <<? ell); reflexivity.
Qed.

Theorem proj_preserves_fresh_nid_top: forall ell s id,
    fresh_nid_top s id -> (* The normal fresh_nid version has <->, but not provable here *)
    fresh_nid_top (state_low_proj ell s) id.
Proof.
    unfold fresh_nid_top. autounfold with loweq. unfold fnd.
    destruct s. simpl. intros. destruct (nodes id).
    intros. inversion H. destruct (top <<? ell); reflexivity.
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

(*
The theorems below in low_equivalence are copied from NIUtilTheorems.
The theorem statements and bodies are the same, but use the PS low
projections and PS Hints.
*)

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

Theorem node_state_proj_index_assoc: forall ell ns id,
    (node_state_low_proj ell ns) id = low_proj ell (ns id).
Proof.
    autounfold with loweq. auto.
Qed.

Theorem node_state_proj_index_assoc_form2: forall ell s id,
    nodes (state_low_proj ell s) id = low_proj ell ((nodes s) id).
Proof.
    autounfold with loweq. auto.
Qed.

Theorem chan_state_proj_index_assoc: forall ell cs han,
    (chan_state_low_proj ell cs) han = low_proj ell (cs han).
Proof.
    autounfold with loweq. auto.
Qed.

Theorem chan_state_proj_index_assoc_form2: forall ell s han,
    (chans (state_low_proj ell s)) han = low_proj ell ((chans s) han).
Proof.
    autounfold with loweq. auto.
Qed.

End low_equivalence.

Section misc.

(* These split theorems are generic and could be put somewhere else to be shared. *)

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

Section unobservable.

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

Theorem state_upd_node_labeled_unobs: forall ell s id n_l,
    ~(lbl (nodes s).[? id] <<L ell) ->
    ~(lbl n_l <<L ell) ->
    (state_low_eq ell s (state_upd_node_labeled id n_l s)).
Proof.
    intros. unfold fnd in H. split; intros; simpl.
    (* chan_state_low_proj *) 2:congruence.
    (* node_state_low_proj *)
    unfold node_state_low_proj.
    destruct (dec_eq_nid nid id); subst.
    - (* nid = id *)
        rewrite upd_eq. unfold fnd, low_proj.
        destruct (nodes s id); destruct n_l; cbv [State.lbl] in *.
        destruct_match; destruct_match; try contradiction. congruence.
    - (* nid <> id *)
        rewrite upd_neq; auto.
Qed.

Theorem state_upd_chan_unobs: forall ell s han ch,
    ~(lbl (chans s).[? han] <<L ell) ->
    (state_low_eq ell s (state_upd_chan han ch s)).
Proof.
    intros. unfold fnd in H. split; intros; simpl.
    (* node_state_low_proj *) congruence.
    (* chan_state_low_proj *)
    unfold chan_state_low_proj.
    destruct (dec_eq_h han0 han); subst.
    - (* han0 = han *)
        rewrite upd_eq. unfold fnd, low_proj.
        destruct_match. simpl in *.
        destruct (lbl <<? ell); congruence.
    - (* han0 <> han *)
        rewrite upd_neq; auto.
Qed.

(* TODO(mcswiggen): Possibly this and state_upd_chan_unobs could be combined? *)
Theorem state_upd_chan_labeled_unobs: forall ell s han ch_l,
    ~(lbl (chans s).[? han] <<L ell) ->
    ~(lbl ch_l <<L ell) ->
    (state_low_eq ell s (state_upd_chan_labeled han ch_l s)).
Proof.
    intros. unfold fnd in H. split; intros; simpl.
    (* node_state_low_proj *) congruence.
    (* chan_state_low_proj *)
    unfold chan_state_low_proj.
    destruct (dec_eq_h han0 han); subst.
    - (* han0 = han *)
        rewrite upd_eq. unfold fnd, low_proj.
        destruct (chans s han); destruct ch_l; cbv [State.obj State.lbl] in *.
        destruct_match; destruct_match; try contradiction. congruence.
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

Theorem chan_state_fe: forall ell chs1 chs2,
    (forall h, low_eq ell chs1.[?h] chs2.[?h]) ->
    chan_state_low_eq ell chs1 chs2.
Proof.
    intros. unfold chan_state_low_eq, chan_state_low_proj, low_proj.
    intros. specialize (H han). unfold low_eq in *. 
    unfold low_proj in *. eauto.
Qed.

End unobservable.

(*
Theorem new_secret_chan_unobs: forall ell ell' s h ,
    ~( ell' <<L ell) ->
    fresh_han_top s h ->
    state_low_eq ell s (state_upd_chan_labeled h 
            {| obj := new_chan; lbl := ell'|} s).
Proof.
    cbv [state_low_eq state_low_proj fresh_han_top new_chan]. intros.
    eapply state_low_eq_parts; [cbv [state_upd_chan_labeled]; reflexivity | ].
    eapply chan_state_fe.
    intros. simpl. cbv [low_eq]. destruct s. cbv [State.chans] in *.
    unfold low_proj.
    destruct (dec_eq_h h h0). 
    - rewrite <- e. rewrite H0.
    replace 
        ((chans .[ h <- {| obj := Some {| ms := [] |}; lbl := ell' |}]).[? h])
        with
        ({| obj := Some {| ms := [] |}; lbl := ell' |}) by (symmetry; eapply upd_eq).
    destruct (top <<? ell); destruct (ell' <<? ell); (contradiction || reflexivity).
    -  replace 
        ( (chans .[ h <- {| obj := Some {| ms := [] |}; lbl := ell' |}]).[? h0])
        with
        (chans.[? h0]).
        reflexivity. symmetry. apply upd_neq; auto. 
Qed.
*)

From OakIFC Require Import
        Lattice
        Parameters
        GenericMap
        RuntimeModel
        EvAugSemantics
        Events
        LowEquivalences.
Require Import Coq.Lists.List.
Import ListNotations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* For Transitive, Symmetric *)
Require Import Coq.Classes.RelationClasses.

Local Open Scope map_scope.

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
    intros. destruct x. unfold low_proj. simpl in H.
    destruct (lbl <<? ell); eauto; try contradiction.
Qed.

Theorem proj_pres_handle_fresh: forall ell s,
    handle_fresh (state_low_proj ell s) = handle_fresh s.
Proof.
Admitted.

Theorem proj_pres_nid_fresh: forall ell s,
    nid_fresh (state_low_proj ell s) = nid_fresh s.
Proof.
Admitted.

Definition idempotent {A: Type} (f: A -> A) := forall a, f (f a) = f a.

Theorem labeled_low_proj_idempotent {A: Type}:
    forall ell, idempotent (@low_proj A ell).
Proof.
    intros. unfold idempotent. intros x.
    destruct x. unfold low_proj. destruct (lbl <<? ell)  eqn:Hflows;
    rewrite Hflows; eauto.
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
    destruct x. destruct (lbl <<? ell) eqn:Hflows;
    rewrite Hflows; reflexivity.
Qed.

Definition node_low_proj_loweq := @labeled_low_proj_loweq node.
Definition chan_low_proj_loweq := @labeled_low_proj_loweq channel.
Definition event_low_proj_loweq := @labeled_low_proj_loweq event.

Theorem state_low_proj_loweq: 
    @low_proj_loweq state state_low_proj state_low_eq.
Proof.
Admitted.

Theorem low_projection_preserves_lbl {A: Type}: forall ell (x: @labeled A),
    (low_proj ell x).(lbl) = x.(lbl).
Proof.
    intros. destruct x. simpl. destruct (lbl <<? ell); auto.
Qed.

Definition node_projection_preserves_lbl :=
    @low_projection_preserves_lbl node.
Definition chan_projection_preserves_lbl := 
    @low_projection_preserves_lbl channel.

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
    symmetry; eauto using flows_labeled_proj.
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

Theorem node_projection_preserves_flowsto: forall ell s id n n',
    s.(nodes).[? id] = n ->
    (state_low_proj ell s).(nodes).[? id] = n' ->
    ~(n.(lbl) <<L ell) ->
    ~(n'.(lbl) <<L ell).
Proof.
Admitted.

End low_projection.

Section low_equivalence.

Global Instance state_low_eq_refl: forall ell, Reflexive (state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance state_low_eq_trans: forall ell, Transitive (state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance state_low_eq_sym: forall ell, Symmetric (state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance node_state_low_eq_refl: forall ell, Reflexive (node_state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance node_state_low_eq_trans: forall ell, Transitive (node_state_low_eq ell) | 10.
Proof. congruence. Qed.

Global Instance node_state_low_eq_sym: forall ell, Symmetric (node_state_low_eq ell) | 10.
Proof. congruence. Qed.

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
    intros. unfold state_low_eq. unfold low_eq. unfold state_low_proj. congruence.
Qed.

Theorem state_loweq_to_deref_node: forall ell s1 s2 id n1,
    (nodes s1).[? id] = n1 ->
    (state_low_eq ell s1 s2) ->
    exists n2,
        (nodes s2).[? id] = n2 /\
        (node_low_eq ell n1 n2).
Proof.
    intros. inversion H0. unfold node_state_low_proj in *. 
    match type of H2 with
        ?f = ?g => assert (f id = g id)
    end.
Admitted. 

Theorem node_low_eq_to_lbl_eq: forall ell n1 n2,
    (node_low_eq ell n1 n2) ->
    (n1.(lbl) = n2.(lbl)).
Proof.
    intros. inversion H.
    assert ( lbl (low_proj ell n1) = lbl (low_proj ell n2)).
    rewrite H1. reflexivity.
    rewrite !node_projection_preserves_lbl in H0.
    assumption.
Qed.

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

Theorem set_call_unobs: forall ell s id n c,
    (nodes s).[? id] = n ->
    ~(lbl n <<L ell) ->
    (state_low_eq ell s (s_set_call s id c)).
Proof.
Admitted.

Theorem state_upd_chan_unobs: forall ell s han ch ch',
    (chans s).[? han] = ch ->
    ~(lbl ch <<L ell) ->
    (state_low_eq ell s (state_upd_chan han ch' s)).
Proof.
Admitted.

Theorem state_upd_node_unobs: forall ell s id n n',
    (nodes s).[? id] = n ->
    ~(lbl n <<L ell) ->
    (state_low_eq ell s (state_upd_node id n' s)).
Proof.
Admitted.

End unobservable.

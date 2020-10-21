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

Section misc_theorems.

Theorem eq_nodes_have_eq_lbls: forall n1 n2,
    n1 = n2 -> (nlbl n1) = (nlbl n2).
Proof. congruence. Qed.

Theorem state_upd_node_eq: forall id n s,
    (state_upd_node id n s).(nodes).[? id] = Some n.
Proof.
    intros. eapply upd_eq.
Qed.

Theorem state_upd_node_neq: forall (id id': node_id) n s,
    id' <> id ->
    (state_upd_node id n s).(nodes).[?id'] = s.(nodes).[?id'].
Proof.
    intros. eapply upd_neq. congruence.
Qed.

End misc_theorems.

Section low_projection.

Theorem flows_node_proj: forall ell n,
    (nlbl n <<L ell) ->
    (node_low_proj ell n) = n.
Proof.
    intros. unfold node_low_proj. destruct (nlbl n <<? ell). reflexivity.
    contradiction.
Qed.

Theorem nflows_node_proj: forall ell n,
    ~(nlbl n <<L ell) ->
    (node_low_proj ell n) = (empty_node n.(nlbl)).
Proof.
    intros. unfold node_low_proj. destruct (nlbl n <<? ell). contradiction.
    reflexivity.
Qed.

Theorem flows_chan_proj: forall ell ch,
    (clbl ch <<L ell) ->
    (chan_low_proj ell ch) = ch.
Proof.
Admitted.


Theorem nflows_event_proj: forall ell e,
    ~(elbl e <<L ell) ->
    (event_low_proj ell e) = empty_event e.(elbl).
Proof.
    intros. unfold event_low_proj. destruct (elbl e <<? ell); eauto. contradiction.
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

Theorem node_low_proj_idempotent: forall ell, idempotent (node_low_proj ell).
Proof. 
    intros. unfold idempotent. intros n.
    unfold node_low_proj. destruct (nlbl n <<? ell) eqn:Hflows.
    - (* flows *)
        rewrite Hflows. reflexivity.
    - (* not flows *) 
        replace (nlbl (empty_node (nlbl n))) with (nlbl n) by auto.
        rewrite Hflows. reflexivity.
Qed.

Theorem chan_low_proj_idempotent: forall ell, idempotent (chan_low_proj ell).
    intros. unfold idempotent. intros ch.
    unfold chan_low_proj. destruct (clbl ch <<? ell) eqn:Hflows.
    - (* flows *)
        rewrite Hflows. reflexivity.
    - (* not flows *) 
        replace (clbl (empty_chan (clbl ch))) with (clbl ch) by auto.
        rewrite Hflows. reflexivity.
Qed.

Theorem state_low_proj_idempotent: forall ell, idempotent (state_low_proj ell).
Proof.
Admitted.

Theorem event_low_proj_idempotent: forall ell, idempotent (event_low_proj ell).
Proof.
Admitted.

Theorem state_low_proj_loweq: forall ell s,
    (state_low_eq ell (state_low_proj ell s) s).
Proof.
Admitted.

Theorem node_low_proj_loweq: forall ell n,
    (node_low_eq ell (node_low_proj ell n) n).
Proof.
    intros. unfold node_low_eq. unfold low_eq. unfold node_low_proj.
    destruct (nlbl n <<? ell) eqn:Hflows. rewrite Hflows. reflexivity.
    replace (nlbl (empty_node (nlbl n))) with (nlbl n) by auto.
    rewrite Hflows. reflexivity.
Qed.

Theorem chan_low_proj_loweq: forall ell ch,
    (chan_low_eq ell (chan_low_proj ell ch) ch).
Proof.
    intros. unfold chan_low_eq. unfold low_eq. unfold chan_low_proj.
    destruct (clbl ch <<? ell) eqn:Hflows. rewrite Hflows. reflexivity.
    replace (clbl (empty_chan (clbl ch))) with (clbl ch) by auto.
    rewrite Hflows. reflexivity.
Qed.

Theorem node_projection_preserves_lbl: forall ell n,
    ((node_low_proj ell n).(nlbl) = n.(nlbl)).
Proof.
    intros. unfold node_low_proj. destruct (nlbl n <<? ell).
    reflexivity. auto.
Qed.

Theorem chan_projection_preserves_lbl: forall ell ch,
    (clbl (chan_low_proj ell ch)) = clbl ch.
Proof.
    intros. unfold chan_low_proj. destruct (clbl ch <<? ell).
    reflexivity. auto.
Qed.

Theorem uncons_proj_chan_s: forall ell s han ch,
    (chans (state_low_proj ell s)).[? han] = Some ch ->
    exists ch',
         (chans s).[? han] = Some ch' /\
        chan_low_proj ell ch' = ch.
Proof.
Admitted. (* WIP *)

Theorem state_nidx_to_proj_state_idx: forall ell s id n,
    ((nodes s).[? id] = Some n) ->
    ((nodes (state_low_proj ell s)).[? id] = Some (node_low_proj ell n)).
Proof.
Admitted.

Theorem state_hidx_to_proj_state_hidx: forall ell s h ch,
    ((chans s).[? h] = Some ch) ->
    ((chans (state_low_proj ell s)).[? h] = Some (chan_low_proj ell ch)).
Proof.
Admitted.

Theorem proj_node_state_to_proj_n: forall ell s id n,
    ((nodes (state_low_proj ell s)).[? id] = Some n) ->
    exists n',
        ((nodes s).[? id] = Some n') /\
        (node_low_proj ell n') = n.
Proof.
    (* XXX *)
    (* This is no longer true, I think *)
Admitted.

Theorem node_projection_preserves_flowsto: forall ell s id n n',
    s.(nodes).[? id] = Some n ->
    (state_low_proj ell s).(nodes).[? id] = Some n' ->
    ~(n.(nlbl) <<L ell) ->
    ~(n'.(nlbl) <<L ell).
Proof.
    (*
    intros. unfold state_low_proj in *. cbn in H0.  unfold node_state_low_proj in H0.
    destruct (nodes s id) eqn: E in H0. 
        - (* some *) 
        replace n0 with n in *.
        erewrite nflows_node_proj in H0. inversion H0. auto. auto.
        replace (nodes s id) with ((nodes s).[? id]) in E by auto.
        congruence.
    *)
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
    (nodes s1).[? id] = Some n1 ->
    (state_low_eq ell s1 s2) ->
    exists n2,
        (nodes s2).[? id] = Some n2 /\
        (node_low_eq ell n1 n2).
Proof.
    intros. inversion H0. unfold node_state_low_proj in *. 
    match type of H2 with
        ?f = ?g => assert (f id = g id)
    end.
Admitted. 

Theorem node_low_eq_to_lbl_eq: forall ell n1 n2,
    (node_low_eq ell n1 n2) ->
    (n1.(nlbl) = n2.(nlbl)).
Proof.
    intros. inversion H.
    assert ( nlbl (node_low_proj ell n1) = nlbl (node_low_proj ell n2)).
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

Theorem trace_loweq_to_deref_node: forall ell t1 t2 id s1 n1,
(* If two traces are low-equivalent and in the first trace:
    - the head element has some state (it's not an emty trace)
    - and in the head state, id can be dereferenced to some node
    then:
    - there must be some head state in the other trace (s2)
    - and we must be able to also dereference id in s2 to some node 
Mostly, this is just a consequence of the def of trace-low-equivalence.
*)
    (trace_low_eq ell t1 t2) ->
    (head_st t1 = Some s1) ->
    ((nodes s1).[? id] = Some n1) ->
    (exists s2 n2,
        head_st t2 = Some s2 /\ 
        (nodes s2).[? id] = Some n2 ).
Proof.
    intros.
    destruct (head_st t2) eqn:Ht2head.
    - (* some s *)
        destruct (nodes s).[? id] eqn:Hsid.
            + (* some n *)
                exists s. exists n.
                split; (reflexivity || assumption).
            + (* none *)
                inversion H; subst.
                * (* t1 = [] and t2 = [] *) discriminate H0.
                * exfalso. inversion H4; subst. simpl in Ht2head.
                admit. 
                (* 
                 unfold node_state_low_eq in H5.
                 inversion Ht2head. rewrite H8 in H5. specialize (H5 id).
                 rewrite Hsid in H5. simpl in H0. inversion H0.
                 rewrite H9, H1 in H5. assumption.
                *)
    - (* none *)
        inversion H; subst. 
            + discriminate H0.
            + inversion Ht2head.
Admitted. (* WIP *)

End low_equivalence.

Section unobservable.

(* These are theorems that say that when you change a part of a state that is
    not visible to ell the old and new state are ell-equivalent
*)

Theorem set_call_unobs: forall ell s id n c,
    (nodes s).[? id] = Some n ->
    ~(nlbl n <<L ell) ->
    (state_low_eq ell s (s_set_call s id c)).
Proof.
Admitted.

Theorem state_upd_chan_unobs: forall ell s han ch ch',
    (chans s).[? han] = Some ch ->
    ~(clbl ch <<L ell) ->
    (clbl ch = clbl ch') ->
    (state_low_eq ell s (state_upd_chan han ch' s)).
Proof.
Admitted.

Theorem state_upd_node_unobs: forall ell s id n n',
    (nodes s).[? id] = Some n ->
    ~(nlbl n <<L ell) ->
    (nlbl n = nlbl n') ->
    (state_low_eq ell s (state_upd_node id n' s)).
Proof.
Admitted.

Theorem new_secret_node_unobs: forall ell s id n,
    (nodes s).[? id] = None ->
    ~(nlbl n <<L ell) ->
    (state_low_eq ell s (state_upd_node id n s)).
Proof.
Admitted.

Theorem new_secret_chan_unobs: forall ell s han ch,
    (chans s).[? han] = None ->
    ~(clbl ch <<L ell) ->
    (state_low_eq ell s (state_upd_chan han ch s)).
Proof.
Admitted.

End unobservable.

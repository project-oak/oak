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

Local Open Scope map_scope.

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
            assert (head_st ((xs, xe) :: t0 ) = Some xs).
            reflexivity. congruence.
        }
        assert (ys = s2). {
            assert (head_st ((ys, ye) :: t3 ) = Some ys).
            reflexivity. congruence.
        }
    congruence.
Qed.

Theorem flows_uncons_proj: forall ell n,
    (nlbl n <<L ell) ->
    (node_low_proj ell n) = n.
Proof.
    intros. unfold node_low_proj. destruct (nlbl n <<? ell). reflexivity.
    contradiction.
Qed.

Theorem nflows_uncons_proj: forall ell n,
    ~(nlbl n <<L ell) ->
    (node_low_proj ell n) = (empty_node n.(nlbl)).
Proof.
    intros. unfold node_low_proj. destruct (nlbl n <<? ell). contradiction.
    reflexivity.
Qed.

Theorem state_leq_and_flowsto_to_node_eq: forall ell s1 s2 id n1 n2,
    (nodes s1).[? id] = Some n1 ->
    (nodes s2).[? id] = Some n2 ->
    (state_low_eq ell s1 s2) -> 
    (nlbl n1 <<L ell) ->
    n1 = n2.
Proof.
    (*
    intros.
    inversion H1. specialize (H3 id). rewrite H, H0 in H3. inversion H3.
    assert (nlbl n2 <<L ell). destruct (nlbl n2 <<? ell).
    assumption. rewrite flows_uncons_proj in H6. rewrite nflows_uncons_proj in H6.
    *)
Admitted.  (* WIP *)

Theorem state_upd_chan_preserves_node_state_leq:
    forall ell s1 s2 han1 ch1 han2 ch2,
    node_state_low_eq ell (nodes s1) (nodes s2) ->
    node_state_low_eq ell
        (nodes (state_upd_chan han1 ch1 s1))
        (nodes (state_upd_chan han2 ch2 s2)).
Proof.
Admitted. (* WIP // TODO *)

Theorem state_upd_node_preserves_chan_state_leq:
    forall ell s1 s2 id1 id2 n1 n2,
    chan_state_low_eq ell (chans s1) (chans s2) ->
    chan_state_low_eq ell
        (chans (state_upd_node id1 n1 s1))
        (chans (state_upd_node id2 n2 s2)).
Proof.
Admitted. (* WIP // TODO *)

Theorem leq_node_updates_preserve_node_state_leq:
    forall ell s1 s2 n1 n2 id,
    node_state_low_eq ell (nodes s1) (nodes s2) ->
    node_low_eq ell n1 n2 ->
    node_state_low_eq ell
        (nodes (state_upd_node id n1 s1)) (nodes (state_upd_node id n2 s2)).
Proof.
Admitted. (* WIP // TODO *)

Theorem leq_chan_updates_preserve_chan_state_leq:
    forall ell s1 s2 ch1 ch2 han,
    chan_state_low_eq ell (chans s1) (chans s2) ->
    chan_low_eq ell ch1 ch2 ->
    chan_state_low_eq ell
        (chans (state_upd_chan han ch1 s1)) (chans (state_upd_chan han ch2 s2)).
Proof.
Admitted. (* WIP // TODO *)

Theorem node_low_eq_reflexive:
    forall ell n, node_low_eq ell n n.
Proof.
Admitted. (* WIP // TODO *)

Theorem other_chan_exists_from_chans_leq: forall ell s1 s2 han ch1,
    chan_state_low_eq ell (chans s1) (chans s2) ->
    (chans s1).[? han] = Some ch1 ->
    exists ch2, ((chans s2).[? han ] = Some ch2) /\
        (chan_low_eq ell ch1 ch2).
Proof.
Admitted. (* WIP // TODO *)

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


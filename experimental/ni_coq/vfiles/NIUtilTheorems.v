From OakIFC Require Import
        RuntimeModel
        Parameters
        LowEquivalences
        GenericMap.
Require Import Coq.Lists.List.
Import ListNotations.

Theorem chan_upd_preserves_nodes: forall h ch s,
    (state_upd_chan h ch s).(nodes) = s.(nodes).
Proof.
    intros; simpl; reflexivity.
Qed.

Theorem chan_append_unwind: forall ell m ch1 ch2,
    (chan_low_eq ell ch1 ch2) ->
    (chan_low_eq ell (chan_append ch1 m) (chan_append ch2 m)). 
Proof.
    intros. inversion H. 
    constructor. rewrite H0. reflexivity.
    constructor 2.
    apply H1. apply H2.
Qed. 

Theorem leq_ch_upd_preserves_sleq: forall (ell: level)
    (h:handle)(ch1 ch2: channel)(s1 s2:state),
    (chan_low_eq ell ch1 ch2) ->
    (state_low_eq ell s1 s2) ->
    (state_low_eq ell 
        (state_upd_chan h ch1 s1)
        (state_upd_chan h ch2 s2)).
Proof.
    intros.
    inversion H.
        (* ch1 = ch2 *)
        - rewrite H1. unfold state_low_eq. split.
            (* node_state *)
            rewrite chan_upd_preserves_nodes.
            rewrite chan_upd_preserves_nodes.
            apply H0.
            (* chan_state *)
            unfold chan_state_low_eq. intros.
            destruct (dec_eq_h h h0).
                (* h = h0 *)
                + rewrite e. unfold state_upd_chan.
                simpl. rewrite upd_eq. rewrite upd_eq.
                constructor. reflexivity.
                (* h <> h0 *)
                + unfold state_upd_chan. simpl. 
                rewrite upd_neq. rewrite upd_neq.
                apply H0. apply n. apply n.
        (* ~(ch1.l flowsTo ell) /\ ~(ch2.l flowsTo ell) *)
        - unfold state_low_eq. split.
            (* node_state *)
            rewrite chan_upd_preserves_nodes.
            rewrite chan_upd_preserves_nodes.
            apply H0.
            (* chan_state *)
            unfold chan_state_low_eq. intros. destruct (dec_eq_h h h0).
                (* h = h0 *)
                + rewrite e. unfold state_upd_chan. simpl.
                rewrite upd_eq. rewrite upd_eq.
                constructor 2. apply H1. apply H2.
                (* h <> h0 *)
                + unfold state_upd_chan. simpl. 
                rewrite upd_neq. rewrite upd_neq.
                apply H0. apply n. apply n.
Qed.

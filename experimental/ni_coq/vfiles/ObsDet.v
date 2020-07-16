Require Import OakIFC.RuntimeModel.
Require Import OakIFC.Parameters.
Require Import OakIFC.LowEquivalences.
Require Import Coq.Lists.List.
Require Import OakIFC.GenericMap.
Import ListNotations.

Inductive valid_trace: trace -> Prop :=
    | VTOne s: (valid_trace (s :: nil) )
    | VTAdd s s' t
            (H0: valid_trace  (s :: t) )
            (H1: step_system s s'):
            (valid_trace (s' :: (s :: t))).

Definition observational_determinism: Prop :=
    forall (ell: level) (s1 s2: state) (t1 t2: trace), 
        [s1] = (tl t1) ->
        [s2] = (tl t2) ->
        valid_trace t1 ->
        valid_trace t2 ->
        (state_low_eq ell s1 s2) ->
        (trace_low_eq ell t1 t2).

Theorem chan_upd_preserves_nodes: forall h ch s,
    (state_upd_chan h ch s).(nodes) = s.(nodes).
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

Theorem low_eq_step: forall (ell: level)(s1 s2 s1' s2': state)
        (n: node_id)(c: call),
    (state_low_eq ell s1 s2) ->
    (step_call n c s1 s1') ->
    (step_call n c s2 s2') ->
    (state_low_eq ell s1' s2').
Proof.
    intros.
    destruct c.
    - inversion H0. inversion H1.
    apply leq_ch_upd_preserves_sleq.
    apply chan_append_unwind.
    apply H. apply H.
    - inversion H0. 
Qed.

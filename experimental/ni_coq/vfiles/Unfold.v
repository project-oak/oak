From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    State
    Events
    ModelSemUtils
    RuntimeModel
    LowEquivalences.

(* so far the proofs haven't wanted to unfold state elements deeper than this*)
Hint Unfold obj lbl fnd: structs.

Hint Unfold state_low_eq chan_state_low_eq node_state_low_eq event_low_eq
    chan_low_eq node_low_eq low_eq state_low_proj chan_state_low_proj
    node_state_low_proj event_low_proj chan_low_proj node_low_proj
    low_proj: loweq.

Hint Unfold chan_append chan_pop msg_is_head node_get_hans state_upd_node
    state_upd_node_labeled state_upd_chan state_upd_chan_labeled
    chan_append_labeled state_chan_append_labeled node_add_rhan
    node_add_whan node_del_rhan node_del_rhans new_chan fresh_han fresh_nid
    s_set_call: semutils.


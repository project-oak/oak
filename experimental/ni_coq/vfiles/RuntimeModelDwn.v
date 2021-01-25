Require Import List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    State
    ModelSemUtils.

(* This file is the top-level model of the Oak runtime *)

(* RecordUpdate is a conveninece feature that provides functional updates for
* records with notation: https://github.com/tchajed/coq-record-update *)
(* To work with record updates from this library in proofs "unfold set" quickly
* changes goals back to normal Coq built-in record updates *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Local Open Scope map_scope.


(* Ensembles don't have implicit type params and these lines fix that *)
Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.
Arguments Ensembles.Union {U}.
Arguments Ensembles.Setminus {U}.
Arguments Ensembles.Included {U}.

(*============================================================================
* Single Call Semantics
============================================================================*)

(* step for a single node (which can be thought of as a thread) executing
* a particular call *)
(* It might be akwkard looking that the call of a node is a part of the object,
but that there is no premise checking that this call is really the one used
in the relation. This is checked in the global transition relation just below.
*)
Inductive step_node (id: node_id): call -> state -> state -> Prop :=
    | SWriteChan s n nlbl han clbl msg:
        (s.(nodes).[?id]) = Labeled node (Some n) nlbl ->
            (* caller is a real node with label nlbl *)
        (s.(chans).[? han]).(lbl) = clbl ->
            (* the handle has label clbl, though the call does not
            check whether or not a channel is allocated to the handle
            to avoid leaks (it can be Some or None) *)
        In n.(write_handles) han ->     (* caller has write handle *)
        nlbl <<L clbl ->     (* label of caller flowsTo label of ch*)
        Included msg.(rhs) n.(read_handles) ->
            (* caller has read handles it is sending *)
        Included msg.(whs) n.(write_handles) ->
            (* caller has write handles it is sending *)
        let n' := node_del_rhans msg.(rhs) n in 
            (* remove the read handles from the sender because read
            * handles (but not write handles) are linear *)
        let s0 := state_upd_node id n' s in
            (* NOTE: throwing an error if the channel is not valid would cause
            a leak. It might be possible to still prove NI if the write call
            always proceeds regarldess of validity but only pushes to the 
            validity, but only append the message if *)
        step_node id (WriteChannel han msg) s 
            (state_chan_append_labeled han msg (state_upd_node id n' s))
    | SWriteChanDwn s n nlbl han clbl msg ell':
        (s.(nodes).[? id]) = Labeled node (Some n) nlbl ->
            (* caller is a real node with label nlbl *)
        (s.(chans).[? han]).(lbl) = clbl ->
            (* the handle has label clbl, though the call does not
            check whether or not a channel is allocated to the handle
            to avoid leaks (it can be Some or None) *)
        In n.(write_handles) han ->     (* caller has write handle *)
        Included msg.(rhs) n.(read_handles) ->
            (* caller has read handles it is sending *)
        Included msg.(whs) n.(write_handles) ->
            (* caller has write handles it is sending *)
        let n' := node_del_rhans msg.(rhs) n in 
            (* remove the read handles from the sender because read
            * handles (but not write handles) are linear *)
        let s0 := state_upd_node id n' s in
            (* NOTE: throwing an error if the channel is not valid would cause
            a leak. It might be possible to still prove NI if the write call
            always proceeds regarldess of validity but only pushes to the 
            validity, but only append the message if *)
        step_node id (WriteChannelDown han msg ell') s 
            (state_chan_append_labeled han msg (state_upd_node id n' s))
    | SReadChan s n nlbl han ch clbl msg:
        (s.(nodes).[?id]) = Labeled node (Some n) nlbl ->
            (* caller is a real node with label nlbl *)
        (s.(chans).[?han]) = Labeled channel (Some ch) clbl ->  
            (* handle points to real channel ch  with label clbl*)
        In n.(read_handles) han ->   (* caller has read handle *)
            (* A channel read happens only when there is a message
            available in the channel. TODO, re-check what really happens
            when a message is not available, and possibly improve the model.
            E.g., if an error is thrown, execute an error continuation instead
            of the usual one if an error is _not_ thrown.
            *)
        (msg_is_head ch msg) ->
        channel_valid s han ->
            (* the channel being read is not closed *)
        clbl <<L nlbl ->
            (* label of channel flowsTo label of caller. 
                checks that reading the message is safe
             *)
        nlbl <<L clbl -> 
            (* label of caller flowsTo label of ch. This check is less intuitive than the above.
            However, reads are destructive because the channel is popped, so the calling node
            is effectively doing a write to the channel. Any node that does a subsequent read
            can detect whether or not the channel has been read because its contents may have 
            been changed. This check rules out this more subtle leak *)
        let n' := node_get_hans n msg in
            (* node gets handles from channel *)
        let ch' := chan_pop ch in
            (* pop the message, clear the read/write handles in ch *)
        step_node id (ReadChannel han) s
            (state_upd_chan han ch' (state_upd_node id n' s))
    | SCreateChan s n nlbl h clbl:
        (s.(nodes).[?id]) = Labeled node (Some n) nlbl ->
            (* caller is a real node with label nlbl *)
        fresh_han s h ->
            (* the target handle is not in use *)
        nlbl = bot ->
            (* only public/trusted nodes can create channels, for now *)
            let s0 := (state_upd_chan_labeled h {|
                obj := new_chan; lbl := clbl;
            |} s) in
            let s1 := state_upd_node id (node_add_rhan h n) s0 in
            let s' := state_upd_node id (node_add_whan h n) s1 in
            step_node id (CreateChannel clbl) s s'
    | SCreateNode s n nlbl new_id new_lbl h:
        (s.(nodes).[?id]) = Labeled node (Some n) nlbl ->
            (* caller is a real node with label nlbl *)
        fresh_nid s id ->
            (* target nid is not in use *)
        nlbl = bot ->
            (* only public/trusted nodes can create nodes for now *)
            (* create new node with read handle *)
        let s0 := (state_upd_node_labeled new_id {|
                obj := Some {|
                    read_handles := (Singleton h);
                    write_handles := Empty_set handle;
                    ncall := Internal;
                |};
                lbl := new_lbl;
            |} s) in
        let s' := state_upd_node id (node_add_rhan h n) s0 in
        step_node id (CreateNode new_lbl h) s s'
    | SWaitOnChannels s n hs h ms nlbl clbl:
        (s.(nodes).[?id]) = Labeled node (Some n) nlbl ->
            (* caller is a real node with label nlbl *)
        In hs h->
            (* there is some handle h in the list of handles s.t. ... *)
        s.(chans).[?h] = Labeled channel (Some (Chan ValidChannel ms)) clbl ->
            (* It points to a valid channel s.t. ... *)
        length ms > 0  -> (* it has some pending message and ... *)
        clbl <<L nlbl -> (* its label flows to the label of the node *)
            (* an alternative way to do this would be to check that the
            the labels of all the channels in the list flowTo the label
            of the node before blocking. This specification is implied
            by that other one. *)
        step_node id (WaitOnChannels hs) s s
        (*
            This specification says that we can't step out of a
            WaitOnChannels until there is a non-empty channel in the list.
            A better model might be one that:
                - marks the node as blocked if this is not true
                - in the global scheduler: only un-blocked nodes get scheduled
        *)
    | SChannelClose s n ch han nlbl clbl: 
        (s.(nodes).[?id]) = Labeled node (Some n) nlbl ->
            (* caller is a real node with label nlbl *)
        (s.(chans).[?han]).(lbl) = clbl ->
            (* handle has label clbl *)
        nlbl <<L clbl ->
        step_node id (ChannelClose han) s 
            (state_upd_chan han (chan_close ch) s)
    | SNodeLabelRead s:
        step_node id NodeLabelRead s s
    | SChannelLabelRead s han:
        step_node id (ChannelLabelRead han) s s
    | SInternal s: 
        step_node id Internal s s.

(* step for the full system which (non-deterministically) picks a thread to
* execute. This is needed in addition to step_node, because
we should show that regardless of the thread scheduling, there are no information
leaks. *)
(* To be general and language agnostic, computation of code within nodes other
than the ABI calls is modeled as simply returning an arbitrary continuation 
(c') of the node's choosing (for any call). *)
(* Errors might later be modeled by choosing a different continuation based
on whether or not a call was successful, in this case, the resulting
continuation likely needs to be moved into the local transition relation *)

Inductive step_system: state -> state -> Prop :=
    (* possibly also a termination case *)
    | SystemSkip s: step_system s s
    | SystemStepNode id n c c' s s':
        (s.(nodes) .[?id]).(obj) = Some n ->
        n.(ncall) = c ->
        step_node id c s s' ->
        step_system s (s_set_call s id c').

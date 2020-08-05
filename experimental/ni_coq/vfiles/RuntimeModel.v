Require Import List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap.

(* This file is the top-level model of the Oak runtime *)

(* Ensembles don't have implicit type params and these lines fix that *)
Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.

(*============================================================================
 Commands, State, Etc.
============================================================================*)
Record channel := Chan {
    clbl: level;
    ms: list message
}.

(* ABI Calls *)
Inductive call: Type :=
    | WriteChannel (h: handle)(m: message): call
    | ReadChannel (h: handle): call
    | CreateChannel (lbl: level): call
    | CreateNode (lbl: level)(h: handle): call
    | Internal: call. (* this is any action done by the node other than some
                         ABI call, it is "internal" to the node because it does
                         not affect the rest of the system*)
(* TODO wait_on_channels, channel_close *)
(*
TODO with the linear channels design, we might need a call just for passing
channels separate from message send so that the read handle is removed from the
sender when it is sent.
*)

Record node := Node {
    nlbl: level;
    read_handles: Ensemble handle;
    write_handles: Ensemble handle;
    ncall: call
}.

Instance Knid: KeyT := {
    t := node_id; 
    eq_dec := dec_eq_nid;
}.
Instance Khandle: KeyT := {
    t := handle;
    eq_dec := dec_eq_h;
}.
Definition node_state := tg_map Knid node.
Definition chan_state := tg_map Khandle channel.
Record state := State {
    nodes: node_state;
    chans: chan_state
}.

(*============================================================================
* Empty
============================================================================*)
Definition empty_chan := {| clbl := top; ms := []; |}.
Definition empty_node := {|
        nlbl := top;
        read_handles := Empty_set handle;
        write_handles := Empty_set handle;
        ncall := Internal;
    |}.

(*============================================================================
* Utils
============================================================================*)
(*
TODO look into this:  https://github.com/tchajed/coq-record-update
or other record libraries more deeply since records are used often.
*)
Definition chan_append (c: channel)(m: message): channel :=
    {| clbl := c.(clbl); ms := (m :: c.(ms)) |}.

(* this is used in channel read where there is a premise
* that checks that the channel is not empty *)
Definition chan_pop (c: channel): channel :=
    {| 
        clbl := c.(clbl); 
        ms := match c.(ms) with
            | nil => nil
            | m :: ms' => ms'
        end;
    |}.

Definition state_upd_node (nid: node_id)(n: node)(s: state): state :=
    {| 
        nodes := tg_update s.(nodes) nid n; 
        chans := s.(chans)
    |}.


Definition state_upd_chan (h: handle)(ch: channel)(s: state): state :=
    {|
        nodes := s.(nodes);
        chans := tg_update s.(chans) h ch;
    |}.

Definition state_upd_call (nid: node_id)(c: call)(s: state): state :=
    let old_n := (s.(nodes) nid) in
    state_upd_node nid ({|
            nlbl := old_n.(nlbl);
            read_handles := old_n.(read_handles);
            write_handles := old_n.(write_handles);
            ncall := c;
        |}) s.

Definition state_append_msg (h: handle)(m: message)(s: state): state :=
    state_upd_chan h (chan_append (s.(chans) h) m) s.

Definition state_chan_pop (h: handle)(s: state): state :=
    state_upd_chan h (chan_pop (s.(chans) h)) s.

Definition state_node_add_rhan (h: handle)(nid: node_id)(s: state): state :=
    let old_n := (s.(nodes) nid) in
    state_upd_node nid {|
            nlbl  := old_n.(nlbl);
            read_handles := Ensembles.Add old_n.(read_handles) h;
            write_handles := old_n.(write_handles);
            ncall := old_n.(ncall);
        |} s.

Definition state_node_add_whan (h: handle)(nid: node_id)(s: state): state :=
    let old_n := (s.(nodes) nid) in
    state_upd_node nid {|
            nlbl  := old_n.(nlbl);
            read_handles := old_n.(read_handles);
            write_handles := Ensembles.Add old_n.(write_handles) h;
            ncall := old_n.(ncall);
        |} s.

Definition state_node_del_rhan (h: handle)(nid: node_id)(s: state): state :=
    let old_n := (s.(nodes) nid) in
    state_upd_node nid {|
            nlbl  := old_n.(nlbl);
            read_handles := Ensembles.Subtract old_n.(read_handles) h;
            write_handles := old_n.(write_handles);
            ncall := old_n.(ncall);
        |} s.

(* 
NOTE it might actually be better to use option types
for the range of both the node state and channel states 
*)
(* There may be potential problems with these definitions *)
Definition handle_fresh (s: state)(h: handle): Prop :=
    (s.(chans) h) = empty_chan.

Definition nid_fresh (s: state)(nid: node_id): Prop :=
    (s.(nodes) nid) = empty_node.

(*============================================================================
* Single Call Semantics
============================================================================*)

(* step for a single node (which can be thought of as a thread) executing
* a particular call *)
(* It might be akwkard looking that the call of a node is a part of the object,
but that there is no premise checking that this call is really the one used
in the relation. This is checked in the global transition relation just below.
*)
Inductive step_node: node_id -> call -> state -> state -> Prop :=
    | SWriteChan s id n han msg:
        (s.(nodes) id) = n ->
        In n.(write_handles) han ->
        n.(nlbl) << (s.(chans) han).(clbl) ->
        step_node id (WriteChannel han msg) s (state_append_msg han msg s)
    | SReadChan s id n han chan:
        (s.(nodes) id) = n ->
        In n.(read_handles) han ->
        (s.(chans) han) = chan ->
            (* A channel read happens only when there is a message
            available in the channel. TODO, re-check what really happens
            when a message is not available, and possibly improve the model.
            E.g., if an error is thrown, execute an error continuation instead
            of the usual one if an error is _not_ thrown.
            *)
        length chan.(ms) > 0 ->
        chan.(clbl) << n.(nlbl) ->
        step_node id (ReadChannel han) s (state_chan_pop han s)
    | SCreateChan s cid h lbl:
        (s.(nodes) cid).(nlbl) << lbl ->
        handle_fresh s h ->
            let s0 := (state_upd_chan h {| ms := []; clbl := lbl; |} s) in
            let s1 := (state_node_add_rhan h cid s0) in
            let s' := (state_node_add_whan h cid s1) in
            step_node cid (CreateChannel lbl) s s'
    | SCreateNode s cid nid lbl h:
        (s.(nodes) cid).(nlbl) << lbl ->
        (nid_fresh s nid) ->
            (* create new node with read handle *)
        let s0 := (state_upd_node nid {| 
                nlbl := lbl;
                read_handles := (Singleton h);
                write_handles := Empty_set handle;
                ncall := Internal;
            |} s) in
        let s' := state_node_del_rhan h cid s0 in
        step_node cid (CreateNode lbl h) s s'
    | SInternal s id: step_node id Internal s s.

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
    | ValidStep id n c c' s s':
        (s.(nodes) id) = n ->
        n.(ncall) = c ->
        step_node id c s s' ->
        step_system s (state_upd_call id c' s').


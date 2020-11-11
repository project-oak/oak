Require Import List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap.

(* RecordUpdate is a conveninece feature that provides functional updates for
* records with notation: https://github.com/tchajed/coq-record-update *)
(* To work with record updates from this library in proofs "unfold set" quickly
* changes goals back to normal Coq built-in record updates *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Local Open Scope map_scope.

(* This file is the top-level model of the Oak runtime *)

(* Ensembles don't have implicit type params and these lines fix that *)
Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.
Arguments Ensembles.Union {U}.
Arguments Ensembles.Setminus{U}.
Arguments Ensembles.Included{U}.

(*============================================================================
 Commands, State, Etc.
============================================================================*)
(* These are messages sent over channels *)
Record message := Message {
    bytes : data;            (* the data part of the message *)
    rhs : Ensemble handle;   (* a set of read handles being sent *)
    whs : Ensemble handle;   (* a set of write handles being sent *)
}.
(* etamessage just enumerates the fields of the record, as provided
* by https://github.com/tchajed/coq-record-update *)
(* When a new field is added to a record, be sure to add it here as well *)
Instance etamessage : Settable _ := settable! Message<bytes; rhs; whs>.

(* 
messages model the messages in the oak impl. found in
oak/oak_io/src/lib.rs. Note that unlike in the implementation,
this model separates read and write handles into two different types
*)

Record channel := Chan {
    ms: list message;    (* list of pending messages in channel *)
}.
Instance etachannel : Settable _ := settable! Chan<ms>.


(* ABI Calls *)
Inductive call: Type :=
    | WriteChannel (h: handle)(m: message): call
        (* write a message m,
        * a set of read handles rhs, and 
        * a set of write handles whs
        * into the channel pointed to by h unless this would
        * cause an IFC violation *)
    | ReadChannel (h: handle): call
        (* read the top message and all the handles from the
        * channel into the caller, unless this would cause an IFC violation *)
    | CreateChannel (lbl: level): call
        (* create a new channel with label lbl, unless IFC violation *)
    | CreateNode (lbl: level)(h: handle): call
        (* create a new node with label lbl, unless IFC violation *)
    | Internal: call. (* this is any action done by the node other than some
                         ABI call, it is "internal" to the node because it does
                         not affect the rest of the system*)
(* TODO wait_on_channels, channel_close *)

Record node := Node {
    read_handles: Ensemble handle;
    write_handles: Ensemble handle;
    ncall: call
}.
Instance etanode: Settable _ :=
    settable! Node<read_handles; write_handles; ncall>.

Instance Knid: KeyT := {
    t := node_id; 
    eq_dec := dec_eq_nid;
}.
Instance Khandle: KeyT := {
    t := handle;
    eq_dec := dec_eq_h;
}.

Record labeled {A: Type} := Labeled {
    obj: option A;
    lbl: level;
}.

Definition node_l := @labeled node.
Definition channel_l := @labeled channel.

Instance etalabeled_chan : Settable _ := settable! (Labeled channel)<obj; lbl >.
Instance etalabeled_node : Settable _ := settable! (Labeled node)<obj ; lbl >.

Definition node_state := tg_map Knid (@labeled node).
Definition chan_state := tg_map Khandle (@labeled channel).
Record state := State {
    nodes: node_state;
    chans: chan_state;
}.

Instance etastate: Settable _ :=
    settable! State<nodes; chans>.

(*============================================================================
* Utils
============================================================================*)
Definition chan_append (c: channel)(m: message): channel :=
    c <|ms := c.(ms) ++ [m]|>.

(* this is used in channel read where there is a premise
* that checks that the channel is not empty *)
Definition chan_pop (c: channel): channel :=
    c <| ms := match c.(ms) with
            | nil => nil
            | m :: ms' => ms'
        end |>.

Definition msg_is_head (ch: channel)(m: message): Prop :=
    match ch.(ms) with
        | [] => False
        | m' :: ms' => m' = m
    end. 

Definition node_get_hans (n: node)(m: message): node :=
    n <| read_handles := (Union n.(read_handles) m.(rhs)) |>
      <| write_handles := (Union n.(write_handles) m.(whs)) |>.

Definition state_upd_node (nid: node_id)(n: node)(s: state): state :=
    (* n_l is a (labeled node) with the same label as the old one,
    but the contents updated to n *)
    let n_l := s.(nodes).[? nid] <| obj  := Some n |> in
    s <| nodes := s.(nodes) .[ nid <- n_l ] |>.

Definition state_upd_node_labeled (nid: node_id )(n_l: node_l)(s: state): state :=
    s<| nodes := s.(nodes).[nid <- n_l] |>.

Definition state_upd_chan (h: handle)(ch: channel)(s: state): state :=
    let ch_l := s.(chans).[? h] <| obj := Some ch |> in
    s <| chans := s.(chans) .[ h <- ch_l ] |>.

Definition state_upd_chan_labeled (h: handle)(ch_l: channel_l)(s: state): state :=
    s <| chans := s.(chans) .[ h <- ch_l ] |>.

(* 
    A node is allowed to write to a handle with a higher label than the node.
    As a result, the node may not be allowed to tell whether the handle
    maps to a real channel or not. To hide the state of the channel,
    a message is appended when the handle maps to a real channel, but if
    there is no channel with the given handle, the update does nothing.
*)
Definition chan_append_labeled (h: handle)(m: message)(s: state)  :=
    let old_chl := s.(chans).[? h] in
    match old_chl.(obj) with
        |  None => old_chl
        |  Some ch => old_chl <| obj := Some (chan_append ch m) |>
    end.

(* I suspect it may be easier to do proofs of things like the unwinding
theorem about this function from states to states rather than
trying to reason about chan_append_labeled (which is state-dependent)
separately from the place where the state update happens

If it does not turn out to be easier, perhaps this improves
readability anyway.
*)
Definition state_chan_append_labeled (h: handle)(m: message)(s: state) :=
    state_upd_chan_labeled h (chan_append_labeled h m s) s.

Definition node_add_rhan (h: handle)(n: node): node:=
    n <| read_handles := Ensembles.Add n.(read_handles) h |>.

Definition node_add_whan (h: handle)(n: node): node :=
    n <| write_handles := Ensembles.Add n.(write_handles) h |>.

Definition node_del_rhan (h: handle)(n: node): node :=
    n <| read_handles := Ensembles.Subtract n.(read_handles) h |>.

Definition node_del_rhans (hs: Ensemble handle)(n: node): node :=
    n <| read_handles := Ensembles.Setminus n.(read_handles) hs |>.

Definition new_chan := Some {| ms := [] |}.

Definition fresh_han s h := s.(chans).[?h] = Labeled channel None top.

Definition fresh_nid s id := s.(nodes).[?id] = Labeled node None top.

Definition s_set_call s id c :=
    match (s.(nodes).[?id]).(obj) with
        | None => s
        | Some n => state_upd_node id (n <|ncall := c|>) s
    end.

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
        step_node id (WriteChannel han msg) s 
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
        nlbl <<L clbl ->
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
        nlbl <<L new_lbl ->
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

Require Import List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.
From OakIFC Require Import
    Lattice
    Parameters.
(* finmap is a library for finite maps.
* it comes with nice notations and some built-in theorems.
* Since this is all that is used from ssreflect, we could cut ssreflect
* if it becomes too much trouble*)
From mathcomp Require Import all_ssreflect finmap.
(* RecordUpdate is a conveninece feature that provides functional updates for
* records with notation: https://github.com/tchajed/coq-record-update *)
(* To work with record updates from this library in proofs "unfold set" quickly
* changes goals back to normal Coq built-in record updates *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* This file is the top-level model of the Oak runtime *)

(* Ensembles don't have implicit type params and these lines fix that *)
Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.

(* Needed for most finite map notation *)
Open Scope fmap_scope.
Open Scope fset_scope.

(*============================================================================
 Commands, State, Etc.
============================================================================*)
Record channel := Chan {
    clbl: level;
    ms: list message
}.

(* etachannel just enumerates the fields of the record, as provided
* by https://github.com/tchajed/coq-record-update *)
(* When a new field is added to channel, be sure to add it here as well *)
Instance etachannel : Settable _ := settable! Chan<clbl; ms>.

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
TODO need to add field for handles in WriteChannel. When these are read handles
they should delete the handle from the sender to keep them linear.
*)

Record node := Node {
    nlbl: level;
    read_handles: Ensemble handle;
    write_handles: Ensemble handle;
    ncall: call
}.
Instance etanode: Settable _ :=
    settable! Node<nlbl; read_handles; write_handles; ncall>.

Definition node_state := {fmap node_id -> node}.
Definition chan_state := {fmap handle -> channel}.
Record state := State {
    nodes: node_state;
    chans: chan_state
}.

Instance etastate: Settable _ :=
    settable! State<nodes; chans>.

(*============================================================================
* Utils
============================================================================*)
Definition chan_append (c: channel)(m: message): channel :=
    c <|ms := m :: c.(ms)|>.

(* this is used in channel read where there is a premise
* that checks that the channel is not empty *)
Definition chan_pop (c: channel): channel :=
    c <| ms := match c.(ms) with
            | nil => nil
            | m :: ms' => ms'
        end |>.

Definition state_upd_node (nid: node_id)(n: node)(s: state): state :=
    s <| nodes := s.(nodes) .[ nid <- n ] |>.


Definition state_upd_chan (h: handle)(ch: channel)(s: state): state :=
    s <| chans := s.(chans) .[ h <- ch ] |>.

Definition node_add_rhan (h: handle)(n: node): node:=
    n <| read_handles := Ensembles.Add n.(read_handles) h |>.

Definition node_add_whan (h: handle)(n: node): node :=
    n <| write_handles := Ensembles.Add n.(write_handles) h |>.

Definition node_del_rhan (h: handle)(n: node): node :=
    n <| read_handles := Ensembles.Subtract n.(read_handles) h |>.

Definition handle_fresh (s: state)(h: handle): Prop :=
    s.(chans) .[?h] = None.

Definition nid_fresh (s: state)(nid: node_id): Prop :=
    s.(nodes) .[?nid] = None.

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
    | SWriteChan s id n han ch msg:
        s.(nodes) .[?id] = Some n ->
        In n.(write_handles) han ->
        s.(chans) .[?han] = Some ch ->
        (n.(nlbl) <<L ch.(clbl)) ->
        step_node id (WriteChannel han msg) s
            (state_upd_chan han (chan_append ch msg) s)
    | SReadChan s id n han ch:
        s.(nodes) .[?id] = Some n ->
        In n.(read_handles) han ->
        s.(chans) .[?han] = Some ch ->
            (* A channel read happens only when there is a message
            available in the channel. TODO, re-check what really happens
            when a message is not available, and possibly improve the model.
            E.g., if an error is thrown, execute an error continuation instead
            of the usual one if an error is _not_ thrown.
            *)
        length ch.(ms) > 0 ->
        ch.(clbl) <<L n.(nlbl) ->
        step_node id (ReadChannel han) s 
            (state_upd_chan han (chan_pop ch) s)
    | SCreateChan s id n h lbl:
        s.(nodes) .[?id] = Some n ->
        n.(nlbl) <<L lbl ->
        handle_fresh s h ->
            let s0 := (state_upd_chan h {| ms := []; clbl := lbl; |} s) in
            let s1 := state_upd_node id (node_add_rhan h n) s0 in
            let s' := state_upd_node id (node_add_whan h n) s1 in
            step_node id (CreateChannel lbl) s s'
    | SCreateNode s caller_id n new_id lbl h:
        s.(nodes) .[?caller_id] = Some n ->
        n.(nlbl) <<L lbl ->
        (nid_fresh s new_id) ->
            (* create new node with read handle *)
        let s0 := (state_upd_node new_id {| 
                nlbl := lbl;
                read_handles := (Singleton h);
                write_handles := Empty_set handle;
                ncall := Internal;
            |} s) in
        let s' := state_upd_node caller_id (node_add_rhan h n) s0 in
        step_node caller_id (CreateNode lbl h) s s'
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
        s.(nodes) .[?id] = Some n ->
        n.(ncall) = c ->
        step_node id c s s' ->
        step_system s (state_upd_node id (n <|ncall := c'|>) s').

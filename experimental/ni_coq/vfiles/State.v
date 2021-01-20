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
Messages model the messages in the oak impl. found in oak/oak_io/src/lib.rs. 
*)

Inductive channelStatus: Type := | ValidChannel | ClosedChannel.

Record channel := Chan {
    status: channelStatus;
    ms: list message; (* list of pending messages in channel *)
}.

Instance etachannel : Settable _ := settable! Chan<status; ms>.


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
    | WaitOnChannels (hs: Ensemble handle): call
        (* block until at least one handle in the supplied list is ready *)
    | ChannelClose (h: handle): call
        (* closes the channel pointed to by h *)
    | NodeLabelRead: call
        (* returns the label of the calling node *)
    | ChannelLabelRead (h: handle): call
        (* returns the label of the target handle *)
    | Internal: call
        (* this is any action done by the node other than some
        ABI call, it is "internal" to the node because it does
        not affect the rest of the system*)
    (* The following calls are only in the downgrading implementation *)
    | WriteChannelDown(h: handle)(m: message)(ell': level): call.
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


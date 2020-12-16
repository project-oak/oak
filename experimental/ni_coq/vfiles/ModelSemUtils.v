Require Import List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    State.

(* 
These are small functions of states or state elements that might be common
accross different model semantics
*)

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
Arguments Ensembles.Setminus{U}.
Arguments Ensembles.Included{U}.

(*============================================================================
* Utils
============================================================================*)

Definition chan_close (c: channel) := c <| status := ClosedChannel |>.

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

Definition new_chan := Some {| status := ValidChannel; ms := [] |}.

Definition fresh_han s h := s.(chans).[?h] = Labeled channel None bot.

Definition fresh_nid s id := s.(nodes).[?id] = Labeled node None bot.

Definition channel_valid s h := exists ms lbl,
    s.(chans).[? h] = Labeled channel (Some (Chan ValidChannel ms)) lbl.

(* unoccupied handles / IDs are secret for the model + security-def where 
labels are partially secret *)
Definition fresh_han_top s h := s.(chans).[?h] = Labeled channel None top.

Definition fresh_nid_top s id := s.(nodes).[?id] = Labeled node None top.

Definition s_set_call s id c :=
    match (s.(nodes).[?id]).(obj) with
        | None => s
        | Some n => state_upd_node id (n <|ncall := c|>) s
    end.


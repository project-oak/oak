From OakIFC Require Import
    Lattice
    Parameters
    State.
Require Import Coq.Lists.List.
Import ListNotations.


Inductive event: Type :=
    | InEv (m: message): event
    | OutEv (m: message): event
    | LabelReadEv (l: level): event
    | NCreateEv: event
    (* Only used in models with downgrading *)
    | DownEv {A: Type}(item: A)
        (lfrom: level)(lto: level): event.
(* note that messages include the bytes and handles sent via channels *)
(* eventually, downgrades will also be represented by events *)

Declare Scope ev_notation.
Local Open Scope ev_notation.
Notation "ell '--->' msg":= (Labeled event (Some (OutEv msg)) ell) (at level 10) : ev_notation.
Notation "ell '<---' msg":= (Labeled event (Some (InEv msg)) ell) (at level 10): ev_notation.
Notation "ell '<--L' lvl":= (Labeled event (Some (LabelReadEv lvl)) ell) (at level 10): ev_notation.
Notation "ell '---'":= (Labeled event None ell) (at level 10) : ev_notation.
Notation "'--' ell '--'" := (Labeled event (Some NCreateEv) ell) (at level 10) : ev_notation.
Notation "item 'DWN' lfrom '|-->' lto '" := 
        (Labeled event (Some DownEv item lfrom lto) lto)
        (at level 10) : ev_notation.

Definition event_l := @labeled event.


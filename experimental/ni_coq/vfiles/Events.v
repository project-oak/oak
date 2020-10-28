From OakIFC Require Import
    Lattice
    Parameters
    RuntimeModel.
Require Import Coq.Lists.List.
Import ListNotations.

(* This file contains  *)

Inductive event: Type :=
    | InEv (m: message): event
    | OutEv (m: message): event
    | NCreateEv: event.
(* note that messages include the bytes and handles sent via channels *)
(* eventually, downgrades will also be represented by events *)

Definition event_l := @labeled event.
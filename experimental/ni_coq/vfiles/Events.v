From OakIFC Require Import
    Lattice
    Parameters
    RuntimeModel.
Require Import Coq.Lists.List.
Import ListNotations.

(* This file contains  *)

Inductive event: Type :=
    | NilEv: event
    | InEv (m: message): event
    | OutEv (m: message): event.
(* note that messages include the bytes and handles sent via channels *)
(* eventually, downgrades will also be represented by events *)

Record event_l := EvL {
    e :event;
    elbl: level;
}.

(*
Inductive ev_low_eq: level -> event_l -> event_l -> Prop :=
    | EvEq ell el1 el2: 
            el1 = el2 ->
            ev_low_eq ell el1 el2
    | EvNoFlow ell el1 el2:
        ~((lvl el2) <<L ell) ->
        ~((lvl el1) <<L ell) ->
        ev_low_eq ell el1 el2.
*)

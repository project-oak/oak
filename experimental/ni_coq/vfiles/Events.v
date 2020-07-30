Require Import OakIFC.Lattice.
Require Import OakIFC.Parameters.

Inductive event: Type :=
    | NilEv: event
    | InEv (m: message): event
    | OutEv (m: message): event.
(* eventually, downgrades might also be represented by events *)

Inductive event_l: Type :=
    | EvL (e: event)(elvl: level): event_l.

Definition lvl(el: event_l): level :=
    match el with | EvL _ l => l end.

Inductive ev_low_eq: level -> event_l -> event_l -> Prop :=
    | EvEq ell el1 el2 (H: el1 = el2): ev_low_eq ell el1 el2
    | EvNoFlow ell el1 el2
        (H1: ~((lvl el2) << ell))
        (H2: ~((lvl el1) << ell)):
        ev_low_eq ell el1 el2.


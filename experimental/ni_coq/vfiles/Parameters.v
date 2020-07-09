Require Import OakIFC.Lattice.

(*
Security levels. The term level is used rather than label because, with
syntax extensions the label syntax might include security levels
as well as other kinds of labels, like functions from values to security levels.
In this case, labels are syntactic objects and levels are the security domains.
*)

Class params := {
    (* Assumed types, most with decidable equality *)
    level: Type; 
    dec_eq_lev: forall x y: level, {x=y} + {x <> y};
    message: Type;
    dec_eq_msg: forall x y: message, {x=y} + {x <> y};
    node_id: Type;
    dec_eq_nid: forall x y: node_id, {x=y} + {x <> y};
    handle: Type;
    dec_eq_h: forall x y: handle, {x=y} + {x <> y};
}.

Context {p: params}.
(* Note: if lat is packed into params, I run into issues when trying to resolve
* the lattice when defining the semantics of calls *)
Context {lat: Lattice level}.

Infix "⊔" := join (at level 40, left associativity).
Infix "⊓" := meet (at level 40, left associativity).
Infix "<<" := ord (at level 50).

Require Import OakIFC.RuntimeModel.
Require Import OakIFC.Parameters.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive chan_low_eq: level -> channel -> channel -> Prop :=
    | ChEq ell ch1 ch2 (H: ch1 = ch2): chan_low_eq ell ch1 ch2
    | ChNoFlow ell ch1 ch2
        (* if the level is not high enough to read either channel,
        * they both look the same to observers at this level *)
        (H1: ~(ch1.(clbl) << ell))
        (H2: ~(ch2.(clbl) << ell)):
        chan_low_eq ell ch1 ch2.

Inductive node_low_eq: level -> node -> node -> Prop :=
    | NodeEq ell n1 n2 (H: n1 = n2): node_low_eq ell n1 n2
    | NodeNoFlow ell n1 n2
        (H1: ~(n1.(nlbl) << ell))
        (H2: ~(n2.(nlbl) << ell)):
        node_low_eq ell n1 n2.

(* Way to phrase this as an inductive ?? *)
Definition chan_state_low_eq (ell: level)(chs1 chs2: chan_state): Prop :=
    forall m, match (chs1 m), (chs2 m) with
        | None, None => True
        | Some ch1, Some ch2 => chan_low_eq ell ch1 ch2
        | _, _ => False
    end.

Definition node_state_low_eq (ell: level)(ns1 ns2: node_state): Prop :=
    forall m, match (ns1 m), (ns2 m) with
        | None, None => True
        | Some ch1, Some ch2 => node_low_eq ell ch1 ch2
        | _, _ => False
    end.

Definition state_low_eq (ell: level)(s1 s2: state): Prop :=
    (node_state_low_eq ell s1.(nodes) s2.(nodes)) /\
        (chan_state_low_eq ell s1.(chans) s2.(chans)).

Definition trace := list state.

Inductive trace_low_eq: level -> trace -> trace -> Prop :=
    | NilEQ ell: trace_low_eq ell [] []
    | AddBoth ell x t1 t2 (H: trace_low_eq ell t1 t2):
        trace_low_eq ell (x::t1) (x::t2)
    | AddEqR ell x y t1 t2 
        (H1: trace_low_eq ell t1 (y::t2))
        (H2: state_low_eq ell x y):
        trace_low_eq ell t1 (x::y::t2)
    | AddEqL ell x y t1 t2 
        (H1: trace_low_eq ell (y::t1) t2)
        (H2: state_low_eq ell x y):
        trace_low_eq ell (x::y::t1) t2.


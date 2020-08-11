Require Import Coq.Lists.List.
Import ListNotations.
From mathcomp Require Import all_ssreflect finmap.
From OakIFC Require Import
    RuntimeModel
    Parameters.

(*=============================================================================
* Low Equivalences
=============================================================================*)
(* 
This file defines "low equivalence relations" over various pieces of state.
These are auxiliary definitions for defining the security condition.
A low-equivalence relation holds for a particular security level ell, and a pair
of state objects s1, s2 whenever they "appear the same" from the perspective of
an observer at the level ell. For example, if the state objects are channels,
an observer with security label "Alice" can see the contents of channels with
label "Alice" (or any other ell s.t. ell flowsTo Alice), so channels with such
labels are related if their contents are equal. By contrast, Alice should not be
able to see channels labeled "Bob", so _any_ pair of channels with this label
are related even if their contents differ.
*)

Inductive chan_low_eq: level -> channel -> channel -> Prop :=
    | ChEq ell ch1 ch2 (H: ch1 = ch2): chan_low_eq ell ch1 ch2
    | ChNoFlow ell ch1 ch2
        (* if the level is not high enough to read either channel,
        * they both look the same to observers at this level *)
        (H1: ~(ch1.(clbl) <<L ell))
        (H2: ~(ch2.(clbl) <<L ell)):
        chan_low_eq ell ch1 ch2.

Inductive node_low_eq: level -> node -> node -> Prop :=
    | NodeEq ell n1 n2 (H: n1 = n2): node_low_eq ell n1 n2
    | NodeNoFlow ell n1 n2
        (H1: ~(n1.(nlbl) <<L ell))
        (H2: ~(n2.(nlbl) <<L ell)):
        node_low_eq ell n1 n2.

(* Is there may a better way to write these using the finset / finmap
* libs *)
Definition chan_state_low_eq (ell: level)(chs1 chs2: chan_state): Prop :=
    forall h, (match (chs1 .[?h]), (chs2 .[?h]) with
        | None, None => True
        | Some ch1, Some ch2 => chan_low_eq ell ch1 ch2
        | _, _ => False
    end).

Definition node_state_low_eq (ell: level)(ns1 ns2: node_state): Prop :=
    forall h, (match (ns1 .[?h]), (ns2 .[?h]) with
        | None, None => True
        | Some n1, Some n2 => node_low_eq ell n1 n2
        | _, _ => False
    end).

Definition state_low_eq (ell: level)(s1 s2: state): Prop :=
    (node_state_low_eq ell s1.(nodes) s2.(nodes)) /\
        (chan_state_low_eq ell s1.(chans) s2.(chans)).

Require Import OakIFC.RuntimeModel.
Require Import OakIFC.Parameters.
Require Import Coq.Lists.List.
Import ListNotations.

(*=============================================================================
* Low Equivalences
=============================================================================*)
(* 
This file defines "low equivalence relations" over various pieces of state.
These are auxiliary definitions for defining the security condition.
A low-equivalence relation holds for a particular security level ell, and a pair
of state objects s1, s2 whenever the "appear the same" from the perspective of
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
    forall h, chan_low_eq ell (chs1 h) (chs2 h).

Definition node_state_low_eq (ell: level)(ns1 ns2: node_state): Prop :=
    forall m, node_low_eq ell (ns1 m) (ns2 m).

Definition state_low_eq (ell: level)(s1 s2: state): Prop :=
    (node_state_low_eq ell s1.(nodes) s2.(nodes)) /\
        (chan_state_low_eq ell s1.(chans) s2.(chans)).


(* 
Usually, the low-equivalence relation over traces of states are where we can
tell if the noninterference definition is timing sensitive. The Oak runtime
does not prevent timing channels, and we actually need to do more work when
specifying the theorem to allow them in the security condition. 

A straightforward trace low-equivalence definition might say that
t1 =L t2 <-> forall i, t1[i] =L t2[i]. But if one of the traces (say t2) 
takes longer to execute code for some node _other than L_, it will "stutter"
with several states in a row that are all low-equivalent because just the "high
parts" that L can't see could have changed.

This "up to high stutter" definition can be thought of as "collapsing" adjacent
low-equivalent states in each trace and then comparing them after they are
collapsed. The "collapsing" constructors are AddEqR and AddEqL.

Trace_low_eq is the simpler definition. It is likely sufficient for trace
propertries about executing a single node in serial.

Stut_trace_low_eq is the "up to high stutter" definition.
*)
Inductive trace_low_eq: level -> trace -> trace -> Prop :=
    | NilEQ ell: trace_low_eq ell [] []
    | AddBoth ell x y t1 t2 
        (H1: trace_low_eq ell t1 t2)
        (H2: state_low_eq ell x y):
        trace_low_eq ell (x::t1) (y::t2).

Inductive stut_trace_low_eq: level -> trace -> trace -> Prop :=
    | SNilEQ ell: stut_trace_low_eq ell [] []
    | SAddBoth ell x y t1 t2 
        (H1: stut_trace_low_eq ell t1 t2)
        (H2: state_low_eq ell x y):
        stut_trace_low_eq ell (x::t1) (y::t2)
    | SAddEqR ell x y t1 t2 
        (H1: stut_trace_low_eq ell t1 (y::t2))
        (H2: state_low_eq ell x y):
        stut_trace_low_eq ell t1 (x::y::t2)
    | SAddEqL ell x y t1 t2 
        (H1: stut_trace_low_eq ell (y::t1) t2)
        (H2: state_low_eq ell x y):
        stut_trace_low_eq ell (x::y::t1) t2.


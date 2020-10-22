Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    Lattice
    Events
    RuntimeModel
    EvAugSemantics.

(* Ensembles don't have implicit type params and this line fixes that *)
Arguments Ensembles.Empty_set{U}.

(* TODO fix comments to also talk about low projections *)
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


(*============================================================================
* Empty Things
*===========================================================================*)
Definition empty_chan (l:level): channel := {|
    clbl := l;
    ms := [];
|}.

Definition empty_node (l: level): node := {|
    nlbl := l;
    read_handles := Empty_set;
    write_handles := Empty_set;
    ncall := Internal; 
|}.

Definition empty_event (l: level): event_l := {|
    elbl := l;
    e := NilEv;
|}.
    

(*============================================================================
* Low Projections
*===========================================================================*)

Definition low_proj (A: Type): Type := level -> A -> A.

Definition chan_low_proj (ell: level)(c: channel): channel :=
    if(c.(clbl) <<? ell) then c else (empty_chan c.(clbl)).

Definition node_low_proj (ell: level)(n: node): node :=
    if(n.(nlbl) <<? ell) then n else (empty_node n.(nlbl)).

Definition event_low_proj (ell: level)(e: event_l): event_l :=
    if(e.(elbl) <<? ell) then e else (empty_event e.(elbl)).

Definition node_state_low_proj (ell: level)(ns: node_state): node_state :=
    fun id => match (ns id) with
        | None => Some (empty_node ell)
        | Some n => Some (node_low_proj ell n)
    end.

Definition chan_state_low_proj (ell: level)(cs: chan_state): chan_state :=
    fun h => match (cs h) with
        | None => Some (empty_chan ell)
        | Some c => Some (chan_low_proj ell c)
    end.

Definition state_low_proj (ell: level)(s: state): state := {|
    nodes := node_state_low_proj ell s.(nodes);
    chans := chan_state_low_proj ell s.(chans);
|}.

(*============================================================================
* Low Equivalences
*===========================================================================*)

Definition low_eq {A: Type} (p: (low_proj A)):=
    fun ell a1 a2 => (p ell a1) = (p ell a2).

Definition chan_low_eq := low_eq chan_low_proj.
Definition node_low_eq := low_eq node_low_proj.
Definition event_low_eq := low_eq event_low_proj.
Definition node_state_low_eq := low_eq node_state_low_proj.
Definition chan_state_low_eq := low_eq chan_state_low_proj.
Definition state_low_eq := low_eq state_low_proj.

(*============================================================================
* Trace Low Equivalences
*===========================================================================*)

(* We might need two different definitions of trace low-equivalence
* depending on the top-level security condition *)

(* This is a straightforward definition of trace low-equivalence
    Roughly, it says that 
    t1 =L t2 <-> forall i, t1[i] =L t2[i].

    This definition would be useful for a 
    "possibilistic security condition". A possibilistic security condition
    says that two executions look the same from the perspective of an observer
    if all _possible behaviors_ look the same if they begin from initial states
    that look the same to the observer.

    Possibilistic security conditions say that
    forall s1 s2 t1, 
        (s1 =L s2 -> <c, s1> => t1),
        exists t2, <c, s2> => t2 /\ t1 =L t2.

    In other words there is some way to reach an execution trace
    that looks the same beginning from the other state.
    
    Trapeze uses a possibilistic definition of security:
    https://pdfs.semanticscholar.org/809b/f2702a765b9e7dba4624a1dbc53af11579db.pdf
    See also:
    https://www.cs.cornell.edu/andru/papers/csfw03.pdf

    and discussion in PossibilisticNI.v
*)

Inductive trace_low_eq: level -> trace -> trace -> Prop :=
    | NilEQ ell: trace_low_eq ell [] []
    | AddBoth ell xs xe ys ye t1 t2:
        trace_low_eq ell t1 t2 ->
        event_low_eq ell xe ye ->
        state_low_eq ell xs ys ->
        trace_low_eq ell ((xs, xe)::t1) ((ys, ye)::t2).


(* An alternative way of specifying security for
   concurrent systems is observational determinism, which says
   that for any two executions that begin from low-equivalent
   initial states, the actual observed behaviors 
   (by contrast to possibly observed behaviors)
   _always_ look the same.

    This looks like:
    forall s1 s2 t1 t2,
        (s1 =L s2) /\
        (step_multi s1) => t1 /\
        (step_multi s2) => t2 ->
            t1 =L t2.

    If we write this top-level theorem using the straightforward
    definition of trace low-equivalence from above, the security condition
    would rule out *some* timing channels that we know our system does not
    prevent (so the security condition would not work). 

    The straightforward security condition would rule out the case where:
    - The observer is L
    - There is label L' s.t. not (L' flowsTo L)
    - A node called Other with Label L' takes more state transitions in one execution to
    perform some computation than in the other.

    While the "Other" node is executing, it can only affect parts of the system
    labeled L' (or higher), so for this part of a single execution, it will
    look like a sequence where ... si =L si+1 =L si+2 ... . In other words, the
    sub-sequence is low-equivalent. If the observer really can't measure time,
    two sequences that differ just in the number of transitions by "Other"
    really do look the same.

    This definition of trace low-equivalence rules this out by collapsing
    adjacent low-equivalent states (called "high stutter") in the traces.
*)
Inductive stut_trace_low_eq: level -> trace -> trace -> Prop :=
    | SNilEQ ell: stut_trace_low_eq ell [] []
    | SAddBoth ell xs xe ys ye t1 t2:
        stut_trace_low_eq ell t1 t2 ->
        event_low_eq ell xe ye ->
        state_low_eq ell xs ys ->
        stut_trace_low_eq ell ((xs, xe)::t1) ((ys, ye)::t2)
    | SAddEqR ell xs xe ys ye t1 t2:
        stut_trace_low_eq ell t1 ((ys, ye)::t2) ->
        event_low_eq ell xe ye ->
        state_low_eq ell xs ys ->
        stut_trace_low_eq ell t1 ((xs, xe)::(ys, ye)::t2)
    | SAddEqL ell xs xe ys ye t1 t2:
        stut_trace_low_eq ell ((ys, ye)::t1) t2 ->
        event_low_eq ell xe ye ->
        state_low_eq ell xs ys ->
        stut_trace_low_eq ell ((xs, xe)::t1) ((ys, ye)::t2).

Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Import ListNotations.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    Lattice
    State
    Events
    ModelTypes.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

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
* Low Projections
*===========================================================================*)

Definition low_proj_t {A: Type}: Type := level -> A -> A.
Definition low_proj {A: Type} ell ( labeled_thing: @labeled A) := 
    match labeled_thing with
        | Labeled _ o ell' => if( ell' <<? ell ) 
            then labeled_thing
            else Labeled A None ell' 
    end.
    (* 
    Importantly, the label of the secret thing is NOT ell'
    but instead the top of the information flow lattice 
    (secret, untrusted) which means that in this formulation,
    labels are not completely public. Instead, an observer at level
    ell can see:
        - whether the label of an object flows to ell, for any object.
        - the precise label of the object if its label does flow to ell.
    Putting it another way, the label ell' of a secret object is not observable,
    but whether or not (ell' <<L ell) is observable.

    This defintion is necessary in order to make the theorem provable while
    still supporting dynamic creation of nodes and channels. 
    Noninterference proofs often rely on theorems that roughly say "when a
    secret step is taken, no public state is updated". (In this code, these
    theorems often have "unobs" in their names. In the literature these are
    sometimes called clearance). To create a node
    or channel, a new labeled object appears, which is effectively a "label
    change". If labels are public, we can't prove the "unobs" theorems because
    because the node/channel creation calls DO create new labels and therefore
    do update public state. 
    
    By revealing only partial information about labels to an arbitrary
    observer, we can show that since secret nodes can only create secret
    objects, these label changes in the secret part of the lattice are actually
    hidden.
    *)

Definition node_low_proj := @low_proj node.
Definition chan_low_proj := @low_proj channel.
Definition event_low_proj := @low_proj event.
Definition down_low_proj := @low_proj down_event.

Definition node_state_low_proj (ell: level)(ns: node_state): node_state :=
    fun id => low_proj ell (ns id).

Definition chan_state_low_proj (ell: level)(cs: chan_state): chan_state :=
    fun h => low_proj ell (cs h).

Definition state_low_proj (ell: level)(s: state): state := {|
    nodes := node_state_low_proj ell s.(nodes);
    chans := chan_state_low_proj ell s.(chans);
|}.

(*============================================================================
* Low Equivalences
*===========================================================================*)

Definition low_eq_t {A: Type}: Type := level -> A -> A -> Prop.
Definition low_eq {A: Type} ell (x: @labeled A) (y: @labeled A) :=
    (low_proj ell x) = (low_proj ell y).

Definition node_low_eq := @low_eq node.
Definition chan_low_eq := @low_eq channel.
Definition event_low_eq := @low_eq event.
Definition down_low_eq := @low_eq down_event.
Definition node_state_low_eq := fun ell ns1 ns2 =>
    forall nid, (node_state_low_proj ell ns1) nid = (node_state_low_proj ell ns2) nid.
Definition chan_state_low_eq := fun ell cs1 cs2 =>
    forall han, (chan_state_low_proj ell cs1) han = (chan_state_low_proj ell cs2) han.
Definition state_low_eq := fun ell s1 s2 =>
    (forall nid, (state_low_proj ell s1).(nodes) nid =
        (state_low_proj ell s2).(nodes) nid) /\
    (forall han, (state_low_proj ell s1).(chans) han=
        (state_low_proj ell s2).(chans) han ).

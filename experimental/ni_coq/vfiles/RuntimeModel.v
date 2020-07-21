Require Import OakIFC.Lattice.
Require Import OakIFC.Parameters.
Require Import OakIFC.GenericMap.
Require Import List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.

(* Ensembles don't have implicit type params and these lines fix that *)
Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.

(*============================================================================
 Commands, State, Etc.
============================================================================*)
Record channel := Chan {
    clbl: level;
    ms: list message
}.

(* ABI Calls *)
Inductive call: Type :=
    | WriteChannel (h: handle) (m: message): call
    | ReadChannel (h: handle): call
    | Internal: call.

Record node := Node {
    nlbl: level;
    hans: Ensemble handle;
    ncall: call
}.

Instance Knid: KeyT := {
    t := node_id; 
    eq_dec := dec_eq_nid;
}.
Instance Khandle: KeyT := {
    t := handle;
    eq_dec := dec_eq_h;
}.
Definition node_state := tg_map Knid node.
Definition chan_state := tg_map Khandle channel.
Record state := State {
    nodes: node_state;
    chans: chan_state
}.

(*============================================================================
* Empty
============================================================================*)
Definition empty_chan := {| clbl := top; ms := []; |}.
Definition empty_node := {|
        nlbl := top;
        hans := Empty_set handle;
        ncall := Internal;
    |}.
Definition empty_state := {| 
        nodes := ( _ !-> empty_node);
        chans := ( _ !-> empty_chan);
    |}.

(*============================================================================
* Utils
============================================================================*)
Definition chan_append (c: channel)(m: message): channel :=
    {| clbl := c.(clbl); ms := (m :: c.(ms)) |}.

Definition state_upd_node (nid: node_id)(n: node)(s: state): state :=
    {| 
        nodes := tg_update s.(nodes) nid n; 
        chans := s.(chans)
    |}.

Definition state_upd_chan (h: handle)(ch: channel)(s: state): state :=
    {|
        nodes := s.(nodes);
        chans := tg_update s.(chans) h ch;
    |}.

(*============================================================================
* Single Call Semantics
============================================================================*)

(* step for a single node (which can be thought of as a thread) *)
Inductive step_node: node_id -> state -> state -> Prop :=
    | SWriteSucc s id n han msg
        (H0: (s.(nodes) id) = n)
        (H1: n.(ncall) = WriteChannel han msg)
        (H1: In n.(hans) han)
        (H2: n.(nlbl) << (s.(chans) han).(clbl)):
        step_node id s
            (state_upd_chan han (chan_append (s.(chans) han) msg) s).
    (* TODO all the other calls *)

(* step for the full system (which picks a thread to execute and is
non-deterministic). This is needed in addition to step_node, because
we should show that regardless of the thread ordering, there are no information
leaks. *)
Inductive step_system: state -> state -> Prop :=
    (* possibly also a termination case *)
    | ValidStep id s s'
        (H1: step_node id s s'):
        step_system s s'.

(* Traces are sequences of states modeling entire executions *)
(* Noninterference definitions are defined by comparing "any two" executions *)
Definition global_state: Type := state.
Definition trace := list global_state.

Definition last_state (t: trace)(s: state): Prop :=
    match t with
        | [] => False
        | x :: t' => s = x
    end.

Inductive valid_trace (init: state): trace -> Prop :=
    | VTOne: (valid_trace init [init] )
    | VTAdd (s s': state)(t: trace)
            (H0: valid_trace init t )
            (H1: last_state t s')
            (H2: step_system s s):
            valid_trace init (s' :: t).


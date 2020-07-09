Require Import OakIFC.Lattice.
Require Import OakIFC.GenericMap.
Require Import List.

(*
Security levels. The term level is used rather than label because, with
syntax extensions the label syntax might include security levels
as well as other kinds of labels, like functions from values to security levels.
In this case, labels are syntactic objects and levels are the security domains.
*)

(* Assumed types, most with decidable equality *)
Variable level: Type.
Context { Lat: Lattice level}.
Context {message: Type}
    {dec_eq_msg: forall x y: message, {x=y} + {x <> y}}.
Context {node_id: Type}
    {dec_eq_nid: forall x y: node_id, {x=y} + {x <> y}}.
Context {handle: Type}
    {dec_eq_h: forall x y: handle, {x=y} + {x <> y}}.

(*============================================================================
 Commands, State, Etc.
============================================================================*)
Record channel := Chan {
    clbl: level;
    ms: list message
}.

(* Internal actions that nodes do other than ABI calls *)
Inductive internal_cmd: Type :=
    | IntRecvErr: internal_cmd (* TODO distinguish errors *)
    | IntOther: internal_cmd
    | IntRecvMesg (m: message): internal_cmd.

(* ABI Calls *)
Inductive call: Type :=
    | WriteChannel (h: handle) (m: message): call
    | Internal (cmd: internal_cmd): call.

Record node := Node {
    nlbl: level;
    calls: list call;
    hans: list handle
}.

(* TODO: unsure if records or inductives are better for proofs.
records are better for spec writing.
also consider using a finite set of nodes rather than a map from
node ids to nodes since node ids are not real anyway *)

Instance Knid : KeyT := {
    t := node_id; 
    eqb := fun x => fun y =>
        if (dec_eq_nid x y) then true else false
}.
Definition node_state := pg_map Knid node.
Instance Khandle : KeyT := {
    t := handle;
    eqb := fun x => fun y =>
        if (dec_eq_h x y) then true else false
}.
Definition chan_state := pg_map Khandle channel.
Record state := State {
    nodes: node_state;
    chans: chan_state
}.

(*============================================================================
* Utils
============================================================================*)
Definition chan_append (c: channel)(m: message): channel :=
    match c with | Chan l ms => Chan l (m :: ms) end.

Definition node_push_c (n: node)(c: call): node :=
    match n with | Node l cs hs => Node l (c :: cs) hs end .

Definition is_node_call (n: node)(c: call): Prop :=
    match n.(calls) with
        | c :: _ => True
        | _ => False
    end.

Definition node_pop_cmd (n: node): node :=
    match n.(calls) with
        | c :: cs' => Node n.(nlbl) n.(calls) n.(hans)
        | _ => n
    end.

Definition state_pop_caller (nid: node_id)(s: state): state := 
    match (s.(nodes) nid) with
        | None => s
        | Some n => 
            {| nodes := pg_update s.(nodes) nid (node_pop_cmd n);
            chans := s.(chans) |}
    end.

Definition opt_match {A: Type}(o: option A)(a: A): Prop :=
    match o with | Some a => True | _ => False end.

(*============================================================================
* Single Call Semantics
============================================================================*)

Inductive step_call: node_id -> call -> state -> state -> Prop :=
    | SWriteSucc caller_id caller han chan msg s
        (H0: In han caller.(hans))
        (H1: opt_match (s.(chans) han) chan)
        (H2: caller.(nlbl) << chan.(clbl)):
        step_call caller_id (WriteChannel han msg) s (
            let chans' :=
                (pg_update s.(chans) han (chan_append chan msg)) in
            {| nodes := s.(nodes); chans := chans'|}
        )
    | SWriteLblErr caller_id caller han chan msg s
        (H0: In han caller.(hans))
        (H1: opt_match (s.(chans) han) chan)
        (H2: ~(caller.(nlbl) << chan.(clbl))):
        step_call caller_id (WriteChannel han msg) s (
            let nodes' :=
                (pg_update s.(nodes) caller_id
                    (node_push_c caller (Internal IntRecvErr) )) in
            {| nodes := nodes'; chans := s.(chans) |}
        ).

Inductive step_node: node_id -> state -> state -> Prop :=
    | ValidStep caller_id caller call s s_pop s'
        (H0: opt_match (s.(nodes) caller_id) caller)
        (H1: is_node_call caller call)
        (H3: s_pop = state_pop_caller caller_id s)
        (H4: step_call caller_id call s_pop s'):
        step_node caller_id s s'.



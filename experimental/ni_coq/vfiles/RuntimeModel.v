Require Import OakIFC.Lattice.
Require Import OakIFC.Parameters.
Require Import OakIFC.GenericMap.
Require Import List.
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
    hans: Ensemble handle
}.

(* TODO: unsure if records or inductives are better for proofs.
records are better for spec writing.
also consider using a finite set of nodes rather than a map from
node ids to nodes since node ids are not real anyway *)

Instance Knid: KeyT := {
    t := node_id; 
    eq_dec := dec_eq_nid;
}.
Definition node_state := tg_map Knid node.
Instance Khandle: KeyT := {
    t := handle;
    eq_dec := dec_eq_h;
}.
Definition chan_state := tg_map Khandle channel.
Record state := State {
    nodes: node_state;
    chans: chan_state
}.

(*============================================================================
* Utils
============================================================================*)
Definition chan_append (c: channel)(m: message): channel :=
    {| clbl := c.(clbl); ms := (m :: c.(ms)) |}.

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

Definition state_pop_caller (nid: node_id)(s: state): state := 
    state_upd_node nid (node_pop_cmd (s.(nodes) nid)) s.

(*
Definition opt_match {A: Type}(o: option A)(a: A): Prop :=
    match o with | Some a => True | _ => False end.
*)

(*============================================================================
* Single Call Semantics
============================================================================*)

Inductive step_call: node_id -> call -> state -> state -> Prop :=
    | SWriteSucc caller_id han msg s
        (H0: In (s.(nodes) caller_id).(hans) han)
        (H2: (s.(nodes) caller_id).(nlbl) << (s.(chans) han).(clbl)):
        step_call caller_id (WriteChannel han msg) s 
            (state_upd_chan han (chan_append (s.(chans) han) msg) s).
    (*
    | SWriteLblErr caller_id han chan msg s
        (H0: In (s.(nodes) caller_id).(hans) han)
        (H1: opt_match (s.(chans) han) chan)
        (H2: ~((s.(nodes) caller_id).(nlbl) << chan.(clbl))):
        step_call caller_id (WriteChannel han msg) s 
            ( let n' := (node_push_c (s.(nodes) caller_id)
                (Internal IntRecvErr)) in
            state_upd_node caller_id n' s).
    *)

Inductive step_system: state -> state -> Prop :=
    | ValidStep caller_id caller call s s_pop s'
        (H1: is_node_call caller call)
        (H3: s_pop = state_pop_caller caller_id s)
        (H4: step_call caller_id call s_pop s'):
        step_system s s'.

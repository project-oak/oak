Require Import OakIFC.Lattice.
Require Import List.

Section RuntimeModel.
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

Infix "⊔" := join (at level 40, left associativity).
Infix "⊓" := meet (at level 40, left associativity).
Infix "<<" := ord (at level 50).

(*============================================================================
 Commands, State, Etc.
============================================================================*)
Inductive channel: Type :=
    | Chan (l: level) (ms: list message): channel.

(* Internal actions that nodes do other than ABI calls *)
Inductive internal_cmd: Type :=
    | IntRecvErr: internal_cmd (* TODO distinguish errors *)
    | IntOther: internal_cmd
    | IntRecvMesg (m: message): internal_cmd.

(* ABI Calls *)
Inductive call: Type :=
    | WriteChannel (h: handle) (m: message): call
    | Internal (cmd: internal_cmd): call.

Inductive node: Type :=
    | Node (l: level)(calls: list call): node.

Definition node_state := node_id-> option node.
Definition chan_state := handle -> (option channel).
Record state := State {
    nodes: node_state;
    chans: chan_state
}.

(*============================================================================
* Updaters
============================================================================*)
Definition chan_append (c: channel)(m: message): channel :=
    match c with | Chan l ms => Chan l (m :: ms) end.

Definition node_push_c (n: node)(c: call): node :=
    match n with | Node l cs => Node l (c :: cs) end .

Definition upd_node (id: node_id)(n: node)(ns: node_state): node_state :=
    fun x => if (dec_eq_nid id x) then Some n else (ns x).

Definition upd_chan (h: handle)(ch: channel)(cs: chan_state): chan_state :=
    fun x => if (dec_eq_h h x) then Some ch else (cs x).

(*============================================================================
* Single Call Semantics
============================================================================*)
(* TODO well-formed def making sure caller id, caller, top cmd in caller list
* all match *)
(* Is there a way to structure this using inductive properties, more like a
* type system would be formalized? So that the inversion tactic could be used ?*)
(* TODO need to pop command *)
Definition step_call (c: call)(caller: node)(cid: node_id)(s: state): state :=
    match c with
        | WriteChannel h m => 
                match (s.(chans) h) with
                    | Some ch => let chans' := 
                            upd_chan h (chan_append ch m) s.(chans) in
                            {| nodes := s.(nodes); chans := chans'|}
                    | None => 
                            let caller' := node_push_c caller (Internal
                                IntRecvErr) in
                            let nodes' := upd_node cid caller' s.(nodes) in
                            {| nodes := nodes'; chans := s.(chans) |}
                end
        | Internal cmd => s (* TODO, internal command semantics *)
    end.

(* Execute a single node, non-deterministically. Because this is
* nondeterministic, a relation is used *)
(* TODO: try using sets of threads instead of a map from TIDs to threads*)
Definition active_node (nid: node_id) (s: state): Prop :=
    match s.(nodes) nid with
        | Some _ => True
        | None => False
    end.

(* These definitions are clearly terrible *)
(* Look at using sets of nodes *)
Definition valid_sys_step (s1: state) (s2: state) :=
    exists nid: node_id, (active_node nid s1) /\
     (* this bit can at least be improved by rolling this back into step *)
        match s1.(nodes) nid with
            | Some n => match n with
                | Node l cmds =>
                    match cmds with
                        | nil => False
                        | hd :: cmds' => (step_call hd n nid s1) = s2
                    end
                end
            | None => False
        end.

End RuntimeModel.

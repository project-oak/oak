Require Import OakIFC.RuntimeModel.
Require Import OakIFC.Lattice.
Require Import OakIFC.Parameters.
Require Import OakIFC.GenericMap.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Definition empty_chan := Chan bot nil.


(*
Note: this file is attempting to define an NI definition in based on
low-projections, which are functions from "things" and security levels to
"things from the perspective of that level". This does not work out too easily
though:
    - Trace low-projections need to be defined "up to high stutter" which
    necessitates either boolean or otherwise decidable equality on states (not
    just propositional equality).
    - States are records including generic maps. These generic maps are defined
    using functions. Propositional equality can be given by using functional
    extensionality, but this does not give a way to provide eqb.

So it looks like an NI definition JUST in terms of low-equivalence relations is
needed instead.
*)

(*---------------------------------------------------------------------------*)
(* Boolean Equalities *)
(*---------------------------------------------------------------------------*)

Fixpoint list_eqb {A: Type} (a_eqb: A -> A -> bool)(l1 l2: list A): bool :=
    match l1, l2 with
        | nil, nil => true
        | x :: l1', y :: l2' => (a_eqb x y) && ((list_eqb a_eqb) l1' l2')
        | _, _ => false
    end.

Definition chan_eqb (ch1 ch2:channel): bool :=
    if dec_eq_lev ch1.(clbl) ch2.(clbl)
    then (if (list_eq_dec dec_eq_msg) ch1.(ms) ch2.(ms)
        then true else false)
    else false.

Definition internal_cmd_eqb (cmd1 cmd2: internal_cmd): bool :=
    match cmd1, cmd2 with
        | IntRecvErr, IntRecvErr => true
        | IntOther, IntOther => true
        | IntRecvMesg m1, IntRecvMesg m2 => 
                if dec_eq_msg m1 m2 then true else false
        | _, _ => false
    end.

Definition call_eqb (c1 c2: call): bool :=
    match c1, c2 with
        | WriteChannel h1 m1, WriteChannel h2 m2 =>
            if (dec_eq_h h1 h2) 
            then (if dec_eq_msg m1 m2 then true else false)
            else false
        | Internal cmd1, Internal cmd2 =>
            internal_cmd_eqb cmd1 cmd2
        | _, _ => false
    end.

Definition node_eqb (n1 n2: node): bool :=
    if (dec_eq_lev n1.(nlbl) n2.(nlbl))
    then (if (list_eq_dec dec_eq_h) n1.(hans) n2.(hans)
        then (list_eqb call_eqb) n1.(calls) n2.(calls)
        else false)
    else false.
    

(*
Definition state_eqb (s1 s2: state): bool :=
    ((list_eqb chan_eqb) s1.(chans) s2.(chans)) &&
        ((list_eqb node_eqb) s1.(nodes) s2.(nodes)).
*)

(*---------------------------------------------------------------------------*)
(* Low Projections *)
(*---------------------------------------------------------------------------*)
(* These functions take "a thing", and a security label, and produce a version
of "the thing" from the perspective of an observer at the given security level.
Generally, if the label of the thing flowsTo the label of the observer, this
means the observer gets to see it, so the low-projection returns the original
thing. If this flowsTo relation does not hold, the low-projection returns some
nil version instead. Low projections are a common technique for defining
noninterference variants (security hyperproperties). *)
Definition chan_proj (ell: level)(ch: channel): channel :=
    if (ord_dec ch.(clbl) ell) then ch
    else empty_chan.

Definition empty_node := Node bot nil nil.

Definition node_proj (ell: level)(n: node): node :=
    if (ord_dec n.(nlbl) ell) then n
    else empty_node.

Definition state_proj (ell: level)(s: state): state := {|
    nodes := pg_fmap (node_proj ell) s.(nodes);
    chans := pg_fmap (chan_proj ell) s.(chans);
|}.

Definition state_low_eqb (ell: level)(s1: state)(s2: state): bool :=
    (state_proj ell s1) = (state_proj ell s2).

(* This definition of trace low-equivalence is "up to high stutter". Adjacent
* states within a trace that are low-equivalent are collapsed to one state.
* This is needed for a timing-insensitive definition of noninterference *)
(* Using two matches rather than matching on (x :: y :: nil) is needed to make
* coq happy about termination, AFAICT *)

(* Need decidable equality on states!!*)

(*
Fixpoint trace_ell_proj (ell: level)(t: list state): list state :=
    match t with
        | x :: t' => match t' with
            | y :: t'' => if (state_low_eq ell x y)
                    then (trace_ell_proj ell t')
                    else x :: (trace_ell_proj ell t')
            | nil => t
        end
        | nil => t
    end.


(* TODO need a up-to- high-stutter definition *)
Definition trace_low_eq (t1: list state)(t2: list state)(ell:level): Prop :=

(* TODO need a valid initial state definition ? *)
Inductive valid_trace: (list state) -> Prop :=
    | VTOne s: (valid_trace (s :: nil) )
    | VTAdd s s' t
            (H0: valid_trace  (s :: t) )
            (H1: step_system s s'):
            (valid_trace (s' :: (s :: t))).

*) 

(* TODO make this generic in terms of call definitions, so that
* one theorem can be proved for a set of calls including downgrades
* and another can be proven for calls w/o *)

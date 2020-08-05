Require Import OakIFC.RuntimeModel.
Require Import OakIFC.Lattice.
Require Import OakIFC.Parameters.
Require Import OakIFC.GenericMap.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

(*
This file gives various definitions of boolean equality.
This was at one point used for various definitions of the theorem,
but is not used at the moment. It is kept around, but moved out of the 
way because it seems like the sort of thing that could turn
out to be useful again.
*)

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
    

Definition state_eqb (s1 s2: state): bool :=
    ((list_eqb chan_eqb) s1.(chans) s2.(chans)) &&
        ((list_eqb node_eqb) s1.(nodes) s2.(nodes)).


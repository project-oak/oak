Require Import OakIFC.Lattice.
Require Import OakIFC.Parameters.
Require Import OakIFC.GenericMap.
Require Import List.
Import ListNotations.
Require Import RuntimeModel.
Require Import OakIFC.Events.
Require Import Coq.Sets.Ensembles.

Definition trace := list (event_l).

Arguments Ensembles.In {U}.
Arguments Ensembles.Add {U}.
Arguments Ensembles.Subtract {U}.
Arguments Ensembles.Singleton {U}.

Definition msg_is_head (ch: channel)(m: message): Prop :=
    match ch.(ms) with
        | [] => False
        | m' :: ms' => m' = m
    end. 

(* TODO consider whether traces should really also be
 list (state * event_l)
 for example so that we can reason about the level of commands
 of individual steps.
*)

Inductive step_node_ev: node_id -> call -> state -> trace -> state -> trace -> Prop :=
    | SWriteChan s id n han msg t ev
        (H0: (s.(nodes) id) = n)
        (H1: Ensembles.In n.(whans) han)
        (H2: n.(nlbl) << (s.(chans) han).(clbl))
        (H3: ev = (EvL (OutEv msg) n.(nlbl))):
        step_node_ev id (WriteChannel han msg) s t
            (state_append_msg han msg s) (ev :: t)
    | SReadChan s id n han chan msg t ev
        (H0: (s.(nodes) id) = n)
        (H1: In n.(rhans) han)
        (H2: (s.(chans) han) = chan)
        (H3: (length chan.(ms)) > 0)
        (H4: chan.(clbl) << n.(nlbl))
        (H5: (msg_is_head chan msg))
        (H6: ev = (EvL (InEv msg) n.(nlbl))):
        step_node_ev id (ReadChannel han) s t 
            (state_chan_pop han s) (ev :: t)
    | SCreateChan s n cid h lbl t ev
        (H0: (s.(nodes) cid) = n)
        (H1: n.(nlbl) << lbl)
        (H2: handle_fresh s h)
        (H3: ev = (EvL NilEv n.(nlbl)) ):
            let s0 := (state_upd_chan h {| ms := []; clbl := lbl; |} s) in
            let s1 := (state_node_add_rhan h cid s0) in
            let s' := (state_node_add_whan h cid s1) in
            step_node_ev cid (CreateChannel lbl) s t s' (ev :: t)
    | SCreateNode s n cid nid lbl h t ev
        (H0: (s.(nodes) cid) = n)
        (H1: n.(nlbl) << lbl)
        (H2: (nid_fresh s nid))
        (H3: ev = (EvL NilEv n.(nlbl))):
        let s0 := (state_upd_node nid {| 
                nlbl := lbl;
                rhans := (Singleton h);
                whans := Empty_set handle;
                ncall := Internal;
            |} s) in
        let s' := state_node_del_rhan h cid s0 in
        step_node_ev cid (CreateNode lbl h) s t s' (ev :: t)
    | SInternal s id t ev
        (H0: ev = (EvL NilEv (s.(nodes) id).(nlbl))) :
        step_node_ev id Internal s t s (ev :: t).

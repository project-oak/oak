Require Import Coq.Sets.Ensembles.
Require Import List.
From OakIFC Require Import
    Lattice
    Parameters
    GenericMap
    ModelSemUtils
    RuntimeModel
    State
    Events.
Import ListNotations.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Local Open Scope map_scope.
Local Open Scope ev_notation.

Inductive step_node_ev (id: node_id): call -> state -> down_l ->
        state -> event_l -> Prop :=
    | SWriteChanEv s nlbl han msg s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (WriteChannel han msg) s s' ->
        step_node_ev id (WriteChannel han msg) s (ell DWN nil)
            s' (nlbl ---> msg)
        (* The notations used for events on this last line and others
        is in Events.v *)
    | SWriteChanDwnEv s nlbl han msg s' ell':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (WriteChannel han msg ell') s s' ->
        step_node_ev id (WriteChannel han msg ell') s (msg DWN nlbl |--> ell')
            s' (nlbl ---> msg)
    | SReadChanEv s nlbl han chan msg s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (ReadChannel han) s s' ->
        msg_is_head chan msg ->
        step_node_ev id (ReadChannel han) s (ell DWN nil)
            s' (nlbl <--- msg)
    | SCreateChanEv s nlbl clbl s':
        (* It seems clear that no event is needed since nodes only observe
        * contents of channels indirectly via reads *)
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (CreateChannel clbl) s s' ->
        step_node_ev id (CreateChannel clbl) s (ell DWN nil)
            s' (nlbl --- )
    | SCreateNodeEv s nlbl new_lbl h s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (CreateNode new_lbl h) s s' ->
        step_node_ev id (CreateNode new_lbl h) s (ell DWN nil)
            s' ( -- nlbl -- )
    | SWaitOnChannelsEv s hs nlbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (WaitOnChannels hs) s s' ->
        step_node_ev id (WaitOnChannels hs) s (ell DWN nil)
            s' (nlbl ---)
    | SChannelCloseEv s han nlbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id (ChannelClose han) s s' ->
        step_node_ev id (ChannelClose han) s (ell DWN nil)
            s' (nlbl ---)
    | SNodeLabelReadEv s nlbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id NodeLabelRead s s' ->
        step_node_ev id NodeLabelRead s (ell DWN nil)
            s' (nlbl <--L nlbl)
    | SChannelLabelReadEv s han nlbl clbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        (s.(chans) .[?han]).(lbl) = clbl ->
        step_node id (ChannelLabelRead han) s s' ->
        step_node_ev id (ChannelLabelRead han) s (ell DWN nil)
            s' (nlbl <--L clbl)
    | SInternalEv s nlbl s':
        (s.(nodes) .[?id]).(lbl) = nlbl ->
        step_node id Internal s s' ->
        step_node_ev id Internal s (ell DWN nil)
            s' (nlbl ---).

Inductive step_system_ev: state -> state -> event_l -> Prop :=
    | SytsemEvSkip s ell: step_system_ev s s (ell ---) 
    | SystemEvStepNode id n c c' s s' e:
        (s.(nodes).[?id]).(obj) = Some n ->
        n.(ncall) = c ->
        step_node_ev id c s s' e ->
        let s'' := (s_set_call s' id c') in
            (* Here c' is an arbitrary command. The next ABI call
            that the node makes after the one executed here is an arbitrary one
            of that node's choosing *)
        step_system_ev s s'' e.

Definition trace := list (state * event_l).

(* This is used for state/event pairs in EvAug. 
* The type is slightly awkward now post refactor *)
Definition head_st (t: trace) :=
    match t with 
        | nil => None
        | (s', _)::_ => Some s'
    end.

Inductive step_system_ev_t: trace -> trace -> Prop :=
    | StepTrace t s s' e:
        head_st t = Some s -> 
        step_system_ev s s' e ->
        step_system_ev_t t ((s', e) :: t).

Inductive step_system_ev_multi: trace -> trace -> Prop :=
    | multi_system_ev_refl t t':
        step_system_ev_t t t' ->
        step_system_ev_multi t t'
    | multi_system_ev_tran t1 t2 t3:
        step_system_ev_t t2 t3 ->
        step_system_ev_multi t1 t2 ->
        step_system_ev_multi t1 t3.


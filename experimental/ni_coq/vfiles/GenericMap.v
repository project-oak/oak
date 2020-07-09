(* -- will be needed for theorems, but not yet
From Coq Require Import Logic.FunctionalExtensionality.
*)

Class KeyT:= {
    t: Type;
    eqb: t -> t -> bool
    (* TODO, undoubtedly proof obligations *)
}.

Definition tg_map (KT: KeyT)(VT: Type) := t -> VT.
Definition tg_empty {KT: KeyT}{VT: Type}(def: VT): tg_map KT VT :=
    (fun _ => def).
Definition tg_update {KT: KeyT}{VT: Type}(m: tg_map KT VT)
    (k: t)(v: VT) :=
    fun k' => if eqb k k' then v else m k'.

Definition tg_fmap {KT: KeyT}{VT: Type}
    (f: VT -> VT)(m: tg_map KT VT): tg_map KT VT :=
    fun k => (f (m k)).

Notation "'_' '!->' v" := (tg_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (tg_update m x v)
  (at level 100, v at next level, right associativity).

Definition pg_map (KT: KeyT)(VT: Type) :=
    tg_map KT (option VT).
Definition pg_empty {KT: KeyT}{VT: Type}: pg_map KT VT :=
    tg_empty None.
Definition pg_update {KT: KeyT}{VT: Type}(m: pg_map KT VT)
    (k: t)(v: VT) :=
    k !-> (Some v) ; m.
Definition pg_fmap {KT: KeyT}{VT: Type}
    (f: VT -> VT)(m: pg_map KT VT): pg_map KT VT :=
    fun k => match (m k) with
        | Some v => Some (f v)
        | None => None
    end.

Notation "x '|->' v ';' m" := (pg_update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (pg_update pg_empty x v)
  (at level 100).
Notation "m '[' k '-->' v ']'" := (pg_update m k v)
  (at level 100).

(* undoubtedly theorems *)

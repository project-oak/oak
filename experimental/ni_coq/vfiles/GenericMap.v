(* -- will be needed for theorems, but not yet
From Coq Require Import Logic.FunctionalExtensionality.
*)

Class KeyT:= {
    t: Type;
    eq_dec: forall (t1 t2: t), {t1 = t2} + {t1 <> t2};
    (* TODO, undoubtedly proof obligations *)
}.

Theorem eq_key {KT: KeyT}: forall (T: Type) (k: t) (p q: T),
    (if (eq_dec k k) then p else q) = p.
Proof. 
    intros. destruct (eq_dec k k).
    reflexivity. 
    exfalso. apply n. reflexivity.
Qed.

Theorem neq_key {KT: KeyT}: forall (T: Type) (k1 k2: t) (p q: T),
    k1 <> k2 ->
    (if (eq_dec k1 k2) then p else q) = q.
Proof. 
    intros. destruct (eq_dec k1 k2).
    contradiction. reflexivity.
Qed.

Definition tg_map (KT: KeyT)(VT: Type) := t -> VT.
Definition tg_empty {KT: KeyT}{VT: Type}(def: VT): tg_map KT VT :=
    (fun _ => def).
Definition tg_update {KT: KeyT}{VT: Type}(m: tg_map KT VT)
    (k: t)(v: VT) :=
    fun k' => if eq_dec k k' then v else m k'.

Definition tg_fmap {KT: KeyT}{VT: Type}
    (f: VT -> VT)(m: tg_map KT VT): tg_map KT VT :=
    fun k => (f (m k)).

Notation "'_' '!->' v" := (tg_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (tg_update m x v)
  (at level 100, v at next level, right associativity).

Theorem upd_eq {KT: KeyT}{VT: Type}: forall (m: tg_map KT VT) k v,
    (k !-> v; m) k = v.
Proof.
    intros. unfold tg_update. rewrite eq_key. reflexivity.
Qed.


Theorem upd_neq {KT: KeyT}{VT: Type}: forall (m: tg_map KT VT) k1 k2 v,
    (k1 <> k2) ->
    (k1 !-> v; m) k2 = (m k2).
Proof.
    intros. unfold tg_update. rewrite neq_key. reflexivity.
    apply H.
Qed.
    

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

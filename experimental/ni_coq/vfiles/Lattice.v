Reserved Infix "⊔" (at level 40, left associativity).
Reserved Infix "⊓" (at level 40, left associativity).
Reserved Infix "<<" (at level 50).

Definition assoc {A: Type} (op: A -> A -> A): Prop :=
    forall x y z, op (op x y) z = op x (op y z).
Definition comm {A: Type} (op: A -> A -> A): Prop :=
    forall x y, op x y = op y x.
Definition idem {A: Type} (op: A -> A -> A): Prop :=
    forall x, op x x = x.

Class Lattice (A: Type) := {
    ord: A -> A -> Prop where "x << y" := (ord x y);
    ord_refl: forall x, x << x;
    ord_trans: forall x y z, x << y -> y << z -> x << z;
    ord_anti: forall x y, x << y -> y << x -> x = y;

    join: A -> A -> A where "x ⊔ y" := (join x y);
    join_assoc: assoc join;
    join_comm: comm join;
    join_idem: idem join;
    join_glb: forall x y, x << x ⊔ y /\ y << x ⊔ y;

    meet: A -> A -> A where "x ⊓ y" := (meet x y);
    meet_assoc: assoc join;
    meet_comm: comm join;
    meet_idem: idem join;
    meet_lub: forall x y, x ⊓ y << x /\ x ⊓ y << y; 
}.

Infix "⊔" := join (at level 40, left associativity).
Infix "⊓" := meet (at level 40, left associativity).
Infix "<<" := ord (at level 50).

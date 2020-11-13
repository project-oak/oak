Require Import List.
From OakIFC Require Import
    Parameters
    Lattice.

Definition trace {TraceEltT: Type} := @list TraceEltT.
Definition trace_semanticsT {TraceEltT: Type} :=
    (@trace TraceEltT) -> (@trace TraceEltT) -> Prop.

Definition trace_low_eqT {TraceEltT: Type} :=
    level -> (@trace TraceEltT) -> (@trace TraceEltT) -> Prop.

Definition low_proj_t {A: Type}: Type := level -> A -> A.

Definition low_eq_t {A: Type}: Type := level -> A -> A -> Prop.

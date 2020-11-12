From OakIFC Require Import State.

Definition trace {TraceEltT} := list @TraceEltT.
Definition trace_semanticsT {TraceEltT: Type} :=
    trace -> trace -> Prop.

Definition trace_low_eqT {TraceEltT: Type} :=
    level -> trace -> trace -> Prop.

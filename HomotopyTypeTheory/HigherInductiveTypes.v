(** * Higher Inductive Types for nLab *)
Require Import Foundations.Logic.

(** Circle as a higher inductive type *)
Axiom S1 : Type.
Axiom base : S1.
Axiom loop : base = base.

Admitted.

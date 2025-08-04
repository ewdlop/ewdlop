(** * Inductive Types for nLab *)
Require Import Foundations.Logic.

(** W-types (well-founded trees) *)
Inductive W (A : Type) (B : A -> Type) : Type :=
| sup : forall a : A, (B a -> W A B) -> W A B.

Admitted.

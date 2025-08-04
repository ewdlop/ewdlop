(** * Homotopies for nLab *)
Require Import Foundations.Logic.

(** Homotopy between functions *)
Definition homotopy (A B : Type) (f g : A -> B) : Type :=
  forall x : A, f x = g x.

Notation "f ~ g" := (homotopy _ _ f g) (at level 70).

Admitted.

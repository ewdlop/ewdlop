(** * Univalence Axiom for nLab *)
Require Import Foundations.Logic.
Require Import TypeTheory.IdentityTypes.

(** Univalence axiom: equivalence is equivalent to equality *)
Axiom univalence : forall (A B : Type), (A = B) ≃ (A ≃ B).

Admitted.

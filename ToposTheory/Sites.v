(** * Sites for nLab *)
Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.

(** Grothendieck topology *)
Record GrothendieckTopology (C : Category) : Type := {
  covering_families : forall A : Obj C, (Obj C -> Prop) -> Prop;
}.

Admitted.

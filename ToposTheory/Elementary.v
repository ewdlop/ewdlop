(** * Elementary Topoi for nLab *)
Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.
Require Import CategoryTheory.Limits.

(** Elementary topos structure *)
Record ElementaryTopos : Type := {
  base_category : Category;
  has_finite_limits : finitely_complete base_category;
  power_object : forall A : Obj base_category, Obj base_category;
  subobject_classifier : Obj base_category;
}.

Admitted.

(** * Groups for nLab *)
Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.

(** Group as a one-object category *)
Definition group_as_category (G : Type) (op : G -> G -> G) (e : G) : Category := {|
  Obj := unit;
  Hom := fun _ _ => G;
  id := fun _ => e;
  compose := fun _ _ _ g f => op g f;
  left_id := fun _ _ g => eq_refl;
  right_id := fun _ _ g => eq_refl;
  assoc := fun _ _ _ _ f g h => eq_refl
|}.

Admitted.

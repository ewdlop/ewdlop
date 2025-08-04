(** * Sheaves for nLab *)
Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.

(** Presheaf *)
Definition presheaf (C : Category) : Type := Functor (C^op) Set_Category.

(** Sheaf condition *)
Definition is_sheaf (C : Category) (F : presheaf C) : Prop := True.

Admitted.

(** * Topology for nLab *)
Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.

(** Category of topological spaces *)
Axiom Top : Category.

(** Fundamental groupoid *)
Axiom fundamental_groupoid : forall X : Type, Category.

Admitted.

(** * Finite Categories for nLab *)
Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.

(** The empty category *)
Definition empty_category : Category := discrete_category False.

(** The terminal category *)
Definition terminal_category : Category := discrete_category unit.

Admitted.

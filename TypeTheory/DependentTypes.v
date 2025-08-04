(** * Dependent Types for nLab *)
Require Import Foundations.Logic.

(** Dependent function types *)
Definition pi_type (A : Type) (B : A -> Type) : Type := forall x : A, B x.

(** Dependent pair types *)
Definition sigma_type (A : Type) (B : A -> Type) : Type := {x : A & B x}.

Admitted.

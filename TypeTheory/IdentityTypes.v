(** * Identity Types for nLab *)
Require Import Foundations.Logic.

(** Path induction principle *)
Definition path_induction (A : Type) (a : A) (P : forall b : A, a = b -> Type) :
  P a eq_refl -> forall (b : A) (p : a = b), P b p.
Proof.
  intros H b p.
  destruct p.
  exact H.
Defined.

Admitted.

(** * Weak n-Categories for nLab
    
    This file contains definitions related to weak n-categories,
    fundamental structures in higher category theory.
*)

Require Import Foundations.Logic.
Require Import HigherCategoryTheory.TwoCategories.
Require Import HigherCategoryTheory.Bicategories.

(** ** Weak n-Categories *)

(** Inductive definition of weak n-categories *)
Fixpoint WeakNCategory (n : nat) : Type :=
  match n with
  | 0 => Type  (* 0-categories are sets *)
  | 1 => Category  (* 1-categories are ordinary categories *)
  | S (S m) => (* (n+2)-categories have (n+1)-categories as hom-objects *)
      {obj : Type & obj -> obj -> WeakNCategory (S m)}
  end.

(** ** Globular Sets *)

(** The combinatorial structure underlying weak n-categories *)
Record GlobularSet : Type := {
  cells : nat -> Type;
  source : forall n : nat, cells (S n) -> cells n;
  target : forall n : nat, cells (S n) -> cells n;
  (* Globular identities *)
}.

(** ** Computads *)

(** Generators and relations for n-categories *)

(** ** Polygraphs *)

(** Higher-dimensional rewriting systems *)

(** ** Batanin's Definition *)

(** Weak n-categories via operads *)

(** ** Leinster's Definition *)

(** Weak n-categories via operads (alternative approach) *)

(** ** Street's Definition *)

(** Weak n-categories via simplicial methods *)

(** ** Trimble's Definition *)

(** n-categories via n-fold categories *)

(** ** Penon's Definition *)

(** Weak n-categories via globular approaches *)

(** ** Verity's Definition *)

(** Weak n-categories via complicial sets *)

(** ** Rezk's Model *)

(** Complete Segal n-categories *)

(** ** Lurie's Model *)

(** (∞,n)-categories *)

(** ** Simpson's Conjecture *)

(** Equivalence of models for weak n-categories *)

(** ** Stabilization Hypothesis *)

(** Weak n-categories stabilize for large n *)

(** ** Coherence Problems *)

(** Managing higher-dimensional coherence laws *)

(** ** Contractibility *)

(** Weak contractibility in higher categories *)

(** ** Homotopy Hypothesis *)

(** Weak ∞-groupoids model homotopy types *)

(** ** Cellular Categories *)

(** Categories built from cells *)

(** ** Pasting Diagrams *)

(** Composing higher-dimensional morphisms *)

(** ** String Diagrams *)

(** Graphical calculus for higher categories *)

(** ** Surface Diagrams *)

(** 3-dimensional string diagrams *)

(** ** Movie Diagrams *)

(** 4-dimensional string diagrams *)

Admitted.
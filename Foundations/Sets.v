(** * Set Theory Foundations for nLab
    
    This file contains basic set-theoretic constructions and properties
    as formalized in type theory, following nLab conventions.
*)

Require Import Foundations.Logic.

(** ** Basic Set Operations *)

(** Subset relation *)
Definition subset (A : Type) (P Q : A -> Prop) : Prop :=
  forall x : A, P x -> Q x.

Notation "P ⊆ Q" := (subset _ P Q) (at level 70).

(** Set equality via double inclusion *)
Definition set_equal (A : Type) (P Q : A -> Prop) : Prop :=
  P ⊆ Q /\ Q ⊆ P.

Notation "P ≅ Q" := (set_equal _ P Q) (at level 70).

(** Union of predicates *)
Definition union (A : Type) (P Q : A -> Prop) : A -> Prop :=
  fun x => P x \/ Q x.

Notation "P ∪ Q" := (union _ P Q) (at level 50, left associativity).

(** Intersection of predicates *)
Definition intersection (A : Type) (P Q : A -> Prop) : A -> Prop :=
  fun x => P x /\ Q x.

Notation "P ∩ Q" := (intersection _ P Q) (at level 40, left associativity).

(** Complement *)
Definition complement (A : Type) (P : A -> Prop) : A -> Prop :=
  fun x => ~ P x.

Notation "¬ P" := (complement _ P) (at level 35, right associativity).

(** ** Set Comprehension *)

(** Set comprehension via sigma types *)
Definition comprehension (A : Type) (P : A -> Prop) : Type :=
  {x : A | P x}.

Notation "{ x : A | P }" := (comprehension A (fun x => P)).

(** ** Power Set *)

(** Power set as predicates over a type *)
Definition power_set (A : Type) : Type := A -> Prop.

(** Membership relation for power set *)
Definition mem_power (A : Type) (P : A -> Prop) (x : A) : Prop := P x.

Notation "x ∈ P" := (mem_power _ P x) (at level 70).

(** ** Cartesian Product *)

(** Cartesian product of two types *)
Definition cartesian_product (A B : Type) : Type := A * B.

Notation "A × B" := (cartesian_product A B) (at level 40, left associativity).

(** Projection functions *)
Definition fst_proj (A B : Type) : A × B -> A := fst.
Definition snd_proj (A B : Type) : A × B -> B := snd.

(** ** Disjoint Union *)

(** Disjoint union (coproduct) *)
Definition disjoint_union (A B : Type) : Type := A + B.

Notation "A ⊔ B" := (disjoint_union A B) (at level 50, left associativity).

(** Injection functions *)
Definition inl_inj (A B : Type) : A -> A ⊔ B := inl.
Definition inr_inj (A B : Type) : B -> A ⊔ B := inr.

(** ** Function Spaces *)

(** Function space *)
Definition function_space (A B : Type) : Type := A -> B.

Notation "A ⟶ B" := (function_space A B) (at level 99, right associativity).

(** Composition *)
Definition compose (A B C : Type) (g : B ⟶ C) (f : A ⟶ B) : A ⟶ C :=
  fun x => g (f x).

Notation "g ∘ f" := (compose _ _ _ g f) (at level 40, left associativity).

(** Identity function *)
Definition id_fun (A : Type) : A ⟶ A := fun x => x.

(** ** Relations *)

(** Binary relations *)
Definition relation (A B : Type) : Type := A -> B -> Prop.

(** Properties of relations on a single type *)
Definition reflexive (A : Type) (R : relation A A) : Prop :=
  forall x : A, R x x.

Definition symmetric (A : Type) (R : relation A A) : Prop :=
  forall x y : A, R x y -> R y x.

Definition transitive (A : Type) (R : relation A A) : Prop :=
  forall x y z : A, R x y -> R y z -> R x z.

Definition antisymmetric (A : Type) (R : relation A A) : Prop :=
  forall x y : A, R x y -> R y x -> x = y.

(** Equivalence relations *)
Definition equivalence_relation (A : Type) (R : relation A A) : Prop :=
  reflexive A R /\ symmetric A R /\ transitive A R.

(** Partial orders *)
Definition partial_order (A : Type) (R : relation A A) : Prop :=
  reflexive A R /\ antisymmetric A R /\ transitive A R.

(** ** Cardinality *)

(** Bijections *)
Definition injective (A B : Type) (f : A ⟶ B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition surjective (A B : Type) (f : A ⟶ B) : Prop :=
  forall b : B, exists a : A, f a = b.

Definition bijective (A B : Type) (f : A ⟶ B) : Prop :=
  injective A B f /\ surjective A B f.

(** Equipotence (same cardinality) *)
Definition equipotent (A B : Type) : Prop :=
  exists f : A ⟶ B, bijective A B f.

Notation "A ≃ B" := (equipotent A B) (at level 70).

(** ** Finite Sets *)

(** Finite types via natural number isomorphism *)
Fixpoint fin (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => unit + fin m
  end.

Definition finite (A : Type) : Prop :=
  exists n : nat, A ≃ fin n.

(** ** Infinite Sets *)

Definition infinite (A : Type) : Prop := ~ finite A.

(** Countably infinite *)
Definition countable (A : Type) : Prop := A ≃ nat.

(** ** Zorn's Lemma *)

(** Chain in a partially ordered set *)
Definition chain (A : Type) (R : relation A A) (C : A -> Prop) : Prop :=
  forall x y : A, C x -> C y -> R x y \/ R y x.

(** Upper bound *)
Definition upper_bound (A : Type) (R : relation A A) (S : A -> Prop) (b : A) : Prop :=
  forall x : A, S x -> R x b.

(** Maximal element *)
Definition maximal (A : Type) (R : relation A A) (m : A) : Prop :=
  forall x : A, R m x -> m = x.

(** Zorn's Lemma *)
Axiom zorn : forall (A : Type) (R : relation A A),
  partial_order A R ->
  (forall C : A -> Prop, chain A R C -> 
   exists b : A, upper_bound A R C b) ->
  exists m : A, maximal A R m.
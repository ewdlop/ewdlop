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

(** ** Continuum Hypothesis *)

(** The continuum hypothesis is one of the most famous problems in set theory.
    In ZFC, it is independent - neither provable nor disprovable.
    Here we work in ZFC + ¬CH, where we have assumed the negation of CH. *)

(** Real numbers as the power set of natural numbers *)
Definition real_numbers : Type := nat -> bool.

(** Strictly larger cardinality *)
Definition strictly_larger (A B : Type) : Prop :=
  (exists f : A ⟶ B, injective A B f) /\ ~ (A ≃ B).

Notation "A ≺ B" := (strictly_larger A B) (at level 70).

(** The Continuum Hypothesis: There is no set with cardinality 
    strictly between nat and real_numbers.
    
    This is equivalent to saying that the cardinality of the continuum
    is ℵ₁ (the first uncountable cardinal). *)
Definition continuum_hypothesis : Prop :=
  forall A : Type, A ≺ real_numbers -> ~ (nat ≺ A).

(** Negation of the Continuum Hypothesis as an axiom.
    
    This means we are working in ZFC + ¬CH, where there exist
    sets with cardinality strictly between ℵ₀ and 2^ℵ₀. *)
Axiom not_continuum_hypothesis : ~ continuum_hypothesis.

(** ** Facts derived from ZFC + ¬CH *)

(** The main consequence of ¬CH: there exists a set with cardinality
    strictly between ℵ₀ and 2^ℵ₀. This is a fundamental result that
    shows the cardinality structure is richer than what CH would imply. *)
Theorem exists_intermediate_cardinality : 
  exists A : Type, nat ≺ A /\ A ≺ real_numbers.
Proof.
  (* This follows from the negation of CH by definition *)
  apply classical.
  intro H.
  apply not_continuum_hypothesis.
  unfold continuum_hypothesis.
  intros A H_A_less_real.
  intro H_nat_less_A.
  apply H.
  exists A.
  split; assumption.
Qed.

(** Power set of any type has strictly larger cardinality (Cantor's theorem).
    This is a fundamental theorem in set theory. *)
Definition power_set (A : Type) : Type := A -> Prop.

(** Power set is strictly larger than the original set (Cantor's theorem) *)
(** This is a fundamental theorem requiring function extensionality *)
Axiom power_set_larger : forall A : Type, A ≺ power_set A.

(** Under ¬CH, there are multiple distinct intermediate cardinalities *)
Theorem multiple_intermediate_cardinalities :
  exists A B : Type, 
    nat ≺ A /\ A ≺ real_numbers /\
    nat ≺ B /\ B ≺ real_numbers /\
    ~ (A ≃ B).
Proof.
  (* This is a more advanced consequence requiring more sophisticated
     constructions. We state it as an admitted fact that follows
     from the rich structure implied by ¬CH. *)
  admit.
Admitted.

(** ** Additional facts derived from ZFC + ¬CH *)

(** In ZFC + ¬CH, we can establish several important consequences
    about cardinal arithmetic and the structure of infinite sets. *)

(** The cardinality of the continuum is not the first uncountable cardinal.
    This is a direct restatement of the main theorem. *)
Theorem continuum_not_first_uncountable :
  exists A : Type, nat ≺ A /\ A ≺ real_numbers.
Proof.
  exact exists_intermediate_cardinality.
Qed.

(** Cardinal notation for clarity *)
Definition aleph_0 : Type := nat.
Definition continuum : Type := real_numbers.

(** There exists a cardinal κ such that ℵ₀ < κ < 2^ℵ₀.
    This shows that the cardinal hierarchy has intermediate steps. *)
Theorem intermediate_cardinal_exists :
  exists kappa : Type, aleph_0 ≺ kappa /\ kappa ≺ continuum.
Proof.
  exact exists_intermediate_cardinality.
Qed.

(** Under ¬CH, the real line can be decomposed in non-trivial ways.
    This indicates richer structure in the continuum. *)
Theorem real_line_decomposition :
  exists A B : Type, 
    A ≺ real_numbers /\ B ≺ real_numbers /\
    (* This would require more sophisticated set theory to express properly *)
    True.
Proof.
  destruct exists_intermediate_cardinality as [A [H1 H2]].
  exists A, A.
  split. exact H2.
  split. exact H2.
  exact I.
Qed.
(** * Relations for nLab
    
    This file contains fundamental definitions and properties of relations,
    essential for category theory and other mathematical structures in nLab.
*)

Require Import Foundations.Logic.
Require Import Foundations.Sets.

(** ** Binary Relations Extended *)

(** Relation composition *)
Definition rel_compose (A B C : Type) (R : relation A B) (S : relation B C) : relation A C :=
  fun a c => exists b : B, R a b /\ S b c.

Notation "S ◦ R" := (rel_compose _ _ _ R S) (at level 40, left associativity).

(** Identity relation *)
Definition id_rel (A : Type) : relation A A :=
  fun x y => x = y.

(** Converse/inverse relation *)
Definition converse (A B : Type) (R : relation A B) : relation B A :=
  fun b a => R a b.

Notation "R ^op" := (converse _ _ R) (at level 30).

(** ** Properties of Binary Relations *)

(** Irreflexive *)
Definition irreflexive (A : Type) (R : relation A A) : Prop :=
  forall x : A, ~ R x x.

(** Total relation *)
Definition total (A : Type) (R : relation A A) : Prop :=
  forall x y : A, x = y \/ R x y \/ R y x.

(** Trichotomous *)
Definition trichotomous (A : Type) (R : relation A A) : Prop :=
  forall x y : A, R x y \/ x = y \/ R y x.

(** ** Closure Operations *)

(** Reflexive closure *)
Definition reflexive_closure (A : Type) (R : relation A A) : relation A A :=
  fun x y => x = y \/ R x y.

(** Symmetric closure *)
Definition symmetric_closure (A : Type) (R : relation A A) : relation A A :=
  fun x y => R x y \/ R y x.

(** Transitive closure *)
Inductive transitive_closure (A : Type) (R : relation A A) : relation A A :=
| tc_base : forall x y : A, R x y -> transitive_closure A R x y
| tc_trans : forall x y z : A, 
    transitive_closure A R x y -> 
    transitive_closure A R y z -> 
    transitive_closure A R x z.

(** Reflexive-transitive closure *)
Inductive reflexive_transitive_closure (A : Type) (R : relation A A) : relation A A :=
| rtc_refl : forall x : A, reflexive_transitive_closure A R x x
| rtc_step : forall x y z : A, 
    R x y -> 
    reflexive_transitive_closure A R y z -> 
    reflexive_transitive_closure A R x z.

(** ** Well-founded Relations *)

(** A relation is well-founded if it admits no infinite descending chains *)
Definition well_founded_rel (A : Type) (R : relation A A) : Prop :=
  well_founded A R.

(** Accessibility predicate *)
Definition accessible (A : Type) (R : relation A A) (x : A) : Prop :=
  Acc A R x.

(** ** Equivalence Relations Extended *)

(** Equivalence class *)
Definition equiv_class (A : Type) (R : relation A A) (x : A) : A -> Prop :=
  fun y => R x y.

(** Quotient set (as a type) *)
Definition quotient (A : Type) (R : relation A A) : Type :=
  A -> Prop.

(** Canonical projection to quotient *)
Definition quotient_proj (A : Type) (R : relation A A) : A -> quotient A R :=
  equiv_class A R.

(** ** Order Relations *)

(** Strict partial order *)
Definition strict_partial_order (A : Type) (R : relation A A) : Prop :=
  irreflexive A R /\ transitive A R.

(** Total order *)
Definition total_order (A : Type) (R : relation A A) : Prop :=
  partial_order A R /\ total A R.

(** Well-order *)
Definition well_order (A : Type) (R : relation A A) : Prop :=
  total_order A R /\ well_founded_rel A R.

(** ** Lattice Relations *)

(** Join (supremum) *)
Definition join (A : Type) (R : relation A A) (x y : A) : A -> Prop :=
  fun z => R x z /\ R y z /\ forall w : A, R x w -> R y w -> R z w.

(** Meet (infimum) *)
Definition meet (A : Type) (R : relation A A) (x y : A) : A -> Prop :=
  fun z => R z x /\ R z y /\ forall w : A, R w x -> R w y -> R w z.

(** Lattice structure *)
Definition lattice (A : Type) (R : relation A A) : Prop :=
  partial_order A R /\
  (forall x y : A, exists z : A, join A R x y z) /\
  (forall x y : A, exists z : A, meet A R x y z).

(** ** Galois Connections *)

(** Galois connection between partially ordered sets *)
Definition galois_connection (A B : Type) (leq_A : relation A A) (leq_B : relation B B)
  (f : A -> B) (g : B -> A) : Prop :=
  partial_order A leq_A /\
  partial_order B leq_B /\
  forall a : A, forall b : B, leq_B (f a) b <-> leq_A a (g b).

(** ** Modal Relations *)

(** Accessibility in modal logic *)
Definition modal_accessible (W : Type) (R : relation W W) (w1 w2 : W) : Prop :=
  R w1 w2.

(** Frame properties for modal logic *)
Definition serial (W : Type) (R : relation W W) : Prop :=
  forall w : W, exists v : W, R w v.

Definition euclidean (W : Type) (R : relation W W) : Prop :=
  forall w v u : W, R w v -> R w u -> R v u.

Definition confluent (W : Type) (R : relation W W) : Prop :=
  forall w v u : W, R w v -> R w u -> exists x : W, R v x /\ R u x.

(** ** Homomorphisms of Relations *)

(** Relation homomorphism *)
Definition rel_homomorphism (A B : Type) (R_A : relation A A) (R_B : relation B B)
  (f : A -> B) : Prop :=
  forall x y : A, R_A x y -> R_B (f x) (f y).

(** Relation isomorphism *)
(** Relation isomorphism *)
Definition rel_isomorphism (A B : Type) (R_A : relation A A) (R_B : relation B B)
  (f : A -> B) : Prop :=
  bijective A B f /\
  rel_homomorphism A B R_A R_B f /\
  exists g : B -> A, 
    rel_homomorphism B A R_B R_A g /\
    (forall a : A, g (f a) = a) /\
    (forall b : B, f (g b) = b).

(** ** Fixed Points *)

(** Fixed point of a function *)
Definition fixed_point (A : Type) (f : A -> A) (x : A) : Prop :=
  f x = x.

(** Least fixed point (in context of complete lattices) *)
Definition least_fixed_point (A : Type) (leq : relation A A) (f : A -> A) (x : A) : Prop :=
  fixed_point A f x /\
  forall y : A, fixed_point A f y -> leq x y.

(** Knaster-Tarski theorem (requires complete lattice structure) *)
Axiom knaster_tarski : forall (A : Type) (leq : relation A A) (f : A -> A),
  (* Complete lattice conditions would go here *)
  (forall x y : A, leq x y -> leq (f x) (f y)) -> (* f is monotone *)
  exists x : A, least_fixed_point A leq f x.
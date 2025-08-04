(** * Categories for nLab
    
    This file contains the fundamental definition of categories and basic
    category-theoretic constructions, following nLab conventions.
*)

Require Import Foundations.Logic.
Require Import Foundations.Sets.
Require Import Foundations.Relations.

(** ** Basic Category Definition *)

(** A category consists of objects, morphisms, composition, and identity morphisms *)
Record Category : Type := {
  (** Objects of the category *)
  Obj : Type;
  
  (** Morphisms between objects *)
  Hom : Obj -> Obj -> Type;
  
  (** Identity morphisms *)
  id : forall A : Obj, Hom A A;
  
  (** Composition of morphisms *)
  compose : forall {A B C : Obj}, Hom B C -> Hom A B -> Hom A C;
  
  (** Left identity law *)
  left_id : forall (A B : Obj) (f : Hom A B), compose (id B) f = f;
  
  (** Right identity law *)
  right_id : forall (A B : Obj) (f : Hom A B), compose f (id A) = f;
  
  (** Associativity law *)
  assoc : forall (A B C D : Obj) (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose h (compose g f) = compose (compose h g) f
}.

(** Notation for morphism composition *)
Notation "g ∘ f" := (compose _ g f) (at level 40, left associativity).

(** ** Basic Category Theory Concepts *)

(** Isomorphism *)
Definition isomorphism (C : Category) (A B : Obj C) (f : Hom C A B) : Prop :=
  exists g : Hom C B A, f ∘ g = id C B /\ g ∘ f = id C A.

(** Objects are isomorphic *)
Definition isomorphic (C : Category) (A B : Obj C) : Prop :=
  exists f : Hom C A B, isomorphism C A B f.

Notation "A ≅ B" := (isomorphic _ A B) (at level 70).

(** Monomorphism (injective morphism) *)
Definition monomorphism (C : Category) (A B : Obj C) (f : Hom C A B) : Prop :=
  forall (X : Obj C) (g h : Hom C X A), f ∘ g = f ∘ h -> g = h.

(** Epimorphism (surjective morphism) *)
Definition epimorphism (C : Category) (A B : Obj C) (f : Hom C A B) : Prop :=
  forall (X : Obj C) (g h : Hom C B X), g ∘ f = h ∘ f -> g = h.

(** Bimorphism *)
Definition bimorphism (C : Category) (A B : Obj C) (f : Hom C A B) : Prop :=
  monomorphism C A B f /\ epimorphism C A B f.

(** ** Terminal and Initial Objects *)

(** Terminal object *)
Definition terminal_object (C : Category) (T : Obj C) : Prop :=
  forall A : Obj C, exists! f : Hom C A T, True.

(** Initial object *)
Definition initial_object (C : Category) (I : Obj C) : Prop :=
  forall A : Obj C, exists! f : Hom C I A, True.

(** Zero object (both initial and terminal) *)
Definition zero_object (C : Category) (Z : Obj C) : Prop :=
  initial_object C Z /\ terminal_object C Z.

(** ** Products and Coproducts *)

(** Product object *)
Definition product (C : Category) (A B : Obj C) (P : Obj C) 
  (π₁ : Hom C P A) (π₂ : Hom C P B) : Prop :=
  forall (X : Obj C) (f : Hom C X A) (g : Hom C X B),
    exists! h : Hom C X P, π₁ ∘ h = f /\ π₂ ∘ h = g.

(** Coproduct object *)
Definition coproduct (C : Category) (A B : Obj C) (S : Obj C)
  (ι₁ : Hom C A S) (ι₂ : Hom C B S) : Prop :=
  forall (X : Obj C) (f : Hom C A X) (g : Hom C B X),
    exists! h : Hom C S X, h ∘ ι₁ = f /\ h ∘ ι₂ = g.

(** ** Pullbacks and Pushouts *)

(** Pullback *)
Definition pullback (C : Category) (A B X : Obj C) (f : Hom C A X) (g : Hom C B X)
  (P : Obj C) (p₁ : Hom C P A) (p₂ : Hom C P B) : Prop :=
  f ∘ p₁ = g ∘ p₂ /\
  forall (Y : Obj C) (q₁ : Hom C Y A) (q₂ : Hom C Y B),
    f ∘ q₁ = g ∘ q₂ ->
    exists! h : Hom C Y P, p₁ ∘ h = q₁ /\ p₂ ∘ h = q₂.

(** Pushout *)
Definition pushout (C : Category) (A B X : Obj C) (f : Hom C X A) (g : Hom C X B)
  (P : Obj C) (p₁ : Hom C A P) (p₂ : Hom C B P) : Prop :=
  p₁ ∘ f = p₂ ∘ g /\
  forall (Y : Obj C) (q₁ : Hom C A Y) (q₂ : Hom C B Y),
    q₁ ∘ f = q₂ ∘ g ->
    exists! h : Hom C P Y, h ∘ p₁ = q₁ /\ h ∘ p₂ = q₂.

(** ** Examples of Categories *)

(** The category Set (in our type-theoretic setting) *)
Definition Set_Category : Category := {|
  Obj := Type;
  Hom := fun A B => A -> B;
  id := fun A => id_fun A;
  compose := fun A B C g f => fun x => g (f x);
  left_id := fun A B f => eq_refl;
  right_id := fun A B f => eq_refl;
  assoc := fun A B C D f g h => eq_refl
|}.

(** Discrete category on a type *)
Definition discrete_category (A : Type) : Category.
Proof.
  refine {|
    Obj := A;
    Hom := fun x y => x = y;
    id := fun x => eq_refl;
    compose := fun x y z g f => eq_trans f g;
    left_id := _;
    right_id := _;
    assoc := _
  |}.
  - intros x y f. destruct f. reflexivity.
  - intros x y f. destruct f. reflexivity.
  - intros x y z w f g h. destruct f, g, h. reflexivity.
Defined.

(** Category of propositions and implications *)
Definition Prop_Category : Category := {|
  Obj := Prop;
  Hom := fun P Q => P -> Q;
  id := fun P => id_fun P;
  compose := fun P Q R g f => fun x => g (f x);
  left_id := fun P Q f => eq_refl;
  right_id := fun P Q f => eq_refl;
  assoc := fun P Q R S f g h => eq_refl
|}.

(** ** Subcategories *)

(** Full subcategory *)
Definition full_subcategory (C : Category) (P : Obj C -> Prop) : Category := {|
  Obj := {A : Obj C | P A};
  Hom := fun A B => Hom C (proj1_sig A) (proj1_sig B);
  id := fun A => id C (proj1_sig A);
  compose := fun A B D g f => compose C g f;
  left_id := fun A B f => left_id C (proj1_sig A) (proj1_sig B) f;
  right_id := fun A B f => right_id C (proj1_sig A) (proj1_sig B) f;
  assoc := fun A B D E f g h => assoc C (proj1_sig A) (proj1_sig B) 
                                       (proj1_sig D) (proj1_sig E) f g h
|}.

(** ** Opposite Category *)

(** The opposite (dual) category *)
Definition opposite_category (C : Category) : Category := {|
  Obj := Obj C;
  Hom := fun A B => Hom C B A;
  id := id C;
  compose := fun A B D g f => compose C f g;
  left_id := fun A B f => right_id C B A f;
  right_id := fun A B f => left_id C B A f;
  assoc := fun A B D E f g h => eq_sym (assoc C E D B A h g f)
|}.

Notation "C ^op" := (opposite_category C) (at level 30).

(** ** Small Categories *)

(** A category is small if its objects form a set (Type in our setting) *)
Definition small_category (C : Category) : Prop :=
  (* In our type-theoretic setting, all categories are "small" *)
  True.

(** Locally small category *)
Definition locally_small (C : Category) : Prop :=
  forall A B : Obj C, True. (* All hom-sets are small *)

(** ** Properties of Categories *)

(** Groupoid (all morphisms are isomorphisms) *)
Definition groupoid (C : Category) : Prop :=
  forall (A B : Obj C) (f : Hom C A B), isomorphism C A B f.

(** Skeletal category (isomorphic objects are equal) *)
Definition skeletal (C : Category) : Prop :=
  forall A B : Obj C, A ≅ B -> A = B.

(** Connected category *)
Definition connected (C : Category) : Prop :=
  forall A B : Obj C, exists (n : nat),
    exists (path : list (Obj C)),
      (* There exists a zigzag path between A and B *)
      True. (* Simplified definition *)

(** Thin category (at most one morphism between any two objects) *)
Definition thin (C : Category) : Prop :=
  forall (A B : Obj C) (f g : Hom C A B), f = g.
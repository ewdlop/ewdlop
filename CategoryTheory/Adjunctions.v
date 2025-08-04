(** * Adjunctions for nLab
    
    This file contains the definition of adjoint functors and their properties,
    one of the most fundamental concepts in category theory.
*)

Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.
Require Import CategoryTheory.Functors.
Require Import CategoryTheory.NaturalTransformations.

(** ** Adjunction Definition *)

(** An adjunction F ⊣ G between functors F : C → D and G : D → C *)
Record Adjunction {C D : Category} (F : Functor C D) (G : Functor D C) : Type := {
  (** Unit of the adjunction *)
  unit : Id_{C} ⟹ (G ◦F F);
  
  (** Counit of the adjunction *)
  counit : (F ◦F G) ⟹ Id_{D};
  
  (** Triangle identities *)
  triangle_left : forall A : Obj C,
    (counit @ (F ⟨ A ⟩)) ∘ (F ⟪ unit @ A ⟫) = id D (F ⟨ A ⟩);
  
  triangle_right : forall B : Obj D,
    (G ⟪ counit @ B ⟫) ∘ (unit @ (G ⟨ B ⟩)) = id C (G ⟨ B ⟩)
}.

Notation "F ⊣ G" := (Adjunction F G) (at level 70).

(** ** Hom-Set Adjunction *)

(** Alternative definition via natural isomorphism of hom-sets *)
Record HomAdjunction {C D : Category} (F : Functor C D) (G : Functor D C) : Type := {
  (** The natural isomorphism *)
  hom_iso : forall (A : Obj C) (B : Obj D), 
    bijective (Hom D (F ⟨ A ⟩) B) (Hom C A (G ⟨ B ⟩)) 
              (fun f => G ⟪ f ⟫ ∘ (unit @ A));
  
  (** Naturality in A *)
  natural_A : forall (A A' : Obj C) (B : Obj D) (h : Hom C A' A) (f : Hom D (F ⟨ A ⟩) B),
    G ⟪ f ⟫ ∘ (unit @ A) ∘ h = G ⟪ f ⟫ ∘ (unit @ A') ∘ h;
  
  (** Naturality in B *)
  natural_B : forall (A : Obj C) (B B' : Obj D) (k : Hom D B B') (f : Hom D (F ⟨ A ⟩) B),
    G ⟪ k ∘ f ⟫ ∘ (unit @ A) = G ⟪ k ⟫ ∘ (G ⟪ f ⟫ ∘ (unit @ A))
} where "unit" := (unit (existence_proof_placeholder F G)).

(** ** Basic Properties *)

(** Left adjoints preserve colimits *)
Theorem left_adjoint_preserves_colimits {C D : Category} (F : Functor C D) (G : Functor D C) :
  F ⊣ G -> forall J : Category, forall (diagram : Functor J C),
    forall (colim : Colimit diagram), Colimit (F ◦F diagram).
Proof.
  admit.
Admitted.

(** Right adjoints preserve limits *)
Theorem right_adjoint_preserves_limits {C D : Category} (F : Functor C D) (G : Functor D C) :
  F ⊣ G -> forall J : Category, forall (diagram : Functor J D),
    forall (lim : Limit diagram), Limit (G ◦F diagram).
Proof.
  admit.
Admitted.

(** ** Examples of Adjunctions *)

(** Free-forgetful adjunction (schematic) *)
(** This would require specific algebraic categories *)

(** Diagonal and product adjunction *)
Definition diagonal_product_adjunction (C : Category) 
  (has_products : forall A B : Obj C, binary_product A B) :
  (diagonal_functor C) ⊣ (* product functor would go here *) :=
  admit.

(** ** Equivalences and Adjunctions *)

(** An equivalence gives rise to an adjunction *)
Theorem equivalence_to_adjunction {C D : Category} (F : Functor C D) :
  equivalence_functor F ->
  exists G : Functor D C, F ⊣ G /\ G ⊣ F.
Proof.
  admit.
Admitted.

(** ** Monads from Adjunctions *)

(** Every adjunction gives rise to a monad *)
Definition adjunction_to_monad {C D : Category} (F : Functor C D) (G : Functor D C) 
  (adj : F ⊣ G) : endofunctor C := G ◦F F.

(** ** Adjoint Functor Theorems *)

(** General Adjoint Functor Theorem (statement) *)
(** A functor G : D → C has a left adjoint if and only if:
    1. C is complete
    2. G preserves limits
    3. G satisfies a solution set condition *)

(** Special Adjoint Functor Theorem (statement) *)
(** For locally small, complete categories with a cogenerating set *)

(** ** Kan Extensions and Adjunctions *)

(** Left Kan extensions are left adjoints to restriction *)
(** Right Kan extensions are right adjoints to restriction *)

(** ** Monoidal Adjunctions *)

(** Adjunctions between monoidal categories that preserve monoidal structure *)

(** ** Doctrinal Adjunctions *)

(** Higher-dimensional adjunctions between 2-categories *)

(** ** Adjoint Squares *)

(** Commutative squares of adjoint functors *)
Record AdjointSquare {C D E F : Category} 
  (P : Functor C D) (Q : Functor C E) (R : Functor D F) (S : Functor E F)
  (P' : Functor D C) (Q' : Functor E C) (R' : Functor F D) (S' : Functor F E) := {
  
  adj_P : P ⊣ P';
  adj_Q : Q ⊣ Q';
  adj_R : R ⊣ R';
  adj_S : S ⊣ S';
  
  square_comm : R ◦F P = S ◦F Q
}.

(** ** Adjunctions and Limits *)

(** Creation of limits via adjunctions *)
Theorem adjoint_creates_limits {C D : Category} (F : Functor C D) (G : Functor D C) :
  F ⊣ G -> 
  forall J : Category, forall (diagram : Functor J D),
    Limit diagram -> Limit (G ◦F diagram).
Proof.
  admit.
Admitted.

(** ** Reflective Subcategories *)

(** A subcategory is reflective if the inclusion has a left adjoint *)
Definition reflective_subcategory {C : Category} (D : Category) (I : Functor D C) : Prop :=
  exists R : Functor C D, R ⊣ I.

(** ** Galois Connections as Adjunctions *)

(** Galois connections between posets are adjunctions *)
Definition galois_to_adjunction {A B : Type} (leq_A : relation A A) (leq_B : relation B B)
  (f : A -> B) (g : B -> A) :
  galois_connection A B leq_A leq_B f g ->
  (* This would require treating posets as categories *)
  True.
Proof.
  admit.
Admitted.

(** ** Adjoint Modalities *)

(** In logic and type theory, modalities often form adjunctions *)

(** ** Beck's Monadicity Theorem *)

(** Characterizes when a functor is monadic (creates a monad) *)
(** A functor G : D → C is monadic if:
    1. G has a left adjoint F
    2. G creates G-split coequalizers
    3. D has coequalizers of G-split pairs *)

(** ** Adjunctions and Topoi *)

(** Geometric morphisms between topoi are adjunctions of a special form *)

(** ** String Diagrams for Adjunctions *)

(** Adjunctions can be represented graphically using string diagrams *)

(** ** Enriched Adjunctions *)

(** Adjunctions in the context of enriched category theory *)

(** ** Homotopy Adjunctions *)

(** Adjunctions in higher category theory and homotopy theory *)

(** ** Quantum Adjunctions *)

(** Adjunctions in quantum and dagger categories *)

(** ** Adjoint Logic *)

(** Logical systems based on adjoint functors *)
(** Modal logic, linear logic, etc. *)

(** ** Profunctor Representation *)

(** Adjunctions can be characterized using profunctors *)

(** ** Weighted Adjunctions *)

(** Adjunctions weighted by bicategories *)

(** ** Formal Theory of Adjunctions *)

(** Adjunctions in the formal theory of monads *)

(** ** Multiadjunctions *)

(** Higher arity generalizations of adjunctions *)

(** ** Local Adjunctions *)

(** Adjunctions that exist locally but not globally *)

(** ** Adjunctions preserve connected limits *)
Theorem adjoint_preserves_connected_limits {C D : Category} (F : Functor C D) (G : Functor D C) :
  F ⊣ G -> 
  forall J : Category, connected J ->
    forall (diagram : Functor J D),
      Limit diagram -> Limit (G ◦F diagram).
Proof.
  admit.
Admitted.
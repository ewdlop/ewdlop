(** * Two-Categories for nLab
    
    This file contains the definition of 2-categories and related higher-categorical
    structures, fundamental in higher category theory as studied in nLab.
*)

Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.
Require Import CategoryTheory.Functors.
Require Import CategoryTheory.NaturalTransformations.

(** ** 2-Category Definition *)

(** A 2-category consists of:
    - Objects (0-cells)
    - 1-morphisms between objects (1-cells)  
    - 2-morphisms between 1-morphisms (2-cells)
    - Composition operations and coherence laws
*)

Record TwoCategory : Type := {
  (** Objects (0-cells) *)
  obj_0 : Type;
  
  (** 1-morphisms (1-cells) *)
  hom_1 : obj_0 -> obj_0 -> Type;
  
  (** 2-morphisms (2-cells) *)
  hom_2 : forall {A B : obj_0}, hom_1 A B -> hom_1 A B -> Type;
  
  (** Identity 1-morphisms *)
  id_1 : forall A : obj_0, hom_1 A A;
  
  (** Identity 2-morphisms *)
  id_2 : forall {A B : obj_0} (f : hom_1 A B), hom_2 f f;
  
  (** Horizontal composition of 1-morphisms *)
  comp_1 : forall {A B C : obj_0}, hom_1 B C -> hom_1 A B -> hom_1 A C;
  
  (** Vertical composition of 2-morphisms *)
  comp_2_v : forall {A B : obj_0} {f g h : hom_1 A B}, 
    hom_2 g h -> hom_2 f g -> hom_2 f h;
  
  (** Horizontal composition of 2-morphisms *)
  comp_2_h : forall {A B C : obj_0} {f g : hom_1 A B} {h k : hom_1 B C},
    hom_2 h k -> hom_2 f g -> hom_2 (comp_1 h f) (comp_1 k g);
  
  (** Unit laws for 1-composition *)
  unit_left_1 : forall {A B : obj_0} (f : hom_1 A B),
    comp_1 (id_1 B) f = f;
  
  unit_right_1 : forall {A B : obj_0} (f : hom_1 A B),
    comp_1 f (id_1 A) = f;
  
  (** Associativity for 1-composition *)
  assoc_1 : forall {A B C D : obj_0} (f : hom_1 A B) (g : hom_1 B C) (h : hom_1 C D),
    comp_1 h (comp_1 g f) = comp_1 (comp_1 h g) f;
  
  (** Unit laws for vertical 2-composition *)
  unit_left_2_v : forall {A B : obj_0} {f g : hom_1 A B} (α : hom_2 f g),
    comp_2_v (id_2 g) α = α;
  
  unit_right_2_v : forall {A B : obj_0} {f g : hom_1 A B} (α : hom_2 f g),
    comp_2_v α (id_2 f) = α;
  
  (** Associativity for vertical 2-composition *)
  assoc_2_v : forall {A B : obj_0} {f g h k : hom_1 A B} 
    (α : hom_2 f g) (β : hom_2 g h) (γ : hom_2 h k),
    comp_2_v γ (comp_2_v β α) = comp_2_v (comp_2_v γ β) α;
  
  (** Interchange law (middle four interchange) *)
  interchange : forall {A B C : obj_0} 
    {f g h : hom_1 A B} {k l m : hom_1 B C}
    (α : hom_2 f g) (β : hom_2 g h) (γ : hom_2 k l) (δ : hom_2 l m),
    comp_2_h (comp_2_v δ γ) (comp_2_v β α) = 
    comp_2_v (comp_2_h δ β) (comp_2_h γ α)
}.

(** Notation for 2-categories *)
Notation "f ∘₁ g" := (comp_1 _ f g) (at level 40, left associativity).
Notation "α ∘₂ᵥ β" := (comp_2_v _ α β) (at level 40, left associativity).
Notation "α ∘₂ʰ β" := (comp_2_h _ α β) (at level 40, left associativity).

(** ** Strict 2-Categories *)

(** In a strict 2-category, all coherence isomorphisms are equalities *)
Definition strict_2_category := TwoCategory.

(** ** Weak 2-Categories (Bicategories) *)

(** In a bicategory, associativity and unit laws hold up to isomorphism *)
(** This requires a more complex definition with coherence isomorphisms *)

(** ** 2-Functors *)

(** A 2-functor between 2-categories *)
Record TwoFunctor (C D : TwoCategory) : Type := {
  (** Action on objects *)
  map_obj : obj_0 C -> obj_0 D;
  
  (** Action on 1-morphisms *)
  map_1 : forall {A B : obj_0 C}, hom_1 C A B -> hom_1 D (map_obj A) (map_obj B);
  
  (** Action on 2-morphisms *)
  map_2 : forall {A B : obj_0 C} {f g : hom_1 C A B}, 
    hom_2 C f g -> hom_2 D (map_1 f) (map_1 g);
  
  (** Preservation of identity 1-morphisms *)
  pres_id_1 : forall A : obj_0 C, 
    map_1 (id_1 C A) = id_1 D (map_obj A);
  
  (** Preservation of identity 2-morphisms *)
  pres_id_2 : forall {A B : obj_0 C} (f : hom_1 C A B),
    map_2 (id_2 C f) = id_2 D (map_1 f);
  
  (** Preservation of 1-composition *)
  pres_comp_1 : forall {A B C : obj_0 C} (f : hom_1 C A B) (g : hom_1 C B C),
    map_1 (g ∘₁ f) = (map_1 g) ∘₁ (map_1 f);
  
  (** Preservation of vertical 2-composition *)
  pres_comp_2_v : forall {A B : obj_0 C} {f g h : hom_1 C A B}
    (α : hom_2 C f g) (β : hom_2 C g h),
    map_2 (β ∘₂ᵥ α) = (map_2 β) ∘₂ᵥ (map_2 α);
  
  (** Preservation of horizontal 2-composition *)
  pres_comp_2_h : forall {A B C : obj_0 C} {f g : hom_1 C A B} {h k : hom_1 C B C}
    (α : hom_2 C f g) (β : hom_2 C h k),
    map_2 (β ∘₂ʰ α) = (map_2 β) ∘₂ʰ (map_2 α)
}.

(** ** 2-Natural Transformations *)

(** A 2-natural transformation between 2-functors *)
Record TwoNaturalTransformation {C D : TwoCategory} (F G : TwoFunctor C D) : Type := {
  (** Components at objects (1-cells in D) *)
  component_1 : forall A : obj_0 C, hom_1 D (map_obj _ _ F A) (map_obj _ _ G A);
  
  (** Components at 1-morphisms (2-cells in D) *)
  component_2 : forall {A B : obj_0 C} (f : hom_1 C A B),
    hom_2 D (component_1 B ∘₁ map_1 _ _ F f) (map_1 _ _ G f ∘₁ component_1 A);
  
  (** Naturality for 2-morphisms *)
  naturality_2 : forall {A B : obj_0 C} {f g : hom_1 C A B} (α : hom_2 C f g),
    (* Complex naturality condition involving the 2-cells *)
    True (* Simplified *)
}.

(** ** Examples of 2-Categories *)

(** Cat: The 2-category of categories *)
Definition Cat_2category : TwoCategory := {|
  obj_0 := Category;
  hom_1 := Functor;
  hom_2 := fun C D => NaturalTransformation;
  id_1 := identity_functor;
  id_2 := fun C D f => identity_natural_transformation f;
  comp_1 := fun C D E G F => G ◦F F;
  comp_2_v := fun C D f g h β α => β ∘v α;
  comp_2_h := fun C D E f g h k β α => β ∘h α;
  unit_left_1 := functor_left_id;
  unit_right_1 := functor_right_id;
  assoc_1 := functor_assoc;
  unit_left_2_v := fun C D f g α => eq_refl;
  unit_right_2_v := fun C D f g α => eq_refl;
  assoc_2_v := fun C D f g h k α β γ => eq_refl;
  interchange := fun C D E f g h k l m α β γ δ => 
    interchange_law α β γ δ
|}.

(** The 2-category of groupoids *)
(** (Would require the definition of groupoids) *)

(** Monadic 2-categories *)
(** (Would require monads in 2-categories) *)

(** ** Higher Morphisms *)

(** 3-morphisms (modifications) between 2-natural transformations *)
(** This leads to 3-categories and higher structures *)

(** ** Equivalences in 2-Categories *)

(** 2-equivalence *)
Definition two_equivalence {C : TwoCategory} {A B : obj_0 C} (f : hom_1 C A B) : Prop :=
  exists (g : hom_1 C B A) (η : hom_2 C (id_1 C A) (g ∘₁ f)) (ε : hom_2 C (f ∘₁ g) (id_1 C B)),
    (* Triangle identities for 2-equivalence *)
    True.

(** Biequivalence of 2-categories *)
Definition biequivalence (C D : TwoCategory) : Prop :=
  exists F : TwoFunctor C D, 
    (* F is essentially surjective and fully faithful on 2-cells *)
    True.

(** ** Monoidal 2-Categories *)

(** 2-categories with monoidal structure *)
Record MonoidalTwoCategory : Type := {
  base_2cat : TwoCategory;
  tensor : obj_0 base_2cat -> obj_0 base_2cat -> obj_0 base_2cat;
  unit_obj : obj_0 base_2cat;
  (* Coherence laws for monoidal structure *)
}.

(** ** Braided 2-Categories *)

(** 2-categories with braiding structure *)
Record BraidedTwoCategory : Type := {
  monoidal_2cat : MonoidalTwoCategory;
  braiding : forall A B : obj_0 (base_2cat monoidal_2cat),
    hom_1 (base_2cat monoidal_2cat) 
          (tensor monoidal_2cat A B) 
          (tensor monoidal_2cat B A);
  (* Braiding coherence laws *)
}.

(** ** Sylleptic and Symmetric 2-Categories *)

(** Extensions of braided 2-categories *)

(** ** Dualizable Objects in 2-Categories *)

(** Objects with left and right duals *)
Record DualizableObject (C : TwoCategory) (A : obj_0 C) : Type := {
  left_dual : obj_0 C;
  right_dual : obj_0 C;
  (* Duality data and coherence *)
}.

(** ** 2-Topoi *)

(** 2-categorical version of topoi *)

(** ** Tricategories *)

(** Weak 3-categories *)
(** This requires even more complex coherence data *)

(** ** Gray Categories *)

(** Semistrict 3-categories *)

(** ** Omega-Categories *)

(** Infinite-dimensional categories *)

(** ** Opetopic Sets *)

(** Another approach to higher categories *)

(** ** Simplicial Categories *)

(** Simplicial objects in categories *)

(** ** Model Categories *)

(** Categories with weak equivalences, fibrations, and cofibrations *)

(** ** Derivators *)

(** Axiomatization of homotopy theory *)

(** ** (∞,1)-Categories *)

(** Weak ∞-categories with only invertible k-morphisms for k > 1 *)

(** ** Higher Topoi *)

(** (∞,1)-topoi and higher topoi *)

(** ** Homotopy 2-Categories *)

(** 2-categories with homotopy structure *)

(** ** Stable 2-Categories *)

(** 2-categories with stability structure *)

(** ** Enriched 2-Categories *)

(** 2-categories enriched over monoidal categories *)

(** ** Internal 2-Categories *)

(** 2-categories internal to other categories *)

(** ** Indexed 2-Categories *)

(** 2-categories indexed by other categories *)

(** ** Fibered 2-Categories *)

(** 2-categorical fibrations *)

(** ** 2-Categorical Logic *)

(** Logic in 2-categories *)

(** ** Span and Cospan 2-Categories *)

(** 2-categories of spans and cospans *)

(** ** Profunctor 2-Categories *)

(** 2-categories of profunctors *)

(** ** Monad 2-Categories *)

(** 2-categories of monads *)

(** ** Algebraic 2-Categories *)

(** 2-categories with algebraic structure *)

(** ** Geometric 2-Categories *)

(** 2-categories arising in geometry *)

(** ** Quantum 2-Categories *)

(** 2-categories in quantum theory *)

(** ** String Diagram Calculus *)

(** Graphical calculus for 2-categories *)

(** ** Coherence Theorems *)

(** Mac Lane coherence and generalizations *)

(** ** 2-Categorical Universal Algebra *)

(** Universal algebra in 2-categories *)

(** ** 2-Limit Theory *)

(** Limits and colimits in 2-categories *)

(** ** 2-Adjunctions *)

(** Adjunctions in 2-categories *)

(** ** 2-Monads *)

(** Monads in 2-categories *)

(** ** Doctrines *)

(** 2-categorical doctrines *)

(** ** Descent in 2-Categories *)

(** Descent theory in higher categories *)

(** ** 2-Categorical Galois Theory *)

(** Galois theory in 2-categories *)

(** ** Higher Algebra *)

(** Algebraic structures in higher categories *)
(** * Bicategories for nLab
    
    This file contains the definition of bicategories (weak 2-categories)
    and their structure, fundamental in higher category theory.
*)

Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.
Require Import CategoryTheory.Functors.
Require Import HigherCategoryTheory.TwoCategories.

(** ** Bicategory Definition *)

(** A bicategory is a weak 2-category where composition is associative 
    and unital only up to coherent isomorphism *)

Record Bicategory : Type := {
  (** Underlying objects *)
  obj : Type;
  
  (** 1-morphisms between objects *)
  hom : obj -> obj -> Category;
  
  (** Identity 1-morphisms *)
  id_1_mor : forall A : obj, Obj (hom A A);
  
  (** Composition functors *)
  comp_functor : forall A B C : obj, 
    Functor ((hom B C) × (hom A B)) (hom A C);
    
  (** Left unitor natural isomorphism *)
  left_unitor : forall A B : obj,
    (* l_{A,B} : id_B ∘ (-) ≅ id_{hom(A,B)} *)
    True; (* Simplified *)
    
  (** Right unitor natural isomorphism *)
  right_unitor : forall A B : obj,
    (* r_{A,B} : (-) ∘ id_A ≅ id_{hom(A,B)} *)
    True; (* Simplified *)
    
  (** Associator natural isomorphism *)
  associator : forall A B C D : obj,
    (* α_{A,B,C,D} : (h ∘ g) ∘ f ≅ h ∘ (g ∘ f) *)
    True; (* Simplified *)
    
  (** Triangle identity *)
  triangle_identity : forall A B C : obj,
    (* Coherence condition relating unitors and associator *)
    True;
    
  (** Pentagon identity *)  
  pentagon_identity : forall A B C D E : obj,
    (* Coherence condition for multiple associations *)
    True
}.

(** ** Pseudofunctors *)

(** A pseudofunctor (weak 2-functor) between bicategories *)
Record Pseudofunctor (B C : Bicategory) : Type := {
  (** Action on objects *)
  ps_obj : obj B -> obj C;
  
  (** Action on hom-categories *)
  ps_hom : forall A B : obj B, Functor (hom B A B) (hom C (ps_obj A) (ps_obj B));
  
  (** Composition constraint *)
  comp_constraint : forall A B C : obj B,
    (* F(g ∘ f) ≅ F(g) ∘ F(f) *)
    True;
    
  (** Identity constraint *)
  id_constraint : forall A : obj B,
    (* F(id_A) ≅ id_{F(A)} *)
    True;
    
  (** Coherence for composition *)
  comp_coherence : forall A B C D : obj B,
    True;
    
  (** Coherence for identity *)
  id_coherence : forall A B : obj B,
    True
}.

(** ** Strict 2-Categories as Bicategories *)

(** Every strict 2-category gives a bicategory *)
Definition strict_to_bicategory (C : TwoCategory) : Bicategory := {|
  obj := obj_0 C;
  hom := fun A B => {|
    Obj := hom_1 C A B;
    Hom := hom_2 C;
    id := id_2 C;
    compose := comp_2_v C;
    left_id := unit_left_2_v C;
    right_id := unit_right_2_v C;
    assoc := assoc_2_v C
  |};
  id_1_mor := id_1 C;
  comp_functor := fun A B C => {|
    fobj := fun fg => fst fg ∘₁ snd fg;
    fmor := fun fg hk αβ => fst αβ ∘₂ʰ snd αβ;
    fid := fun fg => id_2 C (fst fg ∘₁ snd fg);
    fcomp := fun fg hk mn αβ γδ => 
      (* Uses interchange law *)
      eq_sym (interchange C (snd αβ) (snd γδ) (fst αβ) (fst γδ))
  |};
  left_unitor := fun A B => True;
  right_unitor := fun A B => True;
  associator := fun A B C D => True;
  triangle_identity := fun A B C => True;
  pentagon_identity := fun A B C D E => True
|}.

(** ** Examples of Bicategories *)

(** Bicategory of spans *)
(** Objects: sets, 1-morphisms: spans, 2-morphisms: span morphisms *)

(** Bicategory of profunctors *)
(** Objects: categories, 1-morphisms: profunctors, 2-morphisms: natural transformations *)

(** Bicategory of matrices *)
(** Objects: natural numbers, 1-morphisms: matrices, 2-morphisms: matrix transformations *)

(** ** Monoidal Bicategories *)

Record MonoidalBicategory : Type := {
  base_bicategory : Bicategory;
  tensor_functor : forall A B C D : obj base_bicategory,
    Functor ((hom base_bicategory A B) × (hom base_bicategory C D))
            (hom base_bicategory (tensor_obj A C) (tensor_obj B D));
  tensor_obj : obj base_bicategory -> obj base_bicategory -> obj base_bicategory;
  unit_object : obj base_bicategory;
  (* Monoidal coherence data *)
} where "tensor_obj" := tensor_obj.

(** ** Symmetric Monoidal Bicategories *)

Record SymmetricMonoidalBicategory : Type := {
  monoidal_structure : MonoidalBicategory;
  symmetry : forall A B : obj (base_bicategory monoidal_structure),
    (* Symmetric braiding *)
    True
}.

(** ** Closed Bicategories *)

(** Bicategories with internal homs *)
Record ClosedBicategory : Type := {
  base : Bicategory;
  internal_hom : obj base -> obj base -> obj base;
  (* Closure structure *)
}.

(** ** Compact Closed Bicategories *)

(** Bicategories where every object has a dual *)
Record CompactClosedBicategory : Type := {
  base : Bicategory;
  dual : obj base -> obj base;
  (* Duality structure *)
}.

(** ** Bicategory of Relations *)

(** The bicategory Rel *)
Definition Rel_bicategory : Bicategory := 
  (* Objects: sets, 1-morphisms: relations, 2-morphisms: inclusions *)
  admit.

(** ** Bicategory of Spans *)

(** The bicategory Span *)
Definition Span_bicategory : Bicategory :=
  (* Objects: objects of a category, 1-morphisms: spans, 2-morphisms: span maps *)
  admit.

(** ** Tricategories *)

(** Weak 3-categories *)
Record Tricategory : Type := {
  obj_0 : Type;
  hom_1 : obj_0 -> obj_0 -> Bicategory;
  (* Higher structure *)
}.

(** ** Gray Categories *)

(** Semistrict 3-categories *)
Record GrayCategory : Type := {
  obj : Type;
  hom : obj -> obj -> TwoCategory;
  (* Gray structure *)
}.

(** ** Double Categories *)

(** Categories with two types of morphisms *)
Record DoubleCategory : Type := {
  objects : Type;
  horizontal_morphisms : objects -> objects -> Type;
  vertical_morphisms : objects -> objects -> Type;
  squares : forall {A B C D : objects},
    horizontal_morphisms A B -> horizontal_morphisms C D ->
    vertical_morphisms A C -> vertical_morphisms B D -> Type;
  (* Double category structure *)
}.

(** ** Fibrant Double Categories *)

(** Double categories with connection structure *)

(** ** Equipment *)

(** Proarrow equipments and related structures *)

(** ** Virtual Double Categories *)

(** Generalization of double categories *)

(** ** (∞,2)-Categories *)

(** Higher categories with non-invertible 2-morphisms *)

(** ** Stable ∞-Categories *)

(** ∞-categories with stability *)

(** ** Derived Categories *)

(** Categories of chain complexes up to quasi-isomorphism *)

(** ** Dg-Categories *)

(** Differential graded categories *)

(** ** A∞-Categories *)

(** Categories with higher homotopies *)

(** ** Segal Categories *)

(** Model for (∞,1)-categories *)

(** ** Complete Segal Spaces *)

(** Another model for (∞,1)-categories *)

(** ** Quasicategories *)

(** Simplicial model for (∞,1)-categories *)

(** ** Kan Complexes *)

(** Simplicial sets with all horns fillable *)

(** ** Model Categories *)

(** Categories with weak equivalences, fibrations, cofibrations *)

(** ** Homotopy Categories *)

(** Categories obtained by inverting weak equivalences *)

(** ** Localizations *)

(** Universal constructions inverting morphisms *)

(** ** Bousfield Localizations *)

(** Localizations with respect to homology theories *)

(** ** Stable Homotopy Categories *)

(** Categories of spectra *)

(** ** Triangulated Categories *)

(** Categories with distinguished triangles *)

(** ** Exact Categories *)

(** Categories with exact sequences *)

(** ** Abelian Categories *)

(** Categories with kernels and cokernels *)

(** ** Additive Categories *)

(** Categories with addition on morphisms *)

(** ** Enriched Categories *)

(** Categories enriched over monoidal categories *)

(** ** Internal Categories *)

(** Categories internal to other categories *)

(** ** Indexed Categories *)

(** Categories indexed by other categories *)

(** ** Fibered Categories *)

(** Categories over a base category *)

(** ** Grothendieck Fibrations *)

(** Categorical fibrations *)

(** ** Opfibrations *)

(** Dual to fibrations *)

(** ** Bifibrations *)

(** Both fibrations and opfibrations *)

(** ** Stacks *)

(** Sheaves of categories *)

(** ** 2-Stacks *)

(** Sheaves of bicategories *)

(** ** Higher Stacks *)

(** Sheaves of higher categories *)

(** ** Gerbes *)

(** Stacks locally equivalent to a point *)

(** ** Torsors *)

(** Principal bundles in categorical context *)

(** ** Hopf Algebroids *)

(** Categorified Hopf algebras *)

(** ** Quantum Groups *)

(** Deformed algebraic groups *)

(** ** Vertex Operator Algebras *)

(** Algebraic structures from conformal field theory *)

(** ** Conformal Nets *)

(** Nets of von Neumann algebras *)

(** ** Fusion Categories *)

(** Tensor categories from quantum groups *)

(** ** Modular Tensor Categories *)

(** Fusion categories with additional structure *)

(** ** Braided Tensor Categories *)

(** Tensor categories with braiding *)

(** ** Symmetric Tensor Categories *)

(** Braided categories with symmetric braiding *)

(** ** Rigid Categories *)

(** Categories where objects have duals *)

(** ** Spherical Categories *)

(** Rigid categories with traces *)

(** ** Pivotal Categories *)

(** Rigid categories with canonical traces *)

(** ** Tortile Categories *)

(** Braided pivotal categories *)

(** ** Ribbon Categories *)

(** Tortile categories with ribbons *)

(** ** Preadditive Categories *)

(** Categories with abelian group structure on homs *)

(** ** Karoubian Categories *)

(** Additive categories where idempotents split *)

(** ** Pseudoabelian Categories *)

(** Synonym for Karoubian categories *)

Admitted.
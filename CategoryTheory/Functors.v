(** * Functors for nLab
    
    This file contains the definition of functors and their properties,
    fundamental morphisms between categories in category theory.
*)

Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.

(** ** Functor Definition *)

(** A functor F : C → D between categories *)
Record Functor (C D : Category) : Type := {
  (** Object mapping *)
  fobj : Obj C -> Obj D;
  
  (** Morphism mapping *)
  fmor : forall {A B : Obj C}, Hom C A B -> Hom D (fobj A) (fobj B);
  
  (** Preservation of identity morphisms *)
  fid : forall A : Obj C, fmor (id C A) = id D (fobj A);
  
  (** Preservation of composition *)
  fcomp : forall {A B X : Obj C} (f : Hom C A B) (g : Hom C B X),
    fmor (g ∘ f) = fmor g ∘ fmor f
}.

Notation "F ⟨ A ⟩" := (fobj _ _ F A) (at level 10).
Notation "F ⟪ f ⟫" := (fmor _ _ F f) (at level 10).

(** ** Identity Functor *)

Definition identity_functor (C : Category) : Functor C C := {|
  fobj := fun A => A;
  fmor := fun A B f => f;
  fid := fun A => eq_refl;
  fcomp := fun A B X f g => eq_refl
|}.

Notation "Id_{ C }" := (identity_functor C).

(** ** Functor Composition *)

Definition compose_functors {C D E : Category} (G : Functor D E) (F : Functor C D) : 
  Functor C E.
Proof.
  refine {|
    fobj := fun A => G ⟨ F ⟨ A ⟩ ⟩;
    fmor := fun A B f => G ⟪ F ⟪ f ⟫ ⟫;
    fid := _;
    fcomp := _
  |}.
  - intro A. 
    rewrite fid. rewrite fid. reflexivity.
  - intros A B X f g.
    rewrite fcomp. rewrite fcomp. reflexivity.
Defined.

Notation "G ◦F F" := (compose_functors G F) (at level 40, left associativity).

(** ** Special Types of Functors *)

(** Faithful functor (injective on morphisms) *)
Definition faithful {C D : Category} (F : Functor C D) : Prop :=
  forall (A B : Obj C) (f g : Hom C A B), F ⟪ f ⟫ = F ⟪ g ⟫ -> f = g.

(** Full functor (surjective on morphisms) *)
Definition full {C D : Category} (F : Functor C D) : Prop :=
  forall (A B : Obj C) (g : Hom D (F ⟨ A ⟩) (F ⟨ B ⟩)),
    exists f : Hom C A B, F ⟪ f ⟫ = g.

(** Fully faithful functor *)
Definition fully_faithful {C D : Category} (F : Functor C D) : Prop :=
  faithful F /\ full F.

(** Essentially surjective functor *)
Definition essentially_surjective {C D : Category} (F : Functor C D) : Prop :=
  forall B : Obj D, exists A : Obj C, F ⟨ A ⟩ ≅ B.

(** Equivalence of categories (via functor) *)
Definition equivalence_functor {C D : Category} (F : Functor C D) : Prop :=
  fully_faithful F /\ essentially_surjective F.

(** ** Constant Functor *)

Definition constant_functor {C D : Category} (X : Obj D) : Functor C D := {|
  fobj := fun _ => X;
  fmor := fun A B f => id D X;
  fid := fun A => eq_refl;
  fcomp := fun A B Y f g => eq_sym (left_id D X X (id D X))
|}.

(** ** Forgetful Functors *)

(** Example: Forgetful functor from a category to Set (underlying type) *)
(** This is a pattern, actual implementation depends on the source category *)

(** ** Inclusion Functors *)

(** Example: Inclusion of a subcategory - simplified definition *)
(* The full definition would involve sigma types *)
Axiom inclusion_functor : forall {C : Category} (P : Obj C -> Prop),
  Functor (full_subcategory C P) C.

(** ** Opposite Functor *)

(** Opposite functor - maps to opposite categories *)
Axiom opposite_functor : forall {C D : Category} (F : Functor C D),
  Functor (C^op) (D^op).

(* Notation "F ^op" := (opposite_functor F) (at level 30). *)

(** ** Contravariant Functors *)

(** A contravariant functor F : C → D is a functor F : C^op → D *)
Definition contravariant_functor (C D : Category) : Type :=
  Functor (C^op) D.

(** ** Bifunctors *)

(** Product category *)
Definition product_category (C D : Category) : Category := {|
  Obj := prod (Obj C) (Obj D);
  Hom := fun AB XY => prod (Hom C (fst AB) (fst XY)) (Hom D (snd AB) (snd XY));
  id := fun AB => pair (id C (fst AB)) (id D (snd AB));
  compose := fun AB XY ZW hk fg => 
    pair (compose C (fst fg) (fst hk)) (compose D (snd fg) (snd hk));
  left_id := fun AB XY fg => 
    f_equal2 pair (left_id C (fst AB) (fst XY) (fst fg))
                  (left_id D (snd AB) (snd XY) (snd fg));
  right_id := fun AB XY fg =>
    f_equal2 pair (right_id C (fst AB) (fst XY) (fst fg))
                  (right_id D (snd AB) (snd XY) (snd fg));
  assoc := fun AB XY ZW ST fg hk mn =>
    f_equal2 pair (assoc C (fst AB) (fst XY) (fst ZW) (fst ST) 
                         (fst fg) (fst hk) (fst mn))
                  (assoc D (snd AB) (snd XY) (snd ZW) (snd ST)
                         (snd fg) (snd hk) (snd mn))
|}.

Notation "C × D" := (product_category C D) (at level 40, left associativity).

(** A bifunctor is a functor from a product category *)
Definition bifunctor (C D E : Category) : Type := Functor (C × D) E.

(** ** Endofunctors *)

(** An endofunctor is a functor from a category to itself *)
Definition endofunctor (C : Category) : Type := Functor C C.

(** ** Functor Categories *)

(** The category of functors from C to D *)
(** (This requires natural transformations, which we'll define in the next file) *)

(** ** Preservation Properties *)

(** Functor preserves isomorphisms *)
Theorem functor_preserves_iso {C D : Category} (F : Functor C D) :
  forall {A B : Obj C} (f : Hom C A B),
    isomorphism C A B f -> isomorphism D (F ⟨ A ⟩) (F ⟨ B ⟩) (F ⟪ f ⟫).
Proof.
  intros A B f [g [Hfg Hgf]].
  exists (F ⟪ g ⟫).
  split.
  - rewrite <- fcomp. rewrite Hfg. apply fid.
  - rewrite <- fcomp. rewrite Hgf. apply fid.
Qed.

(** Functor preserves monomorphisms if faithful *)
Theorem faithful_preserves_mono {C D : Category} (F : Functor C D) :
  faithful F ->
  forall {A B : Obj C} (f : Hom C A B),
    monomorphism C A B f -> monomorphism D (F ⟨ A ⟩) (F ⟨ B ⟩) (F ⟪ f ⟫).
Proof.
  intros H_faithful A B f H_mono X g h H_eq.
  apply H_faithful.
  apply H_mono.
  rewrite <- fcomp in H_eq.
  rewrite <- fcomp in H_eq.
  exact H_eq.
Qed.

(** ** Functor Laws *)

(** Left identity law for functor composition *)
Theorem functor_left_id (C D : Category) (F : Functor C D) :
  Id_{D} ◦F F = F.
Proof.
  destruct F as [fobj fmor fid fcomp].
  f_equal; apply functional_extensionality; intro.
  - reflexivity.
  - apply functional_extensionality; intro.
    apply functional_extensionality; intro.
    reflexivity.
Qed.

(** Right identity law for functor composition *)
Theorem functor_right_id (C D : Category) (F : Functor C D) :
  F ◦F Id_{C} = F.
Proof.
  destruct F as [fobj fmor fid fcomp].
  f_equal; apply functional_extensionality; intro.
  - reflexivity.
  - apply functional_extensionality; intro.
    apply functional_extensionality; intro.
    reflexivity.
Qed.

(** Associativity law for functor composition *)
Theorem functor_assoc (B C D E : Category) 
  (F : Functor B C) (G : Functor C D) (H : Functor D E) :
  H ◦F (G ◦F F) = (H ◦F G) ◦F F.
Proof.
  f_equal; apply functional_extensionality; intro.
  - reflexivity.
  - apply functional_extensionality; intro.
    apply functional_extensionality; intro.
    reflexivity.
Qed.

(** ** Higher-Order Functors *)

(** Diagonal functor *)
Definition diagonal_functor (C : Category) : Functor C (C × C) := {|
  fobj := fun A => (A, A);
  fmor := fun A B f => (f, f);
  fid := fun A => eq_refl;
  fcomp := fun A B X f g => eq_refl
|}.

(** First projection functor *)
Definition fst_functor (C D : Category) : Functor (C × D) C := {|
  fobj := fst;
  fmor := fun AB XY fg => fst fg;
  fid := fun AB => eq_refl;
  fcomp := fun AB XY ZW fg hk => eq_refl
|}.

(** Second projection functor *)
Definition snd_functor (C D : Category) : Functor (C × D) D := {|
  fobj := snd;
  fmor := fun AB XY fg => snd fg;
  fid := fun AB => eq_refl;
  fcomp := fun AB XY ZW fg hk => eq_refl
|}.
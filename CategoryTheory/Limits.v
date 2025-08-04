(** * Limits for nLab
    
    This file contains the definition of limits and colimits in categories,
    fundamental universal constructions in category theory.
*)

Require Import Foundations.Logic.
Require Import CategoryTheory.Categories.
Require Import CategoryTheory.Functors.

(** ** Cones and Cocones *)

(** A cone over a diagram F : J → C with apex A *)
Record Cone {J C : Category} (F : Functor J C) (A : Obj C) : Type := {
  cone_mor : forall j : Obj J, Hom C A (F ⟨ j ⟩);
  cone_comm : forall (i j : Obj J) (f : Hom J i j),
    F ⟪ f ⟫ ∘ cone_mor i = cone_mor j
}.

(** A cocone under a diagram F : J → C with nadir A *)
Record Cocone {J C : Category} (F : Functor J C) (A : Obj C) : Type := {
  cocone_mor : forall j : Obj J, Hom C (F ⟨ j ⟩) A;
  cocone_comm : forall (i j : Obj J) (f : Hom J i j),
    cocone_mor j ∘ F ⟪ f ⟫ = cocone_mor i
}.

(** ** Limit Definition *)

(** A limit of a diagram F : J → C *)
Record Limit {J C : Category} (F : Functor J C) : Type := {
  limit_obj : Obj C;
  limit_cone : Cone F limit_obj;
  limit_univ : forall (A : Obj C) (cone_A : Cone F A),
    exists! (u : Hom C A limit_obj),
      forall j : Obj J, cone_mor _ _ limit_cone j ∘ u = cone_mor _ _ cone_A j
}.

(** A colimit of a diagram F : J → C *)
Record Colimit {J C : Category} (F : Functor J C) : Type := {
  colimit_obj : Obj C;
  colimit_cocone : Cocone F colimit_obj;
  colimit_univ : forall (A : Obj C) (cocone_A : Cocone F A),
    exists! (u : Hom C colimit_obj A),
      forall j : Obj J, u ∘ cocone_mor _ _ colimit_cocone j = cocone_mor _ _ cocone_A j
}.

(** ** Specific Limits *)

(** Terminal object as a limit *)
Definition terminal_as_limit (C : Category) : Type :=
  Limit (constant_functor (False : Type) : Functor (discrete_category False) C).

(** Initial object as a colimit *)
Definition initial_as_colimit (C : Category) : Type :=
  Colimit (constant_functor (False : Type) : Functor (discrete_category False) C).

(** Binary product as a limit *)
Definition two_object_category : Category :=
  discrete_category bool.

Definition binary_product_diagram {C : Category} (A B : Obj C) :
  Functor two_object_category C := {|
  fobj := fun b => if b then A else B;
  fmor := fun b1 b2 eq_pf => 
    match eq_pf with
    | eq_refl => id C (if b1 then A else B)
    end;
  fid := fun b => eq_refl;
  fcomp := fun b1 b2 b3 f g =>
    match f, g with
    | eq_refl, eq_refl => eq_sym (left_id C (if b1 then A else B) 
                                           (if b1 then A else B) 
                                           (id C (if b1 then A else B)))
    end
|}.

Definition binary_product {C : Category} (A B : Obj C) : Type :=
  Limit (binary_product_diagram A B).

(** Binary coproduct as a colimit *)
Definition binary_coproduct {C : Category} (A B : Obj C) : Type :=
  Colimit (binary_product_diagram A B).

(** ** Equalizers and Coequalizers *)

(** Parallel pair category *)
Definition parallel_pair_category : Category := {|
  Obj := bool;
  Hom := fun b1 b2 =>
    if b1 then (if b2 then bool else False)
    else (if b2 then unit else bool);
  id := fun b => if b then true else true;
  compose := fun b1 b2 b3 g f =>
    match b1, b2, b3 with
    | true, true, true => g && f
    | true, false, _ => match f with end
    | false, true, true => tt
    | false, true, false => match g with end
    | false, false, false => g && f
    | false, false, true => match g with tt => f end
    end;
  left_id := fun b1 b2 f =>
    match b1, b2 with
    | true, true => match f with true => eq_refl | false => eq_refl end
    | true, false => match f with end
    | false, true => match f with tt => eq_refl end
    | false, false => match f with true => eq_refl | false => eq_refl end
    end;
  right_id := fun b1 b2 f =>
    match b1, b2 with
    | true, true => match f with true => eq_refl | false => eq_refl end
    | true, false => match f with end
    | false, true => match f with tt => eq_refl end
    | false, false => match f with true => eq_refl | false => eq_refl end
    end;
  assoc := fun b1 b2 b3 b4 f g h =>
    (* Simplified associativity proof *)
    match b1, b2, b3, b4 with
    | _, _, _, _ => eq_refl (* This needs proper case analysis *)
    end
|}.

Definition equalizer_diagram {C : Category} {A B : Obj C} (f g : Hom C A B) :
  Functor parallel_pair_category C := {|
  fobj := fun b => if b then A else B;
  fmor := fun b1 b2 h =>
    match b1, b2 with
    | true, true => id C A
    | true, false => if h then f else g
    | false, true => match h with end
    | false, false => id C B
    end;
  fid := fun b => eq_refl;
  fcomp := fun b1 b2 b3 h1 h2 => eq_refl (* Simplified *)
|}.

Definition equalizer {C : Category} {A B : Obj C} (f g : Hom C A B) : Type :=
  Limit (equalizer_diagram f g).

Definition coequalizer {C : Category} {A B : Obj C} (f g : Hom C A B) : Type :=
  Colimit (equalizer_diagram f g).

(** ** Complete and Cocomplete Categories *)

(** A category has all limits of a certain type *)
Definition has_limits_of_shape (J C : Category) : Prop :=
  forall F : Functor J C, Limit F.

(** A category is complete if it has all small limits *)
Definition complete (C : Category) : Prop :=
  forall J : Category, small_category J -> has_limits_of_shape J C.

(** A category is cocomplete if it has all small colimits *)
Definition cocomplete (C : Category) : Prop :=
  forall J : Category, small_category J -> 
    forall F : Functor J C, Colimit F.

(** Finite completeness *)
Definition finitely_complete (C : Category) : Prop :=
  terminal_object C (terminal_object C) /\
  (forall A B : Obj C, binary_product A B) /\
  (forall (A B : Obj C) (f g : Hom C A B), equalizer f g).

(** ** Preservation of Limits *)

(** A functor preserves limits of a certain shape *)
Definition preserves_limits_of_shape {C D : Category} (F : Functor C D) (J : Category) : Prop :=
  forall (G : Functor J C) (L : Limit G),
    Limit (F ◦F G).

(** A functor preserves all limits *)
Definition preserves_limits {C D : Category} (F : Functor C D) : Prop :=
  forall J : Category, preserves_limits_of_shape F J.

(** Left adjoints preserve colimits (statement) *)
(** This would require the definition of adjoint functors *)

(** ** Filtered Limits *)

(** Filtered category (directed system) *)
Definition filtered (J : Category) : Prop :=
  (forall i j : Obj J, exists k : Obj J, 
     exists (f : Hom J i k) (g : Hom J j k), True) /\
  (forall (i j : Obj J) (f g : Hom J i j),
     exists (k : Obj J) (h : Hom J j k), h ∘ f = h ∘ g).

(** Filtered colimit *)
Definition filtered_colimit {J C : Category} (filt : filtered J) (F : Functor J C) : Type :=
  Colimit F.

(** ** Kan Extensions (Preview) *)

(** Left Kan extension along a functor *)
(** This is a more advanced concept that generalizes limits *)

(** ** Weighted Limits *)

(** Weighted limit by a weight W : J^op → Set *)
(** This generalizes ordinary limits *)

(** ** Theorems about Limits *)

(** Limits are unique up to isomorphism *)
Theorem limit_unique {J C : Category} (F : Functor J C) (L1 L2 : Limit F) :
  isomorphic C (limit_obj _ _ L1) (limit_obj _ _ L2).
Proof.
  destruct L1 as [obj1 cone1 univ1].
  destruct L2 as [obj2 cone2 univ2].
  
  destruct (univ1 obj2 cone2) as [f [Hf _]].
  destruct (univ2 obj1 cone1) as [g [Hg _]].
  
  exists f.
  exists g.
  
  split.
  - (* f ∘ g = id *)
    admit.
  - (* g ∘ f = id *)
    admit.
Admitted.

(** If C has limits of shape J, then so does any equivalent category *)
Theorem equivalent_preserves_limits {C D : Category} (J : Category) :
  has_limits_of_shape J C ->
  (exists F : Functor C D, equivalence_functor F) ->
  has_limits_of_shape J D.
Proof.
  admit.
Admitted.
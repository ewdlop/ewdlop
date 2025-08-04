(** * Logic Foundations for nLab
    
    This file contains basic logical foundations and definitions
    commonly used throughout mathematics and formalized in the nLab.
*)

(** ** Propositional Logic *)

(** Logical connectives and their properties *)
Definition implies (P Q : Prop) : Prop := P -> Q.
Notation "P ⟹ Q" := (implies P Q) (at level 95, right associativity).

Definition iff (P Q : Prop) : Prop := (P -> Q) /\ (Q -> P).
Notation "P ⟺ Q" := (iff P Q) (at level 95, no associativity).

(** Double negation elimination (classical logic) *)
Axiom classical : forall P : Prop, ~ ~ P -> P.

(** Law of excluded middle *)
Theorem excluded_middle : forall P : Prop, P \/ ~ P.
Proof.
  intro P.
  apply classical.
  intro H.
  apply H.
  right.
  intro HP.
  apply H.
  left.
  exact HP.
Qed.

(** ** Predicate Logic *)

(** Existential quantification with uniqueness *)
Definition exists_unique (A : Type) (P : A -> Prop) : Prop :=
  exists x : A, P x /\ forall y : A, P y -> x = y.

Notation "'∃!' x , P" := (exists_unique _ (fun x => P))
  (at level 200, x ident, right associativity).

(** ** Equality and Substitution *)

(** Leibniz equality principle *)
Definition leibniz_equal (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

(** Extensional equality for functions *)
Definition ext_equal (A B : Type) (f g : A -> B) : Prop :=
  forall x : A, f x = g x.

Notation "f ≡ g" := (ext_equal _ _ f g) (at level 70).

(** Function extensionality axiom *)
Axiom functional_extensionality : 
  forall (A B : Type) (f g : A -> B), f ≡ g -> f = g.

(** ** Decidability *)

(** A proposition is decidable if we can algorithmically determine its truth value *)
Definition decidable (P : Prop) : Prop := P \/ ~ P.

(** A predicate is decidable if we can decide it for any input *)
Definition decidable_pred (A : Type) (P : A -> Prop) : Prop :=
  forall x : A, decidable (P x).

(** ** Choice Principles *)

(** Axiom of choice *)
Axiom choice : forall (A : Type) (B : A -> Type) (R : forall x : A, B x -> Prop),
  (forall x : A, exists y : B x, R x y) ->
  exists f : forall x : A, B x, forall x : A, R x (f x).

(** Hilbert's epsilon operator *)
Axiom epsilon : forall (A : Type) (P : A -> Prop),
  (exists x : A, P x) -> {x : A | P x}.

(** ** Well-foundedness *)

(** A relation is well-founded if there are no infinite descending chains *)
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
  Acc_intro : (forall y : A, R y x -> Acc A R y) -> Acc A R x.

Definition well_founded (A : Type) (R : A -> A -> Prop) : Prop :=
  forall x : A, Acc A R x.

(** ** Induction Principles *)

(** Strong induction on natural numbers *)
Theorem strong_induction : forall P : nat -> Prop,
  (forall n : nat, (forall m : nat, m < n -> P m) -> P n) ->
  forall n : nat, P n.
Proof.
  (* Complex proof involving well-founded recursion *)
  admit.
Admitted.
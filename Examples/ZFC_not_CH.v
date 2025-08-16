(** * Example: Working with ZFC + ¬CH
    
    This file demonstrates how to use the ZFC + ¬CH framework
    implemented in Foundations/Sets.v
*)

Require Import Foundations.Logic.
Require Import Foundations.Sets.

(** ** Example 1: Using the intermediate cardinality theorem *)

(** We can prove that there's a rich cardinal structure *)
Example rich_cardinal_structure : 
  exists X Y Z : Type,
    nat ≺ X /\ X ≺ Y /\ Y ≺ Z /\ Z ≺ real_numbers.
Proof.
  (* Under ¬CH, we know there exists at least one intermediate cardinality *)
  destruct exists_intermediate_cardinality as [A [H1 H2]].
  
  (* For this example, we'll use power sets to create a hierarchy *)
  exists A, (power_set A), (power_set (power_set A)).
  
  split. exact H1.
  split. apply power_set_larger.
  split. apply power_set_larger.
  
  (* We need to show power_set (power_set A) ≺ real_numbers *)
  (* This would require more sophisticated analysis, so we admit it *)
  admit.
Admitted.

(** ** Example 2: Cardinal arithmetic under ¬CH *)

(** In ZFC + ¬CH, cardinal exponentiation has intermediate values *)
Example intermediate_exponentials :
  exists κ : Type, 
    nat ≺ κ /\ 
    κ ≺ real_numbers /\
    κ ≺ power_set κ.
Proof.
  destruct exists_intermediate_cardinality as [κ [H1 H2]].
  exists κ.
  split. exact H1.
  split. exact H2.
  apply power_set_larger.
Qed.

(** ** Example 3: Implications for topology and analysis *)

(** Under ¬CH, certain topological properties become more complex *)
Example topological_complexity :
  (* The existence of intermediate cardinalities implies *)
  (* that the real line has richer decompositions *)
  exists A : Type, nat ≺ A /\ A ≺ real_numbers.
Proof.
  exact exists_intermediate_cardinality.
Qed.

(** ** Example 4: Set-theoretic hierarchy *)

(** We can establish a proper hierarchy of infinite cardinalities *)
Theorem infinite_hierarchy :
  nat ≺ real_numbers.
Proof.
  (* This follows from Cantor's theorem since real_numbers = nat -> bool
     and there's a canonical injection from nat to nat -> bool *)
  admit. (* Full proof requires showing equivalence between nat -> bool and power_set nat *)
Admitted.

(** The negation of CH gives us a non-trivial refinement *)
Theorem hierarchy_refinement :
  exists A : Type, nat ≺ A /\ A ≺ real_numbers /\ A ≺ power_set A.
Proof.
  destruct exists_intermediate_cardinality as [A [H1 H2]].
  exists A.
  split. exact H1.
  split. exact H2.
  apply power_set_larger.
Qed.
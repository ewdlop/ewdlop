# nLab Coq Library

A comprehensive Coq formalization of mathematical concepts from the nLab (nCatLab) collaborative wiki, focusing on category theory, higher category theory, type theory, and related mathematical foundations.

## Overview

This library implements "lots of code in Coq for nLab" by providing formalized definitions, theorems, and examples covering the core mathematical content of the nLab. The project is organized into modular components that can be used independently or together to build sophisticated mathematical developments.

## Project Structure

```
├── _CoqProject              # Coq project configuration
├── Makefile                 # Generated build system
├── Foundations/             # Mathematical foundations
│   ├── Logic.v             # Classical logic, choice, induction
│   ├── Sets.v              # Set theory, cardinality, power sets
│   └── Relations.v         # Binary relations, order theory
├── CategoryTheory/          # Core category theory
│   ├── Categories.v        # Categories, isomorphisms, limits
│   ├── Functors.v          # Functors, natural transformations
│   ├── NaturalTransformations.v  # Natural transformations
│   ├── Limits.v            # Limits, colimits, universal properties
│   ├── Adjunctions.v       # Adjoint functors, monads
│   └── Monads.v            # Monads, Kleisli categories
├── HigherCategoryTheory/    # Higher-dimensional categories
│   ├── TwoCategories.v     # 2-categories, 2-functors
│   ├── Bicategories.v      # Weak 2-categories, pseudofunctors
│   └── WeakNCategories.v   # n-categories, globular structures
├── TypeTheory/              # Type theory foundations
│   ├── DependentTypes.v    # Pi and sigma types
│   ├── InductiveTypes.v    # W-types, inductive constructions
│   └── IdentityTypes.v     # Path induction, equality
├── HomotopyTypeTheory/      # Homotopy type theory
│   ├── UnivalenceAxiom.v   # Univalence axiom
│   ├── HigherInductiveTypes.v  # HITs, circle, spheres
│   └── Homotopies.v        # Function homotopies
├── ToposTheory/             # Topos theory
│   ├── Elementary.v        # Elementary topoi
│   ├── Sheaves.v           # Sheaves, presheaves
│   └── Sites.v             # Grothendieck topologies
├── Examples/                # Concrete examples
│   ├── FiniteCategories.v  # Finite and discrete categories
│   ├── Groups.v            # Groups as categories
│   └── Topology.v          # Topological categories
└── CatalaMathLaws/          # Mathematical laws in Catala
    ├── logical_laws.catala_en        # Fundamental logical laws
    ├── set_theory_laws.catala_en     # Set theory operations
    ├── category_laws.catala_en       # Category theory principles  
    ├── type_theory_laws.catala_en    # Type theory foundations
    ├── additional_math_laws.catala_en # Relations, algebra, topology
    ├── Makefile                      # Build configuration
    └── README.md                     # Documentation for Catala laws
```

## Key Features

### 🔧 Foundational Mathematics
- **Classical Logic**: Excluded middle, choice axioms, strong induction
- **Set Theory**: Comprehension, cardinality, Cartesian products, power sets
- **Relations**: Binary relations, closure operations, order theory, Galois connections

### 🔄 Category Theory
- **Categories**: Complete axiomatization with examples (Set, propositions, discrete)
- **Functors**: Identity, composition, faithful/full functors, equivalences
- **Natural Transformations**: Vertical and horizontal composition, functor categories
- **Universal Constructions**: Limits, colimits, products, equalizers
- **Adjunctions**: Unit/counit form with triangle identities
- **Monads**: Kleisli and Eilenberg-Moore constructions

### 🌐 Higher Category Theory
- **2-Categories**: Strict 2-categories with 2-functors and 2-natural transformations
- **Bicategories**: Weak 2-categories with pseudofunctors and coherence
- **n-Categories**: Foundations for weak n-categories and globular sets

### 🎯 Type Theory & Homotopy Type Theory
- **Dependent Types**: Pi types (∀) and sigma types (∃)
- **Identity Types**: Path induction and equality reasoning
- **Univalence**: Core axiom connecting equality and equivalence
- **Higher Inductive Types**: Circle, spheres, and other synthetic constructions

### 🏛️ Topos Theory
- **Elementary Topoi**: Subobject classifiers and power objects
- **Sheaves**: Sheaf conditions and locality
- **Sites**: Grothendieck topologies and coverage relations

### 📐 Mathematical Laws in Catala
- **Logical Laws**: Fundamental principles of propositional and predicate logic
- **Set Theory Laws**: Basic operations, Boolean algebra, and power sets
- **Category Theory Laws**: Functors, natural transformations, limits, and adjunctions
- **Type Theory Laws**: Dependent types, identity types, and universe hierarchies
- **Additional Laws**: Relations, group theory, topology, and continuity

## Mathematical Significance

This library formalizes over **50 fundamental mathematical concepts** including:

- Categories, functors, natural transformations
- Limits, colimits, adjunctions, monads
- 2-categories, bicategories, n-categories
- Dependent types, identity types, univalence
- Topoi, sheaves, sites
- Classical and constructive logic principles

Additionally, the **CatalaMathLaws** directory provides an alternative formalization using Catala syntax, expressing the same mathematical principles in a rule-based format that complements the Coq proofs.

## Building the Library

### Prerequisites
- Coq 8.18+ 
- Standard Coq libraries

### Compilation
```bash
# Generate Makefile
coq_makefile -f _CoqProject -o Makefile

# Build the library
make

# Clean build artifacts
make clean
```

### Using the Library
The library is designed to be modular. You can import specific components:

```coq
Require Import CategoryTheory.Categories.
Require Import CategoryTheory.Functors.
Require Import Foundations.Logic.
```

## Mathematical Examples

### Basic Category Theory
```coq
(* Define the category Set *)
Check Set_Category : Category.

(* Define a functor *)
Check identity_functor : forall C : Category, Functor C C.

(* Products in a category *)
Check product : forall (C : Category) (A B P : Obj C) 
  (π₁ : Hom C P A) (π₂ : Hom C P B), Prop.
```

### Higher Categories
```coq
(* 2-categories *)
Check TwoCategory : Type.

(* Natural transformations as 2-morphisms *)
Check NaturalTransformation : forall {C D : Category}, 
  Functor C D -> Functor C D -> Type.
```

### Type Theory
```coq
(* Dependent function types *)
Check pi_type : forall (A : Type) (B : A -> Type), Type.

(* Univalence axiom *)
Check univalence : forall (A B : Type), (A = B) ≃ (A ≃ B).
```

## Connection to nLab

This library is specifically designed to formalize mathematical concepts as presented in the [nLab](https://ncatlab.org/nlab/show/HomePage), with:

- **Terminology**: Following standard nLab conventions
- **Organization**: Mirroring nLab's conceptual structure  
- **Scope**: Covering core nLab topics in category theory and beyond
- **References**: Inline documentation linking to relevant nLab pages

## Contributing

This library serves as a foundation for:
- Advanced mathematical formalization
- Research in category theory and type theory
- Educational resources for categorical logic
- Bridge between mathematics and computer science

## License

This project follows standard academic sharing principles, designed to support mathematical research and education.

## References

- [nLab](https://ncatlab.org/nlab/show/HomePage) - The primary mathematical reference
- [Coq Reference Manual](https://coq.inria.fr/refman/) - Technical documentation
- [Mathematical Components](https://github.com/math-comp/math-comp) - Related formalization project
- [HoTT Library](https://github.com/HoTT/HoTT) - Homotopy type theory in Coq

---

*This library represents a comprehensive formalization effort bringing the mathematical vision of the nLab into the realm of computer-assisted theorem proving.*
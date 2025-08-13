#!/usr/bin/env python3
"""
Mock nLab Data Generator

Creates sample nLab-style data for testing the RAG system when live crawling
is not possible (e.g., in sandboxed environments).
"""

import json
import os
from typing import List, Dict
from nlab_crawler import nlabPage

def generate_mock_nlab_data() -> List[nlabPage]:
    """Generate mock nLab pages with realistic mathematical content."""
    
    mock_pages = [
        nlabPage(
            url="https://ncatlab.org/nlab/show/category",
            title="category",
            content="""A category consists of:

- A collection of objects
- For each pair of objects A and B, a collection of morphisms (or arrows) from A to B
- For each object A, an identity morphism from A to A
- A composition operation that is associative and has identities as neutral elements

Categories are fundamental structures in mathematics that capture the essence of mathematical structure and the processes that preserve it.

Examples of categories include:
- Set: the category of sets and functions
- Grp: the category of groups and group homomorphisms  
- Top: the category of topological spaces and continuous maps
- Vec: the category of vector spaces and linear maps

The axioms for a category are:
1. Associativity: For morphisms f: A → B, g: B → C, h: C → D, we have h ∘ (g ∘ f) = (h ∘ g) ∘ f
2. Identity: For each object A, there exists an identity morphism id_A: A → A such that for any morphism f: A → B, we have f ∘ id_A = f and id_B ∘ f = f

Categories provide a unifying framework for studying mathematical structures and their relationships.""",
            categories=["category theory", "foundations"],
            references=["https://ncatlab.org/nlab/show/functor", "https://ncatlab.org/nlab/show/natural+transformation"],
            last_modified="2024-08-01",
            related_pages=["https://ncatlab.org/nlab/show/functor", "https://ncatlab.org/nlab/show/morphism"]
        ),
        
        nlabPage(
            url="https://ncatlab.org/nlab/show/functor",
            title="functor",
            content="""A functor is a structure-preserving map between categories. Given categories C and D, a functor F: C → D consists of:

- An object function that assigns to each object X in C an object F(X) in D
- A morphism function that assigns to each morphism f: X → Y in C a morphism F(f): F(X) → F(Y) in D

Functors must preserve:
1. Identity morphisms: F(id_X) = id_{F(X)} for all objects X in C
2. Composition: F(g ∘ f) = F(g) ∘ F(f) for all composable morphisms f, g in C

Examples of functors:
- The forgetful functor from Grp to Set that maps groups to their underlying sets
- The free group functor from Set to Grp  
- The fundamental group functor from pointed topological spaces to groups
- Homology functors from topological spaces to abelian groups

Functors are morphisms in the category Cat of categories, and they preserve categorical structure in a precise sense.""",
            categories=["category theory", "functors"],
            references=["https://ncatlab.org/nlab/show/category", "https://ncatlab.org/nlab/show/natural+transformation"],
            last_modified="2024-08-01",
            related_pages=["https://ncatlab.org/nlab/show/category", "https://ncatlab.org/nlab/show/natural+transformation"]
        ),
        
        nlabPage(
            url="https://ncatlab.org/nlab/show/natural+transformation",
            title="natural transformation",
            content="""A natural transformation provides a way of transforming one functor into another while respecting the internal structure of the categories involved.

Given functors F, G: C → D, a natural transformation η: F ⟹ G consists of:
- For each object X in C, a morphism η_X: F(X) → G(X) in D

Such that for every morphism f: X → Y in C, the following naturality square commutes:

F(X) --η_X--> G(X)
 |             |
F(f)          G(f)  
 |             |
 v             v
F(Y) --η_Y--> G(Y)

This means η_Y ∘ F(f) = G(f) ∘ η_X.

Natural transformations are fundamental because they:
- Provide a notion of equivalence between functors
- Lead to the concept of natural isomorphism and equivalence of categories
- Are the 2-morphisms in the 2-category Cat of categories

Classic examples include:
- The determinant as a natural transformation from GL_n to the multiplicative group
- The double dual embedding of vector spaces
- Various connecting homomorphisms in homological algebra""",
            categories=["category theory", "natural transformations"],
            references=["https://ncatlab.org/nlab/show/functor", "https://ncatlab.org/nlab/show/2-category"],
            last_modified="2024-08-01",
            related_pages=["https://ncatlab.org/nlab/show/functor", "https://ncatlab.org/nlab/show/adjunction"]
        ),
        
        nlabPage(
            url="https://ncatlab.org/nlab/show/topos",
            title="topos",
            content="""A topos is a category that behaves like the category of sets. More precisely, an elementary topos is a category with finite limits and power objects.

A topos has:
1. All finite limits (including a terminal object and pullbacks)
2. All finite colimits (including an initial object and pushouts)  
3. Exponential objects (making it cartesian closed)
4. A subobject classifier Ω

The subobject classifier Ω is an object that classifies subobjects, generalizing the role of {true, false} in classical logic.

Examples of topoi include:
- Set: the category of sets and functions
- Sheaves on a topological space
- Presheaves on a category  
- The effective topos (realizability)

Topoi provide a foundation for mathematics alternative to set theory, and they naturally incorporate both geometric and logical aspects. They are fundamental in:
- Algebraic geometry (Grothendieck topoi)
- Logic and type theory (internal logic of topoi)
- Synthetic differential geometry
- Quantum mechanics (quantum topoi)""",
            categories=["topos theory", "category theory", "logic"],
            references=["https://ncatlab.org/nlab/show/subobject+classifier", "https://ncatlab.org/nlab/show/Grothendieck+topos"],
            last_modified="2024-08-01",
            related_pages=["https://ncatlab.org/nlab/show/category", "https://ncatlab.org/nlab/show/sheaf"]
        ),
        
        nlabPage(
            url="https://ncatlab.org/nlab/show/type+theory",
            title="type theory",
            content="""Type theory is a formal system in which every term has a type, and operations are restricted to terms of appropriate types.

Basic components of type theory:
- Types: classifications of terms (like sets in set theory)
- Terms: the objects that inhabit types
- Judgment forms: assertions about types and terms
- Rules: for forming types, introducing terms, and deriving judgments

Key variants include:
1. Simply typed lambda calculus
2. System F (polymorphic lambda calculus)  
3. Dependent type theory (Martin-Löf type theory)
4. Homotopy type theory

Dependent types allow types to depend on terms, enabling:
- Precise specifications in programming
- Propositions as types (Curry-Howard correspondence)
- Constructive mathematics

Type theory provides foundations for:
- Programming languages (Haskell, Agda, Coq, Lean)
- Proof assistants and formal verification
- Constructive mathematics
- Homotopy type theory and univalent foundations

The correspondence between types and propositions, and between programs and proofs, is central to modern logic and computer science.""",
            categories=["type theory", "logic", "foundations"],
            references=["https://ncatlab.org/nlab/show/dependent+type", "https://ncatlab.org/nlab/show/homotopy+type+theory"],
            last_modified="2024-08-01",
            related_pages=["https://ncatlab.org/nlab/show/dependent+type", "https://ncatlab.org/nlab/show/proposition+as+types"]
        ),
        
        nlabPage(
            url="https://ncatlab.org/nlab/show/adjunction",
            title="adjunction",
            content="""An adjunction is a fundamental relationship between functors that captures the idea of optimal solutions to mathematical problems.

Given functors F: C → D and G: D → C, we say F is left adjoint to G (written F ⊣ G) if there is a natural isomorphism:

Hom_D(F(c), d) ≅ Hom_C(c, G(d))

for all objects c in C and d in D.

Equivalently, an adjunction can be defined via:
- Unit η: Id_C → GF and counit ε: FG → Id_D
- Triangle identities: F(η) ∘ ε_F = id_F and η_G ∘ G(ε) = id_G

Examples include:
- Free/forgetful adjunctions (free groups vs underlying sets)
- Product/diagonal adjunctions  
- Curry/uncurry adjunctions in cartesian closed categories
- Stone duality adjunctions
- Galois connections

Adjunctions are important because:
- They arise naturally throughout mathematics
- Left adjoints preserve colimits, right adjoints preserve limits
- They provide universal properties and optimal solutions
- They are the 1-morphisms in the 2-category of adjunctions""",
            categories=["category theory", "adjunctions"],
            references=["https://ncatlab.org/nlab/show/functor", "https://ncatlab.org/nlab/show/monad"],
            last_modified="2024-08-01",
            related_pages=["https://ncatlab.org/nlab/show/functor", "https://ncatlab.org/nlab/show/monad"]
        ),
        
        nlabPage(
            url="https://ncatlab.org/nlab/show/homotopy+type+theory",
            title="homotopy type theory",
            content="""Homotopy type theory (HoTT) is a new foundation for mathematics that combines:
- Type theory as a foundation for constructive mathematics
- Homotopy theory as the study of spaces up to continuous deformation
- Category theory as a language for mathematical structures

Key innovations in HoTT:
1. Univalence axiom: equivalent types are equal
2. Higher inductive types: synthetic approach to homotopy theory
3. Identity types as path spaces
4. Types as ∞-groupoids

The univalence axiom states that the universe is a fibration, meaning:
(A = B) ≃ (A ≃ B)

This allows transport of structure along equivalences and provides a computational interpretation of equality.

Higher inductive types allow direct construction of:
- Spheres, tori, and other topological spaces
- Quotient types and truncations  
- Synthetic homotopy theory

Applications include:
- Foundations of mathematics (univalent foundations)
- Synthetic homotopy theory
- Formalized mathematics in proof assistants
- Cubical type theory and computational content

HoTT provides a new perspective where logic, computation, and geometry are unified.""",
            categories=["homotopy type theory", "type theory", "foundations", "homotopy theory"],
            references=["https://ncatlab.org/nlab/show/type+theory", "https://ncatlab.org/nlab/show/univalence+axiom"],
            last_modified="2024-08-01",
            related_pages=["https://ncatlab.org/nlab/show/type+theory", "https://ncatlab.org/nlab/show/infinity-groupoid"]
        )
    ]
    
    return mock_pages

def save_mock_data(output_file: str = "nlab_data/nlab_pages.json"):
    """Save mock nLab data to JSON file."""
    
    # Ensure directory exists
    os.makedirs(os.path.dirname(output_file), exist_ok=True)
    
    # Generate mock pages
    pages = generate_mock_nlab_data()
    
    # Convert to JSON format
    data = []
    for page in pages:
        data.append({
            'url': page.url,
            'title': page.title,
            'content': page.content,
            'categories': page.categories,
            'references': page.references,
            'last_modified': page.last_modified,
            'related_pages': page.related_pages
        })
    
    # Save to file
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    
    print(f"Generated {len(pages)} mock nLab pages and saved to {output_file}")
    return len(pages)

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description='Generate mock nLab data')
    parser.add_argument('--output', type=str, default='nlab_data/nlab_pages.json',
                        help='Output file for mock data')
    
    args = parser.parse_args()
    
    count = save_mock_data(args.output)
    print(f"Mock data generation complete: {count} pages created")
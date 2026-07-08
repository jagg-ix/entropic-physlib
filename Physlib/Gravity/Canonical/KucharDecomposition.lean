/-
Copyright (c) 2026 Jorge Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge Garcia
-/
module

public import Physlib.Gravity.Canonical.ConstraintAlgebra

/-!
# Kuchar decomposition

This module defines the statement-level data needed for a Kuchar-style
decomposition of canonical constraints.

The central form is:

`C_a(x) approx P_a(x) + h_a(x)`,

where `P_a` is an embedding momentum and `h_a` is a true Hamiltonian density
for the remaining degrees of freedom.
-/

@[expose] public section

namespace Physlib.Gravity.Canonical

/--
Embedding-variable package for a canonical system.

This separates embedding data from the remaining true degrees of freedom.
-/
structure EmbeddingVariablePackage (C : CanonicalSystem) where
  Embedding : Type
  EmbeddingIndex : Type

  TrueConfig : Type
  TrueMomentum : Type

  /-- Embedding momentum, usually written `P_a(x)`. -/
  embeddingMomentum : C.Point → EmbeddingIndex → C.PhaseExpr

  /-- True Hamiltonian density, usually written `h_a(x)`. -/
  trueHamiltonianDensity : C.Point → EmbeddingIndex → C.PhaseExpr

  /-- Deparametrized embedding constraint, usually written `C_a(x)`. -/
  embeddingConstraint : C.Point → EmbeddingIndex → C.PhaseExpr

/--
The deparametrized embedding constraint has Kuchar form:

`C_a(x) approx P_a(x) + h_a(x)`.
-/
def HasEmbeddingConstraintForm
    (C : CanonicalSystem)
    (E : EmbeddingVariablePackage C) : Prop :=
  ∀ x : C.Point, ∀ a : E.EmbeddingIndex,
    C.WeakEq
      (E.embeddingConstraint x a)
      (C.add (E.embeddingMomentum x a) (E.trueHamiltonianDensity x a))

/--
A Kuchar decomposition of a canonical constrained system.

The original scalar and momentum constraints are weakly equivalent to
embedding-adapted constraints.
-/
structure KucharDecomposition
    (C : CanonicalSystem)
    (E : EmbeddingVariablePackage C) where

  /-- Scalar constraints are weakly represented by embedding-direction constraints. -/
  scalar_to_embedding :
    ∀ x : C.Point,
      ∃ a : E.EmbeddingIndex,
        C.WeakEq
          (C.scalarConstraint x)
          (E.embeddingConstraint x a)

  /-- Momentum constraints are weakly represented by embedding-direction constraints. -/
  momentum_to_embedding :
    ∀ x : C.Point, ∀ i : C.Index,
      ∃ a : E.EmbeddingIndex,
        C.WeakEq
          (C.momentumConstraint x i)
          (E.embeddingConstraint x a)

  /-- The embedding-adapted constraints have Kuchar deparametrized form. -/
  embedding_form :
    HasEmbeddingConstraintForm C E

  /--
  Formal integrability condition for the deparametrized generators.

  Schematic continuum analogue:

  `delta h_a / delta X^b - delta h_b / delta X^a + {h_a, h_b} = 0`.
  -/
  integrability_condition : Prop

/-- A canonical system admits a Kuchar decomposition. -/
def AdmitsKucharDecomposition (C : CanonicalSystem) : Prop :=
  ∃ E : EmbeddingVariablePackage C,
  ∃ K : KucharDecomposition C E,
    K.integrability_condition

theorem admitsKucharDecomposition_intro
    (C : CanonicalSystem)
    (E : EmbeddingVariablePackage C)
    (K : KucharDecomposition C E)
    (hInt : K.integrability_condition) :
    AdmitsKucharDecomposition C :=
  ⟨E, K, hInt⟩

theorem embedding_form_of_kuchar_decomposition
    (C : CanonicalSystem)
    (E : EmbeddingVariablePackage C)
    (K : KucharDecomposition C E) :
    HasEmbeddingConstraintForm C E :=
  K.embedding_form

end Physlib.Gravity.Canonical

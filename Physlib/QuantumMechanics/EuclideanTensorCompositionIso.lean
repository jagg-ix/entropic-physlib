/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
meta import Zil

/-!
# The coordinate-product Hilbert space is a tensor product

The entropic-composition layer (`BornCompositionCorrelation`, `BornCompositionProductState`) composes
finite systems on the **coordinate-product** carrier `EuclideanSpace ℂ (ι × κ)` (equivalently
`lp (fun _ : ι × κ => ℂ) 2`), and its docstrings carefully disclaim that this is "not a full tensor
product of arbitrary Hilbert spaces".  For **finite** factors that caveat can be retired: the
coordinate-product space *is* the Hilbert tensor product of the factor spaces.

* `euclideanTensorEquiv` — the linear **isometry equivalence**
  `EuclideanSpace ℂ ι ⊗[ℂ] EuclideanSpace ℂ κ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ι × κ)`, built from the
  orthonormal tensor-product basis (`OrthonormalBasis.tensorProduct`).
* `euclideanTensorEquiv_basisFun` — it sends the tensor of factor basis vectors to the product-index
  basis vector, `(e_i ⊗ e_j) ↦ e_{(i,j)}` — the defining tensor-product correspondence, confirming the
  composite carrier is the tensor product with the standard product basis.

So the entropic framework's finite coordinate-product composite carries a genuine Hilbert tensor
product structure; only the infinite-dimensional case, and the identification of the framework's
Koopman *permutation* coupling with an arbitrary entangling gate, remain outside this statement.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.EuclideanTensorCompositionIso

open TensorProduct

/-- **The coordinate-product Hilbert space is the tensor product of the factors** (finite index): the
linear isometry equivalence `EuclideanSpace ℂ ι ⊗[ℂ] EuclideanSpace ℂ κ ≃ₗᵢ EuclideanSpace ℂ (ι × κ)`,
from the orthonormal tensor-product basis. -/
def euclideanTensorEquiv (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (EuclideanSpace ℂ ι ⊗[ℂ] EuclideanSpace ℂ κ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ι × κ) :=
  ((EuclideanSpace.basisFun ι ℂ).tensorProduct (EuclideanSpace.basisFun κ ℂ)).repr

/-- **The tensor isometry realizes the product basis**: the tensor of the factor basis vectors
`e_i ⊗ e_j` maps to the product-index unit vector `e_{(i,j)}` — the defining tensor-product
correspondence, so the coordinate-product carrier is the tensor product with the standard basis. -/
@[zil_level bridge_theorem]
theorem euclideanTensorEquiv_basisFun {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (i : ι) (j : κ) :
    euclideanTensorEquiv ι κ
        (EuclideanSpace.basisFun ι ℂ i ⊗ₜ[ℂ] EuclideanSpace.basisFun κ ℂ j)
      = EuclideanSpace.single (i, j) (1 : ℂ) := by
  rw [euclideanTensorEquiv, ← OrthonormalBasis.tensorProduct_apply, OrthonormalBasis.repr_self]

end Physlib.QuantumMechanics.EuclideanTensorCompositionIso

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.EuclideanTensorCompositionIso

zil attach euclideanTensorEquiv_basisFun where
  formalizes @ "claim:the-finite-coordinate-product-hilbert-space-euclidean-space-over-i-times-k-is-the-hilbert-tensor-product-of-the-factor-spaces-via-an-isometry-that-sends-the-tensor-of-factor-basis-vectors-to-the-product-index-basis-vector"

zil_file_contract physlib.euclideanTensorCompositionIso where
  promises "The coordinate-product Hilbert space is a tensor product, retiring for finite factors the not-a-tensor-product caveat of the entropic composition layer. There is a linear isometry equivalence between the tensor product of the two factor Euclidean spaces over i and over k and the coordinate-product Euclidean space over i times k, built from the orthonormal tensor-product basis. This isometry sends the tensor of the factor basis vectors e i tensor e j to the product-index unit vector e at i j, the defining tensor-product correspondence, so the finite coordinate-product composite carrier carries a genuine Hilbert tensor product structure with the standard product basis. Honest scope: this is the finite-dimensional case only; the infinite-dimensional Hilbert tensor product and the identification of the framework's Koopman permutation coupling with an arbitrary entangling gate remain outside this statement."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects []
  forbids_substitutes [
    "reading the finite coordinate-product tensor isometry as covering the infinite-dimensional Hilbert tensor product or as identifying the Koopman permutation coupling with an arbitrary entangling gate"
  ]
  witnessed_by [
    euclideanTensorEquiv_basisFun
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.euclideanTensorCompositionIso

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.DifferentialForms
public import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-!
# Lie derivatives and Cartan's formula

This module formalizes the Lie-derivative layer of Lovelock--Rund Section 4.4
on an arbitrary normed model space.

The implementation reuses Mathlib's Fréchet derivative, vector-field Lie
bracket, continuous alternating maps, and exterior derivative.

* Scalars: `L_V f = Df(V)`.
* Vector fields: `L_V W = [V,W]`.
* Positive-degree differential forms:
  `L_V ω = d(i_V ω) + i_V(dω)`.

The model space need not be finite dimensional.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open ContinuousAlternatingMap VectorField

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

/-- Lie derivative of a scalar or vector-valued function along a vector field. -/
def scalarLieDerivative
    (V : E → E) (f : E → F) : E → F :=
  fun x => fderiv 𝕜 f x (V x)

/-- A zero vector field differentiates every function to zero. -/
@[simp] theorem scalarLieDerivative_zero_vector
    (f : E → F) :
    scalarLieDerivative (𝕜 := 𝕜) 0 f = 0 := by
  funext x
  simp [scalarLieDerivative]

/-- The Lie derivative of a constant function vanishes. -/
@[simp] theorem scalarLieDerivative_const
    (V : E → E) (c : F) :
    scalarLieDerivative (𝕜 := 𝕜) V (fun _ => c) = 0 := by
  funext x
  simp [scalarLieDerivative]

/-- Lie derivative of one vector field along another is the Lie bracket. -/
def vectorLieDerivative
    (V W : E → E) : E → E :=
  lieBracket 𝕜 V W

/-- A vector field has zero Lie derivative along itself. -/
@[simp] theorem vectorLieDerivative_self
    (V : E → E) :
    vectorLieDerivative (𝕜 := 𝕜) V V = 0 :=
  lieBracket_self

/-- Interior product `i_V ω` of a vector field with a positive-degree form. -/
def interiorProduct
    (V : E → E)
    (ω : DifferentialForm 𝕜 E F (n + 1)) :
    DifferentialForm 𝕜 E F n :=
  fun x => (ω x).curryLeft (V x)

@[simp] theorem interiorProduct_apply
    (V : E → E)
    (ω : DifferentialForm 𝕜 E F (n + 1))
    (x : E) (v : Fin n → E) :
    interiorProduct V ω x v =
      ω x (Matrix.vecCons (V x) v) :=
  rfl

/-- Contracting the same vector twice into an alternating form gives zero. -/
@[simp] theorem interiorProduct_self_zero
    (V : E → E)
    (ω : DifferentialForm 𝕜 E F (n + 2)) :
    interiorProduct V (interiorProduct V ω) = 0 := by
  funext x
  exact curryLeft_same (ω x) (V x)

/-- Cartan Lie derivative of a positive-degree differential form. -/
def cartanLieDerivative
    (V : E → E)
    (ω : DifferentialForm 𝕜 E F (n + 1)) :
    DifferentialForm 𝕜 E F (n + 1) :=
  fun x =>
    extDeriv (interiorProduct V ω) x +
      interiorProduct V (extDeriv ω) x

/-- Cartan's formula, exposed as the defining pointwise identity. -/
theorem cartanLieDerivative_apply
    (V : E → E)
    (ω : DifferentialForm 𝕜 E F (n + 1)) (x : E) :
    cartanLieDerivative V ω x =
      extDeriv (interiorProduct V ω) x +
        interiorProduct V (extDeriv ω) x :=
  rfl

/-- On a closed form, Cartan's Lie derivative is exact. -/
theorem cartanLieDerivative_of_closed
    (V : E → E)
    (ω : DifferentialForm 𝕜 E F (n + 1))
    (hclosed : IsClosed ω) :
    cartanLieDerivative V ω =
      extDeriv (interiorProduct V ω) := by
  funext x
  unfold cartanLieDerivative
  rw [show extDeriv ω = 0 from hclosed]
  simp [interiorProduct]

/-- A zero vector field has zero Cartan Lie derivative. -/
@[simp] theorem cartanLieDerivative_zero_vector
    (ω : DifferentialForm 𝕜 E F (n + 1)) :
    cartanLieDerivative (0 : E → E) ω = 0 := by
  have hInterior : interiorProduct (0 : E → E) ω = 0 := by
    funext x
    change (ContinuousAlternatingMap.curryLeft (ω x)) 0 = 0
    exact map_zero (ContinuousAlternatingMap.curryLeft (ω x))
  funext x
  rw [cartanLieDerivative_apply, hInterior]
  have hExt :
      extDeriv (0 : DifferentialForm 𝕜 E F n) x = 0 := by
    unfold extDeriv
    rw [show fderiv 𝕜 (0 : E → E [⋀^Fin n]→L[𝕜] F) x = 0 by
      exact congrFun fderiv_zero x]
    exact map_zero
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F)
  rw [hExt]
  simp [interiorProduct]

end Physlib.Mathematics.LovelockRund

end

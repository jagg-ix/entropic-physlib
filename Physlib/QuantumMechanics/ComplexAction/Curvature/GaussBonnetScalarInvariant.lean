/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
meta import Zil

/-!
# The Gauss–Bonnet scalar as a curvature invariant

Lovelock's order-2 Lagrangian is the Gauss–Bonnet (Euler) density

`𝒢 = R_{abcd}R^{abcd} − 4 R_{ab}R^{ab} + R²`,

the quadratic curvature invariant whose variation gives the Lovelock order-2 field equation.  The
repository carried only the *scalar formula* `eulerDensity4D r s t = r − 4s + t` in abstract arguments and
the combinatorial `genKroneckerTrace` termination layer; it never built `𝒢` as an actual contraction of the
Riemann/Ricci tensors.  This module supplies it, from the existing `ricci`, `scalarCurvature` and the raised
Riemann self-contraction, and records its two structural reductions.

* `kretschmann` — the Kretschmann scalar `R_{abcd}R^{abcd}` (full Riemann self-contraction).
* `ricciSquared` — `R_{ab}R^{ab}`.
* `gaussBonnetScalar` — `𝒢 = kretschmann − 4·ricciSquared + R²`.
* `gaussBonnetScalar_flat` — `𝒢 = 0` for a flat metric.
* `gaussBonnetScalar_ricciFlat` — for a **Ricci-flat (vacuum-Einstein)** metric `𝒢 = R_{abcd}R^{abcd}`,
  the Kretschmann scalar, which is generally nonzero (e.g. Schwarzschild).  This is the essential Lovelock
  content: the Gauss–Bonnet term is dynamically distinct from Einstein–Hilbert — non-trivial even in
  vacuum — so in `D ≥ 5` it is an independent gravitational sector.

Honest scope: this is the scalar (Lagrangian-density) invariant.  The order-2 Lovelock *tensor*
`H_{ab}` obtained by varying `𝒢`, and its divergence-freeness, are not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.GaussBonnetScalarInvariant

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad

variable {ι : Type*} [Fintype ι]

/-- **The Kretschmann scalar** `R_{abcd}R^{abcd}` — the full self-contraction of the Riemann tensor with
four inverse-metric raises. -/
def kretschmann (gInv : Matrix ι ι ℝ) (Rm : RiemannTensor ι) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Rm a b c d *
    ∑ p, ∑ q, ∑ r, ∑ s, gInv a p * gInv b q * gInv c r * gInv d s * Rm p q r s

/-- **The Ricci-squared invariant** `R_{ab}R^{ab}` — the self-contraction of the Ricci tensor. -/
def ricciSquared (gInv : Matrix ι ι ℝ) (Rm : RiemannTensor ι) : ℝ :=
  ∑ b, ∑ d, ricci gInv Rm b d * ∑ p, ∑ q, gInv b p * gInv d q * ricci gInv Rm p q

/-- **The Gauss–Bonnet (Euler) scalar** `𝒢 = R_{abcd}R^{abcd} − 4 R_{ab}R^{ab} + R²`, Lovelock's order-2
Lagrangian density built from actual curvature contractions. -/
def gaussBonnetScalar (gInv : Matrix ι ι ℝ) (Rm : RiemannTensor ι) : ℝ :=
  kretschmann gInv Rm - 4 * ricciSquared gInv Rm + (scalarCurvature gInv Rm) ^ 2

/-- **The Kretschmann scalar of a flat metric vanishes** `R_{abcd} = 0 ⇒ R_{abcd}R^{abcd} = 0`. -/
@[simp] lemma kretschmann_zero (gInv : Matrix ι ι ℝ) : kretschmann gInv (0 : RiemannTensor ι) = 0 := by
  simp [kretschmann]

/-- **The Ricci-squared invariant of a flat metric vanishes.** -/
@[simp] lemma ricciSquared_zero (gInv : Matrix ι ι ℝ) : ricciSquared gInv (0 : RiemannTensor ι) = 0 := by
  simp [ricciSquared]

/-- **The scalar curvature of a flat metric vanishes** `R_{abcd} = 0 ⇒ R = 0`. -/
lemma scalarCurvature_zero (gInv : Matrix ι ι ℝ) : scalarCurvature gInv (0 : RiemannTensor ι) = 0 := by
  rw [scalarCurvature, ricci_zero]; simp [ricciScalarContraction]

/-- **The Gauss–Bonnet scalar of a flat metric vanishes** `R_{abcd} = 0 ⇒ 𝒢 = 0`. -/
@[zil_level physical_theorem]
theorem gaussBonnetScalar_flat (gInv : Matrix ι ι ℝ) :
    gaussBonnetScalar gInv (0 : RiemannTensor ι) = 0 := by
  simp [gaussBonnetScalar, scalarCurvature_zero]

/-- **For a Ricci-flat (vacuum-Einstein) metric the Gauss–Bonnet scalar equals the Kretschmann scalar**
`R_{ab} = 0 ⇒ 𝒢 = R_{abcd}R^{abcd}`.  The `−4 R_{ab}R^{ab}` and `R²` terms drop, leaving the Riemann
self-contraction, which is generally nonzero — the Gauss–Bonnet term is dynamically distinct from
Einstein–Hilbert and non-trivial even in vacuum. -/
@[zil_level physical_theorem]
theorem gaussBonnetScalar_ricciFlat (gInv : Matrix ι ι ℝ) (Rm : RiemannTensor ι)
    (h : ricci gInv Rm = 0) :
    gaussBonnetScalar gInv Rm = kretschmann gInv Rm := by
  have hric : ricciSquared gInv Rm = 0 := by
    unfold ricciSquared; simp [h]
  have hsc : scalarCurvature gInv Rm = 0 := by
    rw [scalarCurvature, h]; simp [ricciScalarContraction]
  rw [gaussBonnetScalar, hric, hsc]; ring

end Physlib.QuantumMechanics.ComplexAction.Curvature.GaussBonnetScalarInvariant

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.GaussBonnetScalarInvariant

zil attach gaussBonnetScalar_flat where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.GaussBonnetScalarInvariant.scalarCurvature_zero",
  formalizes @ "claim:the-lovelock-order-two-gauss-bonnet-euler-scalar-riemann-squared-minus-four-ricci-squared-plus-scalar-curvature-squared-built-from-actual-curvature-contractions-vanishes-for-a-flat-metric"

zil attach gaussBonnetScalar_ricciFlat where
  formalizes @ "claim:for-a-ricci-flat-vacuum-einstein-metric-the-gauss-bonnet-scalar-equals-the-kretschmann-scalar-the-riemann-self-contraction-so-the-gauss-bonnet-term-is-dynamically-distinct-from-einstein-hilbert-and-non-trivial-even-in-vacuum"

zil_file_contract physlib.gaussBonnetScalarInvariant where
  promises "The Gauss-Bonnet scalar as a genuine curvature invariant, Lovelock's order-two Euler Lagrangian density built from actual contractions of the Riemann and Ricci tensors rather than an abstract scalar formula. The Kretschmann scalar is the full self-contraction of the Riemann tensor with four inverse-metric raises; the Ricci-squared invariant is the self-contraction of the Ricci tensor; and the Gauss-Bonnet scalar is the Kretschmann scalar minus four times the Ricci-squared invariant plus the scalar curvature squared. It vanishes for a flat metric. For a Ricci-flat vacuum-Einstein metric the minus-four-Ricci-squared and scalar-curvature-squared terms drop and the Gauss-Bonnet scalar equals the Kretschmann scalar, which is generally nonzero, so the Gauss-Bonnet term is dynamically distinct from the Einstein-Hilbert term and non-trivial even in vacuum. Honest scope: this is the scalar Lagrangian-density invariant; the order-two Lovelock tensor obtained by varying it, and its divergence-freeness, are not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.ricci",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.scalarCurvature"
  ]
  forbids_substitutes [
    "reading the Gauss-Bonnet scalar Lagrangian-density invariant as the order-two Lovelock tensor obtained by varying it or as a proof of its divergence-freeness"
  ]
  witnessed_by [
    gaussBonnetScalar_flat,
    gaussBonnetScalar_ricciFlat
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.gaussBonnetScalarInvariant

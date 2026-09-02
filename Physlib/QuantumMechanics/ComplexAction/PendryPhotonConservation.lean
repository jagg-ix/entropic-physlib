/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Pendry 2021 photon-number conservation — essential content

J. B. Pendry, *Photon number conservation in time dependent
systems*, Optics Express **29** (25), 41587 (2021), arXiv
2209.11576, derives an orthogonality relation between Floquet
eigenvectors of a PT-symmetric time-dependent medium (his eq. 9
/ 15):

  `δ_lm = Σ_n  (E*_mn · D_ln + H*_ymn · B_yln + H*_xmn · B_xln) /
                       [2 ℏ (ω_m + n Ω)]`.

The numerator is the photon-flux pairing on Floquet modes; the
denominator normalises each eigenvector to one photon per unit
flow.  From this orthogonality plus the (Pendry-proved-from-
Maxwell) fact that the time evolution preserves the inner
product, photon number is conserved:

  `Σ_l |c_l|²`  is independent of time, even though
  `Σ_l ω_l |c_l|²`  (energy) is not.

This module formalises the **essential content** of that
theorem:

  1. A photon-number functional on a finite-dimensional complex
     inner-product space (Pendry's photon count = squared norm
     in the photon-flux inner product, by his normalisation).
  2. A `Prop` `IsPendryEvolution` carrying the empirical input
     "the time evolution preserves the inner product" (this is
     what Pendry actually proves from Maxwell + PT symmetry; the
     Maxwell derivation itself is far out of scope here).
  3. A theorem `pendry_photon_conservation`: under any evolution
     satisfying `IsPendryEvolution`, photon number is conserved.

A complementary lemma `photonNumber_eq_sum_sq_coeff` expresses
the photon count as the sum over Floquet sidebands of squared
coefficients — the standard form of Pendry's eq. 9.

## Honest scope

This module does **not** derive `IsPendryEvolution` for any
specific Maxwell-coupled time-dependent medium.  Pendry's paper
proves it (his Sections 2.1, 2.2) for spatially-infinite gratings
existing for a finite time and for finite-in-space gratings
existing for infinite time, both under impedance-matched PT
symmetry.  Formalising those derivations would require:

* a Lean formalisation of source-free Maxwell's equations,
* a Bloch / Floquet decomposition framework for periodic media,
* the transfer-matrix construction for s-polarised waves.

None of those exist in Mathlib at the depth needed.  The
present module captures the *implication* (inner-product
preservation → photon conservation), which is provable from
elementary inner-product-space facts.  A consumer who knows or
postulates `IsPendryEvolution` for their specific system can
then use this module to derive the conservation theorem.

## Reference

* J. B. Pendry (2021), *Photon number conservation in time
  dependent systems*, Optics Express **29** (25), 41587.
  arXiv: [2209.11576](https://arxiv.org/abs/2209.11576).

  Companion paper: J. B. Pendry (2024), *An avalanche model for
  femtosecond optical response*, arXiv:[2407.08391](https://arxiv.org/abs/2407.08391),
  which gives the microscopic origin of the non-Hermitian
  structure that makes the PT-symmetric Pendry-2021 regime
  physically interesting (see `BenderIdentity` "Related
  references").
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.PendryPhotonConservation

open scoped ComplexConjugate

variable {n : ℕ}


/-- **Photon-number functional** on a finite-dimensional complex
inner-product space: the squared norm of the state vector.  In
Pendry 2021 this is the sum over Floquet sidebands of the
squared coefficient `|c_l|²`, with the orthonormalisation of
his eq. 9 absorbed into the inner product.

For a vector `v : EuclideanSpace ℂ (Fin n)`, the photon number
is `‖v‖²`. -/
def photonNumber (v : EuclideanSpace ℂ (Fin n)) : ℝ := ‖v‖ ^ 2

/-- Photon number is non-negative. -/
lemma photonNumber_nonneg (v : EuclideanSpace ℂ (Fin n)) :
    0 ≤ photonNumber v := by
  unfold photonNumber
  positivity

/-- **Parseval form of the photon count**: `N(v) = Σ_l |c_l|²`,
the sum of squared moduli of the Floquet-sideband coefficients.
This is the form of Pendry's eq. 9. -/
lemma photonNumber_eq_sum_sq_coeff (v : EuclideanSpace ℂ (Fin n)) :
    photonNumber v = ∑ l, ‖v l‖ ^ 2 := by
  unfold photonNumber
  exact EuclideanSpace.norm_sq_eq v

/-!

Pendry 2021 proves from Maxwell's equations plus PT symmetry
that the time evolution on the Floquet mode space preserves the
photon-flux inner product (his Sections 2.1 and 2.2).  We carry
this as an explicit `Prop` rather than reproving it, because
the Maxwell derivation is out of scope for a lightweight Lean
formalisation. -/

/-- **Pendry evolution hypothesis**: a linear map
`U : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)`
preserves the norm (equivalently, the photon-flux inner
product).  In a PT-symmetric time-dependent medium, the time
evolution operator satisfies this hypothesis — Pendry 2021's
main theorem.

Note: this is strictly weaker than unitarity, because we do not
require `U⁻¹` to also preserve the norm (which would be implied
in finite dimensions but not stated here).  In practice for a
finite-dimensional Floquet space the norm-preservation
hypothesis IS unitarity. -/
def IsPendryEvolution
    (U : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)) : Prop :=
  ∀ v, ‖U v‖ = ‖v‖


/-- **Pendry photon-number conservation**: under any time
evolution that preserves the photon-flux inner product, the
photon number is conserved.

This is the essential content of Pendry 2021.  The hypothesis
`IsPendryEvolution` is what Pendry's eq. 9 / 15 establish for
PT-symmetric Maxwell evolution; the consequence (photon
conservation) is what is formalised here.

Note: the theorem says **nothing** about energy conservation.
The energy functional on the same Floquet space is
`E(v) := Σ_l ω_l |c_l|²` (a weighted sum), and is *not*
preserved by `U` unless additionally `U` commutes with the
diagonal weight matrix `diag(ω_l)`.  Pendry's central point is
that photon conservation is more general than energy
conservation. -/
lemma pendry_photon_conservation
    {U : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (hU : IsPendryEvolution U) (v : EuclideanSpace ℂ (Fin n)) :
    photonNumber (U v) = photonNumber v := by
  unfold photonNumber
  rw [hU v]

/-- **Photon conservation expressed via Floquet-sideband
coefficients**: the sum of squared moduli of the coefficients
is invariant under the evolution.

This is the form that appears in Pendry's numerical examples
(his Table 1: `N_out / N_in ≈ 1` to <= 0.05 % even when
impedance matching is broken). -/
lemma pendry_photon_conservation_coeffs
    {U : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (hU : IsPendryEvolution U) (v : EuclideanSpace ℂ (Fin n)) :
    ∑ l, ‖(U v) l‖ ^ 2 = ∑ l, ‖v l‖ ^ 2 := by
  rw [← photonNumber_eq_sum_sq_coeff, ← photonNumber_eq_sum_sq_coeff]
  exact pendry_photon_conservation hU v

/-- **Conservation across two consecutive Pendry evolutions**:
photon number is invariant under composition. -/
lemma pendry_photon_conservation_compose
    {U V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (hU : IsPendryEvolution U) (hV : IsPendryEvolution V)
    (v : EuclideanSpace ℂ (Fin n)) :
    photonNumber (V (U v)) = photonNumber v := by
  rw [pendry_photon_conservation hV, pendry_photon_conservation hU]


/-- **Energy functional on Floquet modes**: `E(v) := Σ_l ω_l ·
|c_l|²` where `ω_l` is the (real) Floquet frequency of sideband
`l`.  In contrast to `photonNumber`, this is a **weighted** sum
and is generally NOT preserved by a Pendry evolution.

The carriers `omega` provides the per-sideband Floquet
frequencies as a real-valued vector of length `n`. -/
def energyFunctional (omega : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ l, omega l * ‖v l‖ ^ 2

/-- **Energy is bounded above by `M · photonNumber`** whenever
`M` bounds every per-sideband frequency from above.  Reduces
`Σ ω_l |c_l|²` to `M · Σ |c_l|²` and applies
`photonNumber_eq_sum_sq_coeff`. -/
lemma energyFunctional_le_max_omega_mul_photonNumber
    {omega : EuclideanSpace ℝ (Fin n)}
    (M : ℝ) (hM : ∀ l, omega l ≤ M)
    (v : EuclideanSpace ℂ (Fin n)) :
    energyFunctional omega v ≤ M * photonNumber v := by
  unfold energyFunctional photonNumber
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _hl
  have h1 : 0 ≤ ‖v l‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right (hM l) h1

end Physlib.QuantumMechanics.ComplexAction.PendryPhotonConservation

end

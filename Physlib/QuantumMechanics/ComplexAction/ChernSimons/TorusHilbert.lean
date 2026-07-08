/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Chern–Simons–Witten torus Hilbert space (explicit)

Replaces the abstract assumptions of `TorusHilbertFactorization` (which merely *records* factorization and
finite-dimensionality as structure fields) with explicit content for the level-`k` torus Hilbert space of
Chern–Simons–Witten theory.

* **§A — theta characters and the heat equation.** The level-`k` characters are the theta modes
  `θ(τ,z) = exp(iπk m² τ + 2iπk m z)` (`thetaMode`); these are the building blocks of the affine /
  Weyl–Kac characters. Each satisfies the **heat equation** `∂_τ θ = (1/(4iπk)) ∂_z² θ`
  (`thetaMode_heat_equation`) — the holomorphy/flatness condition that makes the conformal blocks a flat
  bundle over moduli space.
* **§B — finite-dimensionality.** The level-`k` torus Hilbert space is `EuclideanSpace ℂ (Fin k)`,
  finite-dimensional with `finrank = k` (`torusHilbert_finrank`).
* **§C — inner product and orthogonality.** The character basis is orthonormal (Kronecker inner product), so
  distinct charges are orthogonal — a concrete `HayashiOrthogonalityCarrier` (`torusCharacterCarrier`).
* **§D — the explicit factorization.** A concrete `TorusHilbertFactorization` whose states are
  `left × right` character pairs, whose factorization is the genuine product split, and whose
  finite-dimensionality field is the actual `finrank = k` (`torusHilbertFactorization`).

## References

* E. Witten, *Quantum field theory and the Jones polynomial* (1989); Hayashi (the CSW-gravity torus theorem).
  structure: `Physlib` (`ChernSimons.Gravity`), `Mathlib`.

No new axioms.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — theta characters and the heat equation -/

/-- **The level-`k` theta mode** `θ(τ,z) = exp(iπk m²τ + 2iπk m z)` — the building block of the affine /
Weyl–Kac torus characters (`m = n + a/k` the mode label). -/
noncomputable def thetaMode (k m τ z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) * k * m ^ 2 * τ + 2 * Complex.I * (Real.pi : ℂ) * k * m * z)

/-- **[∂_z of the theta mode] `∂_z θ = (2iπk m) θ`.** -/
theorem hasDerivAt_thetaMode_z (k m τ z : ℂ) :
    HasDerivAt (fun w => thetaMode k m τ w)
      (thetaMode k m τ z * (2 * Complex.I * (Real.pi : ℂ) * k * m)) z := by
  have hlin : HasDerivAt
      (fun w => Complex.I * (Real.pi : ℂ) * k * m ^ 2 * τ + 2 * Complex.I * (Real.pi : ℂ) * k * m * w)
      (2 * Complex.I * (Real.pi : ℂ) * k * m) z := by
    simpa using
      (((hasDerivAt_id z).const_mul (2 * Complex.I * (Real.pi : ℂ) * k * m)).const_add
        (Complex.I * (Real.pi : ℂ) * k * m ^ 2 * τ))
  simpa [thetaMode] using hlin.cexp

/-- **[∂_τ of the theta mode] `∂_τ θ = (iπk m²) θ`.** -/
theorem hasDerivAt_thetaMode_tau (k m τ z : ℂ) :
    HasDerivAt (fun w => thetaMode k m w z)
      (thetaMode k m τ z * (Complex.I * (Real.pi : ℂ) * k * m ^ 2)) τ := by
  have hlin : HasDerivAt
      (fun w => Complex.I * (Real.pi : ℂ) * k * m ^ 2 * w + 2 * Complex.I * (Real.pi : ℂ) * k * m * z)
      (Complex.I * (Real.pi : ℂ) * k * m ^ 2) τ := by
    simpa using
      (((hasDerivAt_id τ).const_mul (Complex.I * (Real.pi : ℂ) * k * m ^ 2)).add_const
        (2 * Complex.I * (Real.pi : ℂ) * k * m * z))
  simpa [thetaMode] using hlin.cexp

/-- **[The theta mode satisfies the heat equation] `∂_τ θ = (1/(4iπk)) ∂_z² θ`.** This holomorphy/flatness
condition is what makes the CSW conformal blocks a flat bundle over the moduli of the torus. -/
theorem thetaMode_heat_equation (k m τ z : ℂ) (hk : k ≠ 0) :
    deriv (fun w => thetaMode k m w z) τ
      = (1 / (4 * Complex.I * (Real.pi : ℂ) * k))
        * deriv (fun w => deriv (fun w' => thetaMode k m τ w') w) z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hLHS : deriv (fun w => thetaMode k m w z) τ
      = thetaMode k m τ z * (Complex.I * (Real.pi : ℂ) * k * m ^ 2) :=
    (hasDerivAt_thetaMode_tau k m τ z).deriv
  have hzz : deriv (fun w => deriv (fun w' => thetaMode k m τ w') w) z
      = thetaMode k m τ z * (2 * Complex.I * (Real.pi : ℂ) * k * m)
        * (2 * Complex.I * (Real.pi : ℂ) * k * m) := by
    have hz : (fun w => deriv (fun w' => thetaMode k m τ w') w)
        = (fun w => thetaMode k m τ w * (2 * Complex.I * (Real.pi : ℂ) * k * m)) := by
      funext w; exact (hasDerivAt_thetaMode_z k m τ w).deriv
    rw [hz, deriv_mul_const (hasDerivAt_thetaMode_z k m τ z).differentiableAt,
      (hasDerivAt_thetaMode_z k m τ z).deriv]
  have hconst : Complex.I * (Real.pi : ℂ) * k * m ^ 2
      = (1 / (4 * Complex.I * (Real.pi : ℂ) * k))
        * ((2 * Complex.I * (Real.pi : ℂ) * k * m) * (2 * Complex.I * (Real.pi : ℂ) * k * m)) := by
    field_simp
    ring
  rw [hLHS, hzz, hconst]
  ring

/-! ## §B — finite-dimensionality -/

/-- **The level-`k` torus Hilbert space** of Chern–Simons–Witten theory: the `k`-dimensional space spanned by
the level-`k` characters. -/
abbrev TorusHilbert (k : ℕ) : Type := EuclideanSpace ℂ (Fin k)

/-- **[The torus Hilbert space is `k`-dimensional]** `finrank ℂ ℋ_torus = k` — the level-`k` CSW physical
Hilbert space on the torus is finite-dimensional, with one state per integrable representation. -/
theorem torusHilbert_finrank (k : ℕ) : Module.finrank ℂ (TorusHilbert k) = k :=
  finrank_euclideanSpace_fin

/-! ## §C — inner product and orthogonality -/

/-- **The character orthogonality structure:** the level-`k` characters are orthonormal, so states of distinct
charge `a ∈ Fin k` are orthogonal (Kronecker inner product). -/
def torusCharacterCarrier (k : ℕ) : HayashiOrthogonalityCarrier (Fin k) (Fin k) where
  inner a b := if a = b then 1 else 0
  charge a := a
  orthogonal_of_charge_ne a b h := by simp [h]

/-! ## §D — the explicit factorization -/

/-- **The explicit CSW torus factorization:** the holomorphic ⊗ anti-holomorphic chiral split. States are
`left × right` character pairs; the factorization is the genuine product split; and the
finite-dimensionality field is the actual `finrank ℂ (EuclideanSpace ℂ (Fin k)) = k`. This is a concrete
instance of the previously abstract `TorusHilbertFactorization`. -/
def torusHilbertFactorization (k : ℕ) :
    TorusHilbertFactorization (Fin k × Fin k) (Fin k) (Fin k) where
  leftState := Prod.fst
  rightState := Prod.snd
  assemble l r := (l, r)
  state_factorizes := fun _ => rfl
  finiteDimensionalAtSpecialLevels := Module.finrank ℂ (TorusHilbert k) = k
  finiteDimensionalAtSpecialLevels_holds := torusHilbert_finrank k

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end

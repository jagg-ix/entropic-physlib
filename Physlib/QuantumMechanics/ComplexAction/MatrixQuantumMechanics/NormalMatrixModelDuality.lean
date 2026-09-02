/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MQMInvertedOscillatorPhase
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# MQM and the Normal Matrix Model: a duality (Alexandrov §VI)

Tachyon perturbations of compactified MQM are dual to the **Normal Matrix Model** (NMM): the grand canonical
MQM partition function coincides with an analytic continuation of the canonical NMM partition function, both
being τ-functions of the Toda hierarchy (Alexandrov, hep-th/0311273, Ch. VI). In the classical limit the
non-compact MQM Fermi sea (a hyperbola `x₊x₋ = μ`) maps to the compact NMM eigenvalue spot (a circle
`(zz̄)^R = const`) under the analytic continuation `x₊ ↔ z^R`, `x₋ ↔ z̄^R` — a duality exchanging the `A`- and
`B`-cycles of an associated complex curve.

* **§A — unitarity of the reflection factor** (Eq. VI.28). `reflectionFactor_unitary`: any reflection factor
  with `‖R‖ = 1` obeys `R̄ R = 1`; `reflectionFactor_crossing_unitary` adds the crossing relation
  `R(−E) = R̄(E)` to give `R(−E)R(E) = 1`. `reflectionFactor_invertedOscillator_unitary` instantiates this on
  the concrete inverted-oscillator reflection coefficient — the same unitarity established in
  `[[project_alexandrov_mqm_thesis]]` (`MatrixQuantumMechanics.MQMInvertedOscillatorPhase.mqmGammaRatio_norm_one`).
* **§B — the equally-spaced spectrum** (Eq. VI.16). `mqmEnergyLevel ℏ R μ n = −μ + iℏ(n+½)/R`; the spacing
  `E_{n+1} − E_n = iℏ/R` (`mqmEnergyLevel_spacing`) — the discrete, equally-spaced spectrum that makes the
  canonical (NMM) representation possible.
* **§C — the duality map** (Eqs. VI.30–VI.31). `duality_product_map`: under `x₊ = x^R`, `x₋ = y^R` the MQM
  product `x₊x₋` equals the NMM spot variable `(xy)^R`, so the Fermi-sea hyperbola `x₊x₋ = μ` is the NMM circle
  `(xy)^R = μ`.

## References

* S. Yu. Alexandrov, *Matrix Quantum Mechanics and Two-dimensional String Theory in Non-trivial
  Backgrounds*, hep-th/0311273, Ch. VI, Eqs. (VI.16), (VI.28), (VI.30)–(VI.31).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MQMInvertedOscillatorPhase

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.NormalMatrixModelDuality


/-- **[Reflection-factor unitarity, Eq. VI.28]** a unimodular reflection factor `‖R‖ = 1` obeys `R̄ R = 1`.
This is the pure-phase property of the MQM scattering used throughout the NMM duality proof. -/
lemma reflectionFactor_unitary {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z * z = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  norm_num

/-- **[Crossing + unitarity, Eq. VI.28]** with the crossing relation `R(−E) = R̄(E)` and `‖R(E)‖ = 1`,
`R(−E) R(E) = 1`. -/
lemma reflectionFactor_crossing_unitary (R : ℝ → ℂ) (E : ℝ)
    (hcross : R (-E) = (starRingEnd ℂ) (R E)) (hnorm : ‖R E‖ = 1) :
    R (-E) * R E = 1 := by
  rw [hcross]
  exact reflectionFactor_unitary hnorm

/-- **[VI.28 for the inverted oscillator]** the concrete inverted-oscillator / Moore–Plesser–Ramgoolam
reflection coefficient `Γ(½+iε)/Γ(½−iε)` satisfies the unitarity relation `R̄ R = 1` — the matrix-model
unitarity that underlies the MQM ↔ NMM duality is the inverted-oscillator scattering unitarity. -/
lemma reflectionFactor_invertedOscillator_unitary (ε : ℝ) :
    (starRingEnd ℂ) (Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (ε : ℂ))
        / Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (ε : ℂ)))
      * (Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (ε : ℂ))
        / Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (ε : ℂ))) = 1 :=
  reflectionFactor_unitary (mqmGammaRatio_norm_one ε)


/-- **The equally-spaced MQM/NMM energy spectrum** `E_n = −μ + iℏ(n+½)/R` (Eq. VI.16) — the discrete spectrum
of the compactified, perturbed theory whose `ℛ`-factor product is the partition function (Eq. VI.18). -/
noncomputable def mqmEnergyLevel (ℏ R μ : ℝ) (n : ℕ) : ℂ :=
  -(μ : ℂ) + Complex.I * (ℏ : ℂ) * ((n : ℂ) + 1 / 2) / (R : ℂ)

/-- **[Equal spacing, Eq. VI.16]** `E_{n+1} − E_n = iℏ/R` — the spectrum is equally spaced, the property that
allows the canonical (NMM) representation of the grand canonical MQM partition function. -/
lemma mqmEnergyLevel_spacing (ℏ R μ : ℝ) (n : ℕ) :
    mqmEnergyLevel ℏ R μ (n + 1) - mqmEnergyLevel ℏ R μ n = Complex.I * (ℏ : ℂ) / (R : ℂ) := by
  unfold mqmEnergyLevel
  push_cast
  ring


/-- **[Duality map, Eqs. VI.30–VI.31]** under the analytic continuation `x₊ = x^R`, `x₋ = y^R` the MQM Fermi-sea
product `x₊ x₋` equals the NMM eigenvalue-spot variable `(xy)^R`. Hence the MQM hyperbola `x₊x₋ = μ` becomes the
NMM circle `(xy)^R = μ`: the non-compact Fermi sea is analytically continued to the compact eigenvalue spot. -/
lemma duality_product_map (x y R : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ R * y ^ R = (x * y) ^ R :=
  (Real.mul_rpow hx hy).symm

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.NormalMatrixModelDuality

end

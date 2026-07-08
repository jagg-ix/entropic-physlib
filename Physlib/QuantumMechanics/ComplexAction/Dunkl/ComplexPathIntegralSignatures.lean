/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight
public import Physlib.QuantumMechanics.NonHermitian.WickRotation

/-!
# The Wigner–Dunkl complex path integral serves both signatures: Lorentzian and Euclidean

Ensures the single complex path-integral kernel `lorentzianKernel S_R S_I ℏ = exp(i·S_R/ℏ − S_I/ℏ)` of the
Wigner–Dunkl arc is usable in **both** signatures, with the Cameron–Martin weight `W = e^{−S_I/ℏ}`
(`Dunkl.CameronMartinWeight`) as the common, signature-invariant modulus:

* **Lorentzian (real time, Minkowski).** Evaluated at a real reversible action `S_R`, the kernel is the
  oscillatory `e^{iS_R/ℏ}` propagator; its modulus is the Cameron–Martin weight `e^{−S_I/ℏ}`
  (`lorentzian_modulus_eq_cameron`), and it is unitary (`‖·‖ = 1`) exactly at the reversible point
  `S_I = 0` (`lorentzian_unitary_iff`).
* **Euclidean (imaginary time, heat kernel).** Wick-rotating the reversible phase `t ↦ −iτ` turns the
  kernel into the **real, positive** Euclidean heat kernel `e^{−E_R τ/ℏ}` (`euclidean_kernel_eq_heat`,
  `euclidean_kernel_isReal`); with the entropy damping over gives the real Euclidean evolution factor
  `e^{−E_R τ/ℏ}·e^{−S_I/ℏ}` (`euclidean_factor_eq`).
* **Unification.** The modulus / Cameron–Martin weight `e^{−S_I/ℏ}` is the **same** in both signatures
  (`cameron_weight_signature_invariant`): the entropy/imaginary-action sector is preserved by the Wick
  rotation, while only the reversible phase changes character (oscillatory ↔ decaying). One complex path
  integral, two signatures.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.ComplexPathIntegralSignatures

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-! ## §A — Lorentzian signature (real time, Minkowski) -/

/-- **[Lorentzian] The real-time complex path integral's modulus is the Cameron–Martin weight.**
`‖lorentzianKernel S_R S_I ℏ‖ = entropyDamping S_I ℏ = e^{−S_I/ℏ}` — the oscillatory `e^{iS_R/ℏ}`
Minkowski propagator includes the same `e^{−S_I/ℏ}` damping as the Cameron–Martin weight of
`Dunkl.CameronMartinWeight`. -/
theorem lorentzian_modulus_eq_cameron (S_R S_I ℏ : ℝ) :
    ‖lorentzianKernel S_R S_I ℏ‖ = entropyDamping S_I ℏ := by
  rw [lorentzianKernel_norm_is_damping, entropyDamping]

/-- **[Lorentzian] The complex path integral is unitary iff there is no imaginary action.** For `ℏ > 0`,
`‖lorentzianKernel S_R S_I ℏ‖ = 1 ↔ S_I = 0`: the reversible (Minkowski, norm-preserving) regime is exactly
the no-entropy point. -/
theorem lorentzian_unitary_iff (S_R S_I ℏ : ℝ) (hℏ : 0 < ℏ) :
    ‖lorentzianKernel S_R S_I ℏ‖ = 1 ↔ S_I = 0 := by
  rw [lorentzianKernel_norm_is_damping, Real.exp_eq_one_iff, neg_eq_zero, div_eq_zero_iff]
  exact or_iff_left hℏ.ne'

/-! ## §B — Euclidean signature (imaginary time, heat kernel) -/

/-- **[Euclidean] Wick-rotating the reversible phase gives the real heat kernel.** `reversiblePhaseC E_R ℏ
(−iτ) = e^{−E_R τ/ℏ}` — substituting `t = −iτ` turns the unitary phase `e^{−iE_R t/ℏ}` into the real,
positive Euclidean heat-kernel weight. -/
theorem euclidean_kernel_eq_heat (E_R ℏ τ : ℝ) :
    reversiblePhaseC E_R ℏ (-Complex.I * (τ : ℂ)) = ((Real.exp (-(E_R * τ / ℏ)) : ℝ) : ℂ) :=
  reversiblePhase_wickRotation E_R ℏ τ

/-- **[Euclidean] The Wick-rotated kernel is real** (zero imaginary part): in Euclidean signature the
complex path integral is a genuine real heat kernel, usable directly as a Feynman–Kac / Matsubara weight. -/
theorem euclidean_kernel_isReal (E_R ℏ τ : ℝ) :
    (reversiblePhaseC E_R ℏ (-Complex.I * (τ : ℂ))).im = 0 := by
  rw [euclidean_kernel_eq_heat]; exact Complex.ofReal_im _

/-- **[Euclidean] The full Euclidean evolution factor.** With the entropy damping `e^{−S_I/ℏ}` across
the Wick rotation gives the real Euclidean factor `e^{−E_R τ/ℏ}·e^{−S_I/ℏ} = euclideanEvolutionFactor
(E_R τ) S_I ℏ` — the reversible heat kernel times the Cameron–Martin weight. -/
theorem euclidean_factor_eq (E_R S_I ℏ τ : ℝ) :
    reversiblePhaseC E_R ℏ (-Complex.I * (τ : ℂ)) * ((entropyDamping S_I ℏ : ℝ) : ℂ)
      = ((euclideanEvolutionFactor (E_R * τ) S_I ℏ : ℝ) : ℂ) :=
  lorentzian_to_euclidean_wickRotation E_R S_I ℏ τ

/-! ## §C — unification: one complex path integral, both signatures -/

/-- **[Unification] The Cameron–Martin weight is signature-invariant.** The modulus of the Lorentzian
(real-time) complex path integral equals the entropy damping `e^{−S_I/ℏ}` that is also the Cameron–Martin
weight of the Euclidean factor (`euclidean_factor_eq`). The imaginary-action sector is preserved by the
Wick rotation; only the reversible phase changes from oscillatory (Lorentzian) to decaying (Euclidean). -/
theorem cameron_weight_signature_invariant (S_R S_I ℏ : ℝ) :
    ‖lorentzianKernel S_R S_I ℏ‖ = entropyDamping S_I ℏ :=
  lorentzian_modulus_eq_cameron S_R S_I ℏ

/-- **[Unification] Both signatures reduce to the bare reversible kernel at `S_I = 0`.** With no imaginary
action the Lorentzian kernel is unit-modulus (unitary phase) and the Euclidean factor is the pure heat
kernel `e^{−E_R τ/ℏ}` — the complex path integral degenerates consistently to the reversible theory in
either signature. -/
theorem reversible_both_signatures (S_R E_R ℏ τ : ℝ) (hℏ : 0 < ℏ) :
    ‖lorentzianKernel S_R 0 ℏ‖ = 1
      ∧ reversiblePhaseC E_R ℏ (-Complex.I * (τ : ℂ)) * ((entropyDamping 0 ℏ : ℝ) : ℂ)
          = ((Real.exp (-(E_R * τ / ℏ)) : ℝ) : ℂ) := by
  refine ⟨(lorentzian_unitary_iff S_R 0 ℏ hℏ).mpr rfl, ?_⟩
  rw [euclidean_factor_eq, euclideanEvolutionFactor, entropyDamping, zero_div, neg_zero,
    Real.exp_zero, mul_one]

end Physlib.QuantumMechanics.ComplexAction.Dunkl.ComplexPathIntegralSignatures

end

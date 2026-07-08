/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction

/-!
# One spectral law behind Zeno relaxation, Misra time, the Compton clock and the Regge weight

The Zeno-limit Liouvillian eigenvalue (`ZenoLiouvillianSpectrum`, `λ = c_k Γ + i(u−w)`), the Misra internal-time
evolution (`MisraAgeFutureIncludedHerglotz.liouvilleEvolve = e^{−iλt}·f`), the entangled Compton clock
(`EntanglementReparametrization.deBroglieFrequency = E/ℏ`) and the complex Regge path weight
(`LeviCivita.ComplexReggeAction`, `e^{iS/ℏ}`) are the *same* object seen four ways: a **complex spectral rate `λ`**
whose evolution factor `exp(λt)` has

`‖exp(λt)‖ = exp(Re(λ)·t)` (`Complex.norm_exp`),

so the **real part is decay/damping** and the **imaginary part is unitary phase**. Dissipation ⟺ `Re λ < 0`.

* **§A — the shared spectral magnitude law.** `spectral_norm` (`‖exp(λt)‖ = exp(Re(λ)·t)`) and
 **`spectral_decays_iff`** (`‖exp λ‖ < 1 ↔ Re λ < 0`): the universal decay criterion.
* **§B — Zeno relaxation is the real part.** **`zeno_population_mode_decays`** — the population stripe eigenvalue
 `−Γ` (`zeno_stripe_population`) has `Re = −Γ < 0`, so the mode amplitude `e^{−Γt}` decays; its reciprocal `1/Γ`
 is the relaxation (entropic) timescale.
* **§C — Misra time and the Compton clock are the imaginary part.** **`misra_liouvilleEvolve_norm`**
 (`‖liouvilleEvolve t f lam‖ = ‖f lam‖`, the Misra evolution is unitary — `Re = 0`) and
 **`deBroglie_clock_unitary`** / **`entangled_clock_unitary`** (the de Broglie / entangled Compton frequency
 `E/ℏ` drives a pure phase `‖e^{−iωt}‖ = 1`): real spectrum ⟹ oscillation, the imaginary part `i(u−w)` of the
 Zeno eigenvalue.
* **§D — the Regge weight has the same Re/Im split.** **`regge_weight_decays`** — with imaginary defect (entropic
 Regge action `S_I > 0`) the path weight `‖e^{iS/ℏ}‖ = e^{−S_I/ℏ} < 1` decays (`Re = −S_I/ℏ < 0`), exactly the
 Zeno law; a real defect gives `‖·‖ = 1`, the unitary (Compton/Misra) limit.

Every theorem specializes the one exact identity `‖exp z‖ = exp(z.re)` to the four modules'
objects (reusing `liouvilleEvolve`, `deBroglieFrequency`, `reggeAction_complexActionWeight_norm`,
`zeno_stripe_population`). The unification is the observation that all four rates share this law; no new physics is
claimed beyond the exact `Complex.norm_exp` specializations.

## References

* `Lindblad.ZenoLiouvillianSpectrum`, `ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz`,
 `ComplexAction.ComptonClock.EntanglementReparametrization`, `ComplexAction.LeviCivita.ComplexReggeAction`.

No new axioms.
-/

set_option autoImplicit false

open Complex
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QFT.Wick.Consistency

@[expose] public section

namespace Physlib.QuantumMechanics.Lindblad.ZenoSpectralTimeUnification

/-! ## §A — the shared spectral magnitude law -/

/-- **The spectral evolution magnitude** `‖exp(λt)‖ = exp(Re(λ)·t)` — for a complex rate `λ` and real time `t`,
the magnitude of the evolution factor is set entirely by the real part of `λ` (`Complex.norm_exp`). -/
theorem spectral_norm (l : ℂ) (t : ℝ) :
    ‖Complex.exp (l * t)‖ = Real.exp (l.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **The universal decay criterion** `‖exp λ‖ < 1 ↔ Re λ < 0` — dissipation of the evolution factor is exactly
negativity of the real part of the spectral rate. -/
theorem spectral_decays_iff (l : ℂ) : ‖Complex.exp l‖ < 1 ↔ l.re < 0 := by
  rw [Complex.norm_exp, ← Real.exp_zero]
  exact Real.exp_lt_exp

/-! ## §B — Zeno relaxation is the real part -/

/-- **The Zeno population mode decays** `‖exp(−Γt)‖ < 1` for `Γ, t > 0` — the population stripe eigenvalue `−Γ`
(`ZenoLiouvillianSpectrum.zeno_stripe_population`) has real part `−Γ < 0`, so the dissipative mode amplitude
relaxes; the reciprocal `1/Γ` is the relaxation (entropic) timescale. -/
theorem zeno_population_mode_decays (Γ t : ℝ) (hΓ : 0 < Γ) (ht : 0 < t) :
    ‖Complex.exp ((-Γ : ℂ) * t)‖ < 1 := by
  rw [spectral_norm, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  simp only [Complex.neg_re, Complex.ofReal_re]
  nlinarith

/-! ## §C — Misra time and the Compton clock are the imaginary part -/

/-- **The Misra internal-time evolution is unitary** `‖liouvilleEvolve t f lam‖ = ‖f lam‖` — the Misra/Herglotz
Liouville evolution `e^{−iλt}·f` has a purely imaginary exponent (`Re(−iλt) = 0`), so it preserves magnitude: the
oscillation encoded in the imaginary part `i(u−w)` of the Zeno eigenvalue. -/
theorem misra_liouvilleEvolve_norm (t lam : ℝ) (f : ℝ → ℂ) :
    ‖liouvilleEvolve t f lam‖ = ‖f lam‖ := by
  unfold liouvilleEvolve
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- **The de Broglie / Compton clock is a unitary phase** `‖e^{−iωt}‖ = 1` with `ω = E/ℏ` — the Compton clock
frequency `deBroglieFrequency E ℏ` is a real spectral value, so its evolution is a pure phase (the imaginary,
oscillatory part), exactly the Misra `liouvilleEvolve` factor at `lam = ω`. -/
theorem deBroglie_clock_unitary (E ħ t : ℝ) :
    ‖Complex.exp (-Complex.I * (deBroglieFrequency E ħ : ℂ) * t)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- **The entangled Compton clock is still unitary** `‖e^{−i(cosh η·ω)t}‖ = 1` — the Schmidt-boosted de Broglie
frequency `cosh η·(E/ℏ)` (`entangled_einstein_clock`, the entangled Compton clock) is a larger real spectral
value, hence still a pure oscillatory phase with no damping. -/
theorem entangled_clock_unitary (η m c p ħ t : ℝ) :
    ‖Complex.exp (-Complex.I *
        (deBroglieFrequency (Real.cosh η * einsteinEnergy m c p) ħ : ℂ) * t)‖ = 1 :=
  deBroglie_clock_unitary (Real.cosh η * einsteinEnergy m c p) ħ t

/-! ## §D — the Regge weight has the same Re/Im split -/

/-- **The complex Regge path weight decays with the entropic action** `‖e^{iS/ℏ}‖ = e^{−S_I/ℏ} < 1` — an
imaginary defect (positive entropic Regge action `S_I/ℏ > 0`, `reggeAction_complexActionWeight_norm`) makes the
gravitational path weight dissipate, `Re = −S_I/ℏ < 0`: the *same* real-part-decay law as the Zeno mode
(`zeno_population_mode_decays`). A real defect gives `‖·‖ = 1`, the unitary Compton/Misra limit. -/
theorem regge_weight_decays {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) (ħ : ℝ)
    (hI : 0 < sorkinReggeAction area (fun b => (defect b).im) / ħ) :
    ‖complexActionWeight (complexReggeAction area defect).re
        (complexReggeAction area defect).im ħ‖ < 1 := by
  rw [reggeAction_complexActionWeight_norm, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  linarith

end Physlib.QuantumMechanics.Lindblad.ZenoSpectralTimeUnification

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Yukawa.CouplingIsolation
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

/-!
# The clock entropy rate threads the Nagao–Nielsen contour and the gravitational tensor

`clockFrequency_sets_entropyRate` (`Yukawa.CouplingIsolation`) showed the internal clock frequency `ω` sets the
entropy-production rate `Ṡ_I = (√2 ω₀/(2ℏv))·(ħω/c²)`. That rate is the production rate of the **imaginary
action** `S_I` — the single dissipative object that also appears in two other places in the repo:

* **the Nagao–Nielsen contour** — the complex path weight `e^{iS/ℏ}` (`S = S_R + iS_I`) has modulus
 `‖e^{iS/ℏ}‖ = e^{−S_I/ℏ}` (`NonHermitianComplexAction.EntropicDampingEquivalence.norm_nnPathWeight`): the imaginary action *is* the
 contour's survival/damping exponent;
* **the gravitational sector** — the complex Einstein equation `G + iΛ = κ(T + iS)` splits into the real
 Levi-Civita d'Alembert balance and the **imaginary entropic curvature `Λ = κS`**
 (`LeviCivita.GravitationalTensor.complexEinstein_real_is_dAlembert`): the entropic stress-energy sources the
 imaginary curvature.

So the clock-set entropy production `Ṡ_I` is the *rate* of the imaginary action `S_I = Ṡ_I·t` that (i) damps
the Nagao–Nielsen path weight and (ii) is the action of the entropic stress-energy `S` sourcing the
gravitational imaginary curvature `Λ = κS`. One dissipative sector — clock, contour, gravity.

* **§A — clock ⟶ contour.** `clockEntropy_nnContour_survival` (the NN survival factor with `S_I = Ṡ_I·t`),
 `clockMass_nnContour_survival` (`S_I` written through the Compton clock `ħω/c²`).
* **§B — the three-way bridge.** `clockEntropy_nagao_gravity` — given a clock-mass fermion and a complex
 Einstein solution: the clock entropy rate, the NN contour damping, and the gravitational entropic curvature
 `Λ = κS`, as one statement.

Proven: each face — `Ṡ_I = const·(ħω/c²)`, `‖e^{iS/ℏ}‖ = e^{−S_I/ℏ}`, `Λ = κS` — and that
they share the imaginary/entropic sector (the NN damping uses `S_I`, the gravity uses the entropic
stress-energy `S`). What is **not** formalized: the scalar-rate `Ṡ_I` ↔ matrix-source `S` reduction (the
imaginary action as a contraction of `S`); the bridge identifies the common dissipative sector, it does not
derive `S_I` from `S`.

## References

* `Physlib` (`Yukawa.CouplingIsolation.clockFrequency_sets_entropyRate`,
 `NonHermitianComplexAction.EntropicDampingEquivalence.norm_nnPathWeight`, `LeviCivita.GravitationalTensor.complexEinstein_real_is_dAlembert`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.Yukawa.CouplingIsolation
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockEntropyNagaoGravity

variable {ι : Type*}

/-! ## §A — the clock entropy rate damps the Nagao–Nielsen contour -/

/-- **[Clock entropy ⟶ NN contour survival]** the imaginary action accumulated from the clock-set entropy rate
over time `t`, `S_I = Ṡ_I·t`, is the Nagao–Nielsen contour damping exponent:
`‖e^{iS/ℏ}‖ = e^{−Ṡ_I·t/ℏ}`. The clock frequency sets the contour's decay. -/
theorem clockEntropy_nnContour_survival (S_R y ω₀ ℏ t ℏP : ℝ) :
    ‖nnPathWeight S_R (yukawaEntropyRate y ω₀ ℏ * t) ℏP‖
      = Real.exp (-(yukawaEntropyRate y ω₀ ℏ * t / ℏP)) :=
  norm_nnPathWeight S_R (yukawaEntropyRate y ω₀ ℏ * t) ℏP

/-- **[The NN survival written through the Compton clock]** for a clock-mass fermion
(`yukawaMass y v = comptonMass ω c ħ`), the contour survival decays at the clock-frequency-determined rate:
`‖e^{iS/ℏ}‖ = e^{−(√2 ω₀/(2ℏv))·(ħω/c²)·t/ℏ_P}`. -/
theorem clockMass_nnContour_survival (S_R y v ω c ħ ω₀ ℏ t ℏP : ℝ) (hv : v ≠ 0) (hℏ : ℏ ≠ 0)
    (h : yukawaMass y v = comptonMass ω c ħ) :
    ‖nnPathWeight S_R (yukawaEntropyRate y ω₀ ℏ * t) ℏP‖
      = Real.exp (-((Real.sqrt 2 * ω₀ / (2 * ℏ * v)) * comptonMass ω c ħ * t / ℏP)) := by
  rw [norm_nnPathWeight, clockFrequency_sets_entropyRate y v ω c ħ ω₀ ℏ hv hℏ h]

/-! ## §B — the three-way bridge: clock, contour, gravity -/

/-- **[One entropic sector across clock, contour, and gravity]** given a clock-mass fermion
(`yukawaMass y v = comptonMass ω c ħ`) and a complex Einstein solution, the same imaginary/entropic sector
appears as: the **clock**-set entropy rate `Ṡ_I = (√2 ω₀/(2ℏv))·(ħω/c²)`; the **Nagao–Nielsen contour**
damping `‖e^{iS/ℏ}‖ = e^{−Ṡ_I·t/ℏ_P}` with imaginary action `S_I = Ṡ_I·t`; and the **gravitational** entropic
curvature `Λ = κS` (the imaginary sector of the complex Einstein equation). -/
theorem clockEntropy_nagao_gravity (S_R y v ω c ħ ω₀ ℏ t ℏP : ℝ)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ) (κ : ℝ)
    (hv : v ≠ 0) (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0)
    (hclock : yukawaMass y v = comptonMass ω c ħ)
    (hgrav : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    yukawaEntropyRate y ω₀ ℏ = (Real.sqrt 2 * ω₀ / (2 * ℏ * v)) * comptonMass ω c ħ
      ∧ ‖nnPathWeight S_R (yukawaEntropyRate y ω₀ ℏ * t) ℏP‖
          = Real.exp (-(yukawaEntropyRate y ω₀ ℏ * t / ℏP))
      ∧ Λ = κ • S :=
  ⟨clockFrequency_sets_entropyRate y v ω c ħ ω₀ ℏ hv hℏ hclock,
    clockEntropy_nnContour_survival S_R y ω₀ ℏ t ℏP,
    (complexEinstein_real_is_dAlembert Ric scalarR g Λ T S κ hκ hgrav).2⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockEntropyNagaoGravity

end

end

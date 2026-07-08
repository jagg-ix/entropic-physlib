/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Special.RapidityVibracy
public import Physlib.QFT.Wick.Consistency
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Lipatov's effective action for Regge processes (QCD and gravity)

L. N. Lipatov, *Effective action for the Regge processes in QCD and in gravity* (Nucl. Phys. B Proc.
Suppl. **219–220** (2011) 78). At high energy `s ≫ −t` the gluons/gravitons are **reggeized**; the
scattering amplitude is organized by the Regge trajectory, the signature factor, and (for the Pomeron)
a `2+1`-dimensional reggeon field theory. This module formalizes the algebraic backbone of §2–§3, §5,
tying it to the repository rapidity / complex-action infrastructure.

* **§A — Regge kinematics and rapidity** (Eqs. 1, 10). The particle rapidity
 `y = ½ ln((E+p)/(E−p))` (`reggeRapidity`) is `½` the `RapidityVibracy.vibracy` of the light-cone
 components (`reggeRapidity_eq_half_vibracy`); the multi-Regge ordering `0 < y₁ < ⋯ < yₙ < ln s` is
 the strong rapidity separation.
* **§B — the Regge trajectory, signature factor, and Regge amplitude** (Eqs. 3–5, 7, 15). The linear
 trajectory `ω_p(t) = Δ − α′q²` (`reggeTrajectory`); the **complex signature factor**
 `ξ_p = −e^{−iπω} − p` (`signatureFactor`), whose **signature zeros** at the wrong-signature points
 (`signatureFactor_even_zero`, `signatureFactor_odd_zero`) are the Gribov signature structure;
 signature conservation `p = p₁p₂` closes on `{±1}` (`signature_closed`); the **Regge factor**
 `s^{ω}` composes multiplicatively (`reggeFactor_mul`), the multi-Regge factorization (Eq. 17).
* **§C — the Pomeron Green function and its trajectory** (Eqs. 3, 4, 11). The non-relativistic Pomeron
 Green function `G₀ = 1/(E + Δ − q²/2m)` (`pomeronGreen`) has its **pole exactly on the Regge
 trajectory** `ω = Δ − (1/2m)q²` with `α′ = 1/2m` (`pomeronGreen_pole_iff_trajectory`); the `t`-channel
 partial wave `f_ω = γ²/(ω − ω_p)` (`reggePole`) includes the trajectory as its `ω`-plane pole.

Proven: the rapidity/vibracy identity, the linear trajectory and its Green-function
pole, the signature-factor zeros and signature closure, and the Regge-factor composition. Interpretive:
the BFKL Hamiltonian / integrability (Eqs. 24–29), the Gribov reggeon Lagrangian (Eq. 12), and the
gauge-invariant effective action with kinematical constraints `∂_∓A_± = 0` (Eqs. 41–43) are the
field-theory content the amplitudes summarize; only their scalar/kinematic shadows appear here.

## References

* L. N. Lipatov, "Effective action for the Regge processes in QCD and in gravity", Nucl. Phys. B Proc.
 Suppl. **219–220** (2011) 78 [`Lipatov:2011ab`], §2–§3, §5, Eqs. (1)–(17), (40)–(43). Reuses
 `Physlib.Relativity.Special.RapidityVibracy` (`vibracy`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LipatovReggeEffectiveAction

open Physlib.Relativity.Special.RapidityVibracy
open Physlib.QFT.Wick.Consistency

/-! ## §A — Regge kinematics and rapidity -/

/-- **The particle rapidity** `y = ½ ln((E+p)/(E−p))` (Lipatov Eq. 10), classifying the reggeons by
rapidity in the multi-Regge kinematics. -/
noncomputable def reggeRapidity (E p : ℝ) : ℝ := (1 / 2) * Real.log ((E + p) / (E - p))

/-- **The rapidity is half the light-cone vibracy** `y = ½ vibracy(E+p, E−p)` (Eq. 10): the reggeon
rapidity is `½` the log-ratio of the light-cone energy components — a `RapidityVibracy.vibracy`. -/
theorem reggeRapidity_eq_half_vibracy (E p : ℝ) :
    reggeRapidity E p = (1 / 2) * vibracy (E + p) (E - p) := by
  simp only [reggeRapidity, vibracy]

/-! ## §B — the Regge trajectory, signature factor, and Regge amplitude -/

/-- **The linear Regge trajectory** `ω_p(t) = Δ − α′q²` (Lipatov Eq. 4), with intercept `Δ` and slope
`α′`. -/
noncomputable def reggeTrajectory (Δ αp q2 : ℝ) : ℝ := Δ - αp * q2

/-- **The signature factor** `ξ_p(t) = −e^{−iπω_p(t)} − p` (Lipatov Eq. 5): the complex phase of the
Regge amplitude, with signature `p = ±1`. -/
noncomputable def signatureFactor (p ω : ℝ) : ℂ :=
  -Complex.exp ((-(Real.pi * ω) : ℝ) * Complex.I) - (p : ℂ)

/-- **Signature conservation is closed on `{±1}`** (Lipatov Eq. 7): the Mandelstam-cut signature
`p = p₁p₂` of two reggeons is again `±1`. -/
theorem signature_closed {p1 p2 : ℝ} (h1 : p1 = 1 ∨ p1 = -1) (h2 : p2 = 1 ∨ p2 = -1) :
    p1 * p2 = 1 ∨ p1 * p2 = -1 := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- **The even-signature factor vanishes at `ω = 1`** (`ξ_{+1}(ω=1) = 0`): the Gribov signature
structure — the even-signature amplitude has a zero at odd trajectory values (a "nonsense" zero). -/
theorem signatureFactor_even_zero : signatureFactor 1 1 = 0 := by
  unfold signatureFactor
  have h : ((-(Real.pi * 1) : ℝ) : ℂ) * Complex.I = -((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **The odd-signature factor vanishes at `ω = 0`** (`ξ_{−1}(ω=0) = 0`): the odd-signature amplitude
has a zero at even trajectory values. -/
theorem signatureFactor_odd_zero : signatureFactor (-1) 0 = 0 := by
  unfold signatureFactor
  simp

/-- **The Regge factor** `s^{ω(t)}` (Lipatov Eq. 15): the power of the energy that dresses the Born
amplitude into the reggeized amplitude. -/
noncomputable def reggeFactor (s ω : ℝ) : ℝ := s ^ ω

/-- **The Regge factor composes multiplicatively** `s^{ω₁+ω₂} = s^{ω₁} s^{ω₂}` (Lipatov Eq. 17): the
multi-Regge factorization of the amplitude over rapidity-ordered reggeon exchanges. -/
theorem reggeFactor_mul (s ω1 ω2 : ℝ) (hs : 0 < s) :
    reggeFactor s (ω1 + ω2) = reggeFactor s ω1 * reggeFactor s ω2 := by
  unfold reggeFactor; exact Real.rpow_add hs ω1 ω2

/-! ## §C — the Pomeron Green function and its trajectory -/

/-- **The `t`-channel partial wave** `f_ω(t) = γ²/(ω − ω_p)` (Lipatov Eq. 3): the Regge pole in the
complex angular-momentum (`ω`) plane, at `ω = ω_p(t)`. -/
noncomputable def reggePole (γ2 ω ωp : ℝ) : ℝ := γ2 / (ω - ωp)

/-- **The Pomeron Green function** `G₀ = 1/(E + Δ − q²/2m)` (Lipatov Eq. 11), the non-relativistic
reggeon propagator with `E = −ω`, `α′ = 1/2m`. -/
noncomputable def pomeronGreen (E Δ q2 m : ℝ) : ℝ := 1 / (E + Δ - q2 / (2 * m))

/-- **The Pomeron Green function pole is the Regge trajectory** (Lipatov Eqs. 11 ↔ 4): with `E = −ω`,
the propagator `G₀ = 1/(E + Δ − q²/2m)` is singular exactly when `ω = Δ − (1/2m)q² =
reggeTrajectory Δ (1/2m) q²` — the Pomeron trajectory with slope `α′ = 1/2m`. -/
theorem pomeronGreen_pole_iff_trajectory (E Δ q2 m ω : ℝ) (hE : E = -ω) :
    E + Δ - q2 / (2 * m) = 0 ↔ ω = reggeTrajectory Δ (1 / (2 * m)) q2 := by
  subst hE
  unfold reggeTrajectory
  rw [show q2 / (2 * m) = (1 / (2 * m)) * q2 from by ring]
  constructor <;> intro h <;> linarith

/-! ## §D — bridges to the complex-action / entropic hub -/

/-- **The Regge factor is exponential in the total rapidity** `s^ω = exp(ω · ln s)` for `s > 0`
(Lipatov): with the total rapidity `Y = ln s`, the reggeized amplitude grows as `e^{ωY}` — the same
`exp` form as the entropic weight `‖complexActionWeight‖ = exp(−S_I/ℏ)`, now with `ω Y` in the
exponent. -/
theorem reggeFactor_eq_exp (s ω : ℝ) (hs : 0 < s) :
    reggeFactor s ω = Real.exp (ω * Real.log s) := by
  unfold reggeFactor
  rw [Real.rpow_def_of_pos hs, mul_comm]

/-- **The signature phase** `e^{−iπω}` — the oscillatory, parity-odd part of the signature factor
`ξ_p = −e^{−iπω} − p`. -/
noncomputable def signaturePhase (ω : ℝ) : ℂ := Complex.exp ((-(Real.pi * ω) : ℝ) * Complex.I)

/-- **The signature factor splits into phase and signature** `ξ_p = −(e^{−iπω}) − p`. -/
theorem signatureFactor_eq_phase (p ω : ℝ) :
    signatureFactor p ω = -signaturePhase ω - (p : ℂ) := rfl

/-- **The signature phase has unit modulus** `‖e^{−iπω}‖ = 1`: the parity-odd Regge phase is a pure
phase (no absorption on its own). -/
theorem signaturePhase_norm (ω : ℝ) : ‖signaturePhase ω‖ = 1 := by
  unfold signaturePhase
  rw [Complex.norm_exp]
  simp

/-- **The Regge signature phase is a complex-action weight** (Lipatov ↔ `Wick.Consistency`): the phase
`e^{−iπω}` of the signature factor is exactly the pure-phase `complexActionWeight` with real action
`S_R = −πω·ℏ` and **zero** imaginary action. So the reggeized amplitude's phase lives in the
complex-action arc, and its unit modulus (`signaturePhase_norm`) is the `S_I = 0` case of the entropic
damping `‖w‖ = exp(−S_I/ℏ)`. -/
theorem signaturePhase_eq_complexActionWeight (ω hbar : ℝ) (hbar_ne : hbar ≠ 0) :
    signaturePhase ω = complexActionWeight (-(Real.pi * ω) * hbar) 0 hbar := by
  unfold signaturePhase complexActionWeight
  congr 1
  rw [show (-(Real.pi * ω) * hbar) / hbar = -(Real.pi * ω) from by field_simp,
    show (0 : ℝ) / hbar = 0 from by simp]
  push_cast; ring

end Physlib.QuantumMechanics.ComplexAction.LipatovReggeEffectiveAction

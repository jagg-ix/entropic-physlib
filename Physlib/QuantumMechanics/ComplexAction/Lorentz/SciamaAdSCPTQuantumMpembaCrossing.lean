/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTPetzMonotonicityOperator
public import Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
meta import Zil

/-!
# The quantum Mpemba crossing in the dissipative sector

The **quantum Mpemba effect** — a state initially *farther* from equilibrium relaxing *faster* — lives
exactly in the arc's dissipative sector, and the repo already carries its lane (the "viscosity/Mpemba/Cameron
lane" of `EntropicTime.GravitySynthesis`: `cameronWeight`, damped enstrophy) and its constraints (the
Liouvillian spectral clocks of `Lindblad.ThreeClockReversibilitySpectrum`; the operator Petz monotonicity of
`SciamaAdSCPTPetzMonotonicityOperator`).  What was missing is the defining phenomenon — **the crossing** —
supplied here exactly:

* `mpemba_crossing` — the anomalous overtaking, with the **explicit crossing time**
  `t* = log(a/b)/(λ₂−λ₃)`: a state relaxing on a *faster* Liouvillian mode (`a·e^{λ₃t}`, `λ₃ < λ₂ < 0` —
  its slow-mode overlap vanishes, the Mpemba mechanism) overtakes a state on the slow mode (`b·e^{λ₂t}`) for
  every `t > t*` — **even when it starts farther** (`a > b` is allowed; it only moves `t*` later).
* `mpemba_rate_is_spectral` — the relaxation rate is the real part of the occupied Liouvillian mode
  (`flow_norm_from_re`, `‖e^{λt}‖ = e^{Re λ·t}`): the Mpemba ordering is an ordering of *occupied* spectral
  gaps, the three-clock decomposition's entropic component.
* `mpemba_consistent_with_petz` — **no monotonicity is violated**: under each relaxation step (a CPTP
  channel) *both* states' relative entropies to the stationary state decrease (`qRelativeEnt_DPI`, twice).
  The Mpemba anomaly is a crossing *between* trajectories, never a violation *along* one — the operator
  data-processing inequality and the Mpemba effect coexist exactly.
* `cameron_is_kuiken` — the existing Mpemba lane's Cameron suppression weight **is** the arc's
  Kuiken/entropic damping (`e^{−τ} = kuikenWeight 1 τ`): the lane sits in the same imaginary-action sector as
  the NS viscosity, the decoherence visibility, and the confinement weight.

`quantum_mpemba_synthesis` bundles the four with the dissipative-sector sign
(`entropic_generator_flow_contracts`): the quantum Mpemba effect is an ordering anomaly **between**
individually-monotone trajectories in the `Re λ < 0` sector shared by the Navier–Stokes viscosity and the
decoherence arc, with mechanism (slow-mode orthogonality), rate (spectral), and crossing time all exact.

Honest scope: the two-mode exponential model is the exact finite carrier of the Lindblad-spectral Mpemba
mechanism (Carollo–Lasanta–Lesanovsky); the entanglement-asymmetry version and the mode-overlap dynamics for
specific models are cited context.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTPetzMonotonicityOperator
open Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

/-! ## §1. The crossing -/

/-- **The Mpemba crossing time** `t* = log(a/b)/(λ₂−λ₃)` — after `t*`, the fast-mode state (initial amplitude
`a`, rate `λ₃`) is strictly below the slow-mode state (amplitude `b`, rate `λ₂ > λ₃`). -/
def mpembaCrossingTime (a b lam2 lam3 : ℝ) : ℝ := Real.log (a / b) / (lam2 - lam3)

/-- **[The quantum Mpemba crossing]** — a state relaxing on a faster Liouvillian mode (`a·e^{λ₃t}`,
`λ₃ < λ₂`: its slow-mode overlap vanishes) overtakes the slow-mode state (`b·e^{λ₂t}`) for every
`t > t* = log(a/b)/(λ₂−λ₃)` — **even when it starts farther** (`a > b` allowed; it only delays `t*`): the
anomalous relaxation ordering, with the crossing time explicit. -/
theorem mpemba_crossing {a b lam2 lam3 : ℝ} (ha : 0 < a) (hb : 0 < b) (hlam : lam3 < lam2)
    {t : ℝ} (ht : mpembaCrossingTime a b lam2 lam3 < t) :
    a * Real.exp (lam3 * t) < b * Real.exp (lam2 * t) := by
  have hab : a * Real.exp (lam3 * t) = Real.exp (Real.log a + lam3 * t) := by
    rw [Real.exp_add, Real.exp_log ha]
  have hbb : b * Real.exp (lam2 * t) = Real.exp (Real.log b + lam2 * t) := by
    rw [Real.exp_add, Real.exp_log hb]
  rw [hab, hbb, Real.exp_lt_exp]
  have hpos : 0 < lam2 - lam3 := sub_pos.mpr hlam
  have ht' : Real.log (a / b) < t * (lam2 - lam3) :=
    (div_lt_iff₀ hpos).mp ht
  rw [Real.log_div ha.ne' hb.ne'] at ht'
  linarith

/-! ## §2. The rate is spectral -/

/-- **[The Mpemba rate is the occupied spectral gap]** `‖e^{λt}‖ = e^{Re λ·t}` — the relaxation rate of each
trajectory is the real part of its slowest *occupied* Liouvillian mode: the Mpemba ordering is an ordering of
occupied spectral gaps (the three-clock entropic component). -/
theorem mpemba_rate_is_spectral (l : ℂ) (t : ℝ) :
    ‖Complex.exp (l * t)‖ = Real.exp (l.re * t) :=
  flow_norm_from_re l t

/-! ## §3. No monotonicity is violated -/

/-- **[The Mpemba effect coexists with operator Petz monotonicity]** — under each relaxation step (a CPTP
channel `Φ`), *both* states' relative entropies to the stationary reference decrease.  The Mpemba anomaly is
a crossing *between* trajectories, never a violation *along* one. -/
theorem mpemba_consistent_with_petz {d₁ d₂ : Type*}
    [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρA ρB σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    qRelativeEnt (Φ ρA) (Φ σ) ≤ qRelativeEnt ρA σ
      ∧ qRelativeEnt (Φ ρB) (Φ σ) ≤ qRelativeEnt ρB σ :=
  ⟨qRelativeEnt_DPI ρA σ Φ, qRelativeEnt_DPI ρB σ Φ⟩

/-! ## §4. The lane sits in the arc's imaginary-action sector -/

/-- **[The Cameron weight is the Kuiken/entropic damping]** `e^{−τ} = kuikenWeight 1 τ` — the existing
viscosity/Mpemba lane's suppression weight is the arc's entropic damping: the Mpemba lane lives in the same
imaginary-action sector as the NS viscosity, the decoherence visibility, and the confinement weight. -/
theorem cameron_is_kuiken (tau : ℝ) : cameronWeight tau = kuikenWeight 1 tau := by
  simp [cameronWeight, kuikenWeight]

/-! ## §5. The synthesis -/

/-- **[The quantum Mpemba effect, located in the arc]** — **(i)** the crossing: the fast-mode state overtakes
after the explicit `t*`, even starting farther; **(ii)** the rate is the occupied spectral gap; **(iii)** no
monotonicity is violated: both trajectories' relative entropies decrease under every channel step (operator
Petz); **(iv)** the lane's damping is the arc's Kuiken weight; **(v)** the sector is dissipative:
`Re λ < 0` flows strictly contract.  The quantum Mpemba effect is an ordering anomaly **between**
individually-monotone trajectories in the dissipative sector shared by the Navier–Stokes viscosity and the
decoherence arc. -/
theorem quantum_mpemba_synthesis {a b lam2 lam3 : ℝ} (ha : 0 < a) (hb : 0 < b) (hlam : lam3 < lam2)
    {t : ℝ} (ht : mpembaCrossingTime a b lam2 lam3 < t)
    {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρA ρB σ : MState d₁) (Φ : CPTPMap d₁ d₂)
    (l : ℂ) (s : ℝ) (hl : l.re < 0) (hs : 0 < s) (tau : ℝ) :
    a * Real.exp (lam3 * t) < b * Real.exp (lam2 * t)
      ∧ ‖Complex.exp (l * s)‖ = Real.exp (l.re * s)
      ∧ (qRelativeEnt (Φ ρA) (Φ σ) ≤ qRelativeEnt ρA σ
          ∧ qRelativeEnt (Φ ρB) (Φ σ) ≤ qRelativeEnt ρB σ)
      ∧ cameronWeight tau = kuikenWeight 1 tau
      ∧ ‖Complex.exp (l * s)‖ < 1 :=
  ⟨mpemba_crossing ha hb hlam ht,
    mpemba_rate_is_spectral l s,
    mpemba_consistent_with_petz ρA ρB σ Φ,
    cameron_is_kuiken tau,
    entropic_generator_flow_contracts l s hl hs⟩

/-! ## §G. The Gaussian-envelope crossing (dilation-decoherence shape) -/

/-- **[The Mpemba crossing for Gaussian envelopes]** — time-dilation decoherence decays *Gaussianly*,
`V = e^{−(Γt)²}`, not exponentially.  The crossing framework transfers exactly under `u = t²`: for
`Γ₂ < Γ₃` (both `≥ 0`), `a·e^{−(Γ₃t)²} < b·e^{−(Γ₂t)²}` for every `t` with
`t² > mpembaCrossingTime a b (−Γ₂²) (−Γ₃²)` — the fast-decohering (heavier/more-modes) branch drops below
even starting larger, in squared time. -/
theorem gaussian_mpemba_crossing {a b Γ₂ Γ₃ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h0 : 0 ≤ Γ₂) (hΓ : Γ₂ < Γ₃)
    {t : ℝ} (ht : mpembaCrossingTime a b (-Γ₂ ^ 2) (-Γ₃ ^ 2) < t ^ 2) :
    a * Real.exp (-(Γ₃ * t) ^ 2) < b * Real.exp (-(Γ₂ * t) ^ 2) := by
  have hlam : -Γ₃ ^ 2 < -Γ₂ ^ 2 := by nlinarith
  have hcr := mpemba_crossing ha hb hlam ht
  have e3 : -(Γ₃ * t) ^ 2 = -Γ₃ ^ 2 * t ^ 2 := by ring
  have e2 : -(Γ₂ * t) ^ 2 = -Γ₂ ^ 2 * t ^ 2 := by ring
  rwa [e3, e2]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing.mpemba_crossing where
  formalizes @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  supported_by @ "paper:carollo-lasanta-lesanovsky-2021-exponentially-accelerated-approach-to-stationarity",
  caveat @ "epistemic:two-mode-exponential-model-the-exact-finite-carrier-of-the-lindblad-spectral-mpemba-mechanism"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing.mpemba_consistent_with_petz where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTPetzMonotonicityOperator.qRelativeEnt_DPI",
  formalizes @ "claim:the-quantum-mpemba-anomaly-is-a-crossing-between-trajectories-never-a-violation-of-per-trajectory-data-processing-monotonicity",
  requires @ "claim:the-umegaki-quantum-relative-entropy-contracts-under-every-cptp-channel-the-operator-petz-uhlmann-data-processing-inequality",
  caveat @ "epistemic:per-step-channel-monotonicity-the-continuous-time-semigroup-statement-is-the-cited-counterpart"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing.quantum_mpemba_synthesis where
  formalizes @ "claim:the-quantum-mpemba-effect-is-an-ordering-anomaly-between-monotone-trajectories-in-the-dissipative-sector-shared-by-viscosity-and-decoherence",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.cameronWeight",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.flow_norm_from_re",
  caveat @ "epistemic:the-slow-mode-overlap-dynamics-for-specific-models-and-the-entanglement-asymmetry-version-are-cited-context"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing.gaussian_mpemba_crossing where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing.mpemba_crossing",
  formalizes @ "claim:the-mpemba-crossing-transfers-exactly-to-gaussian-envelopes-under-squared-time-the-dilation-decoherence-shape",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  caveat @ "epistemic:gaussian-short-time-shape-is-the-cited-pikovski-thermal-composite-result"

/- ZIL-END -/

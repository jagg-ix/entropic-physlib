/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.LorentzianPropagator
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

/-!
# The Wigner–Dunkl complex path integral consumes the Nagao–Nielsen `(p,q)` propagator and entropy production

Feeds the Wigner–Dunkl complex/Lorentzian path integral (`Dunkl.LorentzianPropagator`) the two
operational halves of the Nagao–Nielsen complex-action path integral already on this branch:

* the **phase-space `(p,q)` momentum propagator** (`PathIntegral.MomentumPathIntegral`): the Dunkl oscillator
  Hamiltonian `H = p²/2m + V` written in Nagao–Nielsen phase-space form, the canonical momentum
  `p = ∂L/∂q̇ = m q̇` (Eq. 3.10), the saddle reduction `L(p,q̇)|_{p=mq̇} = L(q̇)` (Eq. 3.15), and the
  momentum Gaussian integral (Eq. 3.17) with its convergence condition `Im m > 0` — the reversible
  half of the propagator;
* the **entropy production** (`FeynmanKac` entropic-time correspondence): the imaginary action
  `S_I = t·H_I` per unit `ℏ` is the produced entropy `τ_ent = t·H_I/ℏ`, the modulus of the complex
  propagator is `e^{−τ_ent}`, this entropy is non-negative (the second law), and it equals both the
  Nagao–Nielsen entropic time `V·T` and the Feynman–Kac weight — the irreversible half.

So the Wigner–Dunkl complex propagator `‖·‖·e^{i·phase}` factors operationally into the Nagao–Nielsen
reversible `(p,q)` phase and the irreversible entropy-production damping.

* **§A** `dunkl_phaseLagrangian_saddle`, `dunkl_momentum_relation` — the `(p,q)` saddle and `p = mq̇`.
* **§B** `dunkl_momentum_converges_iff`, `dunkl_momentum_gaussian` — the momentum integral (Eq. 3.17) and
  the `Im m > 0` Feynman–Kac convergence.
* **§C** `dunklEntropyProduction`, `dunklOsc_propagator_norm_eq_entropy`, `dunkl_entropy_production_nonneg`
  (second law), `dunkl_entropy_is_entropic_time`, `dunkl_propagator_norm_eq_fk_weight`.
* **§D** `dunkl_zero_entropy_iff_reversible` — zero entropy production ⟺ the reversible (`H_I = 0`) point.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.PhaseSpaceEntropy

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open scoped Real

/-! ## §A — the Nagao–Nielsen `(p,q)` phase space for the Dunkl oscillator -/

/-- **The Wigner–Dunkl harmonic potential** `V(x) = ½ m ω² x²` (Junker §3, the oscillator interaction). -/
noncomputable def dunklOscPotential (m ω x : ℂ) : ℂ := (1 / 2) * m * ω ^ 2 * x ^ 2

/-- **[Consume NN Eq. 3.15] The Dunkl oscillator's phase-space Lagrangian reduces to the configuration
Lagrangian at the saddle `p = m q̇`.** `L(p, q̇)|_{p = mq̇} = ½ m q̇² − V` — the momentum is integrated out
at its stationary point, the first half of the Nagao–Nielsen `(p,q)` path integral. -/
theorem dunkl_phaseLagrangian_saddle (m ω x qdot : ℂ) (hm : m ≠ 0) :
    phaseLagrangian m (m * qdot) qdot (dunklOscPotential m ω x)
      = configLagrangian m qdot (dunklOscPotential m ω x) :=
  phaseLagrangian_at_saddle m qdot (dunklOscPotential m ω x) hm

/-- **[Consume NN Eq. 3.10] The Dunkl canonical momentum** `p = ∂L/∂q̇ = m q̇`. The configuration
Lagrangian of the Dunkl oscillator has `q̇`-derivative `m q̇` — the momentum conjugate to position, the
classical shadow of the Dunkl momentum operator `P = (ℏ/i) D_ν`. -/
theorem dunkl_momentum_relation (m ω x qdot : ℂ) :
    HasDerivAt (fun q' => configLagrangian m q' (dunklOscPotential m ω x)) (m * qdot) qdot :=
  momentum_relation m qdot (dunklOscPotential m ω x)

/-! ## §B — the Dunkl momentum Gaussian integral and the `Im m > 0` convergence (NN Eq. 3.17) -/

/-- **[Consume NN Eq. 3.1/3.17] The Dunkl momentum path integral converges iff `Im m > 0`.** The
phase-space momentum integration is a complex Gaussian whose coefficient has positive real part exactly
when the imaginary mass is positive — the Nagao–Nielsen "sensible boson" / Feynman–Kac damping condition
that makes the Wigner–Dunkl complex path integral well-defined. -/
theorem dunkl_momentum_converges_iff (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  momentum_integral_converges_iff m hℏ hdt hm

/-- **[Consume NN Eq. 3.17] The Dunkl saddle-point momentum integral** `∫ e^{−b(p−mq̇)²} dp =
(π/b)^{1/2}`, evaluated under the convergence `Im m > 0`. This is the reversible Gaussian factor of each
time slice of the Wigner–Dunkl complex path integral. -/
theorem dunkl_momentum_gaussian (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm_I : 0 < m.im) :
    ∫ u : ℝ, Complex.exp (-(momentumGaussianCoeff m ℏ dt) * (u : ℂ) ^ 2)
      = (↑π / momentumGaussianCoeff m ℏ dt) ^ (1 / 2 : ℂ) :=
  momentum_gaussian_integral m hℏ hdt hm_I

/-! ## §C — entropy production: the irreversible half of the complex propagator -/

/-- **The entropy produced by the Wigner–Dunkl complex propagator** over time `t`: the imaginary action
per unit `ℏ`, `τ_ent = t·H_I/ℏ` (Nagao–Nielsen entropic time). -/
noncomputable def dunklEntropyProduction (H : ComplexHamiltonian) (t ℏ : ℝ) : ℝ := t * H.H_I / ℏ

/-- **[Bridge] The modulus of the complex propagator is `e^{−(entropy produced)}`.**
`‖lorentzianPropagator H t ℏ‖ = e^{−τ_ent}` with `τ_ent = t·H_I/ℏ` — the irreversible damping of the
Wigner–Dunkl complex path integral is precisely the exponential of the produced entropy. -/
theorem dunklOsc_propagator_norm_eq_entropy (H : ComplexHamiltonian) (t ℏ : ℝ) :
    ‖lorentzianPropagator H t ℏ‖ = Real.exp (-(dunklEntropyProduction H t ℏ)) := by
  rw [lorentzianPropagator_norm_is_damping, dunklEntropyProduction]

/-- **[Second law] The entropy production is non-negative** for `t ≥ 0`, `ℏ > 0`: `τ_ent ≥ 0`, since the
dissipative part `H_I ≥ 0`. The Wigner–Dunkl complex path integral never decreases entropy forward in
time — it is a genuine (sub-unitary) irreversible process. -/
theorem dunkl_entropy_production_nonneg (H : ComplexHamiltonian) (t ℏ : ℝ) (ht : 0 ≤ t) (hℏ : 0 < ℏ) :
    0 ≤ dunklEntropyProduction H t ℏ :=
  div_nonneg (mul_nonneg ht H.H_I_nonneg) hℏ.le

/-- **[Consume NN entropic time] The entropy production is the Nagao–Nielsen entropic time** `τ_ent =
V·T` whenever the imaginary action matches `t·H_I = ℏ·V·T` (`FeynmanKac.entropic_time_is_cumulative_
potential`): the dissipative Hamiltonian part `H_I` is the entropy-production rate, `t` the elapsed
(imaginary) time. -/
theorem dunkl_entropy_is_entropic_time (H : ComplexHamiltonian) (t ℏ V T : ℝ) (hℏ : 0 < ℏ)
    (h : t * H.H_I = V * T * ℏ) : dunklEntropyProduction H t ℏ = V * T := by
  unfold dunklEntropyProduction; rw [h]; field_simp

/-- **[Consume FK correspondence] The complex propagator's modulus is the Feynman–Kac weight.**
`‖lorentzianPropagator H t ℏ‖ = feynman_kac_weight (·↦V) T ()` under `t·H_I = ℏ·V·T` — the irreversible
half of the Wigner–Dunkl complex path integral is exactly the (real) Feynman–Kac/entropic damping of the
Euclidean Dunkl process. -/
theorem dunkl_propagator_norm_eq_fk_weight (H : ComplexHamiltonian) (t ℏ V T : ℝ) (hℏ : 0 < ℏ)
    (h : t * H.H_I = V * T * ℏ) :
    ‖lorentzianPropagator H t ℏ‖ = feynman_kac_weight (fun _ : Unit => V) T () := by
  rw [dunklOsc_propagator_norm_eq_entropy, dunkl_entropy_is_entropic_time H t ℏ V T hℏ h,
    constant_potential_fk_weight]

/-! ## §D — the reversible / irreversible split -/

/-- **Zero entropy production ⟺ the reversible point.** For `t > 0`, `ℏ > 0` the produced entropy
vanishes iff `H_I = 0` — the reversible (unitary, Minkowskian) Dunkl evolution where the complex path
integral is the pure Nagao–Nielsen `(p,q)` phase with no Feynman–Kac damping
(`Dunkl.LorentzianPropagator.dunklOsc_reversible_unitary`). -/
theorem dunkl_zero_entropy_iff_reversible (H : ComplexHamiltonian) (t ℏ : ℝ) (ht : 0 < t) (hℏ : 0 < ℏ) :
    dunklEntropyProduction H t ℏ = 0 ↔ H.H_I = 0 := by
  unfold dunklEntropyProduction
  rw [div_eq_zero_iff, mul_eq_zero]
  constructor
  · rintro (h | h)
    · rcases h with h | h
      · exact absurd h ht.ne'
      · exact h
    · exact absurd h hℏ.ne'
  · intro h; exact Or.inl (Or.inr h)

end Physlib.QuantumMechanics.ComplexAction.Dunkl.PhaseSpaceEntropy

end

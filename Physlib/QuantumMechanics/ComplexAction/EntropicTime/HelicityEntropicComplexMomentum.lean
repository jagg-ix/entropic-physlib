/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AcharyaCanonicalSpinHelicity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

/-!
# The helicity, the Nagao–Nielsen complex momentum, and the entropic proper time

This file links the **helicity** of `AcharyaCanonicalSpinHelicity` (Acharya–Sudarshan 1960 §2) to the
two pillars of this development: the **Nagao–Nielsen complex momentum** (`PathIntegral.MomentumPathIntegral`) and
the **entropic proper time** (`Bogoliubov.EntropicTime` / `EntropicTime.MetricCommonRootEntropicTime`).

## The helicity momentum is the Bogoliubov off-diagonal `ξ`

The helicity `h = S·p̂ = ½σ·p̂` has `(σ·p)² = |p|²·1`, so its momentum scale is `|p| = √(p·p)`
(`helicityMomentum`). This `|p|` is exactly the **Bogoliubov off-diagonal frequency `ξ`**: with the
gap `Δ = mc²`, the on-shell energy is

 `E = √(|p|² + Δ²) = bogoliubovEnergy |p| Δ` (`helicity_bogoliubov_energy`),

the Einstein dispersion `E² = (pc)² + (mc²)²`. So the helicity momentum drives the Bogoliubov
quasiparticle structure.

## The entropic proper time of the helicity sector

The Bogoliubov quasiparticle occupation is `v² = (1 − |p|/E)/2` (the lower-spinor / negative-energy
weight), and the **entropic proper time** is its binary entropy:

 `τ_ent = binEntropy((1 − |p|/E)/2)` (`helicity_entropicTime`).

So the helicity momentum `|p|` determines the entropic proper time. It **vanishes** exactly at the
metric-luminal limit `|p|/E = ±1` (massless / `Δ → 0`) — the reversible helicity
(`helicity_entropicTime_zero_iff_luminal`).

## The Nagao–Nielsen complex momentum

When the mass is the Nagao–Nielsen **complex mass** `m = m_R + i m_I`, the momentum Gaussian (the
complex-action / Feynman–Kac weight) converges exactly when `Im m > 0`:

 `0 < Re(momentumGaussianCoeff m ℏ Δt) ⟺ 0 < Im m` (`helicity_complex_momentum_converges`),

the entropic-damping condition `e^{−S_I/ℏ}` of the complex action. So the helicity sector's complex
momentum is convergent precisely under the same positivity that makes the entropic proper time
well-defined.

## Scope

The link is exact: `helicityMomentum = ξ` (the off-diagonal), the dispersion, the entropic-time
formula, and the complex-momentum convergence are all proved/reused. It identifies the *operational*
correspondence (helicity momentum ↔ Bogoliubov `ξ`); it does not assert that the helicity *operator*
and the Bogoliubov *quasiparticle* are the same object beyond sharing the momentum scale `|p|` and the
dispersion `E = √(|p|²+Δ²)`.

## References

* R. Acharya, E. C. G. Sudarshan, J. Math. Phys. **1** (1960) 532, §2. This development:
 `AcharyaCanonicalSpinHelicity`, `Bogoliubov.EntropicTime`, `EntropicTime.MetricCommonRootEntropicTime`,
 `PathIntegral.MomentumPathIntegral`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Complex

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum

open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
open Physlib.QuantumMechanics.ComplexAction.AcharyaCanonicalSpinHelicity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

/-! ## §A — the helicity momentum is the Bogoliubov off-diagonal `ξ = |p|` -/

/-- **The helicity momentum** `|p| = √(p·p)` — the scale of the helicity `h = S·p̂`, equal to the
Bogoliubov off-diagonal frequency `ξ`. -/
def helicityMomentum (p : Fin 3 → ℝ) : ℝ := Real.sqrt (dotR p p)

/-- **`p·p ≥ 0`** (a Euclidean norm-square). -/
theorem dotR_self_nonneg (p : Fin 3 → ℝ) : 0 ≤ dotR p p := by
  unfold dotR
  have h0 := mul_self_nonneg (p 0)
  have h1 := mul_self_nonneg (p 1)
  have h2 := mul_self_nonneg (p 2)
  linarith

/-- **`|p|² = p·p`** — the helicity momentum squares to the dot product. -/
theorem helicityMomentum_sq (p : Fin 3 → ℝ) : helicityMomentum p ^ 2 = dotR p p :=
  Real.sq_sqrt (dotR_self_nonneg p)

/-- **The helicity projection in terms of the helicity momentum**: `(S·p)² = ¼|p|²·1`. -/
theorem helicityProj_sq_momentum (p : Fin 3 → ℝ) :
    helicityProj p * helicityProj p = ((1 / 4 * helicityMomentum p ^ 2 : ℝ) : ℂ) • 1 := by
  rw [helicityProj_sq, helicityMomentum_sq]

/-! ## §B — the dispersion `E = √(|p|² + Δ²)` -/

/-- **The helicity dispersion is the Bogoliubov energy**: with gap `Δ = mc²`, the on-shell energy is
`E = √(|p|² + Δ²) = bogoliubovEnergy |p| Δ` — the Einstein relation `E² = (pc)² + (mc²)²`. -/
theorem helicity_bogoliubov_energy (p : Fin 3 → ℝ) (Δ : ℝ) :
    bogoliubovEnergy (helicityMomentum p) Δ = Real.sqrt (dotR p p + Δ ^ 2) := by
  rw [bogoliubovEnergy, helicityMomentum_sq]

/-! ## §C — the entropic proper time of the helicity sector -/

/-- **The entropic proper time from the helicity momentum** `τ_ent = binEntropy((1 − |p|/E)/2)`: the
helicity momentum `|p|` determines the Bogoliubov occupation `v² = (1 − |p|/E)/2` and hence the
entropic proper time. -/
theorem helicity_entropicTime (p : Fin 3 → ℝ) (Δ : ℝ) :
    bogoliubovEntropicTime (helicityMomentum p) Δ
      = Real.binEntropy ((1 - helicityMomentum p / bogoliubovEnergy (helicityMomentum p) Δ) / 2) :=
  entropicTime_eq_binEntropy_velocity (helicityMomentum p) Δ

/-- **The helicity entropic time vanishes at the luminal limit** `τ_ent = 0 ⟺ |p|/E = ±1`: the
reversible helicity is the metric-null (massless / `Δ → 0`) one — the `45°` light cone. -/
theorem helicity_entropicTime_zero_iff_luminal (p : Fin 3 → ℝ) (Δ : ℝ) :
    bogoliubovEntropicTime (helicityMomentum p) Δ = 0
      ↔ helicityMomentum p / bogoliubovEnergy (helicityMomentum p) Δ = 1
        ∨ helicityMomentum p / bogoliubovEnergy (helicityMomentum p) Δ = -1 :=
  entropicTime_zero_iff_metric_luminal (helicityMomentum p) Δ

/-! ## §D — the Nagao–Nielsen complex momentum -/

/-- **The helicity sector's Nagao–Nielsen complex momentum converges iff `Im m > 0`**: with the
complex mass `m = m_R + i m_I` (the gap `Δ = mc²` complexified), the momentum Gaussian — the
complex-action / Feynman–Kac weight — has positive real part exactly when the imaginary mass is
positive, the entropic-damping condition `e^{−S_I/ℏ}`. -/
theorem helicity_complex_momentum_converges (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt)
    (hm : m ≠ 0) : 0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  momentum_integral_converges_iff m hℏ hdt hm

/-! ## §E — the bundled link -/

/-- **The helicity ↔ complex-momentum ↔ entropic-proper-time link.** For a momentum `p`, gap `Δ`,
complex mass `m ≠ 0`, and `ℏ, Δt > 0`:

* **(helicity ↔ Bogoliubov)** the helicity dispersion is the Bogoliubov energy `E = √(|p|² + Δ²)`;
* **(entropic proper time)** the helicity sector's entropic proper time is
  `τ_ent = binEntropy((1 − |p|/E)/2)`;
* **(Nagao–Nielsen complex momentum)** the complex momentum converges iff `Im m > 0` — the entropic
  damping of the complex action. -/
theorem helicity_complexMomentum_entropicTime_link (p : Fin 3 → ℝ) (Δ : ℝ) (m : ℂ)
    {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    bogoliubovEnergy (helicityMomentum p) Δ = Real.sqrt (dotR p p + Δ ^ 2)
      ∧ bogoliubovEntropicTime (helicityMomentum p) Δ
        = Real.binEntropy ((1 - helicityMomentum p / bogoliubovEnergy (helicityMomentum p) Δ) / 2)
      ∧ (0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im) :=
  ⟨helicity_bogoliubov_energy p Δ, helicity_entropicTime p Δ,
   helicity_complex_momentum_converges m hℏ hdt hm⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum

end

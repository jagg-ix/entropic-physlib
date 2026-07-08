/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixC
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixD
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium

/-!
# Linking Appendix C and Appendix D to the entropic-time common root

`CausalDiamond.AppendixC` formalized the zeroth law for bifurcate conformal Killing horizons (Eqs.
C.1–C.8: `κ` constant on `𝓗`), and `CausalDiamond.AppendixD` formalized the conformal group from the
two-time `ℝ^{2,d}` embedding (Eqs. D.1–D.6). Both were proved as self-contained algebraic/geometric
identities. This file shows they are **consistent with** — and meet at — the established
metric-common-root / entropic-time infrastructure.

The de Sitter embedding (Eq. D.3) writes the timelike-section coordinates as `X⁰ = w sinh(t/L)`,
`X^d = w cosh(t/L)` with `w² = L² − r²`. The single observation that drives everything:

 `X^d = bogoliubovEnergy(X⁰, w)` (`embeddingEnergy_eq_bogoliubov`),

because `√((w sinh)² + w²) = w√(sinh² + 1) = w cosh`. So the embedding's spacelike-time coordinate **is
the Bogoliubov energy** `E` of the mode `(ξ, Δ) = (X⁰, w)`, and the embedding ratio is the metric root:

 `X⁰ / X^d = tanh(t/L) = ξ/E = v` (`embeddingVelocity_eq_tanh`),

the very velocity that fixes the Lorentz factor `γ = cosh` and the entropic proper time
`τ_ent = binEntropy((1 − v)/2)` (`CausalDiamond.MetricCommonRoot`). At the unit hyperboloid `w = 1` this
reproduces `diamond_horizon_energy` and `diamond_metric_velocity` exactly: Appendix D's embedding **is**
the diamond Bogoliubov mode `(sinh η, 1)` with `η = R_*/L` the boost rapidity (Eq. D.6, `iJ_{0d} = L∂_t`).

The zeroth law (Appendix C, `𝓛_ζκ = 0`) and the boost-invariance of the entropic rate
(`qifEntropicRate_lorentz_invariant`) are the two faces — geometric and kinematic — of the same fact:
the horizon-generating flow is the `J_{0d}` boost of the embedding, and `κ` (hence the temperature) is
constant along it (`zerothLaw_boost_temperature_consistency`). The main result
`appendixCD_entropic_consistency` bundles Appendix C (zeroth law), Appendix D (embedding ↔ Bogoliubov
energy and velocity), the entropic proper time, and the boost-invariance.

## Scope

The embedding/Bogoliubov identifications are exact scalar identities. The zeroth law and the
boost-invariance are reused verbatim from `CausalDiamond.AppendixC` and `CausalDiamond.QIFEquilibrium`; the
identification "horizon generator = `J_{0d}` boost = entropic-rate boost" is the physical reading the
algebra makes consistent, not an independently derived geometric theorem.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EmbeddingZerothLaw

open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixC
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixD
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency

/-! ## §A — the Appendix-D embedding coordinate `X^d` is the Bogoliubov energy -/

/-- **The embedding's spacelike-time coordinate is the Bogoliubov energy** `X^d = bogoliubovEnergy(X⁰, w)`.
With the de Sitter embedding (Eq. D.3) `X⁰ = w sinh(t/L)`, `X^d = w cosh(t/L)` (`w = √(L²−r²) ≥ 0`),
`bogoliubovEnergy(w sinh, w) = √((w sinh)² + w²) = w√(sinh² + 1) = w cosh = X^d`: the `ℝ^{2,d}` embedding
energy **is** the Bogoliubov dispersion of the mode `(ξ, Δ) = (X⁰, w)`. -/
theorem embeddingEnergy_eq_bogoliubov (w η : ℝ) (hw : 0 ≤ w) :
    bogoliubovEnergy (w * Real.sinh η) w = w * Real.cosh η := by
  have hcs : Real.cosh η ^ 2 = Real.sinh η ^ 2 + 1 := Real.cosh_sq η
  rw [bogoliubovEnergy,
    show (w * Real.sinh η) ^ 2 + w ^ 2 = (w * Real.cosh η) ^ 2 from by
      rw [mul_pow, mul_pow, hcs]; ring]
  exact Real.sqrt_sq (mul_nonneg hw (Real.cosh_pos η).le)

/-- **At the unit hyperboloid `w = 1` the embedding energy is the diamond Bogoliubov energy**
`bogoliubovEnergy(sinh η, 1) = cosh η` — Appendix D's embedding reproduces `diamond_horizon_energy` of the
helicity/metric-common-root bridge. -/
theorem embedding_unit_eq_diamondEnergy (η : ℝ) :
    bogoliubovEnergy (Real.sinh η) 1 = Real.cosh η := by
  have h := embeddingEnergy_eq_bogoliubov 1 η zero_le_one
  rwa [one_mul, one_mul] at h

/-! ## §B — the embedding ratio is the metric common root `X⁰/X^d = tanh(t/L) = v` -/

/-- **The embedding ratio is the metric common root** `X⁰/X^d = tanh(t/L)`. The ratio of the two
timelike-section embedding coordinates `X⁰ = w sinh(t/L)` and `X^d = w cosh(t/L) = bogoliubovEnergy(X⁰, w)`
is the boost velocity `tanh(t/L) = ξ/E` — the velocity that fixes `γ = cosh` and `τ_ent`. -/
theorem embeddingVelocity_eq_tanh (w η : ℝ) (hw : 0 < w) :
    (w * Real.sinh η) / bogoliubovEnergy (w * Real.sinh η) w = Real.tanh η := by
  rw [embeddingEnergy_eq_bogoliubov w η hw.le, Real.tanh_eq_sinh_div_cosh,
    mul_div_mul_left _ _ hw.ne']

/-- **At `w = 1` the embedding velocity is the diamond metric velocity** `sinh η/cosh η = tanh η`
(`diamond_metric_velocity`): the embedding ratio of Appendix D and the metric common root of
`CausalDiamond.MetricCommonRoot` coincide. -/
theorem embedding_unit_velocity_eq_diamond (η : ℝ) :
    Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 = Real.tanh η :=
  diamond_metric_velocity η

/-! ## §C — the entropic proper time from the embedding velocity -/

/-- **The entropic proper time of the embedding mode** `τ_ent = binEntropy((1 − tanh(t/L))/2)`. The
metric velocity `v = X⁰/X^d = tanh(t/L)` of the Appendix-D embedding fixes the entropic proper time of
the Bogoliubov mode `(X⁰, w)` (`entropicTime_eq_binEntropy_velocity`). -/
theorem embedding_entropicTime_eq_velocity (w η : ℝ) (hw : 0 < w) :
    bogoliubovEntropicTime (w * Real.sinh η) w
      = Real.binEntropy ((1 - Real.tanh η) / 2) := by
  rw [entropicTime_eq_binEntropy_velocity, embeddingVelocity_eq_tanh w η hw]

/-- **The de Sitter embedding point lies on the `ℝ^{2,d}` light cone with `X^d` the Bogoliubov energy.**
For `w² = L² − r²` (`w ≥ 0`), the Eq.-D.3 point `(X^{−1}, X⁰, Xⁱ, X^d) = (L, w sinh(t/L), rΩⁱ, w cosh(t/L))`
satisfies `X · X = 0` (Eq. D.1/D.3) *and* `X^d = bogoliubovEnergy(X⁰, w)` — the Appendix-D light-cone
constraint and the Bogoliubov dispersion are the same statement. -/
theorem embedding_on_cone_energy (L r t w : ℝ) (hw : w ^ 2 = L ^ 2 - r ^ 2) (hwpos : 0 ≤ w) :
    (-L ^ 2 - (w * Real.sinh (t / L)) ^ 2
        + (r ^ 2 + (bogoliubovEnergy (w * Real.sinh (t / L)) w) ^ 2) = 0)
      ∧ bogoliubovEnergy (w * Real.sinh (t / L)) w = w * Real.cosh (t / L) := by
  have he := embeddingEnergy_eq_bogoliubov w (t / L) hwpos
  refine ⟨?_, he⟩
  rw [he]
  exact dS_embedding_lightCone L r t w hw

/-! ## §D — the zeroth law (App C) is the boost-invariance of the entropic rate (App D) -/

/-- **The zeroth law is the boost-invariance of the entropic rate.** The Appendix-C zeroth law
`𝓛_ζκ = 0` (`κ` constant along each generator) and the boost-invariance of the QIF entropic rate
(`qifEntropicRate_lorentz_invariant`) are the geometric and kinematic faces of one fact: the
horizon-generating flow is the Appendix-D boost `J_{0d}` (Eq. D.6, `iJ_{0d} = L∂_t`), and `κ` — hence the
temperature `k_B T/ℏ` — is constant along it. -/
theorem zerothLaw_boost_temperature_consistency
    (κ α Lκ ℏ c kB θ : ℝ) (F : FrameData)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0)
    (hC : -4 * α * κ = -2 * Lκ - 4 * α * κ) :
    Lκ = 0
      ∧ (boostFrame θ F).entropicRate = F.entropicRate
      ∧ qifEntropicRate κ c = kB * hawkingTemperature ℏ κ c kB / ℏ :=
  ⟨lieKappa_eq_zero κ α Lκ hC, qifEntropicRate_lorentz_invariant θ F,
   qifEntropicRate_eq_kB_temperature_over_hbar ℏ κ c kB hℏ hc hkB⟩

/-! ## §E — the main result: Appendix C + Appendix D meet at the entropic common root -/

/-- **Appendix C and Appendix D are consistent at the entropic common root.** For the diamond rapidity
`η = R_*/L` and the conformal Killing data of Appendix C:

* **(App C — zeroth law)** `𝓛_ζκ = 0`, the surface gravity is constant along the generator;
* **(App D — embedding energy)** the embedding coordinate `X^d = bogoliubovEnergy(X⁰, 1) = cosh η`;
* **(metric common root)** the embedding ratio `X⁰/X^d = tanh η = v` is the metric velocity;
* **(entropic proper time)** `τ_ent = binEntropy((1 − v)/2)` is fixed by that velocity;
* **(App D — boost)** the entropic rate is invariant under the `J_{0d}` boost that generates the horizon.

The geometric zeroth law (App C), the two-time embedding (App D), and the entropic-time common root meet
in one statement. -/
theorem appendixCD_entropic_consistency
    (η κ α Lκ θ : ℝ) (F : FrameData)
    (hC : -4 * α * κ = -2 * Lκ - 4 * α * κ) :
    Lκ = 0
      ∧ bogoliubovEnergy (Real.sinh η) 1 = Real.cosh η
      ∧ Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 = Real.tanh η
      ∧ bogoliubovEntropicTime (Real.sinh η) 1 = Real.binEntropy ((1 - Real.tanh η) / 2)
      ∧ (boostFrame θ F).entropicRate = F.entropicRate :=
  ⟨lieKappa_eq_zero κ α Lκ hC, embedding_unit_eq_diamondEnergy η,
   diamond_metric_velocity η, diamond_entropicTime_eq_velocity η,
   qifEntropicRate_lorentz_invariant θ F⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EmbeddingZerothLaw

end

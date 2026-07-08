/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT

/-!
# Quantization of the non-Abelian topological mass from large-gauge invariance

Section III of Deser–Jackiw–Templeton, *Topologically Massive Gauge Theories* (Ann. Phys. **281**
(2000) 409, `Deser:1982vy`): for a **non-Abelian** gauge group, *"gauge invariance implies that the mass
term — in a dimensionless combination with the dimensionful coupling constant — is quantized"* (p. 410).
This is the derivation that `ChernSimons.TopologicalMassDJT` (`m_CS = e²|k|/(2π)`, `k ∈ ℤ`) and
`ChernSimons.WittenChernSimonsRepo` (Witten's integer level) *assume*.

Under a **large** gauge transformation of winding number `w ∈ ℤ` (a map to the group not connected to
the identity), the Chern–Simons action shifts by `ΔS = 2π k w`, where `k` is the dimensionless level
(the topological-mass / coupling ratio). The path-integral weight `e^{iS}` — and hence the quantum
theory — is invariant under **every** large gauge transformation exactly when the level is an
**integer**:

 `(∀ w ∈ ℤ, e^{i·2πkw} = 1) ↔ k ∈ ℤ` (`largeGaugePhase_eq_one_iff_int`).

So the topological mass cannot take arbitrary values: gauge invariance quantizes it. (Contrast the
Abelian case of `TopologicalMassAbelianHiggsFlux`, where the paper notes *"we see no reason for
quantizing any of the parameters."*)

* **§A — the large-gauge phase.** `largeGaugePhase k w = e^{i·2πkw}`.
* **§B — the quantization.** `largeGaugePhase_eq_one_iff_int`: invariance under all windings ⟺ `k ∈ ℤ`;
 and the necessity from a **single** nontrivial winding (`largeGaugePhase_one_eq_one_iff_int`).
* **§C — link to the DJT topological mass.** The quantized level is exactly the integer `level` of
 `ChernSimons.TopologicalMassDJT.DJTData`: gauge invariance turns a real level into a genuine DJT mass
 `e²|m|/(2π)` (`gaugeInvariant_level_isDJTMass`), quantized in units of the quantum `e²/(2π)`
 (`topologicalMass_eq_level_mul_unit`, `gaugeInvariant_mass_quantized`).

Proven: the phase `e^{i·2πkw}` equals one for all integer windings iff `k` is an
integer (the exact number-theoretic content of the quantization). Interpretive: that the Chern–Simons
action shifts by `2πkw` under a winding-`w` large gauge transformation is the standard topological
input (not re-derived from the group-manifold `π₃(G) = ℤ` here); given it, the quantization is exact.

## References

* S. Deser, R. Jackiw, S. Templeton, Ann. Phys. **281** (2000) 409 (§III, the non-Abelian mass
 quantization). Complements `ChernSimons.TopologicalMassDJT`, `ChernSimons.WittenChernSimonsRepo`,
 and `TopologicalMassAbelianHiggsFlux`.

No additional assumptions.
-/

set_option autoImplicit false

open scoped Real

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassLevelQuantization

/-! ## §A — the large-gauge phase -/

/-- **The Chern–Simons weight's phase under a winding-`w` large gauge transformation** `e^{i·2πkw}`:
the action shifts by `2πkw` (level `k`, winding `w`), so the path-integral weight `e^{iS}` picks up this
phase. -/
noncomputable def largeGaugePhase (k : ℝ) (w : ℤ) : ℂ :=
  Complex.exp (2 * π * k * (w : ℝ) * Complex.I)

/-! ## §B — the quantization condition -/

/-- **A single nontrivial winding already quantizes the level** `e^{i·2πk} = 1 ↔ k ∈ ℤ`: invariance of
the Chern–Simons weight under the `w = 1` large gauge transformation forces the level to be an integer. -/
theorem largeGaugePhase_one_eq_one_iff_int (k : ℝ) :
    largeGaugePhase k 1 = 1 ↔ ∃ m : ℤ, k = (m : ℝ) := by
  unfold largeGaugePhase
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hfac : (2 * (π : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hrw : (k : ℂ) * (2 * ↑π * Complex.I) = (n : ℂ) * (2 * ↑π * Complex.I) := by
      rw [← hn]; push_cast; ring
    exact_mod_cast mul_right_cancel₀ hfac hrw
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/-- **Chern–Simons level quantization** (Deser §III): the Chern–Simons weight is invariant under *every*
large gauge transformation (winding `w ∈ ℤ`) iff the level `k` is an **integer**. Gauge invariance
quantizes the non-Abelian topological mass. -/
theorem largeGaugePhase_eq_one_iff_int (k : ℝ) :
    (∀ w : ℤ, largeGaugePhase k w = 1) ↔ ∃ m : ℤ, k = (m : ℝ) := by
  constructor
  · intro h
    exact (largeGaugePhase_one_eq_one_iff_int k).mp (h 1)
  · rintro ⟨m, rfl⟩ w
    unfold largeGaugePhase
    rw [Complex.exp_eq_one_iff]
    exact ⟨m * w, by push_cast; ring⟩

/-! ## §C — link: the quantized level is the Deser–Jackiw–Templeton topological mass -/

/-- **The fundamental topological-mass quantum** `e²/(2π)`: the DJT mass comes in integer multiples of
it. -/
noncomputable def topologicalMassUnit (e : ℝ) : ℝ := e ^ 2 / (2 * π)

/-- **The DJT topological mass is `|k|` quanta** `m_CS = |k|·(e²/2π)`: the mass of
`ChernSimons.TopologicalMassDJT` is an integer-level multiple of the fundamental quantum. -/
theorem topologicalMass_eq_level_mul_unit (dj : TopologicalMassDJT.DJTData) :
    TopologicalMassDJT.topologicalMass dj = |(dj.level : ℝ)| * topologicalMassUnit dj.e := by
  unfold TopologicalMassDJT.topologicalMass topologicalMassUnit; ring

/-- **Gauge invariance turns a real level into a genuine DJT mass**: if the Chern–Simons weight is
invariant under every large gauge transformation, the level is an integer `m` and the mass `e²|k|/(2π)`
is exactly the Deser–Jackiw–Templeton topological mass of `TopologicalMassDJT.topologicalMass ⟨e, m⟩`. -/
theorem gaugeInvariant_level_isDJTMass (e k : ℝ) (h : ∀ w : ℤ, largeGaugePhase k w = 1) :
    ∃ m : ℤ, k = (m : ℝ) ∧
      e ^ 2 * |k| / (2 * π) = TopologicalMassDJT.topologicalMass ⟨e, m⟩ := by
  obtain ⟨m, hm⟩ := (largeGaugePhase_eq_one_iff_int k).mp h
  refine ⟨m, hm, ?_⟩
  rw [hm]; rfl

/-- **The topological mass is quantized in units of `e²/(2π)`**: under large-gauge invariance the mass is
`|m|` copies of the fundamental quantum, with `m ∈ ℤ` the Chern–Simons level. -/
theorem gaugeInvariant_mass_quantized (e k : ℝ) (h : ∀ w : ℤ, largeGaugePhase k w = 1) :
    ∃ m : ℤ, e ^ 2 * |k| / (2 * π) = |(m : ℝ)| * topologicalMassUnit e := by
  obtain ⟨m, _, hmass⟩ := gaugeInvariant_level_isDJTMass e k h
  exact ⟨m, by rw [hmass, topologicalMass_eq_level_mul_unit]⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassLevelQuantization

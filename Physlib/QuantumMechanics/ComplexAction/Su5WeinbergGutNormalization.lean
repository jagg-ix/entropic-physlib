/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
meta import Zil

/-!
# The `SU(5)` prediction `sin²θ_W = 3/8`, from first principles

`WeinbergAngle.su5_sin2Weinberg_eq_three_eighths` computed the ratio `Tr(T₃²)/Tr(Q²) = 3/8` on the
`5̄`. This module supplies the *reasoning* behind that number — why the ratio is the weak mixing
angle — and equates the group-theory value with the coupling-side angle `sin²θ_W = g'²/(g²+g'²)`.

The chain, on the `SU(5)` `5̄ = (d^c, d^c, d^c, e⁻, ν)`:

* **Gell-Mann–Nishijima** `Q = T₃ + Y` (`su5Charge_isospin_add_hypercharge`), with the hypercharge
  `Y = (1/3, 1/3, 1/3, −1/2, −1/2)` (`hyperchargeY`).
* **Orthogonality of the generators**: `Tr(T₃ Y) = 0` (`traceIsospinHypercharge`), so
  `Tr(Q²) = Tr(T₃²) + Tr(Y²)` (`traceChargeSq_eq`) — derived structurally from `Q = T₃ + Y`, not by
  plugging numbers.
* **The `SU(5)` normalization** `Tr(T₃²) = 1/2`, `Tr(Y²) = 5/6`, giving
  `tan²θ_W = Tr(T₃²)/Tr(Y²) = 3/5` (`gut_tanSqWeinberg`) and hence
  `sin²θ_W = Tr(T₃²)/Tr(Q²) = 3/8` (`gut_sinSqWeinberg`).
* **The coupling side agrees**: under the GUT normalization `g'² = (3/5) g²` (i.e. `g'²/g²` equal to
  the trace ratio `Tr(T₃²)/Tr(Y²)`), the angle built from the couplings is
  `sinWeinberg g g' ² = 3/8` (`sinSqWeinberg_of_gutNorm`), so the physical mixing angle equals the
  group-theory trace ratio (`su5_sinSqWeinberg_eq_trace_ratio`).

**Honest layering.** Everything here is proven. Interpretive (as before): the low-energy measured
`sin²θ_W ≈ 0.23` is this `3/8` renormalization-group-evolved from `M_GUT`, which is not formalized.

## References

* H. Georgi, H. Quinn, S. Weinberg, "Hierarchy of Interactions in Unified Gauge Theories", Phys. Rev.
  Lett. **33**, 451 (1974). Reuses `WeinbergAngle` (`weakIsospin3`, `sinWeinberg`,
  `su5_sin2Weinberg_eq_three_eighths`) and `Su5ChargeQuantizationCartanTensor` (`su5AntifundCharge`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization

open Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor

/-! ## Gell-Mann–Nishijima and the hypercharge -/

/-- **The weak hypercharge `Y` on the `5̄`** `= (1/3, 1/3, 1/3, −1/2, −1/2)`: `+1/3` for the down
antiquark colour triplet, `−1/2` for the lepton doublet. -/
def hyperchargeY : Fin 5 → ℚ := ![1/3, 1/3, 1/3, -1/2, -1/2]

/-- **Gell-Mann–Nishijima on the `5̄`** `Q = T₃ + Y`: electric charge is weak isospin plus hypercharge
(here `Y` is the `U(1)` generator normalized so it adds directly to `T₃`, i.e. half the conventional
weak hypercharge of `Particles.GellMannNishijima`; the two are reconciled in the electroweak links). -/
lemma su5Charge_isospin_add_hypercharge (i : Fin 5) :
    su5AntifundCharge i = weakIsospin3 i + hyperchargeY i := by
  fin_cases i <;> norm_num [su5AntifundCharge, weakIsospin3, hyperchargeY]

/-! ## The generator traces on the `5̄` -/

/-- `Tr(T₃²) = 1/2`. -/
lemma traceIsospinSq : ∑ i, weakIsospin3 i ^ 2 = 1 / 2 := by
  simp [weakIsospin3, Fin.sum_univ_five]; norm_num

/-- `Tr(Y²) = 5/6`. -/
lemma traceHyperchargeSq : ∑ i, hyperchargeY i ^ 2 = 5 / 6 := by
  simp [hyperchargeY, Fin.sum_univ_five]; norm_num

/-- **`Tr(T₃ Y) = 0`** — weak isospin and hypercharge are orthogonal generators. -/
lemma traceIsospinHypercharge : ∑ i, weakIsospin3 i * hyperchargeY i = 0 := by
  simp [weakIsospin3, hyperchargeY, Fin.sum_univ_five]; norm_num

/-- **`Tr(Q²) = Tr(T₃²) + Tr(Y²)`** — derived from `Q = T₃ + Y` and the orthogonality `Tr(T₃ Y) = 0`,
not by plugging in the numbers. -/
lemma traceChargeSq_eq :
    (∑ i, su5AntifundCharge i ^ 2)
      = (∑ i, weakIsospin3 i ^ 2) + (∑ i, hyperchargeY i ^ 2) := by
  have hexp : ∀ i, su5AntifundCharge i ^ 2
      = weakIsospin3 i ^ 2 + 2 * (weakIsospin3 i * hyperchargeY i) + hyperchargeY i ^ 2 :=
    fun i => by rw [su5Charge_isospin_add_hypercharge i]; ring
  calc ∑ i, su5AntifundCharge i ^ 2
      = ∑ i, (weakIsospin3 i ^ 2 + 2 * (weakIsospin3 i * hyperchargeY i) + hyperchargeY i ^ 2) :=
        Finset.sum_congr rfl fun i _ => hexp i
    _ = (∑ i, weakIsospin3 i ^ 2) + 2 * (∑ i, weakIsospin3 i * hyperchargeY i)
          + (∑ i, hyperchargeY i ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ i, weakIsospin3 i ^ 2) + (∑ i, hyperchargeY i ^ 2) := by
        rw [traceIsospinHypercharge]; ring

/-! ## The `SU(5)` normalization: `tan²θ_W = 3/5`, `sin²θ_W = 3/8` -/

/-- **The `SU(5)` GUT normalization `tan²θ_W = Tr(T₃²)/Tr(Y²) = 3/5`** — this fixes the ratio of the
`U(1)_Y` to `SU(2)_L` couplings at unification. -/
lemma gut_tanSqWeinberg :
    (∑ i, weakIsospin3 i ^ 2) / (∑ i, hyperchargeY i ^ 2) = 3 / 5 := by
  rw [traceIsospinSq, traceHyperchargeSq]; norm_num

/-- **`sin²θ_W = Tr(T₃²)/Tr(Q²) = 3/8`**, derived structurally via `traceChargeSq_eq`. -/
lemma gut_sinSqWeinberg :
    (∑ i, weakIsospin3 i ^ 2) / (∑ i, su5AntifundCharge i ^ 2) = 3 / 8 := by
  rw [traceChargeSq_eq, traceIsospinSq, traceHyperchargeSq]; norm_num

/-! ## The coupling side agrees -/

/-- **Under the GUT normalization `g'² = (3/5) g²`, the coupling-side angle is `sin²θ_W = 3/8`.** -/
lemma sinSqWeinberg_of_gutNorm (g g' : ℝ) (hg : 0 < g) (hnorm : g' ^ 2 = 3 / 5 * g ^ 2) :
    sinWeinberg g g' ^ 2 = 3 / 8 := by
  have hgsq : 0 < g ^ 2 := by positivity
  have hS : 0 < g ^ 2 + g' ^ 2 := by rw [hnorm]; nlinarith
  have hSs : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt (le_of_lt hS)
  unfold sinWeinberg
  rw [div_pow, hSs, hnorm]; field_simp; ring

/-- **The formal proof: the physical weak mixing angle equals the `SU(5)` trace ratio.** Under the GUT
normalization `g'² = (3/5) g²` — where `3/5 = Tr(T₃²)/Tr(Y²)` is itself the trace ratio
(`gut_tanSqWeinberg`) — the mixing angle built from the gauge couplings equals the group-theory ratio
`Tr(T₃²)/Tr(Q²)`, both `3/8`. This welds the coupling-side `sinWeinberg` to the `SU(5)` prediction. -/
lemma su5_sinSqWeinberg_eq_trace_ratio (g g' : ℝ) (hg : 0 < g) (hnorm : g' ^ 2 = 3 / 5 * g ^ 2) :
    sinWeinberg g g' ^ 2 = ((∑ i, weakIsospin3 i ^ 2) / (∑ i, su5AntifundCharge i ^ 2) : ℚ) := by
  rw [sinSqWeinberg_of_gutNorm g g' hg hnorm, gut_sinSqWeinberg]; norm_num

end Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization.gut_sinSqWeinberg where
  formalizes @ "claim:the-gut-normalized-weak-mixing-angle-is-sin-squared-theta-w-equals-three-eighths",
  supported_by @ "paper:georgi-glashow-1974-su5-unification",
  caveat @ "claim:the-tree-level-gut-value-runs-to-the-measured-0.23-below-the-unification-scale"

zil attach Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization.su5_sinSqWeinberg_eq_trace_ratio where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization.gut_sinSqWeinberg",
  formalizes @ "claim:the-weak-mixing-angle-is-the-ratio-of-the-isospin-trace-to-the-charge-trace-over-the-antifundamental",
  requires @ "claim:the-gut-normalized-weak-mixing-angle-is-sin-squared-theta-w-equals-three-eighths"

zil_file_contract physlib.su5WeinbergGutNormalization where
  promises "The SU(5) grand-unified weak mixing angle: with the GUT hypercharge normalization the tree-level sin squared theta-w is three eighths, obtained as the ratio of the weak-isospin trace to the charge trace over the anti-fundamental five-bar."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization.weakIsospin3",
    "lean:Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization.su5AntifundCharge"]
  forbids_substitutes ["the measured low-energy value 0.23, obtained only after renormalization-group running below the unification scale"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization.gut_sinSqWeinberg,
    Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization.su5_sinSqWeinberg_eq_trace_ratio]

/- ZIL-END -/

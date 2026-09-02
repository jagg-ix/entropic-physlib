/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadicTube
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric
public import Physlib.QFT.PathIntegral.DampedHeatLandauerDichotomy
public import Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy
meta import Zil

/-!
# Linking the dyadic Calderón ladder to the dissipation/scale ZIL arc

The Section-4 multi-norm Calderón formalization (`Mathematics.HarmonicAnalysis.MultiNorm*`) and the
dissipation / wedge-modular arc (`zil-dissipation-landauer`: `DampedHeatLandauerDichotomy`, `WickClock`,
`ScaleDilationLogMetric`, `SchwarzschildHorizonScaleMobius`) live on the same branch and step along the
**same dyadic scale ladder**. This module welds their ZIL claim graphs with two genuine theorems:

* **the Calderón resolution ladder is the blockspin scale ladder** (`dyadicCalderon_blockspin_ladder`):
  the scale-metric distance from the `n`-th dyadic Calderón expansion factor to unity is exactly `n·log 2`
  — the Calderón resolutions sit at the rungs of the RG blockspin ladder (`blockspin_ladder`), the same
  `log 2` that prices one bit in `landauerCost`, one factor-2 dilation in `scaleDistance_two_one`, and the
  one-bit ER=EPR horizon entropy;
* **one Landauer bit-time steps the Calderón ladder down one rung** (`dampedHeat_dyadic_step`): evolving the
  `(n+1)`-st dyadic expansion factor through the damped-heat semigroup for exactly the bit-erasure time
  `ln 2/(m²+λ)` (`dampedHeat_bit_erasure_time`) yields the `n`-th factor — each rung of the Calderón
  resolution ladder costs precisely one erased bit of the dissipative flow.

The `zil attach` edges make the cross-arc relation queryable: the Calderón claims
(`physlib.entropicSpine.multiNormSection4*`) and the dissipation claims (`physlib.dampedHeat.*`,
`physlib.wedgeKms.*`) are joined through the shared scale-ladder structure, with caveats keeping the weld
honest (a numerical scale identity, not an identification of harmonic-analysis resolutions with physical RG
transformations or thermodynamic erasure).
-/

set_option autoImplicit false

open Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric
open Physlib.QFT.PathIntegral

@[expose] public section

namespace Physlib.Meta.DyadicCalderonScaleLadderZil

/-- **[The Calderón resolution ladder is the blockspin scale ladder]**
`scaleDistance (dyadicExpansion n) 1 = n·log 2` — the `n`-th dyadic Calderón expansion factor `2^n` sits at
scale-metric distance exactly `n·log 2` from unity: the Calderón resolutions are the rungs of the RG
blockspin ladder, in the same `log 2` currency as the Landauer bit and the one-bit horizon entropy. -/
@[zil_claim physlib.scaleLadder.calderonBlockspinLadder,
  zil_concept physics.dyadicScaleLadder, zil_requires assumptions.dyadicResolutionFamily,
  zil_export]
theorem dyadicCalderon_blockspin_ladder (n : ℕ) :
    scaleDistance (dyadicExpansion n) 1 = n * Real.log 2 := by
  have h := blockspin_ladder n 1 one_pos
  rw [mul_one] at h
  rw [dyadicExpansion]
  exact h

/-- **[One Landauer bit-time steps the Calderón ladder down one rung]**
`p(ln 2/(m²+λ)) · 2^{n+1} = 2^n` — evolving the `(n+1)`-st dyadic expansion factor through the damped-heat
semigroup for exactly the bit-erasure time halves it to the `n`-th factor: each rung of the Calderón
resolution ladder costs one erased bit of the dissipative flow. -/
@[zil_claim physlib.scaleLadder.dampedHeatDyadicStep,
  zil_concept physics.dyadicScaleLadder, zil_requires assumptions.positiveDecayRate,
  zil_export]
theorem dampedHeat_dyadic_step (m_sq lam : ℝ) (ha : 0 < m_sq + lam) (n : ℕ) :
    damped_heat_propagator (Real.log 2 / (m_sq + lam)) m_sq lam * dyadicExpansion (n + 1)
      = dyadicExpansion n := by
  rw [dampedHeat_bit_erasure_time m_sq lam (dyadicExpansion (n + 1)) ha, dyadicExpansion,
    dyadicExpansion, pow_succ]
  ring

/-- **[The multi-norm log-scale lattice IS the blockspin scale ladder]**
`scaleDistance (2^{L i}) 1 = toLogPoint L i · log 2` — the multi-norm machinery's own log-coordinate system
(`MultiNormDyadic.toLogPoint L i = L i`, integer log-scales) lands on exactly the entropic blockspin ladder:
a multi-norm dotted scale at integer level `L i` sits at scale-metric distance `L i · log 2` from unit scale.
A *second, independent* multi-norm scale object (distinct from `dyadicExpansion`) on the same entropic ladder,
so the harmonic-analysis coordinate system and the entropic scale metric are the same integer-log lattice —
not a coincidence of one definition. -/
@[zil_claim physlib.scaleLadder.multiNormLogPointLadder,
  zil_concept physics.dyadicScaleLadder, zil_requires assumptions.multiNormLogCoordinates,
  zil_export]
theorem multiNormLogPoint_blockspin_ladder {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (L : ι → ℕ) (i : ι) :
    scaleDistance (2 ^ (L i)) 1
      = Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.toLogPoint L i * Real.log 2 := by
  have h := blockspin_ladder (L i) 1 one_pos
  rw [mul_one] at h
  simpa [Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.toLogPoint] using h

zil_theorem_intent multiNormLogPoint_blockspin_ladder where
  at_level bridge_theorem
  must_mention [Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.toLogPoint,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.scaleDistance]

zil attach multiNormLogPoint_blockspin_ladder where
  formalizes @ "claim:multinorm-log-lattice-is-blockspin-scale-ladder",
  requires @ "definition:multinorm-log-coordinates",
  requires @ "claim:blockspin-ladder-arithmetic-progression",
  supported_by @ "definition:scale-dilation-log-metric",
  caveat @ "claim:coordinate-lattice-identity-not-a-physical-rg-flow-of-the-multinorm-machinery"

zil_theorem_intent dyadicCalderon_blockspin_ladder where
  at_level bridge_theorem
  must_mention [Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicExpansion,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.scaleDistance]

zil_theorem_intent dampedHeat_dyadic_step where
  at_level bridge_theorem
  must_mention [Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicExpansion,
    Physlib.QFT.PathIntegral.damped_heat_propagator]

zil attach dyadicCalderon_blockspin_ladder where
  formalizes @ "claim:calderon-resolution-ladder-is-blockspin-scale-ladder",
  requires @ "definition:dyadic-expansion-factor",
  requires @ "claim:blockspin-ladder-arithmetic-progression",
  supported_by @ "claim:lemma4.2-certified-dual-families-cancellation-support-partial-and-full-calderon-identities",
  supported_by @ "definition:scale-dilation-log-metric",
  caveat @ "claim:numerical-scale-identity-not-rg-transformation-identification"

zil attach dampedHeat_dyadic_step where
  formalizes @ "claim:one-landauer-bit-time-steps-calderon-ladder-one-rung",
  requires @ "claim:damped-heat-bit-erasure-time",
  requires @ "definition:dyadic-expansion-factor",
  supported_by @ "claim:calderon-resolution-ladder-is-blockspin-scale-ladder",
  caveat @ "claim:scalar-factor-evolution-not-kernel-family-dynamics"

zil_rule scaleLadderCrossArc:
  ?claim # crosses_arc @ ?other IF
  ?declaration # formalizes @ ?claim AND
  ?declaration # requires @ ?other

zil_rule scaleLadderEvidence:
  ?claim # supported_by @ ?source IF
  ?declaration # formalizes @ ?claim AND
  ?declaration # supported_by @ ?source

/-! ### The irreversible clock: constant scale speed, bit-metered amplitude, the Misra reading -/

section IrreversibleClock

open Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz
open Physlib.QuantumMechanics.RelationalTime

/-- **[The damped orbit moves at constant speed in the scale metric]**
`d_scale(|p(t)·x|, |x|) = (m² + λ)·t`. The damped-heat orbit — the dilation-group flow
`dilationFlow (−(m²+λ))` of `ScaleDilationLogMetric`, whose composition law is
`dampedHeat_group_hom` — is a constant-speed ray in the log/scale metric: each unit of time costs
the same scale distance, and each `log 2` of scale distance is one bit
(`dampedHeat_bit_erasure_time`, the dyadic ladder above). -/
theorem dampedHeat_scaleDistance (t m_sq lam x : ℝ) (ht : 0 ≤ t)
    (hrate : 0 ≤ m_sq + lam) (hx : x ≠ 0) :
    scaleDistance |damped_heat_propagator t m_sq lam * x| |x| = (m_sq + lam) * t := by
  have hxa : |x| ≠ 0 := abs_ne_zero.mpr hx
  unfold scaleDistance
  rw [dampedHeat_abs_apply, mul_div_assoc, div_self hxa, mul_one, Real.log_exp,
    abs_of_nonpos (by nlinarith)]
  ring

/-- **[The damped amplitude is `2^(−bits)`]** `|p(t)·x| = 2^(−(m²+λ)t/ln 2)·|x|` — exponential
decay with the Landauer bit as the unit: the exponent `(m²+λ)t/ln 2` is the number of bits the
orbit has erased by time `t` (one per `ln 2/(m²+λ)`, `dampedHeat_bit_erasure_time`). -/
theorem dampedHeat_amplitude_bits (t m_sq lam x : ℝ) :
    |damped_heat_propagator t m_sq lam * x|
      = (2 : ℝ) ^ (-((m_sq + lam) * t / Real.log 2)) * |x| := by
  rw [dampedHeat_abs_apply]
  congr 1
  rw [Real.rpow_def_of_pos two_pos]
  congr 1
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

/-- **[The Misra clock's reading is metered in Landauer bits]** the same elapsed time `t` that the
Misra–Prigogine internal-time operator `T = i d/dλ` *reads* on the unitary Liouville face
(`ageOperator_reads_evolution_time` — the `i[L,T] = I` clock of
`misra_jacobson_entropic_synthesis` and `misraTime_reads_classical_time`) is *metered in bits* on
the damped face: the amplitude is `2^(−bits(t))` with `bits(t) = (m²+λ)t/ln 2`. One irreversible
time, two faces — and each of those bits, erased at a horizon, costs exactly `k_B ln 2` of horizon
entropy (`horizon_bit_erasure_is_one_bit_entropy`, the Landauer–Bekenstein identity). -/
theorem misraClock_reads_time_priced_in_bits (t lam m_sq damping x : ℝ) :
    ageOperator (liouvilleEvolve t (fun _ => 1)) lam
        = (t : ℂ) * liouvilleEvolve t (fun _ => 1) lam
      ∧ |damped_heat_propagator t m_sq damping * x|
          = (2 : ℝ) ^ (-((m_sq + damping) * t / Real.log 2)) * |x| :=
  ⟨ageOperator_reads_evolution_time t lam, dampedHeat_amplitude_bits t m_sq damping x⟩

end IrreversibleClock

/- ZIL: the irreversible-clock chain — dilation orbit → scale speed → bits → Misra reading →
horizon pricing. -/

zil attach Physlib.QFT.PathIntegral.dampedHeat_group_hom where
  formalizes @ "claim:damped-heat-orbit-is-dilation-group-orbit",
  supported_by @ "paper:misra-prigogine-courbage-1979",
  caveat @ "claim:scalar-mode-flow-law-not-an-operator-dilation-theorem"

zil attach dampedHeat_scaleDistance where
  formalizes @ "claim:damped-orbit-moves-at-constant-speed-in-the-scale-metric",
  requires @ "claim:damped-heat-orbit-is-dilation-group-orbit",
  supported_by @ "paper:misra-prigogine-courbage-1979"

zil attach dampedHeat_amplitude_bits where
  formalizes @ "claim:damped-amplitude-is-two-to-minus-bits",
  requires @ "claim:damped-orbit-moves-at-constant-speed-in-the-scale-metric",
  supported_by @ "paper:landauer-1961"

zil_theorem_intent misraClock_reads_time_priced_in_bits where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.RelationalTime.ageOperator, damped_heat_propagator]

zil attach misraClock_reads_time_priced_in_bits where
  formalizes @ "claim:misra-internal-time-reading-is-metered-in-landauer-bits",
  requires @ "claim:misra-internal-time-reads-classical-time",
  requires @ "claim:damped-amplitude-is-two-to-minus-bits",
  prices_with @ "law:one-bit-erased-at-the-horizon-grows-horizon-entropy-by-exactly-kb-ln-two",
  supported_by @ "paper:misra-prigogine-1978",
  caveat @ "claim:conjunction-of-unitary-face-reading-and-damped-face-metering"

zil_rule misraLandauerClockPricing:
  ?claim # is_priced_by @ ?law IF
  ?decl # formalizes @ ?claim AND
  ?decl # prices_with @ ?law

zil_file_contract physlib.dyadicCalderonScaleLadder where
  promises "The Section-4 multi-norm Calderon dyadic resolution ladder and the dissipation/scale arc step along the same ladder: the n-th dyadic expansion factor sits at scale-metric distance n log 2 from unity (the blockspin ladder), and one damped-heat bit-erasure time steps the expansion factor down exactly one dyadic rung."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicExpansion",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.scaleDistance",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.blockspin_ladder",
    "lean:Physlib.QFT.PathIntegral.damped_heat_propagator",
    "lean:Physlib.QFT.PathIntegral.dampedHeat_bit_erasure_time"]
  forbids_substitutes ["an identification of harmonic-analysis dyadic resolutions with physical RG transformations",
    "a thermodynamic erasure claim about Calderon kernel families",
    "a convergence statement about the Calderon reproducing series from the scalar ladder identity"]
  witnessed_by [dyadicCalderon_blockspin_ladder, dampedHeat_dyadic_step,
    multiNormLogPoint_blockspin_ladder]

#zil_formalization_lint physlib.dyadicCalderonScaleLadder

/-! ### The harmonic-analysis track's identity and its true place in the spine

The `Mathematics.HarmonicAnalysis.MultiNorm*` family (35 modules — Calderón reproducing formula, Rychkov
spatial/dual estimates, ℓ²-decoupling infrastructure, dyadic-tube/marked-cone geometry) is a **self-contained
harmonic-analysis library**: none of its modules imports or references the entropic-dynamics core. It is
nonetheless imported by `Physlib.EntropicSpine` (under the "Hamilton–Killing → quantum mechanics" section
heading, which it does not belong to). This contract records the *honest* relationship the imports leave
implicit:

* the track's **only** formalized connection to the entropic program is the **scale ladder** — its two
  independent dyadic-scale objects (`MultiNormSchwartzKernel.dyadicExpansion`, `MultiNormDyadic.toLogPoint`)
  both land on the entropic blockspin ladder (`dyadicCalderon_blockspin_ladder`,
  `multiNormLogPoint_blockspin_ladder`), and one dissipative bit-erasure time steps that ladder one rung
  (`dampedHeat_dyadic_step`);
* *conceptually*, the multi-norm machinery is the analytic **foundation** of the Carleson / Du–Zhang
  Schrödinger pointwise-convergence arc (`Schrodinger.SchrodingerCarlesonThreshold`) — the question of whether
  the entropic clock's initial datum is recoverable pointwise — but that role is mediated entirely through the
  scale ladder above, not by any entropic content inside the `MultiNorm*` files.

The contract forbids over-reading the spine import as a direct entropic result. -/

zil_file_contract physlib.harmonicAnalysisSpineIdentity where
  promises "The MultiNorm* harmonic-analysis family is a self-contained library (Calderon reproducing formula, Rychkov, decoupling, dyadic-tube geometry) with no entropic imports; its sole formalized connection to the entropic spine is the scale ladder, via which its dyadic-scale objects coincide with the entropic blockspin ladder and it serves as the analytic foundation of the Carleson-Schrodinger pointwise-convergence arc."
  at_level structural
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicExpansion",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.toLogPoint",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.scaleDistance"]
  forbids_substitutes ["reading the EntropicSpine import of MultiNorm* as a direct entropic or quantum-mechanical result",
    "any claim that the multi-norm machinery contains entropic-dynamics content",
    "a physical RG-flow interpretation of the multi-norm log-coordinate lattice"]
  witnessed_by [multiNormLogPoint_blockspin_ladder]

#zil_formalization_lint physlib.harmonicAnalysisSpineIdentity

zil_rule harmonicAnalysisSpineBridge:
  ?track # connects_to_spine_via @ ?bridge IF
  ?declaration # formalizes @ ?bridge AND
  ?declaration # requires @ ?track

end Physlib.Meta.DyadicCalderonScaleLadderZil

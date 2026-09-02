/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNobleMetalBandStructure
public import Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Conductivity as coherence: the `s–d` scattering rate is a decoherence rate

The `s–d` scattering that makes gold the worst conductor (`SciamaAdSCPTNobleMetalBandStructure`) is the *same*
process that destroys the electron's phase coherence.  This module makes the identification precise and links it
to the path-integral / decoherence-functional interference already formalized in the repo.

**The decoherence rate = the transport relaxation rate.**  The Fermi-golden-rule `s–d` scattering rate
`Γ = 1/τ = (2π/ℏ)|M|² g_d(E_F)` (`sdScatteringRate`) plays two roles from one quantity:

* **Transport** — Drude `σ = n e² τ / m* = carrier / Γ`, so `σ · Γ = carrier` (`transport_coherence_identity`):
  conductivity is inversely the scattering rate, i.e. `σ ∝` the coherence time `1/Γ`.
* **Decoherence** — a Poisson process at rate `Γ`: the fraction of carriers that have *not* scattered (that
  retain phase coherence) after a time `t` is `exp(−Γt)` (`interferenceVisibility`) — the **interference
  visibility**.  This is the same `exp(−φ)` entropic-damping modulus as the Caldeira–Leggett influence
  functional `CaldeiraLeggettDecoherence.caldeiraLeggettSuppression` (with the `d`-band / phonon bath as the
  Caldeira–Leggett bath), and the entropy-production factor of `CaldeiraLeggettDecoherence`.

**The double-slit / path-integral interference it suppresses.**  In the Dowker–Johnston–Sorkin *Hilbert spaces
from path integrals* framework (`QuantumMeasureHistoryHilbert`), two disjoint histories `α, β` (the two slit
paths) have quantum measure `μ(α⊔β) = μ(α) + μ(β) + 2 Re D(α,β)` (`interference`), the extra `2 Re D(α,β)` being
the double-slit fringe.  When the environment decoheres them (`Re D(α,β) = 0`) the fringe vanishes and the
measure is classically additive (`interference_decohered`).  Scaling the off-diagonal by the visibility
`v = exp(−Γt)` interpolates between the two:

* `decoheredMeasure_full_coherence` — at `v = 1` (no scattering) the full Sorkin interference `μ(α⊔β)`.
* `decoheredMeasure_classical` — at `v = 0` (fully decohered) the classical sum `μ(α) + μ(β)`.
* `decoheredMeasure_fringe_bound` — the fringe `|v · 2 Re D(α,β)| ≤ μ(α) + μ(β)` at any visibility, from the
  Sorkin two-history strong-positivity bound `abs_interference_le`.

**The upshot** (`gold_worst_and_decoheres_fastest`, `gold_suppresses_fringe_most`): gold, with the largest
`g_d(E_F)`, has the largest `Γ` — so it both conducts *worst* (`σ = carrier/Γ` smallest) and decoheres *fastest*
(`exp(−Γt)` smallest, fringe most suppressed).  Conductivity and interference visibility are two readings of the
one golden-rule scattering rate: gold is a poor conductor *because* it is a fast decoherer.

Honest scope: the identity `σ·Γ = carrier`, the visibility `exp(−Γt)`, and the visibility-scaled interference
bound (reusing the repo's Sorkin `interference`/`abs_interference_le`).  The microscopic equality of the two `Γ`'s
is the physical identification (one golden-rule rate); the `g_d(E_F)` ordering is the band-structure input as in
`SciamaAdSCPTNobleMetalBandStructure`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNobleMetalBandStructure
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert

/-! ## A. The `s–d` scattering rate as a decoherence rate: the interference visibility -/

/-- The interference visibility / coherent fraction after `s–d` scattering over a time `t`: `exp(−Γt)` with
`Γ = sdScatteringRate` (Fermi golden rule).  The Poisson survival probability of *not* scattering = the fraction
of carriers retaining phase coherence = the fringe visibility — the same `exp(−φ)` form as
`CaldeiraLeggettDecoherence.caldeiraLeggettSuppression`. -/
noncomputable def interferenceVisibility (prefactor t : ℝ) (X : NobleMetal) : ℝ :=
  Real.exp (-(sdScatteringRate prefactor X * t))

/-- **[Visibility is positive]** `exp(−Γt) > 0`. -/
theorem interferenceVisibility_pos (prefactor t : ℝ) (X : NobleMetal) :
    0 < interferenceVisibility prefactor t X := Real.exp_pos _

/-- **[Visibility ≤ 1] coherence can only decay.** -/
theorem interferenceVisibility_le_one {prefactor t : ℝ} (hp : 0 ≤ prefactor) (ht : 0 ≤ t) (X : NobleMetal) :
    interferenceVisibility prefactor t X ≤ 1 := by
  unfold interferenceVisibility sdScatteringRate
  rw [Real.exp_le_one_iff]
  nlinarith [mul_nonneg (mul_nonneg hp (le_of_lt (dBandDOS_pos X))) ht]

/-- **[Full coherence at `t = 0`]** `exp(0) = 1` — no scattering, no decoherence. -/
theorem interferenceVisibility_full_at_zero (prefactor : ℝ) (X : NobleMetal) :
    interferenceVisibility prefactor 0 X = 1 := by
  unfold interferenceVisibility; simp

/-- **[Gold decoheres fastest] the visibility is smallest for gold] `v_Au < v_Cu < v_Ag`.**  Gold's largest
`g_d(E_F)` gives the largest scattering rate `Γ`, hence the fastest coherence decay. -/
theorem interferenceVisibility_gold_least {prefactor t : ℝ} (hp : 0 < prefactor) (ht : 0 < t) :
    interferenceVisibility prefactor t .gold < interferenceVisibility prefactor t .copper
      ∧ interferenceVisibility prefactor t .copper < interferenceVisibility prefactor t .silver := by
  unfold interferenceVisibility sdScatteringRate dBandDOS
  refine ⟨Real.exp_lt_exp.mpr ?_, Real.exp_lt_exp.mpr ?_⟩ <;> nlinarith [mul_pos hp ht]

/-! ## B. The transport relaxation rate IS the decoherence rate -/

/-- **[Conductivity × scattering rate = carrier] `σ · Γ = n e²/m*`.**  The Drude conductivity is inversely the
`s–d` scattering rate; the *same* `Γ` is the decoherence rate.  Hence `σ ∝` the coherence time `1/Γ`. -/
theorem transport_coherence_identity {carrier prefactor : ℝ} (hp : 0 < prefactor) (X : NobleMetal) :
    bandConductivity carrier prefactor X * sdScatteringRate prefactor X = carrier := by
  have hne : sdScatteringRate prefactor X ≠ 0 := ne_of_gt (mul_pos hp (dBandDOS_pos X))
  unfold bandConductivity
  field_simp

/-- **[Gold conducts worst *and* decoheres fastest]** — from the one largest `g_d(E_F)`: `σ_Au < σ_Ag` and
`v_Au < v_Ag`.  Conductivity and coherence are two readings of the same golden-rule scattering rate. -/
theorem gold_worst_and_decoheres_fastest {carrier prefactor t : ℝ}
    (hc : 0 < carrier) (hp : 0 < prefactor) (ht : 0 < t) :
    bandConductivity carrier prefactor .gold < bandConductivity carrier prefactor .silver
      ∧ interferenceVisibility prefactor t .gold < interferenceVisibility prefactor t .silver := by
  refine ⟨bandConductivity_antitone hc hp (show dBandDOS .silver < dBandDOS .gold by norm_num [dBandDOS]),
    lt_trans (interferenceVisibility_gold_least hp ht).1 (interferenceVisibility_gold_least hp ht).2⟩

/-! ## C. The double-slit / path-integral interference (Sorkin) controlled by the visibility -/

variable {ι : Type*} [DistribLattice ι] [OrderBot ι] {D : ι → ι → ℂ}

/-- The two-history quantum measure with the interference term scaled by the coherence/visibility `v`:
`μ_v(α⊔β) = μ(α) + μ(β) + v·(2 Re D(α,β))`.  `v = 1` is the full Sorkin interference, `v = 0` the classical sum. -/
noncomputable def decoheredMeasure (D : ι → ι → ℂ) (v : ℝ) (α β : ι) : ℝ :=
  quantalMeasure D α + quantalMeasure D β + v * (2 * (D α β).re)

/-- **[Full coherence `v = 1` recovers the Sorkin interference]** `μ₁(α⊔β) = μ(α⊔β)` (`interference`). -/
theorem decoheredMeasure_full_coherence (h : IsDecoherenceFunctional D) (α β : ι) (hd : Disjoint α β) :
    decoheredMeasure D 1 α β = quantalMeasure D (α ⊔ β) := by
  rw [decoheredMeasure, interference h α β hd]; ring

omit [DistribLattice ι] [OrderBot ι] in
/-- **[Full decoherence `v = 0` gives the classical sum]** `μ₀ = μ(α) + μ(β)` — no fringe, as in
`interference_decohered`. -/
theorem decoheredMeasure_classical (D : ι → ι → ℂ) (α β : ι) :
    decoheredMeasure D 0 α β = quantalMeasure D α + quantalMeasure D β := by
  rw [decoheredMeasure]; ring

/-- **[The fringe is bounded by the measures at any visibility] `|μ_v − (μα+μβ)| ≤ μα + μβ`.**  The
visibility-scaled double-slit fringe `v·2 Re D(α,β)` cannot exceed the classical weight — from the Sorkin
two-history strong-positivity bound `abs_interference_le`. -/
theorem decoheredMeasure_fringe_bound (h : IsDecoherenceFunctional D) {α β : ι} (hαβ : α ≠ β)
    {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    |decoheredMeasure D v α β - (quantalMeasure D α + quantalMeasure D β)|
      ≤ quantalMeasure D α + quantalMeasure D β := by
  have hbound := abs_interference_le h hαβ
  have hsum : 0 ≤ quantalMeasure D α + quantalMeasure D β :=
    add_nonneg (quantalMeasure_nonneg h α) (quantalMeasure_nonneg h β)
  have hdiff : decoheredMeasure D v α β - (quantalMeasure D α + quantalMeasure D β)
      = v * (2 * (D α β).re) := by rw [decoheredMeasure]; ring
  rw [hdiff, abs_mul, abs_of_nonneg hv]
  calc v * |2 * (D α β).re| ≤ v * (quantalMeasure D α + quantalMeasure D β) :=
        mul_le_mul_of_nonneg_left hbound hv
    _ ≤ 1 * (quantalMeasure D α + quantalMeasure D β) := mul_le_mul_of_nonneg_right hv1 hsum
    _ = quantalMeasure D α + quantalMeasure D β := one_mul _

/-- **[The `s–d` scattering visibility caps the double-slit fringe]** — applying `decoheredMeasure_fringe_bound`
at the transport visibility `v = exp(−Γt)`.  Strong scattering (small visibility) drives the fringe toward the
classical sum. -/
theorem twoSlit_fringe_scales_with_visibility (h : IsDecoherenceFunctional D) {α β : ι} (hαβ : α ≠ β)
    {prefactor t : ℝ} (hp : 0 ≤ prefactor) (ht : 0 ≤ t) (X : NobleMetal) :
    |decoheredMeasure D (interferenceVisibility prefactor t X) α β
        - (quantalMeasure D α + quantalMeasure D β)|
      ≤ quantalMeasure D α + quantalMeasure D β :=
  decoheredMeasure_fringe_bound h hαβ (le_of_lt (interferenceVisibility_pos prefactor t X))
    (interferenceVisibility_le_one hp ht X)

omit [DistribLattice ι] [OrderBot ι] in
/-- **[Gold suppresses the fringe most]** — for constructively-interfering slit paths (`Re D(α,β) > 0`), gold's
smallest visibility gives the smallest double-slit measure: the fast decoherer washes out the fringe. -/
theorem gold_suppresses_fringe_most {α β : ι}
    {prefactor t : ℝ} (hp : 0 < prefactor) (ht : 0 < t) (hre : 0 < (D α β).re) :
    decoheredMeasure D (interferenceVisibility prefactor t .gold) α β
      < decoheredMeasure D (interferenceVisibility prefactor t .silver) α β := by
  unfold decoheredMeasure
  have hvgs : interferenceVisibility prefactor t .gold < interferenceVisibility prefactor t .silver :=
    lt_trans (interferenceVisibility_gold_least hp ht).1 (interferenceVisibility_gold_least hp ht).2
  nlinarith [mul_pos (sub_pos.mpr hvgs) hre]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.Thermodynamics.BoltzmannHTheorem
public import Physlib.Thermodynamics.KullbackLeiblerInformationGain
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic.Linarith
meta import Zil

/-!
# Total-correlation and continuum coarse-graining clocks for entropic time

The motivating two-level structure is

  microscopic joint-entropy conservation + asymmetric marginal conditions ⟹ a monotone clock.

For a bipartite state `p_XY` (two subsystems, or the split of an `N`-body state into "one particle" and
"the rest") the **total correlation** — the multi-information generated between the parts —

  `C(p_XY) = D(p_XY ‖ p_X ⊗ p_Y)`

(`totalCorrelation`, reusing `finiteMutualInformation`; `totalCorrelation_eq_klDivergence` connects it
to the product-type Gibbs API)

is nonnegative (`totalCorrelation_nonneg`, the subadditivity of entropy) and, by
`mutualInfo_eq_entropies`, equals the **negentropy gap**

  `C = S(X) + S(Y) − S(X,Y)`   (`totalCorrelation_eq_entropyGap`),

which is the bipartite (`N = 2`) analogue of the Grad/Layzer multi-information formula. This file does
not define arbitrary `N`-partite total correlation: its exact identity is only
`C = S(X) + S(Y) − S(X,Y)`.

The conditional monotonicity is a theorem of explicitly supplied premises (`totalCorrelation_monotone`):

  * **Liouville / reversible conservation** — the joint entropy `S(X,Y)` is invariant (`hLiouville`), and
  * **the Boltzmann `H`-theorem** — the reduced entropies `S(X), S(Y)` do not decrease (`hBoltzmann…`),

the total correlation cannot decrease. Reversible microscopic evolution funnels macroscopic information
into correlations in this bipartite model. Neither premise is constructed in this file.

Calibrating the imaginary action to this dimensionless correlation,

  `S_I = ħ·γ·C`   (`imaginaryAction`),   `τ_ent = S_I/ħ = γ·C`   (`entropicClock`),   `γ > 0`,

gives an entropic time that is nonnegative (`entropicClock_nonneg`), frozen **exactly** on the
independent sector `p_XY = p_X ⊗ p_Y` — the biconditional
`entropicClock_eq_zero_iff_independent`, whose reverse direction reuses the shared KL equality case
`klDivergence_eq_zero_iff` (the analogue of
`ComptonClock.EntropicProperDistance.reversible_iff_separable`) — and monotone for any pair of states
satisfying the stated entropy premises (`entropicClock_monotone`, `imaginaryAction_monotone`). Because `C` is
dimensionless, `S_I = ħγC` carries the units of action with no further constant.

Substitution into the existing master complex-action integrand gives the correlation-selected weight
`correlationComplexWeight`. Its modulus is exactly `exp (-τ_ent)`
(`correlationComplexWeight_norm`), is at most one (`correlationComplexWeight_norm_le_one`), decreases
when the conditional clock advances (`correlationComplexWeight_norm_antitone`), and equals one exactly on
the independent sector (`correlationComplexWeight_norm_eq_one_iff_independent`). Thus the information
arrow is connected to the amplitude level without defining a second path-integral formalism.

The total-correlation monotonicity is **conditional**: `Liouville`-invariance of the joint entropy and the `Boltzmann`
increase of the reduced entropies enter as hypotheses. No theorem from
`EntropicTime.EntropicDataProcessingHTheorem` or the Spohn layer is applied to
`totalCorrelation_monotone`; a concrete dynamics must separately discharge these premises. The
later marginalization result is a distinct, concrete data-processing theorem.

A complementary **remaining-disequilibrium clock** `τ_rem = γ·D(f ‖ f_eq)` (`remainingClock`) measures the
relative entropy still to be dissipated: nonnegative, and contracting whenever the state approaches
equilibrium (`remainingClock_antitone_of_contraction`), so the **accumulated** clock
`γ·[D(f₀‖f_eq) − D(f_t‖f_eq)]` (`accumulatedClock`) starts at zero and grows under the same contraction
(`accumulatedClock_nonneg_of_contraction`). For the concrete operation of forgetting the second
coordinate, `klDivergence_marginalFst_le` now reuses the log-sum H-theorem to prove the contraction;
`remainingClock_marginalFst_le` and `marginalizationClockGain_nonneg` therefore require no separately
supplied contraction certificate. The associated master-weight modulus increases monotonically as this
remaining distinguishability is discarded (`remainingClockComplexWeight_norm_marginalFst_mono`).

The same construction is then promoted to finite measures without rebuilding the analytic core.
`measureRemainingClock_map_le` directly applies the existing measure-theoretic `klDiv_map_le` theorem:
every measurable deterministic coarse-graining map contracts the real clock when the initial extended-
real KL is finite. `measureMapClockGain_nonneg` records the discarded information, and
`measureRemainingClockComplexWeight_norm_map_mono` transports that contraction to the master amplitude.
The stronger `measureRemainingClock_comp_le` and
`measureRemainingClockComplexWeight_norm_comp_mono` apply the same conclusions to an arbitrary common
Markov kernel, using `BoltzmannHTheorem.klDiv_comp_le` rather than reducing the channel to a function.
`MeasureKernelPositiveTimeSemigroup` promotes this to positive continuum channel time: relative entropy
to a stationary reference is antitone, interval clock production is nonnegative and additive, and the
master-weight modulus is monotone. Finally, `coarseGrainingComplexWeight_norm_eq_entropyProduced` uses
the repository's genuine
Markov-kernel `CoarseGrainingStep`: its amplitude damping is exactly the conditional KL entropy produced
by that packaged step. The channel choice remains explicit physical input.

* **§A — total correlation.** `totalCorrelation`, `totalCorrelation_eq_klDivergence`,
  `totalCorrelation_nonneg`, `totalCorrelation_eq_entropyGap`,
  `totalCorrelation_eq_zero_of_independent`, `klDivergence_eq_zero_iff`,
  `totalCorrelation_eq_zero_iff_independent`.
* **§B — the entropic clock and imaginary action.** `entropicClock`, `imaginaryAction`,
  `correlationComplexWeight`, `entropicClock_eq_imaginaryAction_div`, `correlationComplexWeight_norm`,
  `entropicClock_nonneg`, `correlationComplexWeight_norm_le_one`,
  `entropicClock_eq_zero_iff_independent`, `correlationComplexWeight_norm_eq_one_iff_independent`.
* **§C — conditional monotonicity.** `totalCorrelation_monotone`, `entropicClock_monotone`,
  `imaginaryAction_monotone`, `correlationComplexWeight_norm_antitone`.
* **§D — the remaining-disequilibrium clock.** `remainingClock`, `remainingClock_antitone_of_contraction`,
  `accumulatedClock`, `accumulatedClock_nonneg_of_contraction`, `klDivergence_marginalFst_le`,
  `remainingClock_marginalFst_le`, `marginalizationClockGain`,
  `remainingClockComplexWeight_norm_marginalFst_mono`.
* **§E — continuum measure clocks.** `measureRemainingClock`, `measureRemainingClock_map_le`,
  `measureMapClockGain`, `measureMapClockGain_nonneg`,
  `measureRemainingClockComplexWeight_norm_map_mono`, `measureRemainingClock_comp_le`,
  `measureKernelClockGain_nonneg`, `measureRemainingClockComplexWeight_norm_comp_mono`.
* **§F — positive-time continuum Markov semigroups.** `MeasureKernelPositiveTimeSemigroup`,
  `remainingClockAt_antitone`, `intervalClockGain_nonneg`, `intervalClockGain_cocycle`,
  `remainingClockComplexWeightAt_norm_monotone`.
* **§G — weakly continuous continuum dynamics.** `MeasureKernelC0Semigroup`,
  its concrete `identity`, `initial_observable_recovery`, `HasObservableGenerator`,
  `observableGenerator_eq_zero_of_fixedReference`, `HasRightClockProductionRate`,
  `rightClockProductionRate_nonneg`, `fixedReference_hasRightClockProductionRate_zero`, and
  `rightClockProductionRate_eq_zero_of_fixedReference`.
* **§H — Markov-kernel complex action.** `coarseGrainingComplexWeight`,
  `coarseGrainingComplexWeight_norm_le_one`,
  `coarseGrainingComplexWeight_norm_eq_entropyProduced`.

## References

* H. Grad, *Principles of the Kinetic Theory of Gases*, Handbuch der Physik XII (1958) — the full Liouville
  `H_N` is conserved while the reduced Boltzmann `H₁` decreases under molecular chaos.
* D. Layzer, *The Arrow of Time* — macroscopic information flows into microscopic correlations
  `C_N = H_N − N·H₁`, and the maximum entropy may itself grow with the geometry.
  Companions: `EntropicTime.RelativeEntropyGibbsInequality` (the `D ≥ 0` master inequality),
  `EntropicTime.EntropicDataProcessingHTheorem` (relative entropy contracts under coarse-graining),
  `Thermodynamics.BoltzmannHTheorem` (measure-theoretic KL maps and Markov-kernel steps),
  `ComptonClock.EntropicProperDistance` (`S_I = ħ log K` for the two-mode Schmidt case).
-/

set_option autoImplicit false

open Finset
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BoundedContinuousFunction

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.Thermodynamics.KullbackLeiblerInformationGain

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock

variable {ι : Type*} [Fintype ι]

/-! ### §A — the total correlation -/

/-- The **total correlation** of a bipartite state, reusing the repository's canonical
`finiteMutualInformation` after converting a product-typed joint distribution to curried form. -/
noncomputable def totalCorrelation {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ) : ℝ :=
  finiteMutualInformation (fun i j => pXY (i, j))

/-- The curried `finiteMutualInformation` carrier used by `totalCorrelation` is exactly the product-type
`klDivergence` from the shared Gibbs layer. This is the sole representation adapter between the two
pre-existing APIs. -/
theorem totalCorrelation_eq_klDivergence {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ) :
    totalCorrelation pXY =
      klDivergence pXY (fun z => marginalFst pXY z.1 * marginalSnd pXY z.2) := by
  simp [totalCorrelation, finiteMutualInformation, finiteKLDivergence₂, klDivergence,
    xMarginal, yMarginal, marginalFst, marginalSnd, Fintype.sum_prod_type]

/-- **[Total correlation is the negentropy gap]** `C = S(X) + S(Y) − S(X,Y)`: the generated correlation is
built from the joint (fine-grained) entropy and the marginal (reduced) entropies. It is the exact
bipartite identity used here, not an arbitrary `N`-body theorem. -/
theorem totalCorrelation_eq_entropyGap {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) :
    totalCorrelation pXY
      = entropy (marginalFst pXY) + entropy (marginalSnd pXY) - entropy pXY := by
  have hmX : ∀ i, 0 < marginalFst pXY i :=
    fun i => Finset.sum_pos (fun j _ => hpXY (i, j)) Finset.univ_nonempty
  have hmY : ∀ j, 0 < marginalSnd pXY j :=
    fun j => Finset.sum_pos (fun i _ => hpXY (i, j)) Finset.univ_nonempty
  rw [totalCorrelation_eq_klDivergence]
  exact mutualInfo_eq_entropies pXY hpXY hmX hmY

/-- **[Total correlation ≥ 0]** the generated bipartite correlation is nonnegative. This is a direct
corollary of the shared entropy-subadditivity theorem, so the marginal normalization proof is not
duplicated here. -/
theorem totalCorrelation_nonneg {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) (hsum : ∑ z, pXY z = 1) :
    0 ≤ totalCorrelation pXY := by
  rw [totalCorrelation_eq_entropyGap pXY hpXY]
  linarith [entropy_subadditive pXY hpXY hsum]

/-- **[Independent states have no correlation]** if the joint state factorizes into its marginals,
the total correlation vanishes. Independence is a statistical condition; it is not identified here
with every possible notion of reversible dynamics. -/
theorem totalCorrelation_eq_zero_of_independent {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ)
    (h : ∀ z, pXY z = marginalFst pXY z.1 * marginalSnd pXY z.2) :
    totalCorrelation pXY = 0 := by
  have hfun : (fun z => marginalFst pXY z.1 * marginalSnd pXY z.2) = pXY :=
    funext (fun z => (h z).symm)
  rw [totalCorrelation_eq_klDivergence]
  rw [hfun]
  exact klDivergence_self pXY

/-- **[Zero total correlation ⟺ independence]** the total correlation vanishes exactly when the joint
state factorizes into its marginals. This characterizes statistical independence, not reversibility in
general. -/
theorem totalCorrelation_eq_zero_iff_independent {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) (hsum : ∑ z, pXY z = 1) :
    totalCorrelation pXY = 0 ↔ ∀ z, pXY z = marginalFst pXY z.1 * marginalSnd pXY z.2 := by
  refine ⟨fun h0 => ?_, totalCorrelation_eq_zero_of_independent pXY⟩
  have hmX : ∀ i, 0 < marginalFst pXY i :=
    fun i => Finset.sum_pos (fun j _ => hpXY (i, j)) Finset.univ_nonempty
  have hmY : ∀ j, 0 < marginalSnd pXY j :=
    fun j => Finset.sum_pos (fun i _ => hpXY (i, j)) Finset.univ_nonempty
  have hXs : ∑ i, marginalFst pXY i = 1 := by
    simp only [marginalFst]; rw [← Fintype.sum_prod_type]; exact hsum
  have hYs : ∑ j, marginalSnd pXY j = 1 := by
    simp only [marginalSnd]; rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact hsum
  have hprodsum : ∑ z : ι × κ, marginalFst pXY z.1 * marginalSnd pXY z.2 = 1 := by
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum (marginalFst pXY) (marginalSnd pXY), hXs, hYs,
      mul_one]
  rw [totalCorrelation_eq_klDivergence] at h0
  have heq := (klDivergence_eq_zero_iff hpXY
    (fun z => mul_pos (hmX z.1) (hmY z.2)) hsum hprodsum).mp h0
  exact fun z => congrFun heq z

/-! ### §B — the entropic clock and the imaginary action -/

/-- The **entropic clock** `τ_ent = γ·C` read off the total correlation, with dimensionless calibration
`γ > 0`. This is `S_I/ħ`. -/
noncomputable def entropicClock {κ : Type*} [Fintype κ] (γ : ℝ) (pXY : ι × κ → ℝ) : ℝ :=
  γ * totalCorrelation pXY

/-- The **imaginary action** `S_I = ħ·γ·C = ħ·τ_ent` calibrated to the generated correlation. Since `C` is
dimensionless, `S_I` carries the units of action with no further constant. -/
noncomputable def imaginaryAction {κ : Type*} [Fintype κ] (ħ γ : ℝ) (pXY : ι × κ → ℝ) : ℝ :=
  ħ * entropicClock γ pXY

/-- The **correlation-selected complex-action weight** obtained by inserting
`S_I = ħ·γ·C(p_XY)` into the existing master path-integral weight.  Its real action is left
arbitrary: correlation controls the modulus, while `S_R` controls only the phase. -/
noncomputable def correlationComplexWeight {κ : Type*} [Fintype κ]
    (S_R ħ γ : ℝ) (pXY : ι × κ → ℝ) : ℂ :=
  complexActionPathIntegralWeight S_R (imaginaryAction ħ γ pXY) ħ

/-- **[Entropic time is imaginary action per quantum of action]** `τ_ent = S_I/ħ` for `ħ ≠ 0`. -/
theorem entropicClock_eq_imaginaryAction_div {κ : Type*} [Fintype κ] (ħ γ : ℝ) (hħ : ħ ≠ 0)
    (pXY : ι × κ → ℝ) : entropicClock γ pXY = imaginaryAction ħ γ pXY / ħ := by
  unfold imaginaryAction
  rw [mul_comm, mul_div_assoc, div_self hħ, mul_one]

/-- **[The complex-action modulus is the entropic-clock damping]**
`|w_C| = exp (-τ_ent)`.  This identifies the total-correlation clock with an observable
amplitude suppression in the already established master complex-action integrand; the result is
independent of the real action `S_R`. -/
theorem correlationComplexWeight_norm (S_R ħ γ : ℝ) (hħ : ħ ≠ 0)
    {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ) :
    ‖correlationComplexWeight S_R ħ γ pXY‖ = Real.exp (-entropicClock γ pXY) := by
  unfold correlationComplexWeight
  rw [master_modulus_is_kuiken, kuikenWeight,
    ← entropicClock_eq_imaginaryAction_div ħ γ hħ pXY]

/-- **[The clock never runs backward]** `τ_ent ≥ 0` for `γ ≥ 0`, from `totalCorrelation_nonneg`. -/
theorem entropicClock_nonneg {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ] (γ : ℝ) (hγ : 0 ≤ γ)
    (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) (hsum : ∑ z, pXY z = 1) :
    0 ≤ entropicClock γ pXY := by
  unfold entropicClock
  exact mul_nonneg hγ (totalCorrelation_nonneg pXY hpXY hsum)

/-- **[Correlation-selected amplitudes are contractive]** `|w_C| ≤ 1` for a normalized
positive joint state and nonnegative clock calibration. -/
theorem correlationComplexWeight_norm_le_one (S_R ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) (hsum : ∑ z, pXY z = 1) :
    ‖correlationComplexWeight S_R ħ γ pXY‖ ≤ 1 := by
  rw [correlationComplexWeight_norm S_R ħ γ hħ pXY, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (entropicClock_nonneg γ hγ pXY hpXY hsum)

/-- **[The imaginary action is nonnegative]** `S_I ≥ 0` for `ħ, γ ≥ 0`. -/
theorem imaginaryAction_nonneg {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ] (ħ γ : ℝ)
    (hħ : 0 ≤ ħ) (hγ : 0 ≤ γ) (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) (hsum : ∑ z, pXY z = 1) :
    0 ≤ imaginaryAction ħ γ pXY := by
  unfold imaginaryAction
  exact mul_nonneg hħ (entropicClock_nonneg γ hγ pXY hpXY hsum)

/-- **[The clock is frozen on independent states]** for `p_XY = p_X ⊗ p_Y`, the entropic clock reads
zero. This does not assert that independence exhausts reversible dynamics. -/
theorem entropicClock_frozen_of_independent {κ : Type*} [Fintype κ] (γ : ℝ) (pXY : ι × κ → ℝ)
    (h : ∀ z, pXY z = marginalFst pXY z.1 * marginalSnd pXY z.2) :
    entropicClock γ pXY = 0 := by
  unfold entropicClock
  rw [totalCorrelation_eq_zero_of_independent pXY h, mul_zero]

/-- **[The clock vanishes exactly on independent states]** for `γ ≠ 0`, the entropic clock vanishes
if and only if the joint state is independent. -/
theorem entropicClock_eq_zero_iff_independent {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (γ : ℝ) (hγ : γ ≠ 0) (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) (hsum : ∑ z, pXY z = 1) :
    entropicClock γ pXY = 0 ↔ ∀ z, pXY z = marginalFst pXY z.1 * marginalSnd pXY z.2 := by
  unfold entropicClock
  rw [mul_eq_zero, or_iff_right hγ, totalCorrelation_eq_zero_iff_independent pXY hpXY hsum]

/-- **[Unit modulus exactly characterizes independence]** for nonzero `ħ` and clock calibration,
the correlation-selected master weight has unit modulus exactly when the joint state factorizes into
its marginals. -/
theorem correlationComplexWeight_norm_eq_one_iff_independent (S_R ħ γ : ℝ)
    (hħ : ħ ≠ 0) (hγ : γ ≠ 0) {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) (hsum : ∑ z, pXY z = 1) :
    ‖correlationComplexWeight S_R ħ γ pXY‖ = 1 ↔
      ∀ z, pXY z = marginalFst pXY z.1 * marginalSnd pXY z.2 := by
  rw [correlationComplexWeight_norm S_R ħ γ hħ pXY, Real.exp_eq_one_iff,
    neg_eq_zero, entropicClock_eq_zero_iff_independent γ hγ pXY hpXY hsum]

/-! ### §C — conditional monotonicity -/

/-- **[Conditional total-correlation monotonicity]** the total correlation does not decrease for any
pair of states satisfying both conditions:

  * the joint (fine-grained) entropy is conserved — the Liouville-style input
    (`hLiouville : S(X,Y)_q = S(X,Y)_p`), and
  * does not decrease the reduced (marginal) entropies — the Boltzmann `H`-theorem
    (`hBoltzmannX`, `hBoltzmannY`).

Because `C = S(X) + S(Y) − S(X,Y)`, a constant joint term and nondecreasing marginal terms force `C` up.
The monotonicity of the entropic clock is a theorem of these two inputs, not a separate axiom. -/
theorem totalCorrelation_monotone {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (p q : ι × κ → ℝ) (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z)
    (hLiouville : entropy q = entropy p)
    (hBoltzmannX : entropy (marginalFst p) ≤ entropy (marginalFst q))
    (hBoltzmannY : entropy (marginalSnd p) ≤ entropy (marginalSnd q)) :
    totalCorrelation p ≤ totalCorrelation q := by
  rw [totalCorrelation_eq_entropyGap p hp, totalCorrelation_eq_entropyGap q hq]
  linarith

/-- **[The entropic clock advances]** `τ_ent(p) ≤ τ_ent(q)` under Liouville conservation of the joint
entropy and the Boltzmann increase of the reduced entropies, for `γ ≥ 0`. -/
theorem entropicClock_monotone {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ] (γ : ℝ) (hγ : 0 ≤ γ)
    (p q : ι × κ → ℝ) (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z)
    (hLiouville : entropy q = entropy p)
    (hBoltzmannX : entropy (marginalFst p) ≤ entropy (marginalFst q))
    (hBoltzmannY : entropy (marginalSnd p) ≤ entropy (marginalSnd q)) :
    entropicClock γ p ≤ entropicClock γ q := by
  unfold entropicClock
  exact mul_le_mul_of_nonneg_left
    (totalCorrelation_monotone p q hp hq hLiouville hBoltzmannX hBoltzmannY) hγ

/-- **[The imaginary action accumulates]** `S_I(p) ≤ S_I(q)` under the same two inputs, for `ħ, γ ≥ 0` —
the complex action's dissipative sector grows along the arrow. -/
theorem imaginaryAction_monotone {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ] (ħ γ : ℝ)
    (hħ : 0 ≤ ħ) (hγ : 0 ≤ γ) (p q : ι × κ → ℝ) (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z)
    (hLiouville : entropy q = entropy p)
    (hBoltzmannX : entropy (marginalFst p) ≤ entropy (marginalFst q))
    (hBoltzmannY : entropy (marginalSnd p) ≤ entropy (marginalSnd q)) :
    imaginaryAction ħ γ p ≤ imaginaryAction ħ γ q := by
  unfold imaginaryAction
  exact mul_le_mul_of_nonneg_left
    (entropicClock_monotone γ hγ p q hp hq hLiouville hBoltzmannX hBoltzmannY) hħ

/-- **[The conditional arrow suppresses the complex-action amplitude]** if Liouville conservation
and the reduced Boltzmann inequalities advance the total-correlation clock, then the modulus
of the corresponding master complex-action weight cannot increase. -/
theorem correlationComplexWeight_norm_antitone {κ : Type*} [Fintype κ]
    [Nonempty ι] [Nonempty κ] (S_Rp S_Rq ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (p q : ι × κ → ℝ) (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z)
    (hLiouville : entropy q = entropy p)
    (hBoltzmannX : entropy (marginalFst p) ≤ entropy (marginalFst q))
    (hBoltzmannY : entropy (marginalSnd p) ≤ entropy (marginalSnd q)) :
    ‖correlationComplexWeight S_Rq ħ γ q‖ ≤ ‖correlationComplexWeight S_Rp ħ γ p‖ := by
  rw [correlationComplexWeight_norm S_Rq ħ γ hħ q,
    correlationComplexWeight_norm S_Rp ħ γ hħ p, Real.exp_le_exp]
  exact neg_le_neg
    (entropicClock_monotone γ hγ p q hp hq hLiouville hBoltzmannX hBoltzmannY)

/-! ### §D — the remaining-disequilibrium clock -/

/-- **[Product-type data processing]** marginalizing the second coordinate cannot increase the
classical relative entropy. This is the product-typed adapter to the curried
`relativeEntropy_marginal_le`; unlike the earlier conditional clock theorem, its contraction premise is
proved from the log-sum inequality. -/
theorem klDivergence_marginalFst_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (p q : ι × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 < q z)
    (hpX : ∀ i, 0 < marginalFst p i) :
    klDivergence (marginalFst p) (marginalFst q) ≤ klDivergence p q := by
  simpa [klDivergence, marginalFst, Fintype.sum_prod_type] using
    (relativeEntropy_marginal_le (fun i j => p (i, j)) (fun i j => q (i, j))
      (fun i j => hp (i, j)) (fun i j => hq (i, j)) hpX)

/-- The **remaining-disequilibrium clock** `τ_rem = γ·D(f ‖ f_eq)`: the relative entropy still separating
the state from equilibrium, the "distance remaining to equilibrium". -/
noncomputable def remainingClock (γ : ℝ) (f feq : ι → ℝ) : ℝ := γ * klDivergence f feq

/-- **[Remaining disequilibrium ≥ 0]** `τ_rem ≥ 0`, and zero at equilibrium `f = f_eq`. -/
theorem remainingClock_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (f feq : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hfeq : ∀ i, 0 < feq i) (hfs : ∑ i, f i = 1) (hfeqs : ∑ i, feq i = 1) :
    0 ≤ remainingClock γ f feq := by
  unfold remainingClock
  exact mul_nonneg hγ (klDivergence_nonneg f feq hf hfeq hfs hfeqs)

/-- **[The remaining clock contracts toward equilibrium]** whenever the relative entropy to equilibrium
does not increase (`H`-theorem contraction), the remaining-disequilibrium clock does not increase. -/
theorem remainingClock_antitone_of_contraction (γ : ℝ) (hγ : 0 ≤ γ) (f₀ f_t feq : ι → ℝ)
    (hcontract : klDivergence f_t feq ≤ klDivergence f₀ feq) :
    remainingClock γ f_t feq ≤ remainingClock γ f₀ feq := by
  unfold remainingClock
  exact mul_le_mul_of_nonneg_left hcontract hγ

/-- **[Concrete H-theorem for the remaining clock]** marginalization itself discharges the relative-
entropy contraction premise, so the remaining clock decreases without an externally supplied
`hcontract`. -/
theorem remainingClock_marginalFst_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (γ : ℝ) (hγ : 0 ≤ γ) (p q : ι × κ → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 < q z) (hpX : ∀ i, 0 < marginalFst p i) :
    remainingClock γ (marginalFst p) (marginalFst q) ≤ remainingClock γ p q := by
  unfold remainingClock
  exact mul_le_mul_of_nonneg_left (klDivergence_marginalFst_le p q hp hq hpX) hγ

/-- The **accumulated relaxation clock** `γ·[D(f₀‖f_eq) − D(f_t‖f_eq)]`: the disequilibrium already
dissipated, oriented opposite to `remainingClock`. -/
noncomputable def accumulatedClock (γ : ℝ) (f₀ f_t feq : ι → ℝ) : ℝ :=
  γ * (klDivergence f₀ feq - klDivergence f_t feq)

/-- **[The accumulated clock starts at zero]** at the initial state no disequilibrium has yet dissipated. -/
theorem accumulatedClock_start (γ : ℝ) (f₀ feq : ι → ℝ) : accumulatedClock γ f₀ f₀ feq = 0 := by
  unfold accumulatedClock
  rw [sub_self, mul_zero]

/-- **[The accumulated clock advances under contraction]** `0 ≤ γ·[D(f₀‖f_eq) − D(f_t‖f_eq)]` whenever the
relative entropy to equilibrium contracts — the same `H`-theorem input, read as accumulated relaxation. -/
theorem accumulatedClock_nonneg_of_contraction (γ : ℝ) (hγ : 0 ≤ γ) (f₀ f_t feq : ι → ℝ)
    (hcontract : klDivergence f_t feq ≤ klDivergence f₀ feq) :
    0 ≤ accumulatedClock γ f₀ f_t feq := by
  unfold accumulatedClock
  exact mul_nonneg hγ (by linarith)

/-- The **clock gained by marginalization**: the scaled relative entropy discarded when the second
coordinate is forgotten. The two KL terms live on different finite carriers, so this definition cannot
be expressed using `accumulatedClock`, whose states share one index type. -/
noncomputable def marginalizationClockGain {κ : Type*} [Fintype κ]
    (γ : ℝ) (p q : ι × κ → ℝ) : ℝ :=
  γ * (klDivergence p q - klDivergence (marginalFst p) (marginalFst q))

/-- **[Exact remaining/gained-clock telescope]** the joint remaining clock is the marginal remaining
clock plus the information discarded by marginalization. -/
theorem remainingClock_eq_marginal_add_gain {κ : Type*} [Fintype κ]
    (γ : ℝ) (p q : ι × κ → ℝ) :
    remainingClock γ p q =
      remainingClock γ (marginalFst p) (marginalFst q) + marginalizationClockGain γ p q := by
  simp only [remainingClock, marginalizationClockGain]
  ring

/-- **[Concrete accumulated clock]** the clock gained by marginalization is nonnegative, directly from
the data-processing theorem rather than from a supplied contraction assumption. -/
theorem marginalizationClockGain_nonneg {κ : Type*} [Fintype κ] [Nonempty κ]
    (γ : ℝ) (hγ : 0 ≤ γ) (p q : ι × κ → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 < q z) (hpX : ∀ i, 0 < marginalFst p i) :
    0 ≤ marginalizationClockGain γ p q := by
  unfold marginalizationClockGain
  exact mul_nonneg hγ (sub_nonneg.mpr (klDivergence_marginalFst_le p q hp hq hpX))

/-- The existing master complex-action weight calibrated by the remaining-disequilibrium clock. -/
noncomputable def remainingClockComplexWeight (S_R ħ γ : ℝ) (f feq : ι → ℝ) : ℂ :=
  complexActionPathIntegralWeight S_R (ħ * remainingClock γ f feq) ħ

/-- **[Remaining-clock damping]** the modulus of the master weight is exactly the exponential of minus
the remaining clock. -/
theorem remainingClockComplexWeight_norm (S_R ħ γ : ℝ) (hħ : ħ ≠ 0) (f feq : ι → ℝ) :
    ‖remainingClockComplexWeight S_R ħ γ f feq‖ = Real.exp (-remainingClock γ f feq) := by
  rw [remainingClockComplexWeight, master_modulus_is_kuiken, kuikenWeight,
    mul_div_cancel_left₀ _ hħ]

/-- **[Amplitude recovery under coarse-graining]** because marginalization reduces the remaining KL
disequilibrium, the corresponding master-weight modulus cannot decrease. -/
theorem remainingClockComplexWeight_norm_marginalFst_mono
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (S_Rjoint S_Rmarg ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (p q : ι × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 < q z)
    (hpX : ∀ i, 0 < marginalFst p i) :
    ‖remainingClockComplexWeight S_Rjoint ħ γ p q‖ ≤
      ‖remainingClockComplexWeight S_Rmarg ħ γ (marginalFst p) (marginalFst q)‖ := by
  rw [remainingClockComplexWeight_norm S_Rjoint ħ γ hħ,
    remainingClockComplexWeight_norm S_Rmarg ħ γ hħ, Real.exp_le_exp]
  exact neg_le_neg (remainingClock_marginalFst_le γ hγ p q hp hq hpX)

/-! ### §E — continuum measure-theoretic clocks -/

/-- The continuum remaining-disequilibrium clock on finite measures. The extended-real Mathlib
divergence is converted to a real clock only when downstream theorems carry the required finiteness
hypothesis explicitly. -/
noncomputable def measureRemainingClock {α : Type*} [MeasurableSpace α]
    (γ : ℝ) (μ ν : Measure α) : ℝ :=
  γ * (klDiv μ ν).toReal

/-- **[Continuum data-processing clock]** pushing a state and its reference through the same measurable
coarse-graining map cannot increase the remaining clock. This is a direct adapter to the repository's
measure-theoretic `klDiv_map_le`, not a second proof of data processing. -/
theorem measureRemainingClock_map_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (γ : ℝ) (hγ : 0 ≤ γ) {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv μ ν ≠ ⊤) :
    measureRemainingClock γ (μ.map f) (ν.map f) ≤ measureRemainingClock γ μ ν := by
  unfold measureRemainingClock
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hfin
      (Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_map_le hf μ ν)) hγ

/-- The continuum clock gained by a measurable coarse-graining map. -/
noncomputable def measureMapClockGain {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (γ : ℝ) (f : α → β) (μ ν : Measure α) : ℝ :=
  γ * ((klDiv μ ν).toReal - (klDiv (μ.map f) (ν.map f)).toReal)

/-- **[Continuum clock telescope]** the original remaining clock is exactly the coarse remaining clock
plus the information discarded by the measurable map. -/
theorem measureRemainingClock_eq_map_add_gain
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (γ : ℝ) (f : α → β) (μ ν : Measure α) :
    measureRemainingClock γ μ ν =
      measureRemainingClock γ (μ.map f) (ν.map f) + measureMapClockGain γ f μ ν := by
  simp only [measureRemainingClock, measureMapClockGain]
  ring

/-- **[Continuum accumulated clock]** the clock gained by a measurable coarse-graining is nonnegative.
Finiteness of the initial KL is explicit because the clock is real-valued while Mathlib's continuum KL
lives in `ℝ≥0∞`. -/
theorem measureMapClockGain_nonneg
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (γ : ℝ) (hγ : 0 ≤ γ) {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv μ ν ≠ ⊤) :
    0 ≤ measureMapClockGain γ f μ ν := by
  unfold measureMapClockGain
  exact mul_nonneg hγ (sub_nonneg.mpr
    (ENNReal.toReal_mono hfin
      (Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_map_le hf μ ν)))

/-- **[Arbitrary-kernel continuum clock]** applying the same Markov kernel to a state and reference
cannot increase their remaining relative-entropy clock. -/
theorem measureRemainingClock_comp_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (γ : ℝ) (hγ : 0 ≤ γ) (κ : Kernel α β) [IsMarkovKernel κ]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv μ ν ≠ ⊤) :
    measureRemainingClock γ (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ measureRemainingClock γ μ ν := by
  unfold measureRemainingClock
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hfin
      (Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_comp_le κ μ ν)) hγ

/-- Information-clock gain discarded by an arbitrary Markov kernel. -/
noncomputable def measureKernelClockGain
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (γ : ℝ) (κ : Kernel α β) (μ ν : Measure α) : ℝ :=
  γ * ((klDiv μ ν).toReal - (klDiv (κ ∘ₘ μ) (κ ∘ₘ ν)).toReal)

/-- **[Arbitrary-kernel clock telescope]** the input clock equals the output clock plus the information
clock gain discarded by the channel. -/
theorem measureRemainingClock_eq_comp_add_gain
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (γ : ℝ) (κ : Kernel α β) (μ ν : Measure α) :
    measureRemainingClock γ μ ν =
      measureRemainingClock γ (κ ∘ₘ μ) (κ ∘ₘ ν) + measureKernelClockGain γ κ μ ν := by
  simp only [measureRemainingClock, measureKernelClockGain]
  ring

/-- **[Arbitrary-kernel accumulated clock]** the information-clock gain discarded by a Markov kernel
is nonnegative whenever the initial extended-real KL is finite. -/
theorem measureKernelClockGain_nonneg
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (γ : ℝ) (hγ : 0 ≤ γ) (κ : Kernel α β) [IsMarkovKernel κ]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv μ ν ≠ ⊤) :
    0 ≤ measureKernelClockGain γ κ μ ν := by
  unfold measureKernelClockGain
  exact mul_nonneg hγ (sub_nonneg.mpr
    (ENNReal.toReal_mono hfin
      (Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_comp_le κ μ ν)))

/-- The master complex-action weight calibrated by the continuum remaining clock. -/
noncomputable def measureRemainingClockComplexWeight
    {α : Type*} [MeasurableSpace α]
    (S_R ħ γ : ℝ) (μ ν : Measure α) : ℂ :=
  complexActionPathIntegralWeight S_R (ħ * measureRemainingClock γ μ ν) ħ

/-- **[Continuum remaining-clock damping]** the continuum master weight has modulus exactly
`exp (-γ D(μ ‖ ν))` after the explicit `ENNReal.toReal` conversion. -/
theorem measureRemainingClockComplexWeight_norm
    {α : Type*} [MeasurableSpace α]
    (S_R ħ γ : ℝ) (hħ : ħ ≠ 0) (μ ν : Measure α) :
    ‖measureRemainingClockComplexWeight S_R ħ γ μ ν‖ =
      Real.exp (-measureRemainingClock γ μ ν) := by
  rw [measureRemainingClockComplexWeight, master_modulus_is_kuiken, kuikenWeight,
    mul_div_cancel_left₀ _ hħ]

/-- **[Continuum amplitude recovery]** measurable coarse-graining cannot decrease the modulus of the
remaining-clock complex weight, because it cannot increase continuum KL distinguishability. -/
theorem measureRemainingClockComplexWeight_norm_map_mono
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (S_Rfine S_Rcoarse ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv μ ν ≠ ⊤) :
    ‖measureRemainingClockComplexWeight S_Rfine ħ γ μ ν‖ ≤
      ‖measureRemainingClockComplexWeight S_Rcoarse ħ γ (μ.map f) (ν.map f)‖ := by
  rw [measureRemainingClockComplexWeight_norm S_Rfine ħ γ hħ,
    measureRemainingClockComplexWeight_norm S_Rcoarse ħ γ hħ, Real.exp_le_exp]
  exact neg_le_neg (measureRemainingClock_map_le γ hγ hf μ ν hfin)

/-- **[Arbitrary-kernel amplitude recovery]** applying a common Markov kernel cannot decrease the
remaining-clock master-weight modulus. This is the full classical channel statement, beyond the
deterministic measurable-map special case. -/
theorem measureRemainingClockComplexWeight_norm_comp_mono
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (S_Rin S_Rout ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv μ ν ≠ ⊤) :
    ‖measureRemainingClockComplexWeight S_Rin ħ γ μ ν‖ ≤
      ‖measureRemainingClockComplexWeight S_Rout ħ γ (κ ∘ₘ μ) (κ ∘ₘ ν)‖ := by
  rw [measureRemainingClockComplexWeight_norm S_Rin ħ γ hħ,
    measureRemainingClockComplexWeight_norm S_Rout ħ γ hħ, Real.exp_le_exp]
  exact neg_le_neg (measureRemainingClock_comp_le γ hγ κ μ ν hfin)

/-! ### §F — positive-time continuum Markov semigroups -/

/-- A positive-time semigroup of Markov kernels on an arbitrary measurable state space.  This is
the continuum classical-channel analogue of the repository's finite-dimensional
`CPTPPositiveTimeSemigroup`; it deliberately carries no continuity or generator assumption. -/
structure MeasureKernelPositiveTimeSemigroup (α : Type*) [MeasurableSpace α] where
  /-- Markov transition kernel at nonnegative elapsed time. -/
  channel : NNReal → Kernel α α
  /-- Every transition kernel preserves probability mass. -/
  isMarkov_channel : ∀ t, IsMarkovKernel (channel t)
  /-- Zero elapsed time is the identity kernel. -/
  channel_zero : channel 0 = Kernel.id
  /-- Additive time is composition of transition kernels. -/
  channel_add : ∀ s t, channel (s + t) = channel s ∘ₖ channel t

namespace MeasureKernelPositiveTimeSemigroup

variable {α : Type*} [MeasurableSpace α] (S : MeasureKernelPositiveTimeSemigroup α)

instance (t : NNReal) : IsMarkovKernel (S.channel t) := S.isMarkov_channel t

/-- Evolve a measure through the Markov transition kernel at time `t`. -/
noncomputable def measureAt (μ : Measure α) (t : NNReal) : Measure α :=
  S.channel t ∘ₘ μ

/-- A reference measure is stationary when every semigroup channel fixes it. -/
def IsFixedReference (ν : Measure α) : Prop :=
  ∀ t, S.measureAt ν t = ν

@[simp]
theorem measureAt_zero (μ : Measure α) : S.measureAt μ 0 = μ := by
  rw [measureAt, S.channel_zero, Measure.id_comp]

/-- The kernel semigroup law transported to measures. -/
theorem measureAt_add (μ : Measure α) (s t : NNReal) :
    S.measureAt μ (s + t) = S.measureAt (S.measureAt μ t) s := by
  rw [measureAt, measureAt, measureAt, S.channel_add, ← Measure.comp_assoc]

/-- Continuum KL divergence to a stationary reference cannot increase at any positive time. -/
theorem klDiv_measureAt_le [StandardBorelSpace α] [Nonempty α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfix : S.IsFixedReference ν) (t : NNReal) :
    klDiv (S.measureAt μ t) ν ≤ klDiv μ ν := by
  calc
    klDiv (S.measureAt μ t) ν =
        klDiv (S.measureAt μ t) (S.measureAt ν t) := by rw [hfix t]
    _ ≤ klDiv μ ν :=
      Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_comp_le (S.channel t) μ ν

/-- Remaining continuum entropic clock along a Markov semigroup orbit. -/
noncomputable def remainingClockAt
    (γ : ℝ) (μ ν : Measure α) (t : NNReal) : ℝ :=
  measureRemainingClock γ (S.measureAt μ t) ν

/-- **[Continuum Markov H-theorem]** the remaining relative-entropy clock is antitone along a
positive-time Markov semigroup whenever the reference measure is stationary. -/
theorem remainingClockAt_antitone [StandardBorelSpace α] [Nonempty α]
    (γ : ℝ) (hγ : 0 ≤ γ) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfix : S.IsFixedReference ν) (hfin : klDiv μ ν ≠ ⊤) :
    Antitone (S.remainingClockAt γ μ ν) := by
  intro s t hst
  obtain ⟨u, rfl⟩ := exists_add_of_le hst
  letI : IsFiniteMeasure (S.measureAt μ s) := by
    unfold measureAt
    infer_instance
  have hfin_s : klDiv (S.measureAt μ s) ν ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (S.klDiv_measureAt_le μ ν hfix s)
  rw [remainingClockAt, remainingClockAt, add_comm, S.measureAt_add]
  calc
    measureRemainingClock γ (S.measureAt (S.measureAt μ s) u) ν =
        measureRemainingClock γ (S.measureAt (S.measureAt μ s) u) (S.measureAt ν u) := by
      rw [hfix u]
    _ ≤ measureRemainingClock γ (S.measureAt μ s) ν :=
      measureRemainingClock_comp_le γ hγ (S.channel u) (S.measureAt μ s) ν hfin_s

/-- Clock produced on the ordered interval `[s,t]`. -/
noncomputable def intervalClockGain
    (γ : ℝ) (μ ν : Measure α) (s t : NNReal) : ℝ :=
  S.remainingClockAt γ μ ν s - S.remainingClockAt γ μ ν t

/-- The interval gain plus the clock remaining at the final time equals the clock at the initial
time. -/
theorem intervalClockGain_add_residual_eq
    (γ : ℝ) (μ ν : Measure α) (s t : NNReal) :
    S.intervalClockGain γ μ ν s t + S.remainingClockAt γ μ ν t =
      S.remainingClockAt γ μ ν s := by
  unfold intervalClockGain
  ring

/-- Clock production is nonnegative on every ordered interval of a Markov semigroup with stationary
reference. -/
theorem intervalClockGain_nonneg [StandardBorelSpace α] [Nonempty α]
    (γ : ℝ) (hγ : 0 ≤ γ) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfix : S.IsFixedReference ν) (hfin : klDiv μ ν ≠ ⊤)
    {s t : NNReal} (hst : s ≤ t) :
    0 ≤ S.intervalClockGain γ μ ν s t := by
  exact sub_nonneg.mpr (S.remainingClockAt_antitone γ hγ μ ν hfix hfin hst)

/-- Interval clock production is an exact additive cocycle on adjacent intervals. -/
theorem intervalClockGain_cocycle
    (γ : ℝ) (μ ν : Measure α) (s t u : NNReal) :
    S.intervalClockGain γ μ ν s t + S.intervalClockGain γ μ ν t u =
      S.intervalClockGain γ μ ν s u := by
  simp only [intervalClockGain]
  ring

/-- The continuum complex-action weight evaluated along a Markov semigroup orbit. -/
noncomputable def remainingClockComplexWeightAt
    (S_R ħ γ : ℝ) (μ ν : Measure α) (t : NNReal) : ℂ :=
  measureRemainingClockComplexWeight S_R ħ γ (S.measureAt μ t) ν

/-- **[Continuum semigroup amplitude Lyapunov law]** the master-weight modulus is monotone along
positive detector time because the remaining KL clock is antitone. -/
theorem remainingClockComplexWeightAt_norm_monotone
    [StandardBorelSpace α] [Nonempty α]
    (S_R ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfix : S.IsFixedReference ν) (hfin : klDiv μ ν ≠ ⊤) :
    Monotone (fun t => ‖S.remainingClockComplexWeightAt S_R ħ γ μ ν t‖) := by
  intro s t hst
  change
    ‖measureRemainingClockComplexWeight S_R ħ γ (S.measureAt μ s) ν‖ ≤
      ‖measureRemainingClockComplexWeight S_R ħ γ (S.measureAt μ t) ν‖
  rw [
    measureRemainingClockComplexWeight_norm S_R ħ γ hħ,
    measureRemainingClockComplexWeight_norm S_R ħ γ hħ, Real.exp_le_exp]
  exact neg_le_neg (S.remainingClockAt_antitone γ hγ μ ν hfix hfin hst)

end MeasureKernelPositiveTimeSemigroup

/-! ### §G — weakly continuous continuum dynamics and its generator -/

/-- A continuum `C₀` Markov semigroup.  Strong continuity is weak continuity of every
probability-measure orbit, i.e. continuity against every bounded continuous observable.  This is
the measure-theoretic analogue of `CPTPC0Semigroup`; it does not assume a density or a finite state
space. -/
structure MeasureKernelC0Semigroup (α : Type*) [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] extends MeasureKernelPositiveTimeSemigroup α where
  /-- Every probability-measure orbit is weakly continuous: all bounded continuous observable
  expectations vary continuously. -/
  strong_continuous : ∀ (μ : ProbabilityMeasure α) (f : α →ᵇ ℝ),
    Continuous (fun t => ∫ x, f x ∂
      (toMeasureKernelPositiveTimeSemigroup.measureAt (μ : Measure α) t))

namespace MeasureKernelC0Semigroup

open Filter Set

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (S : MeasureKernelC0Semigroup α)

/-- The identity Markov kernel at every time, packaged as a concrete continuum `C₀` semigroup. -/
noncomputable def identity (α : Type*) [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] : MeasureKernelC0Semigroup α where
  channel := fun _ => Kernel.id
  isMarkov_channel := fun _ => inferInstance
  channel_zero := rfl
  channel_add := fun _ _ => by simp
  strong_continuous := fun μ f => by
    simpa [MeasureKernelPositiveTimeSemigroup.measureAt] using
      (continuous_const : Continuous (fun _ : NNReal => ∫ x, f x ∂(μ : Measure α)))

/-- The probability-measure orbit generated by a continuum `C₀` Markov semigroup. -/
noncomputable def probabilityAt (μ : ProbabilityMeasure α) (t : NNReal) :
    ProbabilityMeasure α :=
  ⟨S.toMeasureKernelPositiveTimeSemigroup.measureAt (μ : Measure α) t, by
    unfold MeasureKernelPositiveTimeSemigroup.measureAt
    infer_instance⟩

@[simp]
theorem probabilityAt_toMeasure (μ : ProbabilityMeasure α) (t : NNReal) :
    ((S.probabilityAt μ t : ProbabilityMeasure α) : Measure α) =
      S.toMeasureKernelPositiveTimeSemigroup.measureAt (μ : Measure α) t := rfl

/-- Expectation of a bounded continuous observable along a continuum Markov orbit. -/
noncomputable def observableExpectation (μ : ProbabilityMeasure α) (f : α →ᵇ ℝ)
    (t : NNReal) : ℝ :=
  ∫ x, f x ∂(S.probabilityAt μ t : ProbabilityMeasure α)

/-- Weak continuity and the identity law recover the initial expectation at time zero. -/
theorem initial_observable_recovery (μ : ProbabilityMeasure α) (f : α →ᵇ ℝ) :
    Tendsto (fun t => S.observableExpectation μ f t) (nhds 0)
      (nhds (∫ x, f x ∂(μ : Measure α))) := by
  have h : Tendsto
      (fun t => ∫ x, f x ∂
        (S.toMeasureKernelPositiveTimeSemigroup.measureAt (μ : Measure α) t))
      (nhds 0)
      (nhds (∫ x, f x ∂
        (S.toMeasureKernelPositiveTimeSemigroup.measureAt (μ : Measure α) 0))) :=
    (S.strong_continuous μ f).continuousAt
  simpa only [observableExpectation, probabilityAt_toMeasure,
    MeasureKernelPositiveTimeSemigroup.measureAt_zero] using h

/-- Weak `C₀` continuity is equivalently continuity of expectation against every bounded
continuous real observable. -/
theorem continuous_observableExpectation (μ : ProbabilityMeasure α) (f : α →ᵇ ℝ) :
    Continuous (fun t => ∫ x, f x ∂(S.probabilityAt μ t : ProbabilityMeasure α)) :=
  S.strong_continuous μ f

/-- A weak infinitesimal generator, identified by right difference quotients of every bounded
continuous observable along every probability-measure orbit. -/
def HasObservableGenerator
    (A : ProbabilityMeasure α → (α →ᵇ ℝ) → ℝ) : Prop :=
  ∀ (μ : ProbabilityMeasure α) (f : α →ᵇ ℝ),
    Tendsto
      (fun t : NNReal => (t : ℝ)⁻¹ *
        (S.observableExpectation μ f t - S.observableExpectation μ f 0))
      (nhdsWithin 0 (Ioi 0)) (nhds (A μ f))

/-- The concrete identity continuum semigroup has the zero weak observable generator. -/
theorem identity_hasObservableGenerator_zero :
    (identity α).HasObservableGenerator (fun _ _ => 0) := by
  intro μ f
  simp [observableExpectation, probabilityAt, identity,
    MeasureKernelPositiveTimeSemigroup.measureAt]

/-- A stationary reference measure gives a constant probability-measure orbit. -/
theorem probabilityAt_eq_of_fixedReference (μ : ProbabilityMeasure α)
    (hfix : S.toMeasureKernelPositiveTimeSemigroup.IsFixedReference (μ : Measure α))
    (t : NNReal) :
    S.probabilityAt μ t = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  exact hfix t

/-- Every identified weak generator vanishes on a stationary reference.  This is the continuum
fixed-point/generator balance law, with no finite-state or density assumption. -/
theorem observableGenerator_eq_zero_of_fixedReference
    (A : ProbabilityMeasure α → (α →ᵇ ℝ) → ℝ)
    (hgen : S.HasObservableGenerator A) (μ : ProbabilityMeasure α)
    (hfix : S.toMeasureKernelPositiveTimeSemigroup.IsFixedReference (μ : Measure α))
    (f : α →ᵇ ℝ) :
    A μ f = 0 := by
  have heq :
      (fun t : NNReal => (t : ℝ)⁻¹ *
        (S.observableExpectation μ f t - S.observableExpectation μ f 0)) =
        fun _ => 0 := by
    funext t
    rw [observableExpectation, observableExpectation,
      S.probabilityAt_eq_of_fixedReference μ hfix t,
      S.probabilityAt_eq_of_fixedReference μ hfix 0]
    simp
  have hzero : Tendsto
      (fun t : NNReal => (t : ℝ)⁻¹ *
        (S.observableExpectation μ f t - S.observableExpectation μ f 0))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    rw [heq]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique (hgen μ f) hzero)

/-- The right derivative of the interval clock at zero, formulated without assuming differentiable
densities.  It is the continuum analogue of `finiteSpohnIntervalProduction_rate_tendsto`. -/
def HasRightClockProductionRate
    (γ : ℝ) (μ ν : Measure α) (rate : ℝ) : Prop :=
  Tendsto
    (fun t : NNReal => (t : ℝ)⁻¹ *
      S.toMeasureKernelPositiveTimeSemigroup.intervalClockGain γ μ ν 0 t)
    (nhdsWithin 0 (Ioi 0)) (nhds rate)

/-- A stationary reference has an actually constructed zero right clock-production rate when it is
used as both state and reference.  No differentiability of a density is required. -/
theorem fixedReference_hasRightClockProductionRate_zero
    (γ : ℝ) (ν : Measure α)
    (hfix : S.toMeasureKernelPositiveTimeSemigroup.IsFixedReference ν) :
    S.HasRightClockProductionRate γ ν ν 0 := by
  have heq :
      (fun t : NNReal => (t : ℝ)⁻¹ *
        S.toMeasureKernelPositiveTimeSemigroup.intervalClockGain γ ν ν 0 t) =
        fun _ => 0 := by
    funext t
    simp only [MeasureKernelPositiveTimeSemigroup.intervalClockGain,
      MeasureKernelPositiveTimeSemigroup.remainingClockAt]
    rw [hfix 0, hfix t]
    ring
  rw [HasRightClockProductionRate, heq]
  exact tendsto_const_nhds

/-- Any supplied right production rate at a stationary reference is forced to equal zero, because
the same difference quotient already has the constructed zero limit. -/
theorem rightClockProductionRate_eq_zero_of_fixedReference
    (γ : ℝ) (ν : Measure α)
    (hfix : S.toMeasureKernelPositiveTimeSemigroup.IsFixedReference ν)
    (rate : ℝ) (hrate : S.HasRightClockProductionRate γ ν ν rate) :
    rate = 0 :=
  tendsto_nhds_unique hrate (S.fixedReference_hasRightClockProductionRate_zero γ ν hfix)

/-- Every probability measure is stationary for the concrete identity continuum semigroup. -/
theorem identity_isFixedReference (μ : Measure α) :
    (identity α).toMeasureKernelPositiveTimeSemigroup.IsFixedReference μ := by
  intro t
  simp [MeasureKernelPositiveTimeSemigroup.measureAt, identity]

/-- The identity continuum dynamics has a constructed zero right clock-production rate for every
state/reference pair with the same measure. -/
theorem identity_hasRightClockProductionRate_zero (γ : ℝ) (μ : Measure α) :
    (identity α).HasRightClockProductionRate γ μ μ 0 :=
  (identity α).fixedReference_hasRightClockProductionRate_zero γ μ
    (identity_isFixedReference μ)

/-- **[Continuum differential H-theorem]** whenever the right clock-production rate exists, it is
nonnegative.  The proof is the limit of the already proved nonnegative interval production and does
not postulate a second entropy-production functional. -/
theorem rightClockProductionRate_nonneg
    [StandardBorelSpace α] [Nonempty α]
    (γ : ℝ) (hγ : 0 ≤ γ) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfix : S.toMeasureKernelPositiveTimeSemigroup.IsFixedReference ν)
    (hfin : klDiv μ ν ≠ ⊤) (rate : ℝ)
    (hrate : S.HasRightClockProductionRate γ μ ν rate) :
    0 ≤ rate := by
  apply ge_of_tendsto hrate
  filter_upwards [] with t
  exact mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg t))
    (S.toMeasureKernelPositiveTimeSemigroup.intervalClockGain_nonneg
      γ hγ μ ν hfix hfin bot_le)

end MeasureKernelC0Semigroup

/-! ### §H — genuine Markov-kernel coarse-graining and complex action -/

/-- The master complex-action weight whose imaginary action is the entropic proper-time advance of an
existing measure-theoretic `CoarseGrainingStep`. -/
noncomputable def coarseGrainingComplexWeight
    (S : Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep)
    (S_R ħ : ℝ) : ℂ :=
  complexActionPathIntegralWeight S_R (ħ * S.tauEnt) ħ

/-- **[Kernel coarse-graining damping]** the Markov-step master weight has modulus exactly the
exponential of minus the derived entropic proper-time advance. -/
theorem coarseGrainingComplexWeight_norm
    (S : Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep)
    (S_R ħ : ℝ) (hħ : ħ ≠ 0) :
    ‖coarseGrainingComplexWeight S S_R ħ‖ = Real.exp (-S.tauEnt) := by
  rw [coarseGrainingComplexWeight, master_modulus_is_kuiken, kuikenWeight,
    mul_div_cancel_left₀ _ hħ]

/-- **[Kernel H-theorem as amplitude contraction]** every packaged coarse-graining step produces a
contractive complex-action amplitude. -/
theorem coarseGrainingComplexWeight_norm_le_one
    (S : Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep)
    (S_R ħ : ℝ) (hħ : ħ ≠ 0) :
    ‖coarseGrainingComplexWeight S S_R ħ‖ ≤ 1 := by
  rw [coarseGrainingComplexWeight_norm S S_R ħ hħ, Real.exp_le_one_iff]
  exact neg_nonpos.mpr S.tauEnt_nonneg

/-- **[Entropy-production identity at amplitude level]** the same modulus is the exponential of minus
the conditional KL entropy produced by the Markov coarse-graining step. -/
theorem coarseGrainingComplexWeight_norm_eq_entropyProduced
    (S : Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep)
    (S_R ħ : ℝ) (hħ : ħ ≠ 0) :
    ‖coarseGrainingComplexWeight S S_R ħ‖ = Real.exp (-S.entropyProduced) := by
  rw [coarseGrainingComplexWeight_norm S S_R ħ hħ, S.tauEnt_eq_entropyProduced]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock

end

/- ZIL-BEGIN -/

open Zil

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_nonneg where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_klDivergence where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_entropyGap where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.entropy]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_zero_of_independent where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalFst,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalSnd]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_eq_imaginaryAction_div where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.imaginaryAction]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_nonneg where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_monotone where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_monotone where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.imaginaryAction_monotone where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.imaginaryAction]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_antitone_of_contraction where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.accumulatedClock_nonneg_of_contraction where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.accumulatedClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.klDivergence_marginalFst_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalFst]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_marginalFst_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalFst]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_eq_marginal_add_gain where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.marginalizationClockGain]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.marginalizationClockGain_nonneg where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.marginalizationClockGain]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight_norm where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight_norm_marginalFst_mono where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalFst]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_map_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_eq_map_add_gain where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureMapClockGain]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureMapClockGain_nonneg where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureMapClockGain]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm_map_mono where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_comp_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_eq_comp_add_gain where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureKernelClockGain]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureKernelClockGain_nonneg where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureKernelClockGain]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm_comp_mono where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.measureAt_add where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.measureAt]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockAt_antitone where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockAt]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain_nonneg where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain_cocycle where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockComplexWeightAt_norm_monotone where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockComplexWeightAt]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.initial_observable_recovery where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.observableExpectation]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.observableGenerator_eq_zero_of_fixedReference where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.HasObservableGenerator]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.rightClockProductionRate_nonneg where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.HasRightClockProductionRate]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity_hasObservableGenerator_zero where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.HasObservableGenerator]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.fixedReference_hasRightClockProductionRate_zero where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.HasRightClockProductionRate]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.rightClockProductionRate_eq_zero_of_fixedReference where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.HasRightClockProductionRate]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity_isFixedReference where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight,
    Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep.tauEnt]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm_le_one where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm_eq_entropyProduced where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight,
    Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep.entropyProduced]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_zero_iff_independent where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalFst,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalSnd]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_eq_zero_iff_independent where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalFst,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalSnd]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_le_one where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_eq_one_iff_independent where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalFst,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalSnd]

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_antitone where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight]

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_entropyGap where
  formalizes @ "claim:bipartite-total-correlation-equals-the-sum-of-marginal-entropies-minus-the-joint-entropy",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:layzer-arrow-of-time-macroscopic-to-microscopic-information-flow",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.mutualInfo_eq_entropies"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_klDivergence where
  formalizes @ "claim:the-curried-finite-mutual-information-and-product-type-kl-total-correlation-representations-are-identical",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.KullbackLeiblerInformationGain.finiteMutualInformation",
  caveat @ "claim:representation-adapter-only-no-new-information-theoretic-law"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_monotone where
  formalizes @ "claim:bipartite-total-correlation-is-monotone-conditionally-on-joint-entropy-conservation-and-both-marginal-entropy-increases",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:bipartite-total-correlation-equals-the-sum-of-marginal-entropies-minus-the-joint-entropy",
  supported_by @ "paper:grad-1958-principles-of-the-kinetic-theory-of-gases-reversible-hn-conserved-reduced-h1-decreases",
  caveat @ "claim:monotonicity-is-conditional-on-the-explicit-liouville-and-reduced-boltzmann-entropy-premises"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.imaginaryAction_monotone where
  formalizes @ "claim:the-imaginary-action-s-i-equals-hbar-gamma-total-correlation-accumulates-along-the-arrow-the-dissipative-sector-of-the-complex-action-grows",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:bipartite-total-correlation-is-monotone-conditionally-on-joint-entropy-conservation-and-both-marginal-entropy-increases",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_monotone",
  caveat @ "claim:the-identification-s-i-equals-hbar-gamma-c-is-model-calibration-not-an-independent-empirical-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_zero_iff_independent where
  formalizes @ "claim:full-support-bipartite-total-correlation-vanishes-if-and-only-if-the-state-is-independent",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_eq_zero_iff",
  caveat @ "claim:statistical-independence-is-not-by-itself-an-equivalence-with-general-reversible-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm where
  formalizes @ "claim:the-master-complex-action-weight-calibrated-by-total-correlation-has-modulus-exactly-exp-minus-entropic-time",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_le_one where
  formalizes @ "claim:a-normalized-positive-bipartite-state-produces-a-contractive-correlation-selected-complex-action-amplitude",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-master-complex-action-weight-calibrated-by-total-correlation-has-modulus-exactly-exp-minus-entropic-time",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_nonneg"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_eq_one_iff_independent where
  formalizes @ "claim:the-correlation-selected-complex-action-amplitude-has-unit-modulus-if-and-only-if-the-bipartite-state-factorizes",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:finite-classical-full-support-bipartite-distributions-not-a-type-three-quantum-factor-independence-theorem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_eq_zero_iff_independent"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_antitone where
  formalizes @ "claim:conditional-total-correlation-growth-makes-the-master-complex-action-amplitude-monotone-nonincreasing",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:bipartite-total-correlation-is-monotone-conditionally-on-joint-entropy-conservation-and-both-marginal-entropy-increases",
  caveat @ "claim:amplitude-suppression-is-conditional-on-the-explicit-liouville-and-boltzmann-premises-not-a-construction-of-the-underlying-dynamics",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_monotone"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.klDivergence_marginalFst_le where
  formalizes @ "claim:product-typed-classical-relative-entropy-cannot-increase-when-the-second-coordinate-is-marginalized",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem.relativeEntropy_marginal_le",
  caveat @ "claim:finite-classical-coordinate-marginalization-not-a-general-stochastic-or-quantum-channel"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_marginalFst_le where
  formalizes @ "claim:the-remaining-relative-entropy-clock-contracts-under-coordinate-marginalization-without-an-external-contraction-certificate",
  epistemic_status @ "consistency-identity",
  requires @ "claim:product-typed-classical-relative-entropy-cannot-increase-when-the-second-coordinate-is-marginalized",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.klDivergence_marginalFst_le"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_eq_marginal_add_gain where
  formalizes @ "claim:joint-remaining-clock-equals-marginal-remaining-clock-plus-the-clock-gain-discarded-by-marginalization",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.marginalizationClockGain",
  caveat @ "claim:exact-algebraic-telescope-not-an-independent-physical-law"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.marginalizationClockGain_nonneg where
  formalizes @ "claim:the-clock-gain-discarded-by-coordinate-marginalization-is-nonnegative",
  epistemic_status @ "consistency-identity",
  requires @ "claim:product-typed-classical-relative-entropy-cannot-increase-when-the-second-coordinate-is-marginalized",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.klDivergence_marginalFst_le"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight_norm where
  formalizes @ "claim:the-master-complex-action-weight-calibrated-by-remaining-relative-entropy-has-modulus-exp-minus-the-remaining-clock",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight_norm_marginalFst_mono where
  formalizes @ "claim:coordinate-marginalization-monotonically-recovers-the-remaining-clock-master-amplitude-as-distinguishability-is-discarded",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-remaining-relative-entropy-clock-contracts-under-coordinate-marginalization-without-an-external-contraction-certificate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight_norm",
  caveat @ "claim:finite-classical-amplitude-bridge-not-a-dynamical-decoherence-or-recoherence-model"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_map_le where
  formalizes @ "claim:the-continuum-relative-entropy-remaining-clock-cannot-increase-under-a-measurable-coarse-graining-map",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_map_le",
  caveat @ "claim:real-valued-clock-requires-finite-initial-extended-real-kl-and-the-operation-is-a-deterministic-measurable-map"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_eq_map_add_gain where
  formalizes @ "claim:the-continuum-remaining-clock-equals-the-coarse-clock-plus-the-information-loss-clock-gain",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureMapClockGain",
  caveat @ "claim:exact-algebraic-telescope-not-an-independent-physical-law"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureMapClockGain_nonneg where
  formalizes @ "claim:the-continuum-clock-gain-under-a-measurable-coarse-graining-map-is-nonnegative",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-continuum-relative-entropy-remaining-clock-cannot-increase-under-a-measurable-coarse-graining-map",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_map_le"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm where
  formalizes @ "claim:the-continuum-relative-entropy-clock-calibrates-the-master-complex-action-modulus-as-exp-minus-the-remaining-clock",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm_map_mono where
  formalizes @ "claim:measurable-continuum-coarse-graining-monotonically-recovers-the-relative-entropy-clock-master-amplitude",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-continuum-relative-entropy-remaining-clock-cannot-increase-under-a-measurable-coarse-graining-map",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm",
  caveat @ "claim:amplitude-monotonicity-is-induced-by-information-discarding-not-a-unitary-real-time-propagation-law"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_comp_le where
  formalizes @ "claim:the-continuum-relative-entropy-remaining-clock-cannot-increase-when-state-and-reference-pass-through-the-same-arbitrary-markov-kernel",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_comp_le",
  caveat @ "claim:classical-markov-kernel-data-processing-not-a-quantum-cptp-or-type-three-relative-entropy-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_eq_comp_add_gain where
  formalizes @ "claim:the-continuum-input-clock-equals-the-markov-output-clock-plus-the-information-clock-gain-discarded-by-the-kernel",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureKernelClockGain",
  caveat @ "claim:exact-algebraic-telescope-not-an-independent-physical-law"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureKernelClockGain_nonneg where
  formalizes @ "claim:the-continuum-information-clock-gain-discarded-by-an-arbitrary-markov-kernel-is-nonnegative",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-continuum-relative-entropy-remaining-clock-cannot-increase-when-state-and-reference-pass-through-the-same-arbitrary-markov-kernel",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_comp_le"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm_comp_mono where
  formalizes @ "claim:an-arbitrary-common-markov-kernel-monotonically-recovers-the-continuum-relative-entropy-clock-master-amplitude",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-continuum-relative-entropy-remaining-clock-cannot-increase-when-state-and-reference-pass-through-the-same-arbitrary-markov-kernel",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_comp_le",
  caveat @ "claim:classical-channel-amplitude-monotonicity-not-a-unitary-real-time-or-quantum-channel-law"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.measureAt_add where
  formalizes @ "claim:a-positive-time-continuum-markov-kernel-semigroup-acts-on-measures-by-the-exact-additive-time-composition-law",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:MeasureTheory.Measure.comp_assoc"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockAt_antitone where
  formalizes @ "claim:continuum-relative-entropy-to-a-stationary-reference-is-antitone-along-a-positive-time-markov-kernel-semigroup",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:a-supplied-positive-time-markov-kernel-semigroup-and-stationary-reference-measure",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_comp_le",
  caveat @ "claim:data-processing-H-theorem-conditional-on-supplied-semigroup-stationarity-and-finite-initial-kl-not-a-construction-of-a-generator"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain_nonneg where
  formalizes @ "claim:every-ordered-interval-of-a-stationary-reference-continuum-markov-semigroup-has-nonnegative-relative-entropy-clock-production",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:continuum-relative-entropy-to-a-stationary-reference-is-antitone-along-a-positive-time-markov-kernel-semigroup",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockAt_antitone",
  caveat @ "claim:the-identification-of-relative-entropy-production-with-a-physical-clock-rate-is-a-model-ansatz-the-theorem-itself-is-the-exact-relative-entropy-monotonicity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain_cocycle where
  formalizes @ "claim:continuum-markov-interval-clock-production-is-exactly-additive-on-adjacent-time-intervals",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain",
  caveat @ "claim:algebraic-difference-cocycle-not-an-independent-physical-production-law"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockComplexWeightAt_norm_monotone where
  formalizes @ "claim:the-continuum-complex-action-master-weight-modulus-is-a-lyapunov-monotone-along-stationary-reference-markov-detector-time",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:continuum-relative-entropy-to-a-stationary-reference-is-antitone-along-a-positive-time-markov-kernel-semigroup",
  caveat @ "claim:complex-weight-modulus-consequence-not-a-construction-of-GKLS-dynamics-or-a-quantum-measurement-instrument",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockAt_antitone"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.initial_observable_recovery where
  formalizes @ "claim:a-weakly-continuous-continuum-markov-semigroup-recovers-every-bounded-continuous-observable-expectation-at-zero-time",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:a-supplied-weakly-continuous-positive-time-markov-kernel-semigroup",
  caveat @ "claim:C0-carrier-over-arbitrary-probability-measures-not-a-construction-of-a-specific-physical-transition-kernel",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.probabilityAt_toMeasure"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.observableGenerator_eq_zero_of_fixedReference where
  formalizes @ "claim:every-identified-weak-observable-generator-annihilates-each-stationary-reference-probability-measure",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:a-supplied-weak-generator-limit-and-stationary-reference",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.generator_eq_zero_of_fixedPoint",
  caveat @ "claim:continuum-fixed-point-generator-balance-not-existence-or-uniqueness-of-a-generator-for-every-C0-semigroup"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.rightClockProductionRate_nonneg where
  formalizes @ "claim:an-existing-right-differential-relative-entropy-clock-production-rate-is-nonnegative-for-a-stationary-reference-continuum-markov-semigroup",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:a-supplied-weak-C0-markov-semigroup-stationary-reference-finite-initial-kl-and-existing-right-rate-limit",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain_nonneg",
  caveat @ "claim:limit-consequence-of-the-interval-H-theorem-not-a-proof-that-the-rate-exists-or-equals-a-specific-GKLS-Spohn-functional"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity_hasObservableGenerator_zero where
  formalizes @ "claim:the-concrete-identity-continuum-C0-markov-semigroup-has-the-zero-weak-observable-generator",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:reversible-zero-generator-control-case-not-a-nontrivial-relaxation-or-GKLS-dynamics",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.fixedReference_hasRightClockProductionRate_zero where
  formalizes @ "claim:a-stationary-reference-constructs-an-existing-zero-right-relative-entropy-clock-production-rate",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:stationarity-of-the-reference-under-the-supplied-continuum-C0-semigroup",
  caveat @ "claim:equilibrium-rate-existence-only-not-differentiability-or-a-nonzero-nonequilibrium-Spohn-formula",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.rightClockProductionRate_eq_zero_of_fixedReference where
  formalizes @ "claim:any-right-clock-production-rate-at-a-stationary-reference-is-uniquely-zero",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:a-stationary-reference-constructs-an-existing-zero-right-relative-entropy-clock-production-rate",
  caveat @ "claim:stationary-equality-case-not-an-identification-of-nonequilibrium-production-with-a-GKLS-functional",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.fixedReference_hasRightClockProductionRate_zero"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity_isFixedReference where
  formalizes @ "claim:every-measure-is-stationary-under-the-concrete-identity-continuum-C0-semigroup",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:identity-control-semigroup-not-a-physical-thermalization-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.measureAt"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm where
  formalizes @ "claim:a-measure-theoretic-markov-coarse-graining-step-calibrates-the-master-complex-action-modulus-as-exp-minus-its-derived-entropic-proper-time",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep.tauEnt"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm_le_one where
  formalizes @ "claim:the-master-amplitude-of-every-packaged-markov-coarse-graining-step-is-contractive",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep.tauEnt_nonneg",
  caveat @ "claim:the-coarse-graining-channel-pair-and-finite-kl-datum-are-explicit-physical-inputs"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm_eq_entropyProduced where
  formalizes @ "claim:the-markov-coarse-graining-master-amplitude-is-exp-minus-the-conditional-kl-entropy-produced",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep.tauEnt_eq_entropyProduced",
  caveat @ "claim:exact-identity-for-the-packaged-step-not-a-derivation-of-the-environment-channel-choice"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_nonneg where
  formalizes @ "claim:the-bipartite-total-correlation-of-a-full-support-normalized-joint-state-is-nonnegative-so-the-clock-it-calibrates-has-a-floor",
  epistemic_status @ "consistency-identity",
  requires @ "claim:bipartite-total-correlation-equals-the-sum-of-marginal-entropies-minus-the-joint-entropy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.entropy_subadditive",
  caveat @ "nonnegativity-is-subadditivity-of-the-shannon-entropy-it-does-not-by-itself-supply-a-direction-of-time"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_zero_of_independent where
  formalizes @ "claim:a-joint-state-that-factorizes-into-its-marginals-has-zero-total-correlation-so-independence-freezes-the-clock",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_self",
  caveat @ "independence-is-a-statistical-condition-it-is-not-identified-here-with-every-notion-of-reversible-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_eq_imaginaryAction_div where
  formalizes @ "claim:the-entropic-clock-reading-is-the-imaginary-action-per-quantum-of-action-tau-ent-equals-s-i-over-hbar",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight",
  caveat @ "the-identification-s-i-equals-hbar-gamma-c-is-model-calibration-so-this-divides-a-calibrated-quantity-rather-than-deriving-the-calibration"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_nonneg where
  formalizes @ "claim:the-entropic-clock-never-runs-backward-for-nonnegative-calibration-gamma",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-bipartite-total-correlation-of-a-full-support-normalized-joint-state-is-nonnegative-so-the-clock-it-calibrates-has-a-floor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.entropy_subadditive",
  caveat @ "the-floor-is-inherited-from-total-correlation-nonnegativity-and-from-the-sign-convention-on-gamma-not-from-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_monotone where
  formalizes @ "claim:the-entropic-clock-advances-conditionally-on-joint-entropy-conservation-and-both-marginal-entropy-increases",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:bipartite-total-correlation-is-monotone-conditionally-on-joint-entropy-conservation-and-both-marginal-entropy-increases",
  supported_by @ "paper:grad-1958-principles-of-the-kinetic-theory-of-gases-reversible-hn-conserved-reduced-h1-decreases",
  caveat @ "monotonicity-is-conditional-on-the-explicit-liouville-and-reduced-boltzmann-entropy-premises-it-is-not-an-unconditional-arrow-of-time"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_eq_zero_iff_independent where
  formalizes @ "claim:for-nonzero-calibration-the-entropic-clock-vanishes-exactly-on-independent-joint-states",
  epistemic_status @ "consistency-identity",
  requires @ "claim:full-support-bipartite-total-correlation-vanishes-if-and-only-if-the-state-is-independent",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_eq_zero_iff",
  caveat @ "the-nonzero-calibration-hypothesis-is-what-makes-this-an-equivalence-at-gamma-equals-zero-the-clock-is-frozen-on-every-state"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_antitone_of_contraction where
  formalizes @ "claim:the-remaining-disequilibrium-clock-does-not-increase-whenever-the-relative-entropy-to-equilibrium-contracts",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_map_le",
  caveat @ "the-relative-entropy-contraction-is-an-explicit-premise-here-the-concrete-marginalization-instance-that-discharges-it-is-proved-separately"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.accumulatedClock_nonneg_of_contraction where
  formalizes @ "claim:the-accumulated-clock-is-nonnegative-under-the-same-relative-entropy-contraction-read-as-elapsed-relaxation",
  epistemic_status @ "conditional-model",
  requires @ "claim:the-remaining-disequilibrium-clock-does-not-increase-whenever-the-relative-entropy-to-equilibrium-contracts",
  supported_by @ "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_map_le",
  caveat @ "same-explicit-contraction-premise-read-as-accumulated-relaxation-rather-than-remaining-disequilibrium"

zil_file_contract physlib.totalCorrelationEntropicClock where
  promises "The bipartite total correlation is the nonnegative negentropy gap. Its calibrated master weight is contractive and decreases under explicit Liouville-plus-Boltzmann premises. The shared finite log-sum theorem handles coordinate marginalization. At continuum measure level, measurable maps and arbitrary common Markov kernels contract the remaining clock, give exact nonnegative information-loss telescopes, and monotonically recover the master modulus. A positive-time continuum Markov-kernel semigroup with stationary reference has an antitone remaining clock, nonnegative additive interval production, and a monotone complex-action modulus. Its weakly continuous C0 extension recovers initial bounded-observable expectations, identifies stationary measures with the kernel of any supplied weak generator, and makes every existing right clock-production rate nonnegative. The concrete identity C0 control semigroup has zero weak generator; stationary references construct a zero rate, and uniqueness forces every stationary right rate to vanish."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.entropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.mutualInfo_eq_entropies",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem.relativeEntropy_marginal_le",
    "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_map_le",
    "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_comp_le",
    "lean:Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep.tauEnt_eq_entropyProduced",
    "lean:Physlib.Thermodynamics.KullbackLeiblerInformationGain.finiteMutualInformation",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight"]
  forbids_substitutes ["an unconditional arrow-of-time theorem: the Liouville and two marginal-entropy inequalities are explicit inputs here",
    "a single observer-independent entropy scalar, whereas the clock is built from a joint entropy and its marginals",
    "a constructed model-specific Markov or GKLS generator, quantum instrument, or collapse dynamics from the abstract weak-C0 and generator-limit carriers"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_klDivergence,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_entropyGap,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_zero_of_independent,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_eq_imaginaryAction_div,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_monotone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_monotone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.imaginaryAction_monotone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_antitone_of_contraction,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.accumulatedClock_nonneg_of_contraction,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_zero_iff_independent,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.entropicClock_eq_zero_iff_independent,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_le_one,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_eq_one_iff_independent,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_antitone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.klDivergence_marginalFst_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_marginalFst_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_eq_marginal_add_gain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.marginalizationClockGain_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight_norm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight_norm_marginalFst_mono,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_map_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_eq_map_add_gain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureMapClockGain_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm_map_mono,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_comp_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_eq_comp_add_gain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureKernelClockGain_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm_comp_mono,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.measureAt_add,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockAt_antitone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.intervalClockGain_cocycle,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockComplexWeightAt_norm_monotone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.initial_observable_recovery,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.observableGenerator_eq_zero_of_fixedReference,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.rightClockProductionRate_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity_hasObservableGenerator_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.fixedReference_hasRightClockProductionRate_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.rightClockProductionRate_eq_zero_of_fixedReference,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.identity_isFixedReference,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm_le_one,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm_eq_entropyProduced]

#zil_formalization_lint physlib.totalCorrelationEntropicClock

/- ZIL-END -/

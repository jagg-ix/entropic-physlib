/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
/-!
# Finite Canonical Ensemble

This file specializes the general measure-theoretic framework of the canonical ensemble to systems
with a finite number of discrete microstates. This is a common and important case in statistical
mechanics to study models like spin systems (e.g., the Ising model) and other systems with a
discrete quantum state space.

## Main Definitions and Results

The specialization is achieved through the `IsFinite` class, which asserts that:
1. The type of microstates `ι` is a `Fintype`.
2. The measure `μ` on `ι` is the standard counting measure.
3. The number of degrees of freedom `dof` is 0.
4. The `phaseSpaceunit` is 1.

These assumptions correspond to systems where the state space is fundamentally discrete, and no
semi-classical approximation from a continuous phase space is needed. Consequently, the
dimensionless physical quantities are directly equivalent to their mathematical counterparts.

The main results proved in this file are:
- The abstract integral definitions for thermodynamic quantities (partition function, mean energy)
  are shown to reduce to the familiar finite sums found in introductory texts. For example, the
  partition function becomes `Z = ∑ᵢ exp(-β Eᵢ)`.
- The abstract `thermodynamicEntropy`, defined generally for measure-theoretic systems, is proven
  to be equal to the standard `shannonEntropy` (`S = -k_B ∑ᵢ pᵢ log pᵢ`). The semi-classical
  correction terms from the general theory vanish under the `IsFinite` assumptions.
- The **fluctuation-dissipation theorem** in the form `C_V = Var(E) / (k_B T²)`, which connects the
  heat capacity `C_V` to the variance of energy fluctuations, is formally proven for these systems.
- **Nernst's heat theorem** for finite spectra: as `β → +∞` the Gibbs distribution
  equidistributes over the ground level, the mean energy converges to the ground energy, and the
  entropy converges to the residual entropy `k_B log g₀` (`g₀` the ground-level degeneracy) —
  zero exactly in the non-degenerate case (Planck's form), with the Boltzmann inversion
  `g₀ = exp (S₀ / k_B)`.

This file also confirms that the `IsFinite` property is preserved under the composition of
systems (addition, `nsmul`, and `congr`).

## References

- L. D. Landau & E. M. Lifshitz, *Statistical Physics, Part 1*, §31.
- D. Tong, *Lectures on Statistical Physics*, §1.3.

-/

@[expose] public section

namespace CanonicalEnsemble

open Real Temperature MeasureTheory Constants Filter Topology
open scoped Temperature CanonicalEnsemble

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι)

variable {ι1 : Type} [Fintype ι1] [MeasurableSpace ι1]
  [MeasurableSingletonClass ι1] (𝓒1 : CanonicalEnsemble ι1)

/-- A finite `CanonicalEnsemble` is one whose microstates form a finite type
and whose measure is the counting measure. For such systems, the state space is
inherently discrete and dimensionless, so we require `dof = 0` and
`phaseSpaceUnit = 1`. -/
class IsFinite (𝓒 : CanonicalEnsemble ι) [Fintype ι] : Prop where
  μ_eq_count : 𝓒.μ = Measure.count
  dof_eq_zero : 𝓒.dof = 0
  phase_space_unit_eq_one : 𝓒.phaseSpaceunit = 1

/-- The canonical ensemble carried by a finite discrete energy spectrum.  This constructor
lets quantum spectral developments reuse the canonical-ensemble API without rebuilding its
counting measure, zero degrees-of-freedom convention, or unit phase-space normalization. -/
noncomputable def ofFiniteEnergy (E : ι → ℝ) : CanonicalEnsemble ι where
  energy := E
  dof := 0
  phaseSpaceunit := 1
  hPos := by positivity
  energy_measurable := measurable_of_finite E
  μ := Measure.count

/-- A finite discrete energy spectrum satisfies the repository's finite-ensemble contract. -/
instance ofFiniteEnergy_isFinite (E : ι → ℝ) : IsFinite (ofFiniteEnergy E) where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

instance [IsFinite 𝓒] [IsFinite 𝓒1] : IsFinite (𝓒 + 𝓒1) where
  μ_eq_count := by
    rw [μ_add]
    rw [IsFinite.μ_eq_count (𝓒:=𝓒), IsFinite.μ_eq_count (𝓒:=𝓒1)]
    refine Measure.prod_eq ?_
    intro s t hs ht
    rw [Measure.count_apply, Measure.count_apply, Measure.count_apply]
    rw [← ENat.toENNReal_mul]
    congr
    simp only [Set.encard_prod]
    · exact ht
    · exact hs
    · exact MeasurableSet.prod hs ht
  dof_eq_zero := by
    simp [IsFinite.dof_eq_zero (𝓒:=𝓒), IsFinite.dof_eq_zero (𝓒:=𝓒1)]
  phase_space_unit_eq_one := by
    simp [IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

instance [IsFinite 𝓒] (e : ι1 ≃ᵐ ι) : IsFinite (congr 𝓒 e) where
  μ_eq_count := by
    simp [congr]
    rw [IsFinite.μ_eq_count (𝓒:=𝓒)]
    refine Measure.ext_iff.mpr ?_
    intro s hs
    rw [@MeasurableEquiv.map_apply]
    rw [Measure.count_apply, Measure.count_apply]
    simp only [ENat.toENNReal_inj]
    rw [@MeasurableEquiv.preimage_symm]
    rw [← Set.Finite.cast_ncard_eq, ← Set.Finite.cast_ncard_eq]
    congr 1
    change (e.toEmbedding '' s).ncard = _
    rw [Set.ncard_map]
    · exact Set.toFinite s
    · exact Set.toFinite (⇑e '' s)
    · exact hs
    · exact (MeasurableEquiv.measurableSet_preimage e.symm).mpr hs
  dof_eq_zero := by
    simp [IsFinite.dof_eq_zero (𝓒:=𝓒)]
  phase_space_unit_eq_one := by
    simp [IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

instance [IsFinite 𝓒] (n : ℕ) : IsFinite (nsmul n 𝓒) where
  μ_eq_count := by
    induction n with
    | zero =>
      haveI : Subsingleton (Fin 0 → ι) := ⟨by intro f g; funext i; exact Fin.elim0 i⟩
      have h_cases : ∀ s : Set (Fin 0 → ι), s = ∅ ∨ s = Set.univ := fun s =>
        s.eq_empty_or_nonempty.imp_right fun ⟨y, hy⟩ =>
          Set.eq_univ_of_forall fun x => by rwa [Subsingleton.elim x y]
      refine Measure.ext (fun s _ => ?_)
      rcases h_cases s with hs | hs
      · subst hs
        simp [CanonicalEnsemble.nsmul]
      · subst hs
        simp [CanonicalEnsemble.nsmul, IsFinite.μ_eq_count (𝓒:=𝓒)]
    | succ n ih =>
      haveI : IsFinite (nsmul n 𝓒) := {
        μ_eq_count := ih
        dof_eq_zero := by
          simp [CanonicalEnsemble.dof_nsmul, IsFinite.dof_eq_zero (𝓒:=𝓒)]
        phase_space_unit_eq_one := by
          simp [CanonicalEnsemble.phase_space_unit_nsmul,
            IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]
      }
      letI : Fintype (Fin (n+1) → ι) := inferInstance
      have h :
        ((𝓒 + nsmul n 𝓒).congr
            (MeasurableEquiv.piFinSuccAbove (fun _ => ι) 0)).μ
          = Measure.count := by erw [IsFinite.μ_eq_count]; aesop
      rw [← h]; rw [← @nsmul_succ]
  dof_eq_zero := by
    simp [CanonicalEnsemble.dof_nsmul, IsFinite.dof_eq_zero (𝓒:=𝓒)]
  phase_space_unit_eq_one := by
    simp [CanonicalEnsemble.phase_space_unit_nsmul,
      IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

instance [IsFinite 𝓒] : IsFiniteMeasure (𝓒.μ) := by
  rw [IsFinite.μ_eq_count]
  infer_instance

/-- In the finite (counting) case a nonempty index type gives a nonzero measure. -/
instance [IsFinite 𝓒] [Nonempty ι] : NeZero 𝓒.μ := by
  refine ⟨?_⟩
  intro hμ
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hone : 𝓒.μ {i₀} = 1 := by
    simp [IsFinite.μ_eq_count (𝓒:=𝓒)]
  simp_all only [Measure.coe_zero, Pi.zero_apply, zero_ne_one]

/-- The Shannon entropy of a finite canonical ensemble.
This is defined by the formula `S = -k_B ∑ pᵢ log pᵢ`. It is proven to be
equivalent to the `differentialEntropy` and the `thermodynamicEntropy` for systems
satisfying the `IsFinite` property. -/
noncomputable def shannonEntropy (T : Temperature) : ℝ :=
  -kB * ∑ i, 𝓒.probability T i * log (𝓒.probability T i)

lemma mathematicalPartitionFunction_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.mathematicalPartitionFunction T = ∑ i, exp (- β T * 𝓒.energy i) := by
  rw [mathematicalPartitionFunction_eq_integral, MeasureTheory.integral_fintype]
  simp [IsFinite.μ_eq_count]
  · rw [IsFinite.μ_eq_count]
    exact Integrable.of_finite

lemma partitionFunction_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.partitionFunction T = ∑ i, exp (- T.β * 𝓒.energy i) := by
  simp [partitionFunction, mathematicalPartitionFunction_of_fintype,
        IsFinite.dof_eq_zero, IsFinite.phase_space_unit_eq_one]

@[simp]
lemma μBolt_of_fintype (T : Temperature) [IsFinite 𝓒] (i : ι) :
    (𝓒.μBolt T).real {i} = Real.exp (- β T * 𝓒.energy i) := by
  rw [μBolt]
  simp only [neg_mul]
  rw [@measureReal_def]
  simp [IsFinite.μ_eq_count]
  exact Real.exp_nonneg _

instance {T} [IsFinite 𝓒] : IsFiniteMeasure (𝓒.μBolt T) := by
  rw [μBolt]
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact HasFiniteIntegral.of_finite

@[simp]
lemma μProd_of_fintype (T : Temperature) [IsFinite 𝓒] (i : ι) :
    (𝓒.μProd T).real {i} = 𝓒.probability T i := by
  rw [μProd]
  simp [probability]
  rw [inv_mul_eq_div]
  rfl

lemma meanEnergy_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.meanEnergy T = ∑ i, 𝓒.energy i * 𝓒.probability T i := by
  simp [meanEnergy]
  rw [MeasureTheory.integral_fintype]
  simp [mul_comm]
  exact Integrable.of_finite

end CanonicalEnsemble
namespace CanonicalEnsemble
open Real Temperature MeasureTheory Constants
open scoped Temperature CanonicalEnsemble

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
  (𝓒 : CanonicalEnsemble ι)

variable {ι1 : Type} [Fintype ι1] [MeasurableSpace ι1]
  (𝓒1 : CanonicalEnsemble ι1)
open Constants

lemma entropy_of_fintype (T : Temperature) :
    𝓒.shannonEntropy T = - kB * ∑ i, 𝓒.probability T i * log (𝓒.probability T i) := by
  simp [shannonEntropy]

lemma probability_le_one
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) (i : ι) :
    𝓒.probability T i ≤ 1 := by
  have hZpos : 0 < 𝓒.mathematicalPartitionFunction T := by
    rw [mathematicalPartitionFunction_of_fintype]
    exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  rw [probability, div_le_one hZpos, mathematicalPartitionFunction_of_fintype]
  simpa [neg_mul] using Finset.single_le_sum
    (f := fun j : ι => Real.exp (- β T * 𝓒.energy j)) (fun j _ => Real.exp_nonneg _)
    (Finset.mem_univ i)

/-- Finite specialization: strict positivity of the mathematical partition function. -/
lemma mathematicalPartitionFunction_pos_finite
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 < 𝓒.mathematicalPartitionFunction T := by
  simpa using (CanonicalEnsemble.mathematicalPartitionFunction_pos (𝓒:=𝓒) T)

/-- Finite specialization: strict positivity of the (physical) partition function. -/
lemma partitionFunction_pos_finite
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 < 𝓒.partitionFunction T := by
  simpa [partitionFunction, IsFinite.dof_eq_zero (𝓒:=𝓒),
        IsFinite.phase_space_unit_eq_one (𝓒:=𝓒), pow_zero]
    using mathematicalPartitionFunction_pos_finite (𝓒:=𝓒) (T:=T)

/-- Finite specialization: non-negativity (indeed positivity) of probabilities. -/
lemma probability_nonneg_finite
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) (i : ι) :
    0 ≤ 𝓒.probability T i := by
  unfold probability
  have hZpos := mathematicalPartitionFunction_pos_finite (𝓒:=𝓒) (T:=T)
  exact div_nonneg (Real.exp_nonneg _) hZpos.le

/-- The sum of probabilities over all microstates is 1. -/
lemma sum_probability_eq_one
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    ∑ i, 𝓒.probability T i = 1 := by
  have hZne : 𝓒.mathematicalPartitionFunction T ≠ 0 :=
    (mathematicalPartitionFunction_pos_finite 𝓒 T).ne'
  simp_rw [probability, ← Finset.sum_div, ← mathematicalPartitionFunction_of_fintype]
  exact div_self hZne

/-- The entropy of a finite canonical ensemble (Shannon entropy) is non-negative. -/
lemma entropy_nonneg [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 ≤ 𝓒.shannonEntropy T := by
  have hsum : ∑ i, 𝓒.probability T i * log (𝓒.probability T i) ≤ 0 :=
    Fintype.sum_nonpos fun i =>
      mul_nonpos_iff.2 <| Or.inl ⟨probability_nonneg_finite 𝓒 T i,
        Real.log_nonpos (probability_nonneg_finite 𝓒 T i) (probability_le_one 𝓒 T i)⟩
  rw [shannonEntropy, neg_mul, neg_nonneg]
  exact mul_nonpos_iff.2 <| Or.inl ⟨kB_pos.le, hsum⟩

lemma shannonEntropy_eq_differentialEntropy
    [MeasurableSingletonClass ι] [IsFinite 𝓒] (T : Temperature) :
    𝓒.shannonEntropy T = 𝓒.differentialEntropy T := by
  simp [shannonEntropy, differentialEntropy, integral_fintype, μProd_of_fintype]

/-- In the finite, nonempty case the thermodynamic and Shannon entropies coincide.
All semi-classical correction factors vanish (`dof = 0`, `phaseSpaceUnit = 1`),
so the absolute thermodynamic entropy reduces to the discrete Shannon form. -/
theorem thermodynamicEntropy_eq_shannonEntropy [MeasurableSingletonClass ι] [IsFinite 𝓒]
    (T : Temperature) :-- (hT : 0 < T.val) :
    𝓒.thermodynamicEntropy T = 𝓒.shannonEntropy T := by
  have h_thermo_eq_diff :
      𝓒.thermodynamicEntropy T = 𝓒.differentialEntropy T := by
    unfold CanonicalEnsemble.thermodynamicEntropy
      CanonicalEnsemble.differentialEntropy
    have h_log :
        (fun i => Real.log (𝓒.physicalProbability T i))
          = (fun i => Real.log (𝓒.probability T i)) := by
      funext i
      simp [CanonicalEnsemble.physicalProbability,
            IsFinite.dof_eq_zero (𝓒:=𝓒),
            IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]
    simp_all only [physicalProbability_def]
  have h_shannon :
      𝓒.shannonEntropy T = 𝓒.differentialEntropy T :=
    (shannonEntropy_eq_differentialEntropy (𝓒:=𝓒) T)
  calc
    𝓒.thermodynamicEntropy T
        = 𝓒.differentialEntropy T := h_thermo_eq_diff
    _ = 𝓒.shannonEntropy T := h_shannon.symm

open Real Temperature MeasureTheory Constants
open scoped Temperature CanonicalEnsemble BigOperators Constants ENNReal NNReal

/-! ## Fluctuations in Finite Systems -/

section FluctuationsFinite

lemma meanSquareEnergy_of_fintype [MeasurableSingletonClass ι] [IsFinite 𝓒] (T : Temperature) :
    𝓒.meanSquareEnergy T = ∑ i, (𝓒.energy i)^2 * 𝓒.probability T i := by
  simp [CanonicalEnsemble.meanSquareEnergy]
  rw [MeasureTheory.integral_fintype]
  simp [μProd_of_fintype, mul_comm]
  exact Integrable.of_finite

lemma energyVariance_of_fintype
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    𝓒.energyVariance T = (∑ i, (𝓒.energy i)^2 * 𝓒.probability T i) - (𝓒.meanEnergy T)^2 := by
  have hE_int := Integrable.of_finite (f := 𝓒.energy) (μ := 𝓒.μProd T)
  have hE2_int := Integrable.of_finite (f := fun i => (𝓒.energy i)^2) (μ := 𝓒.μProd T)
  rw [CanonicalEnsemble.energyVariance_eq_meanSquareEnergy_sub_meanEnergy_sq 𝓒 T hE_int hE2_int]
  rw [meanSquareEnergy_of_fintype]

/-! ## β-parameterization for finite systems -/

/-- The finite-sum partition function as a real function of the inverse temperature `b = β`,
defined by `Z(b) = ∑ i exp (-b * 𝓒.energy i)`. -/
noncomputable def mathematicalPartitionFunctionBetaReal (b : ℝ) : ℝ :=
  ∑ i, Real.exp (-b * 𝓒.energy i)

lemma mathematicalPartitionFunctionBetaReal_pos [Nonempty ι] (b : ℝ) :
    0 < 𝓒.mathematicalPartitionFunctionBetaReal b := by
  apply Finset.sum_pos
  · intro i _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- For inverse temperature `b = β`, the (real-valued) Boltzmann probability of microstate `i`,
given by `exp (-b * E i) / Z(b)` where `Z(b) = ∑ i exp (-b * E i)`. -/
noncomputable def probabilityBetaReal (b : ℝ) (i : ι) : ℝ :=
  Real.exp (-b * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal b

/-- The mean energy as a function of inverse temperature `b = β` in the finite case,
defined by `U(b) = ∑ i, E i * p_b i` with `p_b i = exp (-b * E i) / Z(b)` and `Z(b) = ∑ i,
exp (-b * E i)`. -/
noncomputable def meanEnergyBetaReal (b : ℝ) : ℝ :=
  ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i

/-- The finite Gibbs probabilities form a probability distribution for every real inverse
temperature. -/
lemma sum_probabilityBetaReal_eq_one [Nonempty ι] (b : ℝ) :
    ∑ i, 𝓒.probabilityBetaReal b i = 1 := by
  unfold probabilityBetaReal mathematicalPartitionFunctionBetaReal
  rw [← Finset.sum_div]
  exact div_self (mathematicalPartitionFunctionBetaReal_pos 𝓒 b).ne'

/-- Shannon/Gibbs entropy as a function of the real inverse temperature `b = β`.  This is
the inverse-temperature counterpart of `shannonEntropy`, using the same Boltzmann constant
and the finite probability family already used for the paper's mean-energy identities. -/
noncomputable def shannonEntropyBetaReal (b : ℝ) : ℝ :=
  -kB * ∑ i, 𝓒.probabilityBetaReal b i * Real.log (𝓒.probabilityBetaReal b i)

/-- Pointwise logarithm of a finite Gibbs probability in the real `β` parameterization. -/
lemma log_probabilityBetaReal [Nonempty ι] (b : ℝ) (i : ι) :
    Real.log (𝓒.probabilityBetaReal b i) =
      -b * 𝓒.energy i - Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) := by
  unfold probabilityBetaReal
  rw [Real.log_div (Real.exp_ne_zero _) (mathematicalPartitionFunctionBetaReal_pos 𝓒 b).ne',
    Real.log_exp]

/-- Finite canonical entropy identity `S(β) = k_B (β U(β) + log Z(β))`. -/
lemma shannonEntropyBetaReal_eq [Nonempty ι] (b : ℝ) :
    𝓒.shannonEntropyBetaReal b =
      kB * (b * 𝓒.meanEnergyBetaReal b +
        Real.log (𝓒.mathematicalPartitionFunctionBetaReal b)) := by
  have hsum :
      (∑ i, 𝓒.probabilityBetaReal b i *
        (-b * 𝓒.energy i - Real.log (𝓒.mathematicalPartitionFunctionBetaReal b))) =
        (-b) * (∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i) -
          Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) *
            ∑ i, 𝓒.probabilityBetaReal b i := by
    calc
      _ = ∑ i,
          ((-b) * (𝓒.energy i * 𝓒.probabilityBetaReal b i) -
            Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) *
              𝓒.probabilityBetaReal b i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i, (-b) * (𝓒.energy i * 𝓒.probabilityBetaReal b i)) -
          ∑ i, Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) *
            𝓒.probabilityBetaReal b i := by
            simp
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  unfold shannonEntropyBetaReal
  simp_rw [log_probabilityBetaReal 𝓒 b]
  rw [hsum, sum_probabilityBetaReal_eq_one 𝓒 b]
  unfold meanEnergyBetaReal
  ring

/-- Boltzmann probabilities are unchanged when all energies are shifted by the energy of a
reference state.  This relative-energy form is the useful one for zero-temperature limits. -/
lemma probabilityBetaReal_eq_shift (b : ℝ) (i i₀ : ι) :
    𝓒.probabilityBetaReal b i =
      Real.exp (-b * (𝓒.energy i - 𝓒.energy i₀)) /
        ∑ j, Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀)) := by
  have hterm (j : ι) :
      Real.exp (-b * 𝓒.energy j) =
        Real.exp (-b * 𝓒.energy i₀) *
          Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold probabilityBetaReal mathematicalPartitionFunctionBetaReal
  rw [hterm i]
  have hsum : (∑ j, Real.exp (-b * 𝓒.energy j)) =
      Real.exp (-b * 𝓒.energy i₀) *
        ∑ j, Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    exact hterm j
  rw [hsum]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

/-- At inverse temperature `β → +∞`, a finite Gibbs distribution with a unique ground state
concentrates on that state. -/
lemma tendsto_probabilityBetaReal_atTop_of_unique_min [DecidableEq ι] (i₀ i : ι)
    (hmin : ∀ j, j ≠ i₀ → 𝓒.energy i₀ < 𝓒.energy j) :
    Filter.Tendsto (fun b : ℝ => 𝓒.probabilityBetaReal b i) Filter.atTop
      (nhds (if i = i₀ then 1 else 0)) := by
  classical
  have hterm (j : ι) :
      Filter.Tendsto (fun b : ℝ => Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀)))
        Filter.atTop
        (nhds (if j = i₀ then 1 else 0)) := by
    by_cases hj : j = i₀
    · subst j
      simp
    · have hgap : 0 < 𝓒.energy j - 𝓒.energy i₀ := sub_pos.mpr (hmin j hj)
      have hscale : Filter.Tendsto (fun b : ℝ => b * (𝓒.energy j - 𝓒.energy i₀))
          Filter.atTop Filter.atTop := by
        simpa [mul_comm] using
          Filter.Tendsto.const_mul_atTop hgap Filter.tendsto_id
      rw [if_neg hj]
      simpa only [Function.comp_def, neg_mul] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hden : Filter.Tendsto
      (fun b : ℝ => ∑ j, Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀))) Filter.atTop
      (nhds 1) := by
    have hsum := tendsto_finsetSum Finset.univ (fun j _hj => hterm j)
    simpa using hsum
  have hratio := (hterm i).div hden one_ne_zero
  change Filter.Tendsto
    (fun b : ℝ => Real.exp (-b * (𝓒.energy i - 𝓒.energy i₀)) /
      ∑ j, Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀))) Filter.atTop
    (nhds ((if i = i₀ then 1 else 0) / 1)) at hratio
  have hfun : (fun b : ℝ => 𝓒.probabilityBetaReal b i) =
      (fun b : ℝ => Real.exp (-b * (𝓒.energy i - 𝓒.energy i₀)) /
        ∑ j, Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀))) := by
    funext b
    exact probabilityBetaReal_eq_shift 𝓒 b i i₀
  rw [hfun]
  simpa using hratio

/-- Paper Eq. (3.9), in reusable finite-spectrum form: if the ground state is unique, the
canonical mean energy converges to its energy as `β → +∞`. -/
lemma tendsto_meanEnergyBetaReal_atTop_of_unique_min [DecidableEq ι] (i₀ : ι)
    (hmin : ∀ j, j ≠ i₀ → 𝓒.energy i₀ < 𝓒.energy j) :
    Filter.Tendsto 𝓒.meanEnergyBetaReal Filter.atTop (nhds (𝓒.energy i₀)) := by
  classical
  have hterm (i : ι) : Filter.Tendsto
      (fun b : ℝ => 𝓒.energy i * 𝓒.probabilityBetaReal b i) Filter.atTop
      (nhds (𝓒.energy i * if i = i₀ then 1 else 0)) :=
    tendsto_const_nhds.mul
      (tendsto_probabilityBetaReal_atTop_of_unique_min 𝓒 i₀ i hmin)
  have hsum := tendsto_finsetSum Finset.univ (fun i _hi => hterm i)
  change Filter.Tendsto
    (fun b : ℝ => ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i)
    Filter.atTop (nhds (𝓒.energy i₀))
  simpa using hsum

/-- A finite Gibbs state with a unique ground state has vanishing Shannon entropy in the
zero-temperature limit `β → +∞`. -/
lemma tendsto_shannonEntropyBetaReal_atTop_of_unique_min [DecidableEq ι] (i₀ : ι)
    (hmin : ∀ j, j ≠ i₀ → 𝓒.energy i₀ < 𝓒.energy j) :
    Filter.Tendsto 𝓒.shannonEntropyBetaReal Filter.atTop (nhds 0) := by
  classical
  have hterm (i : ι) : Filter.Tendsto
      (fun b : ℝ => 𝓒.probabilityBetaReal b i * Real.log (𝓒.probabilityBetaReal b i))
      Filter.atTop (nhds 0) := by
    have hp := tendsto_probabilityBetaReal_atTop_of_unique_min 𝓒 i₀ i hmin
    by_cases hi : i = i₀
    · have hp' : Filter.Tendsto (fun b : ℝ => 𝓒.probabilityBetaReal b i)
          Filter.atTop (nhds 1) := by simpa [hi] using hp
      have hcontinuous : Filter.Tendsto (fun x : ℝ => x * Real.log x)
          (nhds 1) (nhds (1 * Real.log 1)) :=
        (Real.continuous_mul_log).continuousAt
      simpa only [Function.comp_def, one_mul, Real.log_one] using hcontinuous.comp hp'
    · have hp' : Filter.Tendsto (fun b : ℝ => 𝓒.probabilityBetaReal b i)
          Filter.atTop (nhds 0) := by simpa [hi] using hp
      have hcontinuous : Filter.Tendsto (fun x : ℝ => x * Real.log x)
          (nhds 0) (nhds (0 * Real.log 0)) :=
        (Real.continuous_mul_log).continuousAt
      simpa only [Function.comp_def, zero_mul] using hcontinuous.comp hp'
  have hsum : Filter.Tendsto
      (fun b : ℝ => ∑ i,
        𝓒.probabilityBetaReal b i * Real.log (𝓒.probabilityBetaReal b i))
      Filter.atTop (nhds 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _hi => hterm i)
    simpa using h
  change Filter.Tendsto
    (fun b : ℝ => -kB * ∑ i,
      𝓒.probabilityBetaReal b i * Real.log (𝓒.probabilityBetaReal b i))
    Filter.atTop (nhds 0)
  have hscaled :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => -kB) Filter.atTop (nhds (-kB))).mul hsum
  simpa using hscaled

/-! ## Nernst's heat theorem: the zero-temperature limit with a degenerate ground level -/

/-- At inverse temperature `β → +∞`, a finite Gibbs distribution with ground level `E₀` of
degeneracy `g₀ = G.card` equidistributes over the ground states: each ground state carries
probability `1/g₀`, every excited state decouples.  The unique-ground-state case is
`tendsto_probabilityBetaReal_atTop_of_unique_min` (`G = {i₀}`). -/
lemma tendsto_probabilityBetaReal_atTop_of_degenerate_min [DecidableEq ι]
    (G : Finset ι) (hne : G.Nonempty) (E₀ : ℝ)
    (hG : ∀ j ∈ G, 𝓒.energy j = E₀) (hout : ∀ j ∉ G, E₀ < 𝓒.energy j) (i : ι) :
    Filter.Tendsto (fun b : ℝ => 𝓒.probabilityBetaReal b i) Filter.atTop
      (nhds (if i ∈ G then ((G.card : ℝ))⁻¹ else 0)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  have hE₀ : 𝓒.energy i₀ = E₀ := hG i₀ hi₀
  have hterm (j : ι) :
      Filter.Tendsto (fun b : ℝ => Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀)))
        Filter.atTop (nhds (if j ∈ G then 1 else 0)) := by
    by_cases hj : j ∈ G
    · rw [if_pos hj]
      have hzero : 𝓒.energy j - 𝓒.energy i₀ = 0 := by rw [hG j hj, hE₀]; ring
      simp [hzero]
    · have hgap : 0 < 𝓒.energy j - 𝓒.energy i₀ := by
        rw [hE₀]; exact sub_pos.mpr (hout j hj)
      have hscale : Filter.Tendsto (fun b : ℝ => b * (𝓒.energy j - 𝓒.energy i₀))
          Filter.atTop Filter.atTop := by
        simpa [mul_comm] using
          Filter.Tendsto.const_mul_atTop hgap Filter.tendsto_id
      rw [if_neg hj]
      simpa only [Function.comp_def, neg_mul] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hcount : (∑ j, if j ∈ G then (1 : ℝ) else 0) = (G.card : ℝ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : ((G.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨i₀, hi₀⟩).ne'
  have hden : Filter.Tendsto
      (fun b : ℝ => ∑ j, Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀))) Filter.atTop
      (nhds (G.card : ℝ)) := by
    have hsum := tendsto_finsetSum Finset.univ (fun j _hj => hterm j)
    rw [← hcount]
    simpa using hsum
  have hratio := (hterm i).div hden hcard
  change Filter.Tendsto
    (fun b : ℝ => Real.exp (-b * (𝓒.energy i - 𝓒.energy i₀)) /
      ∑ j, Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀))) Filter.atTop
    (nhds ((if i ∈ G then 1 else 0) / (G.card : ℝ))) at hratio
  have hfun : (fun b : ℝ => 𝓒.probabilityBetaReal b i) =
      (fun b : ℝ => Real.exp (-b * (𝓒.energy i - 𝓒.energy i₀)) /
        ∑ j, Real.exp (-b * (𝓒.energy j - 𝓒.energy i₀))) := by
    funext b
    exact probabilityBetaReal_eq_shift 𝓒 b i i₀
  rw [hfun]
  by_cases hi : i ∈ G
  · simpa [hi, one_div] using hratio
  · simpa [hi] using hratio

/-- With a degenerate ground level, the canonical mean energy converges to the ground energy
as `β → +∞`. -/
lemma tendsto_meanEnergyBetaReal_atTop_of_degenerate_min [DecidableEq ι]
    (G : Finset ι) (hne : G.Nonempty) (E₀ : ℝ)
    (hG : ∀ j ∈ G, 𝓒.energy j = E₀) (hout : ∀ j ∉ G, E₀ < 𝓒.energy j) :
    Filter.Tendsto 𝓒.meanEnergyBetaReal Filter.atTop (nhds E₀) := by
  classical
  have hcard : ((G.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have hterm (i : ι) : Filter.Tendsto
      (fun b : ℝ => 𝓒.energy i * 𝓒.probabilityBetaReal b i) Filter.atTop
      (nhds (𝓒.energy i * if i ∈ G then ((G.card : ℝ))⁻¹ else 0)) :=
    tendsto_const_nhds.mul
      (tendsto_probabilityBetaReal_atTop_of_degenerate_min 𝓒 G hne E₀ hG hout i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _hi => hterm i)
  have hval : (∑ i, 𝓒.energy i * if i ∈ G then ((G.card : ℝ))⁻¹ else 0) = E₀ := by
    have h1 : ∀ i : ι, 𝓒.energy i * (if i ∈ G then ((G.card : ℝ))⁻¹ else 0)
        = if i ∈ G then 𝓒.energy i * ((G.card : ℝ))⁻¹ else 0 := by
      intro i; by_cases hi : i ∈ G <;> simp [hi]
    simp_rw [h1]
    rw [Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_congr rfl (fun i hi => by rw [hG i hi]),
      Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hlim : Filter.Tendsto
      (fun b : ℝ => ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i)
      Filter.atTop (nhds E₀) := by
    rw [← hval]
    exact hsum
  exact hlim

/-- **Nernst's heat theorem** (finite spectrum): as `β → +∞` the canonical entropy of a finite
Gibbs ensemble whose ground level `E₀` has degeneracy `g₀ = G.card` converges to the residual
entropy `k_B · log g₀` — Boltzmann's entropy of the ground shell, independent of every energy
above the gap.  Planck's form of the third law is the non-degenerate case `g₀ = 1`, residual
entropy zero (`tendsto_shannonEntropyBetaReal_atTop_of_unique_min`).  A nonzero residual
entropy at `T = 0` therefore *is* ground-level degeneracy
(`one_lt_card_of_residual_entropy_ne_zero`, `card_eq_exp_residual_entropy_div_kB`) — the
thermodynamic side of the extremal black hole's `T = 0`, `S ≠ 0`
(`Curvature.KerrNewmanThirdLaw.kn_hawkingTemperature_extremal`): not a third-law violation but
a degeneracy statement. -/
lemma tendsto_shannonEntropyBetaReal_atTop_of_degenerate_min [DecidableEq ι]
    (G : Finset ι) (hne : G.Nonempty) (E₀ : ℝ)
    (hG : ∀ j ∈ G, 𝓒.energy j = E₀) (hout : ∀ j ∉ G, E₀ < 𝓒.energy j) :
    Filter.Tendsto 𝓒.shannonEntropyBetaReal Filter.atTop
      (nhds (kB * Real.log G.card)) := by
  classical
  have hcard : ((G.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have hterm (i : ι) : Filter.Tendsto
      (fun b : ℝ => 𝓒.probabilityBetaReal b i * Real.log (𝓒.probabilityBetaReal b i))
      Filter.atTop
      (nhds ((if i ∈ G then ((G.card : ℝ))⁻¹ else 0) *
        Real.log (if i ∈ G then ((G.card : ℝ))⁻¹ else 0))) := by
    have hp := tendsto_probabilityBetaReal_atTop_of_degenerate_min 𝓒 G hne E₀ hG hout i
    have hcont : Filter.Tendsto (fun x : ℝ => x * Real.log x)
        (nhds (if i ∈ G then ((G.card : ℝ))⁻¹ else 0))
        (nhds ((if i ∈ G then ((G.card : ℝ))⁻¹ else 0) *
          Real.log (if i ∈ G then ((G.card : ℝ))⁻¹ else 0))) :=
      (Real.continuous_mul_log).continuousAt
    simpa only [Function.comp_def] using hcont.comp hp
  have hsum := tendsto_finsetSum Finset.univ (fun i _hi => hterm i)
  have hval : (∑ i, (if i ∈ G then ((G.card : ℝ))⁻¹ else 0) *
      Real.log (if i ∈ G then ((G.card : ℝ))⁻¹ else 0)) = -Real.log (G.card : ℝ) := by
    have h1 : ∀ i : ι, (if i ∈ G then ((G.card : ℝ))⁻¹ else 0) *
        Real.log (if i ∈ G then ((G.card : ℝ))⁻¹ else 0)
        = if i ∈ G then ((G.card : ℝ))⁻¹ * Real.log ((G.card : ℝ))⁻¹ else 0 := by
      intro i; by_cases hi : i ∈ G <;> simp [hi]
    simp_rw [h1]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      Real.log_inv, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  have hlim : -kB * (∑ i, (if i ∈ G then ((G.card : ℝ))⁻¹ else 0) *
      Real.log (if i ∈ G then ((G.card : ℝ))⁻¹ else 0)) = kB * Real.log (G.card : ℝ) := by
    rw [hval]; ring
  change Filter.Tendsto
    (fun b : ℝ => -kB * ∑ i,
      𝓒.probabilityBetaReal b i * Real.log (𝓒.probabilityBetaReal b i))
    Filter.atTop (nhds (kB * Real.log (G.card : ℝ)))
  rw [← hlim]
  exact
    (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => -kB) Filter.atTop (nhds (-kB))).mul hsum

/-- A finite Gibbs ensemble whose entropy has a **nonzero** zero-temperature limit must have a
degenerate ground level: `S(β) → S₀ ≠ 0` forces `g₀ > 1`.  Contrapositive of Planck's form of
the third law; no positivity of `k_B` is needed. -/
lemma one_lt_card_of_residual_entropy_ne_zero [DecidableEq ι]
    (G : Finset ι) (hne : G.Nonempty) (E₀ : ℝ)
    (hG : ∀ j ∈ G, 𝓒.energy j = E₀) (hout : ∀ j ∉ G, E₀ < 𝓒.energy j)
    (S₀ : ℝ) (hlim : Filter.Tendsto 𝓒.shannonEntropyBetaReal Filter.atTop (nhds S₀))
    (hS₀ : S₀ ≠ 0) : 1 < G.card := by
  have hval : S₀ = kB * Real.log (G.card : ℝ) :=
    tendsto_nhds_unique hlim
      (tendsto_shannonEntropyBetaReal_atTop_of_degenerate_min 𝓒 G hne E₀ hG hout)
  by_contra hle
  have h1 : G.card = 1 :=
    le_antisymm (Nat.le_of_not_lt hle) (Finset.card_pos.mpr hne)
  rw [h1] at hval
  simp at hval
  exact hS₀ hval

/-- **Boltzmann inversion of the residual entropy**: the ground-level degeneracy is the
exponential of the residual entropy in units of `k_B`, `g₀ = exp (S₀ / k_B)`.  This is the
exact statement behind reading a nonzero zero-temperature entropy as a microstate count. -/
lemma card_eq_exp_residual_entropy_div_kB [DecidableEq ι]
    (G : Finset ι) (hne : G.Nonempty) (E₀ : ℝ)
    (hG : ∀ j ∈ G, 𝓒.energy j = E₀) (hout : ∀ j ∉ G, E₀ < 𝓒.energy j)
    (S₀ : ℝ) (hlim : Filter.Tendsto 𝓒.shannonEntropyBetaReal Filter.atTop (nhds S₀)) :
    (G.card : ℝ) = Real.exp (S₀ / kB) := by
  have hval : S₀ = kB * Real.log (G.card : ℝ) :=
    tendsto_nhds_unique hlim
      (tendsto_shannonEntropyBetaReal_atTop_of_degenerate_min 𝓒 G hne E₀ hG hout)
  have hcardpos : (0 : ℝ) < (G.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  rw [hval, mul_comm, mul_div_assoc, div_self kB_ne_zero, mul_one,
    Real.exp_log hcardpos]

lemma meanEnergy_Beta_eq_finite [MeasurableSingletonClass ι] [IsFinite 𝓒] (b : ℝ) (hb : 0 < b) :
    𝓒.meanEnergyBeta b = 𝓒.meanEnergyBetaReal b := by
  let T := Temperature.ofβ (Real.toNNReal b)
  have hT_beta : (T.β : ℝ) = b := by
    simp [T, Real.toNNReal_of_nonneg hb.le]
  rw [meanEnergyBeta, meanEnergy_of_fintype 𝓒 T, meanEnergyBetaReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [CanonicalEnsemble.probability, probabilityBetaReal,
        mathematicalPartitionFunction_of_fintype, mathematicalPartitionFunctionBetaReal, hT_beta]

lemma differentiable_meanEnergyBetaReal
    [Nonempty ι] : Differentiable ℝ 𝓒.meanEnergyBetaReal := by
  unfold meanEnergyBetaReal probabilityBetaReal mathematicalPartitionFunctionBetaReal
  refine Differentiable.fun_sum (by
    intro i _
    refine (Differentiable.div ?_ ?_ ?_).const_mul (𝓒.energy i)
    · apply Differentiable.exp; simp
    · refine Differentiable.fun_sum ?_; intro j _; apply Differentiable.exp; simp
    · intro x; exact (mathematicalPartitionFunctionBetaReal_pos 𝓒 x).ne')

/-! Derivatives of Z and numerator -/

lemma differentiable_mathematicalPartitionFunctionBetaReal :
    Differentiable ℝ 𝓒.mathematicalPartitionFunctionBetaReal := by
  unfold mathematicalPartitionFunctionBetaReal
  refine Differentiable.fun_sum ?_; intro i _; simp

/-- The numerator in the finite-sum expression of the mean energy as a function of the
inverse temperature `b = β`,
namely `∑ i, E i * exp (-b * E i)` (so that `U(b) = meanEnergyNumerator b / Z(b)`). -/
noncomputable def meanEnergyNumerator (b : ℝ) : ℝ :=
  ∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i)

lemma differentiable_meanEnergyNumerator :
    Differentiable ℝ 𝓒.meanEnergyNumerator := by
  unfold meanEnergyNumerator
  refine Differentiable.fun_sum ?_; intro i _; apply Differentiable.const_mul; simp

lemma deriv_mathematicalPartitionFunctionBetaReal (b : ℝ) :
    deriv 𝓒.mathematicalPartitionFunctionBetaReal b = -𝓒.meanEnergyNumerator b := by
  unfold mathematicalPartitionFunctionBetaReal meanEnergyNumerator
  have hd : ∀ c : ℝ, HasDerivAt (fun x => Real.exp (-x * c)) (-c * Real.exp (-b * c)) b := by
    intro c
    have h : HasDerivAt (fun x => -x * c) (-c) b := by
      simpa using (hasDerivAt_id b).neg.mul_const c
    simpa [mul_comm] using h.exp
  have h_sum : HasDerivAt (fun x => ∑ i, Real.exp (-x * 𝓒.energy i))
      (∑ i, -𝓒.energy i * Real.exp (-b * 𝓒.energy i)) b :=
    HasDerivAt.fun_sum fun i _ => hd (𝓒.energy i)
  simpa [Finset.sum_neg_distrib] using h_sum.deriv

/-- Finite Gibbs identity used in arXiv:2112.15212v1, Eq. (3.7): the mean energy is
the negative derivative of `log Z` with respect to the real inverse temperature.  This is the
finite-sum specialization of the measure-theoretic canonical-ensemble result in `Lemmas.lean`. -/
lemma meanEnergyBetaReal_eq_neg_deriv_log_partition [Nonempty ι] (b : ℝ) :
    𝓒.meanEnergyBetaReal b =
      -deriv (fun beta : ℝ => Real.log (𝓒.mathematicalPartitionFunctionBetaReal beta)) b := by
  have hZ_ne : 𝓒.mathematicalPartitionFunctionBetaReal b ≠ 0 :=
    (mathematicalPartitionFunctionBetaReal_pos 𝓒 b).ne'
  have hZ : HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal
      (-𝓒.meanEnergyNumerator b) b := by
    have hd := (differentiable_mathematicalPartitionFunctionBetaReal 𝓒 b).hasDerivAt
    rw [deriv_mathematicalPartitionFunctionBetaReal 𝓒 b] at hd
    exact hd
  have hlog := (Real.hasDerivAt_log hZ_ne).comp b hZ
  have hlog' : HasDerivAt
      (fun beta : ℝ => Real.log (𝓒.mathematicalPartitionFunctionBetaReal beta))
      ((𝓒.mathematicalPartitionFunctionBetaReal b)⁻¹ *
        (-𝓒.meanEnergyNumerator b)) b := by
    simpa [Function.comp_def] using hlog
  rw [hlog'.deriv]
  simp only [meanEnergyBetaReal, probabilityBetaReal, meanEnergyNumerator]
  simp_rw [← mul_div_assoc]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

lemma deriv_meanEnergyNumerator (b : ℝ) :
    deriv 𝓒.meanEnergyNumerator b =
      -∑ i, (𝓒.energy i)^2 * Real.exp (-b * 𝓒.energy i) := by
  unfold meanEnergyNumerator
  have hd : ∀ c : ℝ, HasDerivAt (fun x => Real.exp (-x * c)) (-c * Real.exp (-b * c)) b := by
    intro c
    have h : HasDerivAt (fun x => -x * c) (-c) b := by
      simpa using (hasDerivAt_id b).neg.mul_const c
    simpa [mul_comm] using h.exp
  have h_sum : HasDerivAt (fun x => ∑ i, 𝓒.energy i * Real.exp (-x * 𝓒.energy i))
      (∑ i, -(𝓒.energy i)^2 * Real.exp (-b * 𝓒.energy i)) b := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    simpa [sq, mul_comm, mul_left_comm, mul_assoc] using
      (hd (𝓒.energy i)).const_mul (𝓒.energy i)
  simpa [Finset.sum_neg_distrib, sq, mul_comm, mul_left_comm, mul_assoc] using h_sum.deriv

/-! Quotient rule: dU/db = U^2 - ⟨E^2⟩_β -/

variable [Nonempty ι]

lemma deriv_meanEnergyBetaReal (b : ℝ) :
    deriv 𝓒.meanEnergyBetaReal b =
    (𝓒.meanEnergyBetaReal b)^2 - ∑ i, (𝓒.energy i)^2 * 𝓒.probabilityBetaReal b i := by
  have hN_diff := (differentiable_meanEnergyNumerator 𝓒) b
  have hZ_diff := (differentiable_mathematicalPartitionFunctionBetaReal 𝓒) b
  have hZ_ne : 𝓒.mathematicalPartitionFunctionBetaReal b ≠ 0 :=
    (mathematicalPartitionFunctionBetaReal_pos 𝓒 b).ne'
  have hU : 𝓒.meanEnergyBetaReal
      = 𝓒.meanEnergyNumerator / 𝓒.mathematicalPartitionFunctionBetaReal := by
    funext x
    simp [meanEnergyBetaReal, probabilityBetaReal, meanEnergyNumerator,
          mathematicalPartitionFunctionBetaReal, Pi.div_apply, Finset.sum_div, mul_div_assoc]
  have hprob : ∑ i, (𝓒.energy i)^2 * 𝓒.probabilityBetaReal b i
      = (∑ i, (𝓒.energy i)^2 * Real.exp (-b * 𝓒.energy i))
          / 𝓒.mathematicalPartitionFunctionBetaReal b := by
    simp [probabilityBetaReal, Finset.sum_div, mul_div_assoc]
  rw [hprob, hU, deriv_div hN_diff hZ_diff hZ_ne, deriv_meanEnergyNumerator,
      deriv_mathematicalPartitionFunctionBetaReal, Pi.div_apply]
  set S2 := ∑ i, (𝓒.energy i) ^ 2 * Real.exp (-b * 𝓒.energy i)
  field_simp
  ring

/-- (∂U/∂β) = -Var(E) for finite systems. -/
lemma derivWithin_meanEnergy_Beta_eq_neg_variance
    [MeasurableSingletonClass ι][𝓒.IsFinite] (T : Temperature) (hT_pos : 0 < T.val) :
    derivWithin 𝓒.meanEnergyBeta (Set.Ioi 0) (T.β : ℝ) = - 𝓒.energyVariance T := by
  let β₀ := (T.β : ℝ)
  have hβ₀_pos : 0 < β₀ := beta_pos T hT_pos
  have h_eq_on : Set.EqOn 𝓒.meanEnergyBeta 𝓒.meanEnergyBetaReal (Set.Ioi 0) := by
    intro b hb; exact meanEnergy_Beta_eq_finite 𝓒 b hb
  rw [derivWithin_congr h_eq_on (h_eq_on hβ₀_pos)]
  have h_diff : DifferentiableAt ℝ 𝓒.meanEnergyBetaReal β₀ :=
    (differentiable_meanEnergyBetaReal 𝓒) β₀
  rw [h_diff.derivWithin (uniqueDiffOn_Ioi 0 β₀ hβ₀_pos)]
  rw [deriv_meanEnergyBetaReal 𝓒 β₀]
  have h_U_eq : 𝓒.meanEnergyBetaReal β₀ = 𝓒.meanEnergy T := by
    rw [← meanEnergy_Beta_eq_finite 𝓒 β₀ hβ₀_pos]
    simp [meanEnergyBeta]
    simp_all only [NNReal.coe_pos, toNNReal_coe, ofβ_β, β₀]
  have h_prob_eq (i : ι) : 𝓒.probabilityBetaReal β₀ i = 𝓒.probability T i := by
    unfold probabilityBetaReal CanonicalEnsemble.probability
    congr 1
    · unfold mathematicalPartitionFunctionBetaReal
      rw [mathematicalPartitionFunction_of_fintype]
  rw [h_U_eq]
  simp_rw [h_prob_eq]
  rw [energyVariance_of_fintype 𝓒 T]
  ring

/-- FDT for finite canonical ensembles: C_V = Var(E) / (k_B T²). -/
theorem fluctuation_dissipation_theorem_finite
    [MeasurableSingletonClass ι] [𝓒.IsFinite] (T : Temperature) (hT_pos : 0 < T.val) :
    𝓒.heatCapacity T = 𝓒.energyVariance T / (kB * (T.val : ℝ)^2) := by
  have hβ₀_pos : 0 < (T.β : ℝ) := beta_pos T hT_pos
  let β₀ := (T.β : ℝ)
  have h_diff_U_beta : DifferentiableWithinAt ℝ 𝓒.meanEnergyBeta (Set.Ioi 0) β₀ := by
    have h_eq_on : Set.EqOn 𝓒.meanEnergyBeta 𝓒.meanEnergyBetaReal (Set.Ioi 0) := by
      intro b hb; exact meanEnergy_Beta_eq_finite 𝓒 b hb
    have h_diff' := (differentiable_meanEnergyBetaReal 𝓒) (T.β : ℝ)
    exact DifferentiableWithinAt.congr_of_eventuallyEq h_diff'.differentiableWithinAt
      (eventuallyEq_nhdsWithin_of_eqOn h_eq_on) (h_eq_on hβ₀_pos)
  have h_Var_eq_neg_dUdβ := derivWithin_meanEnergy_Beta_eq_neg_variance 𝓒 T hT_pos
  exact CanonicalEnsemble.fluctuation_dissipation_energy_parametric 𝓒 T hT_pos
    (by simp_all only [NNReal.coe_pos, neg_neg, β₀]) h_diff_U_beta

end FluctuationsFinite

end CanonicalEnsemble

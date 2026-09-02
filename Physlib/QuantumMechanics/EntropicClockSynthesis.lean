/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.CyclicAutomatonSpectrum
public import Physlib.StatisticalMechanics.CanonicalEnsemble.ParametricForce
public import Physlib.Thermodynamics.ComputationLandauer
public import Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.FiniteTarget.NagaoNielsenSchrodinger
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MisraJacobsonSynthesis
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenJonesPolynomialChernSimons
public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Physlib.Thermodynamics.Landauer
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.Meta.HypothesisInhabitationCheck
meta import Zil

/-!
# Clock, information, force, and correlation: the entropic-clock synthesis

The coherence layer binding four already-formalized pillars into one exact
structure - the clock (the cyclic automaton and its quantization), the
information ledger (Kullback-Leibler under computation), the thermodynamic
force (the parametric canonical ensemble), and the correlation bounds (the
CHSH combination):

* **The clock costs nothing.** The cyclic automaton's step, encoded as the
  injective driver `j ↦ (j+1) mod N` on the naturals
  (`cogwheelNatStep_injective`, intertwining the residue shift through the
  value map, `cogwheelNatStep_val`), preserves Kullback-Leibler divergence
  exactly as a computation channel (`cogwheel_channel_keeps_kl`) - the clock
  sits on the reversible side of the Landauer dichotomy.
* **The force conjugate to the tick.** For a spectrum scaling as `ε/λ` in
  the tick `λ` - the cyclic-automaton ladder `2πk/(Nδt)` is of this form -
  the Hellmann-Feynman derivative of the canonical free energy is minus the
  mean energy over the tick (`tick_force_virial`): `λ ∂λF = -U`, the exact
  virial-type identity for clock-rate thermodynamics, with the
  Kullback-Leibler ledger tied to the same free energy by the existing
  variational identity (`freeEnergy_sub_eq_kl`: excess free energy is
  `T` times the divergence from the Gibbs state).
* **Shared randomness cannot beat the classical bound.** Averaging the CHSH
  combination over any probability weight on deterministic assignments stays
  within `2` (`sharedRandomness_chsh_bound`) - the convex closure of the
  local bound: zero shared quantum information means factorized statistics
  and at most `2`.
* **The quantum optimum lives on the clock.** The CHSH-optimal analyzer
  phases are eighth-root clock angles, and the Tsirelson combination of
  their characters is exactly `2√2` (`stdAddChar_re`,
  `tsirelson_on_eight_clock`) - the quantum value written as a `ZMod 8`
  character identity.
* **The Bell-information-gravity chain**
  (`bell_information_gravity_chain`): a CHSH violation at the correlator
  level - four no-signalling outcome tables whose CHSH combination
  exceeds `2` - propagates through exact arrows. The violation certifies
  strictly positive mutual information in some table
  (`chsh_violation_positive_mutual_information`, via the factorized
  bracket bound `chsh_correlator_bracket_bound` and the vanishing case of
  the Gibbs inequality `table_factorizes_of_kl_nonpos`); the certified
  divergence `D` carries the Landauer energy `kB T D`
  (`certified_information_landauer_energy`), counted in the same bit
  units the holographic layer applies to horizon area
  (`certified_entropy_bekenstein_bits`), and equals `β` times an excess
  Helmholtz free energy over the factorized equilibrium
  (`certified_information_excess_free_energy`); the Verlinde entropic
  force transporting the certificate's entropy across one screen
  displacement does exactly that Landauer work
  (`entropic_force_work_eq_landauer_energy`) and is strictly positive;
  and the same force law at the Unruh temperature of an accelerated
  screen is Newton's second law - correlation, information,
  thermodynamics, and gravitation linked by exact identities.
* **The antecedent is derived from the quantum state.** The Born rule for
  the maximally entangled pair state, measured in orthonormal analyzer
  bases whose vectors are `±1`-eigenvectors of the spin analyzer
  (`spinAnalyzer_eigen`), yields exactly the symmetric no-signalling
  table with correlation `cos (α - β)` (`bornOutcomeTable_eq`); at the
  eighth-root clock angles the correlators are the clock-character
  cosines and the CHSH combination is `2√2`
  (`eight_clock_table_violates`, consuming `tsirelson_on_eight_clock`).
  The `#physlib_hypotheses_inhabited` gate enforces that both
  conditionals have exhibited antecedents, closing the
  antecedent-failure vacuity class the non-vacuity gate cannot see.
* **The synthesis** (`entropic_clock_synthesis`): one statement carrying all
  four faces.

**Honest boundary.** The four faces are exact theorems and the links are the
stated identities; no unified dynamical law deriving all four from one
action is claimed and no quantitative information-correlation bound of
Pinsker type is proved. The witness table is derived by the Born rule from
the maximally entangled pair state in real amplitudes - the measurement
plane slice of the qubit pair, which suffices for these analyzer angles.
No-signalling marginal consistency is an assumption of the chain,
satisfied by the derived table. The chain's gravitational terminus is the
Verlinde-Unruh inertia identity cited from the thermodynamic layer; no
derivation of the Einstein equations from the Bell certificate is claimed.
-/

set_option autoImplicit false

open Real
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

@[expose] public section

namespace Physlib.QuantumMechanics.EntropicClockSynthesis

open Physlib.QuantumMechanics.CyclicAutomatonSpectrum
open Physlib.Thermodynamics.ComputationLandauer
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
open Physlib.Thermodynamics
open Physlib.Thermodynamics.Landauer
open CanonicalEnsemble

variable (N : ℕ) [NeZero N]

/-! ## The clock as a reversible computation channel -/

/-- **The clock driver on the naturals**: the cyclic step below `N`, the
identity above - the automaton encoded for the computation-thermodynamics
layer. -/
def cogwheelNatStep : ℕ → ℕ := fun j => if j < N then (j + 1) % N else j

/-- The residue shift in value form. -/
theorem cyclicShift_val (k : ZMod N) :
    (cyclicShift N k).val = (k.val + 1) % N := by
  have h : cyclicShift N k = ((k.val + 1 : ℕ) : ZMod N) := by
    rw [show cyclicShift N k = k + 1 from rfl]
    push_cast [ZMod.natCast_zmod_val]
    rfl
  rw [h, ZMod.val_natCast]

/-- **The clock driver intertwines the residue shift** through the value
map: the natural-number encoding is faithful to the automaton. -/
@[zil_level bridge_theorem]
theorem cogwheelNatStep_val (k : ZMod N) :
    cogwheelNatStep N k.val = (cyclicShift N k).val := by
  unfold cogwheelNatStep
  rw [if_pos (ZMod.val_lt k), cyclicShift_val]

/-- **The clock driver is injective** - the clock sits on the reversible
side of the Carneiro-basis split of the computation-thermodynamics layer. -/
@[zil_level physical_theorem]
theorem cogwheelNatStep_injective : Function.Injective (cogwheelNatStep N) := by
  have hval : ∀ a, a < N →
      cogwheelNatStep N a = if a + 1 = N then 0 else a + 1 := by
    intro a ha
    unfold cogwheelNatStep
    rw [if_pos ha]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt ha) with h | h
    · have h' : a + 1 = N := h
      rw [if_pos h', h', Nat.mod_self]
    · have h' : a + 1 < N := h
      rw [if_neg (Nat.ne_of_lt h'), Nat.mod_eq_of_lt h']
  intro a b hab
  by_cases ha : a < N <;> by_cases hb : b < N
  · rw [hval a ha, hval b hb] at hab
    split_ifs at hab <;> omega
  · rw [hval a ha] at hab
    unfold cogwheelNatStep at hab
    rw [if_neg hb] at hab
    split_ifs at hab <;> omega
  · rw [hval b hb] at hab
    unfold cogwheelNatStep at hab
    rw [if_neg ha] at hab
    split_ifs at hab <;> omega
  · unfold cogwheelNatStep at hab
    rwa [if_neg ha, if_neg hb] at hab

/-- **The clock channel preserves Kullback-Leibler divergence**: as a
computation channel, one clock step costs no information - the clock is
thermodynamically free, in exact contrast with erasure. -/
@[zil_level bridge_theorem]
theorem cogwheel_channel_keeps_kl (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ ⊗ₘ computationKernel (cogwheelNatStep N))
        (ν ⊗ₘ computationKernel (cogwheelNatStep N)) = klDiv μ ν :=
  computation_keeps_kl (cogwheelNatStep N) μ ν

/-! ## The force conjugate to the clock tick -/

/-- **The tick-force virial identity**: for a spectrum scaling as `ε/λ` in
the tick `λ` - the form of the cyclic-automaton ladder `2πk/(Nδt)` - the
free-energy derivative in the tick is minus the mean energy over the tick:
`λ ∂λF = -U`. The thermodynamic force conjugate to the clock rate is set by
the clock's own mean energy. -/
@[zil_level bridge_theorem]
theorem tick_force_virial {ι : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] {b : ℝ} (hb : b ≠ 0)
    (ε : ι → ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    HasDerivAt
      (fun l => (ofFiniteEnergy (fun i => ε i / l)).freeEnergyBetaReal b)
      (-(1 / lam) *
        (ofFiniteEnergy (fun i => ε i / lam)).meanEnergyBetaReal b) lam := by
  have hE : ∀ i, HasDerivAt (fun l : ℝ => ε i / l) (-(ε i / lam ^ 2)) lam := by
    intro i
    have h1 : HasDerivAt (fun l : ℝ => ε i * l⁻¹)
        (ε i * -(lam ^ 2)⁻¹) lam := (hasDerivAt_inv hlam).const_mul (ε i)
    have hfun : (fun l : ℝ => ε i / l) = fun l : ℝ => ε i * l⁻¹ := by
      funext l
      rw [div_eq_mul_inv]
    have hval : ε i * -(lam ^ 2)⁻¹ = -(ε i / lam ^ 2) := by
      field_simp
    rw [hfun, ← hval]
    exact h1
  have hHF := hasDerivAt_parametric_freeEnergy (ι := ι) hb
    (fun l i => ε i / l) (fun i => -(ε i / lam ^ 2)) lam hE
  convert hHF using 1
  show -(1 / lam) *
      (ofFiniteEnergy (fun i => ε i / lam)).meanEnergyBetaReal b
    = ∑ i, (ofFiniteEnergy (fun i => ε i / lam)).probabilityBetaReal b i *
        -(ε i / lam ^ 2)
  unfold CanonicalEnsemble.meanEnergyBetaReal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show -(1 / lam) *
      ((ε i / lam) *
        (ofFiniteEnergy (fun i => ε i / lam)).probabilityBetaReal b i)
    = (ofFiniteEnergy (fun i => ε i / lam)).probabilityBetaReal b i *
        -(ε i / lam ^ 2)
  field_simp

/-! ## Correlation: the convex classical bound and the clock-angle optimum -/

/-- **Shared randomness cannot beat the classical bound**: averaging the
CHSH combination over any probability weight on deterministic assignments
stays within `2` - the convex closure of the local-hidden-variable bound.
Zero shared quantum information means factorized statistics and at most
`2`. -/
@[zil_level bridge_theorem]
theorem sharedRandomness_chsh_bound {κ : Type*} [Fintype κ]
    (x : κ → CHSHAssignment) (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    |∑ i, w i * ((classicalCHSHValue (x i) : ℤ) : ℝ)| ≤ 2 := by
  calc |∑ i, w i * ((classicalCHSHValue (x i) : ℤ) : ℝ)|
      ≤ ∑ i, |w i * ((classicalCHSHValue (x i) : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hw i)]
        have hS : |((classicalCHSHValue (x i) : ℤ) : ℝ)| ≤ 2 := by
          exact_mod_cast classicalCHSH_bound (x i)
        exact mul_le_mul_of_nonneg_left hS (hw i)
    _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The real part of the standard character is the clock-angle cosine. -/
theorem stdAddChar_re (j : ℤ) :
    (ZMod.stdAddChar ((j : ℤ) : ZMod N)).re = Real.cos (2 * π * j / N) := by
  rw [ZMod.stdAddChar_coe]
  have h : (2 * (π : ℂ) * Complex.I * (j : ℂ) / (N : ℂ))
      = ((2 * π * (j : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

/-- **The Tsirelson combination on the eighth-root clock**: the CHSH-optimal
analyzer phases are eighth-root clock angles, and the combination of their
character cosines is exactly `2√2` - the quantum CHSH value written as a
`ZMod 8` character identity. -/
@[zil_level bridge_theorem]
theorem tsirelson_on_eight_clock :
    3 * (ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re
      - (ZMod.stdAddChar (((3 : ℤ) : ZMod 8))).re = 2 * Real.sqrt 2 := by
  rw [stdAddChar_re 8 1, stdAddChar_re 8 3]
  have h1 : (2 * π * ((1 : ℤ) : ℝ) / ((8 : ℕ) : ℝ)) = π / 4 := by
    push_cast
    ring
  have h3 : (2 * π * ((3 : ℤ) : ℝ) / ((8 : ℕ) : ℝ)) = π - π / 4 := by
    push_cast
    ring
  rw [h1, h3, Real.cos_pi_sub, Real.cos_pi_div_four]
  ring

/-! ## Program anchors: the Compton trinity clock, the discrete age, the
damped contour phase, and the clock partition function -/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity in
/-- **The Compton clock strobes to the automaton**: at the physical rotation
frequency `ω_C = mc²/ħ` of the frequency trinity, one commensurate tick
lands exactly on the primitive root of unity - the automaton samples the
mass clock. -/
@[zil_level bridge_theorem]
theorem compton_tick_primitive_root (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0)
    (hħ : ħ ≠ 0) :
    Complex.exp (Complex.I * comptonFrequency m c ħ *
        (2 * π / (N * comptonFrequency m c ħ)))
      = ZMod.stdAddChar (((1 : ℤ) : ZMod N)) := by
  refine rotation_tick_eq_primitive_root N _ ?_
  unfold comptonFrequency
  exact div_ne_zero (mul_ne_zero hm (pow_ne_zero 2 hc)) hħ

/-- **The discrete age observable**: the clock reading advances by exactly
one unit per step, modulo the period - `j` steps take the reading to
`(v + j) mod N`. The discrete face of the Misra-type internal time; the
continuous Misra operator lives on the line, where Pauli's obstruction to a
time operator does not apply. -/
@[zil_level bridge_theorem]
theorem clock_reading_advances (k : ZMod N) (j : ℕ) :
    ((⇑(cyclicShift N))^[j] k).val = (k.val + j) % N := by
  have h : (⇑(cyclicShift N))^[j] k = ((k.val + j : ℕ) : ZMod N) := by
    rw [cyclicShift_iterate]
    push_cast [ZMod.natCast_zmod_val]
    rfl
  rw [h, ZMod.val_natCast]

/-- **The damped contour phase**: complexifying the clock energy by `-iγ` -
the contour deformation of the complex-action program - multiplies the
eigenphase modulus by `e^(-γ)` per step. -/
@[zil_level bridge_theorem]
theorem damped_clock_phase (E γ : ℝ) :
    ‖Complex.exp (-(Complex.I) * ((E : ℂ) - (γ : ℂ) * Complex.I))‖
      = Real.exp (-γ) := by
  have harg : -(Complex.I) * ((E : ℂ) - (γ : ℂ) * Complex.I)
      = ((-γ : ℝ) : ℂ) + ((-E : ℝ) : ℂ) * Complex.I := by
    push_cast
    linear_combination ((γ : ℂ)) * Complex.I_sq
  rw [harg, Complex.exp_add, norm_mul, ← Complex.ofReal_exp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Norm-squared decay per step at rate `2γ`** - the discrete face of the
non-Hermitian norm decay rate `d‖ψ‖²/dt = -(2/ħ)⟨H_I⟩` of the
complex-Hamiltonian program. -/
@[zil_level physical_theorem]
theorem damped_clock_norm_sq (E γ : ℝ) :
    ‖Complex.exp (-(Complex.I) * ((E : ℂ) - (γ : ℂ) * Complex.I))‖ ^ 2
      = Real.exp (-(2 * γ)) := by
  rw [damped_clock_phase, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

instance : MeasurableSpace (ZMod N) := ⊤

instance : MeasurableSingletonClass (ZMod N) := ⟨fun _ => trivial⟩

/-- **The clock partition function in closed form**: the canonical partition
function of the cyclic-automaton ladder sums to the finite geometric form
`(e^(-2πb) - 1)/(e^(-2πb/N) - 1)` - the exactly summable thermal side of
the periodic clock, the finite sibling of the analytic path-integral
partition functions of the Chern-Simons layer. -/
@[zil_level bridge_theorem]
theorem cogwheel_partition_closed_form {b : ℝ} (hb : b ≠ 0) :
    (ofFiniteEnergy
        (fun k : ZMod N => 2 * π * (k.val : ℝ) / N)).mathematicalPartitionFunctionBetaReal b
      = (Real.exp (-(2 * π * b)) - 1) / (Real.exp (-(2 * π * b / N)) - 1) := by
  have hNr : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hx : -(2 * π * b / N) ≠ 0 := by
    have h1 : 2 * π * b ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hb
    exact neg_ne_zero.mpr (div_ne_zero h1 hNr)
  have hr : Real.exp (-(2 * π * b / N)) ≠ 1 := by
    rw [Ne, Real.exp_eq_one_iff]
    exact hx
  have hZ : (ofFiniteEnergy
      (fun k : ZMod N => 2 * π * (k.val : ℝ) / N)).mathematicalPartitionFunctionBetaReal b
      = ∑ j ∈ Finset.range N, Real.exp (-(2 * π * b / N)) ^ j := by
    show (∑ k : ZMod N, Real.exp (-b * (2 * π * (k.val : ℝ) / N))) = _
    have hre : ∑ k : ZMod N, Real.exp (-b * (2 * π * (k.val : ℝ) / N))
        = ∑ j ∈ Finset.range N, Real.exp (-b * (2 * π * (j : ℝ) / N)) := by
      obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
      subst hM
      exact Fin.sum_univ_eq_sum_range
        (fun j => Real.exp (-b * (2 * π * (j : ℝ) / ((M + 1 : ℕ) : ℝ)))) (M + 1)
    rw [hre]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -b * (2 * π * (j : ℝ) / N) = (j : ℕ) * (-(2 * π * b / N)) from by
      push_cast
      ring, Real.exp_nat_mul]
  rw [hZ, geom_sum_eq hr N]
  have hpow : Real.exp (-(2 * π * b / N)) ^ N = Real.exp (-(2 * π * b)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hpow]

/-! ## The Bell-information-gravity chain -/

/-- **The local-strategy pair assignment**: Alice's wing read from her
strategy index alone, Bob's from his - the deterministic-assignment
combination of a local hidden-variable model over a pair of strategy
spaces. -/
def strategyPairAssignment {ι κ : Type*} (x : ι → CHSHAssignment)
    (y : κ → CHSHAssignment) (z : ι × κ) : CHSHAssignment :=
  ⟨(x z.1).a, (x z.1).aPrime, (y z.2).b, (y z.2).bPrime,
   (x z.1).ha, (x z.1).haPrime, (y z.2).hb, (y z.2).hbPrime⟩

/-- **Factorized statistics obey the classical bound**: when the weight
over strategy pairs is a product - zero mutual information between the
wings - the averaged CHSH combination stays within `2`. -/
@[zil_level physical_theorem]
theorem factorized_strategy_chsh_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (pX : ι → ℝ) (pY : κ → ℝ) (hX : ∀ i, 0 ≤ pX i) (hY : ∀ j, 0 ≤ pY j)
    (hXs : ∑ i, pX i = 1) (hYs : ∑ j, pY j = 1)
    (x : ι → CHSHAssignment) (y : κ → CHSHAssignment) :
    |∑ z : ι × κ, pX z.1 * pY z.2 *
        ((classicalCHSHValue (strategyPairAssignment x y z) : ℤ) : ℝ)| ≤ 2 := by
  refine sharedRandomness_chsh_bound (strategyPairAssignment x y)
    (fun z => pX z.1 * pY z.2) (fun z => mul_nonneg (hX z.1) (hY z.2)) ?_
  calc ∑ z : ι × κ, pX z.1 * pY z.2
      = ∑ i, ∑ j, pX i * pY j := Fintype.sum_prod_type _
    _ = (∑ i, pX i) * ∑ j, pY j := (Fintype.sum_mul_sum pX pY).symm
    _ = 1 := by rw [hXs, hYs, mul_one]

/-- The `±1` outcome value carried by a binary outcome label. -/
def outcomeSign : Bool → ℝ := fun s => if s then 1 else -1

@[simp] lemma outcomeSign_true : outcomeSign true = 1 := rfl

@[simp] lemma outcomeSign_false : outcomeSign false = -1 := rfl

/-- Expansion of a sum over the two-element outcome space. -/
lemma sum_bool_expand (f : Bool → ℝ) : ∑ s, f s = f true + f false := by
  rw [Fintype.univ_bool, Finset.sum_insert (by simp), Finset.sum_singleton]

/-- The **correlator** of a joint outcome table: the expectation of the
product of the two wings' `±1` outcomes. -/
def pairCorrelator (q : Bool × Bool → ℝ) : ℝ :=
  ∑ z : Bool × Bool, q z * outcomeSign z.1 * outcomeSign z.2

/-- A `±1` expectation of any subnormalized-to-one nonnegative weight lies
in `[-1, 1]`. -/
theorem abs_expectation_le_one (f : Bool → ℝ) (hf : ∀ s, 0 ≤ f s)
    (hfs : ∑ s, f s = 1) : |∑ s, outcomeSign s * f s| ≤ 1 := by
  rw [sum_bool_expand] at hfs
  rw [sum_bool_expand]
  simp only [outcomeSign_true, outcomeSign_false, one_mul, neg_one_mul]
  have h₀ := hf true
  have h₁ := hf false
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Product tables have factorized correlators**: the correlator of a
product outcome table is the product of the wing expectations. -/
theorem product_pairCorrelator (f g : Bool → ℝ) :
    pairCorrelator (fun z => f z.1 * g z.2)
      = (∑ s, outcomeSign s * f s) * (∑ t, outcomeSign t * g t) := by
  simp only [pairCorrelator, Fintype.sum_prod_type, sum_bool_expand,
    outcomeSign_true, outcomeSign_false]
  ring

/-- **The CHSH bracket bound**: four wing expectations in `[-1, 1]` keep
the CHSH combination of factorized correlators within `2`. -/
theorem chsh_correlator_bracket_bound {u u' v v' : ℝ}
    (hu : |u| ≤ 1) (hu' : |u'| ≤ 1) (hv : |v| ≤ 1) (hv' : |v'| ≤ 1) :
    |u * v + u * v' + u' * v - u' * v'| ≤ 2 := by
  obtain ⟨hv₁, hv₂⟩ := abs_le.mp hv
  obtain ⟨hv'₁, hv'₂⟩ := abs_le.mp hv'
  have key : |v + v'| + |v - v'| ≤ 2 := by
    rcases abs_cases (v + v') with ⟨e₁, _⟩ | ⟨e₁, _⟩ <;>
      rcases abs_cases (v - v') with ⟨e₂, _⟩ | ⟨e₂, _⟩ <;>
      rw [e₁, e₂] <;> linarith
  have hsplit : u * v + u * v' + u' * v - u' * v'
      = u * (v + v') + u' * (v - v') := by ring
  calc |u * v + u * v' + u' * v - u' * v'|
      = |u * (v + v') + u' * (v - v')| := by rw [hsplit]
    _ ≤ |u * (v + v')| + |u' * (v - v')| := abs_add_le _ _
    _ = |u| * |v + v'| + |u'| * |v - v'| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |v + v'| + 1 * |v - v'| :=
        add_le_add (mul_le_mul_of_nonneg_right hu (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hu' (abs_nonneg _))
    _ = |v + v'| + |v - v'| := by ring
    _ ≤ 2 := key

/-- **Vanishing mutual information factorizes the table**: an outcome
table whose Kullback-Leibler divergence from the product of its marginals
is nonpositive is that product, pointwise - the vanishing case of the
Gibbs inequality. -/
theorem table_factorizes_of_kl_nonpos (q : Bool × Bool → ℝ)
    (hq : ∀ z, 0 < q z) (hqs : ∑ z, q z = 1)
    (hle : klDivergence q
      (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2))) ≤ 0) :
    ∀ z, q z = (∑ t, q (z.1, t)) * (∑ s, q (s, z.2)) := by
  have hXs : (∑ s, ∑ t, q (s, t)) = 1 := by
    rw [← Fintype.sum_prod_type]
    exact hqs
  have hYs : (∑ t, ∑ s, q (s, t)) = 1 := by
    rw [← Fintype.sum_prod_type_right]
    exact hqs
  have hpX : ∀ s, 0 < ∑ t, q (s, t) := fun s =>
    Finset.sum_pos (fun t _ => hq (s, t)) Finset.univ_nonempty
  have hpY : ∀ t, 0 < ∑ s, q (s, t) := fun t =>
    Finset.sum_pos (fun s _ => hq (s, t)) Finset.univ_nonempty
  have hprod : ∀ z : Bool × Bool, 0 < (∑ t, q (z.1, t)) * (∑ s, q (s, z.2)) :=
    fun z => mul_pos (hpX z.1) (hpY z.2)
  have hqsum : ∑ z : Bool × Bool,
      (∑ t, q (z.1, t)) * (∑ s, q (s, z.2)) = 1 := by
    calc ∑ z : Bool × Bool, (∑ t, q (z.1, t)) * (∑ s, q (s, z.2))
        = ∑ a, ∑ b, (∑ t, q (a, t)) * (∑ s, q (s, b)) :=
          Fintype.sum_prod_type _
      _ = (∑ a, ∑ t, q (a, t)) * ∑ b, ∑ s, q (s, b) :=
          (Fintype.sum_mul_sum _ _).symm
      _ = 1 := by rw [hXs, hYs, mul_one]
  have hzero : klDivergence q
      (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2))) = 0 :=
    le_antisymm hle (mutualInformation_nonneg q (fun s => ∑ t, q (s, t))
      (fun t => ∑ s, q (s, t)) (fun z => (hq z).le) hpX hpY hqs hXs hYs)
  have h := (klDivergence_eq_zero_iff hq hprod hqs hqsum).mp hzero
  intro z
  conv_lhs => rw [h]

/-- **A CHSH violation certifies positive mutual information**: for four
setting-pair outcome tables obeying no-signalling marginal consistency, if
the CHSH combination of their correlators exceeds the classical bound `2`,
at least one table carries strictly positive mutual information between
the wings - its Kullback-Leibler divergence from the product of its own
marginals is strictly positive. Correlation beyond the classical bound has
an exact information price. The antecedent is inhabited: the eight-clock
quantum table realizes every hypothesis (`eight_clock_table_violates`),
enforced by `#physlib_hypotheses_inhabited`. -/
@[zil_level bridge_theorem]
theorem chsh_violation_positive_mutual_information
    (q₁ q₂ q₃ q₄ : Bool × Bool → ℝ)
    (h₁ : ∀ z, 0 < q₁ z) (h₂ : ∀ z, 0 < q₂ z)
    (h₃ : ∀ z, 0 < q₃ z) (h₄ : ∀ z, 0 < q₄ z)
    (hs₁ : ∑ z, q₁ z = 1) (hs₂ : ∑ z, q₂ z = 1)
    (hs₃ : ∑ z, q₃ z = 1) (hs₄ : ∑ z, q₄ z = 1)
    (hA : ∀ s, (∑ t, q₁ (s, t)) = ∑ t, q₂ (s, t))
    (hA' : ∀ s, (∑ t, q₃ (s, t)) = ∑ t, q₄ (s, t))
    (hB : ∀ t, (∑ s, q₁ (s, t)) = ∑ s, q₃ (s, t))
    (hB' : ∀ t, (∑ s, q₂ (s, t)) = ∑ s, q₄ (s, t))
    (hviol : 2 < |pairCorrelator q₁ + pairCorrelator q₂
        + pairCorrelator q₃ - pairCorrelator q₄|) :
    (0 < klDivergence q₁ (fun z => (∑ t, q₁ (z.1, t)) * (∑ s, q₁ (s, z.2))))
    ∨ (0 < klDivergence q₂ (fun z => (∑ t, q₂ (z.1, t)) * (∑ s, q₂ (s, z.2))))
    ∨ (0 < klDivergence q₃ (fun z => (∑ t, q₃ (z.1, t)) * (∑ s, q₃ (s, z.2))))
    ∨ (0 < klDivergence q₄
        (fun z => (∑ t, q₄ (z.1, t)) * (∑ s, q₄ (s, z.2)))) := by
  by_contra hall
  push_neg at hall
  obtain ⟨n₁, n₂, n₃, n₄⟩ := hall
  have hf₁ := table_factorizes_of_kl_nonpos q₁ h₁ hs₁ n₁
  have hf₂ := table_factorizes_of_kl_nonpos q₂ h₂ hs₂ n₂
  have hf₃ := table_factorizes_of_kl_nonpos q₃ h₃ hs₃ n₃
  have hf₄ := table_factorizes_of_kl_nonpos q₄ h₄ hs₄ n₄
  have hc₁ : pairCorrelator q₁
      = (∑ s, outcomeSign s * (∑ t, q₁ (s, t)))
        * (∑ t, outcomeSign t * (∑ s, q₁ (s, t))) :=
    (congrArg pairCorrelator (funext hf₁)).trans
      (product_pairCorrelator (fun s => ∑ t, q₁ (s, t)) (fun t => ∑ s, q₁ (s, t)))
  have hc₂ : pairCorrelator q₂
      = (∑ s, outcomeSign s * (∑ t, q₂ (s, t)))
        * (∑ t, outcomeSign t * (∑ s, q₂ (s, t))) :=
    (congrArg pairCorrelator (funext hf₂)).trans
      (product_pairCorrelator (fun s => ∑ t, q₂ (s, t)) (fun t => ∑ s, q₂ (s, t)))
  have hc₃ : pairCorrelator q₃
      = (∑ s, outcomeSign s * (∑ t, q₃ (s, t)))
        * (∑ t, outcomeSign t * (∑ s, q₃ (s, t))) :=
    (congrArg pairCorrelator (funext hf₃)).trans
      (product_pairCorrelator (fun s => ∑ t, q₃ (s, t)) (fun t => ∑ s, q₃ (s, t)))
  have hc₄ : pairCorrelator q₄
      = (∑ s, outcomeSign s * (∑ t, q₄ (s, t)))
        * (∑ t, outcomeSign t * (∑ s, q₄ (s, t))) :=
    (congrArg pairCorrelator (funext hf₄)).trans
      (product_pairCorrelator (fun s => ∑ t, q₄ (s, t)) (fun t => ∑ s, q₄ (s, t)))
  have hu₂ : (∑ s, outcomeSign s * (∑ t, q₂ (s, t)))
      = ∑ s, outcomeSign s * (∑ t, q₁ (s, t)) :=
    Finset.sum_congr rfl fun s _ => by rw [← hA s]
  have hu₄ : (∑ s, outcomeSign s * (∑ t, q₄ (s, t)))
      = ∑ s, outcomeSign s * (∑ t, q₃ (s, t)) :=
    Finset.sum_congr rfl fun s _ => by rw [← hA' s]
  have hv₃ : (∑ t, outcomeSign t * (∑ s, q₃ (s, t)))
      = ∑ t, outcomeSign t * (∑ s, q₁ (s, t)) :=
    Finset.sum_congr rfl fun t _ => by rw [← hB t]
  have hv₄ : (∑ t, outcomeSign t * (∑ s, q₄ (s, t)))
      = ∑ t, outcomeSign t * (∑ s, q₂ (s, t)) :=
    Finset.sum_congr rfl fun t _ => by rw [← hB' t]
  have hu : |∑ s, outcomeSign s * (∑ t, q₁ (s, t))| ≤ 1 :=
    abs_expectation_le_one _
      (fun s => (Finset.sum_pos (fun t _ => h₁ (s, t))
        Finset.univ_nonempty).le)
      (by rw [← Fintype.sum_prod_type]; exact hs₁)
  have hu' : |∑ s, outcomeSign s * (∑ t, q₃ (s, t))| ≤ 1 :=
    abs_expectation_le_one _
      (fun s => (Finset.sum_pos (fun t _ => h₃ (s, t))
        Finset.univ_nonempty).le)
      (by rw [← Fintype.sum_prod_type]; exact hs₃)
  have hv : |∑ t, outcomeSign t * (∑ s, q₁ (s, t))| ≤ 1 :=
    abs_expectation_le_one _
      (fun t => (Finset.sum_pos (fun s _ => h₁ (s, t))
        Finset.univ_nonempty).le)
      (by rw [← Fintype.sum_prod_type_right]; exact hs₁)
  have hv' : |∑ t, outcomeSign t * (∑ s, q₂ (s, t))| ≤ 1 :=
    abs_expectation_le_one _
      (fun t => (Finset.sum_pos (fun s _ => h₂ (s, t))
        Finset.univ_nonempty).le)
      (by rw [← Fintype.sum_prod_type_right]; exact hs₂)
  rw [hc₁, hc₂, hc₃, hc₄, hu₂, hu₄, hv₃, hv₄] at hviol
  exact absurd hviol (not_lt.mpr (chsh_correlator_bracket_bound hu hu' hv hv'))

/-- The **symmetric correlated pair table** at correlation `E`: the unique
no-signalling table with uniform wing marginals and correlator `E` - the
quantum outcome statistics of a maximally entangled pair at analyzer
angles with correlation `E`. -/
noncomputable def correlatedPairTable (E : ℝ) : Bool × Bool → ℝ :=
  fun z => (1 + E * outcomeSign z.1 * outcomeSign z.2) / 4

theorem correlatedPairTable_pos {E : ℝ} (hE : |E| < 1) :
    ∀ z, 0 < correlatedPairTable E z := by
  obtain ⟨hl, hr⟩ := abs_lt.mp hE
  rintro ⟨s, t⟩
  cases s <;> cases t <;>
    simp only [correlatedPairTable, outcomeSign_true, outcomeSign_false,
      mul_one, mul_neg, neg_neg] <;>
    exact div_pos (by linarith) (by norm_num)

theorem correlatedPairTable_sum (E : ℝ) :
    ∑ z, correlatedPairTable E z = 1 := by
  simp only [correlatedPairTable, Fintype.sum_prod_type, sum_bool_expand,
    outcomeSign_true, outcomeSign_false]
  ring

theorem correlatedPairTable_marginalFst (E : ℝ) (s : Bool) :
    (∑ t, correlatedPairTable E (s, t)) = 1 / 2 := by
  cases s <;>
    simp only [correlatedPairTable, sum_bool_expand, outcomeSign_true,
      outcomeSign_false] <;>
    ring

theorem correlatedPairTable_marginalSnd (E : ℝ) (t : Bool) :
    (∑ s, correlatedPairTable E (s, t)) = 1 / 2 := by
  cases t <;>
    simp only [correlatedPairTable, sum_bool_expand, outcomeSign_true,
      outcomeSign_false] <;>
    ring

theorem correlatedPairTable_correlator (E : ℝ) :
    pairCorrelator (correlatedPairTable E) = E := by
  simp only [pairCorrelator, correlatedPairTable, Fintype.sum_prod_type,
    sum_bool_expand, outcomeSign_true, outcomeSign_false]
  ring

/-! ### The Born-rule derivation of the witness table -/

/-- The **analyzer basis** at angle `θ`: the orthonormal eigenbasis of the
spin analyzer along direction `θ` in the measurement plane -
`|+⟩ = (cos θ/2, sin θ/2)`, `|-⟩ = (-sin θ/2, cos θ/2)`. -/
noncomputable def analyzerVector (θ : ℝ) : Bool → Bool → ℝ
  | true, false => Real.cos (θ / 2)
  | true, true => Real.sin (θ / 2)
  | false, false => -(Real.sin (θ / 2))
  | false, true => Real.cos (θ / 2)

/-- The **spin analyzer** along angle `θ` in the measurement plane:
`cos θ σ_z + sin θ σ_x`. -/
noncomputable def spinAnalyzer (θ : ℝ) : Bool → Bool → ℝ
  | false, false => Real.cos θ
  | false, true => Real.sin θ
  | true, false => Real.sin θ
  | true, true => -(Real.cos θ)

/-- The **maximally entangled pair state** `(|00⟩ + |11⟩)/√2`. -/
noncomputable def bellPairState : Bool × Bool → ℝ
  | (false, false) => (Real.sqrt 2)⁻¹
  | (true, true) => (Real.sqrt 2)⁻¹
  | (false, true) => 0
  | (true, false) => 0

/-- **The analyzer basis vectors are normalized** at every angle. -/
theorem analyzerVector_orthonormal_self (θ : ℝ) (s : Bool) :
    ∑ i, analyzerVector θ s i * analyzerVector θ s i = 1 := by
  cases s <;>
    simp only [analyzerVector, sum_bool_expand, neg_mul, mul_neg, neg_neg] <;>
    linear_combination Real.sin_sq_add_cos_sq (θ / 2)

/-- **The two analyzer basis vectors are orthogonal** at every angle. -/
theorem analyzerVector_orthogonal (θ : ℝ) :
    ∑ i, analyzerVector θ true i * analyzerVector θ false i = 0 := by
  simp only [analyzerVector, sum_bool_expand, mul_neg]
  ring

/-- **The pair state is normalized.** -/
theorem bellPairState_normalized : ∑ z, bellPairState z ^ 2 = 1 := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  simp only [Fintype.sum_prod_type, sum_bool_expand, bellPairState, h2]
  norm_num

/-- **The measurement outcomes are eigenvalues**: the analyzer basis
vectors are eigenvectors of the spin analyzer along the same angle, with
eigenvalues the `±1` outcome values - the outcomes of the Bell experiment
are the spectrum of the measured observable. -/
@[zil_level physical_theorem]
theorem spinAnalyzer_eigen (θ : ℝ) (s : Bool) (i : Bool) :
    ∑ j, spinAnalyzer θ i j * analyzerVector θ s j
      = outcomeSign s * analyzerVector θ s i := by
  have hc := Real.cos_sub θ (θ / 2)
  have hs := Real.sin_sub θ (θ / 2)
  rw [show θ - θ / 2 = θ / 2 from by ring] at hc hs
  cases s <;> cases i <;>
    simp only [spinAnalyzer, analyzerVector, outcomeSign_true,
      outcomeSign_false, sum_bool_expand, neg_mul, mul_neg, neg_neg,
      one_mul] <;>
    first
    | linear_combination hs
    | linear_combination hc
    | linear_combination (-1 : ℝ) * hc
    | linear_combination (-1 : ℝ) * hs

/-- The **Born amplitude** for the outcome pair `(s, t)` at analyzer
angles `(α, β)`: the inner product of the product analyzer state with the
entangled pair state. -/
noncomputable def bornAmplitude (α β : ℝ) (s t : Bool) : ℝ :=
  ∑ i, ∑ j, analyzerVector α s i * analyzerVector β t j * bellPairState (i, j)

/-- The Born amplitude for equal outcomes: `cos` of the half-difference. -/
theorem bornAmplitude_eq_of_eq (α β : ℝ) (s : Bool) :
    bornAmplitude α β s s = (Real.sqrt 2)⁻¹ * Real.cos ((α - β) / 2) := by
  have hc := Real.cos_sub (α / 2) (β / 2)
  rw [show α / 2 - β / 2 = (α - β) / 2 from by ring] at hc
  cases s <;>
    simp only [bornAmplitude, analyzerVector, bellPairState, sum_bool_expand,
      mul_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg] <;>
    linear_combination (-(Real.sqrt 2)⁻¹) * hc

/-- The Born amplitude for opposite outcomes: `±sin` of the
half-difference. -/
theorem bornAmplitude_eq_of_ne (α β : ℝ) {s t : Bool} (hst : s ≠ t) :
    bornAmplitude α β s t
      = (Real.sqrt 2)⁻¹ * (outcomeSign s * Real.sin ((α - β) / 2)) := by
  have hs' := Real.sin_sub (α / 2) (β / 2)
  rw [show α / 2 - β / 2 = (α - β) / 2 from by ring] at hs'
  cases s <;> cases t
  · exact absurd rfl hst
  · simp only [bornAmplitude, analyzerVector, bellPairState, sum_bool_expand,
      outcomeSign_false, mul_zero, add_zero, zero_add, neg_mul, mul_neg,
      neg_neg, one_mul]
    linear_combination (Real.sqrt 2)⁻¹ * hs'
  · simp only [bornAmplitude, analyzerVector, bellPairState, sum_bool_expand,
      outcomeSign_true, mul_zero, add_zero, zero_add, neg_mul, mul_neg,
      neg_neg, one_mul]
    linear_combination (-(Real.sqrt 2)⁻¹) * hs'
  · exact absurd rfl hst

/-- The **Born outcome table** at analyzer angles `(α, β)`: outcome
probabilities as squared Born amplitudes. -/
noncomputable def bornOutcomeTable (α β : ℝ) : Bool × Bool → ℝ := fun z =>
  bornAmplitude α β z.1 z.2 ^ 2

/-- **The Born rule yields the correlated pair table**: measuring the
maximally entangled pair state in the analyzer bases at angles `α` and
`β` produces exactly the symmetric no-signalling table with correlation
`cos (α - β)`. The outcome statistics of the chain's witness are derived
from a quantum state and measurement bases, not postulated. -/
@[zil_level bridge_theorem]
theorem bornOutcomeTable_eq (α β : ℝ) :
    bornOutcomeTable α β = correlatedPairTable (Real.cos (α - β)) := by
  have hpyth := Real.sin_sq_add_cos_sq ((α - β) / 2)
  have hd : Real.cos (α - β)
      = Real.cos ((α - β) / 2) ^ 2 - Real.sin ((α - β) / 2) ^ 2 := by
    have h := Real.cos_add ((α - β) / 2) ((α - β) / 2)
    rw [show (α - β) / 2 + (α - β) / 2 = α - β from by ring] at h
    linear_combination h
  have hinv : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  funext z
  obtain ⟨s, t⟩ := z
  simp only [bornOutcomeTable]
  cases s <;> cases t
  · rw [bornAmplitude_eq_of_eq, mul_pow, hinv, hd]
    simp only [correlatedPairTable, outcomeSign_false, mul_neg, neg_mul,
      neg_neg, mul_one]
    linear_combination (1 / 4 : ℝ) * hpyth
  · rw [bornAmplitude_eq_of_ne α β (by decide), mul_pow, mul_pow, hinv, hd]
    simp only [correlatedPairTable, outcomeSign_false, outcomeSign_true,
      mul_neg, neg_mul, neg_neg, mul_one, one_mul, neg_one_sq]
    linear_combination (1 / 4 : ℝ) * hpyth
  · rw [bornAmplitude_eq_of_ne α β (by decide), mul_pow, mul_pow, hinv, hd]
    simp only [correlatedPairTable, outcomeSign_false, outcomeSign_true,
      mul_neg, neg_mul, neg_neg, mul_one, one_mul, one_pow]
    linear_combination (1 / 4 : ℝ) * hpyth
  · rw [bornAmplitude_eq_of_eq, mul_pow, hinv, hd]
    simp only [correlatedPairTable, outcomeSign_true, mul_one, one_mul]
    linear_combination (1 / 4 : ℝ) * hpyth

/-- **The eight-clock table violates the classical bound**: the Born
outcome tables of the maximally entangled pair state, measured in
analyzer bases at the eighth-root clock angles `0, π/4, π/2, -π/4`, have
correlators equal to the clock-character cosines, satisfy every
hypothesis of `chsh_violation_positive_mutual_information` - positivity,
normalization, no-signalling - and their CHSH combination is `2√2 > 2` by
`tsirelson_on_eight_clock`. The Bell-side antecedent of the chain is
derived from the quantum state at the clock angles. -/
@[zil_level bridge_theorem]
theorem eight_clock_table_violates :
    ∃ q₁ q₂ q₃ q₄ : Bool × Bool → ℝ,
      (∀ z, 0 < q₁ z) ∧ (∀ z, 0 < q₂ z) ∧ (∀ z, 0 < q₃ z) ∧ (∀ z, 0 < q₄ z)
      ∧ (∑ z, q₁ z = 1) ∧ (∑ z, q₂ z = 1) ∧ (∑ z, q₃ z = 1)
      ∧ (∑ z, q₄ z = 1)
      ∧ (∀ s, (∑ t, q₁ (s, t)) = ∑ t, q₂ (s, t))
      ∧ (∀ s, (∑ t, q₃ (s, t)) = ∑ t, q₄ (s, t))
      ∧ (∀ t, (∑ s, q₁ (s, t)) = ∑ s, q₃ (s, t))
      ∧ (∀ t, (∑ s, q₂ (s, t)) = ∑ s, q₄ (s, t))
      ∧ 2 < |pairCorrelator q₁ + pairCorrelator q₂
          + pairCorrelator q₃ - pairCorrelator q₄| := by
  have hs2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs1 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hc1 : (ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re = Real.sqrt 2 / 2 := by
    rw [stdAddChar_re 8 1]
    have h1 : (2 * π * ((1 : ℤ) : ℝ) / ((8 : ℕ) : ℝ)) = π / 4 := by
      push_cast
      ring
    rw [h1, Real.cos_pi_div_four]
  have hc3 : (ZMod.stdAddChar (((3 : ℤ) : ZMod 8))).re
      = -(Real.sqrt 2 / 2) := by
    rw [stdAddChar_re 8 3]
    have h3 : (2 * π * ((3 : ℤ) : ℝ) / ((8 : ℕ) : ℝ)) = π - π / 4 := by
      push_cast
      ring
    rw [h3, Real.cos_pi_sub, Real.cos_pi_div_four]
  have habs1 : |(ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re| < 1 := by
    rw [hc1, abs_lt]
    constructor <;> linarith [Real.sqrt_nonneg 2]
  have habs3 : |(ZMod.stdAddChar (((3 : ℤ) : ZMod 8))).re| < 1 := by
    rw [hc3, abs_lt]
    constructor <;> linarith [Real.sqrt_nonneg 2]
  have e₁ : bornOutcomeTable 0 (π / 4)
      = correlatedPairTable ((ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re) := by
    rw [bornOutcomeTable_eq, show (0 : ℝ) - π / 4 = -(π / 4) from by ring,
      Real.cos_neg, Real.cos_pi_div_four, hc1]
  have e₂ : bornOutcomeTable 0 (-(π / 4))
      = correlatedPairTable ((ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re) := by
    rw [bornOutcomeTable_eq, show (0 : ℝ) - -(π / 4) = π / 4 from by ring,
      Real.cos_pi_div_four, hc1]
  have e₃ : bornOutcomeTable (π / 2) (π / 4)
      = correlatedPairTable ((ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re) := by
    rw [bornOutcomeTable_eq, show π / 2 - π / 4 = π / 4 from by ring,
      Real.cos_pi_div_four, hc1]
  have e₄ : bornOutcomeTable (π / 2) (-(π / 4))
      = correlatedPairTable ((ZMod.stdAddChar (((3 : ℤ) : ZMod 8))).re) := by
    rw [bornOutcomeTable_eq, show π / 2 - -(π / 4) = π - π / 4 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four, hc3]
  refine ⟨bornOutcomeTable 0 (π / 4), bornOutcomeTable 0 (-(π / 4)),
    bornOutcomeTable (π / 2) (π / 4), bornOutcomeTable (π / 2) (-(π / 4)),
    by rw [e₁]; exact correlatedPairTable_pos habs1,
    by rw [e₂]; exact correlatedPairTable_pos habs1,
    by rw [e₃]; exact correlatedPairTable_pos habs1,
    by rw [e₄]; exact correlatedPairTable_pos habs3,
    by rw [e₁]; exact correlatedPairTable_sum _,
    by rw [e₂]; exact correlatedPairTable_sum _,
    by rw [e₃]; exact correlatedPairTable_sum _,
    by rw [e₄]; exact correlatedPairTable_sum _,
    fun s => by rw [e₁, e₂],
    fun s => by
      rw [e₃, e₄, correlatedPairTable_marginalFst,
        correlatedPairTable_marginalFst],
    fun t => by rw [e₁, e₃],
    fun t => by
      rw [e₂, e₄, correlatedPairTable_marginalSnd,
        correlatedPairTable_marginalSnd],
    ?_⟩
  rw [e₁, e₂, e₃, e₄, correlatedPairTable_correlator,
    correlatedPairTable_correlator]
  have hsum : (ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re
      + (ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re
      + (ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re
      - (ZMod.stdAddChar (((3 : ℤ) : ZMod 8))).re = 2 * Real.sqrt 2 := by
    linarith [tsirelson_on_eight_clock]
  rw [hsum, abs_of_pos (mul_pos two_pos (Real.sqrt_pos.mpr two_pos))]
  linarith

/-- **The certified divergence is an excess free energy**: for a positive
reference distribution `Q` - the product of marginals of a violating
table - the Kullback-Leibler divergence from `Q` equals `β` times the
Helmholtz free energy at the reference energy landscape `-β⁻¹ log Q`,
whose Gibbs state at unit partition function is `Q` itself. The
information certificate of the Bell violation is the same object the
Gibbs variational identity prices in free energy. -/
@[zil_level bridge_theorem]
theorem certified_information_excess_free_energy {ι : Type*} [Fintype ι]
    {β : ℝ} (hβ : β ≠ 0) (p Q : ι → ℝ) (hQ : ∀ i, 0 < Q i)
    (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1) :
    klDivergence p Q
      = β * freeEnergy β (fun i => -(Real.log (Q i)) / β) p := by
  have hg : gibbsState β 1 (fun i => -(Real.log (Q i)) / β) = Q := by
    funext i
    rw [gibbsState]
    rw [show -β * (-(Real.log (Q i)) / β) = Real.log (Q i) from by
      field_simp]
    rw [Real.exp_log (hQ i), div_one]
  have h := freeEnergy_sub_eq_kl β 1 (fun i => -(Real.log (Q i)) / β) p hβ
    one_pos hp hps
  rw [hg, Real.log_one, mul_zero, add_zero] at h
  rw [← h]
  field_simp

/-- **The Landauer price of certified information**: a divergence of `D`
nats is `D / log 2` bits, and erasing them at temperature `T` costs exactly
`kB T D` - the Landauer identity converting the information certificate
into an energy scale. -/
@[zil_level physical_theorem]
theorem certified_information_landauer_energy (T D : ℝ) :
    landauerEnergyForBits T (D / Real.log 2) = Constants.kB * T * D := by
  unfold landauerEnergyForBits landauerCost
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  field_simp

/-- **Certified information in Bekenstein bit units**: the entropy content
`kB D` of the certificate, counted with the same bits-from-entropy
conversion the holographic layer applies to horizon area, is exactly the
Landauer bit count `D / log 2`. -/
@[zil_level physical_theorem]
theorem certified_entropy_bekenstein_bits (D : ℝ) :
    bitsFromEntropy (Constants.kB * D) = D / Real.log 2 := by
  unfold bitsFromEntropy
  have hk : Constants.kB ≠ 0 := ne_of_gt Constants.kB_pos
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  field_simp

/-- **Entropic-force work equals the Landauer energy**: the Verlinde force
transporting the certificate's entropy `kB D` across one screen
displacement `Δx` does exactly the Landauer erasure work `kB T D` - the
energy of the certified information read as force times displacement. -/
@[zil_level bridge_theorem]
theorem entropic_force_work_eq_landauer_energy (T D : ℝ) {Δx : ℝ}
    (hΔx : Δx ≠ 0) :
    verlindeEntropicForce T (Constants.kB * D) Δx * Δx
      = landauerEnergyForBits T (D / Real.log 2) := by
  unfold verlindeEntropicForce landauerEnergyForBits landauerCost
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  field_simp

/-- **The Bell-information-gravity chain**: a CHSH violation by four
no-signalling outcome tables propagates through exact arrows. Some
violating table carries strictly positive mutual information `D` between
the wings; erasing that certificate at temperature `T` costs the Landauer
energy `kB T D`; the certificate's entropy counts in the same bit units
the holographic layer applies to horizon area; the Verlinde entropic force
transporting it across one screen displacement does exactly the Landauer
work and is strictly positive; and the same force law at the Unruh
temperature of an accelerated screen with the displacement entropy is
Newton's second law `F = ma` - the inertia face of the thermodynamic route
to gravity. Correlation, information, thermodynamics, and gravitation
linked by exact identities, with the antecedent inhabited by the
eight-clock table (`bell_information_gravity_chain_hypotheses`). -/
@[zil_level bridge_theorem]
theorem bell_information_gravity_chain
    (q₁ q₂ q₃ q₄ : Bool × Bool → ℝ)
    (h₁ : ∀ z, 0 < q₁ z) (h₂ : ∀ z, 0 < q₂ z)
    (h₃ : ∀ z, 0 < q₃ z) (h₄ : ∀ z, 0 < q₄ z)
    (hs₁ : ∑ z, q₁ z = 1) (hs₂ : ∑ z, q₂ z = 1)
    (hs₃ : ∑ z, q₃ z = 1) (hs₄ : ∑ z, q₄ z = 1)
    (hA : ∀ s, (∑ t, q₁ (s, t)) = ∑ t, q₂ (s, t))
    (hA' : ∀ s, (∑ t, q₃ (s, t)) = ∑ t, q₄ (s, t))
    (hB : ∀ t, (∑ s, q₁ (s, t)) = ∑ s, q₃ (s, t))
    (hB' : ∀ t, (∑ s, q₂ (s, t)) = ∑ s, q₄ (s, t))
    (hviol : 2 < |pairCorrelator q₁ + pairCorrelator q₂
        + pairCorrelator q₃ - pairCorrelator q₄|)
    {T Δx ℏ m c a : ℝ} (hT : 0 < T) (hΔx : 0 < Δx) (hℏ : 0 < ℏ)
    (hm : 0 < m) (hc : 0 < c) :
    (∃ q : Bool × Bool → ℝ, (q = q₁ ∨ q = q₂ ∨ q = q₃ ∨ q = q₄)
      ∧ 0 < klDivergence q (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2)))
      ∧ landauerEnergyForBits T
          (klDivergence q (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2)))
            / Real.log 2)
        = Constants.kB * T *
            klDivergence q (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2)))
      ∧ bitsFromEntropy (Constants.kB *
            klDivergence q (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2))))
          = klDivergence q (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2)))
              / Real.log 2
      ∧ verlindeEntropicForce T
            (Constants.kB *
              klDivergence q
                (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2))))
            Δx * Δx
        = landauerEnergyForBits T
            (klDivergence q (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2)))
              / Real.log 2)
      ∧ 0 < verlindeEntropicForce T
            (Constants.kB *
              klDivergence q
                (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2))))
            Δx)
    ∧ verlindeEntropicForce (unruhTemperature ℏ Constants.kB c a)
          (verlindeDisplacementEntropy ℏ Constants.kB m c Δx) Δx
      = m * a := by
  have hd := chsh_violation_positive_mutual_information q₁ q₂ q₃ q₄
    h₁ h₂ h₃ h₄ hs₁ hs₂ hs₃ hs₄ hA hA' hB hB' hviol
  have hsel : ∃ q : Bool × Bool → ℝ, (q = q₁ ∨ q = q₂ ∨ q = q₃ ∨ q = q₄)
      ∧ 0 < klDivergence q
        (fun z => (∑ t, q (z.1, t)) * (∑ s, q (s, z.2))) := by
    rcases hd with h | h | h | h
    exacts [⟨q₁, Or.inl rfl, h⟩, ⟨q₂, Or.inr (Or.inl rfl), h⟩,
      ⟨q₃, Or.inr (Or.inr (Or.inl rfl)), h⟩,
      ⟨q₄, Or.inr (Or.inr (Or.inr rfl)), h⟩]
  obtain ⟨q, hqsel, hI⟩ := hsel
  exact ⟨⟨q, hqsel, hI, certified_information_landauer_energy T _,
    certified_entropy_bekenstein_bits _,
    entropic_force_work_eq_landauer_energy T _ (ne_of_gt hΔx),
    verlindeEntropicForce_pos hT (mul_pos Constants.kB_pos hI) hΔx⟩,
    newton_second_law_from_verlinde_unruh hℏ Constants.kB_pos hm hc hΔx⟩

/-- **The chain's full antecedent is inhabited**: the eight-clock table
supplies the violating no-signalling statistics and unit physical scales
supply the positive constants - the hypothesis closure demanded by
`#physlib_hypotheses_inhabited` for `bell_information_gravity_chain`. -/
@[zil_level physical_theorem]
theorem bell_information_gravity_chain_hypotheses :
    ∃ q₁ q₂ q₃ q₄ : Bool × Bool → ℝ,
      (∀ z, 0 < q₁ z) ∧ (∀ z, 0 < q₂ z) ∧ (∀ z, 0 < q₃ z) ∧ (∀ z, 0 < q₄ z)
      ∧ (∑ z, q₁ z = 1) ∧ (∑ z, q₂ z = 1) ∧ (∑ z, q₃ z = 1)
      ∧ (∑ z, q₄ z = 1)
      ∧ (∀ s, (∑ t, q₁ (s, t)) = ∑ t, q₂ (s, t))
      ∧ (∀ s, (∑ t, q₃ (s, t)) = ∑ t, q₄ (s, t))
      ∧ (∀ t, (∑ s, q₁ (s, t)) = ∑ s, q₃ (s, t))
      ∧ (∀ t, (∑ s, q₂ (s, t)) = ∑ s, q₄ (s, t))
      ∧ (2 < |pairCorrelator q₁ + pairCorrelator q₂
          + pairCorrelator q₃ - pairCorrelator q₄|)
      ∧ ∃ T Δx ℏ m c a : ℝ,
          0 < T ∧ 0 < Δx ∧ 0 < ℏ ∧ 0 < m ∧ 0 < c := by
  obtain ⟨q₁, q₂, q₃, q₄, h₁, h₂, h₃, h₄, hs₁, hs₂, hs₃, hs₄,
    hA, hA', hB, hB', hv⟩ := eight_clock_table_violates
  exact ⟨q₁, q₂, q₃, q₄, h₁, h₂, h₃, h₄, hs₁, hs₂, hs₃, hs₄,
    hA, hA', hB, hB', hv,
    1, 1, 1, 1, 1, 0, one_pos, one_pos, one_pos, one_pos, one_pos⟩

/-- **Clock, information, force, and correlation cohere**: the clock channel
preserves the Kullback-Leibler ledger, the free-energy force conjugate to
the tick is minus the mean clock energy over the tick, every
shared-randomness average of the CHSH combination stays within the classical
bound, and the quantum optimum is the eighth-root clock-character value
`2√2` - four exact faces of one reversible information structure, with the
Kullback-Leibler ledger tied to the same free energy by the Gibbs
variational identity. -/
@[zil_level bridge_theorem]
theorem entropic_clock_synthesis {ι : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] {b : ℝ} (hb : b ≠ 0)
    (ε : ι → ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (μ ν : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {κ : Type} [Fintype κ] (x : κ → CHSHAssignment) (w : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    (klDiv (μ ⊗ₘ computationKernel (cogwheelNatStep N))
        (ν ⊗ₘ computationKernel (cogwheelNatStep N)) = klDiv μ ν)
    ∧ HasDerivAt
        (fun l => (ofFiniteEnergy (fun i => ε i / l)).freeEnergyBetaReal b)
        (-(1 / lam) *
          (ofFiniteEnergy (fun i => ε i / lam)).meanEnergyBetaReal b) lam
    ∧ (|∑ i, w i * ((classicalCHSHValue (x i) : ℤ) : ℝ)| ≤ 2)
    ∧ (3 * (ZMod.stdAddChar (((1 : ℤ) : ZMod 8))).re
        - (ZMod.stdAddChar (((3 : ℤ) : ZMod 8))).re = 2 * Real.sqrt 2) :=
  ⟨cogwheel_channel_keeps_kl N μ ν, tick_force_virial hb ε hlam,
   sharedRandomness_chsh_bound x w hw hsum, tsirelson_on_eight_clock⟩

end Physlib.QuantumMechanics.EntropicClockSynthesis

end

open Physlib.QuantumMechanics.EntropicClockSynthesis in
#physlib_axiom_clean_all [
  cyclicShift_val,
  cogwheelNatStep_val,
  cogwheelNatStep_injective,
  cogwheel_channel_keeps_kl,
  tick_force_virial,
  sharedRandomness_chsh_bound,
  stdAddChar_re,
  tsirelson_on_eight_clock,
  compton_tick_primitive_root,
  clock_reading_advances,
  damped_clock_phase,
  damped_clock_norm_sq,
  cogwheel_partition_closed_form,
  factorized_strategy_chsh_bound,
  sum_bool_expand,
  abs_expectation_le_one,
  product_pairCorrelator,
  chsh_correlator_bracket_bound,
  table_factorizes_of_kl_nonpos,
  chsh_violation_positive_mutual_information,
  correlatedPairTable_pos,
  correlatedPairTable_sum,
  correlatedPairTable_marginalFst,
  correlatedPairTable_marginalSnd,
  correlatedPairTable_correlator,
  analyzerVector_orthonormal_self,
  analyzerVector_orthogonal,
  bellPairState_normalized,
  spinAnalyzer_eigen,
  bornAmplitude_eq_of_eq,
  bornAmplitude_eq_of_ne,
  bornOutcomeTable_eq,
  eight_clock_table_violates,
  certified_information_excess_free_energy,
  certified_information_landauer_energy,
  certified_entropy_bekenstein_bits,
  entropic_force_work_eq_landauer_energy,
  bell_information_gravity_chain,
  bell_information_gravity_chain_hypotheses,
  entropic_clock_synthesis ]

open Physlib.QuantumMechanics.EntropicClockSynthesis in
#physlib_non_vacuous_all [
  cyclicShift_val,
  cogwheelNatStep_val,
  cogwheelNatStep_injective,
  cogwheel_channel_keeps_kl,
  tick_force_virial,
  sharedRandomness_chsh_bound,
  stdAddChar_re,
  tsirelson_on_eight_clock,
  compton_tick_primitive_root,
  clock_reading_advances,
  damped_clock_phase,
  damped_clock_norm_sq,
  cogwheel_partition_closed_form,
  factorized_strategy_chsh_bound,
  abs_expectation_le_one,
  product_pairCorrelator,
  chsh_correlator_bracket_bound,
  table_factorizes_of_kl_nonpos,
  chsh_violation_positive_mutual_information,
  correlatedPairTable_pos,
  correlatedPairTable_sum,
  correlatedPairTable_marginalFst,
  correlatedPairTable_marginalSnd,
  correlatedPairTable_correlator,
  analyzerVector_orthonormal_self,
  analyzerVector_orthogonal,
  bellPairState_normalized,
  spinAnalyzer_eigen,
  bornAmplitude_eq_of_eq,
  bornAmplitude_eq_of_ne,
  bornOutcomeTable_eq,
  eight_clock_table_violates,
  certified_information_excess_free_energy,
  certified_information_landauer_energy,
  certified_entropy_bekenstein_bits,
  entropic_force_work_eq_landauer_energy,
  bell_information_gravity_chain,
  bell_information_gravity_chain_hypotheses,
  entropic_clock_synthesis ]

open Physlib.QuantumMechanics.EntropicClockSynthesis in
#physlib_hypotheses_inhabited chsh_violation_positive_mutual_information
  using eight_clock_table_violates

open Physlib.QuantumMechanics.EntropicClockSynthesis in
#physlib_hypotheses_inhabited bell_information_gravity_chain
  using bell_information_gravity_chain_hypotheses

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.cogwheelNatStep_val where
  formalizes @ "claim:the-natural-number-clock-driver-intertwines-the-residue-shift-through-the-value-map",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicShift"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.cogwheelNatStep_injective where
  formalizes @ "claim:the-clock-driver-is-injective-on-the-reversible-side-of-the-carneiro-split",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.ComputationLandauer.computationKernel"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.cogwheel_channel_keeps_kl where
  formalizes @ "claim:the-clock-channel-preserves-kl-divergence-one-clock-step-costs-no-information",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.ComputationLandauer.computation_keeps_kl",
  supported_by @ "paper:landauer-1961-irreversibility-and-heat-generation-in-the-computing-process"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.tick_force_virial where
  formalizes @ "claim:the-thermodynamic-force-conjugate-to-the-clock-tick-is-minus-the-mean-clock-energy-over-the-tick",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:CanonicalEnsemble.hasDerivAt_parametric_freeEnergy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.freeEnergy_sub_eq_kl",
  caveat @ "claim:the-kl-free-energy-tie-is-the-cited-gibbs-variational-identity-not-reproved-here"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.sharedRandomness_chsh_bound where
  formalizes @ "claim:every-shared-randomness-average-of-the-chsh-combination-stays-within-the-classical-bound",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds.classicalCHSH_bound",
  supported_by @ "paper:bell-1964-on-the-einstein-podolsky-rosen-paradox"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.tsirelson_on_eight_clock where
  formalizes @ "claim:the-chsh-optimal-analyzer-phases-are-eighth-root-clock-angles-summing-to-two-root-two",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:cirelson-1980-quantum-generalizations-of-bells-inequality",
  caveat @ "claim:the-identity-fixes-the-angle-geometry-attainment-is-realized-in-module-by-the-born-outcome-tables"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.compton_tick_primitive_root where
  formalizes @ "claim:the-compton-trinity-clock-strobes-to-the-cyclic-automaton",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MisraJacobsonSynthesis.misra_jacobson_entropic_synthesis"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.clock_reading_advances where
  formalizes @ "claim:the-discrete-age-observable-advances-one-unit-per-step-modulo-the-period",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:misra-prigogine-courbage-1979-lyapounov-variable-entropy-and-measurement-in-quantum-mechanics",
  caveat @ "claim:the-continuous-misra-operator-lives-on-the-line-paulis-obstruction-blocks-a-discrete-conjugate"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.damped_clock_phase where
  formalizes @ "claim:complexifying-the-clock-energy-damps-the-eigenphase-modulus-per-step",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.normSquaredDecayRate",
  caveat @ "claim:the-contour-reading-is-the-complex-action-program-only-the-modulus-identity-is-proved"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.cogwheel_partition_closed_form where
  formalizes @ "claim:the-clock-partition-function-closes-to-the-finite-geometric-form",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:CanonicalEnsemble.mathematicalPartitionFunctionBetaReal",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.WittenAnalyticPathIntegral.partitionFunction",
  caveat @ "claim:the-chern-simons-partition-function-is-the-cited-analytic-counterpart-no-identification-is-proved"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.factorized_strategy_chsh_bound where
  formalizes @ "claim:factorized-wing-statistics-keep-the-averaged-chsh-combination-within-the-classical-bound",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds.classicalCHSH_bound",
  supported_by @ "paper:bell-1964-on-the-einstein-podolsky-rosen-paradox"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.chsh_violation_positive_mutual_information where
  formalizes @ "claim:a-chsh-violation-certifies-strictly-positive-mutual-information-between-the-wings",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.mutualInformation_nonneg",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_eq_zero_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.EntropicClockSynthesis.eight_clock_table_violates",
  supported_by @ "paper:bell-1964-on-the-einstein-podolsky-rosen-paradox",
  caveat @ "claim:the-certificate-is-qualitative-no-pinsker-type-quantitative-lower-bound-is-proved",
  caveat @ "claim:no-signalling-marginal-consistency-is-assumed-not-derived"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.spinAnalyzer_eigen where
  formalizes @ "claim:the-measurement-outcomes-are-the-plus-minus-one-eigenvalues-of-the-spin-analyzer",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.EntropicClockSynthesis.analyzerVector_orthonormal_self"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.bornOutcomeTable_eq where
  formalizes @ "claim:the-born-rule-for-the-entangled-pair-at-analyzer-angles-yields-the-correlated-pair-table",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.EntropicClockSynthesis.bellPairState_normalized",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.pairAmplitude_singlet",
  supported_by @ "paper:born-1926-zur-quantenmechanik-der-stossvorgaenge",
  caveat @ "claim:amplitudes-are-real-the-measurement-plane-slice-of-the-qubit-pair-suffices-for-these-angles"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.eight_clock_table_violates where
  formalizes @ "claim:the-eight-clock-quantum-table-inhabits-the-chsh-violation-hypotheses",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.EntropicClockSynthesis.tsirelson_on_eight_clock",
  supported_by @ "lean:Physlib.QuantumMechanics.EntropicClockSynthesis.bornOutcomeTable_eq",
  supported_by @ "paper:cirelson-1980-quantum-generalizations-of-bells-inequality"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.certified_information_excess_free_energy where
  formalizes @ "claim:the-certified-divergence-equals-beta-times-the-excess-free-energy-at-the-factorized-reference",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.freeEnergy_sub_eq_kl"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.certified_information_landauer_energy where
  formalizes @ "claim:the-certified-divergence-carries-the-landauer-energy-price",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.Landauer.landauerEnergyForBits",
  supported_by @ "paper:landauer-1961-irreversibility-and-heat-generation-in-the-computing-process"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.certified_entropy_bekenstein_bits where
  formalizes @ "claim:the-certificates-entropy-counts-in-the-same-bit-units-as-horizon-area",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.bitsFromEntropy",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  caveat @ "claim:the-shared-unit-is-the-bits-from-entropy-conversion-no-holographic-bound-on-the-certificate-is-proved"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.entropic_force_work_eq_landauer_energy where
  formalizes @ "claim:the-entropic-force-work-across-one-screen-displacement-equals-the-landauer-energy-of-the-certificate",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.verlindeEntropicForce",
  supported_by @ "paper:verlinde-2010-emergent-gravity"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.bell_information_gravity_chain where
  formalizes @ "claim:bell-correlation-information-thermodynamics-and-gravitation-are-linked-by-exact-identities",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.EntropicClockSynthesis.eight_clock_table_violates",
  supported_by @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  supported_by @ "lean:Physlib.Thermodynamics.verlindeEntropicForce_pos",
  supported_by @ "paper:jacobson-1995-thermodynamics-of-spacetime",
  supported_by @ "paper:verlinde-2010-emergent-gravity",
  caveat @ "claim:the-gravitational-terminus-is-the-verlinde-unruh-inertia-identity-not-a-derivation-of-the-einstein-equations",
  caveat @ "claim:the-chain-transports-identities-and-positivity-no-back-reaction-of-information-on-geometry-is-derived"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.entropic_clock_synthesis where
  formalizes @ "claim:clock-information-force-and-correlation-cohere-through-one-reversible-information-structure",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.freeEnergy_sub_eq_kl",
  supported_by @ "lean:Physlib.Gravity.Canonical.KucharWDWSplit",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MisraJacobsonSynthesis.misra_jacobson_entropic_synthesis",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.coucheEntropicTime",
  supported_by @ "lean:Physlib.Thermodynamics.verlindeEntropicForce",
  caveat @ "claim:coherence-means-the-four-exact-faces-and-the-cited-variational-identity-no-unified-dynamical-law-is-derived",
  caveat @ "claim:the-levicivita-witten-verlinde-edges-are-program-instance-corroborations-not-derivations"

zil_file_contract physlib.entropicClockSynthesis where
  promises "The coherence layer of the entropic-clock program: the cyclic clock encoded as an injective natural-number driver preserves Kullback-Leibler divergence as a computation channel; the free-energy force conjugate to the clock tick is minus the mean clock energy over the tick, with the KL ledger tied to the same free energy by the Gibbs variational identity; every shared-randomness average of the CHSH combination stays within the classical bound; the quantum optimum is the eighth-root clock-character value two root two - four exact faces assembled in one statement; and the Bell-information-gravity chain at the correlator level: a CHSH violation by no-signalling outcome tables certifies strictly positive mutual information in some table, the certified divergence carries the Landauer energy in Bekenstein bit units and equals beta times an excess free energy over the factorized equilibrium, the Verlinde force work across one screen displacement equals that Landauer energy, and the same force law at the Unruh temperature is Newton's second law - with every conditional's antecedent exhibited by the eight-clock table, derived by the born rule from the maximally entangled pair state in analyzer bases at the clock angles, and enforced by the hypotheses-inhabited gate."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.ComputationLandauer.computation_keeps_kl",
    "lean:CanonicalEnsemble.hasDerivAt_parametric_freeEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds.classicalCHSH_bound",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.freeEnergy_sub_eq_kl",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.mutualInformation_nonneg",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_eq_zero_iff",
    "lean:Physlib.Thermodynamics.Landauer.landauerEnergyForBits",
    "lean:Physlib.Thermodynamics.bitsFromEntropy",
    "lean:Physlib.Thermodynamics.verlindeEntropicForce",
    "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
    "lean:ZMod.stdAddChar"]
  forbids_substitutes ["a unified dynamical law deriving the four faces from one action",
    "a quantitative information-correlation bound of Pinsker type",
    "a claim that gravity is derived rather than thermodynamically read",
    "a derivation of the einstein equations from the bell certificate",
    "postulating the witness outcome tables instead of deriving them by the born rule"]
  witnessed_by [
    Physlib.QuantumMechanics.EntropicClockSynthesis.cogwheelNatStep_val,
    Physlib.QuantumMechanics.EntropicClockSynthesis.cogwheelNatStep_injective,
    Physlib.QuantumMechanics.EntropicClockSynthesis.cogwheel_channel_keeps_kl,
    Physlib.QuantumMechanics.EntropicClockSynthesis.tick_force_virial,
    Physlib.QuantumMechanics.EntropicClockSynthesis.sharedRandomness_chsh_bound,
    Physlib.QuantumMechanics.EntropicClockSynthesis.tsirelson_on_eight_clock,
    Physlib.QuantumMechanics.EntropicClockSynthesis.compton_tick_primitive_root,
    Physlib.QuantumMechanics.EntropicClockSynthesis.clock_reading_advances,
    Physlib.QuantumMechanics.EntropicClockSynthesis.damped_clock_phase,
    Physlib.QuantumMechanics.EntropicClockSynthesis.damped_clock_norm_sq,
    Physlib.QuantumMechanics.EntropicClockSynthesis.cogwheel_partition_closed_form,
    Physlib.QuantumMechanics.EntropicClockSynthesis.factorized_strategy_chsh_bound,
    Physlib.QuantumMechanics.EntropicClockSynthesis.chsh_violation_positive_mutual_information,
    Physlib.QuantumMechanics.EntropicClockSynthesis.spinAnalyzer_eigen,
    Physlib.QuantumMechanics.EntropicClockSynthesis.bornOutcomeTable_eq,
    Physlib.QuantumMechanics.EntropicClockSynthesis.eight_clock_table_violates,
    Physlib.QuantumMechanics.EntropicClockSynthesis.certified_information_excess_free_energy,
    Physlib.QuantumMechanics.EntropicClockSynthesis.certified_information_landauer_energy,
    Physlib.QuantumMechanics.EntropicClockSynthesis.certified_entropy_bekenstein_bits,
    Physlib.QuantumMechanics.EntropicClockSynthesis.entropic_force_work_eq_landauer_energy,
    Physlib.QuantumMechanics.EntropicClockSynthesis.bell_information_gravity_chain,
    Physlib.QuantumMechanics.EntropicClockSynthesis.entropic_clock_synthesis ]

/- ZIL-END -/

#zil_formalization_lint physlib.entropicClockSynthesis

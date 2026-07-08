/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Physlib.StatisticalMechanics.BoltzmannConstant
public import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
public import Physlib.Thermodynamics.FreeEnergy
public import Physlib.Thermodynamics.SecondLaw
public import QuantumInfo.ClassicalInfo.Entropy

/-!
# Landauer's principle

Erasing one bit of information at thermodynamic temperature `T` dissipates at
least

  `landauerCost T  =  kB · T · log 2`

units of free energy (Landauer, 1961, *IBM J. Res. Dev.* 5(3): 183-191).

`kB` is the Boltzmann constant supplied by
`Physlib.StatisticalMechanics.BoltzmannConstant`; `log` is the natural
logarithm (`Real.log`).  The bound is a strict positivity claim whenever
`T > 0`: it sits inside the thermodynamic layer as a primitive
information-energetic inequality and does not depend on any quantum,
field-theoretic, or entropic-time structure.


## References

- **Landauer 1961** — *Irreversibility and Heat Generation in Computing*
- **Bennett 1982** — *The thermodynamics of computation — a review*
- **Weberszpil & Sotolongo-Costa 2026** — *Entropy as a Clock: Foundations and
  Parametrizations of Emergent Time*, Int. J. Theor. Phys. **65**:15.
  DOI: 10.1007/s10773-025-06212-1
-/

set_option autoImplicit false

@[expose] public section

open Constants

namespace Physlib.Thermodynamics.Landauer

/-- **Landauer cost.** The minimum free-energy cost of erasing one bit of
information at temperature `T`, in the SI value of `kB`. -/
noncomputable def landauerCost (T : ℝ) : ℝ := kB * T * Real.log 2

@[simp] theorem landauerCost_def (T : ℝ) :
    landauerCost T = kB * T * Real.log 2 := rfl

/-- **Landauer's principle (strict form).** For every positive temperature
`T`, the Landauer cost of erasing one bit is strictly positive. -/
theorem landauerCost_pos (T : ℝ) (hT : 0 < T) : 0 < landauerCost T := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkT : 0 < kB * T := mul_pos kB_pos hT
  simpa [landauerCost] using mul_pos hkT hlog

/-- **Landauer's principle (non-strict form).** The Landauer cost is
non-negative for non-negative temperature. -/
theorem landauerCost_nonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ landauerCost T := by
  have hlog : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have hkT : 0 ≤ kB * T := mul_nonneg kB_nonneg hT
  simpa [landauerCost] using mul_nonneg hkT hlog

/-! ## Complex action as bit counting

The imaginary part `S_I` of a complex action `S = S_R + i·S_I` includes the
information-theoretic content of a worldline.  Via the Brillouin /
Landauer dimensional identity `[S_I/ℏ] = I` (Brillouin 1962, Landauer
1961) the dimensionless quantity `S_I / ℏ` literally counts information
content **in nats** (natural-log units), and dividing by `ln 2` rescales
to **bits**:

  `nats(ℏ, S_I) := S_I / ℏ`
  `bits(ℏ, S_I) := S_I / (ℏ · ln 2)`

The Landauer per-bit energy `landauerCost T = kB · T · log 2` then
translates between bit count and minimum free-energy cost:

  `landauerEnergyForBits T N = N · landauerCost T = N · kB · T · log 2`,

and combining with the energy-dissipation identity `ΔE = ℏ · τ_ent · ⟨H_I⟩`
gives the thermal-rate relation at one-bit-per-`τ_ent = ln 2`,
`⟨H_I⟩ = kB · T / ℏ` (the standard thermal entropic rate).

This is purely an algebraic restatement of dimensional facts plus the
Landauer principle; no new axioms.
-/

/-- **Complex-action information in nats**: `S_I / ℏ` counts information
content in natural units (nats), via the Brillouin/Landauer dimensional
identity `[S_I/ℏ] = I`. -/
noncomputable def complexActionNats (ℏ S_I : ℝ) : ℝ := S_I / ℏ

/-- **Complex-action information in bits**: `S_I / (ℏ · ln 2)` rescales
nats to bits. -/
noncomputable def complexActionBits (ℏ S_I : ℝ) : ℝ :=
  S_I / (ℏ * Real.log 2)

/-- `nats ≥ 0` whenever `ℏ > 0` and `S_I ≥ 0`. -/
theorem complexActionNats_nonneg
    {ℏ S_I : ℝ} (hℏ : 0 < ℏ) (hSI : 0 ≤ S_I) :
    0 ≤ complexActionNats ℏ S_I := by
  unfold complexActionNats
  exact div_nonneg hSI hℏ.le

/-- `bits ≥ 0` whenever `ℏ > 0` and `S_I ≥ 0`. -/
theorem complexActionBits_nonneg
    {ℏ S_I : ℝ} (hℏ : 0 < ℏ) (hSI : 0 ≤ S_I) :
    0 ≤ complexActionBits ℏ S_I := by
  unfold complexActionBits
  apply div_nonneg hSI
  apply mul_nonneg hℏ.le
  exact (Real.log_pos (by norm_num)).le

/-- **Bit-counting via the log-2 rescaling**:
`bits = nats / log 2`. -/
theorem complexActionBits_eq_nats_div_log2
    (ℏ S_I : ℝ) :
    complexActionBits ℏ S_I = complexActionNats ℏ S_I / Real.log 2 := by
  unfold complexActionBits complexActionNats
  rw [div_div]

/-- **One bit of S_I**: when `S_I = ℏ · ln 2`, the bit count is `1`. -/
theorem complexActionBits_one_bit (ℏ : ℝ) (hℏ : 0 < ℏ) :
    complexActionBits ℏ (ℏ * Real.log 2) = 1 := by
  unfold complexActionBits
  have hℏ' : ℏ ≠ 0 := ne_of_gt hℏ
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- **`N` bits of S_I**: when `S_I = N · ℏ · ln 2`, the bit count is `N`. -/
theorem complexActionBits_N_bits (ℏ N : ℝ) (hℏ : 0 < ℏ) :
    complexActionBits ℏ (N * ℏ * Real.log 2) = N := by
  unfold complexActionBits
  have hℏ' : ℏ ≠ 0 := ne_of_gt hℏ
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- **Landauer energy for `N` bits**: `N · landauerCost T = N · kB · T · log 2`. -/
noncomputable def landauerEnergyForBits (T N : ℝ) : ℝ := N * landauerCost T

/-- **Landauer per-bit identity**: erasing `N` bits at temperature `T` costs
`N · kB · T · log 2`. -/
@[simp]
theorem landauerEnergyForBits_def (T N : ℝ) :
    landauerEnergyForBits T N = N * (kB * T * Real.log 2) := rfl

/-- **Landauer cost for the bit content of S_I**: erasing the bits encoded
in an imaginary action `S_I` costs `bits(ℏ, S_I) · kB · T · log 2`. -/
theorem landauerEnergyForBits_from_S_I (ℏ T S_I : ℝ) :
    landauerEnergyForBits T (complexActionBits ℏ S_I)
      = complexActionBits ℏ S_I * (kB * T * Real.log 2) := rfl

/-- **Bit-counting / Landauer bridge** (the headline identity).

For `S_I = ℏ · ln 2` (exactly one bit of imaginary action), the Landauer
energy cost equals the textbook per-bit Landauer cost `kB · T · log 2`. -/
theorem landauerEnergy_one_bit_of_S_I (ℏ T : ℝ) (hℏ : 0 < ℏ) :
    landauerEnergyForBits T (complexActionBits ℏ (ℏ * Real.log 2))
      = kB * T * Real.log 2 := by
  rw [complexActionBits_one_bit ℏ hℏ, landauerEnergyForBits_def, one_mul]

/-- **Bit-counting / Landauer bridge — N-bit form**.

For `S_I = N · ℏ · ln 2` (exactly `N` bits of imaginary action), the
Landauer energy cost equals `N · kB · T · log 2`. -/
theorem landauerEnergy_N_bits_of_S_I (ℏ T N : ℝ) (hℏ : 0 < ℏ) :
    landauerEnergyForBits T (complexActionBits ℏ (N * ℏ * Real.log 2))
      = N * (kB * T * Real.log 2) := by
  rw [complexActionBits_N_bits ℏ N hℏ, landauerEnergyForBits_def]

/-! ## Full mathematical derivation of Landauer's principle

The textbook Landauer derivation has four steps:

1. **Information model**.  A "bit memory" is a degree of freedom with
   two equiprobable states.  As a `ProbDistribution`, it is exactly
   `ProbDistribution.uniform (α := Fin 2)`, with Shannon entropy
   `Hₛ_uniform := log 2`.

2. **Erasure as constant map**.  Erasing the bit maps both states to a
   fixed value `b : Fin 2`.  The post-erasure distribution is
   `ProbDistribution.constant b`, with Shannon entropy `Hₛ = 0`.

3. **Information change**.  The Shannon-entropy decrease is
   `ΔH = Hₛ_pre − Hₛ_post = log 2`.

4. **Second law / Boltzmann's principle**.  Converting Shannon entropy
   to thermodynamic entropy via Boltzmann's identification
   `S_thermo := kB · H_Shannon` and applying the Clausius bound to the
   heat reservoir (any decrease in memory entropy must be matched by an
   increase elsewhere, ultimately as heat at temperature `T`), we get

     `Q_dissipated ≥ T · ΔS_thermo = T · kB · ΔH = kB · T · log 2`.

This module formalises **steps 1–3 fully** (Shannon-entropy calculation
for the bit memory and its erased counterpart, theorem-grade with no
axioms beyond Mathlib + QuantumInfo's `Hₛ`).  Step 4's Clausius
inequality is the standard second-law statement; we expose it here as
an **input** (`hClausius` hypothesis), letting consumers thread their
own second-law witness.

-/

/-- **Step 1.** Shannon entropy of the uniform two-state distribution
(the "maximally-uncertain bit memory") equals `log 2`.

  `Hₛ(uniform on Fin 2) = log 2`.

This is the per-bit information content prior to erasure. -/
theorem bitMemoryEntropy_uniform :
    Hₛ (ProbDistribution.uniform (α := Fin 2)) = Real.log 2 := by
  rw [Hₛ_uniform]
  simp

/-- **Step 2.** Shannon entropy of any constant (post-erasure) distribution
on the bit memory equals `0`.

  `Hₛ(constant b) = 0`. -/
theorem bitMemoryEntropy_constant (b : Fin 2) :
    Hₛ (ProbDistribution.constant b) = 0 :=
  Hₛ_constant_eq_zero

/-- **Step 3.** The Shannon-entropy change during one-bit erasure
(uniform → constant) equals `log 2`.

  `Hₛ_pre − Hₛ_post = log 2`. -/
theorem bitErasure_shannon_entropy_change (b : Fin 2) :
    Hₛ (ProbDistribution.uniform (α := Fin 2))
      - Hₛ (ProbDistribution.constant b)
      = Real.log 2 := by
  rw [bitMemoryEntropy_uniform, bitMemoryEntropy_constant b]; ring

/-- **Step 3' (multiplied by `kB`).** The thermodynamic-entropy change
of the memory during one-bit erasure equals `kB · log 2`.

  `ΔS_thermo = kB · ΔH_Shannon = kB · log 2`. -/
theorem bitErasure_thermo_entropy_change (b : Fin 2) :
    kB *
        (Hₛ (ProbDistribution.uniform (α := Fin 2))
          - Hₛ (ProbDistribution.constant b))
      = kB * Real.log 2 := by
  rw [bitErasure_shannon_entropy_change b]

/-! ### The Landauer floor as a counting result: `log 2` from `|state| = 2`

The per-bit floor `log 2` in `landauerCost` is not an independent
postulate — it is `Real.log (Fintype.card α)` evaluated at a two-state
memory.  By `Hₛ_uniform`, the Shannon entropy of the maximally-uncertain
state of a finite configuration space `α` is `Real.log (Fintype.card α)`;
erasing it to a single fixed configuration (`ProbDistribution.constant`)
drops the entropy by exactly that amount.  For a one-bit memory the
configuration space has `Fintype.card = 2`, so the drop is `log 2` —
the floor is the logarithm of the number of erased microstates, a
counting statement, not assumed data.

These lemmas make the `card → floor` dependence explicit and are used
below to prove the `one_bit_erasure` field of `LandauerErasureSetup`
from the cardinality alone (see `TwoStateErasureSetup`). -/

/-- **Counting form of the erasure entropy drop.** For a memory whose
configuration space `α` is finite and nonempty, erasing it
(uniform → constant) lowers the Shannon entropy by exactly
`Real.log (Fintype.card α)`. -/
theorem uniformErasure_entropy_drop_eq_log_card
    {α : Type*} [Fintype α] [Nonempty α] (b : α) :
    Hₛ (ProbDistribution.uniform (α := α))
        - Hₛ (ProbDistribution.constant b)
      = Real.log (Fintype.card α) := by
  rw [Hₛ_constant_eq_zero, sub_zero, Hₛ_uniform, Finset.card_univ]

/-- **The one-bit floor is `log 2` because `|state| = 2`.** Specialising
the counting form to a two-state memory: the erasure entropy drop is
`Real.log 2`, derived from `Fintype.card α = 2` rather than assumed. -/
theorem twoStateErasure_entropy_drop_eq_log_two
    {α : Type*} [Fintype α] [Nonempty α] (hcard : Fintype.card α = 2) (b : α) :
    Hₛ (ProbDistribution.uniform (α := α))
        - Hₛ (ProbDistribution.constant b)
      = Real.log 2 := by
  rw [uniformErasure_entropy_drop_eq_log_card b, hcard]
  norm_num

/-- **Thermodynamic memory-entropy change of a two-state erasure.**
`ΔS_memory = kB · (Hₛ_post − Hₛ_pre) = −kB · log 2`, derived from
`Fintype.card α = 2`.  This is the field that `LandauerErasureSetup`
previously *assumed* as `one_bit_erasure`. -/
theorem twoStateErasure_memory_entropy_change
    {α : Type*} [Fintype α] [Nonempty α] (hcard : Fintype.card α = 2) (b : α) :
    kB * (Hₛ (ProbDistribution.constant b)
          - Hₛ (ProbDistribution.uniform (α := α)))
      = -kB * Real.log 2 := by
  have h : Hₛ (ProbDistribution.constant b)
            - Hₛ (ProbDistribution.uniform (α := α)) = -Real.log 2 := by
    rw [← neg_sub, twoStateErasure_entropy_drop_eq_log_two hcard b]
  rw [h]; ring

/-- **Step 4 (Landauer's principle, full derivation).**

Given:
* `Q_dissipated ≥ T · kB · ΔH_Shannon` — the Clausius bound on heat
  dissipated to the reservoir (input from the second law),
* the one-bit-erasure Shannon-entropy change `ΔH = log 2`,

we conclude:

  `Q_dissipated ≥ kB · T · log 2  =  landauerCost T`,

i.e. erasing one bit dissipates at least the textbook Landauer energy.

Steps 1–3 are proved here from `Hₛ_uniform` and `Hₛ_constant_eq_zero`
in `QuantumInfo.ClassicalInfo.Entropy`; step 4 is the Clausius
inequality, supplied as a hypothesis `hClausius`. -/
theorem landauerPrinciple_full
    (T Q_dissipated : ℝ) (b : Fin 2)
    (hClausius :
      kB * T *
          (Hₛ (ProbDistribution.uniform (α := Fin 2))
            - Hₛ (ProbDistribution.constant b))
        ≤ Q_dissipated) :
    landauerCost T ≤ Q_dissipated := by
  have hΔ : Hₛ (ProbDistribution.uniform (α := Fin 2))
              - Hₛ (ProbDistribution.constant b) = Real.log 2 :=
    bitErasure_shannon_entropy_change b
  rw [hΔ] at hClausius
  -- Goal: kB · T · log 2 ≤ Q_dissipated; hClausius: kB · T · log 2 ≤ Q_dissipated
  -- (after rewriting)
  show landauerCost T ≤ Q_dissipated
  unfold landauerCost
  linarith

/-- **Equality form**: if the Clausius bound is saturated (reversible
erasure, the equality case of the second law), the heat dissipated
equals exactly `landauerCost T`. -/
theorem landauerPrinciple_saturated
    (T : ℝ) (b : Fin 2)
    (Q_dissipated : ℝ)
    (hReversible :
      Q_dissipated
        = kB * T *
            (Hₛ (ProbDistribution.uniform (α := Fin 2))
              - Hₛ (ProbDistribution.constant b))) :
    Q_dissipated = landauerCost T := by
  rw [hReversible, bitErasure_shannon_entropy_change b]
  unfold landauerCost; ring

/-- **`N`-bit Landauer's principle.** Erasing `N` bits dissipates at
least `N · kB · T · log 2`.  Follows by linearity from the one-bit
case: the Shannon-entropy decrease is `N · log 2`, and Clausius gives
`Q ≥ T · kB · (N · log 2) = N · landauerCost T`. -/
theorem landauerPrinciple_N_bits
    (T Q_dissipated : ℝ) (N : ℝ)
    (hClausius : kB * T * (N * Real.log 2) ≤ Q_dissipated) :
    N * landauerCost T ≤ Q_dissipated := by
  unfold landauerCost
  -- Goal: N · (kB · T · log 2) ≤ Q_dissipated; from hClausius : kB · T · (N · log 2) ≤ Q
  have h : N * (kB * T * Real.log 2) = kB * T * (N * Real.log 2) := by ring
  rw [h]; exact hClausius

/-! ## Szilard's quantum engine: generalized Landauer principle

Following Ashrafi, Ray, Anza, and Crutchfield, **Szilard's Engine as a
Quantum Thermodynamical System**, arXiv:2010.14652 (2022), a single-particle
quantum Szilard engine running a cycle (insertion → measurement → control
→ erasure) obeys a **generalized Landauer principle**:

  `⟨Q_erase⟩ + ⟨Q_measure⟩  =  kB · T · H_bin(δ)`,

where

  `H_bin(δ) := -δ · ln δ - (1 - δ) · ln (1 - δ)`

is the binary entropy function (`Real.binEntropy`) of the partition
parameter `δ ∈ [0,1]` controlling where in the box the dividing barrier
is inserted.  Two key properties make this a genuine **extension** of
the standard Landauer cost rather than a replacement:

1. **Specialisation at `δ = 1/2`.**  `H_bin(1/2) = ln 2`, so for a
   symmetric partition the generalized cost reduces exactly to the
   standard Landauer cost
     `kB · T · log 2  =  landauerCost T`.
   This is the textbook one-bit-erasure cost recovered as the
   `δ = 1/2` special case of the Szilard trade-off.

2. **Upper bound.**  `H_bin(δ) ≤ ln 2` for all `δ ∈ [0,1]` (with
   equality iff `δ = 1/2`), so the Szilard cost is always **at most**
   the standard Landauer cost.  Concretely, asymmetric partitions
   (`δ ≠ 1/2`) reduce the joint thermodynamic price of measurement and
   erasure: information stored about a *biased* partition is cheaper
   to erase than information about an unbiased one.

3. **Reflection symmetry.**  `H_bin(δ) = H_bin(1 - δ)`: the cost is
   invariant under swapping the two compartments.

4. **Zeros.**  `H_bin(0) = H_bin(1) = 0`: a trivial partition (the
   barrier at one of the walls) has no thermodynamic cost.

The Clausius inequality `kB · T · H_bin(δ) ≤ Q_erase + Q_measure` is
threaded as a **hypothesis** (`hClausius`), matching the same pattern as
`landauerPrinciple_full` above; consumers supply their own second-law
witness.

This section is purely **algebraic**: it uses Mathlib's
`Real.binEntropy` lemmas (`binEntropy_two_inv`, `binEntropy_one_sub`,
`binEntropy_le_log_two`, `binEntropy_nonneg`, `binEntropy_eq_zero`).

References:
- **Ashrafi–Ray–Anza–Crutchfield 2022** — *Szilard's Engine as a
  Quantum Thermodynamical System* (arXiv:2010.14652)
- **Sagawa–Ueda 2009** — *Minimal Energy Cost for Thermodynamic
  Information Processing* (the classical δ-dependent trade-off)
- **Landauer 1961** (one-bit specialisation at `δ = 1/2`)
-/

/-- **Szilard / generalized Landauer cost** at partition parameter
`δ ∈ [0,1]`.

  `szilardLandauerCost T δ := kB · T · H_bin(δ)`

where `H_bin = Real.binEntropy` is the binary entropy function.
At `δ = 1/2` this recovers the textbook `landauerCost T = kB · T · log 2`
(see `szilardLandauerCost_at_half`). -/
noncomputable def szilardLandauerCost (T delta : ℝ) : ℝ :=
  kB * T * Real.binEntropy delta

@[simp] theorem szilardLandauerCost_def (T delta : ℝ) :
    szilardLandauerCost T delta = kB * T * Real.binEntropy delta := rfl

/-- **Reduction to standard Landauer at `δ = 1/2`.**  For the symmetric
partition, the Szilard cost equals the textbook per-bit Landauer cost. -/
theorem szilardLandauerCost_at_half (T : ℝ) :
    szilardLandauerCost T (1/2) = landauerCost T := by
  unfold szilardLandauerCost landauerCost
  have : Real.binEntropy (1/2) = Real.log 2 := by
    have h : (1/2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [h, Real.binEntropy_two_inv]
  rw [this]

/-- **Reflection symmetry.**  The Szilard cost is invariant under
swapping the two compartments (`δ ↔ 1 - δ`). -/
theorem szilardLandauerCost_symm (T delta : ℝ) :
    szilardLandauerCost T (1 - delta) = szilardLandauerCost T delta := by
  unfold szilardLandauerCost
  rw [Real.binEntropy_one_sub]

/-- **Non-negativity** on the physical range `δ ∈ [0,1]`, for
non-negative temperature. -/
theorem szilardLandauerCost_nonneg
    (T delta : ℝ) (hT : 0 ≤ T) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    0 ≤ szilardLandauerCost T delta := by
  unfold szilardLandauerCost
  exact mul_nonneg (mul_nonneg kB_nonneg hT) (Real.binEntropy_nonneg hdelta0 hdelta1)

/-- **Upper bound by the standard Landauer cost.**  For any
`δ ∈ ℝ` and `T ≥ 0`, the Szilard cost is at most the standard
Landauer cost.  Saturated iff `δ = 1/2`. -/
theorem szilardLandauerCost_le_landauer
    (T delta : ℝ) (hT : 0 ≤ T) :
    szilardLandauerCost T delta ≤ landauerCost T := by
  unfold szilardLandauerCost landauerCost
  have hkT : 0 ≤ kB * T := mul_nonneg kB_nonneg hT
  exact mul_le_mul_of_nonneg_left Real.binEntropy_le_log_two hkT

/-- **Vanishing endpoints.**  A trivial partition at either wall
has no thermodynamic cost. -/
@[simp] theorem szilardLandauerCost_zero (T : ℝ) :
    szilardLandauerCost T 0 = 0 := by
  unfold szilardLandauerCost
  rw [Real.binEntropy_zero, mul_zero]

@[simp] theorem szilardLandauerCost_one (T : ℝ) :
    szilardLandauerCost T 1 = 0 := by
  unfold szilardLandauerCost
  rw [Real.binEntropy_one, mul_zero]

/-- **Zero-cost classification.**  For positive temperature, the
Szilard cost vanishes iff the partition is trivial (`δ = 0` or
`δ = 1`). -/
theorem szilardLandauerCost_eq_zero_iff
    (T delta : ℝ) (hT : 0 < T) :
    szilardLandauerCost T delta = 0 ↔ delta = 0 ∨ delta = 1 := by
  unfold szilardLandauerCost
  have hkT_ne : kB * T ≠ 0 := ne_of_gt (mul_pos kB_pos hT)
  rw [mul_eq_zero, or_iff_right hkT_ne, Real.binEntropy_eq_zero]

/-- **Generalized Landauer principle (Ashrafi et al. 2022).**

Given:
* `T > 0` — bath temperature,
* `δ : ℝ` — partition parameter (the location at which the dividing
  barrier is inserted),
* `Q_erase, Q_measure : ℝ` — heat dissipated to the reservoir during the
  erasure and measurement stages of the quantum Szilard cycle,
* `hClausius : kB · T · H_bin(δ) ≤ Q_erase + Q_measure` — the Clausius
  bound on the joint thermodynamic price of measurement + erasure
  (input from the second law, exactly the form derived in the
  appendix of Ashrafi et al.),

we conclude:

  `szilardLandauerCost T δ ≤ Q_erase + Q_measure`,

the generalised one-cycle Landauer bound.  At `δ = 1/2` this reduces
to `landauerCost T ≤ Q_erase + Q_measure`; see
`szilardGeneralizedLandauer_at_half` for that corollary. -/
theorem szilardGeneralizedLandauer
    (T delta Q_erase Q_measure : ℝ)
    (hClausius :
      kB * T * Real.binEntropy delta ≤ Q_erase + Q_measure) :
    szilardLandauerCost T delta ≤ Q_erase + Q_measure := by
  unfold szilardLandauerCost
  exact hClausius

/-- **Specialisation at `δ = 1/2` (symmetric partition).**  The Szilard
trade-off reduces to the textbook one-bit Landauer bound. -/
theorem szilardGeneralizedLandauer_at_half
    (T Q_erase Q_measure : ℝ)
    (hClausius :
      kB * T * Real.log 2 ≤ Q_erase + Q_measure) :
    landauerCost T ≤ Q_erase + Q_measure := by
  have h := szilardGeneralizedLandauer T (1/2) Q_erase Q_measure
    (by
      have hbe : Real.binEntropy (1/2) = Real.log 2 := by
        have h2 : (1/2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
        rw [h2, Real.binEntropy_two_inv]
      rw [hbe]; exact hClausius)
  rw [szilardLandauerCost_at_half] at h; exact h

/-- **Reflection-symmetry consequence.**  Reversing the partition's
orientation does not change the generalised Landauer cost: any bound
that holds for `δ` also holds for `1 - δ`. -/
theorem szilardGeneralizedLandauer_one_sub
    (T delta Q_erase Q_measure : ℝ)
    (hClausius :
      kB * T * Real.binEntropy delta ≤ Q_erase + Q_measure) :
    szilardLandauerCost T (1 - delta) ≤ Q_erase + Q_measure := by
  rw [szilardLandauerCost_symm]
  exact szilardGeneralizedLandauer T delta Q_erase Q_measure hClausius

/-- **Trivial-partition consequence.**  Inserting the barrier at one
of the walls (`δ = 0` or `δ = 1`) imposes no Clausius lower bound on
measurement + erasure: the generalised Landauer cost vanishes. -/
theorem szilardGeneralizedLandauer_trivial_partition
    (T : ℝ) (delta : ℝ) (hdelta : delta = 0 ∨ delta = 1) :
    szilardLandauerCost T delta = 0 := by
  rcases hdelta with h | h
  · rw [h, szilardLandauerCost_zero]
  · rw [h, szilardLandauerCost_one]

/-- **Saturation form.**  When the Clausius bound is saturated
(reversible quantum Szilard cycle), the joint heat dissipated equals
exactly `kB · T · H_bin(δ)`. -/
theorem szilardLandauer_saturated
    (T delta Q_erase Q_measure : ℝ)
    (hReversible :
      Q_erase + Q_measure = kB * T * Real.binEntropy delta) :
    Q_erase + Q_measure = szilardLandauerCost T delta := by
  rw [hReversible]; rfl

/-! ## Szilard–Everett–complex-action/entropic-time surprisal identity (general outcome distribution)

The δ-parametric Szilard bound above covers the binary partition; for an
**arbitrary discrete outcome distribution** `p : ProbDistribution α`, the
markdown's §0K.3A *Szilard–Everett–complex-action/entropic-time Measurement Principle* states

* **Per-branch surprisal as imaginary action** —
  `S_I^(i) = -ℏ · log (p i)`,
* **Average-over-branches saturation identity** —
  `⟨S_I⟩ = Σ_i p_i · (-ℏ · log (p i)) = ℏ · Hₛ p`,
* **Generalised Szilard bound** —
  `⟨ΔS_th⟩ ≥ kB · Hₛ p`.

We add only theorems with mathematical content; no naked definitions and
no trivial-unfold "bridge" theorems.  The headline identity below uses
`Hₛ = Σ negMulLog` (`QuantumInfo.ClassicalInfo.Entropy.Hₛ`) and
`Finset.mul_sum`.

References:
- §0K.3A *Szilard–Everett–complex-action/entropic-time Measurement Principle*
  (complex-action/entropic-time theory MD, lines 7801–7988).
-/

/-- **Headline saturation identity** (Born-average ⇔ Shannon).

For every finitely-supported discrete distribution `p : ProbDistribution α`,
the Born-weighted average of per-branch imaginary action
`S_I^(i) = -ℏ · log (p i)` equals `ℏ · Hₛ p`:

  `Σ i, p_i · (-ℏ · log p_i)  =  ℏ · Hₛ p`.

This is the Szilard–Everett saturation: averaged over Born weights the
imaginary-action cost of measurement equals ℏ × Shannon entropy of the
outcome distribution.  Pure algebra atop `Real.negMulLog` and
`Finset.mul_sum`. -/
theorem bornAvgImagAction_eq_Hbar_Hₛ
    {α : Type*} [Fintype α] (ℏ : ℝ) (p : ProbDistribution α) :
    ∑ i, (p.prob i : ℝ) * (-ℏ * Real.log (p.prob i)) = ℏ * Hₛ p := by
  unfold Hₛ H₁
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  unfold Real.negMulLog
  ring

/-- **n-state Shannon erasure identity.**  For a uniform distribution
on `Fin n` (with `n ≥ 1`) erased to a constant value, the Shannon-entropy
change equals `log n`.  Generalises `bitErasure_shannon_entropy_change`
(the `n = 2` case) to arbitrary alphabet size.

  `Hₛ(uniform on Fin n) − Hₛ(constant) = log n`. -/
theorem nStateErasure_shannon_entropy_change
    (n : ℕ) [NeZero n] (i : Fin n) :
    Hₛ (ProbDistribution.uniform (α := Fin n))
      - Hₛ (ProbDistribution.constant i)
      = Real.log n := by
  have h_uniform : Hₛ (ProbDistribution.uniform (α := Fin n))
      = Real.log (Finset.univ.card (α := Fin n)) := Hₛ_uniform
  have h_const : Hₛ (ProbDistribution.constant i) = 0 := Hₛ_constant_eq_zero
  rw [h_uniform, h_const, sub_zero]
  simp

/-- **Szilard–Shannon upper bound.**  For any outcome distribution `p`
on a finite alphabet `α` and any non-negative temperature `T`, the
thermodynamic price `kB · T · Hₛ p` is at most `kB · T · log (card α)`,
saturated by the uniform distribution (`Hₛ_uniform`).

Direct consequence of `Hₛ_le_log_d` scaled by `kB · T`. -/
theorem szilardShannon_le_kBT_log_card
    {α : Type*} [Fintype α] [Nonempty α]
    (T : ℝ) (hT : 0 ≤ T) (p : ProbDistribution α) :
    kB * T * Hₛ p ≤ kB * T * Real.log (Fintype.card α) := by
  have hkT : 0 ≤ kB * T := mul_nonneg kB_nonneg hT
  exact mul_le_mul_of_nonneg_left (Hₛ_le_log_d p) hkT

/-- **Clausius bound on Shannon erasure → direct Hₛ-bound.**

If the Clausius inequality holds with the pre-erasure distribution `p`
and a constant post-erasure distribution `ProbDistribution.constant i`,

  `kB · T · (Hₛ p − Hₛ (constant i))  ≤  Q_dissipated`,

then because `Hₛ (constant i) = 0`:

  `kB · T · Hₛ p  ≤  Q_dissipated`.

Substantive use of `Hₛ_constant_eq_zero`.  Generalises the
`landauerPrinciple_full` shape from `α = Fin 2` to arbitrary
finite alphabets. -/
theorem shannonErasure_clausius_to_Hₛ_bound
    {α : Type*} [Fintype α]
    (T Q_dissipated : ℝ) (p : ProbDistribution α) (i : α)
    (hClausius :
      kB * T *
        (Hₛ p - Hₛ (ProbDistribution.constant i))
        ≤ Q_dissipated) :
    kB * T * Hₛ p ≤ Q_dissipated := by
  have h_const : Hₛ (ProbDistribution.constant i) = 0 := Hₛ_constant_eq_zero
  rw [h_const, sub_zero] at hClausius
  exact hClausius

/-- **Bridge to `landauerCost`.**  For the uniform distribution on
`Fin 2`, the Szilard–Shannon cost `kB · T · Hₛ` equals the textbook
`landauerCost T = kB · T · log 2`.  Combines `Hₛ_uniform` and the
identity `log (card (Fin 2)) = log 2`. -/
theorem szilardShannon_uniform_Fin2_eq_landauerCost (T : ℝ) :
    kB * T * Hₛ (ProbDistribution.uniform (α := Fin 2))
      = landauerCost T := by
  rw [bitMemoryEntropy_uniform]; rfl

/-! ## Connection to entropic time

Three substantive identities from Garcia-Gonzalez, *Complex Action and
Entropic Time: Foundations*, APS PRL submission v3 (2026):

1. **Bit Counting Theorem** (paper §"Information-Theoretic Interpretation
   via Landauer's Principle", line 2259):
     `τ_ent  =  (ln 2) · N_bits`,
   i.e. `complexActionNats ℏ S_I = log 2 · complexActionBits ℏ S_I`.
   Pins down the unit-conversion factor between nats (`complexActionNats`)
   and bits (`complexActionBits`).

2. **Landauer entropic-time advance** (paper lines 2274–2280):
     `(landauerCost T) / T / kB = log 2`,
   the three-step chain `Q_min = kB·T·log 2`, `ΔS_ent = Q_min/T`,
   `Δτ_ent = ΔS_ent/kB`.

3. **Connes-Rovelli bridge** (paper Eq. (38)–(39), line 682):
     `H_th = -ln ρ = S_I/ℏ = τ_ent`,
   for `ρ = exp(-S_I/ℏ)`; here the algebraic core
     `-log (exp (-(S_I/ℏ))) = complexActionNats ℏ S_I`
   uses `Real.log_exp` and identifies modular flow with entropic time.

All three are theorem-grade on the std-3 envelope.
-/

/-- **Bit Counting**.

The natural-log "entropic time" `τ_ent = S_I/ℏ` and the bit-count
`N_bits = S_I/(ℏ · log 2)` differ by exactly the conversion factor
`log 2`:

  `complexActionNats ℏ S_I  =  log 2 · complexActionBits ℏ S_I`.

Equivalent paper statement: `Δτ_ent = (ln 2) · ΔN_bits`. -/
theorem complexActionNats_eq_log2_mul_bits (ℏ S_I : ℝ) :
    complexActionNats ℏ S_I = Real.log 2 * complexActionBits ℏ S_I := by
  unfold complexActionNats complexActionBits
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- **Landauer entropic-time advance**.

Dividing the Landauer cost by the temperature and `kB` recovers exactly
`log 2`, the dimensionless entropic-time advance per erased bit:

  `(landauerCost T) / T / kB  =  log 2`. -/
theorem landauerCost_div_T_div_kB_eq_log2
    (T : ℝ) (hT : 0 < T) :
    (landauerCost T) / T / kB = Real.log 2 := by
  unfold landauerCost
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have hkB_ne : kB ≠ 0 := ne_of_gt kB_pos
  field_simp

/-- **Connes-Rovelli thermal-entropic bridge**.

For a density operator `ρ = exp(-S_I/ℏ)` (Boltzmann-Wick form), the
Connes-Rovelli modular Hamiltonian `H_th = -log ρ` equals the
imaginary-action-per-ℏ:

  `-log (exp (-(S_I/ℏ)))  =  complexActionNats ℏ S_I`.

This is the algebraic core of the boxed identity
`H_th = -ln ρ = S_I/ℏ = τ_ent`, identifying modular flow with
entropic time. Uses `Real.log_exp`. -/
theorem connesRovelli_bridge_modular_eq_complexActionNats
    (ℏ S_I : ℝ) :
    -Real.log (Real.exp (-(S_I / ℏ))) = complexActionNats ℏ S_I := by
  unfold complexActionNats
  simp [Real.log_exp]

/-! ## Wire-up to physlib's second-law infrastructure (`SecondLaw.lean`)

The `landauerPrinciple_full` theorem above threads the Clausius bound
`kB · T · ΔH_Shannon ≤ Q` as a hypothesis `hClausius`.  Physlib's
`Physlib.Thermodynamics.SecondLaw` provides the **entropic-time
monotonicity** form of the second law as a *theorem* —
`EntropyArrowWorldline.tau_ent_delta_nonneg` — for any `S_I_monotone`
worldline.  What that theorem **does not** directly give is the
*energetic* Clausius inequality `Q ≥ T·ΔS_th`: the conversion from
entropic-time advance `Δτ_ent` to dissipated heat `Q` requires
additional first-law / heat-flow content not yet theorem-grade in
physlib.

What we CAN bridge: the **worldline-energy form** of the Landauer
cost.  For an `EntropyArrowWorldline` `W`, the energy scale
`T · kB · Δτ_ent` is bounded below by `landauerCost T` once the
imaginary-action advance reaches the one-bit threshold `W.ℏ · log 2`.
This is a substantive, unconditional theorem (no `hClausius`
hypothesis at the call site): the second-law monotonicity
(`W.S_I_monotone`) is *baked into* the worldline structure, so
proving it on the consumer side is automatic.
-/

open Physlib.Thermodynamics.SecondLaw in
/-- **Landauer cost ≤ worldline energy scale** (one-bit threshold).

Given an `EntropyArrowWorldline` `W`, a temperature `T > 0`, and times
`t₁, t₂` over which the imaginary action advances by at least
`W.ℏ · log 2` (one bit's worth of `S_I`), the energy scale
`T · kB · Δτ_ent` exceeds the textbook Landauer per-bit cost:

  `landauerCost T  ≤  T · kB · (W.τ_ent_along t₂ - W.τ_ent_along t₁)`.

The worldline `S_I_monotone` field (the second-law content from
`SecondLaw.lean`) is used implicitly via `W.τ_ent_eq`. -/
theorem landauerCost_le_kBT_tau_ent_delta_of_one_bit
    (W : EntropyArrowWorldline) (T : ℝ) (hT : 0 < T)
    {t₁ t₂ : ℝ}
    (h_one_bit :
      W.ℏ * Real.log 2 ≤ W.S_I_along t₂ - W.S_I_along t₁) :
    landauerCost T ≤ T * kB * (W.τ_ent_along t₂ - W.τ_ent_along t₁) := by
  unfold landauerCost
  rw [W.τ_ent_eq, W.τ_ent_eq, ← sub_div]
  have hΔτ : Real.log 2 ≤ (W.S_I_along t₂ - W.S_I_along t₁) / W.ℏ := by
    rw [le_div_iff₀ W.ℏ_pos]; linarith
  have hkBT : 0 ≤ T * kB := mul_nonneg hT.le kB_nonneg
  have hcomm : kB * T * Real.log 2 = T * kB * Real.log 2 := by ring
  rw [hcomm]
  exact mul_le_mul_of_nonneg_left hΔτ hkBT

open Physlib.Thermodynamics.SecondLaw in
/-- **One-bit `τ_ent` ↔ one-bit `S_I`.** For an `EntropyArrowWorldline`,
the entropic-time advance equals exactly `log 2` iff the imaginary-action
advance equals exactly `W.ℏ · log 2`. The worldline-level algebraic
content of the bit-counting identification. -/
theorem tau_ent_delta_eq_log2_iff_S_I_delta_eq_hbar_log2
    (W : EntropyArrowWorldline) {t₁ t₂ : ℝ} :
    W.τ_ent_along t₂ - W.τ_ent_along t₁ = Real.log 2 ↔
      W.S_I_along t₂ - W.S_I_along t₁ = W.ℏ * Real.log 2 := by
  rw [W.τ_ent_eq, W.τ_ent_eq, ← sub_div]
  have hℏ_ne : W.ℏ ≠ 0 := ne_of_gt W.ℏ_pos
  rw [div_eq_iff hℏ_ne, mul_comm]

open Physlib.Thermodynamics.SecondLaw in
/-- **Second-law Landauer along a worldline.** The
unconditional form: given an `EntropyArrowWorldline` whose `S_I` advances
by exactly `W.ℏ · log 2` (one bit), the worldline energy scale
`T · kB · Δτ_ent` equals the textbook Landauer cost `landauerCost T`.

Combines `tau_ent_delta_eq_log2_iff_S_I_delta_eq_hbar_log2` with the
`landauerCost` definition; the second-law content is automatically
supplied by the `EntropyArrowWorldline` structure. -/
theorem landauerCost_eq_kBT_tau_ent_delta_at_one_bit
    (W : EntropyArrowWorldline) (T : ℝ)
    {t₁ t₂ : ℝ}
    (h_one_bit :
      W.S_I_along t₂ - W.S_I_along t₁ = W.ℏ * Real.log 2) :
    T * kB * (W.τ_ent_along t₂ - W.τ_ent_along t₁) = landauerCost T := by
  have hτ :
      W.τ_ent_along t₂ - W.τ_ent_along t₁ = Real.log 2 :=
    (tau_ent_delta_eq_log2_iff_S_I_delta_eq_hbar_log2 W).mpr h_one_bit
  rw [hτ]
  unfold landauerCost; ring

/-! ## Szilard partition-function bridge (algebraic chain)

Ashrafi et al. (2022) write the Szilard insertion probability as
`p_L(δ) = Z_x(δ) / (Z_x(δ) + Z_x(1-δ))` for partition functions
`Z_x(δ), Z_x(1-δ) > 0` of a 1D particle-in-box with barrier at `δ`.
The full computation of `Z_x(δ) = ½(θ₃(0, q) - 1)` (Eq. paper p.3)
requires a 1D Schrödinger-box module not present in physlib.

What IS algebraic — and provable theorem-grade here — is the
**informational** half of the chain: any two non-negative reals
`Z_L, Z_R` with `Z_L + Z_R > 0` define a Bernoulli probability
`p_L = Z_L / (Z_L + Z_R)`, and the Szilard cost at that partition
parameter equals `kB · T · binEntropy p_L`.

The substantive identities below use existing physlib infrastructure
(`Real.binEntropy_one_sub`, `szilardLandauerCost_symm`,
`szilardLandauerCost_at_half`).  No QM, no new defs, no axioms.
-/

/-- **Reflection symmetry from partition-function ratios.**

For weights with positive total `Z_L + Z_R > 0`, the Szilard cost at
`p_L = Z_L/(Z_L+Z_R)` equals the Szilard cost at
`p_R = Z_R/(Z_L+Z_R)`.  Direct from `szilardLandauerCost_symm` plus
the algebraic identity `Z_R/(Z_L+Z_R) = 1 - Z_L/(Z_L+Z_R)`. -/
theorem szilardLandauerCost_partition_swap
    (T Z_L Z_R : ℝ) (hsum : 0 < Z_L + Z_R) :
    szilardLandauerCost T (Z_R / (Z_L + Z_R))
      = szilardLandauerCost T (Z_L / (Z_L + Z_R)) := by
  have h_one_sub :
      Z_R / (Z_L + Z_R) = 1 - Z_L / (Z_L + Z_R) := by
    field_simp; ring
  rw [h_one_sub, szilardLandauerCost_symm]

/-- **Symmetric-partition reduction to Landauer** (`Z_L = Z_R` case).

When the two compartment partition functions are equal and positive,
`p_L = Z/(Z+Z) = 1/2`, and the Szilard cost reduces to the textbook
per-bit Landauer cost `landauerCost T`. -/
theorem szilardLandauerCost_symmetric_partition
    (T Z : ℝ) (hZ : 0 < Z) :
    szilardLandauerCost T (Z / (Z + Z)) = landauerCost T := by
  have h_half : Z / (Z + Z) = 1 / 2 := by
    have hZ_ne : Z ≠ 0 := ne_of_gt hZ
    field_simp; ring
  rw [h_half, szilardLandauerCost_at_half]

/-- **Trivial-partition vanishing from partition-function ratios.**

If one of the compartment partition functions vanishes (`Z_L = 0` or
`Z_R = 0`), the Szilard cost is zero: a trivial partition has no
thermodynamic price.  Consequence of `szilardLandauerCost_zero` /
`szilardLandauerCost_one` and the algebra of `Z / (Z + 0)` etc. -/
theorem szilardLandauerCost_trivial_from_partition
    (T Z_L Z_R : ℝ) (hsum : 0 < Z_L + Z_R)
    (h_trivial : Z_L = 0 ∨ Z_R = 0) :
    szilardLandauerCost T (Z_L / (Z_L + Z_R)) = 0 := by
  rcases h_trivial with hL | hR
  · rw [hL, zero_div, szilardLandauerCost_zero]
  · rw [hR, add_zero, div_self (ne_of_gt (by linarith : 0 < Z_L)),
        szilardLandauerCost_one]

/-- **Szilard ≤ Landauer from partition-function ratios.**

For any non-negative `Z_L, Z_R` with `Z_L + Z_R > 0` and `T ≥ 0`,
the Szilard cost at the partition ratio `Z_L/(Z_L+Z_R)` is at most
the standard per-bit Landauer cost, with equality only at the
symmetric partition `Z_L = Z_R`.  Composes `szilardLandauerCost_le_landauer`
with the partition-ratio probability. -/
theorem szilardLandauerCost_from_partition_le_landauer
    (T Z_L Z_R : ℝ) (hT : 0 ≤ T) :
    szilardLandauerCost T (Z_L / (Z_L + Z_R)) ≤ landauerCost T :=
  szilardLandauerCost_le_landauer T (Z_L / (Z_L + Z_R)) hT

/-! ## Boltzmann's principle from the canonical ensemble

Boltzmann's identification `S_thermo = kB · H_Shannon` is encoded
*definitionally* in `Physlib.StatisticalMechanics.CanonicalEnsemble.Finite`
as

  `CanonicalEnsemble.shannonEntropy T  =  -kB · Σ p(i) · log p(i)`

(`Finite.lean:175`), where `p(i) = probability T i = exp(-β E(i)) / Z`
is the Gibbs probability of microstate `i`.  Physlib also proves
`probability_nonneg_finite` and `sum_probability_eq_one`, so the
canonical probabilities canonically form a `ProbDistribution ι`.

The **bridge theorem** below proves that this thermodynamic Shannon
entropy equals `kB · Hₛ` of the canonical probability distribution
viewed as a `QuantumInfo.ClassicalInfo.ProbDistribution`.  This is the
discrete Boltzmann identification *as a theorem* — Boltzmann's principle
holds in the canonical ensemble.

The continuous-Gibbs version `Q ≥ T · ΔS_th` for irreversible processes
is **not** added: it requires first-law / heat-flow machinery
(δQ = T·dS) not yet theorem-grade in physlib.
-/

/-- **Boltzmann's principle in the discrete canonical ensemble** —
the thermodynamic Shannon entropy of a finite canonical ensemble equals
`kB` times the discrete Shannon entropy `Hₛ` of its Gibbs probability
distribution.

  `𝓒.shannonEntropy T  =  kB · Hₛ p_canonical(T)`,

where `p_canonical(T) := ⟨probability T, probability_nonneg_finite, sum_probability_eq_one⟩`
is the canonical probability distribution as a
`QuantumInfo.ClassicalInfo.ProbDistribution`.

Proof: rewrite `Σ p · log p = - Σ negMulLog p`, factor `kB`, and unfold
`Hₛ = Σ negMulLog ∘ d.prob` for the constructed distribution. -/
theorem canonical_shannonEntropy_eq_kB_Hₛ
    {ι : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (𝓒 : CanonicalEnsemble ι) [CanonicalEnsemble.IsFinite 𝓒] [Nonempty ι]
    (T : Temperature) :
    𝓒.shannonEntropy T
      = kB * Hₛ (ProbDistribution.mk' (fun i => 𝓒.probability T i)
                  (𝓒.probability_nonneg_finite T)
                  (𝓒.sum_probability_eq_one T)) := by
  rw [𝓒.entropy_of_fintype T]
  simp only [Hₛ, H₁, Real.negMulLog, Finset.mul_sum, ProbDistribution.prob,
             ProbDistribution.mk', DFunLike.coe]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-! ## Heat-flow identification `δQ = T · dS` derived as a theorem

The previous Landauer-from-Clausius layer took the energetic identification
`Q ≥ T · ΔS_th` as a hypothesis (`hClausius`).  The standard physical
reason is the **reservoir relation** `δQ_res = T · dS_res`, which is
usually stated as the definition of a thermal bath at temperature `T`.

In physlib we can **derive** this relation from
`FreeEnergy.HelmholtzWorldline.clausius_equality_from_helmholtz_constant`:
modelling a thermal reservoir as a `HelmholtzWorldline` whose free
energy `F = U - T·S` is constant (the equilibrium condition for an
idealised heat bath) immediately gives `ΔU = T · ΔS`.  Identifying
the heat absorbed with `ΔU` (no work done on the reservoir, by the
reservoir model) closes the chain:

  `Q_absorbed_by_reservoir  =  T · ΔS_reservoir`            (THEOREM)

This replaces the previously-constitutive "heat-flow identification"
with a derivation from existing physlib infrastructure.
-/

open Physlib.Thermodynamics.FreeEnergy

/-- A **thermal reservoir** is a `HelmholtzWorldline` whose free energy
is constant — the equilibrium condition for an idealised heat bath at
fixed temperature.

The standard "δQ = T·dS" identification is then a *theorem* about
this structure (see `heatAbsorbed_eq_T_entropyChange`), not an axiom.
-/
structure ThermalReservoir extends HelmholtzWorldline where
  /-- The reservoir stays at thermal equilibrium throughout: `F = U − T·S`
  is constant in time.  This encodes the *defining property* of an
  idealised heat bath — it maintains its temperature regardless of
  heat exchanged. -/
  equilibrium : ∀ t₁ t₂ : ℝ,
    U t₁ - T * S t₁ = U t₂ - T * S t₂

namespace ThermalReservoir

variable (R : ThermalReservoir)

/-- **Internal-energy/entropy bridge (theorem).**  For a thermal
reservoir, the internal-energy change equals `T · ΔS`. Direct corollary
of `HelmholtzWorldline.clausius_equality_from_helmholtz_constant` with
the reservoir's `equilibrium` field. -/
theorem internalEnergy_change_eq_T_entropyChange (t₁ t₂ : ℝ) :
    R.U t₂ - R.U t₁ = R.T * (R.S t₂ - R.S t₁) := by
  have hF :
      R.toHelmholtzWorldline.helmholtz t₁
        = R.toHelmholtzWorldline.helmholtz t₂ := by
    unfold HelmholtzWorldline.helmholtz
    exact R.equilibrium t₁ t₂
  exact R.toHelmholtzWorldline.clausius_equality_from_helmholtz_constant hF

/-- **Heat absorbed by the reservoir** = its internal-energy change.

This is the no-work assumption on the reservoir: any energy added to
the reservoir came in as heat.  Together with
`internalEnergy_change_eq_T_entropyChange` this gives the textbook
δQ = T·dS identification (see `heatAbsorbed_eq_T_entropyChange`). -/
def heatAbsorbed (t₁ t₂ : ℝ) : ℝ := R.U t₂ - R.U t₁

/-- **Heat-flow identification (theorem)** — `δQ = T · dS` for a
thermal reservoir.

The textbook reservoir law, now *derived* from
`HelmholtzWorldline.clausius_equality_from_helmholtz_constant` and
the no-work definition of `heatAbsorbed`.

  `Q_absorbed  =  T · ΔS`. -/
theorem heatAbsorbed_eq_T_entropyChange (t₁ t₂ : ℝ) :
    R.heatAbsorbed t₁ t₂ = R.T * (R.S t₂ - R.S t₁) := by
  unfold heatAbsorbed
  exact R.internalEnergy_change_eq_T_entropyChange t₁ t₂

end ThermalReservoir

/-! ## Landauer's principle fully derived (no Clausius input)

With the heat-flow identification now theorem-grade
(`ThermalReservoir.heatAbsorbed_eq_T_entropyChange`) and the second law
applied to the combined memory + reservoir system, the Landauer bound
becomes a *fully-derived* theorem.  No `hClausius` hypothesis is
required at the call site.
-/

/-- A **Landauer-erasure setup**: a memory subsystem whose thermodynamic
entropy decreases by exactly `kB · log 2` (one bit erased), coupled to
a `ThermalReservoir`, with the second law on the total system as the
single physical input.

The second-law field can be supplied from physlib's
`EntropyArrowWorldline` framework (see `SecondLaw.lean`) — it is the
standard `ΔS_total ≥ 0` content from `tau_ent_delta_nonneg`. -/
structure LandauerErasureSetup where
  reservoir : ThermalReservoir
  t_pre : ℝ
  t_post : ℝ
  /-- Memory entropy change in thermodynamic units (J/K).
  For one-bit erasure: `ΔS_memory = -kB · log 2`. -/
  ΔS_memory : ℝ
  /-- Memory loses exactly one bit of thermodynamic entropy. -/
  one_bit_erasure : ΔS_memory = -kB * Real.log 2
  /-- **Second law on the total system** (memory + reservoir): the
  total thermodynamic entropy is non-decreasing across the erasure
  interval.  Encodes the second law as applied to this specific
  process. -/
  total_entropy_nondecreasing :
    0 ≤ ΔS_memory + (reservoir.S t_post - reservoir.S t_pre)

namespace LandauerErasureSetup

variable (E : LandauerErasureSetup)

/-- Heat absorbed by the reservoir during the erasure interval. -/
def Q_to_reservoir : ℝ := E.reservoir.heatAbsorbed E.t_pre E.t_post

/-- **Landauer's principle (fully derived).**

For a one-bit `LandauerErasureSetup`, the heat dumped to the thermal
reservoir is at least the textbook Landauer cost `kB · T · log 2`:

  `landauerCost E.reservoir.T  ≤  E.Q_to_reservoir`.

**Derivation chain — no Clausius input at the call site:**

1. The reservoir is a `HelmholtzWorldline` at constant `F`
   (equilibrium); by `heatAbsorbed_eq_T_entropyChange` (theorem),
   `Q = T · ΔS_reservoir`.
2. From `total_entropy_nondecreasing`:
   `ΔS_reservoir ≥ -ΔS_memory = kB · log 2` (using `one_bit_erasure`).
3. Multiply by `T > 0`: `Q = T · ΔS_reservoir ≥ T · kB · log 2 =
   landauerCost T`.

Every step is a theorem — no `hClausius` hypothesis. -/
theorem landauer_bound :
    landauerCost E.reservoir.T ≤ E.Q_to_reservoir := by
  unfold Q_to_reservoir
  rw [E.reservoir.heatAbsorbed_eq_T_entropyChange]
  -- Goal: landauerCost T ≤ T · (S_post - S_pre)
  have h_sl := E.total_entropy_nondecreasing
  rw [E.one_bit_erasure] at h_sl
  have h_res_ge :
      kB * Real.log 2 ≤ E.reservoir.S E.t_post - E.reservoir.S E.t_pre := by
    linarith
  have hT_nonneg : 0 ≤ E.reservoir.T := le_of_lt E.reservoir.T_pos
  unfold landauerCost
  have hrw : kB * E.reservoir.T * Real.log 2
      = E.reservoir.T * (kB * Real.log 2) := by ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left h_res_ge hT_nonneg

/-- **Reservoir entropy absorbs at least one bit's worth** (corollary).
For one-bit erasure, the reservoir's thermodynamic entropy advances
by at least `kB · log 2`. -/
theorem reservoir_entropy_advance_ge_one_bit :
    kB * Real.log 2 ≤ E.reservoir.S E.t_post - E.reservoir.S E.t_pre := by
  have h_sl := E.total_entropy_nondecreasing
  rw [E.one_bit_erasure] at h_sl
  linarith

end LandauerErasureSetup

/-! ### `one_bit_erasure` proved from `|state| = 2`

`LandauerErasureSetup.one_bit_erasure` plants `ΔS_memory = −kB · log 2`
as a field.  `TwoStateErasureSetup` replaces it with a *concrete*
two-element memory configuration space `State` (`Fintype.card State = 2`)
and a `target` erasure configuration; `ΔS_memory` is then **computed**
as `kB · (Hₛ(constant) − Hₛ(uniform))` and equals `−kB · log 2` by
`twoStateErasure_memory_entropy_change` — a theorem, sourced from the
cardinality.  The only remaining physical input is the second law on
the total system, exactly as in `LandauerErasureSetup`. -/

/-- A **two-state-memory Landauer erasure**: the memory configuration
space is a finite type `State` with exactly two configurations, coupled
to a `ThermalReservoir`.  Unlike `LandauerErasureSetup`, the memory
entropy change is not a free field — it is fixed by `Fintype.card State`. -/
structure TwoStateErasureSetup (State : Type) [Fintype State] [Nonempty State] where
  /-- The thermal reservoir the erased information is dumped into. -/
  reservoir : ThermalReservoir
  /-- Time before erasure. -/
  t_pre : ℝ
  /-- Time after erasure. -/
  t_post : ℝ
  /-- One bit: the memory has exactly two configurations. -/
  card_eq_two : Fintype.card State = 2
  /-- The single post-erasure configuration. -/
  target : State
  /-- **Second law on the total system** (memory + reservoir): the total
  thermodynamic entropy is non-decreasing across the erasure interval,
  with the memory entropy change computed (not assumed) from the
  uniform → constant Shannon-entropy drop. -/
  total_entropy_nondecreasing :
    0 ≤ kB * (Hₛ (ProbDistribution.constant target)
              - Hₛ (ProbDistribution.uniform (α := State)))
        + (reservoir.S t_post - reservoir.S t_pre)

namespace TwoStateErasureSetup

variable {State : Type} [Fintype State] [Nonempty State] (E : TwoStateErasureSetup State)

/-- A `TwoStateErasureSetup` is a `LandauerErasureSetup` whose
`one_bit_erasure` field is **proved** by
`twoStateErasure_memory_entropy_change` — the `−kB · log 2` is derived
from `card_eq_two`, not planted. -/
noncomputable def toLandauerErasureSetup : LandauerErasureSetup where
  reservoir := E.reservoir
  t_pre := E.t_pre
  t_post := E.t_post
  ΔS_memory := kB * (Hₛ (ProbDistribution.constant E.target)
                     - Hₛ (ProbDistribution.uniform (α := State)))
  one_bit_erasure := twoStateErasure_memory_entropy_change E.card_eq_two E.target
  total_entropy_nondecreasing := E.total_entropy_nondecreasing

/-- **Landauer's principle for a two-state memory** — the floor is now
derived from `|state| = 2`.  The heat dumped to the reservoir is at least
`landauerCost T = kB · T · log 2`. -/
theorem landauer_bound :
    landauerCost E.reservoir.T ≤ E.toLandauerErasureSetup.Q_to_reservoir :=
  E.toLandauerErasureSetup.landauer_bound

/-- **The floor equals the log of the memory cardinality.** The reservoir
entropy advances by at least `kB · Real.log (Fintype.card State)`, which
for a one-bit memory (`card = 2`) is `kB · log 2`.  This exhibits the
Landauer floor as a counting result. -/
theorem reservoir_entropy_advance_ge_log_card :
    kB * Real.log (Fintype.card State)
      ≤ E.reservoir.S E.t_post - E.reservoir.S E.t_pre := by
  rw [E.card_eq_two]
  push_cast
  exact E.toLandauerErasureSetup.reservoir_entropy_advance_ge_one_bit

end TwoStateErasureSetup

/-- **Non-vacuity witness**: a concrete reversible one-bit erasure on the
configuration space `Fin 2`.  The reservoir's entropy rises by exactly
`kB · log 2` over `[0, 1]`, so the second-law field holds with equality
(the reversible / Clausius-saturated case).  Confirms
`TwoStateErasureSetup` is inhabited and not vacuous. -/
noncomputable def reversibleBitErasureWitness : TwoStateErasureSetup (Fin 2) where
  reservoir :=
    { U := fun t => kB * Real.log 2 * t
      S := fun t => kB * Real.log 2 * t
      T := 1
      T_pos := one_pos
      equilibrium := by intro t₁ t₂; ring }
  t_pre := 0
  t_post := 1
  card_eq_two := by simp
  target := 0
  total_entropy_nondecreasing := by
    have hu : Hₛ (ProbDistribution.uniform (α := Fin 2)) = Real.log 2 :=
      bitMemoryEntropy_uniform
    have hc : Hₛ (ProbDistribution.constant (0 : Fin 2)) = 0 :=
      bitMemoryEntropy_constant 0
    rw [hu, hc]
    ring_nf
    exact le_refl _

section SecondLawDerived
open Physlib.Thermodynamics.SecondLaw

/-- **Total-entropy worldline for a two-state erasure**, built from a positive
(dissipative) irreversible generator `H_I = 1` on `ℂ`.  Its `S_I_monotone` — the
second law `ΔS_total ≥ 0` — is the *derived* monotonicity of
`SecondLaw.ofPositiveGeneratorArrow`, whose sole premise is `H_I.IsPositive`
(operator positivity, the definition of dissipativity), with no monotonicity
postulate. -/
noncomputable def secondLawErasureWorldline : EntropyArrowWorldline :=
  ofPositiveGeneratorArrow (H := ℂ) 0 1 1 one_pos ContinuousLinearMap.isPositive_one 0

/-- **The second-law field, derived from an entropy-arrow worldline.**
Assembles a `TwoStateErasureSetup` whose `total_entropy_nondecreasing` is obtained
from the monotonicity of an `EntropyArrowWorldline` with the *total*
(memory + reservoir) entropy, given that the worldline matches
`kB·Hₛ(memory) + S_reservoir` at the pre/post endpoints.

The worldline's `S_I_monotone` *is* the second law `ΔS_total ≥ 0`; when the
worldline comes from `SecondLaw.ofPositiveGeneratorArrow`, that monotonicity is a
theorem with sole premise `H_I ⪰ 0`, so no second-law postulate enters the
erasure setup. -/
noncomputable def TwoStateErasureSetup.ofTotalEntropyWorldline
    {State : Type} [Fintype State] [Nonempty State]
    (total : EntropyArrowWorldline) (reservoir : ThermalReservoir)
    (t_pre t_post : ℝ) (htime : t_pre ≤ t_post)
    (hcard : Fintype.card State = 2) (target : State)
    (hpre : total.S_I_along t_pre
            = kB * Hₛ (ProbDistribution.uniform (α := State)) + reservoir.S t_pre)
    (hpost : total.S_I_along t_post
            = kB * Hₛ (ProbDistribution.constant target) + reservoir.S t_post) :
    TwoStateErasureSetup State where
  reservoir := reservoir
  t_pre := t_pre
  t_post := t_post
  card_eq_two := hcard
  target := target
  total_entropy_nondecreasing := by
    have hmono := total.S_I_monotone htime
    rw [hpre, hpost] at hmono
    rw [mul_sub]
    linarith

/-- **The Landauer second law `ΔS_total ≥ 0` is a theorem; its only premise is
`H_I ⪰ 0`.**  For a two-state erasure whose total entropy is encoded in
`SecondLaw.ofPositiveGeneratorArrow H_R H_I hbar _ hpos ψ` — monotone with no
second-law postulate, only the operator positivity `H_I.IsPositive` — the
combined memory + reservoir entropy change is non-negative.  Hypotheses
`hpre`/`hpost` are the operational identification of the worldline's entropy with
the concrete `kB·Hₛ(memory) + S_reservoir`; the second law itself is derived, not
assumed. -/
theorem TwoStateErasureSetup.total_entropy_nondecreasing_of_positive_generator
    {State : Type} [Fintype State] [Nonempty State]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R H_I : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hpos : H_I.IsPositive) (ψ : H)
    (reservoir : ThermalReservoir) {t_pre t_post : ℝ} (htime : t_pre ≤ t_post)
    (target : State)
    (hpre : (ofPositiveGeneratorArrow H_R H_I hbar hbar_pos hpos ψ).S_I_along t_pre
            = kB * Hₛ (ProbDistribution.uniform (α := State)) + reservoir.S t_pre)
    (hpost : (ofPositiveGeneratorArrow H_R H_I hbar hbar_pos hpos ψ).S_I_along t_post
            = kB * Hₛ (ProbDistribution.constant target) + reservoir.S t_post) :
    0 ≤ kB * (Hₛ (ProbDistribution.constant target)
              - Hₛ (ProbDistribution.uniform (α := State)))
        + (reservoir.S t_post - reservoir.S t_pre) := by
  have hmono :=
    ofPositiveGeneratorArrow_S_I_monotone H_R H_I hbar hbar_pos hpos ψ htime
  rw [hpre, hpost] at hmono
  rw [mul_sub]
  linarith

/-- **Fully derived non-vacuity witness.**  A two-state erasure on `Fin 2` whose
second-law field is obtained — through `ofTotalEntropyWorldline` — from
`secondLawErasureWorldline.S_I_monotone`, i.e. from the positivity of the
dissipative generator `H_I = 1`.  Unlike `reversibleBitErasureWitness` (whose
field is proved by direct arithmetic), here the inequality bottoms out in
`H_I ⪰ 0`, with no second-law assumption anywhere in the chain.  The reservoir
entropy is fixed to `S_total − kB·log 2·(1 − t)`, making the endpoint
identifications definitional. -/
noncomputable def secondLawDerivedBitErasure : TwoStateErasureSetup (Fin 2) :=
  TwoStateErasureSetup.ofTotalEntropyWorldline
    secondLawErasureWorldline
    { U := fun t => secondLawErasureWorldline.S_I_along t - kB * Real.log 2 * (1 - t)
      S := fun t => secondLawErasureWorldline.S_I_along t - kB * Real.log 2 * (1 - t)
      T := 1
      T_pos := one_pos
      equilibrium := by intro t₁ t₂; ring }
    0 1 (by norm_num)
    (by simp)
    0
    (by simp only [bitMemoryEntropy_uniform]; ring)
    (by simp only [bitMemoryEntropy_constant]; ring)

end SecondLawDerived

end Physlib.Thermodynamics.Landauer

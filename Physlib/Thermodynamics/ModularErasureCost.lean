/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.ComputationLandauer
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks
public import Physlib.Relativity.SemiClassical.SchwarzschildEntropicRate
meta import Zil

/-!
# The modular erasure cost — Landauer at the KMS temperature of the modular flow

The AQFT form of Landauer's principle: the heat of erasing information is set by the **modular
structure** of the local algebra, `ΔQ = β⁻¹ ΔS` with `β` the KMS inverse temperature of the modular
flow (Kay–Wald on the bifurcate Killing horizon) and `ΔS = k_B log 2` per bit. This module states
that dictionary as exact identities over the repo's existing carriers — no new physical postulate:

* **§A the erasure cost at the modular temperature.** `landauerCost (hawkingTemperature) =
  ℏκ·log 2/(2πc)`: the Boltzmann constant cancels and the cost of one bit is a pure **modular
  quantum** — surface gravity per Euclidean period. The Clausius form
  `β · landauerCost = k_B log 2` is the exact `ΔQ = β⁻¹ ΔS_rel` of the AQFT Landauer bound, and a
  quantum-Turing-machine trace (`QTMTrace`, fields computing) pays its **measurement count** times
  the modular quantum: computation → thermodynamics → modular theory in one chain.
* **§B the modular Hamiltonian is minus the log of the modular operator.** `K = −log Δ` at the
  wedge-eigenvalue level: `−log (wedgeModularEigenvalue κ ℏ) = modularHamEigenvalue κ ℏ`, with
  `Δ > 0` — the Tomita–Takesaki definition of the modular Hamiltonian, realized on the pair shadow.
* **§C no totally separate algebras.** In the operator model, the wedge algebra `{K}″` and its
  causal complement `{K}′` both contain the full center (and the unit): local algebras are never
  tensor-independent islands — the AQFT nonseparability that forces erasure accounting to be done
  relative to the ambient algebra, not an isolated register.

What is **not** claimed: an operator-level Araki relative entropy (the identities are eigenvalue /
counting shadows on existing carriers), and no inequality is asserted beyond the exact ideal-erasure
identities — `traceLandauerEnergy` *is* the Landauer bound saturated.

## References

* R. Landauer, *Irreversibility and heat generation in the computing process*, IBM J. Res. Dev. 5
  (1961). C. H. Bennett, *The thermodynamics of computation — a review*, Int. J. Theor. Phys. 21
  (1982). B. S. Kay, R. M. Wald, *Theorems on the unique quasifree state on horizons*, Phys. Rep.
  207 (1991). H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS 11 (1976).
* Repo carriers: `Thermodynamics.Landauer.landauerCost/qtmLandauerCount/traceLandauerEnergy`,
  `Relativity.SemiClassical.hawkingTemperature`, `KayWaldHawkingKMSHorizon.hawkingBeta`,
  `QFT.PathIntegral.wedgeModularEigenvalue/modularHamEigenvalue`,
  `AlgebraicQFT.SummersVacuumModularLinks.wedgeAlgebra/causalComplementAlgebra`.
-/

set_option autoImplicit false

open Constants
open Physlib.Thermodynamics.Landauer
open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
open Physlib.QFT.PathIntegral

@[expose] public section

namespace Physlib.Thermodynamics.ModularErasureCost

/-! ## A. The erasure cost at the modular temperature -/

/-- **[One bit at the Hawking temperature costs one modular quantum]** `k_B T_H log 2 =
ℏκ·log 2/(2πc)`. Evaluating the Landauer cost at the KMS temperature of the modular flow, the
Boltzmann constant cancels: the erasure cost per bit is surface gravity per Euclidean period — a
pure modular quantum, no thermodynamic constant left. -/
lemma landauerCost_hawkingTemperature (ℏ κ c : ℝ) (hc : c ≠ 0) :
    landauerCost (hawkingTemperature ℏ κ c kB) =
      ℏ * κ * Real.log 2 / (2 * Real.pi * c) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hkB : kB ≠ 0 := kB_pos.ne'
  rw [landauerCost_def, hawkingTemperature_def]
  field_simp

/-- **[The Clausius form of the AQFT Landauer bound]** `β · ΔQ_bit = k_B log 2`. The KMS inverse
temperature of the modular flow times the one-bit erasure heat is exactly the entropy of one bit —
the `ΔQ = β⁻¹ ΔS_rel` of the local Landauer bound, saturated. -/
lemma hawkingBeta_mul_landauerCost (ℏ κ c : ℝ)
    (hT : hawkingTemperature ℏ κ c kB ≠ 0) :
    hawkingBeta ℏ κ c kB * landauerCost (hawkingTemperature ℏ κ c kB) =
      kB * Real.log 2 := by
  unfold hawkingBeta
  rw [landauerCost_def]
  field_simp

/-- **[A quantum Turing machine trace pays its measurement count in modular quanta]**
`E(trace, T_H) = qtmLandauerCount · ℏκ·log 2/(2πc)`. The Landauer energy of a QTM trace at the
modular temperature is the number of its irreversible (measurement) steps times the modular quantum:
the computability layer (`qtmLandauerCount`, fields computing) meets the modular layer (Kay–Wald KMS
temperature) in one exact identity. Unitary-only traces cost zero. -/
theorem qtmTrace_erasure_modular_quantum (trace : QTMTrace) (ℏ κ c : ℝ) (hc : c ≠ 0) :
    traceLandauerEnergy (trace.map QubitStep.reversibility) (hawkingTemperature ℏ κ c kB) =
      (qtmLandauerCount trace : ℝ) * (ℏ * κ * Real.log 2 / (2 * Real.pi * c)) := by
  rw [traceLandauerEnergy_eq_count_mul_landauerCost,
    landauerCost_hawkingTemperature ℏ κ c hc]
  rfl

/-- **[One bit erased at the horizon grows the entropy by exactly one bit]**
`(dS/dM)·(ΔM_bit) = k_B·ln 2`. The Schwarzschild first-law entropy derivative
(`SchwarzschildVerlinde.schwarzschild_first_law`, `dS/dM = 8πGMk_B/(ℏc)`) times the Landauer mass
increment — the cost of erasing one bit at the Hawking temperature, converted to mass by `E = Mc²`
— is exactly one bit of horizon entropy. Landauer's principle and Bekenstein's horizon accounting
are the *same* bookkeeping: feeding the horizon the erasure cost of one bit buys precisely
`k_B ln 2` of entropy — the horizon face of this module's erasure dictionary. Consequently this equality
cannot independently fail once the Schwarzschild first-law normalization, Hawking temperature, and ideal
Landauer cost used here are fixed. -/
theorem horizon_bit_erasure_is_one_bit_entropy
    {M G ℏ c : ℝ} (hM : M ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) :
    (8 * Real.pi * G * M * kB / (ℏ * c))
        * (landauerCost
            (hawkingTemperature ℏ
              (Physlib.Relativity.SemiClassical.schwarzschildSurfaceGravity G M c) c kB) / c ^ 2)
      = kB * Real.log 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hkB : kB ≠ 0 := kB_pos.ne'
  rw [landauerCost_def, hawkingTemperature_def]
  unfold Physlib.Relativity.SemiClassical.schwarzschildSurfaceGravity
  field_simp
  norm_num

/-! ## B. The modular Hamiltonian is minus the log of the modular operator -/

/-- **[The modular operator is strictly positive]** `Δ > 0` — the wedge modular eigenvalue is a
positive Boltzmann weight, as Tomita–Takesaki requires of `Δ`. -/
lemma wedgeModularEigenvalue_pos (κ ℏ : ℝ) : 0 < wedgeModularEigenvalue κ ℏ :=
  Real.exp_pos _

/-- **[`K = −log Δ`]** `−log (wedgeModularEigenvalue κ ℏ) = modularHamEigenvalue κ ℏ`. The
Tomita–Takesaki definition of the modular Hamiltonian — minus the logarithm of the modular
operator — holds exactly at the wedge-eigenvalue level: the log of the full-Euclidean-period
Boltzmann weight is the boost generator eigenvalue `2πκ/ℏ`. -/
theorem neg_log_wedgeModularEigenvalue (κ ℏ : ℝ) :
    -Real.log (wedgeModularEigenvalue κ ℏ) = modularHamEigenvalue κ ℏ := by
  unfold wedgeModularEigenvalue modularHamEigenvalue
  rw [Real.log_exp]
  ring

/-! ## C. No totally separate algebras -/

section NoSeparation

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks

variable {A : Type*} [Ring A]

/-- **[The wedge algebra and its causal complement share the full center]** `Z(A) ⊆ {K}″ ∩ {K}′`.
Local algebras are never totally separate: every central element — in particular the unit — lies in
*both* the wedge algebra and the causal-complement algebra, so the two are not tensor-independent
islands. This is the AQFT nonseparability that forces Landauer accounting to be done relative to the
ambient algebra: a "register" is an embedded subalgebra, never an isolated factor. -/
theorem center_subset_wedge_and_causalComplement (K : A) :
    Set.center A ⊆ wedgeAlgebra K ∧ Set.center A ⊆ causalComplementAlgebra K ∧
      (1 : A) ∈ wedgeAlgebra K ∧ (1 : A) ∈ causalComplementAlgebra K := by
  have key : ∀ (S : Set A), Set.center A ⊆ Set.centralizer S := by
    intro S x hx
    rw [Set.mem_centralizer_iff]
    intro m _
    exact Semigroup.mem_center_iff.mp hx m
  have hone : (1 : A) ∈ Set.center A := Set.one_mem_center
  simp only [wedgeAlgebra, causalComplementAlgebra,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant]
  exact ⟨key _, key _, key _ hone, key _ hone⟩

end NoSeparation

/-! ## D. The erased-information heat — the Clausius / relative-entropy form

The `ΔQ = β⁻¹ ΔS_rel` of the AQFT Landauer bound with `ΔS_rel` the *relative entropy actually
erased* — not a bit count. A `CoarseGrainingStep`'s `tauEnt` is the dissipated KL divergence in
nats (H-theorem, `tauEnt_nonneg` derived); converting nats to bits (`/ log 2`) and pricing each bit
at `landauerCost T` recovers exactly the Clausius heat `k_B T · ΔS_rel`. On the computation
`erasureStep` this welds the measure-theoretic KL layer (`ComputationLandauer`) to the
bit-counting layer (`landauerEnergyForBits`) — the two faces of Landauer's principle in the repo
are one identity. -/

section ErasedInformationHeat

open MeasureTheory ProbabilityTheory InformationTheory
open Physlib.Thermodynamics.BoltzmannHTheorem
open Physlib.Thermodynamics.ComputationLandauer
open scoped ENNReal

/-- **[Erased information, priced in bits, is the Clausius heat]** `E(T, ΔS/log 2) = k_B T · ΔS ≥ 0`.
For any coarse-graining step, the dissipated relative entropy `tauEnt` (nats), converted to bits and
priced at the Landauer cost, equals the Clausius heat `k_B T · ΔS_rel` — and the heat is
non-negative by the H-theorem, never by assumption. This is the relative-entropy form of the
Landauer bound, saturated: `ΔQ = β⁻¹ ΔS_rel` with `β = 1/(k_B T)`. -/
theorem coarseGraining_clausius_heat (S : CoarseGrainingStep) (T : ℝ) (hT : 0 ≤ T) :
    landauerEnergyForBits T (S.tauEnt / Real.log 2) = kB * T * S.tauEnt
      ∧ 0 ≤ kB * T * S.tauEnt := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  constructor
  · show S.tauEnt / Real.log 2 * (kB * T * Real.log 2) = kB * T * S.tauEnt
    field_simp
  · exact mul_nonneg (mul_nonneg kB_nonneg hT) S.tauEnt_nonneg

/-- **[The erased-information heat at the modular temperature]** `k_B T_H · ΔS = ℏκ·ΔS/(2πc)`.
At the KMS temperature of the modular flow the Clausius heat of a coarse-graining step is its
dissipated relative entropy in modular quanta — the Boltzmann constant cancels, as in §A. -/
theorem coarseGraining_modular_heat (S : CoarseGrainingStep) (ℏ κ c : ℝ) (hc : c ≠ 0) :
    kB * hawkingTemperature ℏ κ c kB * S.tauEnt =
      ℏ * κ * S.tauEnt / (2 * Real.pi * c) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hkB : kB ≠ 0 := kB_pos.ne'
  rw [hawkingTemperature_def]
  field_simp

/-- **[The computation erasure step's heat is its conditional KL, priced in bits]** on the
`ComputationLandauer` carrier: discarding the input register of a computation `f` dissipates
`entropyProduced` — the coarse-graining conditional KL divergence, the single genuine physical
input — and pricing the erased information in bits at the Landauer cost returns exactly
`k_B T · entropyProduced ≥ 0`. Computability (the kernel of `f`), measure-theoretic relative
entropy, and thermodynamic heat meet in one identity. -/
theorem erasure_heat_priced_in_bits (f : ℕ → ℕ) (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv (μ ⊗ₘ computationKernel f) (ν ⊗ₘ computationKernel (fun _ => 0)) ≠ ∞)
    (T : ℝ) (hT : 0 ≤ T) :
    landauerEnergyForBits T ((erasureStep f μ ν hfin).tauEnt / Real.log 2)
        = kB * T * (erasureStep f μ ν hfin).entropyProduced
      ∧ 0 ≤ kB * T * (erasureStep f μ ν hfin).tauEnt := by
  have h := coarseGraining_clausius_heat (erasureStep f μ ν hfin) T hT
  exact ⟨by rw [h.1, erasureStep_tauEnt_eq_entropyProduced f μ ν hfin], h.2⟩

end ErasedInformationHeat

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil_theorem_intent qtmTrace_erasure_modular_quantum where
  at_level bridge_theorem
  must_mention [qtmLandauerCount, hawkingTemperature, traceLandauerEnergy]

zil attach qtmTrace_erasure_modular_quantum where
  formalizes @ "claim:qtm-trace-landauer-energy-at-modular-temperature-is-measurement-count-times-modular-quantum",
  requires @ "claim:landauer-cost-at-hawking-temperature-is-a-pure-modular-quantum",
  supported_by @ "paper:landauer-1961",
  supported_by @ "paper:bennett-1982-thermodynamics-of-computation",
  supported_by @ "paper:kay-wald-1991-horizon-kms",
  caveat @ "claim:ideal-erasure-count-model-exact-identity-not-a-measured-heat"

zil_theorem_intent horizon_bit_erasure_is_one_bit_entropy where
  at_level bridge_theorem
  must_mention [landauerCost, hawkingTemperature]

zil attach horizon_bit_erasure_is_one_bit_entropy where
  formalizes @ "claim:one-bit-erased-at-horizon-grows-entropy-by-exactly-kb-ln-two",
  requires @ "claim:first-law-of-schwarzschild-mechanics-on-entropic-time-carrier",
  supported_by @ "paper:landauer-1961",
  supported_by @ "paper:bekenstein-1973",
  caveat @ "claim:static-first-law-increment-not-a-dynamical-infall-process",
  caveat @ "epistemic:consistency-identity-forced-by-first-law-hawking-temperature-and-ideal-landauer-definitions-not-an-independent-prediction"

zil attach hawkingBeta_mul_landauerCost where
  formalizes @ "claim:kms-beta-times-one-bit-erasure-heat-equals-boltzmann-log-two",
  requires @ "assumption:nonvanishing-hawking-temperature",
  supported_by @ "paper:landauer-1961",
  caveat @ "claim:clausius-equality-of-the-ideal-bound-not-an-inequality-over-protocols"

zil_theorem_intent neg_log_wedgeModularEigenvalue where
  at_level bridge_theorem
  must_mention [wedgeModularEigenvalue, modularHamEigenvalue]

zil attach neg_log_wedgeModularEigenvalue where
  formalizes @ "claim:modular-hamiltonian-is-minus-log-of-modular-operator",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:single-mode-eigenvalue-not-operator-modular-theory"

zil attach center_subset_wedge_and_causalComplement where
  formalizes @ "claim:wedge-algebra-and-causal-complement-share-the-center-no-total-separation",
  supported_by @ "paper:haag-kastler-algebraic-approach",
  caveat @ "claim:ring-commutant-model-not-a-von-neumann-algebra-split-inclusion"

zil_theorem_intent coarseGraining_clausius_heat where
  at_level bridge_theorem
  must_mention [landauerEnergyForBits, Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep.tauEnt]

zil attach coarseGraining_clausius_heat where
  formalizes @ "claim:erased-relative-entropy-priced-in-bits-is-the-clausius-heat",
  requires @ "claim:h-theorem-derived-nonnegative-dissipated-kl",
  supported_by @ "paper:landauer-1961",
  supported_by @ "paper:bennett-1982-thermodynamics-of-computation",
  caveat @ "claim:saturated-equality-of-the-ideal-bound-not-an-inequality-over-protocols"

zil attach erasure_heat_priced_in_bits where
  formalizes @ "claim:computation-erasure-heat-is-conditional-kl-priced-in-bits",
  requires @ "claim:erased-relative-entropy-priced-in-bits-is-the-clausius-heat",
  requires @ "claim:erasure-dissipation-nonnegative",
  supported_by @ "paper:bennett-1973",
  caveat @ "claim:finite-trace-setting-not-araki-continuum"

zil_file_contract physlib.modularErasureCost where
  promises "Landauer's principle in AQFT form on existing carriers: the one-bit erasure cost at the Kay-Wald KMS temperature of the modular flow is a pure modular quantum (Boltzmann constant cancels), the Clausius product beta times the one-bit heat is exactly k_B log 2, a quantum Turing machine trace pays its measurement count times the modular quantum, the modular Hamiltonian is minus the log of the modular operator at the wedge-eigenvalue level, and the wedge algebra and its causal complement share the full center so local algebras are never totally separate."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.Landauer.landauerCost",
    "lean:Physlib.Thermodynamics.Landauer.qtmLandauerCount",
    "lean:Physlib.Thermodynamics.Landauer.traceLandauerEnergy",
    "lean:Physlib.Relativity.SemiClassical.hawkingTemperature",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon.hawkingBeta",
    "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue",
    "lean:Physlib.QFT.PathIntegral.modularHamEigenvalue",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.wedgeAlgebra"]
  forbids_substitutes ["an operator-level Araki relative entropy claimed from eigenvalue and counting shadows",
    "a von Neumann split-inclusion or type classification claimed from the ring commutant model",
    "a measured erasure heat claimed from the ideal Landauer-count identity"]
  witnessed_by [landauerCost_hawkingTemperature, hawkingBeta_mul_landauerCost,
    qtmTrace_erasure_modular_quantum, wedgeModularEigenvalue_pos,
    neg_log_wedgeModularEigenvalue, center_subset_wedge_and_causalComplement,
    coarseGraining_clausius_heat, coarseGraining_modular_heat, erasure_heat_priced_in_bits,
    horizon_bit_erasure_is_one_bit_entropy]

/- ZIL-END -/

end Physlib.Thermodynamics.ModularErasureCost

end

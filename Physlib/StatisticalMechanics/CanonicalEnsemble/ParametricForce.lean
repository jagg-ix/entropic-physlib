/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# Generalized force of a parametric canonical ensemble

The exact derivative identities along an external control parameter for the
finite canonical ensemble at fixed real inverse temperature, extending the
`BetaReal` family of `Physlib.StatisticalMechanics.CanonicalEnsemble.Finite`
from the inverse-temperature axis to the control-parameter axis:

* **Parametric partition function.** With energy levels `E lam i`
  differentiable in the parameter, the partition function
  `Z(lam) = ∑ i exp (-b * E lam i)` is differentiable with level-resolved
  derivative (`hasDerivAt_parametric_partition`).
* **Hellmann-Feynman.** The log-partition derivative is the Gibbs-weighted
  mean of level derivatives, `d(log Z) = -b <dE>`
  (`hasDerivAt_log_parametric_partition`), and the free-energy derivative is
  that mean itself, `dF = <dE>` (`hasDerivAt_parametric_freeEnergy`) - the
  Hellmann-Feynman theorem for the canonical free energy: the generalized
  force `-dF` is `-<dE>`.
* **Energetic-entropic force decomposition.** From the exact identity
  `F = U - S/(kB b)` (`freeEnergyBetaReal_eq`, a rearrangement of the finite
  canonical entropy identity), differentiability of mean energy and entropy
  gives `dS = kB b (dU - <dE>)`
  (`parametric_entropy_energy_force_decomposition`) - the exact microscopic
  split `T dS = dU - <dE>` of the free-energy force into an energetic and an
  entropic component.
* **The purely entropic force.** When the mean energy is stationary in the
  parameter, the generalized force is temperature times the entropy
  derivative, `-<dE> = dS/(kB b)`
  (`entropic_force_of_stationary_mean_energy`) - the exact ensemble form of
  an entropic force, the microscopic back-end of the finite-difference
  `verlindeEntropicForce = T ΔS/Δx` of
  `Physlib.Thermodynamics.VerlindeEntropicForce`.

**Honest boundary.** Finite state spaces, fixed real inverse temperature, and
hypotheses of differentiability where used; no continuum ensembles, no
temperature-axis statements (those live in
`Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas`), and no claim that
any particular physical force is purely entropic - only the exact identities.
-/

set_option autoImplicit false

@[expose] public section

namespace CanonicalEnsemble

open Real Constants

variable {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Nonempty ι]

/-- **Helmholtz free energy on the real inverse-temperature axis**:
`F(b) = -(1/b) * log Z(b)` with `Z` the finite-sum partition function - the
`BetaReal` counterpart of `helmholtzFreeEnergy`. -/
noncomputable def freeEnergyBetaReal (𝓒 : CanonicalEnsemble ι) (b : ℝ) : ℝ :=
  -(1 / b) * Real.log (𝓒.mathematicalPartitionFunctionBetaReal b)

/-- **The finite canonical free energy is mean energy minus temperature times
entropy**: `F = U - S/(kB b)` - the free-energy rearrangement of the finite
canonical entropy identity `S = kB (b U + log Z)`. -/
theorem freeEnergyBetaReal_eq (𝓒 : CanonicalEnsemble ι) {b : ℝ} (hb : b ≠ 0) :
    𝓒.freeEnergyBetaReal b =
      𝓒.meanEnergyBetaReal b - 𝓒.shannonEntropyBetaReal b / (kB * b) := by
  rw [𝓒.shannonEntropyBetaReal_eq b]
  unfold freeEnergyBetaReal
  have hkB : (kB : ℝ) ≠ 0 := kB_ne_zero
  field_simp
  ring

/-- **Differentiability of the parametric partition function**: with each
energy level differentiable in the control parameter, the partition function
at fixed inverse temperature is differentiable with the level-resolved
derivative `∑ i, -b * E' i * exp (-b * E lam i)`. -/
@[zil_level physical_theorem]
theorem hasDerivAt_parametric_partition (b : ℝ) (E : ℝ → ι → ℝ) (E' : ι → ℝ)
    (lam : ℝ) (hE : ∀ i, HasDerivAt (fun l => E l i) (E' i) lam) :
    HasDerivAt
      (fun l => (ofFiniteEnergy (E l)).mathematicalPartitionFunctionBetaReal b)
      (∑ i, -b * E' i * Real.exp (-b * E lam i)) lam := by
  have h : ∀ i : ι, HasDerivAt (fun l => Real.exp (-b * E l i))
      (-b * E' i * Real.exp (-b * E lam i)) lam := fun i => by
    have h1 : HasDerivAt (fun l => -b * E l i) (-b * E' i) lam :=
      (hE i).const_mul (-b)
    simpa [mul_comm] using h1.exp
  show HasDerivAt (fun l => ∑ i, Real.exp (-b * E l i)) _ lam
  exact HasDerivAt.fun_sum fun i _ => h i

/-- **Hellmann-Feynman for the log-partition function**: the log-partition
derivative along the control parameter is `-b` times the Gibbs-weighted mean
of the level derivatives. -/
@[zil_level physical_theorem]
theorem hasDerivAt_log_parametric_partition (b : ℝ) (E : ℝ → ι → ℝ)
    (E' : ι → ℝ) (lam : ℝ)
    (hE : ∀ i, HasDerivAt (fun l => E l i) (E' i) lam) :
    HasDerivAt
      (fun l =>
        Real.log ((ofFiniteEnergy (E l)).mathematicalPartitionFunctionBetaReal b))
      (-b * ∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i)
      lam := by
  have hZ := hasDerivAt_parametric_partition b E E' lam hE
  have hZpos := (ofFiniteEnergy (E lam)).mathematicalPartitionFunctionBetaReal_pos b
  have hZne := hZpos.ne'
  have hlog := hZ.log hZne
  have halg :
      (∑ i, -b * E' i * Real.exp (-b * E lam i)) /
          (ofFiniteEnergy (E lam)).mathematicalPartitionFunctionBetaReal b =
        -b * ∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i := by
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [probabilityBetaReal]
    show -b * E' i * Real.exp (-b * E lam i) /
        (ofFiniteEnergy (E lam)).mathematicalPartitionFunctionBetaReal b =
      -b * (Real.exp (-b * E lam i) /
        (ofFiniteEnergy (E lam)).mathematicalPartitionFunctionBetaReal b * E' i)
    field_simp
  exact halg ▸ hlog

/-- **Hellmann-Feynman for the parametric free energy**: at fixed inverse
temperature the free-energy derivative along the control parameter is the
Gibbs-weighted mean of the level derivatives, `dF = <dE>`; the generalized
force `-dF` is minus that mean. -/
@[zil_level bridge_theorem]
theorem hasDerivAt_parametric_freeEnergy {b : ℝ} (hb : b ≠ 0)
    (E : ℝ → ι → ℝ) (E' : ι → ℝ) (lam : ℝ)
    (hE : ∀ i, HasDerivAt (fun l => E l i) (E' i) lam) :
    HasDerivAt (fun l => (ofFiniteEnergy (E l)).freeEnergyBetaReal b)
      (∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i) lam := by
  have hlog := hasDerivAt_log_parametric_partition b E E' lam hE
  have hmul := hlog.const_mul (-(1 / b))
  have hval : -(1 / b) *
      (-b * ∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i) =
        ∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i := by
    field_simp
  show HasDerivAt
    (fun l =>
      -(1 / b) *
        Real.log ((ofFiniteEnergy (E l)).mathematicalPartitionFunctionBetaReal b))
    _ lam
  exact hval ▸ hmul

/-- **Energetic-entropic decomposition of the generalized force**: with the
mean energy and the entropy differentiable along the control parameter, the
entropy derivative is `kB b` times the gap between the mean-energy derivative
and the Gibbs-weighted level derivative - the exact microscopic split
`T dS = dU - <dE>` of the free-energy force into energetic and entropic
components. -/
@[zil_level bridge_theorem]
theorem parametric_entropy_energy_force_decomposition {b : ℝ} (hb : b ≠ 0)
    (E : ℝ → ι → ℝ) (E' : ι → ℝ) (lam u' s' : ℝ)
    (hE : ∀ i, HasDerivAt (fun l => E l i) (E' i) lam)
    (hU : HasDerivAt (fun l => (ofFiniteEnergy (E l)).meanEnergyBetaReal b) u' lam)
    (hS : HasDerivAt
      (fun l => (ofFiniteEnergy (E l)).shannonEntropyBetaReal b) s' lam) :
    s' = kB * b *
      (u' - ∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i) := by
  have hF := hasDerivAt_parametric_freeEnergy hb E E' lam hE
  have hkb : kB * b ≠ 0 := mul_ne_zero kB_ne_zero hb
  have hF2 : HasDerivAt (fun l => (ofFiniteEnergy (E l)).freeEnergyBetaReal b)
      (u' - s' / (kB * b)) lam := by
    have hfun : (fun l => (ofFiniteEnergy (E l)).freeEnergyBetaReal b)
        = fun l => (ofFiniteEnergy (E l)).meanEnergyBetaReal b
            - (ofFiniteEnergy (E l)).shannonEntropyBetaReal b / (kB * b) := by
      funext l
      exact (ofFiniteEnergy (E l)).freeEnergyBetaReal_eq hb
    rw [hfun]
    exact hU.sub (hS.div_const (kB * b))
  have hval := hF.unique hF2
  have h2 : s' / (kB * b) =
      u' - ∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i := by
    linarith
  calc s' = s' / (kB * b) * (kB * b) := (div_mul_cancel₀ s' hkb).symm
    _ = (u' - ∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i) *
        (kB * b) := by rw [h2]
    _ = kB * b *
        (u' - ∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i) := by
      ring

/-- **The purely entropic force**: when the mean energy is stationary in the
control parameter, the generalized force `-dF = -<dE>` equals the temperature
times the entropy derivative, `dS/(kB b)` - the exact finite-ensemble form of
an entropic force. -/
@[zil_level bridge_theorem]
theorem entropic_force_of_stationary_mean_energy {b : ℝ} (hb : b ≠ 0)
    (E : ℝ → ι → ℝ) (E' : ι → ℝ) (lam s' : ℝ)
    (hE : ∀ i, HasDerivAt (fun l => E l i) (E' i) lam)
    (hU : HasDerivAt (fun l => (ofFiniteEnergy (E l)).meanEnergyBetaReal b) 0 lam)
    (hS : HasDerivAt
      (fun l => (ofFiniteEnergy (E l)).shannonEntropyBetaReal b) s' lam) :
    -(∑ i, (ofFiniteEnergy (E lam)).probabilityBetaReal b i * E' i)
      = s' / (kB * b) := by
  have hdec := parametric_entropy_energy_force_decomposition hb E E' lam 0 s' hE hU hS
  have hkb : kB * b ≠ 0 := mul_ne_zero kB_ne_zero hb
  rw [hdec, mul_div_cancel_left₀ _ hkb]
  ring

end CanonicalEnsemble

end

open CanonicalEnsemble in
#physlib_axiom_clean_all [
  freeEnergyBetaReal_eq,
  hasDerivAt_parametric_partition,
  hasDerivAt_log_parametric_partition,
  hasDerivAt_parametric_freeEnergy,
  parametric_entropy_energy_force_decomposition,
  entropic_force_of_stationary_mean_energy ]

open CanonicalEnsemble in
#physlib_non_vacuous_all [
  freeEnergyBetaReal_eq,
  hasDerivAt_parametric_partition,
  hasDerivAt_log_parametric_partition,
  hasDerivAt_parametric_freeEnergy,
  parametric_entropy_energy_force_decomposition,
  entropic_force_of_stationary_mean_energy ]

/- ZIL-BEGIN -/

zil attach CanonicalEnsemble.hasDerivAt_parametric_partition where
  formalizes @ "claim:the-parametric-finite-partition-function-differentiates-level-by-level",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:CanonicalEnsemble.mathematicalPartitionFunctionBetaReal"

zil attach CanonicalEnsemble.hasDerivAt_log_parametric_partition where
  formalizes @ "claim:the-log-partition-derivative-along-a-control-parameter-is-minus-beta-times-the-gibbs-mean-level-derivative",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:feynman-1939-forces-in-molecules"

zil attach CanonicalEnsemble.hasDerivAt_parametric_freeEnergy where
  formalizes @ "claim:hellmann-feynman-for-the-canonical-free-energy-the-generalized-force-is-the-gibbs-mean-level-force",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:feynman-1939-forces-in-molecules",
  supported_by @ "lean:CanonicalEnsemble.probabilityBetaReal"

zil attach CanonicalEnsemble.parametric_entropy_energy_force_decomposition where
  formalizes @ "claim:the-generalized-force-splits-exactly-into-energetic-and-entropic-components-t-ds-equals-du-minus-mean-de",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:CanonicalEnsemble.shannonEntropyBetaReal_eq",
  caveat @ "claim:differentiability-of-mean-energy-and-entropy-along-the-parameter-is-a-hypothesis-not-derived-here"

zil attach CanonicalEnsemble.entropic_force_of_stationary_mean_energy where
  formalizes @ "claim:with-stationary-mean-energy-the-generalized-force-is-temperature-times-the-entropy-derivative",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:verlinde-2011-on-the-origin-of-gravity-and-the-laws-of-newton",
  supported_by @ "lean:Physlib.Thermodynamics.verlindeEntropicForce",
  caveat @ "claim:an-exact-ensemble-identity-no-claim-that-any-particular-physical-force-is-purely-entropic"

zil_file_contract physlib.canonicalEnsembleParametricForce where
  promises "The control-parameter derivative identities of the finite canonical ensemble at fixed real inverse temperature: level-resolved differentiability of the partition function, the Hellmann-Feynman identities for the log-partition function and the free energy, the exact energetic-entropic decomposition T dS = dU minus the Gibbs-mean level derivative, and the purely entropic force identity under stationary mean energy."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:CanonicalEnsemble.mathematicalPartitionFunctionBetaReal",
    "lean:CanonicalEnsemble.probabilityBetaReal",
    "lean:CanonicalEnsemble.shannonEntropyBetaReal_eq",
    "lean:HasDerivAt", "lean:Constants.kB"]
  forbids_substitutes ["continuum or infinite-dimensional ensembles",
    "temperature-axis derivative statements already provided by the ensemble lemma layer",
    "a claim that a particular physical force is purely entropic"]
  witnessed_by [
    CanonicalEnsemble.hasDerivAt_parametric_partition,
    CanonicalEnsemble.hasDerivAt_log_parametric_partition,
    CanonicalEnsemble.hasDerivAt_parametric_freeEnergy,
    CanonicalEnsemble.parametric_entropy_energy_force_decomposition,
    CanonicalEnsemble.entropic_force_of_stationary_mean_energy ]

/- ZIL-END -/

#zil_formalization_lint physlib.canonicalEnsembleParametricForce

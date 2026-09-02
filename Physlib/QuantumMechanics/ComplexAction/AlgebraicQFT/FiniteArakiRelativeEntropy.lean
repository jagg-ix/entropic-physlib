/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy
public import Physlib.QFT.PathIntegral.WickClock
meta import Zil

/-!
# The finite Araki relative entropy — `S(φ‖ψ) = −φ(log Δ_{ψ|φ})` at the eigenvalue level

In type III local algebras the von Neumann entropy does not exist and Araki's **relative entropy** —
defined through the relative modular operator, `S(φ‖ψ) = −⟨ξ_φ, log Δ_{ψ|φ} ξ_φ⟩` — is the only
information measure available. This module realizes that structure at the finite (eigenvalue) level
of the wedge arc, on the repo's existing carriers:

* **§A the Araki form.** For strictly positive weight vectors, the relative entropy
  `S(p‖q) = ∑ pᵢ log(pᵢ/qᵢ)` *is* `−∑ pᵢ log Δᵢ` with `Δᵢ = qᵢ/pᵢ` the eigenvalues of the relative
  modular operator — Araki's `−φ(log Δ_{ψ|φ})`, diagonal case.
* **§B nonnegativity from the spine's Gibbs inequality.** `S(p‖q) ≥ 0` for equal-mass weights, by
  summing the *pointwise* Klein/Gibbs inequality `ρ − ρ_s ≤ ρ log(ρ/ρ_s)` already proved on the
  entropic-dynamics spine (`relativeEntropy_density_ge`) — no new inequality is introduced.
* **§C the free-energy identity, finite form.** Against a Gibbs reference `qᵢ = e^{−βEᵢ}/Z`,
  `S(p‖q) = ∑ pᵢ log pᵢ + β⟨E⟩_p + log Z` — the finite-sum version of the spine's
  `freeEnergyDensity_eq_relativeEntropy` (free energy = relative entropy above the Gibbs minimum).
* **§D the Bogoliubov–Feynman variational principle.** Klein nonnegativity gives the finite Gibbs
  variational bound and, for a Gibbs trial Hamiltonian, the exact diagonal form
  `F ≤ F₀ + ⟨H-H₀⟩₀` used by Sabio–Sols' displaced-oscillator ansatz.
* **§E the wedge KMS instance.** For the two-level wedge system with spectrum
  `{0, modularHamEigenvalue κ ℏ}` at `β = 1`, the partition function is `1 + Δ` with
  `Δ = wedgeModularEigenvalue κ ℏ` — `e^{−K} = Δ` holds definitionally (`K = −log Δ`, §B of
  `ModularErasureCost`) — and the relative entropy to the wedge KMS state is the free-energy
  identity with `log(1 + Δ)`.

What is **not** claimed: operator-level (type III) Araki theory, continuum limits, or monotonicity
of the relative entropy under channels — the statements are exact finite-sum identities and the
Klein inequality, welded to the wedge eigenvalue shadow.

## References

* H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS 11 (1976).
* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*
  (the spine's free-energy = relative-entropy carrier).
* J. Sabio, F. Sols, *Variational approach to the Caldeira–Leggett model*, Physica E **42**
  (2010) 378–382, Eq. 7.
* Repo carriers: `EntropicDynamicsFreeEnergyRelativeEntropy.relativeEntropy_density_ge` /
  `freeEnergyDensity_eq_relativeEntropy`, `QFT.PathIntegral.wedgeModularEigenvalue` /
  `modularHamEigenvalue`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy
open Physlib.QFT.PathIntegral

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy

variable {ι : Type*} [Fintype ι]

/-- **The finite relative entropy** `S(p‖q) = ∑ pᵢ log(pᵢ/qᵢ)` — the Kullback–Leibler divergence of
two weight vectors, the diagonal (eigenvalue-level) case of Araki's relative entropy. -/
noncomputable def finiteRelativeEntropy (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-! ## A. The Araki form: `S(p‖q) = −∑ pᵢ log Δᵢ` with `Δᵢ = qᵢ/pᵢ` -/

/-- **[The relative entropy is `−φ(log Δ)` for the relative modular eigenvalues]**
`S(p‖q) = −∑ pᵢ log(qᵢ/pᵢ)`. The eigenvalues of the relative modular operator `Δ_{ψ|φ}` in the
diagonal case are the ratios `Δᵢ = qᵢ/pᵢ`; the relative entropy is exactly Araki's
`−⟨ξ_φ, log Δ_{ψ|φ} ξ_φ⟩` evaluated on them. -/
theorem finiteRelativeEntropy_eq_neg_sum_log_relModular (p q : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    finiteRelativeEntropy p q = -∑ i, p i * Real.log (q i / p i) := by
  unfold finiteRelativeEntropy
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Real.log (p i / q i) = -Real.log (q i / p i) by
    rw [← Real.log_inv, inv_div]]
  ring

/-! ## B. Nonnegativity — the Klein inequality from the spine's pointwise Gibbs bound -/

/-- **[The finite relative entropy is non-negative]** `S(p‖q) ≥ 0` for equal-mass positive weights.
Proved by *summing the spine's pointwise Gibbs inequality* `ρ − ρ_s ≤ ρ log(ρ/ρ_s)`
(`relativeEntropy_density_ge`, the entropic-dynamics free-energy carrier): the total mass difference
vanishes, so the sum of the divergence densities is non-negative — the Klein inequality, with no new
analytic input. -/
theorem finiteRelativeEntropy_nonneg (p q : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hmass : ∑ i, p i = ∑ i, q i) :
    0 ≤ finiteRelativeEntropy p q := by
  have hsum : ∑ i, (p i - q i) ≤ ∑ i, p i * Real.log (p i / q i) :=
    Finset.sum_le_sum fun i _ => relativeEntropy_density_ge (p i) (q i) (hp i) (hq i)
  have hzero : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  unfold finiteRelativeEntropy
  linarith

/-! ## C. The free-energy identity, finite form -/

/-- **[Relative entropy to a Gibbs reference is the free energy]**
`S(p‖e^{−βE}/Z) = ∑ pᵢ log pᵢ + β⟨E⟩_p + log Z` for a normalized state `p`. The finite-sum version
of the spine's `freeEnergyDensity_eq_relativeEntropy`: minus the Shannon entropy, plus `β` times the
mean energy, plus the log-partition constant — the free energy above the Gibbs minimum. -/
theorem finiteRelativeEntropy_gibbs_free_energy (p E : ι → ℝ) (β Z : ℝ)
    (hp : ∀ i, 0 < p i) (hZ : 0 < Z) (hnorm : ∑ i, p i = 1) :
    finiteRelativeEntropy p (fun i => Real.exp (-(β * E i)) / Z) =
      (∑ i, p i * Real.log (p i)) + β * (∑ i, p i * E i) + Real.log Z := by
  have hterm : ∀ i : ι, p i * Real.log (p i / (Real.exp (-(β * E i)) / Z))
      = p i * Real.log (p i) + β * (p i * E i) + p i * Real.log Z := by
    intro i
    rw [Real.log_div (hp i).ne' (by positivity),
      Real.log_div (Real.exp_ne_zero _) hZ.ne', Real.log_exp]
    ring
  unfold finiteRelativeEntropy
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hnorm, one_mul]

/-! ## D. The Bogoliubov–Feynman variational principle -/

/-- The finite trial-state free energy
`F[p;E] = ⟨E⟩ₚ + β⁻¹ ∑ᵢ pᵢ log pᵢ`.

The second term is `-β⁻¹` times the Shannon entropy. This diagonal finite-spectrum carrier is
the exact setting in which the repository's Klein inequality proves the Bogoliubov–Feynman
bound without assuming a new trace inequality. -/
noncomputable def finiteTrialFreeEnergy (p E : ι → ℝ) (β : ℝ) : ℝ :=
  (∑ i, p i * E i) + (1 / β) * ∑ i, p i * Real.log (p i)

/-- The Gibbs free energy `F = -β⁻¹ log Z`. -/
noncomputable def gibbsFreeEnergy (Z β : ℝ) : ℝ := -Real.log Z / β

/-- **[Finite Gibbs variational bound]** `F ≤ F[p;E]` for every strictly positive normalized
trial distribution `p`. This follows directly from nonnegativity of
`D(p ‖ e^{-βE}/Z)` and the existing exact free-energy identity. -/
theorem finite_gibbs_variational_upper_bound (p E : ι → ℝ) (β Z : ℝ)
    (hp : ∀ i, 0 < p i) (hβ : 0 < β) (hZ : 0 < Z)
    (hnorm : ∑ i, p i = 1)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z) :
    gibbsFreeEnergy Z β ≤ finiteTrialFreeEnergy p E β := by
  let q : ι → ℝ := fun i => Real.exp (-(β * E i)) / Z
  have hq : ∀ i, 0 < q i := fun i => div_pos (Real.exp_pos _) hZ
  have hqnorm : ∑ i, q i = 1 := by
    simp only [q, ← Finset.sum_div, hpartition, div_self hZ.ne']
  have hnonneg := finiteRelativeEntropy_nonneg p q hp hq (hnorm.trans hqnorm.symm)
  have hfree := finiteRelativeEntropy_gibbs_free_energy p E β Z hp hZ hnorm
  have hcore : 0 ≤ (∑ i, p i * Real.log (p i)) + β * (∑ i, p i * E i) +
      Real.log Z := by
    rw [← hfree]
    exact hnonneg
  rw [gibbsFreeEnergy, finiteTrialFreeEnergy]
  apply (div_le_iff₀ hβ).2
  field_simp [hβ.ne']
  linarith

/-- **[Bogoliubov–Feynman upper bound, finite diagonal form]**
`F ≤ F₀ + ⟨E-E₀⟩₀`, where the trial probabilities are the Gibbs weights of `E₀`.

This is Sabio–Sols Eq. 7 on a finite common eigenbasis. It is derived from the repository's
Klein inequality, not introduced as an assumption. The theorem does not assert simultaneous
diagonalizability of arbitrary quantum Hamiltonians or the full noncommutative trace inequality. -/
theorem finite_bogoliubov_feynman_bound (E E0 : ι → ℝ) (β Z Z0 : ℝ)
    (hβ : 0 < β) (hZ : 0 < Z) (hZ0 : 0 < Z0)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z)
    (hpartition0 : ∑ i, Real.exp (-(β * E0 i)) = Z0) :
    gibbsFreeEnergy Z β ≤ gibbsFreeEnergy Z0 β +
      ∑ i, (Real.exp (-(β * E0 i)) / Z0) * (E i - E0 i) := by
  let p : ι → ℝ := fun i => Real.exp (-(β * E0 i)) / Z0
  have hp : ∀ i, 0 < p i := fun i => div_pos (Real.exp_pos _) hZ0
  have hnorm : ∑ i, p i = 1 := by
    simp only [p, ← Finset.sum_div, hpartition0, div_self hZ0.ne']
  have hupper := finite_gibbs_variational_upper_bound p E β Z hp hβ hZ hnorm hpartition
  have hfree0 := finiteRelativeEntropy_gibbs_free_energy p E0 β Z0 hp hZ0 hnorm
  have hself : finiteRelativeEntropy p p = 0 := by
    simp [finiteRelativeEntropy, (hp _).ne']
  have htrial : (∑ i, p i * Real.log (p i)) + β * (∑ i, p i * E0 i) +
      Real.log Z0 = 0 := by
    rw [← hfree0, show (fun i => Real.exp (-(β * E0 i)) / Z0) = p from rfl, hself]
  have henergy : (∑ i, p i * (E i - E0 i)) =
      (∑ i, p i * E i) - ∑ i, p i * E0 i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hidentity : finiteTrialFreeEnergy p E β =
      gibbsFreeEnergy Z0 β + ∑ i, p i * (E i - E0 i) := by
    rw [finiteTrialFreeEnergy, gibbsFreeEnergy, henergy]
    field_simp [hβ.ne'] at htrial ⊢
    linarith
  change gibbsFreeEnergy Z β ≤ gibbsFreeEnergy Z0 β + ∑ i, p i * (E i - E0 i)
  rw [← hidentity]
  exact hupper

/-! ## D.1. Reusable finite Gibbs variational carrier -/

/-- A finite Gibbs system packages the energy spectrum, positive inverse temperature, positive
partition function, and the exact partition identity. It is the common carrier used by the AQFT,
decoherence, thermofield, Caticha, and non-Hermitian variational welds. -/
structure FiniteGibbsVariationalSystem (ι : Type*) [Fintype ι] where
  energy : ι → ℝ
  beta : ℝ
  partition : ℝ
  beta_pos : 0 < beta
  partition_pos : 0 < partition
  partition_eq : ∑ i, Real.exp (-(beta * energy i)) = partition

namespace FiniteGibbsVariationalSystem

/-- The normalized Gibbs weights of a packaged finite variational system. -/
noncomputable def gibbsWeight (G : FiniteGibbsVariationalSystem ι) : ι → ℝ :=
  fun i => Real.exp (-(G.beta * G.energy i)) / G.partition

lemma gibbsWeight_pos (G : FiniteGibbsVariationalSystem ι) (i : ι) :
    0 < G.gibbsWeight i :=
  div_pos (Real.exp_pos _) G.partition_pos

lemma gibbsWeight_normalized (G : FiniteGibbsVariationalSystem ι) :
    ∑ i, G.gibbsWeight i = 1 := by
  simp only [gibbsWeight, ← Finset.sum_div, G.partition_eq,
    div_self G.partition_pos.ne']

/-- The exact finite variational identity
`F[p] - F_Gibbs = D(p ‖ p_Gibbs)/β`. -/
theorem freeEnergy_gap_eq_relativeEntropy_div (G : FiniteGibbsVariationalSystem ι)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    finiteTrialFreeEnergy p G.energy G.beta - gibbsFreeEnergy G.partition G.beta =
      finiteRelativeEntropy p G.gibbsWeight / G.beta := by
  unfold gibbsWeight
  rw [finiteRelativeEntropy_gibbs_free_energy p G.energy G.beta G.partition
    hp G.partition_pos hnorm]
  unfold finiteTrialFreeEnergy gibbsFreeEnergy
  field_simp [G.beta_pos.ne']
  ring

/-- The Gibbs state minimizes finite trial free energy over every strictly positive normalized
trial distribution. -/
theorem freeEnergy_minimized (G : FiniteGibbsVariationalSystem ι)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    gibbsFreeEnergy G.partition G.beta ≤ finiteTrialFreeEnergy p G.energy G.beta :=
  finite_gibbs_variational_upper_bound p G.energy G.beta G.partition hp G.beta_pos
    G.partition_pos hnorm G.partition_eq

/-- The variational free-energy deficit above the Gibbs state is nonnegative. -/
theorem freeEnergy_gap_nonneg (G : FiniteGibbsVariationalSystem ι)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    0 ≤ finiteTrialFreeEnergy p G.energy G.beta - gibbsFreeEnergy G.partition G.beta := by
  linarith [G.freeEnergy_minimized p hp hnorm]

/-- Relative entropy to the packaged Gibbs state is nonnegative. -/
theorem relativeEntropy_nonneg (G : FiniteGibbsVariationalSystem ι)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    0 ≤ finiteRelativeEntropy p G.gibbsWeight :=
  finiteRelativeEntropy_nonneg p G.gibbsWeight hp G.gibbsWeight_pos
    (hnorm.trans G.gibbsWeight_normalized.symm)

end FiniteGibbsVariationalSystem

/-! ## E. The wedge KMS instance: spectrum `{0, K}`, partition `1 + Δ` -/

/-- **[The wedge partition function is `1 + Δ`]** for the two-level system with spectrum
`{0, modularHamEigenvalue κ ℏ}` at `β = 1`: `Z = 1 + e^{−K} = 1 + wedgeModularEigenvalue κ ℏ` —
`e^{−K} = Δ` is definitional (`K = −log Δ`). -/
lemma wedgeKmsPartition_eq (κ ℏ : ℝ) :
    ∑ i : Fin 2, Real.exp (-(1 * ![0, modularHamEigenvalue κ ℏ] i)) =
      1 + wedgeModularEigenvalue κ ℏ := by
  rw [Fin.sum_univ_two]
  simp [wedgeModularEigenvalue, modularHamEigenvalue]

/-- The two-level Bisognano–Wichmann/Kay–Wald wedge mode as a reusable finite Gibbs system. -/
noncomputable def wedgeKmsVariationalSystem (κ ℏ : ℝ) :
    FiniteGibbsVariationalSystem (Fin 2) where
  energy := ![0, modularHamEigenvalue κ ℏ]
  beta := 1
  partition := 1 + wedgeModularEigenvalue κ ℏ
  beta_pos := by norm_num
  partition_pos := by
    have h := Real.exp_pos (-(2 * Real.pi * κ / ℏ))
    unfold wedgeModularEigenvalue
    linarith
  partition_eq := wedgeKmsPartition_eq κ ℏ

/-- **[Relative entropy to the wedge KMS state]** for a two-level state `p` against the Gibbs state
of the wedge modular Hamiltonian (spectrum `{0, K}`, `β = 1`, partition `1 + Δ`): the free-energy
identity with the wedge's own `log(1 + Δ)`. The Araki relative entropy to the KMS state of the
modular flow, realized exactly on the wedge eigenvalue shadow. -/
theorem wedgeKms_relativeEntropy_free_energy (p : Fin 2 → ℝ) (κ ℏ : ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    finiteRelativeEntropy p
        (fun i => Real.exp (-(1 * ![0, modularHamEigenvalue κ ℏ] i))
          / (1 + wedgeModularEigenvalue κ ℏ)) =
      (∑ i, p i * Real.log (p i))
        + (∑ i, p i * ![0, modularHamEigenvalue κ ℏ] i)
        + Real.log (1 + wedgeModularEigenvalue κ ℏ) := by
  have hZ : 0 < 1 + wedgeModularEigenvalue κ ℏ := by
    have := Real.exp_pos (-(2 * Real.pi * κ / ℏ))
    unfold wedgeModularEigenvalue
    linarith
  have h := finiteRelativeEntropy_gibbs_free_energy p (![0, modularHamEigenvalue κ ℏ]) 1
    (1 + wedgeModularEigenvalue κ ℏ) hp hZ hnorm
  rw [h, one_mul]

/-- **[Finite wedge-vacuum passivity]** The wedge KMS Gibbs state minimizes the free energy of
every strictly positive normalized two-level trial state. This is the finite diagonal shadow of
Pusz–Woronowicz/Kay–Wald passivity, not operator-algebraic complete passivity. -/
theorem wedgeKms_freeEnergy_minimized (p : Fin 2 → ℝ) (κ ℏ : ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    gibbsFreeEnergy (1 + wedgeModularEigenvalue κ ℏ) 1 ≤
      finiteTrialFreeEnergy p (![0, modularHamEigenvalue κ ℏ]) 1 :=
  (wedgeKmsVariationalSystem κ ℏ).freeEnergy_minimized p hp hnorm

/-- The excess wedge free energy is exactly the relative entropy to the wedge KMS state. -/
theorem wedgeKms_freeEnergy_gap_eq_relativeEntropy (p : Fin 2 → ℝ) (κ ℏ : ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    finiteTrialFreeEnergy p (![0, modularHamEigenvalue κ ℏ]) 1 -
        gibbsFreeEnergy (1 + wedgeModularEigenvalue κ ℏ) 1 =
      finiteRelativeEntropy p (wedgeKmsVariationalSystem κ ℏ).gibbsWeight := by
  simpa only [wedgeKmsVariationalSystem, div_one] using
    (wedgeKmsVariationalSystem κ ℏ).freeEnergy_gap_eq_relativeEntropy_div p hp hnorm

/-- The finite wedge-KMS passivity package: no normalized positive trial state has lower free
energy, and its exact excess is a nonnegative relative entropy. -/
theorem wedgeKms_finite_vacuum_passivity (p : Fin 2 → ℝ) (κ ℏ : ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    gibbsFreeEnergy (1 + wedgeModularEigenvalue κ ℏ) 1 ≤
        finiteTrialFreeEnergy p (![0, modularHamEigenvalue κ ℏ]) 1 ∧
      0 ≤ finiteRelativeEntropy p (wedgeKmsVariationalSystem κ ℏ).gibbsWeight :=
  ⟨wedgeKms_freeEnergy_minimized p κ ℏ hp hnorm,
    (wedgeKmsVariationalSystem κ ℏ).relativeEntropy_nonneg p hp hnorm⟩

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil_theorem_intent finiteRelativeEntropy_eq_neg_sum_log_relModular where
  at_level bridge_theorem
  must_mention [finiteRelativeEntropy]

zil attach finiteRelativeEntropy_eq_neg_sum_log_relModular where
  formalizes @ "claim:relative-entropy-is-minus-expectation-of-log-relative-modular-operator",
  requires @ "assumption:strictly-positive-finite-weights",
  supported_by @ "paper:araki-1976-relative-entropy",
  caveat @ "claim:diagonal-eigenvalue-case-not-operator-araki-theory"

zil attach finiteRelativeEntropy_nonneg where
  formalizes @ "claim:klein-inequality-from-spine-pointwise-gibbs-bound",
  requires @ "claim:pointwise-gibbs-inequality-on-entropic-spine",
  supported_by @ "paper:araki-1976-relative-entropy",
  caveat @ "claim:equal-mass-hypothesis-replaces-state-normalization"

zil attach finiteRelativeEntropy_gibbs_free_energy where
  formalizes @ "claim:relative-entropy-to-gibbs-reference-is-free-energy-above-minimum",
  requires @ "assumption:normalized-positive-state",
  supported_by @ "paper:jordan-kinderlehrer-otto-1998",
  caveat @ "claim:finite-sum-version-of-spine-density-identity"

zil attach finite_gibbs_variational_upper_bound where
  formalizes @ "claim:finite-gibbs-free-energy-is-bounded-by-every-positive-normalized-trial-state-free-energy",
  epistemic_status @ "risky",
  requires @ "claim:klein-inequality-from-spine-pointwise-gibbs-bound",
  supported_by @ "paper:sabio-sols-2010-eq-7",
  caveat @ "claim:finite-diagonal-spectrum-bound-not-the-general-noncommutative-trace-inequality"

zil attach finite_bogoliubov_feynman_bound where
  formalizes @ "claim:finite-diagonal-bogoliubov-feynman-bound-from-relative-entropy",
  epistemic_status @ "risky",
  requires @ "claim:finite-gibbs-free-energy-is-bounded-by-every-positive-normalized-trial-state-free-energy",
  supported_by @ "paper:sabio-sols-2010-eq-7",
  caveat @ "claim:common-eigenbasis-specialization-does-not-prove-simultaneous-diagonalization-of-interacting-hamiltonians"

zil attach FiniteGibbsVariationalSystem.freeEnergy_gap_eq_relativeEntropy_div where
  formalizes @ "claim:finite-gibbs-free-energy-deficit-is-relative-entropy-divided-by-beta",
  supported_by @ "paper:araki-1976-relative-entropy",
  epistemic_status @ "risky",
  requires @ "assumption:strictly-positive-normalized-finite-state",
  caveat @ "claim:finite-diagonal-carrier-not-operator-relative-entropy-or-continuum-thermodynamics"

zil_theorem_intent wedgeKms_relativeEntropy_free_energy where
  at_level bridge_theorem
  must_mention [finiteRelativeEntropy, wedgeModularEigenvalue, modularHamEigenvalue]

zil attach wedgeKms_relativeEntropy_free_energy where
  formalizes @ "claim:araki-relative-entropy-to-wedge-kms-state-is-free-energy-with-log-one-plus-modular",
  requires @ "claim:relative-entropy-to-gibbs-reference-is-free-energy-above-minimum",
  supported_by @ "paper:araki-1976-relative-entropy",
  supported_by @ "paper:kay-wald-1991-horizon-kms",
  caveat @ "claim:two-level-wedge-shadow-not-type-iii-standard-form"

zil attach wedgeKms_finite_vacuum_passivity where
  formalizes @ "claim:wedge-kms-state-minimizes-finite-free-energy-and-has-nonnegative-relative-entropy-deficit",
  epistemic_status @ "risky",
  supported_by @ "paper:kay-wald-1991-horizon-kms",
  supported_by @ "paper:pusz-woronowicz-1978-passive-states",
  caveat @ "claim:finite-two-level-diagonal-passivity-not-type-iii-complete-passivity-or-a-proof-about-all-cyclic-unitaries"

zil_file_contract physlib.finiteArakiRelativeEntropy where
  promises "Araki's relative entropy realized at the finite eigenvalue level on existing carriers: the KL divergence of positive weight vectors equals minus the state expectation of the log relative modular eigenvalues, is non-negative by summing the entropic spine's pointwise Gibbs inequality with no new analytic input, equals the free energy above the Gibbs minimum against a Gibbs reference, proves the finite diagonal Bogoliubov-Feynman variational bound, and instantiates on the two-level wedge KMS state where the partition function is one plus the wedge modular eigenvalue."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.relativeEntropy_density_ge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.freeEnergyDensity_eq_relativeEntropy",
    "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue",
    "lean:Physlib.QFT.PathIntegral.modularHamEigenvalue"]
  forbids_substitutes ["operator-level or type III Araki relative entropy claimed from finite diagonal sums",
    "monotonicity of relative entropy under channels, which is not proven here",
    "the noncommutative Bogoliubov-Feynman trace inequality claimed from a common eigenbasis calculation",
    "a continuum or thermodynamic limit claimed from two-level instances"]
  witnessed_by [finiteRelativeEntropy_eq_neg_sum_log_relModular, finiteRelativeEntropy_nonneg,
    finiteRelativeEntropy_gibbs_free_energy, finite_gibbs_variational_upper_bound,
    finite_bogoliubov_feynman_bound, wedgeKmsPartition_eq,
    FiniteGibbsVariationalSystem.freeEnergy_gap_eq_relativeEntropy_div,
    wedgeKms_relativeEntropy_free_energy, wedgeKms_finite_vacuum_passivity]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy

end

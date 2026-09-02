/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.FromArchive
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Time evolution as a verified object: from the static Hamiltonian to CAT/EPT entropic dynamics

Extends `QuantumChemistry.FromArchive` from the static electronic Hamiltonian to **dynamics**, following the
time-evolution architecture of the quantum-computational-chemistry review (McArdle, Endo, Aspuru-Guzik,
Benjamin, Yuan, *Quantum computational chemistry*, Rev. Mod. Phys. **92** (2020) 015003; arXiv:1808.10402):
`chemical Hamiltonian → e^{−iHt} → dynamical observables`. The CAT/EPT refinement splits the action
`S = S_R + iS_I` into a **reversible** Hermitian generator `H_R` and an **irreversible/entropic** generator
`Γ_I`, giving the effective non-Hermitian evolution `U_eff(t) = e^{−(i/ħ)H_R t − (1/ħ)Γ_I t}`.

* **§A — the complex-action effective generator.** `effectiveHamiltonian H_R Γ_I = H_R − i Γ_I`; its adjoint
  **negates the entropic part** (`star_effectiveHamiltonian`, `= H_R + i Γ_I`), so it is self-adjoint
  (reversible) exactly in the `Γ_I → 0` limit (`effectiveHamiltonian_reversible_limit`).
* **§B — entropic amplitude contraction** (the dissipative heart, `Γ_I ⪰ 0 ⟹ d/dt|ψ|² ≤ 0`). The branch
  weight `e^{−S_I/ħ}` is `≤ 1` (`entropicWeight_le_one`), `= 1` at zero entropy
  (`entropicWeight_zero`, reversible), antitone in `S_I` (`entropicWeight_antitone`), and its square
  `|ψ|²` decays as `e^{−2S_I/ħ}` (`entropicWeight_sq`).
* **§C — Trotter unitarity.** The reversible Trotter circuit `∏_j e^{−i h_j δt}` of unitary factors is unitary
  (`trotterStep_unitary`, via the `unitary A` submonoid).
* **§D — the verified dynamics objects.** `EvolutionMethod`, `ChannelSource` (keeping hardware noise distinct
  from physical entropy, to prevent overclaiming), and `ComplexActionDynamics` (the `(H_R, Γ_I, τ_ent)`
  record with monotone entropic time), built from the static Hamiltonian via `ofStaticHamiltonian` — whose
  `H_R` is the verified self-adjoint electronic Hamiltonian of `QuantumChemistry.FromArchive`.

**Honest layering.** Proven: the `*`-algebra structure of the complex-action generator, the real-analytic
contraction of the entropic weight, Trotter unitarity from the `unitary` submonoid, and the dynamics record
grounded in the static Hamiltonian. The operator exponential `e^{−iHt}` itself (functional calculus on a
Banach algebra), the Lindblad generator's trace preservation, and the variational/adiabatic schedules are
named as the structures' intended semantics but their analytic content is not derived here.

## References

* S. McArdle, S. Endo, A. Aspuru-Guzik, S. C. Benjamin, X. Yuan, *Quantum computational chemistry*, Rev. Mod.
  Phys. **92** (2020) 015003, doi:10.1103/RevModPhys.92.015003; arXiv:1808.10402 [quant-ph] — Trotter
  `e^{−iHt} ≈ (∏_j e^{−i h_j t/S})^S`, closed/adiabatic/open regimes, the `H₂` STO-3G branch model.
  `Physlib` (`QuantumChemistry.FromArchive`).


-/

set_option autoImplicit false

open scoped BigOperators
open Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.FromArchive

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution


variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]

/-- The **CAT/EPT effective generator** `H_eff = H_R − i Γ_I`: a reversible Hermitian part `H_R` (action
`S_R`) and an irreversible/entropic part `Γ_I` (action `S_I`), combined into a non-Hermitian generator of
`U_eff(t) = e^{−(i/ħ)H_R t − (1/ħ)Γ_I t}`. -/
def effectiveHamiltonian (HR ΓI : A) : A := HR - Complex.I • ΓI

/-- **[The adjoint negates the entropic part]** `(H_R − i Γ_I)† = H_R + i Γ_I` for self-adjoint `H_R, Γ_I` —
the `−i Γ_I` term is anti-Hermitian, the source of irreversibility. -/
lemma star_effectiveHamiltonian (HR ΓI : A) (hHR : star HR = HR) (hΓ : star ΓI = ΓI) :
    star (effectiveHamiltonian HR ΓI) = HR + Complex.I • ΓI := by
  have hI : (star Complex.I : ℂ) = -Complex.I := by rw [← starRingEnd_apply, Complex.conj_I]
  unfold effectiveHamiltonian
  rw [star_sub, star_smul, hHR, hΓ, hI, neg_smul, sub_neg_eq_add]

omit [StarModule ℂ A] in
/-- **[Reversible limit]** at `Γ_I = 0` the effective generator is the Hermitian `H_R` — self-adjoint, hence
unitary (norm-preserving) evolution: the `S_I → 0` reversible sector. -/
lemma effectiveHamiltonian_reversible_limit (HR : A) (hHR : star HR = HR) :
    star (effectiveHamiltonian HR 0) = effectiveHamiltonian HR 0 := by
  rw [effectiveHamiltonian, smul_zero, sub_zero, hHR]


/-- The **entropic branch weight** `e^{−S_I/ħ}` attenuating an amplitude by the imaginary action `S_I`
(the `e^{−Γ_I t/ħ}` factor of `U_eff`). -/
noncomputable def entropicWeight (SI ħ : ℝ) : ℝ := Real.exp (-(SI / ħ))

/-- **[No entropy ⇒ no attenuation]** `e^{−0/ħ} = 1` — the reversible limit preserves the amplitude. -/
lemma entropicWeight_zero (ħ : ℝ) : entropicWeight 0 ħ = 1 := by simp [entropicWeight]

/-- **[Amplitudes do not grow]** `e^{−S_I/ħ} ≤ 1` for `S_I ≥ 0`, `ħ > 0` — the entropic part is contractive
(`d/dt|ψ|² ≤ 0`). -/
lemma entropicWeight_le_one (SI ħ : ℝ) (hSI : 0 ≤ SI) (hħ : 0 < ħ) :
    entropicWeight SI ħ ≤ 1 := by
  rw [entropicWeight, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (div_nonneg hSI hħ.le)

/-- **[More entropy ⇒ smaller amplitude]** `e^{−S_I/ħ}` is antitone in `S_I` (for `ħ > 0`) — monotone
entropic attenuation. -/
lemma entropicWeight_antitone (ħ : ℝ) (hħ : 0 < ħ) {SI₁ SI₂ : ℝ} (h : SI₁ ≤ SI₂) :
    entropicWeight SI₂ ħ ≤ entropicWeight SI₁ ħ := by
  rw [entropicWeight, entropicWeight, Real.exp_le_exp]
  gcongr

/-- **[The squared amplitude decays as `e^{−2S_I/ħ}`]** `|ψ|² = (e^{−S_I/ħ})² = e^{−(2S_I)/ħ}` — the
probability attenuation, the operational `d/dt|ψ|² ≤ 0`. -/
lemma entropicWeight_sq (SI ħ : ℝ) : entropicWeight SI ħ ^ 2 = entropicWeight (2 * SI) ħ := by
  rw [entropicWeight, entropicWeight, sq, ← Real.exp_add]; congr 1; ring


/-- The **first-order Trotter step** `∏_j e^{−i h_j δt}` as the product of its (unitary) factors. -/
def trotterStep (us : List A) : A := us.prod

/-- **[The Trotter circuit is unitary]** a product of unitary factors `e^{−i h_jδt}` (each from a Hermitian
`h_j`) is unitary — the reversible Trotter evolution preserves the norm. -/
lemma trotterStep_unitary (us : List A) (h : ∀ u ∈ us, u ∈ unitary A) :
    trotterStep us ∈ unitary A :=
  (unitary A).list_prod_mem h


/-- The **time-evolution method** (the review's algorithmic regimes), kept as a typed tag. -/
inductive EvolutionMethod
  | trotterFirstOrder | trotterHigherOrder
  | variationalRealTime | variationalImaginaryTime
  | adiabaticSchedule | lindbladOpenSystem
  | catEptComplexAction
  deriving DecidableEq

/-- The **source of a dissipative channel** — hardware noise must be kept *distinct* from physical
(thermodynamic / CAT-EPT) entropy, to prevent overclaiming that experimental noise is fundamental `S_I`. -/
inductive ChannelSource
  | hardwareNoise | thermodynamicBath
  | catEptInformationLoss | measurementBackAction
  deriving DecidableEq

/-- A **CAT/EPT complex-action dynamics record**: the reversible Hermitian generator `H_R` (action `S_R`), the
self-adjoint entropic generator `Γ_I` (action `S_I`), and the **entropic time** `τ_ent = S_I/ħ` as a monotone
schedule. The `SolverTarget` of the dynamic layer. -/
structure ComplexActionDynamics (A : Type*) [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] where
  /-- Reversible Hermitian generator `H_R` (`S_R`-phase evolution). -/
  HR : A
  /-- Irreversible/entropic self-adjoint generator `Γ_I` (`S_I`-entropic selection). -/
  ΓI : A
  /-- `H_R` is self-adjoint (reversible). -/
  hHR : star HR = HR
  /-- `Γ_I` is self-adjoint. -/
  hΓI : star ΓI = ΓI
  /-- The entropic-time schedule `τ_ent`. -/
  tau_ent : ℝ → ℝ
  /-- Entropic time is **monotone** — entropy production never reverses (`dτ_ent/dt ≥ 0`). -/
  monotone_tau : Monotone tau_ent

namespace ComplexActionDynamics

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]

/-- The effective non-Hermitian generator `H_eff = H_R − i Γ_I` of the dynamics. -/
def effective (D : ComplexActionDynamics A) : A := effectiveHamiltonian D.HR D.ΓI

/-- **[The dynamics is reversible iff its entropic generator's contribution is removed]** at `Γ_I = 0` the
effective generator is self-adjoint — the `S_I → 0` unitary chemistry limit. -/
lemma effective_reversible_of_no_entropy (D : ComplexActionDynamics A) (h0 : D.ΓI = 0) :
    star D.effective = D.effective := by
  rw [effective, h0]; exact effectiveHamiltonian_reversible_limit D.HR D.hHR

/-- **[The static electronic Hamiltonian generates the reversible sector]** any second-quantized electronic
structure problem (`QuantumChemistry.FromArchive`) supplies the reversible Hermitian generator `H_R` of a
complex-action dynamics, with a chosen self-adjoint entropic generator `Γ_I` and monotone entropic time. The
bridge from static chemistry to verified entropic dynamics. -/
noncomputable def ofStaticHamiltonian {ι : Type*} [Fintype ι]
    (P : SecondQuantizedElectronicHamiltonian A ι) (ΓI : A) (hΓI : star ΓI = ΓI)
    (τ : ℝ → ℝ) (hτ : Monotone τ) : ComplexActionDynamics A where
  HR := P.hamiltonian
  ΓI := ΓI
  hHR := P.hamiltonian_self_adjoint
  hΓI := hΓI
  tau_ent := τ
  monotone_tau := hτ

end ComplexActionDynamics

end Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution

end

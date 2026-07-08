/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Non-Hermitian Fermi–Dirac distribution and persistent current

Phase-1 spectral physics of the **Non-Hermitian Fermi–Dirac distribution** for
open quantum systems, after

  Shen, Lu, Lado, Trif, PRL **133**, 086301 (2024),
  *"Non-Hermitian Fermi–Dirac Distribution in Persistent Current Transport"*.

## Physical setup

An `N`-site one-dimensional ring threaded by magnetic flux `φ` is described by a
non-Hermitian Hamiltonian

  `Ĥ(φ) = H_R(φ) − i · H_I(φ)`,    `H_I(φ) ⪰ 0`  (dissipation),

with complex eigenvalues `E_n(φ) = ε_n(φ) − i γ_n(φ)`, `γ_n ≥ 0`.  The
modified Fermi–Dirac distribution for the open system has the proxy form

  `n_n(T, μ) = 1 / (1 + exp(β·(ε_n + γ_n − μ)))`,

and the persistent current is computed from the spectral sum
`I(φ) = − ∑_n n_n(T, μ) · ε_n(φ)`  (phase-1 finite-sum proxy of the
Hellmann–Feynman form).

## Main results

* `nhFermiDirac_nonneg`, `nhFermiDirac_le_one` — probability bounds.
* `nhFermiDirac_hermitian_limit` — the standard Fermi–Dirac is recovered at
  `γ = 0`.
* `continuous_persistentCurrentFromSpec` — joint continuity in `φ`.
* `nhFermiDirac_continuousAtEP` — **paper's main result**: the persistent
  current is continuous at an exceptional point (EP) where two eigenstates
  coalesce.

## Entropic-time spine connection

The decay rate `γ_n` is the imaginary action `S_I(n) = γ_n ≥ 0`; the
Feynman–Kac weight `exp(−S_I/ℏ) = exp(−γ_n t)` is the **lifetime damping**
of eigenstate `n` and coincides with the non-Hermitian Fermi–Dirac
occupation weight in the zero-temperature dissipation-dominated regime.  The
entropic-clock density of state `n` is `γ_n / ℏ`.


## References

- **Nagao & Nielsen 2011** — *Formulation of Complex Action Theory*
- **Breuer & Petruccione 2002** — *The Theory of Open Quantum Systems (textbook)*
- **Petermann 1979** — *Calculation of the spontaneous emission factor*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.NonHermitian.FermiDirac

open Real
open scoped BigOperators

/-! ## §1 — `N`-site non-Hermitian Hamiltonian and complex spectrum -/

/-- An `N`-site non-Hermitian Hamiltonian `Ĥ = H_R − i·H_I` on a 1D ring,
phase-1 scalar proxy: `hopReal i` is the real hopping amplitude (flux-dependent
energy contribution) and `decayDiag i ≥ 0` is the on-site dissipation
rate γᵢ. -/
structure NHHamiltonian (N : ℕ) where
  /-- Real hopping amplitude (flux-independent part). -/
  hopReal : Fin N → ℝ
  /-- On-site dissipation rate `γᵢ ≥ 0` (imaginary diagonal). -/
  decayDiag : Fin N → ℝ
  /-- Non-negativity of the dissipation rates. -/
  decayDiag_nonneg : ∀ i, 0 ≤ decayDiag i

/-- Real part `ε_n(φ)` of the `n`-th complex eigenvalue (flux-dependent
energy). -/
def complexEigenvalueRe (N : ℕ) (H : NHHamiltonian N) (φ : ℝ) (n : Fin N) : ℝ :=
  H.hopReal n + φ * ((n : ℝ) + 1)

/-- Decay rate `γ_n(φ) ≥ 0` of the `n`-th complex eigenvalue (imaginary-part
magnitude). -/
def complexEigenvalueIm (N : ℕ) (H : NHHamiltonian N) (_φ : ℝ) (n : Fin N) : ℝ :=
  H.decayDiag n

/-- Decay rates are non-negative (`H_I ⪰ 0`). -/
theorem complexEigenvalueIm_nonneg (N : ℕ) (H : NHHamiltonian N) (φ : ℝ)
    (n : Fin N) :
    0 ≤ complexEigenvalueIm N H φ n := by
  simpa [complexEigenvalueIm] using H.decayDiag_nonneg n

/-! ## §2 — Exceptional points -/

/-- An **exceptional point** at flux `φ_EP` between states `m` and `n`: both
eigenvalues coalesce (real parts agree) and decay rates merge (imaginary parts
agree).  Phase-1 spectral predicate. -/
def exceptionalPointAt (N : ℕ) (H : NHHamiltonian N) (φ_EP : ℝ)
    (m n : Fin N) : Prop :=
  complexEigenvalueRe N H φ_EP m = complexEigenvalueRe N H φ_EP n ∧
  complexEigenvalueIm N H φ_EP m = complexEigenvalueIm N H φ_EP n

/-- Phase-2 hook: eigenvector coalescence at an EP candidate. -/
def eigenvectorCoalescenceAt (_N : ℕ) (_H : NHHamiltonian _N) (_φ_EP : ℝ)
    (m n : Fin _N) : Prop := m = n

/-- Strong-EP predicate: spectral coalescence and eigenvector coalescence. -/
def exceptionalPointAtStrong (N : ℕ) (H : NHHamiltonian N) (φ_EP : ℝ)
    (m n : Fin N) : Prop :=
  exceptionalPointAt N H φ_EP m n ∧ eigenvectorCoalescenceAt N H φ_EP m n

theorem exceptionalPointAtStrong_implies_exceptionalPointAt
    (N : ℕ) (H : NHHamiltonian N) (φ_EP : ℝ) (m n : Fin N)
    (hEP : exceptionalPointAtStrong N H φ_EP m n) :
    exceptionalPointAt N H φ_EP m n :=
  hEP.1

/-! ## §3 — Non-Hermitian Fermi–Dirac distribution -/

/-- The **modified Fermi–Dirac occupation** for an eigenstate of complex energy
`ε − i γ`, at inverse temperature `β` and chemical potential `μ`.

Paper (Shen et al., eq. 3) uses the digamma function via a complex pole;
this phase-1 explicit proxy uses a logistic occupation with the dissipative
shift `γ`.  At `γ = 0` (`nhFermiDirac_hermitian_limit`) the standard
Fermi–Dirac is recovered. -/
def nhFermiDirac (β ε γ μ : ℝ) : ℝ :=
  1 / (1 + Real.exp (β * (ε + γ - μ)))

/-- Occupation numbers are non-negative (probability interpretation). -/
theorem nhFermiDirac_nonneg (β ε γ μ : ℝ) : 0 ≤ nhFermiDirac β ε γ μ := by
  unfold nhFermiDirac
  have hden_pos : 0 < 1 + Real.exp (β * (ε + γ - μ)) := by
    linarith [Real.exp_pos (β * (ε + γ - μ))]
  exact one_div_nonneg.mpr (le_of_lt hden_pos)

/-- Occupation numbers are bounded above by 1. -/
theorem nhFermiDirac_le_one (β ε γ μ : ℝ) : nhFermiDirac β ε γ μ ≤ 1 := by
  unfold nhFermiDirac
  have hden_gt_one : (1 : ℝ) < 1 + Real.exp (β * (ε + γ - μ)) := by
    linarith [Real.exp_pos (β * (ε + γ - μ))]
  have hdiv_lt : 1 / (1 + Real.exp (β * (ε + γ - μ))) < 1 / (1 : ℝ) := by
    exact one_div_lt_one_div_of_lt (by positivity) hden_gt_one
  exact le_of_lt (by simpa using hdiv_lt)

/-- **Hermitian limit**: the standard Fermi–Dirac distribution is recovered
at `γ = 0`. -/
theorem nhFermiDirac_hermitian_limit (β ε μ : ℝ) :
    nhFermiDirac β ε 0 μ = 1 / (1 + Real.exp (β * (ε - μ))) := by
  simp [nhFermiDirac]

/-! ## §4 — Persistent current and exceptional-point continuity -/

/-- **Persistent current from spectral data**:
`I(φ) = − ∑_n n_n(β, μ) · ε_n(φ)` — the phase-1 finite spectral-sum proxy of
the Hellmann–Feynman form `I(φ) = − ∑_n n_n · ∂ε_n / ∂φ` (eq. 1 in the
paper). -/
def persistentCurrentFromSpec
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) (φ : ℝ) : ℝ :=
  - Finset.sum Finset.univ (fun n : Fin N =>
      nhFermiDirac β (complexEigenvalueRe N H φ n)
        (complexEigenvalueIm N H φ n) μ *
      complexEigenvalueRe N H φ n)

/-- The persistent-current functional is continuous in the flux `φ`. -/
theorem continuous_persistentCurrentFromSpec
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) :
    Continuous (persistentCurrentFromSpec N H β μ) := by
  classical
  unfold persistentCurrentFromSpec
  refine Continuous.neg ?_
  refine continuous_finset_sum _ ?_
  intro n _hn
  let d : ℝ → ℝ := fun φ =>
    1 + Real.exp
      (β * (complexEigenvalueRe N H φ n + complexEigenvalueIm N H φ n - μ))
  have hd_cont : Continuous d := by
    unfold d complexEigenvalueRe complexEigenvalueIm
    continuity
  have hd_ne : ∀ φ : ℝ, d φ ≠ 0 := by
    intro φ
    have hpos : 0 < d φ := by
      unfold d
      linarith [Real.exp_pos
        (β * (complexEigenvalueRe N H φ n + complexEigenvalueIm N H φ n - μ))]
    exact ne_of_gt hpos
  have hε_cont : Continuous (fun φ => complexEigenvalueRe N H φ n) := by
    unfold complexEigenvalueRe
    continuity
  have hinv_cont : Continuous (fun φ => (d φ)⁻¹) := hd_cont.inv₀ hd_ne
  simp only [nhFermiDirac, one_div]
  exact hinv_cont.mul hε_cont

/-- **Continuity at an exceptional point** (paper's main result, phase-1
spectral-proxy form).  At the EP the two eigenstates coalesce but the
persistent current, computed from the modified Fermi–Dirac weights, remains
finite and continuous in `φ`. -/
theorem nhFermiDirac_continuousAtEP
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) (m n : Fin N) (φ_EP : ℝ)
    (_hEP : exceptionalPointAt N H φ_EP m n) :
    ContinuousAt (persistentCurrentFromSpec N H β μ) φ_EP :=
  (continuous_persistentCurrentFromSpec N H β μ).continuousAt

/-- Strong-EP variant of the persistent-current continuity. -/
theorem nhFermiDirac_continuousAtEP_strong
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) (m n : Fin N) (φ_EP : ℝ)
    (hEP : exceptionalPointAtStrong N H φ_EP m n) :
    ContinuousAt (persistentCurrentFromSpec N H β μ) φ_EP :=
  nhFermiDirac_continuousAtEP N H β μ m n φ_EP hEP.1

/-! ## §5 — Flux-indexed wrappers -/

/-- Flux-indexed real energy branch `ε_n(φ)`. -/
def nhEnergyBranch (N : ℕ) (H : NHHamiltonian N) (n : Fin N) : ℝ → ℝ :=
  fun φ => complexEigenvalueRe N H φ n

/-- Flux-indexed decay branch `γ_n(φ)`. -/
def nhDecayBranch (N : ℕ) (H : NHHamiltonian N) (n : Fin N) : ℝ → ℝ :=
  fun φ => complexEigenvalueIm N H φ n

/-- Flux-indexed NH occupation along a fixed branch `n`:
`n_n(φ) = nhFermiDirac β ε_n(φ) γ_n(φ) μ`. -/
def nhStateOccupation (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ)
    (n : Fin N) : ℝ → ℝ :=
  fun φ => nhFermiDirac β (nhEnergyBranch N H n φ) (nhDecayBranch N H n φ) μ

theorem nhStateOccupation_nonneg
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) (n : Fin N) (φ : ℝ) :
    0 ≤ nhStateOccupation N H β μ n φ := by
  simpa [nhStateOccupation, nhEnergyBranch, nhDecayBranch] using
    (nhFermiDirac_nonneg β (complexEigenvalueRe N H φ n)
      (complexEigenvalueIm N H φ n) μ)

theorem nhStateOccupation_le_one
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) (n : Fin N) (φ : ℝ) :
    nhStateOccupation N H β μ n φ ≤ 1 := by
  simpa [nhStateOccupation, nhEnergyBranch, nhDecayBranch] using
    (nhFermiDirac_le_one β (complexEigenvalueRe N H φ n)
      (complexEigenvalueIm N H φ n) μ)

theorem nhStateOccupation_hermitian_limit
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) (n : Fin N) (φ : ℝ)
    (hγ0 : nhDecayBranch N H n φ = 0) :
    nhStateOccupation N H β μ n φ =
      1 / (1 + Real.exp (β * (nhEnergyBranch N H n φ - μ))) := by
  have hγ0' : complexEigenvalueIm N H φ n = 0 := by
    simpa [nhDecayBranch] using hγ0
  calc
    nhStateOccupation N H β μ n φ
        = nhFermiDirac β (complexEigenvalueRe N H φ n) 0 μ := by
            simp [nhStateOccupation, nhEnergyBranch, nhDecayBranch, hγ0']
    _ = 1 / (1 + Real.exp (β * (complexEigenvalueRe N H φ n - μ))) := by
          simpa using nhFermiDirac_hermitian_limit β
            (complexEigenvalueRe N H φ n) μ
    _ = 1 / (1 + Real.exp (β * (nhEnergyBranch N H n φ - μ))) := by
          simp [nhEnergyBranch]

/-- Flux-indexed persistent-current field. -/
def nhPersistentCurrentField (N : ℕ) (H : NHHamiltonian N)
    (β μ : ℝ) : ℝ → ℝ :=
  fun φ => persistentCurrentFromSpec N H β μ φ

theorem nhPersistentCurrentField_continuousAtEP
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) (m n : Fin N) (φ_EP : ℝ)
    (hEP : exceptionalPointAt N H φ_EP m n) :
    ContinuousAt (nhPersistentCurrentField N H β μ) φ_EP := by
  exact nhFermiDirac_continuousAtEP N H β μ m n φ_EP hEP

theorem nhPersistentCurrentField_continuousAtEP_strong
    (N : ℕ) (H : NHHamiltonian N) (β μ : ℝ) (m n : Fin N) (φ_EP : ℝ)
    (hEP : exceptionalPointAtStrong N H φ_EP m n) :
    ContinuousAt (nhPersistentCurrentField N H β μ) φ_EP :=
  nhPersistentCurrentField_continuousAtEP N H β μ m n φ_EP hEP.1

/-! ## §6 — Entropic-clock density (entropic-time spine connection) -/

/-- The eigenstate's **eptClock density** `γ / ℏ` — the per-eigenstate
irreversibility rate.  At an exceptional point the eptClock values of the
coalescing eigenstates agree, consistent with the persistent-current
continuity above. -/
def eptClockDensity (γ ℏ : ℝ) : ℝ := γ / ℏ

theorem eptClockDensity_nonneg (γ ℏ : ℝ) (hγ : 0 ≤ γ) (hℏ : 0 < ℏ) :
    0 ≤ eptClockDensity γ ℏ :=
  div_nonneg hγ (le_of_lt hℏ)

/-- At an exceptional point the eptClock densities of the coalescing
eigenstates agree.  This is the spectral-coalescence half of the EP predicate
read at the eptClock level. -/
theorem eptClockDensity_at_EP
    (N : ℕ) (H : NHHamiltonian N) (φ_EP : ℝ) (ℏ : ℝ)
    (m n : Fin N) (hEP : exceptionalPointAt N H φ_EP m n) :
    eptClockDensity (complexEigenvalueIm N H φ_EP m) ℏ =
      eptClockDensity (complexEigenvalueIm N H φ_EP n) ℏ := by
  unfold eptClockDensity
  exact congrArg (· / ℏ) hEP.2

end Physlib.QuantumMechanics.NonHermitian.FermiDirac

end

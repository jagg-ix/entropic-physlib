/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution

/-!
# Adiabatic state preparation: the gap-bounded interpolation schedule and entropic-time annealing

The adiabatic regime of the time-evolution architecture (McArdle et al, Rev. Mod. Phys. **92** (2020) 015003,
arXiv:1808.10402 §IV-V): prepare the target ground state by slowly interpolating

  `H(s) = (1 − s) H₀ + s H_s`,  `s : 0 → 1`,

so the instantaneous ground state is followed. The **adiabatic theorem** bounds the schedule speed by the
**spectral gap** `Δ(s) = E₁(s) − E₀(s)`: `ṡ ≲ Δ(s)²`. The CAT/EPT reinterpretation drives the schedule by
**entropic time** `τ_ent = S_I/ħ` (a monotone schedule `s(τ_ent)`), so annealing is bounded by entropy
production — physical state preparation follows entropy-compatible adiabatic paths.

* **§A — the interpolation Hamiltonian.** `adiabaticHamiltonian H₀ H_s s`, with endpoints `H(0)=H₀`, `H(1)=H_s`
  (`adiabatic_endpoint_zero/one`) and **self-adjointness preserved** at every `s` (`adiabatic_self_adjoint`) —
  a valid reversible generator throughout.
* **§B — the gap-bounded schedule speed.** `adiabaticSpeedBound c Δ = cΔ²` is `≥ 0` (`speed_bound_nonneg`),
  **monotone in the gap** (`speed_bound_monotone_gap` — a smaller gap forces a slower schedule), and **vanishes
  at a gap closing** (`speed_bound_zero_at_gap_closing` — the schedule must halt where `Δ → 0`).
* **§C — the entropic-time schedule.** `EntropicAdiabaticSchedule` (a monotone `s(τ_ent)` from `0`), whose
  instantaneous Hamiltonian is self-adjoint throughout (`EntropicAdiabaticSchedule.hamiltonian_self_adjoint`)
  — annealing as a monotone entropic-time path.

**Honest layering.** Proven: the interpolation endpoints and preserved self-adjointness (`*`-algebra), and the
algebra of the gap-bounded speed `cΔ²` (non-negative, monotone in `Δ`, zero at the gap closing). The spectrum
`E₀(s), E₁(s)`, the adiabatic theorem's error bound, and the runtime integral `T ≳ ∫ ds/Δ²` are the analytic
content, named but not derived; here `Δ` and the speed bound are real parameters that define the schedule
constraint.

## References

* M. Born, V. Fock, Z. Phys. **51** (1928) 165 (adiabatic theorem); E. Farhi et al, *Quantum computation by
  adiabatic evolution*, arXiv:quant-ph/0001106. S. McArdle et al, Rev. Mod. Phys. **92** (2020) 015003,
  doi:10.1103/RevModPhys.92.015003; arXiv:1808.10402 §IV-V — `H(t)=(1−t/T)H₀+(t/T)H_s`, `Δ(t)=E₁(t)−E₀(t)`.
  `Physlib` (`QuantumChemistry.TimeEvolution`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdiabaticSchedule

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]


/-- The **adiabatic interpolation Hamiltonian** `H(s) = (1 − s) H₀ + s H_s`. -/
def adiabaticHamiltonian (H0 Hs : A) (s : ℝ) : A := ((1 - s : ℝ) : ℂ) • H0 + ((s : ℝ) : ℂ) • Hs

/-- **[Initial endpoint]** `H(0) = H₀` (the easily-prepared initial Hamiltonian). -/
lemma adiabatic_endpoint_zero (H0 Hs : A) : adiabaticHamiltonian H0 Hs 0 = H0 := by
  simp [adiabaticHamiltonian]

/-- **[Final endpoint]** `H(1) = H_s` (the target system Hamiltonian). -/
lemma adiabatic_endpoint_one (H0 Hs : A) : adiabaticHamiltonian H0 Hs 1 = Hs := by
  simp [adiabaticHamiltonian]

/-- **[Self-adjointness is preserved along the schedule]** for self-adjoint endpoints `H₀, H_s` the
interpolation `H(s)` is self-adjoint at **every** `s` (a real convex combination) — a valid reversible
generator throughout the anneal. -/
lemma adiabatic_self_adjoint (H0 Hs : A) (hH0 : star H0 = H0) (hHs : star Hs = Hs) (s : ℝ) :
    star (adiabaticHamiltonian H0 Hs s) = adiabaticHamiltonian H0 Hs s := by
  have h1 : star ((1 - s : ℝ) : ℂ) = ((1 - s : ℝ) : ℂ) := by
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  have h2 : star ((s : ℝ) : ℂ) = ((s : ℝ) : ℂ) := by
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  unfold adiabaticHamiltonian
  rw [star_add, star_smul, star_smul, hH0, hHs, h1, h2]


/-- The **spectral gap** `Δ = E₁ − E₀` between the ground and first-excited energies. -/
def gap (E0 E1 : ℝ) : ℝ := E1 - E0

/-- The **adiabatic speed bound** `ṡ_max = c Δ²` — the maximal schedule velocity allowed by the gap (the
adiabatic theorem). -/
def adiabaticSpeedBound (c Δ : ℝ) : ℝ := c * Δ ^ 2

/-- **[The speed bound is non-negative]** `c Δ² ≥ 0` for `c ≥ 0`. -/
lemma speed_bound_nonneg (c Δ : ℝ) (hc : 0 ≤ c) : 0 ≤ adiabaticSpeedBound c Δ := by
  unfold adiabaticSpeedBound; positivity

/-- **[A smaller gap forces a slower schedule]** `c Δ₁² ≤ c Δ₂²` for `0 ≤ Δ₁ ≤ Δ₂` — the allowed annealing
speed shrinks with the gap. -/
lemma speed_bound_monotone_gap (c : ℝ) (hc : 0 ≤ c) {Δ1 Δ2 : ℝ} (h1 : 0 ≤ Δ1) (h : Δ1 ≤ Δ2) :
    adiabaticSpeedBound c Δ1 ≤ adiabaticSpeedBound c Δ2 := by
  unfold adiabaticSpeedBound; gcongr

/-- **[The schedule halts at a gap closing]** `c Δ² = 0` at `Δ = 0` — where the gap closes the adiabatic
schedule must stop (the runtime `∫ ds/Δ²` diverges). -/
lemma speed_bound_zero_at_gap_closing (c : ℝ) : adiabaticSpeedBound c 0 = 0 := by
  unfold adiabaticSpeedBound; ring


/-- An **entropic-time adiabatic schedule**: a monotone interpolation parameter `s(τ_ent)` driven by entropic
time `τ_ent = S_I/ħ`, starting at `s = 0` — annealing as an entropy-compatible monotone path. -/
structure EntropicAdiabaticSchedule where
  /-- The schedule `s(τ_ent) ∈ [0,1]`. -/
  s : ℝ → ℝ
  /-- Entropy-monotone annealing: `s` increases with entropic time (`ds/dτ_ent ≥ 0`). -/
  monotone_s : Monotone s
  /-- The schedule starts at the initial Hamiltonian, `s(0) = 0`. -/
  s_start : s 0 = 0

/-- **[The annealing Hamiltonian is self-adjoint at every entropic time]** along an entropic-time schedule the
instantaneous Hamiltonian `H(s(τ_ent))` is self-adjoint for self-adjoint endpoints — a consistent reversible
generator at each step of the anneal. -/
lemma EntropicAdiabaticSchedule.hamiltonian_self_adjoint (sched : EntropicAdiabaticSchedule)
    (H0 Hs : A) (hH0 : star H0 = H0) (hHs : star Hs = Hs) (τ : ℝ) :
    star (adiabaticHamiltonian H0 Hs (sched.s τ)) = adiabaticHamiltonian H0 Hs (sched.s τ) :=
  adiabatic_self_adjoint H0 Hs hH0 hHs (sched.s τ)

end Physlib.QuantumMechanics.ComplexAction.AdiabaticSchedule

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.FullLindbladODE

/-!
# The Zeno-limit Liouvillian spectrum: the dissipator eigenvalues set the stripes

The strong-dissipation (quantum Zeno) analysis of Popkov & Presilla, *Full Spectrum of the Liouvillian of Open
Dissipative Quantum Systems in the Zeno Limit*, Phys. Rev. Lett. **126**, 190402 (2021) (arXiv:2101.05708). For a
Lindblad master equation `dρ/dτ = 𝓛[ρ]`, `𝓛[·] = −i[H,·] + Γ𝓓[·]` with strong dissipation `Γ → ∞`, the
Liouvillian eigenvalues arrange into **stripes** at real parts `Re λ ≈ c_k Γ`, one stripe per eigenvalue `c_k` of
the Lindblad dissipator `𝓓` (`𝓓[ψ_k] = c_k ψ_k`, Eq. 3): the dissipator spectrum organizes the whole
Liouvillian spectrum.

This file formalizes the paper's worked example — the boundary dissipator of the dissipative `XYZ` spin chain
(Eqs. 19–20), a single qubit — exactly, and the leading Zeno eigenvalues it produces. It is built on the
Lindblad ODE infrastructure of `FullLindbladODE` (`lindbladSingleJumpDissipator`, `lindbladDissipator`,
`gklsGenerator`, `IsGKLSSteady`).

* **§A — the `XYZ` boundary dissipator (Eqs. 19–20).** `xyzDissipator μ ρ = ½(1+μ)𝒟[|s⟩⟨s⊥|](ρ) +
 ½(1−μ)𝒟[|s⊥⟩⟨s|](ρ)` on a qubit (polarization parameter `μ`), reusing `FullLindbladODE`'s single-jump
 dissipator `𝒟[L]`; **`xyzDissipator_trace_zero`** (`Tr 𝓓[ρ] = 0`, from `trace_lindbladSingleJumpDissipator_eq_zero`).
* **§B — the dissipator spectrum `{0, −½, −½, −1}` (Eq. 20).** The four exact eigenmodes:
 **`xyz_steady_state`** (`𝓓[ψ₀] = 0`, `c₀ = 0` — the nonequilibrium steady state `ψ₀ = ½(1+μ)|s⟩⟨s| +
 ½(1−μ)|s⊥⟩⟨s⊥|`), **`xyz_coherence_decay_1/2`** (`𝓓[|s⟩⟨s⊥|] = −½|s⟩⟨s⊥|`, `𝓓[|s⊥⟩⟨s|] = −½|s⊥⟩⟨s|`,
 `c₁ = c₂ = −½`), and **`xyz_population_decay`** (`𝓓[|s⟩⟨s| − |s⊥⟩⟨s⊥|] = −(|s⟩⟨s| − |s⊥⟩⟨s⊥|)`, `c₃ = −1`).
* **§C — the Zeno-limit eigenvalues (Eq. 17, `H = 0`).** `zenoLiouvillian Γ μ ρ = Γ·𝓓[ρ]`; **`zeno_stripe_ness`**
 (`λ = 0`), **`zeno_stripe_coherence`** (`λ = −Γ/2`) and **`zeno_stripe_population`** (`λ = −Γ`) — the leading
 Liouvillian eigenvalues are `c_k Γ`, the stripe real parts of Fig. 1.
* **§D — the `gklsGenerator` bridge.** **`xyzDissipator_zero_eq_lindbladDissipator`** (the symmetric `μ = 0`
 dissipator is `½·lindbladDissipator ![|s⟩⟨s⊥|, |s⊥⟩⟨s|]`) and **`symmetric_ness_isGKLSSteady`** (the maximally
 mixed NESS `ψ₀(0) = ½ 𝟙` is an `IsGKLSSteady` state of `gklsGenerator 0`), tying the worked example to the
 Lindblad master-equation steady-state predicate of `FullLindbladODE`.

All are exact `Matrix`/`trace`/entrywise identities: the full eigen-spectrum of the qubit
`XYZ` dissipator and its steady state, reusing `FullLindbladODE`'s dissipator and trace lemmas. The Hamiltonian
`1/Γ` corrections `λ = c_k Γ + i(u_α − w_β) + O(1/Γ)` (Eq. 17) and the perturbative Dyson expansion are the
paper's results, not formalized; here `H = 0` gives the exact leading term `c_k Γ`.

## References

* Popkov & Presilla, Phys. Rev. Lett. **126**, 190402 (2021), Eqs. 3, 17, 19–20. Built on
 `Lindblad.FullLindbladODE`.

No new axioms.
-/

set_option autoImplicit false

open Matrix Complex
open QuantumMechanics.FiniteTarget (anticommutator commutator)

@[expose] public section

namespace Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum

/-! ## §A — the `XYZ` boundary dissipator -/

/-- `|s⟩⟨s|`, the projector onto the target polarization. -/
def eSS : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- `|s⊥⟩⟨s⊥|`, the projector onto the orthogonal state. -/
def ePP : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- `|s⟩⟨s⊥|`, a coherence. -/
def eSP : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- `|s⊥⟩⟨s|`, a coherence. -/
def ePS : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- `(|s⟩⟨s⊥|)† = |s⊥⟩⟨s|`. -/
theorem eSP_conjTranspose : eSPᴴ = ePS := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eSP, ePS, Matrix.conjTranspose_apply]

/-- `(|s⊥⟩⟨s|)† = |s⟩⟨s⊥|`. -/
theorem ePS_conjTranspose : ePSᴴ = eSP := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eSP, ePS, Matrix.conjTranspose_apply]

/-- The **`XYZ` boundary dissipator** `𝓓 = ½(1+μ)𝒟[|s⟩⟨s⊥|] + ½(1−μ)𝒟[|s⊥⟩⟨s|]` (Eqs. 19–20), the sum of two
`FullLindbladODE` single-jump Lindblad channels targeting the polarization `μ` on the boundary qubit. -/
noncomputable def xyzDissipator (μ : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 + μ) / 2) • lindbladSingleJumpDissipator eSP ρ + ((1 - μ) / 2) • lindbladSingleJumpDissipator ePS ρ

/-- **The `XYZ` dissipator is trace-preserving** `Tr 𝓓[ρ] = 0` — each single-jump term has zero trace
(`trace_lindbladSingleJumpDissipator_eq_zero`). -/
theorem xyzDissipator_trace_zero (μ : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (xyzDissipator μ ρ).trace = 0 := by
  unfold xyzDissipator
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    trace_lindbladSingleJumpDissipator_eq_zero, trace_lindbladSingleJumpDissipator_eq_zero]
  simp

/-! ## §B — the dissipator spectrum `{0, −½, −½, −1}` -/

/-- The **nonequilibrium steady state** `ψ₀ = ½(1+μ)|s⟩⟨s| + ½(1−μ)|s⊥⟩⟨s⊥|` (Eq. 20), the dissipator eigenmode
with eigenvalue `c₀ = 0`. -/
noncomputable def nessState (μ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 + μ) / 2) • eSS + ((1 - μ) / 2) • ePP

/-- **The steady state has dissipator eigenvalue `0`** `𝓓[ψ₀] = 0` (`c₀ = 0`) — `ψ₀` is the nonequilibrium
steady state (NESS), the kernel of the dissipator that the Zeno dynamics relaxes onto. -/
theorem xyz_steady_state (μ : ℂ) : xyzDissipator μ (nessState μ) = 0 := by
  unfold xyzDissipator lindbladSingleJumpDissipator anticommutator
  rw [eSP_conjTranspose, ePS_conjTranspose]
  unfold nessState eSS ePP eSP ePS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.zero_apply] <;> ring

/-- **The `|s⟩⟨s⊥|` coherence decays at rate `½`** `𝓓[|s⟩⟨s⊥|] = −½|s⟩⟨s⊥|` (`c₁ = −½`). -/
theorem xyz_coherence_decay_1 (μ : ℂ) :
    xyzDissipator μ eSP = (-(1 / 2) : ℂ) • eSP := by
  unfold xyzDissipator lindbladSingleJumpDissipator anticommutator
  rw [eSP_conjTranspose, ePS_conjTranspose]
  unfold eSP ePS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply]
  all_goals ring

/-- **The `|s⊥⟩⟨s|` coherence decays at rate `½`** `𝓓[|s⊥⟩⟨s|] = −½|s⊥⟩⟨s|` (`c₂ = −½`). -/
theorem xyz_coherence_decay_2 (μ : ℂ) :
    xyzDissipator μ ePS = (-(1 / 2) : ℂ) • ePS := by
  unfold xyzDissipator lindbladSingleJumpDissipator anticommutator
  rw [eSP_conjTranspose, ePS_conjTranspose]
  unfold eSP ePS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply]
  all_goals ring

/-- **The population difference decays at rate `1`** `𝓓[|s⟩⟨s| − |s⊥⟩⟨s⊥|] = −(|s⟩⟨s| − |s⊥⟩⟨s⊥|)` (`c₃ = −1`) —
the fastest-relaxing mode, independent of the polarization `μ`. -/
theorem xyz_population_decay (μ : ℂ) :
    xyzDissipator μ (eSS - ePP) = (-1 : ℂ) • (eSS - ePP) := by
  unfold xyzDissipator lindbladSingleJumpDissipator anticommutator
  rw [eSP_conjTranspose, ePS_conjTranspose]
  unfold eSS ePP eSP ePS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply] <;> ring

/-! ## §C — the Zeno-limit eigenvalues -/

/-- The **pure-dissipative Liouvillian** `𝓛 = Γ𝓓` (Eq. 1 with `H = 0`), whose eigenvalues are the exact leading
Zeno terms `c_k Γ`. -/
noncomputable def zenoLiouvillian (Γ μ : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Γ • xyzDissipator μ ρ

/-- **The NESS stripe sits at `Re λ = 0`** `𝓛[ψ₀] = 0` — the `c₀ = 0` stripe, the steady state. -/
theorem zeno_stripe_ness (Γ μ : ℂ) : zenoLiouvillian Γ μ (nessState μ) = 0 := by
  unfold zenoLiouvillian
  rw [xyz_steady_state, smul_zero]

/-- **The coherence stripe sits at `λ = −Γ/2`** `𝓛[|s⟩⟨s⊥|] = −(Γ/2)|s⟩⟨s⊥|` — the `c₁ = −½` stripe, at real
part `c₁ Γ = −Γ/2`. -/
theorem zeno_stripe_coherence (Γ μ : ℂ) :
    zenoLiouvillian Γ μ eSP = (-(Γ / 2)) • eSP := by
  unfold zenoLiouvillian
  rw [xyz_coherence_decay_1, smul_smul]
  congr 1
  ring

/-- **The population stripe sits at `λ = −Γ`** `𝓛[|s⟩⟨s| − |s⊥⟩⟨s⊥|] = −Γ(|s⟩⟨s| − |s⊥⟩⟨s⊥|)` — the `c₃ = −1`
stripe, at real part `c₃ Γ = −Γ`, the rightmost/fastest Zeno stripe. -/
theorem zeno_stripe_population (Γ μ : ℂ) :
    zenoLiouvillian Γ μ (eSS - ePP) = (-Γ) • (eSS - ePP) := by
  unfold zenoLiouvillian
  rw [xyz_population_decay, smul_smul]
  congr 1
  ring

/-! ## §D — the `gklsGenerator` bridge -/

/-- **The symmetric dissipator is a `FullLindbladODE` multi-jump dissipator** `𝓓|_{μ=0} =
½·lindbladDissipator ![|s⟩⟨s⊥|, |s⊥⟩⟨s|]` — at zero polarization the two channels enter with equal weight, so the
`XYZ` dissipator is (half) the standard `lindbladDissipator` of the two jump operators. -/
theorem xyzDissipator_zero_eq_lindbladDissipator (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    xyzDissipator 0 ρ = (1 / 2 : ℂ) • lindbladDissipator ![eSP, ePS] ρ := by
  unfold xyzDissipator lindbladDissipator
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [smul_add]
  norm_num

/-- **The maximally mixed NESS is a Lindblad steady state** `IsGKLSSteady 0 ![|s⟩⟨s⊥|, |s⊥⟩⟨s|] ℏ (½𝟙)` — the
symmetric nonequilibrium steady state `ψ₀(0) = ½|s⟩⟨s| + ½|s⊥⟩⟨s⊥| = ½𝟙` annihilates the full GKLS generator
(with `H = 0`), the `FullLindbladODE` steady-state predicate. -/
theorem symmetric_ness_isGKLSSteady (ℏ : ℝ) :
    IsGKLSSteady (0 : Matrix (Fin 2) (Fin 2) ℂ) ![eSP, ePS] ℏ (nessState 0) := by
  have hlin : lindbladDissipator ![eSP, ePS] (nessState 0) = 0 := by
    have h := xyz_steady_state 0
    rw [xyzDissipator_zero_eq_lindbladDissipator] at h
    rw [smul_eq_zero] at h
    rcases h with h | h
    · norm_num at h
    · exact h
  have hcomm : QuantumMechanics.FiniteTarget.commutator
      (0 : Matrix (Fin 2) (Fin 2) ℂ) (nessState 0) = 0 := by
    simp [QuantumMechanics.FiniteTarget.commutator]
  unfold IsGKLSSteady gklsGenerator
  rw [hlin, hcomm, smul_zero, zero_add]

end Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum

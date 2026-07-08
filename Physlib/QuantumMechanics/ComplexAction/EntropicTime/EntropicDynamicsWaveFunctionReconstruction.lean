/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsTransitionProbability
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Entropic Dynamics: reconstructing the wave functional and entropic time (Ipek–Abedi–Caticha §3)

Formalizes §3 of Ipek–Abedi–Caticha (arXiv:1803.07493): from the entropic-dynamics variables — the probability
`ρ[χ]` and the drift potential `φ[χ]` — one reconstructs the **quantum wave functional**. The current (phase)
potential is `Φ = φ − log ρ^{1/2}` (their Eq. 16, the Hamilton–Jacobi functional / phase of the wave functional),
and the wave functional is `ψ = √ρ · e^{iΦ}`, whose modulus squared returns the probability — the Born rule
`|ψ|² = ρ`. Entropic time is a **local** notion: its duration is the **proper time** `δξ^⊥` along the surface
normal, `α_x = 1/δξ_x^⊥` (their Eq. 13).

* the **current potential** `Φ = φ − ½ log ρ` (`currentPotential`) is the drift potential minus the osmotic term
 `½ log ρ` — the phase of the wave functional (Eq. 16); the drift potential recovers as `φ = Φ + ½ log ρ`
 (`driftPotential_eq`);
* the **wave functional** `ψ = √ρ e^{iΦ}` (`edWaveFunction`) reconstructs the quantum state, and its **modulus
 squared is the probability** `|ψ|² = ρ` (`edWaveFunction_modulus_sq`) — the Born rule emerging from entropic
 dynamics, `ρ = |ψ|²`, the Madelung/complex-action polar form `ψ = √ρ e^{iΦ}`;
* **entropic time is proper time** `α_x = 1/δξ_x^⊥` (`edMultiplier_eq_inverse_properTime`), so the fluctuation
 variance is `⟨Δw²⟩ = δξ^⊥/g^{1/2}` (Eq. 13) — the local duration is the invariant proper time along the normal.

So the reconstruction of QFT in curved spacetime assembles the entropic probability and drift potential into the
complex wave functional `ψ = √ρ e^{iΦ}` with `|ψ|² = ρ`, evolving in local entropic (proper) time — the
information-based route to the quantum state, on the arc's complex-action / Madelung structure.

* **§A — the current potential and drift potential** (`currentPotential`, `driftPotential_eq`).
* **§B — the wave functional and the Born rule** (`edWaveFunction`, `edWaveFunction_modulus_sq`).
* **§C — entropic time is proper time** (`edMultiplier_eq_inverse_properTime`).

The current-potential relation, the wave-functional polar form, and the Born rule `|ψ|² = ρ`
are exact algebra; the local-time Fokker–Planck evolution (Eq. 16), the ensemble Hamiltonian (Eq. 20), and the
DHKT hypersurface-deformation algebra (Eqs. 24–26) are *recorded*, not derived. No new axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §3 (Eqs. 13, 16; wave functional, entropic/proper time). Repo
 structure: `EntropicTime.EntropicDynamicsTransitionProbability`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

/-! ## §A — the current potential and drift potential -/

/-- **The current (phase) potential** `Φ = φ − ½ log ρ` (Ipek–Abedi–Caticha Eq. 16) — the drift potential `φ`
minus the osmotic term `log ρ^{1/2} = ½ log ρ`; the Hamilton–Jacobi functional / phase of the wave functional. -/
noncomputable def currentPotential (φ ρ : ℝ) : ℝ := φ - (1 / 2) * Real.log ρ

/-- **[The drift potential is the current plus the osmotic term] `φ = Φ + ½ log ρ`.** The entropic drift potential
decomposes into the current (phase) potential and the osmotic (diffusion) contribution. -/
theorem driftPotential_eq (φ ρ : ℝ) : currentPotential φ ρ + (1 / 2) * Real.log ρ = φ := by
  unfold currentPotential; ring

/-! ## §B — the wave functional and the Born rule -/

/-- **The entropic-dynamics wave functional** `ψ = √ρ · e^{iΦ}` (Ipek–Abedi–Caticha §3) — the complex quantum
state reconstructed from the probability `ρ` and the current (phase) potential `Φ`, in Madelung polar form. -/
noncomputable def edWaveFunction (ρ Φ : ℝ) : ℂ := (Real.sqrt ρ : ℂ) * Complex.exp ((Φ : ℂ) * Complex.I)

/-- **[The Born rule from entropic dynamics] `|ψ|² = ρ`.** The modulus squared of the reconstructed wave
functional returns the entropic probability: `ρ = |ψ|²` — the Born rule emerging from the information-based
dynamics, the probability being the squared magnitude of `ψ = √ρ e^{iΦ}`. -/
theorem edWaveFunction_modulus_sq (ρ Φ : ℝ) (hρ : 0 ≤ ρ) : ‖edWaveFunction ρ Φ‖ ^ 2 = ρ := by
  have hexp : ‖Complex.exp ((Φ : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  unfold edWaveFunction
  rw [norm_mul, hexp, mul_one]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt hρ

/-! ## §C — entropic time is proper time -/

/-- **The maximum-entropy multiplier is the inverse proper-time duration** `α_x = 1/δξ_x^⊥`
(Ipek–Abedi–Caticha Eq. 13) — the local duration between two instants is the invariant proper time `δξ^⊥` along
the surface normal, so the fluctuation variance is `⟨Δw²⟩ = δξ^⊥/g^{1/2}`. -/
noncomputable def edMultiplierFromProperTime (properTime : ℝ) : ℝ := 1 / properTime

/-- **[Entropic time is proper time] `α_x · δξ_x^⊥ = 1`.** The maximum-entropy multiplier is the reciprocal of the
proper-time duration along the normal: the local entropic time interval is the invariant proper time (Eq. 13). -/
theorem edMultiplier_eq_inverse_properTime (properTime : ℝ) (h : properTime ≠ 0) :
    edMultiplierFromProperTime properTime * properTime = 1 := by
  unfold edMultiplierFromProperTime
  field_simp

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

end

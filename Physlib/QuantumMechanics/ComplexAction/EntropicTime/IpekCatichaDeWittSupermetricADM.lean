/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic

/-!
# The DeWitt supermetric and the ADM canonical gravity of entropic dynamics coupled to gravity (Ipek–Caticha)

Formalizes the **gravitational (ADM / geometrodynamics) sector** of Ipek–Caticha (*The Entropic Dynamics of
Quantum Scalar Fields Coupled to Gravity*, arXiv:2006.05036), the canonical gravity to which the entropic-dynamics
quantum matter (`EntropicDynamicsWaveFunctionReconstruction`, the wave functional `Ψ = ρ^{1/2}e^{iΦ}`) is coupled.
Their gravitational super-Hamiltonian (Eqs. 64–66) has kinetic term the **DeWitt supermetric contraction**

`G_{ijkl} π^{ij} π^{kl} · √g = 2 π^{ij}π_{ij} − π² = 2 Tr(M²) − (Tr M)²`,

where `M = π^i_j` is the mixed gravitational momentum. The essential structural fact — the reason canonical gravity
is subtle — is that this supermetric is **indefinite (Lorentzian)**: the trace (conformal) direction has *negative*
kinetic energy while the trace-free (graviton) directions are *positive*. This is the Wheeler–DeWitt
conformal-factor problem, here in the `n = 3` spatial matrix representation.

* the **DeWitt kinetic form** `𝒦(M) = 2 Tr(M²) − (Tr M)²` (`deWittKinetic`);
* the **conformal direction is negative** `𝒦(c·1) = −3c² ≤ 0` (`deWittKinetic_conformal`,
 `deWittKinetic_conformal_nonpos`) — the pure-trace (conformal factor) momentum has negative DeWitt norm;
* a **trace-free direction is positive** `𝒦(diag(1,−1,0)) = 4 > 0` (`deWittKinetic_traceless_pos`) — the transverse
 graviton momentum has positive DeWitt norm;
* so the **supermetric is indefinite** (`deWittKinetic_indefinite`): it takes both signs — the Lorentzian signature
 of superspace;
* the **extrinsic-curvature ↔ momentum inversion** (Eqs. 85/86): `K = (Tr M)·1 − 2M` inverts to
 `M = ½((Tr K)·1 − K)` (`admExtrinsicMixed`, `admExtrinsicMixed_trace`, `admMomentum_from_extrinsic`) — the
 canonical momentum is the trace-reversed extrinsic curvature.

So the gravity to which entropic-dynamics matter couples includes the indefinite DeWitt supermetric (conformal
negative, graviton positive) and the trace-reversal relation between the canonical momentum `π^{ij}` and the
extrinsic curvature `K_{ij}` — the ADM geometrodynamics of the Ipek–Caticha model.

* **§A — the DeWitt supermetric and its indefinite signature** (`deWittKinetic`, `deWittKinetic_conformal`,
 `deWittKinetic_traceless_pos`, `deWittKinetic_indefinite`).
* **§B — the extrinsic-curvature ↔ momentum inversion** (`admExtrinsicMixed`, `admExtrinsicMixed_trace`,
 `admMomentum_from_extrinsic`).

The DeWitt kinetic form, its conformal/graviton signs, the indefiniteness, and the
trace-reversal inversion are exact `3×3` matrix-trace algebra (the mixed-momentum representation of the tensor
contractions). The full functional super-Hamiltonian, the constraint algebra, and the coupling to the quantum
state are the referenced content and the rest of the arc. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 64–66, 85–86); B.S. DeWitt (supermetric); ADM. Repo companion:
 `EntropicTime.EntropicDynamicsWaveFunctionReconstruction` (the ED matter `Ψ = ρ^{1/2}e^{iΦ}`).

No new axioms.
-/

set_option autoImplicit false

open scoped Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM

/-! ## §A — the DeWitt supermetric and its indefinite signature -/

/-- **The DeWitt supermetric kinetic form** `𝒦(M) = 2 Tr(M²) − (Tr M)²` in the mixed-momentum representation
`M = π^i_j` — the kinetic term of the ADM gravitational super-Hamiltonian (Ipek–Caticha Eq. 66,
`= 2π^{ij}π_{ij} − π²`), the norm of the gravitational momentum in the DeWitt supermetric. -/
noncomputable def deWittKinetic (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  2 * (M * M).trace - (M.trace) ^ 2

/-- **[The conformal direction has negative DeWitt norm] `𝒦(c·1) = −3c²`.** The pure-trace (conformal factor)
momentum `M = c·1` has *negative* kinetic energy in the DeWitt supermetric — the wrong-sign conformal mode of
Wheeler–DeWitt superspace. -/
theorem deWittKinetic_conformal (c : ℝ) :
    deWittKinetic (c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = -3 * c ^ 2 := by
  unfold deWittKinetic
  simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat]
  ring

/-- **[The conformal direction is non-positive] `𝒦(c·1) ≤ 0`.** -/
theorem deWittKinetic_conformal_nonpos (c : ℝ) :
    deWittKinetic (c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ≤ 0 := by
  rw [deWittKinetic_conformal]
  nlinarith [sq_nonneg c]

/-- **[A trace-free direction has positive DeWitt norm] `𝒦(diag(1,−1,0)) = 4 > 0`.** The transverse (trace-free)
gravitational momentum has *positive* kinetic energy — the physical graviton direction of the DeWitt supermetric. -/
theorem deWittKinetic_traceless_pos :
    0 < deWittKinetic (Matrix.diagonal ![(1 : ℝ), -1, 0]) := by
  unfold deWittKinetic
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Matrix.trace_diagonal]
  simp [Fin.sum_univ_three]

/-- **[The DeWitt supermetric is indefinite (Lorentzian)].** It takes a negative value on the conformal direction
and a positive value on a trace-free direction — superspace has a Lorentzian, not Riemannian, supermetric. -/
theorem deWittKinetic_indefinite :
    (∃ M : Matrix (Fin 3) (Fin 3) ℝ, deWittKinetic M < 0)
      ∧ (∃ M : Matrix (Fin 3) (Fin 3) ℝ, 0 < deWittKinetic M) :=
  ⟨⟨(1 : Matrix (Fin 3) (Fin 3) ℝ), by
      have := deWittKinetic_conformal 1; rw [one_smul] at this; rw [this]; norm_num⟩,
   ⟨Matrix.diagonal ![(1 : ℝ), -1, 0], deWittKinetic_traceless_pos⟩⟩

/-! ## §B — the extrinsic-curvature ↔ momentum inversion -/

/-- **The mixed extrinsic curvature** `K^i_j = (Tr M)·δ^i_j − 2 M^i_j` (Ipek–Caticha Eq. 85, up to the `κ/√g`
factor) — the trace-reversal of the mixed gravitational momentum `M = π^i_j`. -/
noncomputable def admExtrinsicMixed (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  M.trace • (1 : Matrix (Fin 3) (Fin 3) ℝ) - (2 : ℝ) • M

/-- **[The extrinsic-curvature trace equals the momentum trace] `Tr K = Tr M`.** In `n = 3`,
`Tr((Tr M)·1 − 2M) = 3 Tr M − 2 Tr M = Tr M` — the trace of the trace-reversal returns the original trace. -/
theorem admExtrinsicMixed_trace (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (admExtrinsicMixed M).trace = M.trace := by
  unfold admExtrinsicMixed
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    Nat.cast_ofNat]
  ring

/-- **[The momentum is the trace-reversed extrinsic curvature] `M = ½((Tr K)·1 − K)`** (Ipek–Caticha Eq. 86). The
extrinsic-curvature ↔ momentum relation `K = (Tr M)·1 − 2M` inverts to recover the gravitational momentum, using
the trace relation `Tr K = Tr M`. -/
theorem admMomentum_from_extrinsic (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (1 / 2 : ℝ) • ((admExtrinsicMixed M).trace • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - admExtrinsicMixed M) = M := by
  rw [admExtrinsicMixed_trace]
  unfold admExtrinsicMixed
  module

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM

end

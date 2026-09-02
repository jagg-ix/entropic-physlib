/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

/-!
# The Bender–Dunne time-operator domain on the Nagao–Nielsen complex `p, q`

The Bender–Dunne / time-of-arrival domain (`BenderDunneTimeOperatorDomain`) on the **complexified phase space** of
Nagao–Nielsen (`ComptonClock.NagaoNielsenMassShellCone`, `q̂|q⟩ = q|q⟩` for **complex** `q`, arXiv:1304.4017).
The Bender–Dunne moment domain `{φ : m₀ φ = 0 ∧ m₁ φ = 0}` was formalized over an *arbitrary field*; taking the
field to be `ℂ` — the Nagao–Nielsen setting — the first-moment functional is weighted by the **complex coordinate**
`q = E/c + i·p`, whose real part is the energy and imaginary part the momentum. The Bender–Dunne two-vector
solvability (Eq. 13) then holds verbatim on the NN complex phase space.

* **§A — the NN complex coordinate `q = E/c + i·p` (Eqs. 2.1–2.7).** `nnComplexCoordinate E p c`; **`nnComplexCoordinate_lorentzForm`** (`nnLorentzForm q = (E/c)² − p²`, the `(Re q)² − (Im q)²` Nagao–Nielsen mass-shell
  form — `= (mc)²` on shell, the forward cone `nnConverges` being the NN contour).
* **§B — the NN complex first-moment functional.** `nnMomentForm q φ = ∑_k q_k φ_k`, the `ℂ`-linear moment weighted
  by the complex coordinate `q` (`nnMomentForm_apply`).
* **§C — the Bender–Dunne domain on the NN complex phase space.** `nnBenderDunneDomain q = benderDunneDomain
  sumForm (nnMomentForm q)`, the two-moment domain `{φ : ∑φ = 0 ∧ ∑ q_k φ_k = 0}` with the NN complex weight;
  **`mem_nnBenderDunneDomain_iff`** and **`nn_benderDunne_basis_mem_domain`** — the antisymmetric basis vector lies
  in the NN domain iff the **complex** determinant `∑φ₁ · ∑q φ₂ = ∑φ₂ · ∑q φ₁` vanishes (Eq. 13 over `ℂ`).

The time-of-arrival operator `T` these domains support solves `[T, H] = iℏ`, the same passage-time-type CCR that
the Nagao–Nielsen Feynman propagator realizes (`NonHermitianComplexAction.PropagatorTimeOperator.fpi_liouvillian_age_ccr`,
`i[L,T] = I`): the NN complex-action time operator and the Bender–Dunne time-of-arrival operator are two faces of
the same energy–time conjugacy on the complexified phase space.

**Honest layering.** `nnComplexCoordinate_lorentzForm` is an exact `Complex`-part identity; §B–§C instantiate the
field-general Bender–Dunne domain (`benderDunne_basis_mem_domain`) at `𝕜 = ℂ` with the NN complex coordinate as
the moment weight. The NN contour deformation and complex-action convergence (the analytic content of the
Nagao–Nielsen theory) are recorded not re-derived; the domain construction is exact and field-agnostic.

## References

* Bunao & Galapon, arXiv:1509.00340 (2015); Nagao & Nielsen, arXiv:1304.4017. Bridges
  `TimeOperator.BenderDunneTimeOperatorDomain` and `ComptonClock.NagaoNielsenMassShellCone`.


-/

set_option autoImplicit false

open Complex
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenBenderDunneComplexMoment

variable {n : ℕ}


/-- The **Nagao–Nielsen complex coordinate** `q_k = E_k/c + i·p_k` (Eqs. 2.1–2.7): the complexified phase-space
coordinate whose real part is the energy `E/c` and imaginary part the momentum `p`. -/
noncomputable def nnComplexCoordinate (E p : Fin n → ℝ) (c : ℝ) : Fin n → ℂ :=
  fun k => (E k / c : ℂ) + Complex.I * (p k : ℂ)

/-- **The NN mass-shell form of the complex coordinate** `nnLorentzForm(E/c + i·p) = (E/c)² − p²` — the
`(Re q)² − (Im q)²` Nagao–Nielsen Lorentzian form (`= (mc)²` on shell), whose positivity `nnConverges` is the NN
contour/cone. -/
lemma nnComplexCoordinate_lorentzForm (E p : Fin n → ℝ) (c : ℝ) (k : Fin n) :
    nnLorentzForm (nnComplexCoordinate E p c k) = (E k / c) ^ 2 - (p k) ^ 2 := by
  unfold nnLorentzForm nnComplexCoordinate
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]


/-- The **Nagao–Nielsen first-moment functional** `φ ↦ ∑_k q_k φ_k`, `ℂ`-linear, weighted by the complex
coordinate `q` — the `∫ q φ` moment of the Bender–Dunne domain evaluated on the complexified NN phase space. -/
noncomputable def nnMomentForm (q : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun φ := ∑ k, q k * φ k
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm]

@[simp] lemma nnMomentForm_apply (q φ : Fin n → ℂ) : nnMomentForm q φ = ∑ k, q k * φ k := rfl


/-- The **Bender–Dunne / time-of-arrival domain on the Nagao–Nielsen complex phase space**
`{φ : ∑φ = 0 ∧ ∑ q_k φ_k = 0}` — the two-moment domain with the zeroth moment `sumForm` and the NN complex
first moment `nnMomentForm q`. -/
noncomputable def nnBenderDunneDomain (q : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  benderDunneDomain sumForm (nnMomentForm q)

/-- **Membership in the NN Bender–Dunne domain** `φ ∈ nnBenderDunneDomain q ↔ ∑φ = 0 ∧ ∑ q_k φ_k = 0`. -/
lemma mem_nnBenderDunneDomain_iff (q φ : Fin n → ℂ) :
    φ ∈ nnBenderDunneDomain q ↔ (∑ k, φ k = 0 ∧ ∑ k, q k * φ k = 0) := by
  rw [nnBenderDunneDomain, mem_benderDunneDomain_iff, sumForm_apply, nnMomentForm_apply]

/-- **The Bender–Dunne two-vector solvability on the NN complex phase space (Eq. 13 over `ℂ`)** — the
antisymmetric combination `(∑φ₂)·φ₁ − (∑φ₁)·φ₂` lies in the NN domain iff the **complex** determinant
`(∑φ₁)(∑ q φ₂) = (∑φ₂)(∑ q φ₁)` vanishes: the Bender–Dunne domain construction transports verbatim from the real
line to the Nagao–Nielsen complex coordinate. -/
lemma nn_benderDunne_basis_mem_domain (q φ₁ φ₂ : Fin n → ℂ) :
    ((sumForm φ₂) • φ₁ - (sumForm φ₁) • φ₂) ∈ nnBenderDunneDomain q
      ↔ sumForm φ₁ * nnMomentForm q φ₂ = sumForm φ₂ * nnMomentForm q φ₁ :=
  benderDunne_basis_mem_domain sumForm (nnMomentForm q) φ₁ φ₂

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenBenderDunneComplexMoment

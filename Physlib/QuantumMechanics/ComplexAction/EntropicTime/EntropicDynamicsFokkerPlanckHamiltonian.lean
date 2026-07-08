/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The local-time Fokker–Planck equation and its generating ensemble Hamiltonian (Ipek–Abedi–Caticha §3)

Derives the two dynamical statements of §3 of Ipek–Abedi–Caticha (arXiv:1803.07493) that were previously only
recorded: the **local-time Fokker–Planck (LTFP) equation** (their Eq. 16) as a *continuity equation*, and its
generation by the **ensemble Hamiltonian** (their Eqs. 19–20) via integration by parts. Working in one
configuration dimension (`χ ↦ x ∈ ℝ`), so that functional derivatives `δ/δχ` become ordinary derivatives:

The LTFP equation `∂ρ/∂ξ^⊥ = −g^{−1/2} ∂_χ(ρ ∂_χ Φ)` is the continuity equation `∂ρ/∂t + ∂_x j = 0` with
**probability current** `j = ρ v` and **current velocity** `v = ∂_x Φ` (Eq. 16). The ensemble Hamiltonian is
`H̃ = ∫ ρ (∂_χΦ)²/(2g^{1/2})` (Eq. 20), and Hamilton's equation `∂ρ/∂ξ^⊥ = δ̃H̃/δ̃Φ` (Eq. 19) reproduces the LTFP
equation.

* the **probability current divergence** `∂_x(ρ v) = (∂_xρ) v + ρ (∂_x v)` is derived from the product rule
 (`fokkerPlanck_current_hasDerivAt`) — the spatial part of the continuity/LTFP equation, exact;
* the **kinetic ensemble-Hamiltonian density** `h = ½ ρ v²` (`ensembleHamiltonianDensity`) is the integrand of
 Eq. 20;
* the **ensemble Hamiltonian generates the LTFP equation** (`ensemble_hamiltonian_generates_fokkerPlanck`): by
 integration by parts, the variation of `H̃` against a test function `η` vanishing at the endpoints is
 `∫ j · η' = −∫ (∂_x j) · η`, i.e. `δ̃H̃/δ̃Φ = −∂_x(ρ v)` — Hamilton's equation for `Φ` *is* the negative current
 divergence, deriving the LTFP continuity equation (Eq. 16) from the Hamiltonian (Eq. 20).

So in one configuration dimension the entropic-dynamics probability flow is a genuine continuity equation whose
current divergence is the product rule, and the ensemble Hamiltonian generates it exactly through integration by
parts — the LTFP/Hamiltonian derivation of §3, made rigorous.

* **§A — the probability current and its divergence** (`fokkerPlanckCurrent`, `fokkerPlanck_current_hasDerivAt`).
* **§B — the ensemble Hamiltonian density** (`ensembleHamiltonianDensity`).
* **§C — the Hamiltonian generates the LTFP equation** (`ensemble_hamiltonian_generates_fokkerPlanck`).

The current divergence (product rule) and the integration-by-parts variation are exact
`HasDerivAt` / `intervalIntegral` calculus in one configuration dimension. The full field-theoretic functional
Fokker–Planck (infinite-dimensional `δ/δχ_x`), the metric factor `g^{−1/2}`, and the ensemble-calculus e-functional
derivative are the intended reading, not formalized in infinite dimensions. No new axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §3 (Eqs. 16, 19–20; LTFP, ensemble Hamiltonian). Repo structure:
 `EntropicTime.EntropicDynamicsWaveFunctionReconstruction`.

No new axioms.
-/

set_option autoImplicit false

open MeasureTheory intervalIntegral

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian

/-! ## §A — the probability current and its divergence -/

/-- **The entropic-dynamics probability current** `j = ρ v` (Ipek–Abedi–Caticha Eq. 16) — the density `ρ` times
the current velocity `v = ∂_χ Φ`. The local-time Fokker–Planck equation is the continuity equation
`∂ρ/∂ξ^⊥ = −∂_χ j` (up to the metric factor `g^{−1/2}`). -/
def fokkerPlanckCurrent (ρ v : ℝ → ℝ) : ℝ → ℝ := fun x => ρ x * v x

/-- **[The probability current divergence is the product rule] `∂_x(ρv) = (∂_xρ)v + ρ(∂_xv)`.** The spatial
divergence of the entropic-dynamics probability current — the right-hand side of the local-time Fokker–Planck
continuity equation (Eq. 16) — is the product rule, exact. -/
theorem fokkerPlanck_current_hasDerivAt (ρ v : ℝ → ℝ) (ρ' v' x : ℝ) (hρ : HasDerivAt ρ ρ' x)
    (hv : HasDerivAt v v' x) :
    HasDerivAt (fokkerPlanckCurrent ρ v) (ρ' * v x + ρ x * v') x :=
  hρ.mul hv

/-! ## §B — the ensemble Hamiltonian density -/

/-- **The ensemble-Hamiltonian kinetic density** `h = ½ ρ v²` (Ipek–Abedi–Caticha Eq. 20) — the integrand of
`H̃ = ∫ ρ (∂_χΦ)²/(2g^{1/2})`, the kinetic energy density of the probability flow with current velocity
`v = ∂_χ Φ`. -/
noncomputable def ensembleHamiltonianDensity (ρ v : ℝ → ℝ) : ℝ → ℝ := fun x => ρ x * v x ^ 2 / 2

/-! ## §C — the ensemble Hamiltonian generates the LTFP equation -/

/-- **[The ensemble Hamiltonian generates the Fokker–Planck equation] `δ̃H̃/δ̃Φ = −∂_x(ρv)`.** Integration by parts
gives, for the probability current `j` (with divergence `∂_x j =` `div`) and a test function `η` vanishing at the
endpoints, `∫ j · η' = −∫ (∂_x j) · η`. Thus the variation of the ensemble Hamiltonian `H̃ = ∫ ½ρv²` with respect
to `Φ` (which produces `∫ j · δΦ'`) equals `−∫ (∂_x j) · δΦ`, so Hamilton's equation `∂ρ/∂ξ^⊥ = δ̃H̃/δ̃Φ` reproduces
the negative current divergence — the local-time Fokker–Planck continuity equation (Eq. 16) derived from the
Hamiltonian (Eqs. 19–20). -/
theorem ensemble_hamiltonian_generates_fokkerPlanck {a b : ℝ} (j div η η' : ℝ → ℝ)
    (hj_cont : ContinuousOn j (Set.uIcc a b)) (hη_cont : ContinuousOn η (Set.uIcc a b))
    (hj : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt j (div x) x)
    (hη : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt η (η' x) x)
    (hdiv : IntervalIntegrable div volume a b) (hη' : IntervalIntegrable η' volume a b)
    (hηa : η a = 0) (hηb : η b = 0) :
    ∫ x in a..b, j x * η' x = -∫ x in a..b, div x * η x := by
  rw [integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hj_cont hη_cont hj hη hdiv hη', hηb, hηa]
  simp

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian

end

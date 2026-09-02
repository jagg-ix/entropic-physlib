/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.FluidDynamics.FluidFlow.Momentum

/-!
# Convective energy neutrality: the Navier–Stokes nonlinearity transports but never produces kinetic energy

The energy inequality of the Landau–Lifshitz–Navier–Stokes equation (B. Gess, D. Heydecker, Z. Wu,
arXiv:2311.02223, Eq. 1.3, `½‖u(t)‖² + ∫‖∇u‖² ≤ ½‖u(0)‖² − ∫⟨∇u,g⟩`) is obtained by pairing the momentum
equation against `u`. It has three structural inputs: the viscous term gives the dissipation `−‖∇u‖²`
(`ComplexAction.NavierStokes.ViscousDissipationFisherInformation`), the pressure does no work on a
divergence-free field, and — the piece here — the **convective term is energy-neutral**: it moves kinetic
energy around without creating or destroying it.

The pointwise statement is that pairing the nonlinearity `(u·∇)u` (physlib's
`FluidFlow.convectiveTerm = ∑ⱼ uⱼ ∂[j] u`) against the velocity is exactly the advective transport of the
kinetic-energy density `½‖u‖²`:

  `⟨u, (u·∇)u⟩ = ½ ∑ⱼ uⱼ ∂[j]‖u‖² = (u·∇)(½‖u‖²)`.

The right-hand side is a pure directional derivative of `½‖u‖²` along `u`; for a divergence-free field it is a
total divergence `div(½‖u‖² u)` and hence integrates to zero on a closed domain — so the nonlinearity drops
out of the energy balance, leaving `d/dt ½‖u‖² = −ν‖∇u‖²` (Leray's energy identity). This is precisely why the
supercritical Navier–Stokes nonlinearity never appears as a source in the energy estimate.

Reuses (GREP-first, no duplication) `FluidFlow.convectiveTerm` (`FluidFlow.Momentum`), `Space.deriv` (`∂[j]`), and
Mathlib's inner-product calculus `fderiv_inner_apply`.

* `deriv_normSq_field` — the field chain rule `∂[j]‖u‖² = 2⟨u, ∂[j]u⟩`.
* `inner_velocity_convectiveTerm` — the energy-neutrality identity `⟨u, (u·∇)u⟩ = ½ ∑ⱼ uⱼ ∂[j]‖u‖²`.

## References

* B. Gess, D. Heydecker, Z. Wu, arXiv:2311.02223, Eq. 1.3; J. Leray, Acta Math. 63 (1934) 193 (the energy
  identity, in which the convective term cancels). Carriers: `FluidFlow.convectiveTerm`, `Space.deriv`,
  Mathlib `fderiv_inner_apply`, `ComplexAction.NavierStokes.ViscousDissipationFisherInformation` (the viscous
  half of the balance).
-/

set_option autoImplicit false

open Space Time InnerProductSpace

@[expose] public section

noncomputable section

namespace FluidDynamics.NavierStokes

/-- **[Field chain rule for the squared norm] `∂[j]‖u‖² = 2⟨u, ∂[j]u⟩`.** The spatial derivative of the
kinetic-energy density (up to the factor `½`) of a differentiable velocity field, via `fderiv_inner_apply`
on `‖u‖² = ⟨u, u⟩`. -/
lemma deriv_normSq_field {d : ℕ} (u : Space d → EuclideanSpace ℝ (Fin d)) (x : Space d) (j : Fin d)
    (hu : DifferentiableAt ℝ u x) :
    ∂[j] (fun y => ‖u y‖ ^ 2) x = 2 * ⟪u x, ∂[j] u x⟫_ℝ := by
  have hnorm : (fun y => ‖u y‖ ^ 2) = fun y => ⟪u y, u y⟫_ℝ := by
    funext y; exact (real_inner_self_eq_norm_sq (u y)).symm
  rw [hnorm, Space.deriv_eq_fderiv_basis, fderiv_inner_apply (𝕜 := ℝ) hu hu,
    ← Space.deriv_eq_fderiv_basis, real_inner_comm (∂[j] u x) (u x)]
  ring

/-- **[Convective energy neutrality] `⟨u, (u·∇)u⟩ = ½ ∑ⱼ uⱼ ∂[j]‖u‖²`.** Pairing the Navier–Stokes nonlinear
transport term `FluidFlow.convectiveTerm = (u·∇)u = ∑ⱼ uⱼ ∂[j]u` against the velocity equals the advective
transport of the kinetic-energy density `½‖u‖²`. The nonlinearity therefore produces no net kinetic energy:
for a divergence-free field the right-hand side is a total divergence and integrates to zero, so the convective
term cancels from the Leray energy balance (Eq. 1.3), leaving the viscous dissipation alone. -/
theorem inner_velocity_convectiveTerm {d : ℕ} (fluid : FluidFlow d) (t : Time) (x : Space d)
    (hu : DifferentiableAt ℝ (fluid.velocity t) x) :
    ⟪fluid.velocity t x, FluidFlow.convectiveTerm d fluid t x⟫_ℝ
      = (1 / 2) * ∑ j, fluid.velocity t x j * ∂[j] (fun y => ‖fluid.velocity t y‖ ^ 2) x := by
  simp only [FluidFlow.convectiveTerm, inner_sum, real_inner_smul_right]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deriv_normSq_field (fluid.velocity t) x j hu]
  ring

/-! ### The divergence Leibniz rule and the div-free conservative form -/

/-- **[Product rule for the directional derivative] `∂[i](f·g) = (∂[i]f)·g + f·(∂[i]g)`** for scalar fields,
via Mathlib's `fderiv_fun_mul`. -/
lemma deriv_mul_field {d : ℕ} (f g : Space d → ℝ) (x : Space d) (i : Fin d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ∂[i] (fun y => f y * g y) x = ∂[i] f x * g x + f x * ∂[i] g x := by
  rw [Space.deriv_eq_fderiv_basis, fderiv_fun_mul hf hg]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    ← Space.deriv_eq_fderiv_basis]
  ring

/-- **[The gradient pairs to a coordinate sum] `⟨∇φ, v⟩ = ∑ᵢ (∂[i]φ)·vᵢ`.** The real inner product of the
gradient `∇φ` (components `∂[i]φ`, `Space.grad_apply`) with a vector, expanded via `PiLp.inner_apply`. -/
lemma inner_grad_eq_sum {d : ℕ} (φ : Space d → ℝ) (v : EuclideanSpace ℝ (Fin d)) (x : Space d) :
    ⟪Space.grad φ x, v⟫_ℝ = ∑ i, ∂[i] φ x * v i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Space.grad_apply, RCLike.inner_apply, conj_trivial]
  ring

/-- **[Divergence Leibniz rule] `div(φ u) = ⟨∇φ, u⟩ + φ · div u`.** The product rule for the divergence of a
scalar field `φ` times a vector field `u`: `∂ᵢ(φ uᵢ) = (∂ᵢφ) uᵢ + φ ∂ᵢuᵢ`, summed over `i`. This is the
identity that turns the advective kinetic-energy transport into a total divergence for divergence-free flow. -/
theorem div_smul_field {d : ℕ} (φ : Space d → ℝ) (u : Space d → EuclideanSpace ℝ (Fin d)) (x : Space d)
    (hφ : DifferentiableAt ℝ φ x) (hcomp : ∀ i, DifferentiableAt ℝ (fun y => (u y) i) x) :
    Space.div (fun y => φ y • u y) x = ⟪Space.grad φ x, u x⟫_ℝ + φ x * Space.div u x := by
  rw [inner_grad_eq_sum]
  simp only [Space.div, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [deriv_mul_field φ (fun y => (u y) i) x i hφ (hcomp i)]

/-- **[Div-free conservative form of the convective term] `2⟨u, (u·∇)u⟩ = div(‖u‖² u)`.** For a
divergence-free velocity field, the kinetic-energy production by the nonlinearity is a *total divergence*: the
advective transport `⟨u, (u·∇)u⟩ = ½(u·∇)‖u‖²` (`inner_velocity_convectiveTerm`) equals `½ div(‖u‖² u)` by the
Leibniz rule (`div_smul_field`) with `div u = 0`. Hence on a closed/periodic domain the convective term
integrates to zero and drops out of the Leray energy balance (Eq. 1.3), leaving `d/dt ½‖u‖² = −ν‖∇u‖²`. -/
theorem convectiveTerm_conservative_form {d : ℕ} (fluid : FluidFlow d) (t : Time) (x : Space d)
    (hu : DifferentiableAt ℝ (fluid.velocity t) x)
    (hcomp : ∀ i, DifferentiableAt ℝ (fun y => (fluid.velocity t y) i) x)
    (hdivfree : Space.div (fluid.velocity t) x = 0) :
    2 * ⟪fluid.velocity t x, FluidFlow.convectiveTerm d fluid t x⟫_ℝ
      = Space.div (fun y => ‖fluid.velocity t y‖ ^ 2 • fluid.velocity t y) x := by
  have hnormsq : DifferentiableAt ℝ (fun y => ‖fluid.velocity t y‖ ^ 2) x := by
    have h : (fun y => ‖fluid.velocity t y‖ ^ 2)
        = fun y => ⟪fluid.velocity t y, fluid.velocity t y⟫_ℝ := by
      funext y; exact (real_inner_self_eq_norm_sq _).symm
    rw [h]; exact hu.inner ℝ hu
  rw [div_smul_field (fun y => ‖fluid.velocity t y‖ ^ 2) (fluid.velocity t) x hnormsq hcomp,
    hdivfree, mul_zero, add_zero, inner_grad_eq_sum,
    inner_velocity_convectiveTerm fluid t x hu, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end FluidDynamics.NavierStokes

end

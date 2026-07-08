/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp

/-!
# The comoving frame: linear dissipation as a volume-preserving flow in a new time (Axenides–Floratos §3.1)

The full Lorenz/Rössler flow is integrated formally through the Liouville operator
`L = v·∇` (Axenides, Floratos, JHEP 04 (2010) 036, Eqs. 3.9–3.14): `x(t) = e^{tL} x₀`, with convergent Taylor
series `x(t) = Σ xₖ tᵏ/k!`, `xₖ = Lᵏ x₀`. For the *linear* part of the dissipation the integration is
explicit (Eqs. 3.29–3.33): writing the Nambu–dissipative system `ẋ = (∇H₁×∇H₂) − αx`, etc. in the **comoving
frame** `x = e^{−αt}u, y = e^{−βt}v, z = e^{−γt}w` turns it into a **volume-preserving** flow
`d/dτ(u,v,w) = ∇H₁×∇H₂` in the new time `τ = e^{(α+β+γ)t}/(α+β+γ)` (Eq. 3.33).

This file formalizes the concrete analytic content of that reparametrization (the abstract operator
exponential `e^{tL}` of Eqs. 3.9–3.14 is described, not formalized):

* **§A — the comoving substitution.** `comoving_deriv`: if `x(t) = e^{−αt}u(t)` then
  `ẋ = e^{−αt}(u̇ − αu)`; `comoving_dissipation_cancel`: `ẋ + αx = e^{−αt}u̇` — the linear dissipation `−αx`
  is exactly absorbed, leaving only the comoving velocity.
* **§B — the new time variable** (Eq. 3.33). `comovingTime_deriv`: `τ = e^{st}/s` (`s = α+β+γ ≠ 0`) has
  `dτ/dt = e^{st}`.
* **§C — volume preservation.** `comoving_jacobian`: the comoving volume factor
  `e^{−αt}e^{−βt}e^{−γt} = e^{−st}` (the contraction of phase-space volume by the dissipation);
  `comoving_volume_reciprocal`: `e^{−st}·(dτ/dt) = e^{−st}·e^{st} = 1` — the new time `τ` exactly undoes the
  volume contraction, so the flow is volume-preserving in `(u,v,w,τ)`.

The exponential reparametrization `τ ∝ e^{st}` is the integrating clock that converts the irreversible
(volume-contracting) dissipation into a reversible (volume-preserving) flow — the same role the entropic time
plays across the arc.

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §3.1, Eqs. 3.9–3.14, 3.29–3.33.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LiouvilleComoving

/-! ## §A — the comoving substitution `x = e^{−αt}u` (Eqs. 3.29–3.30) -/

/-- **[Comoving derivative]** if `x(t) = e^{−αt}u(t)` then `ẋ = e^{−αt}(u̇ − αu)` — the product rule for the
comoving substitution that strips the linear dissipation. -/
theorem comoving_deriv (α : ℝ) {u : ℝ → ℝ} {u' t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => Real.exp (-(α * s)) * u s)
      (Real.exp (-(α * t)) * (u' - α * u t)) t := by
  have hinner : HasDerivAt (fun s => -(α * s)) (-α) t := by
    exact (((hasDerivAt_id t).const_mul α).neg).congr_deriv (by ring)
  have hexp : HasDerivAt (fun s => Real.exp (-(α * s))) (Real.exp (-(α * t)) * (-α)) t := by
    exact hinner.exp.congr_deriv (by ring)
  have hmul := hexp.mul hu
  exact hmul.congr_deriv (by ring)

/-- **[Dissipation cancels in the comoving frame]** `ẋ + αx = e^{−αt}u̇`: adding back the linear dissipation
`+αx` to the comoving derivative leaves only `e^{−αt}u̇`, the rescaled comoving velocity (Eq. 3.31). -/
theorem comoving_dissipation_cancel (α t u' ut : ℝ) :
    Real.exp (-(α * t)) * (u' - α * ut) + α * (Real.exp (-(α * t)) * ut)
      = Real.exp (-(α * t)) * u' := by
  ring

/-! ## §B — the new time variable `τ = e^{st}/s` (Eq. 3.33) -/

/-- **[New time variable]** with `s = α+β+γ ≠ 0`, the comoving time `τ = e^{st}/s` has `dτ/dt = e^{st}`: the
exponential reparametrization that rescales the contracting flow to a volume-preserving one (Eq. 3.33). -/
theorem comovingTime_deriv (s t : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun u => Real.exp (s * u) / s) (Real.exp (s * t)) t := by
  have hinner : HasDerivAt (fun u => s * u) s t := by
    simpa using (hasDerivAt_id t).const_mul s
  have hexp : HasDerivAt (fun u => Real.exp (s * u)) (Real.exp (s * t) * s) t := by
    exact hinner.exp.congr_deriv (by ring)
  have hdiv := hexp.div_const s
  exact hdiv.congr_deriv (by rw [mul_div_assoc, div_self hs, mul_one])

/-! ## §C — volume preservation in the comoving frame (Eqs. 3.31–3.33) -/

/-- **[Comoving volume factor]** the Jacobian of `(x,y,z) ↦ (u,v,w)` is the product of the three scale
factors `e^{−αt}e^{−βt}e^{−γt} = e^{−(α+β+γ)t}` — the rate at which the dissipation contracts phase-space
volume. -/
theorem comoving_jacobian (α β γ t : ℝ) :
    Real.exp (-(α * t)) * Real.exp (-(β * t)) * Real.exp (-(γ * t))
      = Real.exp (-((α + β + γ) * t)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **[Volume preservation]** the comoving volume factor `e^{−st}` times the new-time rate `dτ/dt = e^{st}`
equals `1`: the reparametrization `τ = e^{st}/s` exactly undoes the dissipative volume contraction, making the
`(u,v,w)` flow volume-preserving (Eqs. 3.31–3.33). -/
theorem comoving_volume_reciprocal (s t : ℝ) :
    Real.exp (-(s * t)) * Real.exp (s * t) = 1 := by
  rw [← Real.exp_add]
  simp

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LiouvilleComoving

end

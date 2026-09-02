/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HubbardPartialBosonization
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Hubbard flow: threshold functions, the nesting enhancement, and the Schmidt link

The next sections of Denz–Mitter–Pawlowski–Wetterich–Yamada, PRB **101**, 155115
(2020): §V (the flow of the four-fermion coupling and the nesting-driven channel
enhancement) and Appendix B (the Matsubara-summed threshold functions), welded to
the repo's Schmidt/rapidity layer.

## §A — the Fermi function (the Matsubara-summed building block, App. B)

* `fermiFunction` — `f(ξ) = 1/(e^{ξ/T} + 1)`.
* `fermiFunction_particleHole` — `f(−ξ) = 1 − f(ξ)`: the particle-hole symmetry of
  the occupation.
* `fermiFunction_zero` — `f(0) = ½`: the Fermi surface is half-occupied.
* `one_sub_two_fermi` — **`1 − 2f(ξ) = tanh(ξ/2T)`**: the occupation asymmetry is
  the hyperbolic tangent — the universal factor of every Matsubara-summed bubble.

## §B — the threshold bubbles and the nesting enhancement (§V.B, App. B)

The static particle-particle and particle-hole bubbles after Matsubara summation:
`B_PP(ξ₁,ξ₂) = (1 − f(ξ₁) − f(ξ₂))/(ξ₁+ξ₂)`,
`B_PH(ξ₁,ξ₂) = (f(ξ₁) − f(ξ₂))/(ξ₁−ξ₂)`.

* `bubblePP_diag` — the Cooper bubble at zero total momentum:
  `B_PP(ξ,ξ) = tanh(ξ/2T)/(2ξ)` — the log-divergent Cooper form.
* `nesting_bubble_equality` — **the §V.B mechanism**: with the nesting property
  `ξ_{q+Π} = −ξ_q` (`nesting_property`), the particle-hole bubble at transfer `Π`
  satisfies `B_PH(ξ, −ξ) = −B_PP(ξ, ξ)` — at half filling the antiferromagnetic
  (particle-hole at `Π`) channel carries **the same threshold function** as the
  Cooper (particle-particle at zero momentum) channel: nesting puts the AF
  instability on the Cooper channel's log footing, which is why AF order sets in
  for any `U > 0` and why the flow's kernels at `p₁ − p₂ = ±Π` lose their
  external-momentum dependence.

## §C — the Fermi-surface expansion (Eq. 31)

* `hubbardDispersion_hasDerivAt` — the dispersion is differentiable in each
  momentum component with derivative `2t·sin q` — the components of the Fermi
  velocity in `ξ_q ≈ ξ_{q_F} + v_F·(q − q_F)`.
* `fermiVelocity` — `v_F(q) = 2t(sin qₓ, sin q_y)`; on the umklapp surface at
  `(±π/2, ±π/2)` (the nesting peaks of Fig. 1) it has maximal magnitude
  components `±2t`.

## §D — the Schmidt/rapidity weld (linking to the entanglement arc)

* `fermi_schmidt_link` — **`1 − 2f(ξ) = (schmidtNumber(ξ/2T))⁻¹`**: the occupation
  asymmetry of a thermal fermion mode is the *inverse Schmidt number* at rapidity
  `η = ξ/2T` (`tanh = coth⁻¹`, on the
  `MuonAnomaly.SchmidtRapidityHyperbolicUnification` carrier). The thermal
  occupation of the Hubbard fermions and the entanglement dictionary
  (`EntropicProperDistance`, `r = λ_C log K`) run on the same hyperbolic function
  of one rapidity: every Matsubara-summed threshold function of the flow is a
  Schmidt-number datum, and the Cooper/AF bubble `tanh(ξ/2T)/(2ξ)` reads
  `1/(2ξ·K(ξ/2T))`.

## Honest scope

The Matsubara sums themselves (the `T Σₙ` → `f` step of App. B) enter through the
summed forms taken as definitions; the flow equation (Eq. 28) with its `𝒯_PP/DPH/CPH`
diagrams and the `N`-patch numerics are recorded.  Everything here is exact real
analysis/algebra on those forms.

## References

* T. Denz et al., PRB **101**, 155115 (2020): §V.B (nesting enhancement), Eq. 31
  (Fermi-surface expansion), App. B (threshold functions).
* Carriers: `HubbardPartialBosonization` (`hubbardDispersion`, `nesting_property`),
  `MuonAnomaly.SchmidtRapidityHyperbolicUnification` (`schmidtNumber`),
  `ComptonClock.EntropicProperDistance` (the Schmidt dictionary the weld feeds).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HubbardPartialBosonization
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HubbardNestingThresholds

/-! ## §A — the Fermi function -/

/-- **The Fermi function** `f(ξ) = 1/(e^{ξ/T} + 1)` — the Matsubara-summed
occupation of a fermionic mode at energy `ξ` and temperature `T`. -/
noncomputable def fermiFunction (T ξ : ℝ) : ℝ :=
  1 / (Real.exp (ξ / T) + 1)

/-- **Particle-hole symmetry of the occupation**: `f(−ξ) = 1 − f(ξ)`. -/
theorem fermiFunction_particleHole (T ξ : ℝ) :
    fermiFunction T (-ξ) = 1 - fermiFunction T ξ := by
  unfold fermiFunction
  rw [neg_div, Real.exp_neg]
  have h1 : Real.exp (ξ / T) + 1 ≠ 0 := by positivity
  have h2 : (Real.exp (ξ / T))⁻¹ + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The Fermi surface is half-occupied: `f(0) = ½`. -/
theorem fermiFunction_zero (T : ℝ) : fermiFunction T 0 = 1 / 2 := by
  unfold fermiFunction
  norm_num

/-- **The occupation asymmetry is the hyperbolic tangent**:
`1 − 2f(ξ) = tanh(ξ/2T)` — the universal factor of every Matsubara-summed threshold
function (App. B). -/
theorem one_sub_two_fermi (T ξ : ℝ) :
    1 - 2 * fermiFunction T ξ = Real.tanh (ξ / (2 * T)) := by
  unfold fermiFunction
  have hxy : ξ / T = 2 * (ξ / (2 * T)) := by
    rw [mul_div_assoc']
    rw [show 2 * ξ / (2 * T) = ξ / T from mul_div_mul_left ξ T two_ne_zero]
  rw [Real.tanh_eq, Real.exp_neg, hxy,
    show Real.exp (2 * (ξ / (2 * T)))
      = Real.exp (ξ / (2 * T)) * Real.exp (ξ / (2 * T)) by
        rw [← Real.exp_add]; ring_nf]
  have hey : 0 < Real.exp (ξ / (2 * T)) := Real.exp_pos _
  have h1 : Real.exp (ξ / (2 * T)) * Real.exp (ξ / (2 * T)) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-! ## §B — the threshold bubbles and the nesting enhancement -/

/-- **The particle-particle (Cooper) bubble** after Matsubara summation:
`B_PP(ξ₁,ξ₂) = (1 − f(ξ₁) − f(ξ₂))/(ξ₁ + ξ₂)`. -/
noncomputable def bubblePP (T ξ₁ ξ₂ : ℝ) : ℝ :=
  (1 - fermiFunction T ξ₁ - fermiFunction T ξ₂) / (ξ₁ + ξ₂)

/-- **The particle-hole bubble** after Matsubara summation:
`B_PH(ξ₁,ξ₂) = (f(ξ₁) − f(ξ₂))/(ξ₁ − ξ₂)`. -/
noncomputable def bubblePH (T ξ₁ ξ₂ : ℝ) : ℝ :=
  (fermiFunction T ξ₁ - fermiFunction T ξ₂) / (ξ₁ - ξ₂)

/-- **The Cooper form**: at zero total momentum,
`B_PP(ξ,ξ) = tanh(ξ/2T)/(2ξ)` — the log-divergent particle-particle threshold. -/
theorem bubblePP_diag (T ξ : ℝ) :
    bubblePP T ξ ξ = Real.tanh (ξ / (2 * T)) / (2 * ξ) := by
  unfold bubblePP
  rw [show 1 - fermiFunction T ξ - fermiFunction T ξ
      = 1 - 2 * fermiFunction T ξ by ring, one_sub_two_fermi,
    show ξ + ξ = 2 * ξ by ring]

/-- **The nesting enhancement** (paper §V.B): with the nesting property
`ξ_{q+Π} = −ξ_q` (`nesting_property`), the particle-hole bubble at transfer `Π`
equals minus the Cooper bubble: `B_PH(ξ, −ξ) = −B_PP(ξ, ξ)` — at half filling the
antiferromagnetic channel carries the **same threshold function** as the Cooper
channel, so the AF instability sits on the Cooper log footing and sets in for any
`U > 0`. -/
theorem nesting_bubble_equality (T ξ : ℝ) :
    bubblePH T ξ (-ξ) = -bubblePP T ξ ξ := by
  unfold bubblePH bubblePP
  rw [fermiFunction_particleHole,
    show fermiFunction T ξ - (1 - fermiFunction T ξ)
      = -(1 - fermiFunction T ξ - fermiFunction T ξ) by ring,
    show ξ - -ξ = ξ + ξ by ring, neg_div]

/-! ## §C — the Fermi-surface expansion (Eq. 31) -/

/-- **The dispersion is differentiable with derivative `2t·sin qₓ`** — the
`x`-component of the Fermi velocity in the expansion
`ξ_q ≈ ξ_{q_F} + v_F·(q − q_F)` (Eq. 31); the `y`-component is symmetric. -/
theorem hubbardDispersion_hasDerivAt (t μ qy qx : ℝ) :
    HasDerivAt (fun x => hubbardDispersion t μ (x, qy)) (2 * t * Real.sin qx) qx := by
  unfold hubbardDispersion
  have h := ((((Real.hasDerivAt_cos qx).add_const (Real.cos qy)).const_mul
    (2 * t)).neg).const_add (-μ)
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h

/-- **The Fermi velocity** `v_F(q) = 2t(sin qₓ, sin q_y)` — on the umklapp surface
at the nesting points `(±π/2, ±π/2)` its components are maximal, `±2t`. -/
noncomputable def fermiVelocity (t : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (2 * t * Real.sin q.1, 2 * t * Real.sin q.2)

/-- At the nesting point `(π/2, π/2)` the Fermi velocity is `(2t, 2t)`. -/
theorem fermiVelocity_at_nesting (t : ℝ) :
    fermiVelocity t (Real.pi / 2, Real.pi / 2) = (2 * t, 2 * t) := by
  unfold fermiVelocity
  rw [Real.sin_pi_div_two]
  norm_num

/-! ## §D — the Schmidt/rapidity weld -/

/-- **The occupation asymmetry is the inverse Schmidt number**:
`1 − 2f(ξ) = (schmidtNumber(ξ/2T))⁻¹` — `tanh = coth⁻¹`, so the thermal occupation
of a Hubbard fermion mode is a Schmidt/rapidity datum at `η = ξ/2T`: the
Matsubara-summed threshold functions of the flow and the entanglement dictionary
(`r = λ_C·log K` of `EntropicProperDistance`) run on the same hyperbolic function
of one rapidity, and the Cooper/AF bubble reads `1/(2ξ·K(ξ/2T))`. -/
theorem fermi_schmidt_link (T ξ : ℝ) :
    1 - 2 * fermiFunction T ξ = (schmidtNumber (ξ / (2 * T)))⁻¹ := by
  rw [one_sub_two_fermi]
  unfold schmidtNumber
  rw [Real.tanh_eq_sinh_div_cosh, inv_div]

end Physlib.QuantumMechanics.ComplexAction.HubbardNestingThresholds

end

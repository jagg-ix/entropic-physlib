/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

meta import Zil

/- Consolidated from Physlib/QuantumMechanics/ComplexAction/ComptonClock/StrongPoissonHomogeneousDensity.lean -/

/-!
# The strong-form Poisson equation on the canonical Laplacian

gu.md Axiom 15 asserts the Newtonian field equation `∇²Φ = 4πGρ`.  The repository carries this in weak
/ distributional form (`convolutionPotential_weakPoisson`, `isolatedNewtonPotentialDistribution3_laplacian`)
and as Gauss flux (`isolatedNewtonExteriorField3_sphereFlux`), but the **strong pointwise** equation on
the canonical scalar Laplacian `Δ = ∇⬝∇` (`Space.laplacian`) was missing.

This module supplies it for the uniform-density ball interior, whose exact whole-space solution of the
constant-source Poisson equation is the quadratic potential `Φ = (2πGρ/3)‖x‖²`:

* `laplacian_const_mul_norm_sq` — the reusable identity `Δ(c·‖x‖²) = 2d·c` on `Space d` (in
  particular `Δ‖x‖² = 2d`), computed from the coordinate second derivatives.
* `strongPoisson_homogeneousDensity` — the **strong Poisson equation** `∇²Φ = 4πGρ` (pointwise, on
  `Space 3`, canonical `Δ`) for `Φ = (2πGρ/3)‖x‖²`, matching the `4πG` of the weak law and Gauss flux.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity

/-- **The canonical Laplacian of `c·‖x‖²` is the constant `2d·c`** on `Space d` — the coordinate
second-derivative computation `Δ(c‖x‖²) = ∑ᵢ ∂ᵢ∂ᵢ(c‖x‖²) = ∑ᵢ 2c = 2d·c`.  (With `c = 1` this is
`Δ‖x‖² = 2d`.) -/
@[zil_level structural]
theorem laplacian_const_mul_norm_sq {d : ℕ} (c : ℝ) :
    Space.laplacian (fun x : Space d => c * ‖x‖ ^ 2) = fun _ => 2 * (d : ℝ) * c := by
  have hstep : ∀ (x : Space d) (i : Fin d),
      Space.deriv i (Space.deriv i (fun y : Space d => c * ‖y‖ ^ 2)) x = 2 * c := by
    intro x i
    have hcf : (fun y : Space d => c * ‖y‖ ^ 2) = (c : ℝ) • fun y : Space d => ‖y‖ ^ 2 := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    have hf1 : Space.deriv i (fun y : Space d => c * ‖y‖ ^ 2) = fun y : Space d => c * (2 * (y i)) := by
      rw [hcf, Space.deriv_const_smul c (by fun_prop)]
      funext y; simp [Pi.smul_apply, Space.deriv_norm_sq, smul_eq_mul]
    rw [hf1]
    have hcf2 : (fun y : Space d => c * (2 * (y i))) = (c * 2 : ℝ) • fun y : Space d => y i := by
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hcf2, Space.deriv_const_smul (c * 2) (by fun_prop)]
    simp only [Pi.smul_apply, Space.deriv_component_same, smul_eq_mul, mul_one]
    ring
  rw [Space.laplacian_eq_sum_snd_deriv]
  funext x
  simp only [hstep]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The strong-form Poisson equation `∇²Φ = 4πGρ`** (gu.md Axiom 15), pointwise on the canonical
scalar Laplacian `Δ = ∇⬝∇` over `Space 3`, for the uniform-density interior potential
`Φ = (2πGρ/3)‖x‖²`.  The coupling `4πG` matches the weak/distributional Poisson law and the Gauss
flux `∮∇Φ·dA = 4πGM`. -/
@[zil_level physical_theorem]
theorem strongPoisson_homogeneousDensity (G ρ : ℝ) :
    Space.laplacian (fun x : Space 3 => (2 * Real.pi * G * ρ / 3) * ‖x‖ ^ 2)
      = fun _ => 4 * Real.pi * G * ρ := by
  rw [laplacian_const_mul_norm_sq]
  funext _
  push_cast
  ring

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity

zil attach laplacian_const_mul_norm_sq where
  supported_by @ "lean:Space.deriv_component_same",
  supported_by @ "lean:Space.deriv_const_smul",
  formalizes @ "claim:the-canonical-scalar-laplacian-of-c-times-the-norm-squared-equals-two-d-times-c-on-d-dimensional-space-the-coordinate-second-derivative-computation"

zil attach strongPoisson_homogeneousDensity where
  formalizes @ "claim:the-strong-form-pointwise-poisson-equation-laplacian-phi-equals-four-pi-g-rho-on-the-canonical-scalar-laplacian-over-three-space-for-the-uniform-density-interior-quadratic-potential-two-pi-g-rho-over-three-times-norm-squared",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity.laplacian_const_mul_norm_sq"

zil_file_contract physlib.strongPoissonHomogeneousDensity where
  promises "The strong-form pointwise Poisson equation on the canonical scalar Laplacian, gu.md Axiom 15. The canonical Laplacian del dot del of c times the norm squared equals two d times c on d-dimensional space, computed from the coordinate second derivatives; with c equal one this is Laplacian of norm squared equals two d. Hence the strong-form pointwise Poisson equation Laplacian Phi equals four pi G rho holds on the canonical scalar Laplacian over three-space for the uniform-density ball interior quadratic potential Phi equals two pi G rho over three times norm squared, the exact whole-space solution of the constant-source Poisson equation. The coupling four pi G matches the weak distributional Poisson law and the Gauss flux integral of the gradient over a sphere equals four pi G M. Scope is the uniform-density interior quadratic potential on the canonical Space Laplacian; general smooth-density fundamental-solution Poisson remains the weak distributional law."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Space.laplacian",
    "lean:Space.laplacian_eq_sum_snd_deriv",
    "lean:Space.deriv_norm_sq"
  ]
  forbids_substitutes [
    "reading the uniform-density interior quadratic-potential Poisson equation as the general smooth-density fundamental-solution Poisson equation, which remains the weak distributional law"
  ]
  witnessed_by [
    laplacian_const_mul_norm_sq,
    strongPoisson_homogeneousDensity
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.strongPoissonHomogeneousDensity

/- Consolidated from Physlib/QuantumMechanics/ComplexAction/ComptonClock/GeneralDensityRadialPoisson.lean -/

/-!
# The strong Poisson equation for a general density: the radial case

Statement 15 of the relational framework asks for `∇²Φ = 4πGρ` from the screen flux law.
The repository carried the strong (pointwise) form for a *uniform* density only
(`StrongPoissonHomogeneousDensity.strongPoisson_homogeneousDensity`); the general density
existed in weak/distributional form.  This module proves the strong form for an
**arbitrary continuous density**, in the spherically symmetric setting where the physics
lives: the enclosed mass is the shell integral

  `M(r) = ∫₀ʳ 4πs² ρ(s) ds`,

the field is `g(r) = GM(r)/r²`, and one application of the fundamental theorem of calculus
gives Gauss's law in differential form,

  `d/dr (r² g(r)) = 4πG r² ρ(r)`,

whence the divergence-form strong Poisson equation `(1/r²)·d/dr(r²g) = 4πGρ` — pointwise,
for every continuous `ρ` and every `r ≠ 0`.  No symmetry of `ρ` beyond radial dependence,
no compact support, no smoothness: continuity is all the fundamental theorem needs.

Welds: at constant density the enclosed mass is `4πρ₀r³/3` and the field matches the
gradient of `StrongPoissonHomogeneousDensity`'s potential; beyond a radius where the
density vanishes the enclosed mass freezes, giving Newton's point-mass law for arbitrary
compactly supported sources; and the flux identity `4πr²·g = 4πG·M(r)` is the Gauss
screen-flux law of statement 15 for every radius and every density at once.

**Honest layering.**  This is the radial (divergence-form) strong Poisson equation on the
one-dimensional carrier `r ↦ f(r)`; the chain-rule transport to the Cartesian
`Space.laplacian` of `x ↦ f(‖x‖)` is not performed here, and is the remaining piece of
statement 15.  The uniform-density module covers the Cartesian form in its special case.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson

open Real MeasureTheory Topology

/-- **The enclosed mass** `M(r) = ∫₀ʳ 4πs²ρ(s) ds` of a radial density. -/
noncomputable def shellMass (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r, 4 * π * s ^ 2 * ρ s

/-- **The radial gravitational field** `g(r) = GM(r)/r²`. -/
noncomputable def shellField (G : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  G * shellMass ρ r / r ^ 2

/-- **The enclosed mass grows at the shell rate**: `M'(r) = 4πr²ρ(r)` — the fundamental
theorem of calculus applied to the shell integral, for any continuous density. -/
theorem shellMass_hasDerivAt (ρ : ℝ → ℝ) (hρ : Continuous ρ) (r : ℝ) :
    HasDerivAt (shellMass ρ) (4 * π * r ^ 2 * ρ r) r := by
  have hg : Continuous fun s => 4 * π * s ^ 2 * ρ s := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter volume (𝓝 r))
    hg.continuousAt

/-- **Gauss's law in differential form**: `d/dr (r²·g(r)) = 4πG r² ρ(r)`.  Away from the
origin `r²·g(r)` is just `G·M(r)`, so its growth rate is `G` times the shell rate. -/
theorem shellField_gauss (G : ℝ) (ρ : ℝ → ℝ) (hρ : Continuous ρ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun t => t ^ 2 * shellField G ρ t) (4 * π * G * r ^ 2 * ρ r) r := by
  have hM := (shellMass_hasDerivAt ρ hρ r).const_mul G
  have hev : (fun t => G * shellMass ρ t) =ᶠ[𝓝 r] fun t => t ^ 2 * shellField G ρ t := by
    filter_upwards [isOpen_ne.mem_nhds hr] with t ht
    unfold shellField
    field_simp
  exact (hM.congr_of_eventuallyEq hev.symm).congr_deriv (by ring)

/-- **The strong Poisson equation for a general continuous density**, in divergence form:
`(1/r²)·d/dr(r²·g(r)) = 4πGρ(r)` pointwise at every `r ≠ 0`.  This is statement 15's
field equation with no restriction on the density beyond continuity — the uniform case of
`StrongPoissonHomogeneousDensity` is the special case `ρ = const`. -/
theorem radial_strongPoisson_generalDensity (G : ℝ) (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    {r : ℝ} (hr : r ≠ 0) :
    deriv (fun t => t ^ 2 * shellField G ρ t) r / r ^ 2 = 4 * π * G * ρ r := by
  rw [(shellField_gauss G ρ hρ hr).deriv]
  field_simp

/-- **The Gauss screen-flux law, exactly and for every density**: the flux of the field
through the sphere of radius `r` is `4πG` times the enclosed mass — `4πr²·g(r) = 4πG·M(r)`.
Statement 15's integral face, with no hypotheses on the density at all. -/
theorem shellFlux_eq (G : ℝ) (ρ : ℝ → ℝ) {r : ℝ} (hr : r ≠ 0) :
    4 * π * r ^ 2 * shellField G ρ r = 4 * π * G * shellMass ρ r := by
  unfold shellField
  field_simp

/-! ### Welds -/

/-- At constant density the enclosed mass is the volume times the density. -/
theorem shellMass_uniform (ρ₀ r : ℝ) :
    shellMass (fun _ => ρ₀) r = 4 * π * ρ₀ * r ^ 3 / 3 := by
  unfold shellMass
  rw [show (fun s => 4 * π * s ^ 2 * ρ₀) = fun s => (4 * π * ρ₀) * s ^ 2 from by
    funext s; ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  ring

/-- At constant density the field is `(4πGρ₀/3)·r` — the radial gradient of the
`(2πGρ₀/3)‖x‖²` potential whose Cartesian Laplacian
`StrongPoissonHomogeneousDensity.strongPoisson_homogeneousDensity` already computes.  The
two modules describe the same physics in the two coordinates. -/
theorem shellField_uniform (G ρ₀ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    shellField G (fun _ => ρ₀) r = 4 * π * G * ρ₀ * r / 3 := by
  unfold shellField
  rw [shellMass_uniform]
  field_simp

/-- **Beyond the source the enclosed mass freezes**: if the density vanishes from radius
`R` outward, the enclosed mass at any `r ≥ R` is the total mass `M(R)`. -/
theorem shellMass_frozen_beyond (ρ : ℝ → ℝ) (hρ : Continuous ρ) {R r : ℝ} (hRr : R ≤ r)
    (hzero : ∀ s, R ≤ s → ρ s = 0) :
    shellMass ρ r = shellMass ρ R := by
  have hg : Continuous fun s => 4 * π * s ^ 2 * ρ s := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (0 : ℝ) R)
    (hg.intervalIntegrable (μ := volume) R r)
  have htail : (∫ s in R..r, 4 * π * s ^ 2 * ρ s) = 0 := by
    have hEq : Set.EqOn (fun s => 4 * π * s ^ 2 * ρ s) (fun _ => (0 : ℝ)) (Set.uIcc R r) := by
      intro s hs
      rw [Set.uIcc_of_le hRr] at hs
      simp [hzero s hs.1]
    rw [intervalIntegral.integral_congr hEq]
    simp
  unfold shellMass
  rw [← hsplit, htail, add_zero]

/-- **Newton's point-mass law for arbitrary compact sources**: outside any radius where
the density has vanished, the field is exactly `G·M_total/r²` — the inverse-square law of
statement 13, now derived from an arbitrary interior density rather than assumed
spherical. -/
theorem shellField_exterior_newton (G : ℝ) (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    {R r : ℝ} (hRr : R ≤ r) (hr : r ≠ 0) (hzero : ∀ s, R ≤ s → ρ s = 0) :
    shellField G ρ r = G * shellMass ρ R / r ^ 2 := by
  unfold shellField
  rw [shellMass_frozen_beyond ρ hρ hRr hzero]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson.radial_strongPoisson_generalDensity where
  derives @ "claim:the-strong-pointwise-poisson-equation-holds-in-divergence-form-for-an-arbitrary-continuous-radial-density-at-every-nonzero-radius",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity.strongPoisson_homogeneousDensity",
  caveat @ "claim:radial-divergence-form-on-the-one-dimensional-carrier-the-chain-rule-transport-to-the-cartesian-space-laplacian-is-the-remaining-piece-of-statement-fifteen"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson.shellFlux_eq where
  formalizes @ "claim:the-gauss-screen-flux-law-flux-equals-four-pi-g-times-enclosed-mass-holds-exactly-for-every-radius-and-every-density",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson.shellField_exterior_newton where
  formalizes @ "claim:outside-an-arbitrary-compactly-supported-density-the-field-is-newtons-inverse-square-law-with-the-total-enclosed-mass",
  epistemic_status @ "consistency-identity"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson

end

/- Consolidated from Physlib/QuantumMechanics/ComplexAction/ComptonClock/RadialLaplacianTransport.lean -/

/-!
# The radial Laplacian: transporting statement 15 to Cartesian coordinates

`GeneralDensityRadialPoisson` proved the strong Poisson equation for an arbitrary
continuous density in radial divergence form, and named its remaining piece: the chain-rule
transport to the Cartesian `Space.laplacian`.  This module supplies the transport.

The route avoids the norm's non-differentiability at the origin entirely: every smooth
radial function is `h(‖x‖²)` for a profile `h`, and `‖x‖²` is a polynomial.  Two missing
pieces of the coordinate-derivative API are provided — the chain rule
(`deriv_comp_real`) and the product rule (`deriv_mul_real`) for scalar-valued functions —
and then the radial Laplacian formula follows by summing coordinates:

  `Δ (h(‖x‖²)) = 4‖x‖²·h''(‖x‖²) + 2d·h'(‖x‖²)`.

Substituting `u = r²` this is the familiar `f'' + (d−1)/r·f'` for `f(r) = h(r²)`.  At an
affine profile `h(u) = c·u` the second-derivative term dies and the formula reproduces
`StrongPoissonHomogeneousDensity.laplacian_const_mul_norm_sq` exactly — the uniform-density
module is the affine special case, proved as a weld rather than observed.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.RadialLaplacianTransport

open Space

variable {d : ℕ}

/-! ### §A — the two missing rules of the coordinate-derivative API -/

/-- **The chain rule for a real profile**: `∂ᵢ(h ∘ g) = h'(g x)·∂ᵢg`. -/
theorem deriv_comp_real (h : ℝ → ℝ) (g : Space d → ℝ) (μ : Fin d) (x : Space d)
    (hh : DifferentiableAt ℝ h (g x)) (hg : DifferentiableAt ℝ g x) :
    Space.deriv μ (fun y => h (g y)) x = deriv h (g x) * Space.deriv μ g x := by
  rw [Space.deriv_eq_fderiv_basis, Space.deriv_eq_fderiv_basis]
  have hcomp : fderiv ℝ (fun y => h (g y)) x = (fderiv ℝ h (g x)).comp (fderiv ℝ g x) :=
    fderiv_comp x hh hg
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_smul_deriv]
  rw [smul_eq_mul]
  ring

/-- **The product rule for scalar fields**: `∂ᵢ(f·g) = f·∂ᵢg + g·∂ᵢf`. -/
theorem deriv_mul_real (f g : Space d → ℝ) (μ : Fin d) (x : Space d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    Space.deriv μ (fun y => f y * g y) x
      = f x * Space.deriv μ g x + g x * Space.deriv μ f x := by
  rw [Space.deriv_eq_fderiv_basis, Space.deriv_eq_fderiv_basis, Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_mul hf hg]
  simp [smul_eq_mul]

/-! ### §B — the radial Laplacian -/

/-- **The Laplacian of a radial function**, through the smooth presentation `h(‖x‖²)`:

  `Δ(h(‖x‖²)) = 4‖x‖²·h'' + 2d·h'`,

for any profile whose first two derivatives exist.  Substituting `u = r²` gives the
divergence form `f'' + (d−1)/r·f'` of `GeneralDensityRadialPoisson` — this is the
transport its docstring names as the remaining piece of statement 15. -/
theorem laplacian_radial (h : ℝ → ℝ) (hh1 : Differentiable ℝ h)
    (hh2 : Differentiable ℝ (deriv h)) (x : Space d) :
    Space.laplacian (fun y : Space d => h (‖y‖ ^ 2)) x
      = 4 * ‖x‖ ^ 2 * deriv (deriv h) (‖x‖ ^ 2) + 2 * d * deriv h (‖x‖ ^ 2) := by
  have hns : Differentiable ℝ (fun y : Space d => ‖y‖ ^ 2) := by fun_prop
  -- first derivative: ∂ᵢ(h(‖y‖²)) = h'(‖y‖²)·2yᵢ
  have hstep1 : ∀ i : Fin d, Space.deriv i (fun y : Space d => h (‖y‖ ^ 2))
      = fun y : Space d => deriv h (‖y‖ ^ 2) * (2 * y i) := by
    intro i
    funext y
    rw [deriv_comp_real h _ i y (hh1.differentiableAt) (hns.differentiableAt),
      Space.deriv_norm_sq]
  -- second derivative at x: ∂ᵢ of the product
  have hstep2 : ∀ i : Fin d,
      Space.deriv i (fun y : Space d => deriv h (‖y‖ ^ 2) * (2 * y i)) x
        = deriv h (‖x‖ ^ 2) * 2 + 4 * (x i) ^ 2 * deriv (deriv h) (‖x‖ ^ 2) := by
    intro i
    have hfa : DifferentiableAt ℝ (fun y : Space d => deriv h (‖y‖ ^ 2)) x :=
      (hh2.comp hns).differentiableAt
    have hga : DifferentiableAt ℝ (fun y : Space d => 2 * y i) x := by fun_prop
    rw [deriv_mul_real _ _ i x hfa hga]
    have hcoord : Space.deriv i (fun y : Space d => 2 * y i) x = 2 := by
      have hsm : (fun y : Space d => 2 * y i) = (2 : ℝ) • fun y : Space d => y i := by
        funext y; simp [smul_eq_mul]
      rw [hsm, Space.deriv_const_smul 2 (by fun_prop)]
      simp only [Pi.smul_apply, Space.deriv_component_same, smul_eq_mul, mul_one]
    have hchain : Space.deriv i (fun y : Space d => deriv h (‖y‖ ^ 2)) x
        = deriv (deriv h) (‖x‖ ^ 2) * (2 * x i) := by
      rw [deriv_comp_real (deriv h) _ i x (hh2.differentiableAt) (hns.differentiableAt),
        Space.deriv_norm_sq]
    rw [hcoord, hchain]
    ring
  have hL : Space.laplacian (fun y : Space d => h (‖y‖ ^ 2)) x
      = ∑ i : Fin d, Space.deriv i (Space.deriv i (fun y : Space d => h (‖y‖ ^ 2))) x := by
    rw [Space.laplacian_eq_sum_snd_deriv]
  rw [hL]
  have hsum : (∑ i : Fin d, Space.deriv i (Space.deriv i
      (fun y : Space d => h (‖y‖ ^ 2))) x)
      = ∑ i : Fin d, (deriv h (‖x‖ ^ 2) * 2 + 4 * (x i) ^ 2 * deriv (deriv h) (‖x‖ ^ 2)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hstep1 i, hstep2 i]
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hnorm : (∑ i : Fin d, 4 * (x i) ^ 2 * deriv (deriv h) (‖x‖ ^ 2))
      = 4 * ‖x‖ ^ 2 * deriv (deriv h) (‖x‖ ^ 2) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [Space.norm_sq_eq]
    try ring
  rw [hnorm]
  simp only [nsmul_eq_mul]
  try ring

/-! ### §C — the uniform case is the affine profile, as a weld -/

/-- At the affine profile `h(u) = c·u` the radial formula reproduces the uniform-density
Laplacian `2dc` — `StrongPoissonHomogeneousDensity.laplacian_const_mul_norm_sq` is the
special case of `laplacian_radial` with vanishing second derivative. -/
theorem laplacian_radial_affine (c : ℝ) (x : Space d) :
    Space.laplacian (fun y : Space d => c * ‖y‖ ^ 2) x = 2 * d * c := by
  have h := StrongPoissonHomogeneousDensity.laplacian_const_mul_norm_sq (d := d) c
  have hx := congrFun h x
  simpa using hx

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.RadialLaplacianTransport.laplacian_radial where
  derives @ "claim:the-cartesian-laplacian-of-a-radial-function-is-four-r-squared-h-double-prime-plus-two-d-h-prime-through-the-smooth-norm-squared-presentation-completing-statement-fifteens-transport",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson.radial_strongPoisson_generalDensity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.RadialLaplacianTransport.deriv_comp_real",
  caveat @ "claim:the-profile-carries-two-derivatives-globally-and-the-composition-with-the-shell-potential-of-a-given-density-is-the-remaining-assembly-step"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.RadialLaplacianTransport.deriv_comp_real where
  supported_by @ "lean:Space.deriv_eq_fderiv_basis",
  formalizes @ "claim:the-chain-rule-for-the-coordinate-derivative-of-a-real-profile-composed-with-a-scalar-field",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.RadialLaplacianTransport.deriv_mul_real where
  supported_by @ "lean:Space.deriv_eq_fderiv_basis",
  formalizes @ "claim:the-product-rule-for-the-coordinate-derivative-of-scalar-fields",
  epistemic_status @ "consistency-identity"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.RadialLaplacianTransport

end


/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
public import Physlib.Relativity.MinkowskiWickRotation
meta import Zil

/-!
# The functional Schrödinger equation of coupled-gravity entropic dynamics (Ipek–Caticha §10)

Formalizes the structure of the Ipek–Caticha functional Schrödinger equation (arXiv:2006.05036, Eqs. 105–108),

`i ∂_t Ψ = ∫ dx (N_x Ĥ_⊥x + N^i_x Ĥ_ix) Ψ`,

the emergence of quantum evolution from the entropic dynamics: the wave functional `Ψ` evolves under the smeared
Hamiltonian generator built from the lapse `N` times the **normal** (super-Hamiltonian) operator `Ĥ_⊥` and the
shift `N^i` times the **tangential** (super-momentum) operator `Ĥ_i`. At the operator level (single mode `ℂ`) the
smeared generator is `𝓗(N, N^i) = N·Ĥ_⊥ + N^i·Ĥ_i`, and the two essential structural facts are:

* the **smeared generator acts as `N·Ĥ_⊥ + N^i·Ĥ_i`** (`smearedSchrodinger_apply`) — the normal/tangential split of
  Eq. 108: lapse times the super-Hamiltonian plus shift times the super-momentum;
* the **generator is `ℂ`-linear, so the flow superposes** (`smearedSchrodinger_superposition`) — for *fixed*
  operators `Ĥ_⊥, Ĥ_i` (fixed background metric) the functional Schrödinger equation is linear, reusing the
  Hamilton–Killing `schrodinger_superposition`; this is exactly the superposition that the state-sourced metric
  (`IpekCatichaSuperpositionViolation`) destroys;
* the **generator is linear in the lapse and shift** (`smearedSchrodinger_add_deformation`) — `𝓗` depends linearly
  on the deformation `(N, N^i)`, the freedom of foliation: any choice of lapse and shift picks a slicing of
  space-time, and the generator combines them linearly.

So the coupled-gravity entropic dynamics has functional Schrödinger form `i∂_tΨ = 𝓗(N,N^i)Ψ` with the smeared
generator the lapse-weighted super-Hamiltonian plus shift-weighted super-momentum, `ℂ`-linear (superposition) for a
fixed background and linear in the foliation choice — the linear Schrödinger flow whose superposition is broken only
once the metric in `Ĥ_⊥` is sourced by `Ψ`.

* **§A — the smeared functional Schrödinger generator** (`smearedSchrodingerGenerator`,
  `smearedSchrodinger_apply`).
* **§B — linearity: superposition and foliation freedom** (`smearedSchrodinger_superposition`,
  `smearedSchrodinger_add_deformation`).
* **§C — gauge-covariant evolution** (`gaugeCovariantTimeDerivative`,
  `gaugeCovariantSmearedSchrodinger_equation_covariant`) specializes the existing entropic
  covariant derivative to the time direction and proves covariance of the smeared equation.

**Honest layering.** The normal/tangential split, gauge covariance, the `ℂ`-linearity of the flow, and the
linearity in the lapse/shift are exact algebra on one-mode `ℂ`-linear operators, reusing
`schrodinger_superposition` and `complexCovariantDeriv_gauge_covariant`. The functional
derivatives `Ĥ_⊥ = −(1/2√g)δ²/δχ² + …`, the Poisson-bracket derivation (Eqs. 105–107), and the field-theoretic
smearing are the referenced content. The state-dependence of `Ĥ_⊥` (the nonlinearity) is in
`IpekCatichaSuperpositionViolation`. ## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 105–108). Repo carrier:
  `EntropicTime.HamiltonKillingComplexStructureSchrodinger` (`schrodinger_superposition`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger


/-- **The smeared functional Schrödinger generator** `𝓗(N, N^i) = N·Ĥ_⊥ + N^i·Ĥ_i` (Ipek–Caticha Eq. 108) — the
lapse `N` times the normal super-Hamiltonian operator `Ĥ_⊥` plus the shift `N^i` times the tangential super-momentum
operator `Ĥ_i`, the `ℂ`-linear generator of the functional Schrödinger evolution `i∂_tΨ = 𝓗Ψ`. -/
noncomputable def smearedSchrodingerGenerator (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ :=
  (N : ℂ) • Hperp + (Ni : ℂ) • Hi

/-- **[The generator acts as `N·Ĥ_⊥ + N^i·Ĥ_i`].** The normal/tangential split of the functional Schrödinger
generator (Eq. 108): lapse times the super-Hamiltonian applied to `Ψ` plus shift times the super-momentum. -/
lemma smearedSchrodinger_apply (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) (ψ : ℂ) :
    smearedSchrodingerGenerator N Ni Hperp Hi ψ = (N : ℂ) * Hperp ψ + (Ni : ℂ) * Hi ψ := by
  simp only [smearedSchrodingerGenerator, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-! ## A.1. Continuum-capable functional carrier -/

/-- The same lapse/shift-smeared Caticha generator on an arbitrary complex
module of wave functionals. Unlike the scalar specialization above, `Ψ` may
be an infinite-dimensional function space, a space of Cauchy data, or a
completed test-function carrier; the analytic topology and domains remain
properties of the chosen `Ψ` and operators. -/
noncomputable def continuumSmearedSchrodingerGenerator
    {Ψ : Type*} [AddCommMonoid Ψ] [Module ℂ Ψ]
    (N Ni : ℝ) (Hperp Hi : Ψ →ₗ[ℂ] Ψ) : Ψ →ₗ[ℂ] Ψ :=
  (N : ℂ) • Hperp + (Ni : ℂ) • Hi

/-- The continuum-capable generator has the same normal/tangential split as
Ipek--Caticha Eq. 108. -/
lemma continuumSmearedSchrodinger_apply
    {Ψ : Type*} [AddCommMonoid Ψ] [Module ℂ Ψ]
    (N Ni : ℝ) (Hperp Hi : Ψ →ₗ[ℂ] Ψ) (ψ : Ψ) :
    continuumSmearedSchrodingerGenerator N Ni Hperp Hi ψ =
      (N : ℂ) • Hperp ψ + (Ni : ℂ) • Hi ψ := by
  rfl

/-- Fixed-background functional evolution superposes on every complex
module, without a finite-mode or matrix-entry restriction. -/
lemma continuumSmearedSchrodinger_superposition
    {Ψ : Type*} [AddCommMonoid Ψ] [Module ℂ Ψ]
    (N Ni : ℝ) (Hperp Hi : Ψ →ₗ[ℂ] Ψ)
    (c₁ c₂ : ℂ) (ψ₁ ψ₂ : Ψ) :
    continuumSmearedSchrodingerGenerator N Ni Hperp Hi
        (c₁ • ψ₁ + c₂ • ψ₂) =
      c₁ • continuumSmearedSchrodingerGenerator N Ni Hperp Hi ψ₁ +
        c₂ • continuumSmearedSchrodingerGenerator N Ni Hperp Hi ψ₂ := by
  simp


/-- **[The functional Schrödinger flow superposes] `𝓗(c₁ψ₁ + c₂ψ₂) = c₁𝓗ψ₁ + c₂𝓗ψ₂`.** For fixed operators
`Ĥ_⊥, Ĥ_i` (fixed background metric) the smeared generator is `ℂ`-linear, so the functional Schrödinger flow
superposes — reusing the Hamilton–Killing `schrodinger_superposition`. This linearity is exactly what the
state-sourced metric of coupled gravity destroys. -/
lemma smearedSchrodinger_superposition (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) (c₁ c₂ ψ₁ ψ₂ : ℂ) :
    smearedSchrodingerGenerator N Ni Hperp Hi (c₁ • ψ₁ + c₂ • ψ₂)
      = c₁ • smearedSchrodingerGenerator N Ni Hperp Hi ψ₁
        + c₂ • smearedSchrodingerGenerator N Ni Hperp Hi ψ₂ :=
  schrodinger_superposition (smearedSchrodingerGenerator N Ni Hperp Hi) c₁ c₂ ψ₁ ψ₂

/-- **[The generator is linear in the lapse and shift] `𝓗(N₁+N₂, N^i₁+N^i₂) = 𝓗(N₁,N^i₁) + 𝓗(N₂,N^i₂)`.** The
smeared generator depends linearly on the deformation `(N, N^i)` — the freedom of foliation: lapse and shift
combine linearly to select a slicing of space-time. -/
lemma smearedSchrodinger_add_deformation (N₁ N₂ Ni₁ Ni₂ : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) :
    smearedSchrodingerGenerator (N₁ + N₂) (Ni₁ + Ni₂) Hperp Hi
      = smearedSchrodingerGenerator N₁ Ni₁ Hperp Hi + smearedSchrodingerGenerator N₂ Ni₂ Hperp Hi := by
  unfold smearedSchrodingerGenerator
  push_cast
  module

/-! ## C. Gauge-covariant functional Schrödinger evolution -/

/-- The one-mode covariant time derivative obtained by specializing the repository's entropic
complex covariant derivative to the time direction.  `dψ` is the ordinary derivative datum and
`A₀` is the real phase connection. -/
def gaugeCovariantTimeDerivative (dψ : ℂ) (A₀ : ℝ) (ψ : ℂ) : ℂ :=
  complexCovariantDeriv (fun _ : Unit => dψ) (fun _ : Unit => A₀) ψ ()

/-- The gauge-covariant one-mode form of the Ipek–Caticha smeared functional Schrödinger
equation, `i D_t Ψ = (N H_⊥ + Nᵢ H_i)Ψ`. -/
def SatisfiesGaugeCovariantSmearedSchrodinger
    (dψ : ℂ) (A₀ : ℝ) (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) (ψ : ℂ) : Prop :=
  Complex.I * gaugeCovariantTimeDerivative dψ A₀ ψ =
    smearedSchrodingerGenerator N Ni Hperp Hi ψ

/-- **[Gauge covariance of the smeared functional Schrödinger equation].** If
`iD_tΨ = 𝒽Ψ`, then the explicitly transformed derivative datum, shifted phase connection,
and phase-rotated state satisfy the same equation.  The proof reuses
`complexCovariantDeriv_gauge_covariant` and complex linearity of the smeared generator.

This is the exact single-mode/operator layer; it does not replace the continuum functional
derivative or the field-space gauge bundle by a definitional identification. -/
lemma gaugeCovariantSmearedSchrodinger_equation_covariant
    (dψ : ℂ) (A₀ dχ : ℝ) (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) (ψ u : ℂ)
    (h : SatisfiesGaugeCovariantSmearedSchrodinger dψ A₀ N Ni Hperp Hi ψ) :
    SatisfiesGaugeCovariantSmearedSchrodinger
      (u * (dψ - Complex.I * (dχ : ℂ) * ψ)) (A₀ + dχ)
      N Ni Hperp Hi (u * ψ) := by
  have hCov :
      gaugeCovariantTimeDerivative
          (u * (dψ - Complex.I * (dχ : ℂ) * ψ)) (A₀ + dχ) (u * ψ) =
        u * gaugeCovariantTimeDerivative dψ A₀ ψ := by
    simpa [gaugeCovariantTimeDerivative] using congrFun
      (complexCovariantDeriv_gauge_covariant
        (fun _ : Unit => dψ) (fun _ : Unit => A₀) (fun _ : Unit => dχ) ψ u) ()
  unfold SatisfiesGaugeCovariantSmearedSchrodinger at h ⊢
  rw [hCov]
  calc
    Complex.I * (u * gaugeCovariantTimeDerivative dψ A₀ ψ) =
        u * (Complex.I * gaugeCovariantTimeDerivative dψ A₀ ψ) := by ring
    _ = u * smearedSchrodingerGenerator N Ni Hperp Hi ψ := by rw [h]
    _ = smearedSchrodingerGenerator N Ni Hperp Hi (u * ψ) := by
      simpa only [smul_eq_mul] using
        ((smearedSchrodingerGenerator N Ni Hperp Hi).map_smul u ψ).symm

/-! ## D. Caticha's entropic-dynamics QED covariant derivative -/

/-- Caticha's particle covariant derivative
`D_a ψ = ∂_a ψ - i(q/(ℏc)) A_a ψ` (arXiv:2511.19238, Eq. 58), expressed as
a specialization of the repository's entropic complex connection. -/
noncomputable def catichaQEDCovariantDerivative {ι : Type*}
    (Dψ : ι → ℂ) (q ℏ c : ℝ) (A : ι → ℝ) (ψ : ℂ) : ι → ℂ :=
  complexCovariantDeriv Dψ (fun a => -(q / (ℏ * c)) * A a) ψ

/-- The specialized entropic connection expands to Caticha's minimally
coupled derivative `∂_a - i(q/(ℏc))A_a`. -/
lemma catichaQEDCovariantDerivative_apply {ι : Type*}
    (Dψ : ι → ℂ) (q ℏ c : ℝ) (A : ι → ℝ) (ψ : ℂ) (a : ι) :
    catichaQEDCovariantDerivative Dψ q ℏ c A ψ a =
      Dψ a - Complex.I * ((q / (ℏ * c)) * A a : ℝ) * ψ := by
  simp [catichaQEDCovariantDerivative, complexCovariantDeriv]
  ring

/-- **[Caticha QED gauge covariance].** Under `A ↦ A + dξ` and a local phase
factor `ψ ↦ uψ`, with ordinary derivative data transformed by the product-rule
term `+i(q/(ℏc))dξ·ψ`, Caticha's covariant derivative transforms
homogeneously.  This is Eq. 58's gauge mechanism, proved by reusing
`complexCovariantDeriv_gauge_covariant`. -/
lemma catichaQEDCovariantDerivative_gauge_covariant {ι : Type*}
    (Dψ : ι → ℂ) (q ℏ c : ℝ) (A dξ : ι → ℝ) (ψ u : ℂ) :
    catichaQEDCovariantDerivative
        (fun a => u * (Dψ a + Complex.I * ((q / (ℏ * c)) * dξ a : ℝ) * ψ))
        q ℏ c (fun a => A a + dξ a) (u * ψ) =
      fun a => u * catichaQEDCovariantDerivative Dψ q ℏ c A ψ a := by
  have h := complexCovariantDeriv_gauge_covariant Dψ
    (fun a => -(q / (ℏ * c)) * A a)
    (fun a => -(q / (ℏ * c)) * dξ a) ψ u
  unfold catichaQEDCovariantDerivative
  convert h using 1
  all_goals
    funext a
    simp [complexCovariantDeriv]
    ring

/-! ## E. Pointwise spacetime fields and Lorentzian kinetic density -/

/-- Caticha's covariant derivative lifted pointwise to a field on an
arbitrary spacetime/configuration carrier `X`.  This removes the one-mode
restriction of `catichaQEDCovariantDerivative`; the derivative index is also
arbitrary. -/
noncomputable def catichaQEDCovariantFieldDerivative {X ι : Type*}
    (Dψ : X → ι → ℂ) (q ℏ c : ℝ) (A : X → ι → ℝ)
    (ψ : X → ℂ) : X → ι → ℂ :=
  fun x => catichaQEDCovariantDerivative (Dψ x) q ℏ c (A x) (ψ x)

lemma catichaQEDCovariantFieldDerivative_apply {X ι : Type*}
    (Dψ : X → ι → ℂ) (q ℏ c : ℝ) (A : X → ι → ℝ)
    (ψ : X → ℂ) (x : X) (a : ι) :
    catichaQEDCovariantFieldDerivative Dψ q ℏ c A ψ x a =
      Dψ x a - Complex.I * ((q / (ℏ * c)) * A x a : ℝ) * ψ x :=
  catichaQEDCovariantDerivative_apply (Dψ x) q ℏ c (A x) (ψ x) a

/-- **[Pointwise continuum gauge covariance].** Caticha's minimally coupled
derivative transforms homogeneously at every point of an arbitrary
spacetime/configuration carrier. -/
lemma catichaQEDCovariantFieldDerivative_gauge_covariant {X ι : Type*}
    (Dψ : X → ι → ℂ) (q ℏ c : ℝ) (A dξ : X → ι → ℝ)
    (ψ u : X → ℂ) :
    catichaQEDCovariantFieldDerivative
        (fun x a => u x *
          (Dψ x a + Complex.I * ((q / (ℏ * c)) * dξ x a : ℝ) * ψ x))
        q ℏ c (fun x a => A x a + dξ x a) (fun x => u x * ψ x) =
      fun x a => u x * catichaQEDCovariantFieldDerivative Dψ q ℏ c A ψ x a := by
  funext x
  exact catichaQEDCovariantDerivative_gauge_covariant
    (Dψ x) q ℏ c (A x) (dξ x) (ψ x) (u x)

/-- The mostly-minus Lorentzian kinetic density
`η^{μν} conjugate(D_μ ψ) D_ν ψ` of a continuum complex field, evaluated
pointwise on its carrier.  The contraction reuses the repository's
complexified Minkowski bilinear form. -/
noncomputable def catichaLorentzianKineticDensity {X : Type*}
    (Dψ : X → (Fin 1 ⊕ Fin 3) → ℂ) : X → ℂ :=
  fun x => Physlib.Relativity.minkowskiBilinC
    (fun μ => starRingEnd ℂ (Dψ x μ)) (Dψ x)

/-- A unit-modulus local phase leaves the pointwise Lorentzian kinetic
density invariant. -/
lemma catichaLorentzianKineticDensity_phase_invariant {X : Type*}
    (Dψ : X → (Fin 1 ⊕ Fin 3) → ℂ) (u : X → ℂ)
    (hu : ∀ x, ‖u x‖ = 1) :
    catichaLorentzianKineticDensity (fun x μ => u x * Dψ x μ) =
      catichaLorentzianKineticDensity Dψ := by
  funext x
  unfold catichaLorentzianKineticDensity
  apply Finset.sum_congr rfl
  intro μ _
  have hunit : starRingEnd ℂ (u x) * u x = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hu x]
    norm_num
  change (@Physlib.Relativity.minkowskiMatrixC 3 μ μ) *
      starRingEnd ℂ (u x * Dψ x μ) * (u x * Dψ x μ) =
    (@Physlib.Relativity.minkowskiMatrixC 3 μ μ) *
      starRingEnd ℂ (Dψ x μ) * Dψ x μ
  rw [map_mul]
  calc
    _ = (starRingEnd ℂ (u x) * u x) *
        (@Physlib.Relativity.minkowskiMatrixC 3 μ μ *
          starRingEnd ℂ (Dψ x μ) * Dψ x μ) := by ring
    _ = _ := by rw [hunit, one_mul]

/-- **[Lorentzian Caticha-QED continuum invariant].** After the local gauge
shift, the pointwise Caticha covariant derivative changes by a unit phase;
therefore its full mostly-minus Lorentzian kinetic contraction is unchanged
at every spacetime point. -/
lemma catichaQEDLorentzianKineticDensity_gauge_invariant {X : Type*}
    (Dψ : X → (Fin 1 ⊕ Fin 3) → ℂ) (q ℏ c : ℝ)
    (A dξ : X → (Fin 1 ⊕ Fin 3) → ℝ) (ψ u : X → ℂ)
    (hu : ∀ x, ‖u x‖ = 1) :
    catichaLorentzianKineticDensity
        (catichaQEDCovariantFieldDerivative
          (fun x a => u x *
            (Dψ x a + Complex.I * ((q / (ℏ * c)) * dξ x a : ℝ) * ψ x))
          q ℏ c (fun x a => A x a + dξ x a) (fun x => u x * ψ x)) =
      catichaLorentzianKineticDensity
        (catichaQEDCovariantFieldDerivative Dψ q ℏ c A ψ) := by
  rw [catichaQEDCovariantFieldDerivative_gauge_covariant]
  exact catichaLorentzianKineticDensity_phase_invariant
    (catichaQEDCovariantFieldDerivative Dψ q ℏ c A ψ) u hu

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.continuumSmearedSchrodinger_superposition where
  formalizes @ "claim:for-fixed-background-operators-the-smeared-functional-schrodinger-generator-is-complex-linear-so-the-fixed-background-functional-evolution-superposes-on-every-complex-module",
  supported_by @ "paper:ipek-caticha-arxiv-2006-05036-functional-schrodinger-equation-of-coupled-gravity-entropic-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.smearedSchrodinger_add_deformation where
  formalizes @ "claim:the-smeared-functional-schrodinger-generator-depends-linearly-on-the-deformation-lapse-and-shift-which-combine-linearly-to-select-a-slicing-of-spacetime-the-freedom-of-foliation"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-gauge-covariant-smeared-functional-schrodinger-equation-is-covariant-under-a-simultaneous-gauge-shift-of-the-potential-and-a-local-phase-of-the-wavefunction"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.complexCovariantDeriv_gauge_covariant",
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:catichas-entropic-dynamics-qed-covariant-derivative-partial-minus-i-q-over-hbar-c-times-a-transforms-homogeneously-under-a-gauge-shift-of-a-and-a-local-phase-of-the-field-the-minimal-electromagnetic-coupling-gauge-mechanism"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantFieldDerivative_gauge_covariant where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant",
  formalizes @ "claim:catichas-minimally-coupled-derivative-transforms-homogeneously-pointwise-on-an-arbitrary-possibly-infinite-spacetime-or-configuration-carrier",
  caveat @ "claim:pointwise-continuum-field-covariance-not-by-itself-a-functional-analytic-domain-or-an-interacting-qed-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDLorentzianKineticDensity_gauge_invariant where
  formalizes @ "claim:the-mostly-minus-lorentzian-contraction-of-catichas-covariant-field-derivative-is-invariant-under-local-unit-modulus-gauge-phases-at-every-spacetime-point",
  supported_by @ "lean:Physlib.Relativity.minkowskiBilinC",
  caveat @ "claim:genuine-pointwise-lorentzian-continuum-identity-on-a-flat-signature-carrier-not-yet-the-curved-metric-volume-integral-or-a-dynamical-maxwell-equation"

zil_file_contract physlib.ipekCatichaFunctionalSchrodinger where
  promises "The functional Schrodinger equation of coupled-gravity entropic dynamics (Ipek-Caticha, arXiv:2006.05036, section 10), i d_t Psi = integral (N Hperp + N^i Hi) Psi, together with Caticha's entropic-dynamics QED (arXiv:2511.19238). For fixed background operators the smeared generator is complex-linear, so fixed-background functional evolution superposes on every complex module (continuumSmearedSchrodinger_superposition) -- the linearity that the state-sourced metric of coupled gravity destroys -- and it depends linearly on the lapse-and-shift deformation, the freedom of foliation (smearedSchrodinger_add_deformation). The gauge-covariant smeared equation is covariant under a simultaneous gauge shift and local phase (gaugeCovariantSmearedSchrodinger_equation_covariant). Caticha's minimally-coupled QED derivative now acts pointwise on arbitrary spacetime/configuration carriers, transforms homogeneously there, and its full mostly-minus Lorentzian kinetic contraction is invariant under local unit-modulus gauge phases."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.smearedSchrodingerGenerator",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantFieldDerivative",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaLorentzianKineticDensity"]
  forbids_substitutes ["the Dirac constraint algebra of the smeared Hamiltonian and momentum constraints and its continuum operator domain, which are the cited canonical-gravity infrastructure",
    "the state-sourced (coupled-gravity) nonlinear evolution itself, only the fixed-background linearity, the foliation deformation linearity, and the gauge covariance are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.continuumSmearedSchrodinger_superposition,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.smearedSchrodinger_add_deformation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantFieldDerivative_gauge_covariant,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDLorentzianKineticDensity_gauge_invariant]

/- ZIL-END -/

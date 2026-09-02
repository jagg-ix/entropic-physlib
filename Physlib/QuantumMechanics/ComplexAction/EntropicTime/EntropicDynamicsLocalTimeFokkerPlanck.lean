/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
meta import Zil

/-!
# The local-time Fokker–Planck equations (Ipek–Abedi–Caticha, Appendix A)

Formalizes the **local-time Fokker–Planck (LTFP) equations** of Ipek–Abedi–Caticha (*Reconstructing Quantum Field
Theory in Curved Space-time*, arXiv:1803.07493, Eqs. 16, 18, A.8). The probability `ρ_σ[χ]` flows as the surface
`σ` is deformed, obeying a diffusion (Fokker–Planck) equation written as a continuity equation in configuration
space. In the drift–diffusion form (Eq. A.8),

`δρ/δξ⊥ = (η/√g)[ −∂_χ(ρ ∂_χφ) + ½ ∂²_χ ρ ]`,

and in the equivalent current form (Eq. 16),

`δρ/δξ⊥ = −(1/√g) ∂_χ(ρ ∂_χΦ)`,  with the **current potential**  `Φ = φ − ½ log ρ`.

The equivalence of the two forms is the osmotic decomposition: the current velocity `∂_χΦ = ∂_χφ − ½(∂_χρ)/ρ` is
the phase drift `∂_χφ` minus the osmotic velocity `½(∂_χρ)/ρ`, and the continuity flux `ρ ∂_χΦ = ρ∂_χφ − ½∂_χρ`
then differentiates to `∂_χ(ρ∂_χφ) − ½∂²_χρ`, so the current form reproduces the drift–diffusion form with its
diffusion term.

* the **current potential and osmotic velocity** `Φ = φ − ½ log ρ`, `∂_χΦ = ∂_χφ − ½(∂_χρ)/ρ`
  (`currentPotential`, `currentPotential_hasDerivAt`) — the current velocity is the phase drift minus the osmotic
  velocity (Eq. 16);
* the **current flux is drift minus the osmotic current** `ρ ∂_χΦ = ρ∂_χφ − ½∂_χρ` (`ltfp_currentVelocity_flux`) —
  the continuity flux decomposes into the drift current and the diffusion (osmotic) current;
* the **continuity form equals the drift–diffusion form** — the flux `ρ∂_χφ − ½∂_χρ` differentiates to
  `∂_χ(ρ∂_χφ) − ½∂²_χρ` (`ltfp_flux_hasDerivAt`, reusing `fokkerPlanck_current_hasDerivAt`), so
  `−∂_χ(ρ∂_χΦ) = −∂_χ(ρ∂_χφ) + ½∂²_χρ`: the diffusion term `½∂²_χρ` emerges from the osmotic `−½∂_χρ` (Eqs. 16 ⟺ A.8);
* the **local-time / curved-space scaling** `δρ/δξ⊥ = −(1/√g)∂_χ(flux)` (`ltfpLocalRate`) reduces to the flat
  Fokker–Planck continuity equation `∂ρ/∂t = −∂_χ(flux)` at `√g = 1` (`ltfpLocalRate_flat`, Eq. 18).

So the LTFP equations are a Fokker–Planck continuity equation in configuration space, with current velocity the
gradient of the current potential `Φ = φ − ½ log ρ` (phase minus osmotic); the diffusion term is the osmotic part
of the current, and the `1/√g` factor is the curved-space local-time clock.

* **§A — the current potential and osmotic velocity** (`currentPotential`, `currentPotential_hasDerivAt`).
* **§B — the current flux is drift minus osmotic** (`ltfp_currentVelocity_flux`).
* **§C — the continuity/drift–diffusion equivalence** (`ltfp_flux_hasDerivAt`).
* **§D — the local-time scaling and flat limit** (`ltfpLocalRate`, `ltfpLocalRate_flat`).

**Honest layering.** The current potential and its derivative, the flux decomposition, the drift–diffusion flux
derivative, and the local-time scaling are exact one-dimensional (pointwise, functional-derivative → ordinary
derivative) calculus, reusing `fokkerPlanckCurrent`/`fokkerPlanck_current_hasDerivAt` and `HasDerivAt.log`. The full
functional derivation (Appendix A: the test-functional expansion, the singular transition kernel) is the referenced
content. ## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §3 & Appendix A (Eqs. 16, 18, A.8). Repo carrier:
  `EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian` (`fokkerPlanckCurrent`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck


/-- **The current potential** `Φ = φ − ½ log ρ` (Ipek–Abedi–Caticha Eq. 16) — the drift potential `φ` minus the
osmotic contribution `½ log ρ`; its gradient is the current velocity of the probability flow. -/
noncomputable def currentPotential (φ ρ : ℝ) : ℝ := φ - (1 / 2) * Real.log ρ

/-- **[The current velocity is the drift minus the osmotic velocity] `∂_χΦ = ∂_χφ − ½(∂_χρ)/ρ`.** The gradient of
the current potential `Φ = φ − ½ log ρ` is the phase drift `∂_χφ` minus the osmotic velocity `½(∂_χρ)/ρ` — the
current velocity of the local-time Fokker–Planck flow. -/
lemma currentPotential_hasDerivAt (φ ρ : ℝ → ℝ) (φ' ρ' x : ℝ) (hφ : HasDerivAt φ φ' x)
    (hρ : HasDerivAt ρ ρ' x) (hpos : ρ x ≠ 0) :
    HasDerivAt (fun y => currentPotential (φ y) (ρ y)) (φ' - (1 / 2) * (ρ' / ρ x)) x := by
  have hlog : HasDerivAt (fun y => Real.log (ρ y)) (ρ' / ρ x) x := hρ.log hpos
  unfold currentPotential
  exact hφ.sub (hlog.const_mul (1 / 2))


/-- **[The current flux is drift minus the osmotic current] `ρ ∂_χΦ = ρ∂_χφ − ½∂_χρ`.** The continuity flux
`ρ · (current velocity)` decomposes into the drift current `ρ∂_χφ` minus the osmotic (diffusion) current `½∂_χρ`,
since `ρ · ½(∂_χρ)/ρ = ½∂_χρ`. -/
lemma ltfp_currentVelocity_flux (ρ φ' ρ' : ℝ) (hρ : ρ ≠ 0) :
    ρ * (φ' - (1 / 2) * (ρ' / ρ)) = ρ * φ' - (1 / 2) * ρ' := by
  field_simp


/-- **[The continuity flux differentiates to the drift–diffusion form].** The local-time Fokker–Planck current flux
`ρ∂_χφ − ½∂_χρ` (drift current minus osmotic current) has spatial derivative
`∂_χ(ρ∂_χφ) − ½∂²_χρ` — so the continuity form `−∂_χ(ρ∂_χΦ)` reproduces the drift–diffusion form
`−∂_χ(ρ∂_χφ) + ½∂²_χρ` (Ipek–Abedi–Caticha Eqs. 16 ⟺ A.8): the diffusion term `½∂²_χρ` emerges from the osmotic
current, reusing `fokkerPlanck_current_hasDerivAt` for the drift current. -/
lemma ltfp_flux_hasDerivAt (ρ dφ dρ : ℝ → ℝ) (ρ' dφ' ρ'' x : ℝ) (hρ : HasDerivAt ρ ρ' x)
    (hdφ : HasDerivAt dφ dφ' x) (hdρ : HasDerivAt dρ ρ'' x) :
    HasDerivAt (fun y => fokkerPlanckCurrent ρ dφ y - (1 / 2) * dρ y)
      (ρ' * dφ x + ρ x * dφ' - (1 / 2) * ρ'') x :=
  (fokkerPlanck_current_hasDerivAt ρ dφ ρ' dφ' x hρ hdφ).sub (hdρ.const_mul (1 / 2))


/-- **The local-time Fokker–Planck rate** `δρ/δξ⊥ = −(1/√g) ∂_χ(flux)` — the flow rate of the probability per unit
local proper time `δξ⊥`, with the curved-space density `√g` (Ipek–Abedi–Caticha Eq. 16). -/
noncomputable def ltfpLocalRate (rootg fluxDeriv : ℝ) : ℝ := -(1 / rootg) * fluxDeriv

/-- **[The flat limit is the standard Fokker–Planck continuity equation] `∂ρ/∂t = −∂_χ(flux)`.** At a flat surface
(`√g = 1`, `δξ⊥ = dt`) the local-time rate is the standard Fokker–Planck continuity equation (Eq. 18). -/
lemma ltfpLocalRate_flat (fluxDeriv : ℝ) : ltfpLocalRate 1 fluxDeriv = -fluxDeriv := by
  unfold ltfpLocalRate
  ring

/-! ## E. Continuum kinetic Kolmogorov hypoellipticity -/

/-- Free kinetic transport on one-dimensional phase space `(x,v)`: `v ∂ₓ`. -/
def kineticTransport (z : ℝ × ℝ) : ℝ × ℝ := (z.2, 0)

/-- Velocity diffusion direction on phase space: `∂ᵥ`. -/
def kineticDiffusion (_z : ℝ × ℝ) : ℝ × ℝ := (0, 1)

/-- The derivative of the kinetic transport vector field. -/
def kineticTransportDerivative : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ)

/-- The kinetic transport field has the stated constant Fréchet derivative. -/
lemma kineticTransport_hasFDerivAt (z : ℝ × ℝ) :
    HasFDerivAt kineticTransport kineticTransportDerivative z :=
  kineticTransportDerivative.hasFDerivAt

/-- The Lie bracket between velocity diffusion and kinetic transport.  The order is
`D transport · diffusion - D diffusion · transport`. -/
noncomputable def kineticDiffusionTransportBracket (z : ℝ × ℝ) : ℝ × ℝ :=
  fderiv ℝ kineticTransport z (kineticDiffusion z) -
    fderiv ℝ kineticDiffusion z (kineticTransport z)

/-- **Hörmander bracket generation.**  Velocity diffusion supplies `(0,1)` and its bracket
with kinetic transport supplies the missing spatial direction `(1,0)`. -/
lemma kineticDiffusionTransportBracket_eq (z : ℝ × ℝ) :
    kineticDiffusionTransportBracket z = (1, 0) := by
  rw [kineticDiffusionTransportBracket, (kineticTransport_hasFDerivAt z).fderiv]
  have hd :
      HasFDerivAt kineticDiffusion
        (0 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) z := by
    change HasFDerivAt (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))) 0 z
    exact hasFDerivAt_const (x := z) (c := ((0 : ℝ), (1 : ℝ)))
  rw [hd.fderiv]
  simp [kineticTransportDerivative, kineticDiffusion]

/-- Determinant of the covariance matrix
`[[2Dt³/3, Dt²], [Dt², 2Dt]]` of the free kinetic Kolmogorov process. -/
noncomputable def kineticKolmogorovCovDet (D t : ℝ) : ℝ :=
  D ^ 2 * t ^ 4 / 3

/-- Positive diffusion and positive time make the kinetic covariance nondegenerate. -/
lemma kineticKolmogorovCovDet_pos (D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    0 < kineticKolmogorovCovDet D t := by
  unfold kineticKolmogorovCovDet
  positivity

/-- The explicit free kinetic Kolmogorov heat kernel on continuum phase space.  Although
noise acts only in velocity, transport spreads it into position. -/
noncomputable def kineticKolmogorovKernel (D t : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.sqrt 3 / (2 * Real.pi * D * t ^ 2) *
    Real.exp
      (-(3 * z.1 ^ 2 / (D * t ^ 3) -
        3 * z.1 * z.2 / (D * t ^ 2) + z.2 ^ 2 / (D * t)))

/-- At every fixed diffusion and time parameter, the explicit kinetic kernel is smooth
in both continuum phase-space variables. -/
lemma kineticKolmogorovKernel_contDiff (D t : ℝ) :
    ContDiff ℝ ⊤ (kineticKolmogorovKernel D t) := by
  unfold kineticKolmogorovKernel
  fun_prop

/-- In the physical regime `D,t > 0`, the kinetic Kolmogorov kernel is strictly positive
at every phase-space point. -/
lemma kineticKolmogorovKernel_pos (D t : ℝ) (hD : 0 < D) (ht : 0 < t)
    (z : ℝ × ℝ) :
    0 < kineticKolmogorovKernel D t z := by
  unfold kineticKolmogorovKernel
  positivity

/-- **Continuum kinetic/hypoelliptic capstone.**  The free CAT/EPT kinetic carrier has
the bracket-generating directions, nondegenerate covariance, and a strictly positive
smooth phase-space kernel for every positive diffusion and time. -/
lemma kineticKolmogorov_hypoelliptic_certificate
    (D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    (∀ z, kineticDiffusionTransportBracket z = (1, 0))
      ∧ 0 < kineticKolmogorovCovDet D t
      ∧ (∀ z, 0 < kineticKolmogorovKernel D t z)
      ∧ ContDiff ℝ ⊤ (kineticKolmogorovKernel D t) :=
  ⟨kineticDiffusionTransportBracket_eq,
    kineticKolmogorovCovDet_pos D t hD ht,
    kineticKolmogorovKernel_pos D t hD ht,
    kineticKolmogorovKernel_contDiff D t⟩

/-! ## F. The explicit kernel solves the kinetic PDE -/

/-- The positive quadratic form in the exponent of the kinetic Kolmogorov kernel. -/
noncomputable def kineticKolmogorovExponent (D t x v : ℝ) : ℝ :=
  3 * x ^ 2 / (D * t ^ 3) -
    3 * x * v / (D * t ^ 2) + v ^ 2 / (D * t)

/-- The normalization prefactor of the one-dimensional kinetic Kolmogorov kernel. -/
noncomputable def kineticKolmogorovPrefactor (D t : ℝ) : ℝ :=
  Real.sqrt 3 / (2 * Real.pi * D * t ^ 2)

/-- Factorization of the kernel into its normalization and Gaussian exponent. -/
lemma kineticKolmogorovKernel_factor (D t x v : ℝ) :
    kineticKolmogorovKernel D t (x, v) =
      kineticKolmogorovPrefactor D t *
        Real.exp (-kineticKolmogorovExponent D t x v) := by
  rfl

/-- Time derivative of the kinetic Gaussian exponent. -/
lemma kineticKolmogorovExponent_hasDerivAt_time
    (D t x v : ℝ) (hD : D ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun s => kineticKolmogorovExponent D s x v)
      (-9 * x ^ 2 / (D * t ^ 4) +
        6 * x * v / (D * t ^ 3) - v ^ 2 / (D * t ^ 2)) t := by
  unfold kineticKolmogorovExponent
  have ht3 := (hasDerivAt_pow 3 t).const_mul D
  have ht2 := (hasDerivAt_pow 2 t).const_mul D
  have ht1 := (hasDerivAt_id t).const_mul D
  have h1 := (hasDerivAt_const (x := t) (c := 3 * x ^ 2)).div ht3
    (mul_ne_zero hD (pow_ne_zero 3 ht))
  have h2 := (hasDerivAt_const (x := t) (c := 3 * x * v)).div ht2
    (mul_ne_zero hD (pow_ne_zero 2 ht))
  have h3 := (hasDerivAt_const (x := t) (c := v ^ 2)).div ht1
    (mul_ne_zero hD ht)
  have h := (h1.sub h2).add h3
  have hfun :
      (fun s => 3 * x ^ 2 / (D * s ^ 3) -
        3 * x * v / (D * s ^ 2) + v ^ 2 / (D * s)) =
      (((fun _ : ℝ => 3 * x ^ 2) / fun s => D * s ^ 3) -
        ((fun _ : ℝ => 3 * x * v) / fun s => D * s ^ 2)) +
        ((fun _ : ℝ => v ^ 2) / fun s => D * s) := by
    funext s
    rfl
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => congrFun hfun s)).congr_deriv ?_
  norm_num
  field_simp [hD, ht]
  ring

/-- Spatial derivative of the kinetic Gaussian exponent. -/
lemma kineticKolmogorovExponent_hasDerivAt_space (D t x v : ℝ) :
    HasDerivAt (fun y => kineticKolmogorovExponent D t y v)
      (6 * x / (D * t ^ 3) - 3 * v / (D * t ^ 2)) x := by
  unfold kineticKolmogorovExponent
  have h1 := ((hasDerivAt_pow 2 x).const_mul 3).div_const (D * t ^ 3)
  have h2 := ((hasDerivAt_id x).const_mul (3 * v)).div_const (D * t ^ 2)
  have h3 := hasDerivAt_const (x := x) (c := v ^ 2 / (D * t))
  have h := (h1.sub h2).add h3
  have hfun :
      (fun y => 3 * y ^ 2 / (D * t ^ 3) -
        3 * y * v / (D * t ^ 2) + v ^ 2 / (D * t)) =
      ((fun y => 3 * y ^ 2 / (D * t ^ 3)) -
        fun y => 3 * v * y / (D * t ^ 2)) +
        fun _ : ℝ => v ^ 2 / (D * t) := by
    funext y
    change
      3 * y ^ 2 / (D * t ^ 3) -
          3 * y * v / (D * t ^ 2) + v ^ 2 / (D * t) =
        (3 * y ^ 2 / (D * t ^ 3) - 3 * v * y / (D * t ^ 2)) +
          v ^ 2 / (D * t)
    ring
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => congrFun hfun y)).congr_deriv ?_
  norm_num
  ring

/-- Velocity derivative of the kinetic Gaussian exponent. -/
lemma kineticKolmogorovExponent_hasDerivAt_velocity (D t x v : ℝ) :
    HasDerivAt (fun w => kineticKolmogorovExponent D t x w)
      (-3 * x / (D * t ^ 2) + 2 * v / (D * t)) v := by
  unfold kineticKolmogorovExponent
  have h1 := hasDerivAt_const (x := v) (c := 3 * x ^ 2 / (D * t ^ 3))
  have h2 := ((hasDerivAt_id v).const_mul (3 * x)).div_const (D * t ^ 2)
  have h3 := (hasDerivAt_pow 2 v).div_const (D * t)
  have h := (h1.sub h2).add h3
  have hfun :
      (fun w => 3 * x ^ 2 / (D * t ^ 3) -
        3 * x * w / (D * t ^ 2) + w ^ 2 / (D * t)) =
      ((fun _ : ℝ => 3 * x ^ 2 / (D * t ^ 3)) -
        fun w => 3 * x * w / (D * t ^ 2)) +
        fun w => w ^ 2 / (D * t) := by
    funext w
    rfl
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w => congrFun hfun w)).congr_deriv ?_
  norm_num
  ring

/-- Time derivative of the kernel normalization. -/
lemma kineticKolmogorovPrefactor_hasDerivAt
    (D t : ℝ) (hD : D ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (kineticKolmogorovPrefactor D)
      (-2 / t * kineticKolmogorovPrefactor D t) t := by
  unfold kineticKolmogorovPrefactor
  have hden := (hasDerivAt_pow 2 t).const_mul (2 * Real.pi * D)
  have h := (hasDerivAt_const (x := t) (c := Real.sqrt 3)).div hden
    (mul_ne_zero (mul_ne_zero (by positivity) hD) (pow_ne_zero 2 ht))
  have hfun :
      (fun s : ℝ => Real.sqrt 3 / (2 * Real.pi * D * s ^ 2)) =
      (fun s => (fun _ : ℝ => Real.sqrt 3) s /
        (fun y => 2 * Real.pi * D * y ^ 2) s) := by rfl
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => congrFun hfun s)).congr_deriv ?_
  norm_num
  field_simp [hD, ht]

/-- Explicit time derivative of the kinetic kernel. -/
lemma kineticKolmogorovKernel_hasDerivAt_time
    (D t x v : ℝ) (hD : D ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun s => kineticKolmogorovKernel D s (x, v))
      (kineticKolmogorovKernel D t (x, v) *
        (-2 / t -
          (-9 * x ^ 2 / (D * t ^ 4) +
            6 * x * v / (D * t ^ 3) - v ^ 2 / (D * t ^ 2)))) t := by
  rw [show (fun s => kineticKolmogorovKernel D s (x, v)) =
      fun s => kineticKolmogorovPrefactor D s *
        Real.exp (-kineticKolmogorovExponent D s x v) by
    funext s; rw [kineticKolmogorovKernel_factor]]
  have hp := kineticKolmogorovPrefactor_hasDerivAt D t hD ht
  have hq := kineticKolmogorovExponent_hasDerivAt_time D t x v hD ht
  have he := hq.neg.exp
  have hcoef :
      (-2 / t * kineticKolmogorovPrefactor D t) *
          Real.exp (-kineticKolmogorovExponent D t x v) +
        kineticKolmogorovPrefactor D t *
          (Real.exp (-kineticKolmogorovExponent D t x v) *
            -(-9 * x ^ 2 / (D * t ^ 4) +
              6 * x * v / (D * t ^ 3) - v ^ 2 / (D * t ^ 2))) =
        kineticKolmogorovKernel D t (x, v) *
          (-2 / t -
            (-9 * x ^ 2 / (D * t ^ 4) +
              6 * x * v / (D * t ^ 3) - v ^ 2 / (D * t ^ 2))) := by
    rw [kineticKolmogorovKernel_factor]
    ring
  exact hcoef ▸ hp.mul he

/-- Explicit spatial derivative of the kinetic kernel. -/
lemma kineticKolmogorovKernel_hasDerivAt_space (D t x v : ℝ) :
    HasDerivAt (fun y => kineticKolmogorovKernel D t (y, v))
      (-kineticKolmogorovKernel D t (x, v) *
        (6 * x / (D * t ^ 3) - 3 * v / (D * t ^ 2))) x := by
  rw [show (fun y => kineticKolmogorovKernel D t (y, v)) =
      fun y => kineticKolmogorovPrefactor D t *
        Real.exp (-kineticKolmogorovExponent D t y v) by
    funext y; rw [kineticKolmogorovKernel_factor]]
  have hq := kineticKolmogorovExponent_hasDerivAt_space D t x v
  have he := hq.neg.exp
  have hcoef :
      0 * Real.exp (-kineticKolmogorovExponent D t x v) +
        kineticKolmogorovPrefactor D t *
          (Real.exp (-kineticKolmogorovExponent D t x v) *
            -(6 * x / (D * t ^ 3) - 3 * v / (D * t ^ 2))) =
        -kineticKolmogorovKernel D t (x, v) *
          (6 * x / (D * t ^ 3) - 3 * v / (D * t ^ 2)) := by
    rw [kineticKolmogorovKernel_factor]
    ring
  exact hcoef ▸
    (hasDerivAt_const (x := x) (c := kineticKolmogorovPrefactor D t)).mul he

/-- Explicit velocity derivative of the kinetic kernel. -/
lemma kineticKolmogorovKernel_hasDerivAt_velocity (D t x v : ℝ) :
    HasDerivAt (fun w => kineticKolmogorovKernel D t (x, w))
      (-kineticKolmogorovKernel D t (x, v) *
        (-3 * x / (D * t ^ 2) + 2 * v / (D * t))) v := by
  rw [show (fun w => kineticKolmogorovKernel D t (x, w)) =
      fun w => kineticKolmogorovPrefactor D t *
        Real.exp (-kineticKolmogorovExponent D t x w) by
    funext w; rw [kineticKolmogorovKernel_factor]]
  have hq := kineticKolmogorovExponent_hasDerivAt_velocity D t x v
  have he := hq.neg.exp
  have hcoef :
      0 * Real.exp (-kineticKolmogorovExponent D t x v) +
        kineticKolmogorovPrefactor D t *
          (Real.exp (-kineticKolmogorovExponent D t x v) *
            -(-3 * x / (D * t ^ 2) + 2 * v / (D * t))) =
        -kineticKolmogorovKernel D t (x, v) *
          (-3 * x / (D * t ^ 2) + 2 * v / (D * t)) := by
    rw [kineticKolmogorovKernel_factor]
    ring
  exact hcoef ▸
    (hasDerivAt_const (x := v) (c := kineticKolmogorovPrefactor D t)).mul he

/-- Explicit second velocity derivative of the kinetic kernel. -/
lemma kineticKolmogorovKernel_hasDerivAt_velocityDerivative
    (D t x v : ℝ) :
    HasDerivAt
      (fun w => deriv (fun u => kineticKolmogorovKernel D t (x, u)) w)
      (kineticKolmogorovKernel D t (x, v) *
        ((-3 * x / (D * t ^ 2) + 2 * v / (D * t)) ^ 2 -
          2 / (D * t))) v := by
  have hkfun :
      (fun w => deriv (fun u => kineticKolmogorovKernel D t (x, u)) w) =
        fun w => -kineticKolmogorovKernel D t (x, w) *
          (-3 * x / (D * t ^ 2) + 2 * w / (D * t)) := by
    funext w
    exact (kineticKolmogorovKernel_hasDerivAt_velocity D t x w).deriv
  rw [hkfun]
  have hk := kineticKolmogorovKernel_hasDerivAt_velocity D t x v
  have hlin : HasDerivAt
      (fun w : ℝ => -3 * x / (D * t ^ 2) + 2 * w / (D * t))
      (2 / (D * t)) v := by
    have h :=
      (hasDerivAt_const (x := v) (c := -3 * x / (D * t ^ 2))).add
        ((hasDerivAt_id v).const_mul (2 / (D * t)))
    refine (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => ?_)).congr_deriv ?_
    · change
        -3 * x / (D * t ^ 2) + 2 * w / (D * t) =
          -3 * x / (D * t ^ 2) + (2 / (D * t)) * w
      ring
    · ring
  have hcoef :
      -(-kineticKolmogorovKernel D t (x, v) *
          (-3 * x / (D * t ^ 2) + 2 * v / (D * t))) *
          (-3 * x / (D * t ^ 2) + 2 * v / (D * t)) +
        (-kineticKolmogorovKernel D t (x, v)) * (2 / (D * t)) =
      kineticKolmogorovKernel D t (x, v) *
        ((-3 * x / (D * t ^ 2) + 2 * v / (D * t)) ^ 2 -
          2 / (D * t)) := by ring
  exact hcoef ▸ hk.neg.mul hlin

/-- **Actual continuum kinetic PDE.**  The explicit positive-time kernel solves the
one-dimensional forward Kolmogorov equation
`∂ₜ K + v ∂ₓ K = D ∂ᵥ² K`. -/
lemma kineticKolmogorovKernel_satisfies_pde
    (D t x v : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun s => kineticKolmogorovKernel D s (x, v)) t +
        v * deriv (fun y => kineticKolmogorovKernel D t (y, v)) x =
      D * deriv (fun w =>
        deriv (fun u => kineticKolmogorovKernel D t (x, u)) w) v := by
  rw [(kineticKolmogorovKernel_hasDerivAt_time D t x v hD.ne' ht.ne').deriv,
    (kineticKolmogorovKernel_hasDerivAt_space D t x v).deriv,
    (kineticKolmogorovKernel_hasDerivAt_velocityDerivative D t x v).deriv]
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticDiffusionTransportBracket_eq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticTransport_hasFDerivAt",
  formalizes @ "claim:in-the-free-continuum-kinetic-kolmogorov-model-velocity-diffusion-and-its-lie-bracket-with-transport-generate-both-phase-space-directions"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticKolmogorov_hypoelliptic_certificate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticDiffusionTransportBracket_eq",
  formalizes @ "claim:positive-diffusion-and-positive-time-give-a-nondegenerate-covariance-and-a-strictly-positive-smooth-continuum-phase-space-kernel-for-the-bracket-generating-kinetic-kolmogorov-model",
  caveat @ "claim:explicit-free-kinetic-kolmogorov-hypoellipticity-not-a-general-hormander-theorem-for-variable-coefficient-curved-or-nonlinear-vlasov-generators"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticKolmogorovKernel_satisfies_pde where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticKolmogorovKernel_hasDerivAt_space",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticKolmogorovKernel_hasDerivAt_time",
  formalizes @ "claim:the-explicit-positive-time-continuum-kolmogorov-kernel-solves-the-forward-kinetic-pde-partial-t-k-plus-v-partial-x-k-equals-d-partial-v-squared-k",
  requires @ "claim:positive-diffusion-and-positive-time-give-a-nondegenerate-covariance-and-a-strictly-positive-smooth-continuum-phase-space-kernel-for-the-bracket-generating-kinetic-kolmogorov-model",
  caveat @ "claim:this-is-the-free-one-dimensional-kinetic-pde-not-a-variable-coefficient-curved-or-nonlinear-hormander-existence-theorem"

zil_file_contract physlib.entropicDynamicsLocalTimeFokkerPlanck where
  promises "The local-time Fokker--Planck current is decomposed into drift and osmotic parts. Its continuum kinetic extension proves the free Kolmogorov bracket condition, supplies a nondegenerate strictly positive smooth phase-space kernel, and verifies directly that this kernel solves the forward kinetic Kolmogorov PDE."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:ContinuousLinearMap.snd",
    "lean:HasFDerivAt.fderiv",
    "lean:Real.exp"]
  forbids_substitutes ["calling a finite Markov chain a continuum kinetic process",
    "claiming the explicit free kernel proves general variable-coefficient or nonlinear hypoellipticity"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.ltfp_flux_hasDerivAt,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticDiffusionTransportBracket_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticKolmogorov_hypoelliptic_certificate,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticKolmogorovKernel_satisfies_pde]

/- ZIL-END -/

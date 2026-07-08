/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.Coercivity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Feynman–Kac model, weights, and propagator semigroup

The Feynman–Kac (FK) correspondence reads the **entropic damping**
`exp(−S_I/ℏ)` of the path integral as a potential damping factor
in a Markov-style propagator:

* `FeynmanKacModel X` — an abstract path-integral model with a
  potential `V : X → ℝ` and a semigroup `pathIntegral : (X → ℝ) → ℝ → X → ℝ`
  (Chapman–Kolmogorov composition law).
* `feynman_kac_weight V β x = exp(−β · V x)` — the Gibbs/FK weight at
  inverse temperature `β`.
* `feynman_kac_propagator M β obs t x` — the FK propagator with `obs`
  weighted by `feynman_kac_weight`, with the semigroup identity
  `feynman_kac_propagator_semigroup`.
* `fkPathPotential V x t = ∫₀^t V(x τ) dτ` — pathwise cumulative
  potential, with FK path weight `fkPathWeight V x t = exp(−fkPathPotential V x t)`.
* `fkPathWeight_nonneg`, `fkPathWeight_le_one` — probability bounds.
* `damping_satisfies_decay_ODE` — the scalar FK damping satisfies the
  decay ODE `w' = −V·w`.

The entropic-time identification is recorded
at the scalar level: at constant potential `V` over interval `[0, T]`,
`exp(−V·T) = exp(−τ_ent)` where `τ_ent = S_I/ℏ = V·T` after the
correspondence `S_I = ℏ·V·T`.


## References

- **Fujiwara 1979** — *A construction of the fundamental solution for the Schrödinger equation*
- **Grosche 1988** — *Path integration via summation of perturbation expansions*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open Real MeasureTheory

/-! ## §1 — Feynman-Kac model and weights -/

/-- **Abstract Feynman–Kac / Markov path-integral model.**  A potential
`V : X → ℝ` together with a propagator
`pathIntegral : (X → ℝ) → ℝ → X → ℝ` satisfying the Chapman–Kolmogorov
composition law. -/
structure FeynmanKacModel (X : Type*) where
  /-- Potential function. -/
  potential : X → ℝ
  /-- Path-integral propagator `(observable, time, state) ↦ value`. -/
  pathIntegral : (X → ℝ) → ℝ → X → ℝ
  /-- Chapman–Kolmogorov composition law. -/
  compose :
    ∀ (obs : X → ℝ) (t s : ℝ) (x : X),
      pathIntegral obs (t + s) x =
        pathIntegral (fun y => pathIntegral obs s y) t x

/-- **Gibbs / Feynman–Kac weight** `exp(−β·V(x))` — damps configurations
of large potential. -/
def feynman_kac_weight {X : Type*} (V : X → ℝ) (β : ℝ) (x : X) : ℝ :=
  Real.exp (- β * V x)

/-- The FK weight is strictly positive. -/
theorem feynman_kac_weight_pos {X : Type*} (V : X → ℝ) (β : ℝ) (x : X) :
    0 < feynman_kac_weight V β x :=
  Real.exp_pos _

theorem feynman_kac_weight_nonneg {X : Type*} (V : X → ℝ) (β : ℝ) (x : X) :
    0 ≤ feynman_kac_weight V β x :=
  le_of_lt (feynman_kac_weight_pos V β x)

/-- **Constant-potential FK weight (scalar form)**: at constant `V` and
inverse-temperature `T`, the FK weight is `exp(−V·T)`. -/
theorem constant_potential_fk_weight (V T : ℝ) :
    feynman_kac_weight (fun _ : Unit => V) T () = Real.exp (-(V * T)) := by
  unfold feynman_kac_weight
  ring_nf

/-! ## §2 — Feynman–Kac propagator (semigroup form) -/

/-- Weighted observable used in FK-style expectations:
`(weight V β) · obs`. -/
def feynman_kac_integrand {X : Type*}
    (V : X → ℝ) (β : ℝ) (obs : X → ℝ) : X → ℝ :=
  fun x => feynman_kac_weight V β x * obs x

/-- **Feynman–Kac propagator** induced by a `FeynmanKacModel`: the
path-integral propagator applied to the FK-weighted observable. -/
def feynman_kac_propagator {X : Type*}
    (M : FeynmanKacModel X) (β : ℝ) (obs : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  M.pathIntegral (feynman_kac_integrand M.potential β obs) t x

/-- **Semigroup law for the FK propagator** (Chapman–Kolmogorov form). -/
theorem feynman_kac_propagator_semigroup {X : Type*}
    (M : FeynmanKacModel X) (β : ℝ) (obs : X → ℝ) (t s : ℝ) (x : X) :
    feynman_kac_propagator M β obs (t + s) x =
      M.pathIntegral
        (fun y => feynman_kac_propagator M β obs s y) t x := by
  unfold feynman_kac_propagator
  simpa [feynman_kac_propagator, feynman_kac_integrand] using
    M.compose (feynman_kac_integrand M.potential β obs) t s x

/-! ## §3 — Pathwise Feynman–Kac (cumulative potential) -/

/-- **Pathwise FK potential** `∫₀^t V(x τ) dτ` — the integrated potential
along a trajectory. -/
def fkPathPotential (V : ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, V (x τ)

/-- **Pathwise FK weight** `exp(−∫₀^t V(x τ) dτ)`. -/
def fkPathWeight (V : ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (- fkPathPotential V x t)

/-- The pathwise FK weight is strictly positive. -/
theorem fkPathWeight_pos (V : ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) :
    0 < fkPathWeight V x t :=
  Real.exp_pos _

theorem fkPathWeight_nonneg (V : ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) :
    0 ≤ fkPathWeight V x t :=
  le_of_lt (fkPathWeight_pos V x t)

/-- **Pathwise FK weight bound**: for `V ≥ 0` and `t ≥ 0`, the pathwise FK
weight is bounded by `1`. -/
theorem fkPathWeight_le_one
    (V : ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ)
    (hV : ∀ y, 0 ≤ V y) (ht : 0 ≤ t) :
    fkPathWeight V x t ≤ 1 := by
  unfold fkPathWeight fkPathPotential
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hIntNonneg : 0 ≤ ∫ τ in (0 : ℝ)..t, V (x τ) :=
    intervalIntegral.integral_nonneg ht (fun τ _hτ => hV (x τ))
  linarith

/-! ## §4 — Scalar FK damping satisfies the decay ODE -/

/-- The **scalar FK damping** `w(t) = exp(−V·t)` satisfies the decay
ODE `w'(t) = −V · w(t)`. -/
theorem damping_satisfies_decay_ODE (V : ℝ) :
    ∀ t : ℝ, HasDerivAt (fun t => Real.exp (- V * t))
      (- V * Real.exp (- V * t)) t := by
  intro t
  have hf : HasDerivAt (fun t => - V * t) (- V) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id t).const_mul (- V)
  have hg : HasDerivAt (fun t => Real.exp (- V * t))
      (Real.exp (- V * t) * (- V)) t := by
    simpa using hf.exp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hg

/-- Initial condition for the scalar FK damping: `w(0) = 1`. -/
theorem decay_ODE_initial_condition (V : ℝ) (t : ℝ) (ht : t = 0) :
    Real.exp (- V * t) = 1 := by
  simp [ht]

/-! ## §5 — Scalar entropic ↔ FK bridge at constant potential -/

/-- **Entropic time at constant potential** `τ_ent = V·T` when
`S_I = ℏ·V·T`. -/
theorem entropic_time_is_cumulative_potential
    (V T ℏ : ℝ) (hℏ : 0 < ℏ) (S_I : ℝ) (hSI : S_I = V * T * ℏ) :
    S_I / ℏ = V * T := by
  rw [hSI]
  field_simp [hℏ.ne']

/-- **FK ↔ entropic damping equivalence** at constant potential: the FK
damping `exp(−V·T)` equals the entropic damping `exp(−τ_ent)` under
`S_I = ℏ·V·T`. -/
theorem fk_weight_equals_entropic_damping
    (V T ℏ : ℝ) (hℏ : 0 < ℏ) (S_I : ℝ) (hSI : S_I = V * T * ℏ) :
    Real.exp (-(V * T)) = Real.exp (-(S_I / ℏ)) := by
  congr 1
  rw [neg_inj, hSI]
  field_simp [hℏ.ne']

/-- **Main scalar correspondence**: at constant potential and the
entropic identification `S_I = ℏ·V·T`, the FK weight equals the entropic
damping. -/
theorem fk_euclidean_entropic_damping_correspondence
    (V T ℏ : ℝ) (hℏ : 0 < ℏ) (S_I : ℝ) (hSI : S_I = V * T * ℏ) :
    Real.exp (-(S_I / ℏ)) =
      feynman_kac_weight (fun _ : Unit => V) T () := by
  calc Real.exp (-(S_I / ℏ))
      = Real.exp (-(V * T)) :=
        (fk_weight_equals_entropic_damping V T ℏ hℏ S_I hSI).symm
    _ = feynman_kac_weight (fun _ : Unit => V) T () :=
        (constant_potential_fk_weight V T).symm

/-! ## §6 — Navier–Stokes viscous dissipation as FK potential -/

/-- **NS viscous dissipation as a Feynman–Kac potential.**

For an NS flow with viscous decay constant `γ_visc ≥ 0`, the
kinetic-energy decay `E(t) = E₀ · exp(−γ_visc · t)` factorises through
the FK weight `feynman_kac_weight (fun _ => γ_visc) t () = exp(−γ_visc · t)`:

  `E(t) = E₀ · feynman_kac_weight (fun _ => γ_visc) t ()`.

The viscous decay constant plays the role of an FK potential `V = γ_visc`,
and the kinetic-energy ratio `E(t) / E₀` is exactly the FK Gibbs damping.
-/
theorem ns_energy_decay_eq_fk_weight (gamma_visc t : ℝ) :
    Real.exp (- gamma_visc * t) =
      feynman_kac_weight (fun _ : Unit => gamma_visc) t () := by
  unfold feynman_kac_weight
  ring_nf

/-- **NS viscous dissipation ↔ entropic damping** (under
`S_I = ℏ · γ_visc · t`).  The kinetic-energy decay rate identifies with
the entropic-damping factor `exp(−τ_ent)` via the standard
identification. -/
theorem ns_energy_decay_eq_entropic_damping
    (gamma_visc t ℏ : ℝ) (hℏ : 0 < ℏ) (S_I : ℝ)
    (hSI : S_I = gamma_visc * t * ℏ) :
    Real.exp (- gamma_visc * t) = Real.exp (-(S_I / ℏ)) := by
  rw [ns_energy_decay_eq_fk_weight,
    ← fk_euclidean_entropic_damping_correspondence gamma_visc t ℏ hℏ S_I hSI]

end Physlib.QFT.PathIntegral

end

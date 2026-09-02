/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.ContinuumVariational
public import Physlib.SpaceAndTime.Space.Derivatives.Div
public import Physlib.SpaceAndTime.Space.Derivatives.Basic

/-!
# The canonical stress-energy current and Noether's translation theorem

For a first-order local Lagrangian density `L` built from a scalar field `φ` and its first
derivatives, translation invariance produces the **canonical stress-energy current** in direction `ν`,

  `T^μ_ν = π^μ · ∂_ν φ − δ^μ_ν L`,   `π^μ := ∂L/∂(∂_μ φ)`,

and Noether's theorem is the pointwise identity that its spacetime divergence is the Euler–Lagrange
residual paired with the translation characteristic `∂_ν φ`:

  `∂_μ T^μ_ν = (∂_μ π^μ − ∂L/∂φ) · ∂_ν φ`   (`canonicalStressCurrent_div`).

On shell (Euler–Lagrange `∂L/∂φ = ∂_μ π^μ`) the right-hand side vanishes, so `∂_μ T^μ_ν = 0`
(`canonicalStress_conservation`) — the local conservation of momentum/energy.

Spacetime is modelled as a flat `Space n` (index `0` = time, `1 … n−1` = space); the divergence
`∂_μ (·)^μ` is `Space.div` (`∇ ⬝`). The single input encoding "`L` depends on the point only through the
field and its derivatives" is the chain rule `hchain` for `∂_ν L`; everything else is the genuine Noether
reorganisation — the Leibniz rule (`Space.deriv_smul`), the `δ^μ_ν L` collapse, and the cancellation of the
second-derivative terms by Clairaut symmetry (`Space.deriv_commute`).

This is the concrete translation instance of the abstract `Physlib.Mathematics.LovelockRund.NoetherCurrentData`
/ `BalanceLawData` conservation layer.

## Kälbermann eqs. 9–12 and the Ehrenfest theorem

For the Madelung Lagrangian `L(S_t, S_i, R, R_t, R_i)` with `ψ = R e^{iS}`, `conjugateCurrent_continuity` is
Kälbermann's eq. 11 (the phase `S` is cyclic, so the probability four-current `J^μ` is conserved) and
`canonicalStress_conservation` is his eq. 10 (translation invariance conserves the canonical momentum density
`p_j` and stress tensor `T_ij`). Integrated over space against an asymptotically vanishing state, these local
laws become the spatially-averaged relations `d⟨r⟩/dt = ∫J` and `d(∫p)/dt = ⟨F⟩` that are the hypotheses of
`Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest`
(`ehrenfest_from_galilean`, §F). This module thus supplies the field-theoretic Noether layer beneath that
averaged Ehrenfest theorem; the spatial integration / divergence-theorem step is not formalized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open Space

variable {n : ℕ}

/-- The **canonical stress-energy current** in translation direction `ν` for a scalar field `φ` with
conjugate momenta `π μ = ∂L/∂(∂_μ φ)` and on-field Lagrangian value `L`: the `μ`-component is
`T^μ_ν = π^μ ∂_ν φ − δ^μ_ν L`. -/
def canonicalStressCurrent (φ L : Space n → ℝ) (π : Fin n → Space n → ℝ) (ν : Fin n) :
    Space n → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (fun μ => π μ x * ∂[ν] φ x - (if μ = ν then L x else 0))

@[simp]
lemma canonicalStressCurrent_apply (φ L : Space n → ℝ) (π : Fin n → Space n → ℝ) (ν : Fin n)
    (x : Space n) (μ : Fin n) :
    canonicalStressCurrent φ L π ν x μ = π μ x * ∂[ν] φ x - (if μ = ν then L x else 0) := rfl

/-- **Noether's translation identity for a single scalar field.**  The spacetime divergence of the
canonical stress-energy current is the Euler–Lagrange residual paired with the translation characteristic:
`∂_μ T^μ_ν = (∂_μ π^μ − ∂L/∂φ) · ∂_ν φ`.  The only physical input is the chain rule `hchain` for `∂_ν L`
(the statement that `L` is local in the field and its first derivatives); the reorganisation uses the
Leibniz rule, the `δ^μ_ν` collapse, and Clairaut symmetry of the mixed second derivatives. -/
theorem canonicalStressCurrent_div (φ L : Space n → ℝ) (π : Fin n → Space n → ℝ) (ν : Fin n)
    (dLdφ : Space n → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hL : Differentiable ℝ L) (hπ : ∀ μ, Differentiable ℝ (π μ))
    (hchain : ∀ x, ∂[ν] L x
      = dLdφ x * ∂[ν] φ x + ∑ μ, π μ x * ∂[ν] (∂[μ] φ) x) (x : Space n) :
    (∇ ⬝ canonicalStressCurrent φ L π ν) x
      = ((∑ μ, ∂[μ] (π μ) x) - dLdφ x) * ∂[ν] φ x := by
  -- Differentiability of the two component pieces of the current.
  have hf1d : ∀ μ, Differentiable ℝ (fun y => π μ y * ∂[ν] φ y) :=
    fun μ => (hπ μ).mul (deriv_differentiable hφ ν)
  have hf2d : ∀ μ, Differentiable ℝ (fun y : Space n => if μ = ν then L y else 0) := by
    intro μ
    by_cases hμν : μ = ν
    · rw [show (fun y : Space n => if μ = ν then L y else 0) = (fun y => L y) from
        funext fun _ => if_pos hμν]
      exact hL
    · rw [show (fun y : Space n => if μ = ν then L y else 0) = (fun _ => 0) from
        funext fun _ => if_neg hμν]
      exact differentiable_const 0
  -- The divergence is the difference of the momentum-flux sum and the `δ^μ_ν L` sum.
  have hdiv : (∇ ⬝ canonicalStressCurrent φ L π ν) x
      = (∑ μ, ∂[μ] (fun y => π μ y * ∂[ν] φ y) x)
        - ∑ μ, ∂[μ] (fun y : Space n => if μ = ν then L y else 0) x := by
    rw [← Finset.sum_sub_distrib]
    simp only [Space.div]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    have hinner : (fun y => canonicalStressCurrent φ L π ν y μ)
        = (fun y => π μ y * ∂[ν] φ y) - (fun y : Space n => if μ = ν then L y else 0) := by
      funext y; simp [Pi.sub_apply]
    rw [hinner, deriv_sub _ _ (hf1d μ) (hf2d μ), Pi.sub_apply]
  rw [hdiv]
  -- Leibniz rule on the momentum-flux sum.
  have hleib : (∑ μ, ∂[μ] (fun y => π μ y * ∂[ν] φ y) x)
      = ∑ μ, (π μ x * ∂[μ] (∂[ν] φ) x + ∂[μ] (π μ) x * ∂[ν] φ x) := by
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [show (fun y => π μ y * ∂[ν] φ y) = (π μ) • (∂[ν] φ) from rfl,
      deriv_smul (hπ μ).differentiableAt (deriv_differentiable hφ ν).differentiableAt]
    simp only [smul_eq_mul]
  -- The `δ^μ_ν L` sum collapses to `∂_ν L`.
  have hδsum : (∑ μ, ∂[μ] (fun y : Space n => if μ = ν then L y else 0) x) = ∂[ν] L x := by
    refine (Finset.sum_eq_single (a := ν) ?_ ?_).trans ?_
    · intro μ _ hμν
      rw [show (fun y : Space n => if μ = ν then L y else 0) = (fun _ => 0) from
        funext fun _ => if_neg hμν]
      exact Space.deriv_const (0 : ℝ) μ
    · intro h; exact absurd (Finset.mem_univ ν) h
    · simp
  rw [hleib, hδsum, hchain, Finset.sum_add_distrib]
  -- Clairaut symmetry cancels the mixed second-derivative sums.
  have hcomm : (∑ μ, π μ x * ∂[μ] (∂[ν] φ) x) = ∑ μ, π μ x * ∂[ν] (∂[μ] φ) x := by
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [congrFun (deriv_commute φ hφ (u := μ) (v := ν)) x]
  rw [hcomm, sub_mul, Finset.sum_mul]
  ring

/-- **Local conservation of momentum/energy — Noether's translation theorem (Kälbermann eq. 10).**  On shell,
i.e. under the Euler–Lagrange equation `∂L/∂φ = ∂_μ π^μ`, the canonical stress-energy current is divergence
free: `∂_μ T^μ_ν = 0`.  This is the pointwise translation instance of
`Physlib.Mathematics.LovelockRund.NoetherCurrentData.divergence_eq_zero` — the on-shell right-hand side of
`canonicalStressCurrent_div` vanishes because the Euler–Lagrange residual does. -/
theorem canonicalStress_conservation (φ L : Space n → ℝ) (π : Fin n → Space n → ℝ) (ν : Fin n)
    (dLdφ : Space n → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hL : Differentiable ℝ L) (hπ : ∀ μ, Differentiable ℝ (π μ))
    (hchain : ∀ x, ∂[ν] L x = dLdφ x * ∂[ν] φ x + ∑ μ, π μ x * ∂[ν] (∂[μ] φ) x)
    (hEL : ∀ x, dLdφ x = ∑ μ, ∂[μ] (π μ) x) (x : Space n) :
    (∇ ⬝ canonicalStressCurrent φ L π ν) x = 0 := by
  rw [canonicalStressCurrent_div φ L π ν dLdφ hφ hL hπ hchain x, hEL x, sub_self, zero_mul]

/-- The **conjugate (probability) four-current** `J^μ = ∂L/∂(∂_μ φ) = π^μ` of a field `φ`. -/
def conjugateCurrent (π : Fin n → Space n → ℝ) : Space n → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (fun μ => π μ x)

@[simp]
lemma conjugateCurrent_apply (π : Fin n → Space n → ℝ) (x : Space n) (μ : Fin n) :
    conjugateCurrent π x μ = π μ x := rfl

/-- **Continuity from a cyclic coordinate (Kälbermann eq. 11).**  When the Lagrangian does not depend on the
field itself, `∂L/∂φ = 0` (an ignorable/cyclic coordinate — the Madelung phase `S`), the Euler–Lagrange
equation `∂_μ π^μ = ∂L/∂φ` collapses to the continuity equation for the conjugate four-current,
`∂_μ J^μ = 0`.  This is the source-free instance of `Physlib.Mathematics.LovelockRund.BalanceLawData`, with
the phase Euler–Lagrange residual as the (vanishing) source. -/
theorem conjugateCurrent_continuity (π : Fin n → Space n → ℝ) (dLdφ : Space n → ℝ)
    (hcyclic : dLdφ = 0) (hEL : ∀ x, dLdφ x = ∑ μ, ∂[μ] (π μ) x) (x : Space n) :
    (∇ ⬝ conjugateCurrent π) x = 0 := by
  have hJ : (∇ ⬝ conjugateCurrent π) x = ∑ μ, ∂[μ] (π μ) x := by
    simp only [Space.div, conjugateCurrent_apply]
  rw [hJ, ← hEL x, hcyclic, Pi.zero_apply]

/-!
## The field multiplet (Kälbermann eq. 10 with amplitude `R` and phase `S`)

The physical Madelung Lagrangian depends on *both* the amplitude `R` and the phase `S`, so the canonical
stress tensor sums the flux `π_a^μ ∂_ν φ_a` over the field index `a ∈ {R, S}` while subtracting a *single*
shared `δ^μ_ν L`. The following generalise the single-field results to an arbitrary finite field multiplet.
-/

/-- The space derivative commutes with a finite sum. -/
lemma deriv_fun_sum {ι : Type*} (s : Finset ι) (g : ι → Space n → ℝ) (μ : Fin n)
    (hg : ∀ a, Differentiable ℝ (g a)) (x : Space n) :
    ∂[μ] (fun y => ∑ a ∈ s, g a y) x = ∑ a ∈ s, ∂[μ] (g a) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [Space.deriv_const]
  | @insert b s hb ih =>
    have hstep : (fun y => ∑ a ∈ insert b s, g a y)
        = (g b) + (fun y => ∑ a ∈ s, g a y) := by
      funext y; rw [Finset.sum_insert hb]; rfl
    have hsum_d : Differentiable ℝ (fun y => ∑ a ∈ s, g a y) :=
      Differentiable.fun_sum (fun a _ => hg a)
    rw [hstep, deriv_add _ _ (hg b) hsum_d, Pi.add_apply, ih, Finset.sum_insert hb]

/-- The **canonical stress-energy current for a finite field multiplet** in translation direction `ν`:
`T^μ_ν = ∑_a π_a^μ ∂_ν φ_a − δ^μ_ν L`. -/
def canonicalStressCurrentMulti {ι : Type*} [Fintype ι] (φ : ι → Space n → ℝ) (L : Space n → ℝ)
    (π : ι → Fin n → Space n → ℝ) (ν : Fin n) : Space n → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (fun μ => (∑ a, π a μ x * ∂[ν] (φ a) x) - (if μ = ν then L x else 0))

@[simp]
lemma canonicalStressCurrentMulti_apply {ι : Type*} [Fintype ι] (φ : ι → Space n → ℝ) (L : Space n → ℝ)
    (π : ι → Fin n → Space n → ℝ) (ν : Fin n) (x : Space n) (μ : Fin n) :
    canonicalStressCurrentMulti φ L π ν x μ
      = (∑ a, π a μ x * ∂[ν] (φ a) x) - (if μ = ν then L x else 0) := rfl

/-- **Noether's translation identity for a field multiplet.**  `∂_μ T^μ_ν = ∑_a (∂_μ π_a^μ − ∂L/∂φ_a) ∂_ν φ_a`
— the same Leibniz / `δ^μ_ν` / Clairaut mechanism as the single-field case, summed over the fields. -/
theorem canonicalStressMulti_div {ι : Type*} [Fintype ι] (φ : ι → Space n → ℝ) (L : Space n → ℝ)
    (π : ι → Fin n → Space n → ℝ) (ν : Fin n) (dLdφ : ι → Space n → ℝ)
    (hφ : ∀ a, ContDiff ℝ 2 (φ a)) (hL : Differentiable ℝ L)
    (hπ : ∀ a μ, Differentiable ℝ (π a μ))
    (hchain : ∀ x, ∂[ν] L x
      = (∑ a, dLdφ a x * ∂[ν] (φ a) x) + ∑ a, ∑ μ, π a μ x * ∂[ν] (∂[μ] (φ a)) x) (x : Space n) :
    (∇ ⬝ canonicalStressCurrentMulti φ L π ν) x
      = ∑ a, ((∑ μ, ∂[μ] (π a μ) x) - dLdφ a x) * ∂[ν] (φ a) x := by
  have hf1d : ∀ μ, Differentiable ℝ (fun y => ∑ a, π a μ y * ∂[ν] (φ a) y) :=
    fun μ => Differentiable.fun_sum (fun a _ => (hπ a μ).mul (deriv_differentiable (hφ a) ν))
  have hf2d : ∀ μ, Differentiable ℝ (fun y : Space n => if μ = ν then L y else 0) := by
    intro μ
    by_cases hμν : μ = ν
    · rw [show (fun y : Space n => if μ = ν then L y else 0) = (fun y => L y) from
        funext fun _ => if_pos hμν]
      exact hL
    · rw [show (fun y : Space n => if μ = ν then L y else 0) = (fun _ => 0) from
        funext fun _ => if_neg hμν]
      exact differentiable_const 0
  have hdiv : (∇ ⬝ canonicalStressCurrentMulti φ L π ν) x
      = (∑ μ, ∂[μ] (fun y => ∑ a, π a μ y * ∂[ν] (φ a) y) x)
        - ∑ μ, ∂[μ] (fun y : Space n => if μ = ν then L y else 0) x := by
    rw [← Finset.sum_sub_distrib]
    simp only [Space.div]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    have hinner : (fun y => canonicalStressCurrentMulti φ L π ν y μ)
        = (fun y => ∑ a, π a μ y * ∂[ν] (φ a) y) - (fun y : Space n => if μ = ν then L y else 0) := by
      funext y; simp [Pi.sub_apply]
    rw [hinner, deriv_sub _ _ (hf1d μ) (hf2d μ), Pi.sub_apply]
  rw [hdiv]
  have hleib : (∑ μ, ∂[μ] (fun y => ∑ a, π a μ y * ∂[ν] (φ a) y) x)
      = ∑ μ, ∑ a, (π a μ x * ∂[μ] (∂[ν] (φ a)) x + ∂[μ] (π a μ) x * ∂[ν] (φ a) x) := by
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [deriv_fun_sum Finset.univ (fun a => fun y => π a μ y * ∂[ν] (φ a) y) μ
        (fun a => (hπ a μ).mul (deriv_differentiable (hφ a) ν)) x]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show (fun y => π a μ y * ∂[ν] (φ a) y) = (π a μ) • (∂[ν] (φ a)) from rfl,
      deriv_smul (hπ a μ).differentiableAt (deriv_differentiable (hφ a) ν).differentiableAt]
    simp only [smul_eq_mul]
  have hδsum : (∑ μ, ∂[μ] (fun y : Space n => if μ = ν then L y else 0) x) = ∂[ν] L x := by
    refine (Finset.sum_eq_single (a := ν) ?_ ?_).trans ?_
    · intro μ _ hμν
      rw [show (fun y : Space n => if μ = ν then L y else 0) = (fun _ => 0) from
        funext fun _ => if_neg hμν]
      exact Space.deriv_const (0 : ℝ) μ
    · intro h; exact absurd (Finset.mem_univ ν) h
    · simp
  rw [hleib, hδsum, hchain]
  simp only [Finset.sum_add_distrib]
  have hP : (∑ μ, ∑ a, π a μ x * ∂[μ] (∂[ν] (φ a)) x)
      = ∑ a, ∑ μ, π a μ x * ∂[ν] (∂[μ] (φ a)) x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun μ _ => ?_))
    rw [congrFun (deriv_commute (φ a) (hφ a) (u := μ) (v := ν)) x]
  have hQ : (∑ μ, ∑ a, ∂[μ] (π a μ) x * ∂[ν] (φ a) x)
      = ∑ a, (∑ μ, ∂[μ] (π a μ) x) * ∂[ν] (φ a) x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => by rw [Finset.sum_mul])
  rw [hP, hQ,
    show (∑ a, ((∑ μ, ∂[μ] (π a μ) x) - dLdφ a x) * ∂[ν] (φ a) x)
        = (∑ a, (∑ μ, ∂[μ] (π a μ) x) * ∂[ν] (φ a) x) - ∑ a, dLdφ a x * ∂[ν] (φ a) x from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun a _ => by rw [sub_mul])]
  ring

/-- **Momentum/energy conservation for a field multiplet (Kälbermann eq. 10).**  On shell — the
Euler–Lagrange equations `∂L/∂φ_a = ∂_μ π_a^μ` for every field — the multiplet canonical stress-energy
current is divergence free: `∂_μ T^μ_ν = 0`. -/
theorem canonicalStressMulti_conservation {ι : Type*} [Fintype ι] (φ : ι → Space n → ℝ) (L : Space n → ℝ)
    (π : ι → Fin n → Space n → ℝ) (ν : Fin n) (dLdφ : ι → Space n → ℝ)
    (hφ : ∀ a, ContDiff ℝ 2 (φ a)) (hL : Differentiable ℝ L)
    (hπ : ∀ a μ, Differentiable ℝ (π a μ))
    (hchain : ∀ x, ∂[ν] L x
      = (∑ a, dLdφ a x * ∂[ν] (φ a) x) + ∑ a, ∑ μ, π a μ x * ∂[ν] (∂[μ] (φ a)) x)
    (hEL : ∀ a x, dLdφ a x = ∑ μ, ∂[μ] (π a μ) x) (x : Space n) :
    (∇ ⬝ canonicalStressCurrentMulti φ L π ν) x = 0 := by
  rw [canonicalStressMulti_div φ L π ν dLdφ hφ hL hπ hchain x]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [hEL a x, sub_self, zero_mul]

/-!
## Galilean covariance (Kälbermann eqs. 12–13)

Under an infinitesimal Galilean boost `δv` (Kälbermann eq. 6), the Madelung phase picks up `−m δv·r` and the
time derivative shifts `∂_t ↦ ∂_t − δv·∇`, so to first order the fields vary by `δS_t = −δv·∇S`,
`δR_t = −δv·∇R`, and `δ(∇S) ∝ m δv`. Feeding these through the chain rule, the boost variation of the
Lagrangian is (eq. 12)

  `δL = ⟪δv, p⟫ − m⟪δv, J⟫`,   `p = −(∂L/∂S_t)∇S − (∂L/∂R_t)∇R`,  `J = −∂L/∂∇S`,

with `p` the canonical momentum density (the `T^0_j` of `canonicalStressCurrent`) and `J` the probability
flux (the spatial part of `conjugateCurrent`). Covariance of the action means this variation is a *total
gradient*, `δL = ⟪δv, ∇f⟫` for every `δv`; non-degeneracy of the inner product then forces (eq. 13)

  `p = m J + ∇f`.

Integrated over an asymptotically vanishing state the gradient drops out, giving `∫p = m∫J = m v` — exactly the
`fieldMom = m · avgVel` hypothesis of `ehrenfest_from_galilean` (§F). The `∇f = 0` strict-symmetry case is
`galilean_symmetric_momentum`. Spatial vectors live in a real inner-product space `E`; the derivation of the
field variations from the boost (eq. 6) and the spatial integration are the modelling boundaries, as for the
chain-rule input to the Noether identities above.
-/

section Galilean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped RealInnerProductSpace

/-- The **canonical spatial momentum density** `p = −(∂L/∂S_t)∇S − (∂L/∂R_t)∇R` (Kälbermann eq. 10). -/
def canonicalMomentumDensity (πS0 πR0 : ℝ) (gradS gradR : E) : E := -(πS0 • gradS + πR0 • gradR)

/-- The **probability flux** `J = −∂L/∂∇S` (Kälbermann eq. 11); `fluxS := ∂L/∂∇S`. -/
def probabilityFlux (fluxS : E) : E := -fluxS

/-- **[Kälbermann eq. 12] The Galilean-boost variation of the Lagrangian.**  The chain-rule variation under a
boost `δv`, `δL = (∂L/∂S_t)(−δv·∇S) + (∂L/∂R_t)(−δv·∇R) + m(δv·∂L/∂∇S)`, equals `⟪δv, p⟫ − m⟪δv, J⟫`. -/
theorem galilean_boost_variation (m πS0 πR0 : ℝ) (gradS gradR fluxS δv : E) :
    πS0 * (-⟪δv, gradS⟫) + πR0 * (-⟪δv, gradR⟫) + m * ⟪δv, fluxS⟫
      = ⟪δv, canonicalMomentumDensity πS0 πR0 gradS gradR⟫
        - m * ⟪δv, probabilityFlux fluxS⟫ := by
  simp only [canonicalMomentumDensity, probabilityFlux, inner_neg_right, inner_add_right,
    real_inner_smul_right]
  ring

/-- **[Kälbermann eq. 13] Galilean covariance forces `p = mJ + ∇f`.**  If the boost variation is a total
gradient for every boost — `⟪δv, p⟫ − m⟪δv, J⟫ = ⟪δv, ∇f⟫` for all `δv` (covariance up to a boundary term) —
then non-degeneracy of the inner product gives `p = m • J + ∇f`. -/
theorem galilean_covariance_momentum (m : ℝ) (p J gradf : E)
    (hcov : ∀ δv : E, ⟪δv, p⟫ - m * ⟪δv, J⟫ = ⟪δv, gradf⟫) :
    p = m • J + gradf := by
  have h : ∀ δv : E, ⟪δv, p - (m • J + gradf)⟫ = 0 := by
    intro δv
    rw [inner_sub_right, inner_add_right, real_inner_smul_right]
    have hd := hcov δv
    linarith
  have hz : p - (m • J + gradf) = 0 := by
    have hw := h (p - (m • J + gradf))
    rwa [inner_self_eq_zero] at hw
  rwa [sub_eq_zero] at hz

/-- **[Kälbermann eqs. 12–13] Galilean covariance of the Schrödinger action: `p = mJ + ∇f`.**  Combining the
boost variation (eq. 12) with covariance (the variation is a total gradient), the canonical momentum density is
the mass times the probability flux up to a gradient. -/
theorem galilean_covariance_p_eq_mJ (m πS0 πR0 : ℝ) (gradS gradR fluxS gradf : E)
    (hcov : ∀ δv : E,
      πS0 * (-⟪δv, gradS⟫) + πR0 * (-⟪δv, gradR⟫) + m * ⟪δv, fluxS⟫ = ⟪δv, gradf⟫) :
    canonicalMomentumDensity πS0 πR0 gradS gradR = m • probabilityFlux fluxS + gradf := by
  refine galilean_covariance_momentum m _ (probabilityFlux fluxS) gradf (fun δv => ?_)
  rw [← galilean_boost_variation m πS0 πR0 gradS gradR fluxS δv]
  exact hcov δv

/-- **Strict Galilean invariance gives `p = m J` (the field-level `∫p = m v`).**  When the boost is an exact
symmetry (no boundary term, `∇f = 0`), the canonical momentum density is exactly the mass times the flux — the
pointwise field version of the `fieldMom = m · avgVel` hypothesis of `ehrenfest_from_galilean` (§F). -/
theorem galilean_symmetric_momentum (m πS0 πR0 : ℝ) (gradS gradR fluxS : E)
    (hinv : ∀ δv : E,
      πS0 * (-⟪δv, gradS⟫) + πR0 * (-⟪δv, gradR⟫) + m * ⟪δv, fluxS⟫ = 0) :
    canonicalMomentumDensity πS0 πR0 gradS gradR = m • probabilityFlux fluxS := by
  have h := galilean_covariance_p_eq_mJ m πS0 πR0 gradS gradR fluxS 0
    (fun δv => by rw [hinv δv, inner_zero_right])
  rwa [add_zero] at h

/-!
### The field variations from the boost transformation itself (Kälbermann eq. 6)

The variations fed into `galilean_boost_variation` are not postulated — they are *derived* from the Galilean
boost of eq. 6 (`r ↦ r − t δv`, `ψ ↦ e^{iφ}ψ`, `φ = m δv·r`). The coordinate shift gives the operator rule
`∂_t ↦ ∂_t − δv·∇` (so `δS_t = −δv·∇S`, `δR_t = −δv·∇R`), and the phase gives `δ(∇S) = ∇φ = m δv`.
-/

variable [CompleteSpace E]

open scoped Topology in
/-- **[Kälbermann eq. 6] The boost transformation of a field's time derivative.**  Under the Galilean
coordinate shift `r ↦ r − t δv`, the boosted field `F(x − t δv)` has time derivative `−δv·∇F` at `t = 0`.
This *derives* the operator rule `∂_t ↦ ∂_t − δv·∇` (eq. 6) from the coordinate transformation, so the boost
field variations are `δS_t = −δv·∇S` and `δR_t = −δv·∇R`. -/
theorem boost_time_variation (F : E → ℝ) (gradF x δv : E) (hF : HasGradientAt F gradF x) :
    HasDerivAt (fun t : ℝ => F (x - t • δv)) (- ⟪δv, gradF⟫) 0 := by
  have hsmul : HasDerivAt (fun t : ℝ => t • δv) δv 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const δv
  have hcurve : HasDerivAt (fun t : ℝ => x - t • δv) (-δv) 0 := hsmul.const_sub x
  have hy : x = (fun t : ℝ => x - t • δv) 0 := by simp
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasGradientAt_iff_hasFDerivAt.mp hF) hcurve hy
  have hval : (InnerProductSpace.toDual ℝ E gradF) (-δv) = - ⟪δv, gradF⟫ := by
    rw [map_neg, InnerProductSpace.toDual_apply_apply, real_inner_comm gradF δv]
  rw [hval] at hcomp
  exact hcomp

/-- **[Kälbermann eq. 6] The boost transformation of the phase gradient.**  The Galilean phase
`φ(r) = m δv·r` has gradient `m δv`, so the boost variation of the phase gradient is `δ(∇S) = ∇φ = m δv`. -/
theorem boost_phase_gradient (m : ℝ) (δv x : E) :
    HasGradientAt (fun r => m * ⟪δv, r⟫) (m • δv) x := by
  have hfun : (fun r : E => m * ⟪δv, r⟫) = ⇑(InnerProductSpace.toDual ℝ E (m • δv)) := by
    funext r; rw [InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  exact (InnerProductSpace.toDual ℝ E (m • δv)).hasFDerivAt

end Galilean

/-!
## Spatial integration over an asymptotically vanishing state (Kälbermann eqs. 15–16)

The paper closes the loop by integrating the *local* field laws over space "for asymptotically vanishing
wavefunctions", where every boundary term drops out. Formalized faithfully, that assumption is the vanishing
of the integral of a spatial divergence / gradient (`∫∇·J = 0`, `∫∇f = 0`), and the integrated relations then
follow by linearity of the integral:

* eq. 13 `p = mJ + ∇f`, integrated, gives `∫p = m∫J` — the total momentum is the mass times the total flux,
  the field-theoretic origin of the `fieldMom = m · avgVel` hypothesis of `ehrenfest_from_galilean` (§F);
* eq. 11 continuity `∂_t ρ + ∇·J = 0`, integrated, gives `∫∂_t ρ = 0` — total probability is stationary;
* eq. 14 momentum balance `∂_t p_j + ∂_i T_ij + (∂_j U) ρ = 0`, integrated, gives `∫∂_t p_j = −∫(∂_j U)ρ = ⟨F_j⟩`
  (eq. 15) — Newton's second law for the total momentum.

The remaining step from these to the averaged `ehrenfest_from_galilean` — pulling `∂_t` outside the spatial
integral (differentiation under the integral) — is the analytic bridge left to §F's abstract `HasDerivAt`
hypotheses.
-/

section SpatialIntegration

open MeasureTheory
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **[Kälbermann eq. 13 integrated] `∫p = m∫J`.**  Integrating `p = m J + ∇f` over an asymptotically vanishing
state, where `∫∇f = 0`, gives the total momentum as the mass times the total flux — the field-theoretic origin
of the `fieldMom = m · avgVel` hypothesis of `ehrenfest_from_galilean` (§F). -/
theorem integrated_momentum_eq_mass_flux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (m : ℝ) (p J gradf : X → E)
    (hpoint : ∀ x, p x = m • J x + gradf x) (hgradf : ∫ x, gradf x ∂μ = 0)
    (hJ : Integrable J μ) (hg : Integrable gradf μ) :
    ∫ x, p x ∂μ = m • ∫ x, J x ∂μ :=
  calc ∫ x, p x ∂μ
      = ∫ x, (m • J x + gradf x) ∂μ := by simp_rw [hpoint]
    _ = ∫ x, m • J x ∂μ + ∫ x, gradf x ∂μ := integral_add (hJ.smul m) hg
    _ = m • ∫ x, J x ∂μ + ∫ x, gradf x ∂μ := by rw [integral_smul]
    _ = m • ∫ x, J x ∂μ := by rw [hgradf, add_zero]

/-- **[Kälbermann eq. 11 integrated] Total probability is stationary.**  For the local continuity balance
`∂_t ρ + ∇·J = 0`, if the spatial divergence integrates to zero (`∫∇·J = 0`), then `∫∂_t ρ = 0`: the total
probability `∫ρ` has vanishing time rate. -/
theorem integrated_density_rate_zero (rhoDot divJ : X → ℝ)
    (hlocal : ∀ x, rhoDot x + divJ x = 0) (hdiv : ∫ x, divJ x ∂μ = 0) :
    ∫ x, rhoDot x ∂μ = 0 := by
  have hr : ∀ x, rhoDot x = - divJ x := fun x => by linarith [hlocal x]
  simp_rw [hr]
  rw [integral_neg, hdiv, neg_zero]

/-- **[Kälbermann eqs. 14–15 integrated] Newton's second law for the total momentum.**  For the local
momentum balance `∂_t p_j + ∂_i T_ij + (∂_j U)ρ = 0` (eq. 14), if the stress divergence integrates to zero
(`∫∂_i T_ij = 0`), then `∫∂_t p_j = −∫(∂_j U)ρ = ⟨F_j⟩` (eq. 15). -/
theorem integrated_momentum_rate_eq_force (pDot divT force : X → ℝ)
    (hlocal : ∀ x, pDot x + divT x + force x = 0) (hdivT : ∫ x, divT x ∂μ = 0)
    (hdivT_int : Integrable divT μ) (hforce_int : Integrable force μ) :
    ∫ x, pDot x ∂μ = - ∫ x, force x ∂μ := by
  have hp : ∀ x, pDot x = - (divT x + force x) := fun x => by linarith [hlocal x]
  simp_rw [hp]
  rw [integral_neg, integral_add hdivT_int hforce_int, hdivT, zero_add]

/-- **The Leibniz integral rule (differentiation under the integral).**  If the parametrised integrand `F s`
is dominated on a neighbourhood of `t` by an integrable `bound` and is differentiable in the parameter there
with derivative `F' s`, then `d/dt ∫ F(t,·) = ∫ ∂_t F(t,·)`.  A specialisation of Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` to the unit ball around `t`; this discharges the
differentiation-under-the-integral step of the field-theory → Ehrenfest bridge. -/
theorem leibniz_integral_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F F' : ℝ → X → E} {t : ℝ} {bound : X → ℝ}
    (hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) μ) (hF_int : Integrable (F t) μ)
    (hF'_meas : AEStronglyMeasurable (F' t) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t 1, ‖F' s x‖ ≤ bound x) (bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t 1, HasDerivAt (fun r => F r x) (F' s x) s) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' t x ∂μ) t :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t one_pos) hF_meas hF_int
    hF'_meas h_bound bound_int h_diff).2

/-- **Total probability is conserved (continuity ⟹ §F).**  From the local continuity balance
`∂_t ρ + ∇·J = 0`, the spatial-divergence decay `∫∇·J = 0`, and the domination hypotheses on `ρ, ρDot`, the
total probability `∫ρ` has zero time derivative — the conserved-current hypothesis behind
`ehrenfest_from_galilean` (§F).  The differentiation under the integral is proved by
`leibniz_integral_hasDerivAt`, so nothing is assumed beyond integrable domination. -/
theorem total_charge_hasDerivAt (ρ ρDot divJ : ℝ → X → ℝ) (t : ℝ) {bound : X → ℝ}
    (hlocal : ∀ x, ρDot t x + divJ t x = 0) (hdiv : ∫ x, divJ t x ∂μ = 0)
    (hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (ρ s) μ) (hF_int : Integrable (ρ t) μ)
    (hF'_meas : AEStronglyMeasurable (ρDot t) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t 1, ‖ρDot s x‖ ≤ bound x) (bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t 1, HasDerivAt (fun r => ρ r x) (ρDot s x) s) :
    HasDerivAt (fun s => ∫ x, ρ s x ∂μ) 0 t := by
  have hL := leibniz_integral_hasDerivAt hF_meas hF_int hF'_meas h_bound bound_int h_diff
  rwa [integrated_density_rate_zero (ρDot t) (divJ t) hlocal hdiv] at hL

/-- **Newton's second law for the total momentum (momentum balance ⟹ §F `hmom`).**  From the local balance
`∂_t p_j + ∂_i T_ij + (∂_j U)ρ = 0`, the stress decay `∫∂_i T_ij = 0`, and the domination hypotheses on
`p, pDot`, the total momentum obeys `d/dt ∫p_j = −∫(∂_j U)ρ = ⟨F_j⟩` in `HasDerivAt` form — exactly the
`hmom : HasDerivAt fieldMom (force t) t` hypothesis of `ehrenfest_from_galilean` (§F), with `fieldMom = ∫p_j`
and `force t = ⟨F_j⟩ = −∫(∂_j U)ρ`.  With `integrated_momentum_eq_mass_flux` (`∫p = m∫J`, the `hgal` input),
this supplies the averaged Ehrenfest theorem's hypotheses from the local Lagrangian field theory, the
differentiation under the integral now proved (`leibniz_integral_hasDerivAt`). -/
theorem total_momentum_hasDerivAt (p pDot divT force : ℝ → X → ℝ) (t : ℝ) {bound : X → ℝ}
    (hlocal : ∀ x, pDot t x + divT t x + force t x = 0) (hdivT : ∫ x, divT t x ∂μ = 0)
    (hdivT_int : Integrable (divT t) μ) (hforce_int : Integrable (force t) μ)
    (hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (p s) μ) (hF_int : Integrable (p t) μ)
    (hF'_meas : AEStronglyMeasurable (pDot t) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t 1, ‖pDot s x‖ ≤ bound x) (bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t 1, HasDerivAt (fun r => p r x) (pDot s x) s) :
    HasDerivAt (fun s => ∫ x, p s x ∂μ) (- ∫ x, force t x ∂μ) t := by
  have hL := leibniz_integral_hasDerivAt hF_meas hF_int hF'_meas h_bound bound_int h_diff
  rwa [integrated_momentum_rate_eq_force (pDot t) (divT t) (force t) hlocal hdivT hdivT_int
    hforce_int] at hL

end SpatialIntegration

end Physlib.Mathematics.LovelockRund

end

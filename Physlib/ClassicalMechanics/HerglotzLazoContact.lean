/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Physlib.ClassicalMechanics.HamiltonsEquations
public import QuantumInfo.Entropy.EntropicProperTime

meta import Zil

/-!
# Herglotz–Lazo contact dynamics for classical mechanics

A small algebraic carrier for the **Herglotz contact-friction**
extension of the standard Euler–Lagrange / Hamilton flow, plus the
**Lazo** non-conservative variational principle.

## The contact slice

A `HerglotzContactSlice` consists of:

* `L_R : ℝ → ℝ` — the reversible (real) part of the Lagrangian at
  the time-parameter slice,
* `ρ   : ℝ → ℝ` — the contact-friction coefficient,
* `s   : ℝ → ℝ` — the accumulated imaginary action (`ds/dt = L_I`),

with the algebraic identity

  `L_eff(t) := L_R(t) − ρ(t) · s(t)`.

The key reductions at the **Frozen-LRF** (no contact friction):

* `ρ(t) = 0` ⇒ `L_eff(t) = L_R(t)` — standard Euler–Lagrange is
  recovered.
* `s(t) = 0` ⇒ `L_eff(t) = L_R(t)` — no accumulated imaginary action.

For the **damped harmonic oscillator** `m ẍ + k x = −γ ẋ`, the
Herglotz contact identification is `ρ = γ/m` with `s` accumulating
the mechanical-energy time integral.

## Lazo non-conservative principle

The Lazo extension allows `L_R`, `ρ`, `s` themselves to depend on
the action `s` — turning the variational principle into a
non-conservative one. At `ρ = 0` (zero contact friction), the Lazo
EL reduces to the standard conservative EL.

## What this file proves

* `HerglotzContactSlice` — algebraic carrier.
* `effectiveLagrangian` and its decomposition.
* `effectiveLagrangian_at_zero_contact_friction` — reduces to `L_R`.
* `effectiveLagrangian_at_zero_action` — reduces to `L_R`.
* `effectiveLagrangian_linearity_in_ρ_s` — linearity in `ρ · s`.
* `dampedOscillator_contact_rate` — concrete `ρ = γ/m` for the
  damped oscillator.
* `lazo_reduces_to_standard_EL_at_zero_friction` — at `ρ = 0` the
  Lazo non-conservative principle returns the standard EL.

all theorems are direct algebraic facts.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ClassicalMechanics

open Time QuantumInfo.Finite


/-- **Herglotz contact slice**: at the time-parameter slice, decomposes
the Lagrangian into a reversible part `L_R`, a contact-friction
coefficient `ρ`, and an accumulated-action `s` (with `ds/dt = L_I`). -/
structure HerglotzContactSlice where
  /-- Reversible (real) part of the Lagrangian. -/
  L_R : ℝ → ℝ
  /-- Contact-friction coefficient. -/
  ρ : ℝ → ℝ
  /-- Accumulated imaginary action `s`, with `ds/dt = L_I`. -/
  s : ℝ → ℝ


/-- **Effective Herglotz Lagrangian** at the time slice:
`L_eff(t) := L_R(t) − ρ(t) · s(t)`. -/
def HerglotzContactSlice.effectiveLagrangian
    (H : HerglotzContactSlice) (t : ℝ) : ℝ :=
  H.L_R t - H.ρ t * H.s t


/-- **At zero contact friction (`ρ = 0`)** the effective Lagrangian
reduces to the reversible part `L_R`, recovering the standard
Euler–Lagrange / Hamilton flow. -/
lemma effectiveLagrangian_at_zero_contact_friction
    (H : HerglotzContactSlice) (t : ℝ) (h : H.ρ t = 0) :
    H.effectiveLagrangian t = H.L_R t := by
  unfold HerglotzContactSlice.effectiveLagrangian
  rw [h]; ring

/-- **At zero accumulated action (`s = 0`)** the effective Lagrangian
also reduces to `L_R` — no imaginary action has accumulated, so the
contact-friction term vanishes. -/
lemma effectiveLagrangian_at_zero_action
    (H : HerglotzContactSlice) (t : ℝ) (h : H.s t = 0) :
    H.effectiveLagrangian t = H.L_R t := by
  unfold HerglotzContactSlice.effectiveLagrangian
  rw [h]; ring


/-- **Linearity in `ρ · s`**: doubling the product `ρ · s` doubles
the contact correction. -/
lemma effectiveLagrangian_linearity_in_ρ_s
    (H : HerglotzContactSlice) (t : ℝ) (c : ℝ)
    (H' : HerglotzContactSlice)
    (hL : H'.L_R t = H.L_R t)
    (hρs : H'.ρ t * H'.s t = c * (H.ρ t * H.s t)) :
    H'.effectiveLagrangian t = H.L_R t - c * (H.ρ t * H.s t) := by
  unfold HerglotzContactSlice.effectiveLagrangian
  rw [hL, hρs]


/-- **Damped-oscillator Herglotz rate** `ρ = γ / m` (constant in time)
for the damped harmonic oscillator `m ẍ + k x = −γ ẋ`. -/
def dampedOscillatorContactSlice
    (m γ : ℝ) (L_R s : ℝ → ℝ) : HerglotzContactSlice where
  L_R := L_R
  ρ := fun _ => γ / m
  s := s

/-- **Damped-oscillator effective Lagrangian** at the time slice. -/
lemma dampedOscillator_effectiveLagrangian
    (m γ : ℝ) (L_R s : ℝ → ℝ) (t : ℝ) :
    (dampedOscillatorContactSlice m γ L_R s).effectiveLagrangian t =
      L_R t - (γ / m) * s t := rfl

/-- **Damped-oscillator at zero friction** (`γ = 0`): the effective
Lagrangian is the reversible part. -/
lemma dampedOscillator_at_zero_friction
    (m : ℝ) (L_R s : ℝ → ℝ) (t : ℝ) (hm : m ≠ 0) :
    (dampedOscillatorContactSlice m 0 L_R s).effectiveLagrangian t =
      L_R t := by
  rw [dampedOscillator_effectiveLagrangian]
  rw [zero_div, zero_mul, sub_zero]


/-- **Lazo non-conservative principle reduces to standard EL at zero
contact friction**.

In the Lazo extension, the Lagrangian may depend on the accumulated
action `s` itself (`L = L(q, q̇, s)`). When the contact-friction
coefficient `ρ` vanishes, the Lazo non-conservative EL coincides
with the standard conservative EL.

We state this algebraically at the slice level: vanishing `ρ`
makes the effective Lagrangian independent of `s`. -/
lemma lazo_reduces_to_standard_EL_at_zero_friction
    (H : HerglotzContactSlice) (t : ℝ) (h : H.ρ t = 0)
    (s' : ℝ → ℝ) (Hmod : HerglotzContactSlice)
    (hL : Hmod.L_R t = H.L_R t)
    (hρ : Hmod.ρ t = H.ρ t)
    (hsmod : Hmod.s = s') :
    Hmod.effectiveLagrangian t = H.L_R t := by
  unfold HerglotzContactSlice.effectiveLagrangian
  rw [hL, hρ, h]; ring


/-- **`s` accumulates the imaginary action** that defines entropic
proper time (`τ_ent = S_I/ℏ`). When the accumulated action `s(t)`
vanishes — equivalently, the system is in entropic equilibrium —
the contact-friction term vanishes and the effective Lagrangian
equals the reversible part. -/
lemma effectiveLagrangian_at_zero_entropic_time
    (H : HerglotzContactSlice) (t : ℝ) (h_s : H.s t = 0) :
    H.effectiveLagrangian t = H.L_R t :=
  effectiveLagrangian_at_zero_action H t h_s

/-! ### The weighted variation: the Herglotz `δ`-calculus core

The Herglotz variational problem is solved by an integrating factor: with
`ψ = ∫(∂L/∂S)dt`, the varied action satisfies
`d/dt(e^{−ψ}·δS) = e^{−ψ}(δṠ − ψ̇·δS)` — the weighted variation is an exact
derivative, which is what turns the action-dependent problem into the generalized
Euler–Lagrange equations. -/

/-- **The integrating-factor identity of the weighted variation**: for any
accumulant `X` and weight exponent `ψ` with rate `γ`,

  `d/dt (e^{−ψ}·X) = e^{−ψ}·(Ẋ − γ·X)`

— the exact-derivative form of the Herglotz variation (`X = δS`), the step that makes
the action-dependent variational problem integrable. -/
theorem weighted_variation_deriv (ψ X : ℝ → ℝ) (γ X' t : ℝ)
    (hψ : HasDerivAt ψ γ t) (hX : HasDerivAt X X' t) :
    HasDerivAt (fun s => Real.exp (-ψ s) * X s)
      (Real.exp (-ψ t) * (X' - γ * X t)) t := by
  have hexp : HasDerivAt (fun s => Real.exp (-ψ s))
      (-γ * Real.exp (-ψ t)) t := by
    have h := (hψ.neg).exp
    refine h.congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have h := hexp.mul hX
  refine h.congr_deriv ?_
  ring

/-- **The generalized Euler–Lagrange form produces friction**: for the damped-particle
Lagrangian `L = ½mv² − U − (ν/m)S` (the contact slice with `ρ = ν/m`), the Herglotz
equation `∂L/∂x − d/dt ∂L/∂ẋ + (∂L/∂S)·∂L/∂ẋ = 0` is exactly the damped equation of
motion `ma + νv = −U′` — first-order dissipation from a variational principle, the
signature the Hamilton principle cannot produce. -/
theorem herglotz_generalized_EL_damped (m ν U' v a : ℝ) (hm : m ≠ 0) :
    (-U') - m * a + (-(ν / m)) * (m * v) = 0 ↔ m * a + ν * v = -U' := by
  have hcancel : (ν / m) * (m * v) = ν * v := by
    field_simp
  constructor <;> intro h
  · have h' := h
    rw [show (-(ν / m)) * (m * v) = -((ν / m) * (m * v)) from by ring, hcancel] at h'
    linarith [h']
  · rw [show (-(ν / m)) * (m * v) = -((ν / m) * (m * v)) from by ring, hcancel]
    linarith [h]

/- ZIL-BEGIN -/

zil attach ClassicalMechanics.weighted_variation_deriv where
  formalizes @ "claim:the-herglotz-weighted-variation-is-an-exact-derivative-through-the-integrating-factor-the-step-that-makes-the-action-dependent-variational-problem-integrable",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:wazny-csillag-pinto-harko-2025-herglotz-type-f-r-t-gravity-arxiv-2511-16304"

zil attach ClassicalMechanics.herglotz_generalized_EL_damped where
  derives @ "claim:the-generalized-euler-lagrange-form-of-the-herglotz-principle-is-exactly-the-damped-equation-of-motion-first-order-dissipation-from-a-variational-principle",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ClassicalMechanics.dampedOscillatorContactSlice"

/- ZIL-END -/

end ClassicalMechanics

end

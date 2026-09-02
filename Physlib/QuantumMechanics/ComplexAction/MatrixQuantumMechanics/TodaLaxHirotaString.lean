/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Data.Complex.Basic

/-!
# Toda hierarchy: Lax shift algebra, string equation, dispersionless limit, Hirota ⟺ Toda (Alexandrov §II.5)

The Toda lattice hierarchy is the integrable structure underlying the matrix models of 2D string theory
(Alexandrov, hep-th/0311273, Ch. II §5). Its Lax operators `L, L̄` are dressings of the lattice shift
`ω̂ = e^{ℏ∂_s}` (Eq. II.86), and the whole hierarchy is governed by the deformed Heisenberg relation
`[ω̂, s] = ℏ ω̂` (Eq. II.97), whose classical (dispersionless) shadow is the Poisson bracket `{ω, s} = ω`
(Eq. II.139). The shift `s ↦ s + ℏ` with spacing `ℏ` is the discrete / lattice structure of the matrix-model
description of 2d string theory.

* **§A — the Lax shift algebra** (Eq. II.97). `shift ℏ` is `ω̂`, `mulVar` is multiplication by the lattice
  coordinate `s`. `shift_mulVar_commutator`: `[ω̂, s] = ℏ ω̂`; `shiftInv_mulVar_commutator`:
  `[ω̂⁻¹, s] = −ℏ ω̂⁻¹`.
* **§B — the string equation** (Eqs. II.137–II.138, II.153–II.154). `shift_mulShiftInv_commutator`:
  `[ω̂, s ω̂⁻¹] = ℏ`, the popular form `[L, L̄] = ℏ` (Eq. II.154). `stringConsistency`:
  `[s ω̂⁻¹, s] = −ℏ · s ω̂⁻¹`, the consistency condition (Eq. II.138) for the string-equation functions
  `f = s ω̂⁻¹`, `g = s` (Eq. II.153).
* **§C — the dispersionless limit** (Eq. II.139). `poisson_omega_s`: with `ω = e^p` on the `(s,p)` phase
  space, `{ω, s} = ω` — the `ℏ → 0` classical shadow of `[ω̂, s] = ℏ ω̂`.
* **§D — Hirota ⟺ Toda** (Eqs. II.135–II.136). `mixed_log_second_deriv`: the chain-rule identity
  `∂₁∂₋₁ log τ = (τ·∂₁∂₋₁τ − ∂₁τ·∂₋₁τ)/τ²`; `hirota_iff_toda`: via that identity the bilinear Hirota
  equation `ℏ²(τ ∂₁∂₋₁τ − ∂₁τ ∂₋₁τ) + τ_{l+1}τ_{l-1} = 0` is equivalent to the Toda equation
  `ℏ² ∂₁∂₋₁ log τ + τ_{l+1}τ_{l-1}/τ² = 0`.

## References

* S. Yu. Alexandrov, *Matrix Quantum Mechanics and Two-dimensional String Theory in Non-trivial
  Backgrounds*, hep-th/0311273, Ch. II §5, Eqs. (II.86), (II.97), (II.135)–(II.139), (II.153)–(II.154).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.TodaLaxHirotaString


/-- **The lattice shift operator** `ω̂ = e^{ℏ∂_s}` acting on functions of the lattice coordinate `s`:
`(ω̂ f)(s) = f(s + ℏ)` (Eq. II.86, II.97). `ℏ` is the spacing. -/
def shift (ℏ : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := fun s => f (s + ℏ)

/-- **Multiplication by the lattice coordinate** `s`: `(s · f)(s) = s f(s)`. -/
def mulVar (f : ℂ → ℂ) : ℂ → ℂ := fun s => s * f s

/-- **[The deformed Heisenberg relation, Eq. II.97]** `[ω̂, s] = ℏ ω̂`: the shift and the coordinate fail to
commute by exactly the spacing `ℏ` times the shift — the algebraic heart of the Toda/Orlov–Shulman
structure. -/
lemma shift_mulVar_commutator (ℏ : ℂ) (f : ℂ → ℂ) :
    shift ℏ (mulVar f) - mulVar (shift ℏ f) = ℏ • shift ℏ f := by
  funext s
  simp only [shift, mulVar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **[`[ω̂⁻¹, s] = −ℏ ω̂⁻¹`]** — the inverse-shift companion of Eq. II.97 (`ω̂⁻¹ = e^{−ℏ∂_s}`). -/
lemma shiftInv_mulVar_commutator (ℏ : ℂ) (f : ℂ → ℂ) :
    shift (-ℏ) (mulVar f) - mulVar (shift (-ℏ) f) = (-ℏ) • shift (-ℏ) f := by
  funext s
  simp only [shift, mulVar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring


/-- **[The string equation, Eq. II.154]** `[ω̂, s ω̂⁻¹] = ℏ`. With the leading Lax operators `L ~ ω̂` and
`L̄ ~ s ω̂⁻¹`, the canonical commutator `[L, L̄] = ℏ` — the most popular form of the Toda string equation —
follows from `[ω̂, s] = ℏ ω̂`. -/
lemma shift_mulShiftInv_commutator (ℏ : ℂ) (f : ℂ → ℂ) :
    shift ℏ (mulVar (shift (-ℏ) f)) - mulVar (shift (-ℏ) (shift ℏ f)) = ℏ • f := by
  funext s
  simp only [shift, mulVar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show s + ℏ + -ℏ = s from by ring, show s + -ℏ + ℏ = s from by ring]
  ring

/-- **[The string-equation consistency condition, Eq. II.138]** `[s ω̂⁻¹, s] = −ℏ · (s ω̂⁻¹)`. For the
string-equation functions `f = s ω̂⁻¹`, `g = s` (Eq. II.153) the bracket `[f, g] = −ℏ f` holds — the
condition that preserves the Toda structure. -/
lemma stringConsistency (ℏ : ℂ) (f : ℂ → ℂ) :
    mulVar (shift (-ℏ) (mulVar f)) - mulVar (mulVar (shift (-ℏ) f))
      = (-ℏ) • mulVar (shift (-ℏ) f) := by
  funext s
  simp only [shift, mulVar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring


/-- **The canonical Poisson bracket** on the `(s, p)` phase space, `{F, G} = ∂_p F ∂_s G − ∂_s F ∂_p G`
(the sign convention under which the dispersionless `ω = e^p` obeys `{ω, s} = ω`). -/
noncomputable def poisson (F G : ℝ → ℝ → ℝ) (s p : ℝ) : ℝ :=
  deriv (fun p => F s p) p * deriv (fun s => G s p) s
    - deriv (fun s => F s p) s * deriv (fun p => G s p) p

/-- **[The dispersionless Toda relation, Eq. II.139]** `{ω, s} = ω` with `ω = e^p`. This is the classical
(`ℏ → 0`) shadow of the deformed Heisenberg relation `[ω̂, s] = ℏ ω̂` (Eq. II.97): under `[·,·] → ℏ{·,·}` the
shift symbol `ω = e^p` and the coordinate `s` realize the same algebra. -/
lemma poisson_omega_s (s p : ℝ) :
    poisson (fun _ q => Real.exp q) (fun r _ => r) s p = Real.exp p := by
  have he : deriv (fun q : ℝ => Real.exp q) p = Real.exp p := by
    simp [(Real.hasDerivAt_exp p).deriv]
  have hi : deriv (fun x : ℝ => x) s = 1 := by simp
  simp only [poisson, he, hi, deriv_const', mul_zero, sub_zero, mul_one]


/-- **[The mixed second log-derivative, chain rule]** `∂₁∂₋₁ log τ = (τ·∂₁∂₋₁τ − ∂₁τ·∂₋₁τ)/τ²`. This is the
identity that turns the bilinear Hirota equation (Eq. II.135) into the Toda equation (Eq. II.136). -/
lemma mixed_log_second_deriv (τ : ℝ → ℝ → ℝ) (a b : ℝ)
    (hy : ∀ x, DifferentiableAt ℝ (fun y => τ x y) b)
    (hpos : ∀ x, 0 < τ x b)
    (hD2 : DifferentiableAt ℝ (fun x => deriv (fun y => τ x y) b) a)
    (hT : DifferentiableAt ℝ (fun x => τ x b) a) :
    deriv (fun x => deriv (fun y => Real.log (τ x y)) b) a
      = (deriv (fun x => deriv (fun y => τ x y) b) a * τ a b
          - deriv (fun y => τ a y) b * deriv (fun x => τ x b) a) / (τ a b) ^ 2 := by
  have inner : ∀ x, deriv (fun y => Real.log (τ x y)) b = deriv (fun y => τ x y) b / τ x b := by
    intro x
    have h : HasDerivAt (fun y => Real.log (τ x y))
        ((τ x b)⁻¹ * deriv (fun y => τ x y) b) b :=
      (Real.hasDerivAt_log (hpos x).ne').comp b (hy x).hasDerivAt
    rw [h.deriv, inv_mul_eq_div]
  rw [show (fun x => deriv (fun y => Real.log (τ x y)) b)
        = (fun x => deriv (fun y => τ x y) b) / (fun x => τ x b) from by
        funext x; rw [Pi.div_apply]; exact inner x,
    deriv_div hD2 hT (hpos a).ne']

/-- **[Hirota ⟺ Toda, Eqs. II.135–II.136]** Given the mixed log-derivative `Lmix = ∂₁∂₋₁ log τ`
(`= (τ·∂₁∂₋₁τ − ∂₁τ·∂₋₁τ)/τ²` by `mixed_log_second_deriv`) and `τ ≠ 0`, the **bilinear Hirota equation**
`ℏ²(τ·∂₁∂₋₁τ − ∂₁τ·∂₋₁τ) + τ_{l+1}τ_{l-1} = 0` (Eq. II.135) is equivalent to the **Toda equation**
`ℏ²·∂₁∂₋₁ log τ + τ_{l+1}τ_{l-1}/τ² = 0` (Eq. II.136). -/
lemma hirota_iff_toda (ℏ τ τp τm d1 dm1 d1m1 Lmix : ℝ) (hτ : τ ≠ 0)
    (hchain : Lmix = (τ * d1m1 - d1 * dm1) / τ ^ 2) :
    ℏ ^ 2 * (τ * d1m1 - d1 * dm1) + τp * τm = 0
      ↔ ℏ ^ 2 * Lmix + τp * τm / τ ^ 2 = 0 := by
  subst hchain
  rw [show ℏ ^ 2 * ((τ * d1m1 - d1 * dm1) / τ ^ 2) + τp * τm / τ ^ 2
      = (ℏ ^ 2 * (τ * d1m1 - d1 * dm1) + τp * τm) / τ ^ 2 from by ring,
    div_eq_zero_iff]
  simp [pow_ne_zero 2 hτ]

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.TodaLaxHirotaString

end

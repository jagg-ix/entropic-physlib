/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
meta import Zil

/-!
# Asymptotic freedom from the one-loop β-function coefficient

For an `SU(N)` gauge theory with `nf` Dirac fermion flavours, the one-loop renormalization-group β-function
is `μ dg/dμ = β(g) = −(b₀/16π²) g³` with the coefficient (Gross–Wilczek, Politzer 1973)

`b₀ = (11 N − 2 nf)/3`.

**Asymptotic freedom is exactly the statement `b₀ > 0`**: then `β(g) < 0` for `g > 0`, so the coupling
*decreases* as the energy scale `μ` increases.  For QCD (`N = 3`) this holds iff `nf < 33/2`, i.e. up to
`16` flavours — comfortably above the `6` observed.

* `betaZeroOneLoop`, `betaFunctionOneLoop` — the coefficient and the one-loop β-function.
* `betaZeroOneLoop_pos_iff` — `b₀ > 0 ↔ 2 nf < 11 N`.
* `qcd_asymptotically_free` — `nf < 33/2 → b₀(3, nf) > 0`.
* `betaFunction_neg_of_asymptoticFreedom` — `b₀ > 0 ∧ g > 0 → β(g) < 0` (the coupling runs to zero at high
  energy).

Honest scope: the *sign* of the known one-loop coefficient and its consequence for the running (the content
of asymptotic freedom); the loop integral that produces `b₀ = (11N − 2nf)/3` is an input here, not computed,
and the two-and-higher-loop structure is not treated.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop

open Real

/-- **The one-loop β-function coefficient** `b₀ = (11 N − 2 nf)/3` for `SU(N)` with `nf` Dirac flavours. -/
def betaZeroOneLoop (N nf : ℝ) : ℝ := (11 * N - 2 * nf) / 3

/-- **The one-loop β-function** `β(g) = −(b₀/16π²) g³` (`μ dg/dμ = β(g)`). -/
def betaFunctionOneLoop (N nf g : ℝ) : ℝ := -(betaZeroOneLoop N nf) / (16 * π ^ 2) * g ^ 3

/-- **Asymptotic freedom ⇔ positive one-loop coefficient** `b₀ > 0 ↔ 2 nf < 11 N`. -/
@[zil_level physical_theorem]
theorem betaZeroOneLoop_pos_iff (N nf : ℝ) : 0 < betaZeroOneLoop N nf ↔ 2 * nf < 11 * N := by
  unfold betaZeroOneLoop
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro h <;> linarith

/-- **QCD is asymptotically free up to `16` flavours** — for `SU(3)`, `b₀ > 0` whenever `nf < 33/2`. -/
@[zil_level physical_theorem]
theorem qcd_asymptotically_free (nf : ℝ) (h : nf < 33 / 2) : 0 < betaZeroOneLoop 3 nf := by
  rw [betaZeroOneLoop_pos_iff]
  linarith

/-- **A positive coefficient drives the coupling to zero at high energy** — if `b₀ > 0` and `g > 0` then the
one-loop β-function is negative, so `g` decreases as the scale increases (asymptotic freedom). -/
@[zil_level physical_theorem]
theorem betaFunction_neg_of_asymptoticFreedom (N nf g : ℝ)
    (hβ : 0 < betaZeroOneLoop N nf) (hg : 0 < g) : betaFunctionOneLoop N nf g < 0 := by
  unfold betaFunctionOneLoop
  have hπ : 0 < 16 * π ^ 2 := by positivity
  have hg3 : 0 < g ^ 3 := by positivity
  apply mul_neg_of_neg_of_pos _ hg3
  rw [div_neg_iff]
  exact Or.inr ⟨by linarith, hπ⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop

zil attach betaZeroOneLoop_pos_iff where
  formalizes @ "claim:the-one-loop-yang-mills-beta-function-coefficient-eleven-n-minus-two-n-f-over-three-is-positive-if-and-only-if-twice-the-flavour-number-is-less-than-eleven-times-the-number-of-colours"

zil attach qcd_asymptotically_free where
  supported_by @ "lean:betaZeroOneLoop_pos_iff",
  formalizes @ "claim:qcd-with-su-three-colour-is-asymptotically-free-the-one-loop-beta-function-coefficient-is-positive-whenever-the-number-of-fermion-flavours-is-below-thirty-three-halves"

zil attach betaFunction_neg_of_asymptoticFreedom where
  formalizes @ "claim:a-positive-one-loop-beta-function-coefficient-makes-the-beta-function-negative-for-positive-coupling-so-the-running-coupling-decreases-as-the-energy-scale-increases-asymptotic-freedom"

zil_file_contract physlib.asymptoticFreedomOneLoop where
  promises "Asymptotic freedom from the one-loop beta-function coefficient. For an SU(N) gauge theory with nf Dirac flavours the one-loop renormalization-group beta-function is scale times dg by dscale equals minus b-zero over sixteen pi squared times g cubed, with the Gross-Wilczek-Politzer coefficient b-zero equal to eleven N minus two nf all over three. Asymptotic freedom is exactly the positivity of this coefficient: the coefficient is positive if and only if twice the flavour number is less than eleven times the number of colours; for SU(3) this holds whenever the flavour number is below thirty-three halves, up to sixteen flavours. A positive coefficient makes the beta-function negative for positive coupling, so the running coupling decreases as the energy scale increases. Honest scope: the sign of the known one-loop coefficient and its consequence for the running, the content of asymptotic freedom; the loop integral that produces the coefficient is an input here, not computed, and the higher-loop structure is not treated."
  at_level physical_theorem
  contract_status satisfied
  requires_objects []
  forbids_substitutes [
    "reading the sign analysis of the known one-loop coefficient as a computation of the coefficient from the loop integral, or as a treatment of the higher-loop beta-function"
  ]
  witnessed_by [
    betaZeroOneLoop_pos_iff,
    qcd_asymptotically_free,
    betaFunction_neg_of_asymptoticFreedom
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.asymptoticFreedomOneLoop

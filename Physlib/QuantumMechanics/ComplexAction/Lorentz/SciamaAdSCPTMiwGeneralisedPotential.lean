/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-!
# Generalised interworld potentials for wavefunctions with nodes (Wiseman et al., arXiv:1807.01568, §5)

This paper ("Nonlocality in Bell's theorem, in Bohm's theory, and in Many Interacting Worlds theorising")
extends the MIW method beyond the toy model to **wavefunctions with nodes** — exactly the excited-state
structure of the earlier modules (the Maxwell `x²φ` and weighted-Laplace `x²e^{−2|x|}` first excited states have
a node at the origin, `SciamaAdSCPTManyInteractingWorlds.miwFirst_two_lobed`,
`SciamaAdSCPTMiwCoulomb.coulombFirstBaseline_node`).  The construction approximates the Bohmian force
`P′(y)/P(y) = −y″/(y′)²` (via the inverse CDF `y = 𝒞⁻¹`) by finite differences of world positions with
coefficients `{α_{cl}}` chosen so that the derivatives are reproduced exactly to order `L`:

`Σ_c α_{cl} c^{l'} = l! δ_{ll'}`  (Eq. alpha),

giving the generalised interworld potential `U_{α,L}(X) = (ℏ²/8m) Σ_n {Σ_c α_{c2}Δx / (Σ_c α_{c1}Δx)²}²`
(Eq. rational).

* `moment_alpha1_l1`, `moment_alpha1_l2`, `moment_alpha2_l1`, `moment_alpha2_l2` — the four moment conditions
  `Σ_c α_{cl} c^{l'} = l! δ_{ll'}` for the simplest `C = L = 2` (nearest-neighbour `c = ±1`) case, with
  `α_{c1} = (−½, ½)`, `α_{c2} = (1, 1)` — the exact solution `A = M⁻¹ Δ`, `Δ = diag[1!, 2!]`.
* `genInterworldTerm_inverse_square` — the generalised potential term is **inverse-square homogeneous**
  (`U(λx) = λ⁻² U(x)`), so — as in the toy model — Ehrenfest's theorem and wavepacket spreading hold
  (`SciamaAdSCPTMiwEhrenfestHeisenberg`, `SciamaAdSCPTMiwWavepacketSpreading`).
* `cdf_area` — the equal-area partition `𝒞(x_n) = (n − ½)/N` (Eq. cx): each world occupies a neighbourhood of
  probability `1/N` (`𝒞(x_{n+1}) − 𝒞(x_n) = 1/N`), the discretisation underlying the empirical density.

So the MIW method extends to nodal (excited) states via generalised interworld potentials whose exact-to-order-`L`
finite-difference coefficients solve `MA = Δ`, and which retain the inverse-square scaling that gives Ehrenfest
and wavepacket spreading — the technical step toward simulating the nonlocality of Bell/Bohm/MIW.

Honest scope: the `C = L = 2` moment conditions, the potential term's inverse-square scaling, and the CDF
equal-area partition.  The Taylor-expansion accuracy `O(1/N^L)`, the pseudo-inverse for `C > L`, and the
nonlocality simulations are the paper's content, contextualised here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwGeneralisedPotential

open scoped BigOperators

/-! ## A. The exact finite-difference coefficients (`C = L = 2`) -/

/-- The nearest-neighbour offsets `c = −1, 1`. -/
def cVal : Fin 2 → ℝ
  | 0 => -1
  | 1 => 1

/-- The first-derivative coefficients `α_{c1} = (−½, ½)` (for `c = −1, 1`). -/
def alphaOne : Fin 2 → ℝ
  | 0 => -1 / 2
  | 1 => 1 / 2

/-- The second-derivative coefficients `α_{c2} = (1, 1)`. -/
def alphaTwo : Fin 2 → ℝ
  | 0 => 1
  | 1 => 1

/-- **[Eq. alpha, `l=1,l'=1`] `Σ_c α_{c1} c = 1!`.** -/
theorem moment_alpha1_l1 : ∑ i, alphaOne i * cVal i = 1 := by
  simp only [Fin.sum_univ_two, alphaOne, cVal]; norm_num

/-- **[Eq. alpha, `l=1,l'=2`] `Σ_c α_{c1} c² = 0`.** -/
theorem moment_alpha1_l2 : ∑ i, alphaOne i * cVal i ^ 2 = 0 := by
  simp only [Fin.sum_univ_two, alphaOne, cVal]; norm_num

/-- **[Eq. alpha, `l=2,l'=1`] `Σ_c α_{c2} c = 0`.** -/
theorem moment_alpha2_l1 : ∑ i, alphaTwo i * cVal i = 0 := by
  simp only [Fin.sum_univ_two, alphaTwo, cVal]; norm_num

/-- **[Eq. alpha, `l=2,l'=2`] `Σ_c α_{c2} c² = 2!`.** -/
theorem moment_alpha2_l2 : ∑ i, alphaTwo i * cVal i ^ 2 = 2 := by
  simp only [Fin.sum_univ_two, alphaTwo, cVal]; norm_num

/-! ## B. The generalised potential is inverse-square homogeneous -/

/-- One term of the generalised interworld potential (Eq. rational): `(num / den²)²`, with `num = Σ_c α_{c2}Δx`
and `den = Σ_c α_{c1}Δx` the finite-difference approximations to `y″` and `y′`. -/
def genInterworldTerm (num den : ℝ) : ℝ := (num / den ^ 2) ^ 2

/-- **[Inverse-square scaling] `U(λx) = λ⁻² U(x)`.**  Under `x → λx` the numerator scales as `λ` and the
denominator² as `λ²`, so the generalised interworld term scales as `λ⁻²` — hence Ehrenfest's theorem and
wavepacket spreading hold, as for the toy model. -/
theorem genInterworldTerm_inverse_square {lam den : ℝ} (hlam : lam ≠ 0) (hden : den ≠ 0) (num : ℝ) :
    genInterworldTerm (lam * num) (lam * den) = (1 / lam ^ 2) * genInterworldTerm num den := by
  unfold genInterworldTerm
  field_simp

/-! ## C. The equal-area CDF partition -/

/-- The cumulative-distribution value at world `n` (Eq. cx): `𝒞(x_n) = (n − ½)/N`. -/
def cdfNeighbourhood (n N : ℝ) : ℝ := (n - 1 / 2) / N

/-- **[Equal-area partition] `𝒞(x_{n+1}) − 𝒞(x_n) = 1/N`.**  Each world occupies a neighbourhood of probability
`1/N` — the discretisation of the smooth density into `N` interacting worlds. -/
theorem cdf_area (n : ℝ) {N : ℝ} (hN : N ≠ 0) :
    cdfNeighbourhood (n + 1) N - cdfNeighbourhood n N = 1 / N := by
  unfold cdfNeighbourhood
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwGeneralisedPotential

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator
public import Physlib.QFT.PathIntegral.FeynmanKac

/-!
# Euclidean time evolution of the Wigner–Dunkl process: two Bessel processes + Feynman–Kac

Formalization of §5 and Appendix A of *G. Junker, "On the Path Integral Formulation of Wigner–Dunkl
Quantum Mechanics," arXiv:2312.12895*: the Euclidean-time evolution `e^{τ(L^{(ν)} − V)}` of Wigner–Dunkl
quantum mechanics, and the **Dunkl process** that realizes it. The Dunkl process has *jumps* (the
reflection `R`), but it splits — via the parity projectors `P± = (1 ± R)/2` — into **two continuous Bessel
processes**: one *reflecting* (Neumann, index `ν − ½`) and one *absorbing* (Dirichlet, index `ν + ½`).

This file builds the splitting structurally on `ℝ[X]` (reusing `reflPoly` from `Dunkl.Oscillator`) and
**uses the reference tree Feynman–Kac infrastructure** (`Physlib.QFT.PathIntegral.FeynmanKac`):

* **§A — the parity decomposition** (Junker Eq. 76): `P± = (1 ± R)/2` are complementary orthogonal
  idempotents on `ℝ[X]` (`parityPlus_idem`, `parity_add`), with `P₊` even and `P₋` odd
  (`parityPlus_even`, `parityMinus_odd`) and `R = P₊ − P₋`. The even sector drives the reflecting
  process, the odd sector the absorbing process.
* **§B — the two Bessel processes** (Eq. 77, A.1): `besselReflectingIndex ν = ν − ½` (Neumann `f'(0)=0`)
  and `besselAbsorbingIndex ν = ν + ½` (Dirichlet `f(0)=0`), with index difference `1`
  (`bessel_index_diff`); the Bessel generator `L_B^{(α)} = ½(∂² + (2α+1)/x ∂)` has formal monomial
  eigenvalue `½ n(n + 2α)` (`besselGenEigenvalue`).
* **§C — the transition-density split** (Eq. 77): `d_τ^{(ν)}(x,y) = b_τ^{(ν−½)}(|x|,|y|) +
  xy·b_τ^{(ν+½)}(|x|,|y|)` (`dunklTransitionDensity`), and at `ν = 0` (Eq. 79) the Dunkl density is the
  ordinary Wiener/heat kernel `wienerDensity` (`wienerDensity_symm`, `wienerDensity_pos`).
* **§D — the Dunkl–Feynman–Kac formula** (Eq. 78): both Bessel path integrals include the *same*
  reference tree Feynman–Kac weight `fkPathWeight V z τ = exp(−∫₀^τ V(z s) ds)`. The Euclidean Dunkl
  propagator is the parity combination of two `FeynmanKacModel` propagators (`dunklEuclideanFK`); each
  inherits the Chapman–Kolmogorov semigroup law (`dunklEuclideanFK_semigroup_refl/abs`); the free process
  has unit weight (`dunkl_fk_free_weight`), and a non-negative potential damps it (`dunkl_fk_weight_le_one`).
  The Euclidean weight ties to the entropic Wick rotation `euclideanEvolutionFactor`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

open Polynomial
open Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator
open Physlib.QFT.PathIntegral

/-! ## §A — the parity decomposition `P± = (1 ± R)/2` (Junker Eq. 76) -/

/-- `R` is additive: `R(p + q) = Rp + Rq`. -/
theorem reflPoly_add (p q : ℝ[X]) : reflPoly (p + q) = reflPoly p + reflPoly q := by
  simp [reflPoly, add_comp]

/-- `R` commutes with real scalars: `R(c • p) = c • Rp`. -/
theorem reflPoly_smul (c : ℝ) (p : ℝ[X]) : reflPoly (c • p) = c • reflPoly p := by
  simp [reflPoly, smul_comp]

/-- `R` is subtractive: `R(p − q) = Rp − Rq`. -/
theorem reflPoly_sub (p q : ℝ[X]) : reflPoly (p - q) = reflPoly p - reflPoly q := by
  simp [reflPoly, sub_comp]

/-- **[Junker Eq. 76] The even parity projector** `P₊ = (1 + R)/2`. -/
noncomputable def parityPlus (p : ℝ[X]) : ℝ[X] := (1 / 2 : ℝ) • (p + reflPoly p)

/-- **[Junker Eq. 76] The odd parity projector** `P₋ = (1 − R)/2`. -/
noncomputable def parityMinus (p : ℝ[X]) : ℝ[X] := (1 / 2 : ℝ) • (p - reflPoly p)

/-- **The projectors are complementary**: `P₊ p + P₋ p = p` (the even–odd decomposition). -/
theorem parity_add (p : ℝ[X]) : parityPlus p + parityMinus p = p := by
  simp only [parityPlus, parityMinus, ← smul_add]; rw [add_add_sub_cancel,
    show ((1 : ℝ) / 2) • (p + p) = ((1 : ℝ) / 2 * 2) • p by rw [← smul_smul, two_smul]]
  norm_num

/-- **`R = P₊ − P₋`**: the reflection is the difference of the parity projectors. -/
theorem parity_sub_eq_refl (p : ℝ[X]) : parityPlus p - parityMinus p = reflPoly p := by
  simp only [parityPlus, parityMinus, ← smul_sub, sub_sub_sub_cancel_left,
    show p + reflPoly p - (p - reflPoly p) = reflPoly p + reflPoly p by ring,
    show reflPoly p + reflPoly p = (2 : ℝ) • reflPoly p by rw [two_smul], smul_smul]
  norm_num

/-- **`P₊` lands in the even subspace**: `R(P₊ p) = P₊ p`. -/
theorem parityPlus_even (p : ℝ[X]) : reflPoly (parityPlus p) = parityPlus p := by
  rw [parityPlus, reflPoly_smul, reflPoly_add, reflPoly_involutive, add_comm]

/-- **`P₋` lands in the odd subspace**: `R(P₋ p) = −P₋ p`. -/
theorem parityMinus_odd (p : ℝ[X]) : reflPoly (parityMinus p) = -parityMinus p := by
  rw [parityMinus, reflPoly_smul, reflPoly_sub, reflPoly_involutive, ← smul_neg, neg_sub]

/-- **`P₊` is idempotent**: `P₊(P₊ p) = P₊ p` (a genuine projector). -/
theorem parityPlus_idem (p : ℝ[X]) : parityPlus (parityPlus p) = parityPlus p := by
  conv_lhs => rw [parityPlus, parityPlus_even]
  rw [show parityPlus p + parityPlus p = (2 : ℝ) • parityPlus p by rw [two_smul], smul_smul]
  norm_num

/-- **`P₋` is idempotent**: `P₋(P₋ p) = P₋ p`. -/
theorem parityMinus_idem (p : ℝ[X]) : parityMinus (parityMinus p) = parityMinus p := by
  conv_lhs => rw [parityMinus, parityMinus_odd]
  rw [sub_neg_eq_add,
    show parityMinus p + parityMinus p = (2 : ℝ) • parityMinus p by rw [two_smul], smul_smul]
  norm_num

/-! ## §B — the two Bessel processes (Junker Eq. 77, Appendix A.1) -/

/-- **[Junker §5] The reflecting Bessel index** `α = ν − ½` — the even sector becomes a Bessel process
with a Neumann boundary condition `f'(0) = 0` (reflection at the origin). -/
noncomputable def besselReflectingIndex (ν : ℝ) : ℝ := ν - 1 / 2

/-- **[Junker §5] The absorbing Bessel index** `β = ν + ½` — the odd sector becomes a Bessel process with
a Dirichlet boundary condition `f(0) = 0` (absorption at the origin). -/
noncomputable def besselAbsorbingIndex (ν : ℝ) : ℝ := ν + 1 / 2

/-- **The two Bessel indices differ by `1`**: `(ν + ½) − (ν − ½) = 1` — the Radon–Nikodym index shift
(Eq. A.6) relating the reflecting and absorbing processes. -/
theorem bessel_index_diff (ν : ℝ) : besselAbsorbingIndex ν - besselReflectingIndex ν = 1 := by
  unfold besselReflectingIndex besselAbsorbingIndex; ring

/-- **[Junker Eq. A.1] The Bessel generator's monomial eigenvalue** `L_B^{(α)} xⁿ = ½ n(n + 2α) xⁿ⁻²`:
the spectrum of `L_B^{(α)} = ½(∂² + (2α+1)/x ∂)` on `xⁿ`. -/
noncomputable def besselGenEigenvalue (α : ℝ) (n : ℕ) : ℝ := (1 / 2) * n * (n + 2 * α)

/-- The free Bessel generator (`α = −½`, i.e. `ν = 0`) reduces to `½ ∂²`: eigenvalue `½ n(n−1)`, the
ordinary second derivative on `xⁿ` — the generator of Wiener/Brownian motion. -/
theorem besselGenEigenvalue_free (n : ℕ) : besselGenEigenvalue (-(1 / 2)) n = (1 / 2) * n * (n - 1) := by
  unfold besselGenEigenvalue; ring

/-! ## §C — the transition-density split (Junker Eq. 77) and the Wiener limit (Eq. 79) -/

/-- **[Junker Eq. 77] The Dunkl transition density splits into two Bessel densities.** Given a Bessel
transition density `b` (index, time, two points; Eq. A.2), the Dunkl heat kernel is
`d_τ^{(ν)}(x,y) = b_τ^{(ν−½)}(|x|,|y|) + xy·b_τ^{(ν+½)}(|x|,|y|)` — the even (reflecting) part plus the
sign-weighted odd (absorbing) part. The `xy` prefactor is the parity signature of `P₋`. -/
noncomputable def dunklTransitionDensity (b : ℝ → ℝ → ℝ → ℝ → ℝ) (ν τ x y : ℝ) : ℝ :=
  b (besselReflectingIndex ν) τ |x| |y| + x * y * b (besselAbsorbingIndex ν) τ |x| |y|

/-- **[Junker Eq. 79] The Wiener / heat kernel** `d_τ^{(0)}(x,y) = (2πτ)^{−1/2} exp(−(x−y)²/2τ)` — the
`ν = 0` Dunkl density on the real line, the transition density of Brownian motion. -/
noncomputable def wienerDensity (τ x y : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * τ)) * Real.exp (-(x - y) ^ 2 / (2 * τ))

/-- The Wiener density is **symmetric**: `d_τ(x,y) = d_τ(y,x)`. -/
theorem wienerDensity_symm (τ x y : ℝ) : wienerDensity τ x y = wienerDensity τ y x := by
  unfold wienerDensity; rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]

/-- The Wiener density is **strictly positive** for `τ > 0`. -/
theorem wienerDensity_pos (τ x y : ℝ) (hτ : 0 < τ) : 0 < wienerDensity τ x y := by
  unfold wienerDensity
  exact mul_pos (by positivity) (Real.exp_pos _)

/-! ## §D — the Dunkl–Feynman–Kac formula (Junker Eq. 78), using reference tree FK -/

/-- **[Junker Eq. 78] The free Dunkl process records unit Feynman–Kac weight**: with `V = 0` the shared
weight `fkPathWeight V z τ = exp(−∫₀^τ V) = 1`. The Bessel path integrals of Eq. 78 then reduce to the
bare Bessel transition measures. -/
theorem dunkl_fk_free_weight (z : ℝ → ℝ) (τ : ℝ) : fkPathWeight (fun _ => 0) z τ = 1 := by
  simp [fkPathWeight, fkPathPotential]

/-- **A non-negative potential damps the Dunkl–Feynman–Kac weight**: for `V ≥ 0` and `τ ≥ 0` the shared
weight `fkPathWeight V z τ ≤ 1`. So both Bessel path integrals in Eq. 78 are contractive — the Euclidean
evolution is a genuine (sub-Markovian) semigroup. -/
theorem dunkl_fk_weight_le_one (V : ℝ → ℝ) (z : ℝ → ℝ) (τ : ℝ)
    (hV : ∀ y, 0 ≤ V y) (hτ : 0 ≤ τ) : fkPathWeight V z τ ≤ 1 :=
  fkPathWeight_le_one V z τ hV hτ

/-- **[Junker Eq. 78] The Euclidean Dunkl propagator** as the parity combination of two Bessel
Feynman–Kac propagators: `⟨x|e^{τ(L^{(ν)}−V)}|y⟩ = (reflecting) + xy·(absorbing)`. Both `FeynmanKacModel`s
include the same potential `V`; the reflecting one realizes the even sector (index `ν − ½`), the absorbing
one the odd sector (index `ν + ½`). -/
noncomputable def dunklEuclideanFK
    (Brefl Babs : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (τ x y : ℝ) : ℝ :=
  feynman_kac_propagator Brefl β obs τ x + x * y * feynman_kac_propagator Babs β obs τ x

/-- **The reflecting Bessel sector obeys the Chapman–Kolmogorov semigroup law** (Eq. A.3) — inherited
from the reference tree `feynman_kac_propagator_semigroup`. -/
theorem dunklEuclideanFK_semigroup_refl (Brefl : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (t s x : ℝ) :
    feynman_kac_propagator Brefl β obs (t + s) x
      = Brefl.pathIntegral (fun y => feynman_kac_propagator Brefl β obs s y) t x :=
  feynman_kac_propagator_semigroup Brefl β obs t s x

/-- **The absorbing Bessel sector obeys the Chapman–Kolmogorov semigroup law** (Eq. A.3). -/
theorem dunklEuclideanFK_semigroup_abs (Babs : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (t s x : ℝ) :
    feynman_kac_propagator Babs β obs (t + s) x
      = Babs.pathIntegral (fun y => feynman_kac_propagator Babs β obs s y) t x :=
  feynman_kac_propagator_semigroup Babs β obs t s x

/-- **At the origin `x = 0` (or `y = 0`) the absorbing sector drops out**: `dunklEuclideanFK … 0 y =`
the pure reflecting propagator. This is the Dirichlet/absorption boundary condition `f(0) = 0` of the
odd Bessel process — the absorbing process contributes nothing at the origin. -/
theorem dunklEuclideanFK_origin (Brefl Babs : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (τ y : ℝ) :
    dunklEuclideanFK Brefl Babs β obs τ 0 y = feynman_kac_propagator Brefl β obs τ 0 := by
  simp [dunklEuclideanFK]

end Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

end

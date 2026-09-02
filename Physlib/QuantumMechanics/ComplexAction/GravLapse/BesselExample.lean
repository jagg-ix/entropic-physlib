/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ADMSectionII
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

/-!
# Banihashemi–Jacobson all 10 equations: the worked momentum–lapse–Bessel example, linked to the repo

Carries the **complete set of §II equations** of *Banihashemi–Jacobson, arXiv:2405.10307v3 (2025)* and
ties the gravitational lapse machinery to the rest of the repository (the complex-action/entropic-time master formula, the
Nagao–Nielsen momentum path integral, and the one-loop gravitational saddle). The worked example (Eqs. 6–10)
is the relativistic mass-shell `ℋ = p² − m²`; the completion of the momentum square (Eq. 8 → Eq. 9) and the
change of variable to Schläfli's Bessel integral (Eq. 9 → Eq. 10) are proved as exact algebraic identities.

### The ten equations and their Lean carriers

| Eq. | content | carrier |
|----|----|----|
| 1 | phase-space PI `∫𝒟p𝒟q e^{i∫(pq̇−H)}` | `GravLapse.ContourMaster.momenta_before_lapse` (= `PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle`) |
| 2 | constraint `δ(ℋ) = ∫(dN/2π) e^{−i∫Nℋ}` | `GravLapse.ContourMaster.lapseWeight_at_eps_zero` |
| 3 | `ℋ = q^{−1/2}(p^{ij}p_{ij} − ½p²) − q^{1/2}R` | `GravLapse.ADMSectionII.hamiltonianConstraint` |
| 4 | `{p,ℋ} = 2q^{1/2}(R − D²)δ` | consequence only: `GravLapse.ADMSectionII.momentumQuadratic_maximalSlice_nonneg` |
| 5 | `δ(ℋ) = lim ∫(dN/2π) e^{−i(N−iε)ℋ}` | `GravLapse.ContourMaster.lapseWeight` |
| 6 | `∫dⁿp e^{ip·x}δ(p²−m²) = ½mⁿ⁻²Ω_{n−2}∫du(1−u²)^{(n−3)/2}cos(m|x|u)` | `eq6CosIntegrand` (integrand) |
| 7 | `= mⁿ⁻²2^{n/2−1}π^{n/2} J_{n/2−1}(m|x|)/(m|x|)^{n/2−1}` | `schlafliBesselIntegrand` (Eq. 10 contour defines `J`) |
| 8 | `lim ∫dⁿp(dN/2π) e^{ip·x}e^{−i(N−iε)(p²−m²)}` | `GravLapse.ADMSectionII.eq8Integrand`, `eq8_complete_square` |
| 9 | `lim ∫(dN/2π)(π/(i(N−iε)))^{n/2} e^{ix²/4(N−iε)} e^{i(N−iε)m²}` | `eq9Integrand`, `eq8_complete_square` |
| 10 | `(−imⁿ⁻²π^{n/2}/2π)∫dt t^{−n/2} e^{t−z²/4t}` | `eq10Integrand`, `eq9_eq10_exponent` |

### Repository links

* **§A — the gravitational constraint feeds the master formula.** `gravLapseWeight` is the lapse weight of
  the actual Eq. 3 constraint; `gravLapseWeight_eq_master` shows it *is* `complexActionPathIntegralWeight` (hence
  `lorentzianKernel`, and the modulus is the entropic damping). The lapse contour of GR is the complex-action/entropic-time
  master complex-action path integral evaluated at `ℋ`.
* **§D — the momentum Gaussian is the Nagao–Nielsen Legendre transform.** The Eq. 8 → Eq. 9 completion of
  the momentum square (`eq8_complete_square`, saddle `eq8_saddle`) is the relativistic analog of
  `PathIntegral.MomentumPathIntegral.phaseLagrangian_complete_square` (saddle `p = mq̇`): both integrate the momenta by
  completing the square, the step the paper insists must precede the lapse.

**Honest scope.** The evaluation of Eq. 6 to the Bessel function `J_{n/2−1}` (Eq. 7) is the analytic content
(Poisson's integral, DLMF 10.9.4; Schläfli's contour integral DLMF 10.9.19 — which *defines* `J_ν` as the
Eq. 10 contour integral); Mathlib has no Bessel-`J` Poisson representation, so the special-function identity
`Eq. 6 = Eq. 7` is stated, not re-derived. The exact algebraic links in the chain (Eqs. 8 → 9 → 10) and the
master-formula links are fully proved.

## References

* B. Banihashemi, T. Jacobson, *On the lapse contour in the gravitational path integral*,
  arXiv:2405.10307v3 (2 Mar 2025), DOI `10.48550/arXiv.2405.10307`, §II (Eqs. 1–10, pp. 2–4).
* DLMF §10.9 (Poisson 10.9.4, Schläfli 10.9.19) — the Bessel integral representations (Eqs. 6, 7, 10).
* Repo carriers: `GravLapse.ADMSectionII`, `GravLapse.ContourMaster` (`lapseWeight`, `complexEnergy`),
  `PathIntegral.ComplexActionPathIntegralWeight` (`complexActionPathIntegralWeight`), `PathIntegral.MomentumPathIntegral` (`phaseLagrangian_complete_square`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.BesselExample

open Physlib.QuantumMechanics.ComplexAction.GravLapse.ADMSectionII
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.NonHermitian.WickRotation


/-- **[Link Eq. 3 → Eq. 5] The lapse weight of the gravitational Hamiltonian constraint.** Plugging the
Eq. 3 constraint `ℋ = hamiltonianConstraint q ppC pTr R` into the lapse-displaced weight (`lapseWeight`)
gives the per-`N` integrand of the gravitational path integral. -/
noncomputable def gravLapseWeight (q ppC pTr R N ε : ℝ) : ℂ :=
  lapseWeight N ε (hamiltonianConstraint q ppC pTr R)

/-- **[Link → master formula] The gravitational lapse weight IS the complex-action/entropic-time master integrand.**
`gravLapseWeight = complexActionPathIntegralWeight (−Nℋ) (εℋ) 1` (= `lorentzianKernel`): the gravitational lapse contour
is the master complex-action path integral evaluated at the Hamiltonian constraint `ℋ`. -/
lemma gravLapseWeight_eq_master (q ppC pTr R N ε : ℝ) :
    gravLapseWeight q ppC pTr R N ε
      = complexActionPathIntegralWeight (-(N * hamiltonianConstraint q ppC pTr R))
          (ε * hamiltonianConstraint q ppC pTr R) 1 :=
  lapseWeight_eq_master N ε (hamiltonianConstraint q ppC pTr R)

/-- **[Link] The gravitational lapse weight's modulus is the entropic damping at `ℋ`** —
`‖gravLapseWeight‖ = e^{−εℋ}`, the Halliwell–Hartle convergence factor evaluated on the Eq. 3 constraint. -/
lemma gravLapseWeight_modulus (q ppC pTr R N ε : ℝ) :
    ‖gravLapseWeight q ppC pTr R N ε‖ = Real.exp (-(ε * hamiltonianConstraint q ppC pTr R)) := by
  unfold gravLapseWeight
  rw [lapseWeight_modulus, kuikenWeight, div_one]


/-- **[Banihashemi–Jacobson Eq. 6] The Poisson cosine integrand** `(1 − u²)^{(n−3)/2} cos(m|x|u)` (over
`u ∈ [−1,1]`) obtained from hyperspherical polar coordinates for the momentum direction. -/
noncomputable def eq6CosIntegrand (n : ℕ) (m absx u : ℝ) : ℝ :=
  (1 - u ^ 2) ^ (((n : ℝ) - 3) / 2) * Real.cos (m * absx * u)

/-- **[Banihashemi–Jacobson Eq. 7 / Eq. 10; DLMF 10.9.19] Schläfli's Bessel integrand** `e^{t−z²/4t} t^{−ν−1}`,
whose contour integral `J_ν(z) = (1/2πi)∮ e^{t−z²/4t} t^{−ν−1} dt` *defines* the Bessel function `J_ν`. With
`ν = n/2 − 1` and `z = m|x|` this is the integrand of Eq. 10, and its evaluation is Eq. 7. -/
noncomputable def schlafliBesselIntegrand (ν t z : ℂ) : ℂ :=
  Complex.exp (t - z ^ 2 / (4 * t)) * t ^ (-ν - 1)

/-- **[Link Eq. 6 → source] The Eq. 6 cosine is the real part of the plane-wave source.**
`cos(m|x|u) = Re(e^{i·m|x|u})` — the on-shell (`ε → 0`) integrand is real because it is the real part of the
`e^{ip·x}` source factor of Eq. 8. -/
lemma eq6_cos_eq_re_planewave (m absx u : ℝ) :
    Real.cos (m * absx * u) = (Complex.exp (Complex.I * ((m * absx * u : ℝ) : ℂ))).re := by
  rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]

/-- **[Link] The Eq. 6 cosine integrand in terms of the complex plane-wave source.**
`eq6CosIntegrand = (1 − u²)^{(n−3)/2} · Re(e^{i·m|x|u})`, tying the real Poisson integrand to the same
complex exponential `Complex.exp` that builds `eq8Integrand`. -/
lemma eq6CosIntegrand_eq (n : ℕ) (m absx u : ℝ) :
    eq6CosIntegrand n m absx u
      = (1 - u ^ 2) ^ (((n : ℝ) - 3) / 2)
        * (Complex.exp (Complex.I * ((m * absx * u : ℝ) : ℂ))).re := by
  unfold eq6CosIntegrand
  rw [eq6_cos_eq_re_planewave]


/-- **[Banihashemi–Jacobson Eq. 8 → Eq. 9] Completion of the momentum square.** For the mass-shell weight,
the momentum exponent `−i(N−iε)p² + ip·x` (the `p²` part of Eq. 8) completes to
`−i(N−iε)(p − x/(2(N−iε)))² + ix²/(4(N−iε))` (writing `a = N − iε`). Doing the resulting Gaussian momentum
integral yields the `(π/(i a))^{n/2}` prefactor and the `e^{ix²/(4a)}` factor of Eq. 9. -/
lemma eq8_complete_square (a p x : ℂ) (ha : a ≠ 0) :
    -Complex.I * a * p ^ 2 + Complex.I * p * x
      = -Complex.I * a * (p - x / (2 * a)) ^ 2 + Complex.I * x ^ 2 / (4 * a) := by
  field_simp; ring

/-- **The momentum saddle of Eq. 8 is `p = x/(2(N−iε))`** — where the completed square vanishes (the
Gaussian peak), the relativistic analog of the Nagao–Nielsen momentum saddle `p = mq̇`
(`PathIntegral.MomentumPathIntegral.saddle_iff`). -/
lemma eq8_saddle (a x : ℂ) (ha : a ≠ 0) :
    -Complex.I * a * (x / (2 * a)) ^ 2 + Complex.I * (x / (2 * a)) * x
      = Complex.I * x ^ 2 / (4 * a) := by
  rw [eq8_complete_square a (x / (2 * a)) x ha]; simp

/-- **[Link Eq. 8 ↔ Nagao–Nielsen momentum PI] The Eq. 8 momentum exponent IS a phase-space Lagrangian.**
`−i(N−iε)p² + ip·x = phaseLagrangian (1/(2i(N−iε))) p (ix) 0` (`PathIntegral.MomentumPathIntegral.phaseLagrangian`): the
mass-shell momentum integral of Eq. 8 is the Nagao–Nielsen Feynman phase-space path integral, so the
completion of the square (`eq8_complete_square`) is `PathIntegral.MomentumPathIntegral.phaseLagrangian_complete_square`
specialized to the complex mass `1/(2i(N−iε))`. Integrating the momenta first (Eq. 1) is the same Gaussian. -/
lemma eq8_exponent_eq_phaseLagrangian (a p x : ℂ) (ha : a ≠ 0) :
    -Complex.I * a * p ^ 2 + Complex.I * p * x
      = PathIntegral.MomentumPathIntegral.phaseLagrangian (1 / (2 * Complex.I * a)) p (Complex.I * x) 0 := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  unfold PathIntegral.MomentumPathIntegral.phaseLagrangian
  field_simp
  ring

/-- **[Banihashemi–Jacobson Eq. 9] The momentum-integrated form** `(π/(i(N−iε)))^{n/2} e^{ix²/4(N−iε)}
e^{i(N−iε)m²}`, regular on the displaced contour (`ε > 0`, by `lapseContour_avoids_singularity`), singular
on the real axis at `N = 0` (`lapseContour_singular_at_origin`). -/
noncomputable def eq9Integrand (n : ℕ) (x N ε m : ℝ) : ℂ :=
  ((Real.pi : ℂ) / (Complex.I * complexEnergy N ε)) ^ ((n : ℂ) / 2)
    * Complex.exp (Complex.I * (x ^ 2 : ℝ) / (4 * complexEnergy N ε))
    * Complex.exp (Complex.I * complexEnergy N ε * (m ^ 2 : ℝ))

/-- **[Link Eq. 9 → Eq. 5] The Eq. 9 mass factor is a lapse weight.** The `e^{i(N−iε)m²}` factor of the
momentum-integrated form is `lapseWeight N ε (−m²)` — the lapse-displaced weight of the (negative) mass
shell. The whole worked example is built from `GravLapse.ContourMaster.lapseWeight`. -/
lemma eq9_massFactor_eq_lapseWeight (N ε m : ℝ) :
    Complex.exp (Complex.I * complexEnergy N ε * (m ^ 2 : ℝ)) = lapseWeight N ε (-(m ^ 2)) := by
  unfold lapseWeight complexEnergy
  congr 1
  push_cast
  ring


/-- **[Banihashemi–Jacobson Eq. 9 → Eq. 10] The change of variable** `t = i(N−iε)m²`, `z = m|x|` turns the
Eq. 9 exponent `ix²/(4(N−iε)) + i(N−iε)m²` into Schläfli's `t − z²/(4t)`. The identity uses `i² = −1`
(dividing by `i`). -/
lemma eq9_eq10_exponent (a x m : ℂ) (ha : a ≠ 0) (hm : m ≠ 0) :
    Complex.I * x ^ 2 / (4 * a) + Complex.I * a * m ^ 2
      = (Complex.I * a * m ^ 2) - (m * x) ^ 2 / (4 * (Complex.I * a * m ^ 2)) := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  linear_combination (x ^ 2) * Complex.I_sq

/-- The Eq. 9 → Eq. 10 change of variable on the displaced lapse contour `a = N − iε`, `ε > 0`. -/
lemma eq9_eq10_exponent_lapse (N ε : ℝ) (x m : ℂ) (hε : 0 < ε) (hm : m ≠ 0) :
    Complex.I * x ^ 2 / (4 * complexEnergy N ε) + Complex.I * complexEnergy N ε * m ^ 2
      = (Complex.I * complexEnergy N ε * m ^ 2)
        - (m * x) ^ 2 / (4 * (Complex.I * complexEnergy N ε * m ^ 2)) :=
  eq9_eq10_exponent _ x m (lapseContour_avoids_singularity N ε hε) hm

/-- **[Link Eq. 9 → Eq. 10] The Eq. 9 integrand is the prefactor times Schläfli's exponential.** Folding the
two exponentials (`Complex.exp_add`) and applying the change of variable `eq9_eq10_exponent_lapse`, the Eq. 9
integrand is `(π/(i(N−iε)))^{n/2}·e^{t−z²/4t}` with `t = i(N−iε)m²`, `z = m|x|` — exactly the prefactor times
the Schläfli/Eq. 10 exponential (`eq10Integrand`, `schlafliBesselIntegrand`). -/
lemma eq9Integrand_schlafli (n : ℕ) (x N ε m : ℝ) (hε : 0 < ε) (hm : m ≠ 0) :
    eq9Integrand n x N ε m
      = ((Real.pi : ℂ) / (Complex.I * complexEnergy N ε)) ^ ((n : ℂ) / 2)
        * Complex.exp (Complex.I * complexEnergy N ε * (m : ℂ) ^ 2
            - ((m : ℂ) * (x : ℂ)) ^ 2 / (4 * (Complex.I * complexEnergy N ε * (m : ℂ) ^ 2))) := by
  unfold eq9Integrand
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [← eq9_eq10_exponent_lapse N ε (x : ℂ) (m : ℂ) hε hmc]
  push_cast
  ring

/-- **[Banihashemi–Jacobson Eq. 10] Schläfli's Bessel integrand** `t^{−n/2} e^{t−z²/4t}` (with `z = m|x|`),
whose `t`-contour integral (from `−i∞+ε` to `i∞+ε`) is `2πi (z/2)^{1−n/2}` times the Bessel function
`J_{n/2−1}(z)`, recovering Eq. 7. -/
noncomputable def eq10Integrand (n : ℕ) (t z : ℂ) : ℂ :=
  t ^ (-(n : ℂ) / 2) * Complex.exp (t - z ^ 2 / (4 * t))

/-- **[Link] The Eq. 10 integrand is Schläfli's Bessel integrand** (up to the `t^{−n/2}` vs `t^{−ν−1}`
normalization with `ν = n/2 − 1`): `eq10Integrand n t z = schlafliBesselIntegrand (n/2 − 1) t z`, so the
Eq. 10 contour integral is the Bessel function of Eq. 7. -/
lemma eq10Integrand_eq_schlafli (n : ℕ) (t z : ℂ) :
    eq10Integrand n t z = schlafliBesselIntegrand ((n : ℂ) / 2 - 1) t z := by
  unfold eq10Integrand schlafliBesselIntegrand
  rw [show (-(n : ℂ) / 2) = (-((n : ℂ) / 2 - 1) - 1) by ring, mul_comm]

end Physlib.QuantumMechanics.ComplexAction.GravLapse.BesselExample

end

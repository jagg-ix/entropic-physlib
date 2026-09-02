/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulomb

/-!
# Convergence of the MIW Coulomb empirical density (Chen–Wang arXiv:2212.09020, §4)

Chen–Wang prove the empirical density `P*_N` of the finite interacting worlds converges to the 1D-hydrogen
first-excited density `P(x) = 2x²e^{−2|x|}` as `N → ∞`.  This module formalizes the algebraic cores of that
proof (the exponential envelope and the full Stein limit kept out to stay import-light).

**Ground energy (Eq. 16).**  The average Hamiltonian at the first excited state is bounded below,
`H_N ≥ −(me⁴/2ℏ²)·N/(N+1)`, with equality iff `Σ 1/x_n = N`; as `N → ∞` this tends to the exact 1D-hydrogen
first-excited energy `−me⁴/2ℏ²`.

* `coulombEnergyFactor_lt_one`, `coulombEnergyFactor_mono` — the factor `N/(N+1) < 1` increases in `N` to `1`.
* `coulombGroundEnergy_gt` — the finite-`N` ground energy lies strictly above the limit `−E₀` (`E₀ = me⁴/2ℏ²`),
  tending up to it — the Coulomb analog of the MIW zero-point energy bound.

**Smallest world shrinks (Eqs. 19–20).**  Cauchy–Schwarz gives `x_N³·N ≤ 1`, so `x_N³ ≤ 1/N → 0`
(`smallest_world_cube_bound`): the innermost world collapses to the node at the origin.

**Normalization `C = 2` (Eqs. 24–27).**  The density-integral bounds `∫₀^∞ P*_N ≤ 1/2` and
`Σ P*_N(x_n)(x_n − x_{n+1}) ≥ 1/2` (each term `x_n/(x_n+x_{n+1}) ≥ 1/2` for a decreasing world pair) squeeze
`(1/4)C` to exactly `1/2`, forcing **`C = 2`** — so `P(x) = 2x²e^{−2|x|}`:

* `density_term_lower` — `x_n/(x_n+x_{n+1}) ≥ 1/2` for `0 < x_{n+1} ≤ x_n` (the `≥ 1/2` integral bound).
* `normalization_constant_two` — `1/2 ≤ C/4 ∧ C/4 ≤ 1/2 ⟹ C = 2` (the squeeze).
* `convergence_normalization` — the derived `C = 2` is exactly `SciamaAdSCPTMiwCoulomb.laplaceNormSq`: the
  convergence proof *derives* the weighted-Laplace normalization that the density module took as given.

So `P*_N → 2x²e^{−2|x|}` as `N → ∞`, with `C = 2` fixed by the squeeze and the ground energy tending to
`−me⁴/2ℏ²` — the MIW method reproduces the 1D hydrogen first excited state, non-Gaussian and all.

Honest scope: the `N/(N+1)` energy factor, the `x_N³ ≤ 1/N` collapse bound, the per-term `≥ 1/2` density bound,
and the `C = 2` squeeze.  The Riemann-sum limits, the first-order ODE `P' − 2(1/x−1)P = 0`, and the Stein rate
are the paper's analytic content, contextualized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulombConvergence

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulomb

/-! ## A. Ground energy → −me⁴/2ℏ² -/

/-- The Coulomb first-excited ground-energy factor `N/(N+1)` (Eq. 16). -/
def coulombEnergyFactor (N : ℕ) : ℝ := (N : ℝ) / ((N : ℝ) + 1)

/-- **[Below the limit] `N/(N+1) < 1`.** -/
theorem coulombEnergyFactor_lt_one (N : ℕ) : coulombEnergyFactor N < 1 := by
  unfold coulombEnergyFactor
  rw [div_lt_one (by positivity)]
  linarith

/-- **[Increases to the limit] `N/(N+1)` is strictly increasing in `N`** (→ 1 as `N → ∞`). -/
theorem coulombEnergyFactor_mono {N M : ℕ} (h : N < M) :
    coulombEnergyFactor N < coulombEnergyFactor M := by
  unfold coulombEnergyFactor
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hNM : (N : ℝ) + 1 < (M : ℝ) + 1 := by
    have hc : (N : ℝ) < (M : ℝ) := by exact_mod_cast h
    linarith
  have e1 : (N : ℝ) / ((N : ℝ) + 1) = 1 - 1 / ((N : ℝ) + 1) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_self hN1.ne']
  have e2 : (M : ℝ) / ((M : ℝ) + 1) = 1 - 1 / ((M : ℝ) + 1) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_self hM1.ne']
  rw [e1, e2]
  linarith [one_div_lt_one_div_of_lt hN1 hNM]

/-- The Coulomb first-excited ground energy `−E₀·N/(N+1)` (`E₀ = me⁴/2ℏ²`). -/
def coulombGroundEnergy (E₀ : ℝ) (N : ℕ) : ℝ := -E₀ * coulombEnergyFactor N

/-- **[Above the limit `−E₀`] the finite-`N` ground energy exceeds `−me⁴/2ℏ²`, tending up to it.** -/
theorem coulombGroundEnergy_gt {E₀ : ℝ} (hE : 0 < E₀) (N : ℕ) :
    -E₀ < coulombGroundEnergy E₀ N := by
  unfold coulombGroundEnergy
  have hfac : coulombEnergyFactor N < 1 := coulombEnergyFactor_lt_one N
  nlinarith [hfac, hE]

/-! ## B. The smallest world collapses to the node -/

/-- **[Smallest world cube bound] `x_N³·N ≤ 1 ⟹ x_N³ ≤ 1/N`.**  From the Cauchy–Schwarz bound (Eq. 19), the
innermost world shrinks (`x_N³ ≤ 1/N → 0`) toward the node at the origin. -/
theorem smallest_world_cube_bound {xN : ℝ} {N : ℕ} (hN : 0 < N) (h : xN ^ 3 * (N : ℝ) ≤ 1) :
    xN ^ 3 ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [le_div_iff₀ hNpos]
  exact h

/-! ## C. Normalization `C = 2` from the density-integral squeeze -/

/-- **[Density term lower bound] `x_n/(x_n+x_{n+1}) ≥ 1/2`** for a decreasing world pair `0 < x_{n+1} ≤ x_n` —
the per-term bound giving `Σ P*_N(x_n)(x_n−x_{n+1}) ≥ 1/2` (Eq. 24). -/
theorem density_term_lower {xn xn1 : ℝ} (hn : 0 < xn) (h1 : 0 ≤ xn1) (hle : xn1 ≤ xn) :
    (1 : ℝ) / 2 ≤ xn / (xn + xn1) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **[Normalization squeeze] `1/2 ≤ C/4 ∧ C/4 ≤ 1/2 ⟹ C = 2`.**  The integral bounds `∫ P*_N ≤ 1/2` and
`Σ P*_N(x_n)(x_n−x_{n+1}) ≥ 1/2` squeeze `(1/4)C` to `1/2` (Eqs. 26–27), forcing `C = 2`. -/
theorem normalization_constant_two {C : ℝ} (hlo : (1 : ℝ) / 2 ≤ C / 4) (hhi : C / 4 ≤ (1 : ℝ) / 2) :
    C = 2 := by linarith

/-- **[The derived normalization matches the density] `C = 2 = laplaceNormSq`.**  The convergence proof derives
the weighted-Laplace normalization `2` that `SciamaAdSCPTMiwCoulomb` used, so `P(x) = 2x²e^{−2|x|}`. -/
theorem convergence_normalization : (2 : ℝ) = laplaceNormSq := rfl

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulombConvergence

end

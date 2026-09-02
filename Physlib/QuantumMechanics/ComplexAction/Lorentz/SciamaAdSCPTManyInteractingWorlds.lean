/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTEverettBranches

/-!
# Many Interacting Worlds vs Everett branches (McKeague–Peköz–Swan, arXiv:1606.06618)

The Casimir/conductivity modules of this arc treat their "branches" in the **Everett** sense
(`SciamaAdSCPTEverettBranches`): decoherent relative states with Born weights `‖·‖²`.  Those weights are **not
postulated** in this repository — the Born rule is already derived several independent ways: from device
unitarity in entropic dynamics (`EntropicTime.CatichaMeasurementGenericBornRule.generic_born_rule`, Caticha
arXiv:2208.02156), as a genuine probability distribution from unit `ℓ²`-norm (`bornDist_sum_one_of_norm_one`,
`bornProbDistribution`), decision-theoretically (`Foundations.RelativeStateConventionality`, Everett–Deutsch),
modally (`Foundations.MinimalModalOnticDynamics`, Barandes: Born = history weight), and hydrodynamically
(`Schrodinger.MadelungPolarDecomposition.madelung_born_rule`, `ρ = |ψ|²`).  McKeague–Peköz–Swan formalize a
**further** many-worlds ontology — Hall–Deckert–Wiseman's **Many Interacting Worlds (MIW)**: a large but *finite*
number of *classical* worlds that *interact* through an interworld potential (a discretized Bohm quantum
potential), whose empirical particle distribution *converges* to the quantum Born density `|ψ_k|²`.  MIW is a
distinct **realist, finite-N** route, and — unlike the derivations above, which fix the ground/normalization
structure — it reaches the *higher-energy* densities `|ψ_k|²` (Maxwell for `k = 1`) via Stein's method.

For the quantum harmonic oscillator the Born density factors as `p_k(x) = b_k(x) φ(x)` with the polynomial
**baseline** `b_k(x) = (He_k(x))²/k!` (`He_k` = probabilist's Hermite, `φ` = standard normal):

* ground state `k = 0`: `He_0 = 1`, `b_0 = 1`, `p_0 = φ` (Gaussian) — recursion `xₙ₊₁ = xₙ − 1/Σxᵢ`;
* first excited `k = 1`: `He_1(x) = x`, `b_1(x) = x²`, `p_1 = x²φ` (**two-sided Maxwell**) — cube-recursion
  `xₙ₊₁³ = xₙ³ − 3/Σ(1/xᵢ)`.

This module formalizes that structure and its link to the Everett branch:

* `miwFirst_two_lobed` — the first-excited Maxwell baseline `b_1 = x²` has a **node at the origin** and is positive
  on each side: a right lobe (`x > 0`) and a left lobe (`x < 0`).
* `miwFirst_lobes_equal_weight` — `b_1` is even, so the two lobes carry **equal weight** — the realist MIW
  counterpart of the equal-Born-weight of `C`-conjugate branches
  (`SciamaAdSCPTEverettBranches.chargeConjugation_preserves_totalBornWeight`), whose `‖·‖²` weights are grounded
  by the repo's Born-derivation layer above.
* `miwLobe` — the two lobes as the two-outcome branch label (`SpinOutcome`), reusing the Everett branch sign; the
  node `x = 0` is the `C`-parity split.
* `groundRecursion_decreasing` / `firstExcitedCubeStep_decreasing` — both MIW recursions produce a strictly
  decreasing world-ordering `x₁ > x₂ > …`, the ordering hypothesis of the convergence theorems.

The **original** MIW paper (Hall, Deckert, Wiseman, *Quantum phenomena modelled by interactions between many
classical worlds*, Phys. Rev. X **4**, 041013 (2014), arXiv:1402.6144) fixes the interworld force by a
conservative potential `U_N = (ℏ²/8m) Σ [1/(x_{n+1}−x_n) − 1/(x_n−x_{n−1})]²`, from which quantum phenomena
arise as **mutual repulsion between worlds**:

* `interworldGapEnergy_repulsive` — the interworld potential core `1/(gap)²` strictly increases as adjacent
  worlds approach (`→ ∞` as a gap closes): the repulsion that keeps worlds apart.
* `nonclassicalMomentum_average_zero` — the mean nonclassical momentum `⟨p^{nc}⟩ = 0` telescopes to vanishing
  boundary gap-reciprocals.
* **`miwGroundEnergy_pos`** / `miwGroundEnergyFactor_lt_one` / `_mono` — the oscillator **zero-point energy from
  mutual exclusion**: `⟨E⟩_N = (N−1)/N · ℏω/2 > 0` (for `N ≥ 2`), increasing in `N` to the exact quantum ZPE
  `ℏω/2` as `N → ∞`.  This is the MIW derivation of the vacuum zero-point energy — the same zero-point/Casimir
  energy carried by `ComptonClock.ZeroPointLength` and `SciamaFockZetaCasimir`, here obtained purely from
  interworld repulsion, closing the loop with the Casimir re-evaluation below.
* `miwN3_recurrence` — the exact `N = 3` ground-state world configuration `(−1, 0, 1)` satisfies the HDW
  ground-state recurrence.

Re-evaluation of the Casimir/conductivity "branch": those results are **Everett**-flavoured (decoherent
sectors).  Their `‖·‖²` weights are already derived, not postulated, by the repo's Born layer above; MIW adds a
*realist, finite-N* derivation that also reaches the higher-energy densities, and its two-lobed first-excited
state is a concrete model of the equal-weight two-branch structure the Everett modules use.  Neither ontology,
by itself, makes the hypothetical flipped vacuum sector actual: that caveat is unchanged.

Honest scope: the polynomial baselines `b_0 = 1`, `b_1 = x²` (the `He_k = 1, x` values), the node/parity/lobe
structure, and the two recursions' monotonicity.  The Gaussian/Maxwell *convergence* theorems (Stein's method,
the generalized zero-bias fixed point) and the interworld-potential derivation are the paper's analytic content,
contextualized here; the density factor `φ` is carried symbolically (baseline only), avoiding the heavy
special-function machinery.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

open Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates

/-! ## A. The MIW baselines `b_k = (He_k)²/k!` -/

/-- The MIW **ground-state** baseline `b_0(x) = (He_0)²/0! = 1`; the density `p_0 = b_0 φ = φ` is Gaussian. -/
def miwGroundBaseline (_x : ℝ) : ℝ := 1

/-- The MIW **first-excited** baseline `b_1(x) = (He_1)²/1! = x²`; the density `p_1 = x² φ` is the two-sided
Maxwell distribution. -/
def miwFirstBaseline (x : ℝ) : ℝ := x ^ 2

/-- **[`b_1` is even] `b_1(−x) = b_1(x)`.**  The first-excited Born density `|ψ_1|²` is parity-even. -/
theorem miwFirst_even (x : ℝ) : miwFirstBaseline (-x) = miwFirstBaseline x := by
  unfold miwFirstBaseline; ring

/-- **[The first-excited state is two-lobed] node at `0`, positive on each side.**  `b_1(0) = 0` (the node) and
`b_1(x) > 0` for `x ≠ 0` — a right lobe (`x > 0`) and a left lobe (`x < 0`), the Maxwell double peak. -/
theorem miwFirst_two_lobed :
    miwFirstBaseline 0 = 0 ∧ ∀ x : ℝ, x ≠ 0 → 0 < miwFirstBaseline x := by
  refine ⟨by simp [miwFirstBaseline], fun x hx => ?_⟩
  unfold miwFirstBaseline
  exact lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))

/-- **[The two lobes carry equal weight] `b_1(x) = b_1(−x)`.**  The realist MIW counterpart of the Everett
equal-Born-weight of `C`-conjugate branches (`chargeConjugation_preserves_totalBornWeight`). -/
theorem miwFirst_lobes_equal_weight (x : ℝ) : miwFirstBaseline x = miwFirstBaseline (-x) :=
  (miwFirst_even x).symm

/-! ## B. The two lobes as the Everett branch -/

/-- The lobe a world occupies as the two-outcome branch label, reusing the Everett branch sign: `+` = right lobe
(`x > 0`), `−` = left lobe (`x < 0`); the node `x = 0` is the split. -/
def miwLobe (s : SpinOutcome) : ℝ := SpinOutcome.sign s

/-- **[The two lobes are `C`-conjugate] `miwLobe(+) = −miwLobe(−)`.**  The right and left Maxwell lobes are the
`x ↦ −x` mirror pair — the parity/`C` two-branch structure of `SciamaAdSCPTEverettBranches`. -/
theorem miwLobe_conjugate : miwLobe .plus = -miwLobe .minus := by
  simp [miwLobe, SpinOutcome.sign]

/-! ## C. The MIW recursions -/

/-- The MIW **ground-state** recursion `xₙ₊₁ = xₙ − 1/Sₙ`, `Sₙ = Σ_{i≤n} xᵢ` (empirical limit: Gaussian). -/
def groundRecursion (xn Sn : ℝ) : ℝ := xn - 1 / Sn

/-- The MIW **first-excited** cube-recursion `xₙ₊₁³ = xₙ³ − 3/Tₙ`, `Tₙ = Σ_{i≤n} 1/xᵢ` (empirical limit:
Maxwell). -/
def firstExcitedCubeStep (xn3 Tn : ℝ) : ℝ := xn3 - 3 / Tn

/-- **[The ground recursion decreases] `xₙ₊₁ < xₙ`.**  With a positive partial sum, each world lies below the
previous — the decreasing ordering `x₁ > x₂ > …` the Gaussian limit theorem assumes. -/
theorem groundRecursion_decreasing (xn Sn : ℝ) (hS : 0 < Sn) : groundRecursion xn Sn < xn := by
  unfold groundRecursion
  have : 0 < 1 / Sn := one_div_pos.mpr hS
  linarith

/-- **[The first-excited recursion decreases the cubes] `xₙ₊₁³ < xₙ³`.**  With a positive reciprocal sum, the
cube-ordering decreases — the ordering the Maxwell limit theorem assumes. -/
theorem firstExcitedCubeStep_decreasing (xn3 Tn : ℝ) (hT : 0 < Tn) :
    firstExcitedCubeStep xn3 Tn < xn3 := by
  unfold firstExcitedCubeStep
  have : 0 < 3 / Tn := div_pos (by norm_num) hT
  linarith

/-! ## D. Hall–Deckert–Wiseman: mutual repulsion and zero-point energy (arXiv:1402.6144) -/

/-- The repulsive interworld gap energy `1/gap²` between two adjacent worlds — the core of the HDW interworld
potential `U_N = (ℏ²/8m) Σ [1/(x_{n+1}−x_n) − 1/(x_n−x_{n−1})]²`. -/
def interworldGapEnergy (gap : ℝ) : ℝ := 1 / gap ^ 2

/-- **[Mutual repulsion] the gap energy increases as adjacent worlds approach.**  For `0 < g₁ < g₂`,
`interworldGapEnergy g₂ < interworldGapEnergy g₁` — closer worlds carry more interworld potential (`→ ∞` as a
gap closes), the repulsion that prevents world collapse. -/
theorem interworldGapEnergy_repulsive {g1 g2 : ℝ} (h1 : 0 < g1) (hlt : g1 < g2) :
    interworldGapEnergy g2 < interworldGapEnergy g1 := by
  unfold interworldGapEnergy
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith [h1, hlt]

/-- The nonclassical momentum of a world (HDW): `p^{nc} = (ℏ/2)(d_{n+1} − d_n)`, with `d_n = 1/(x_n − x_{n−1})`
the gap-reciprocal. -/
def nonclassicalMomentum (hbar dn dn1 : ℝ) : ℝ := hbar / 2 * (dn1 - dn)

/-- **[Mean nonclassical momentum vanishes] `⟨p^{nc}⟩ = 0`.**  The gap-reciprocal differences telescope to
`d_N − d_0`, which vanishes for the boundary conditions `d_0 = d_N = 0` (from `x_0 = −∞`, `x_{N+1} = ∞`) —
HDW's `⟨p^{nc}⟩_N = 0`. -/
theorem nonclassicalMomentum_average_zero (N : ℕ) (d : ℕ → ℝ) (hd0 : d 0 = 0) (hdN : d N = 0) :
    ∑ i ∈ Finset.range N, (d (i + 1) - d i) = 0 := by
  rw [Finset.sum_range_sub d N, hd0, hdN, sub_zero]

/-- The MIW oscillator ground-state energy for `N` worlds (HDW appendix): `⟨E⟩_N = (N−1)/N · ℏω/2`. -/
def miwOscillatorGroundEnergy (N : ℕ) (hbar omega : ℝ) : ℝ :=
  ((N : ℝ) - 1) / (N : ℝ) * (hbar * omega / 2)

/-- **[Zero-point energy from mutual exclusion] `E_N > 0` for `N ≥ 2`.**  The classical ground state (all worlds
at the potential minimum) has `E = 0`, but mutual exclusion forbids it: the MIW oscillator ground energy is
strictly positive — the zero-point energy. -/
theorem miwGroundEnergy_pos (N : ℕ) (hN : 2 ≤ N) {hbar omega : ℝ} (hb : 0 < hbar) (ho : 0 < omega) :
    0 < miwOscillatorGroundEnergy N hbar omega := by
  unfold miwOscillatorGroundEnergy
  have hNpos : 0 < (N : ℝ) := by positivity
  have hN1 : 0 < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hbo : 0 < hbar * omega / 2 := by positivity
  exact mul_pos (div_pos hN1 hNpos) hbo

/-- **[The MIW ground energy is below the quantum ZPE] `(N−1)/N < 1`.** -/
theorem miwGroundEnergyFactor_lt_one (N : ℕ) (hN : 1 ≤ N) : ((N : ℝ) - 1) / (N : ℝ) < 1 := by
  have hNpos : 0 < (N : ℝ) := by positivity
  rw [div_lt_one hNpos]
  linarith

/-- **[The bound tightens to the quantum ZPE ℏω/2] `(N−1)/N` is strictly increasing in `N`.**  As the number of
worlds grows the MIW bound `⟨E⟩_N = (N−1)/N·ℏω/2` increases to the exact quantum zero-point energy `ℏω/2`. -/
theorem miwGroundEnergyFactor_mono {N M : ℕ} (hN : 1 ≤ N) (h : N < M) :
    ((N : ℝ) - 1) / (N : ℝ) < ((M : ℝ) - 1) / (M : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by positivity
  have hMpos : 0 < (M : ℝ) := by
    have hM : 0 < M := by omega
    exact_mod_cast hM
  have hNM : (N : ℝ) < (M : ℝ) := by exact_mod_cast h
  have e1 : ((N : ℝ) - 1) / (N : ℝ) = 1 - 1 / (N : ℝ) := by rw [sub_div, div_self hNpos.ne']
  have e2 : ((M : ℝ) - 1) / (M : ℝ) = 1 - 1 / (M : ℝ) := by rw [sub_div, div_self hMpos.ne']
  rw [e1, e2]
  have : 1 / (M : ℝ) < 1 / (N : ℝ) := one_div_lt_one_div_of_lt hNpos hNM
  linarith

/-- **[Exact `N = 3` ground state] the world configuration `(−1, 0, 1)`** satisfies the HDW ground-state
recurrence `1/(x_{n+1}−x_n) = (x_1+…+x_n)/α` with `α = −1`, at both interior steps. -/
theorem miwN3_recurrence :
    (1 : ℝ) / (0 - (-1)) = (-1) / (-1) ∧ (1 : ℝ) / (1 - 0) = (-1 + 0) / (-1) := by
  norm_num

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

end

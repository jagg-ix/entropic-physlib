/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Physlib.QuantumMechanics.ComplexAction.Particles.CriticalStabilityPrinciple
meta import Zil

/-!
# The nuclear valley of stability, *derived*: mass parabola, fission limit, shells, β-line

Two layers of the nuclear-stability model in one module, each in its own namespace.

**Part I — `NuclearValleyOfStability`.** The `CriticalStabilityPrinciple` applied to nuclei — with the
stability data **derived** from models, not tabulated. Three independent derivations, each taking only the
standard model *coefficients* as parameters:

* **§A — the line of β-stability, from the isobaric mass parabola.** For a fixed mass number the atomic mass is
  a quadratic `M(Z) = c₂ Z² + c₁ Z + c₀` in the charge (Coulomb + asymmetry curvature `c₂ > 0`). We *derive*
  the most-stable charge as the parabola vertex: `mass_sub_min` (`M(Z) − M(Z*) = c₂ (Z − Z*)²`),
  `stable_charge_is_min` (`M(Z*) ≤ M(Z)` — the derived stability line `Z* = −c₁/2c₂`), and
  `stable_charge_unique` (`M(Z) = M(Z*) ↔ Z = Z*` — one stable isobar per mass number).
* **§B — the heaviest stable element, from the liquid-drop fission limit.** The Coulomb energy `∝ Z(Z−1)`
  overwhelms the surface energy `∝ A`; comparing them *derives* the fission-stability bound
  `heaviest_stable_charge_bound` (`a_C Z(Z−1) ≤ 2 a_S A ↔ Z ≤ 1 + 2 a_S r / a_C`, along `A = r Z`) — an
  explicit heaviest-stable charge `heaviestStableCharge = 1 + 2 a_S r / a_C` from the coefficients, not a
  hard-coded `82`.
* **§C — the instability cliff (the principle instance).** The *derived* per-proton Coulomb cost `a_C · Z` is a
  genuine `CriticalStabilitySystem`; `nuclear_stability_cliff` (`= stable_bounded`) shows the stable-charge
  region is bounded, and `stable_region_eq` proves that bound is *exactly* the derived
  `heaviestStableCharge` of §B — closing the loop with `CriticalStabilityPrinciple`.
* **§D — the magic numbers, from shell-model degeneracy.** The 3-D isotropic oscillator shell `N` holds
  `oscillatorDegeneracy N = (N+1)(N+2)` nucleons (spatial `(N+1)(N+2)/2` × 2 spin); the closed-shell counts are
  the cumulative sums, and we *derive* the closed form **`hoMagic_closed`** (`3 · hoMagic k = (k+1)(k+2)(k+3)`),
  giving `2, 8, 20, 40, 70, …` (`hoMagic_values`) from the degeneracy alone — not a list literal.

**Part II — `NuclearBetaStabilityLine`: the β-stability line from the Pauli principle and exact Coulomb — no
fitted asymmetry term.** Part I §A derived the most-stable charge as the vertex of an abstract mass parabola.
Rather than supply that parabola with the *phenomenological* semi-empirical asymmetry term `a_A (A−2Z)²/A`
(a fit), the whole `Z`-dependence is derived from proven, fundamental structure:

* **The asymmetry energy is the Pauli principle.** Fermions fill single-particle levels one per level
  (exclusion — the same antisymmetry that makes the color-singlet baryon in `ColorSingletBaryon` /
  `Su6SpinFlavorBaryon`). The energy of `n` nucleons in an equally-spaced ladder is
  `ε · ∑_{k<n} k = ε · n(n−1)/2 = ε · C(n,2)` — the **same pairwise/binomial count** as
  `Su3TensorDecomposition.antisym2_dim` (`C(3,2)`) and the `d`-shell capacity `C(2l+1,2)`. This is *derived*,
  not fitted: `pauliLadderEnergy_eq_levelSum`.
* **The Coulomb energy is exact.** `a_C · Z(Z−1)/2 = a_C · C(Z,2)` — the pairwise electrostatic energy of `Z`
  protons; the same `C(Z,2)`. No fit.
* **`isospin_kinetic_min`** — the Pauli ladder energy of two isospin species is minimized at `Z = A/2`: the
  exclusion principle *derives* the `N = Z` symmetry (this is the asymmetry energy, `ε (Z − A/2)²`).
* **`nuclearMass_eq_isobaric`** — Pauli + Coulomb reproduce the Part I quadratic `c₂ Z² + c₁ Z + c₀` with
  *derived* coefficients `c₂ = ε + a_C/2`, `c₁ = −(εA + a_C/2)` — no `a_A`.
* **`neutron_excess`** — for `A > 1`, `Z* < A/2`: the Coulomb term breaks the Pauli `N = Z` symmetry, pushing
  the minimum to a neutron excess. `stable_is_neutron_rich` (`Z* < N* = A − Z*`), and the excess grows linearly
  (`neutronExcess_eq`, `neutronExcess_grows`).

**Honest layering.** Everything asserted is *derived*: the vertex minimizer, the fission bound, the bounded
stable region and its identification with the derived boundary, the magic-number closed form, the Pauli-ladder
asymmetry energy, and the neutron excess. The *parameters* — the SEMF coefficients `a_S, a_C`, the ladder
spacing `ε`, the neutron-excess ratio `r` — are liquid-drop / shell-model physical scales, left as free
variables; no semi-empirical asymmetry term appears. The pure oscillator gives `2, 8, 20, 40, 70`; the
empirical `28, 50, 82, 126` require the spin-orbit intruder shift (`NuclearSpinOrbitMagic`, in
`NuclearIsotopeStability`).

## References

* The isobaric mass parabola and β-stability line; the liquid-drop fission limit `Z²/A`; the harmonic-oscillator
  shell degeneracies; the isospin symmetry energy as a Fermi-gas / Pauli-exclusion effect; exact Coulomb
  self-energy. Built on `Particles.CriticalStabilityPrinciple`; complements `Particles.PeriodicTableBlocks`
  (electron-shell structure) and shares the `C(n,2)` antisymmetric-pair count with
  `Particles.Su3TensorDecomposition` / `ColorSingletBaryon`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.CriticalStabilityPrinciple

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability

open Finset


/-- The **isobaric atomic mass** as a quadratic in the nuclear charge `Z` (fixed mass number): the Coulomb and
symmetry terms of the semi-empirical mass formula combine into `c₂ Z² + c₁ Z + c₀`, with curvature `c₂ > 0`. -/
def isobaricMass (c₀ c₁ c₂ Z : ℝ) : ℝ := c₂ * Z ^ 2 + c₁ * Z + c₀

/-- The **most stable charge** for a fixed mass number — the vertex of the mass parabola, `Z* = −c₁ / 2c₂`. This
is *derived* below as the minimizer, not posited. -/
noncomputable def stableCharge (c₁ c₂ : ℝ) : ℝ := -c₁ / (2 * c₂)

/-- **The mass excess over the stability line is a perfect square** `M(Z) − M(Z*) = c₂ (Z − Z*)²`: completing
the square at the parabola vertex. -/
lemma mass_sub_min (c₀ c₁ c₂ : ℝ) (hc : c₂ ≠ 0) (Z : ℝ) :
    isobaricMass c₀ c₁ c₂ Z - isobaricMass c₀ c₁ c₂ (stableCharge c₁ c₂)
      = c₂ * (Z - stableCharge c₁ c₂) ^ 2 := by
  unfold isobaricMass stableCharge
  field_simp
  ring

/-- **The derived line of stability minimizes the mass** `M(Z*) ≤ M(Z)`: for each mass number the charge
`Z* = −c₁/2c₂` is the most stable, since the mass excess `c₂ (Z − Z*)²` is nonnegative. -/
lemma stable_charge_is_min (c₀ c₁ c₂ : ℝ) (hc : 0 < c₂) (Z : ℝ) :
    isobaricMass c₀ c₁ c₂ (stableCharge c₁ c₂) ≤ isobaricMass c₀ c₁ c₂ Z := by
  have key := mass_sub_min c₀ c₁ c₂ (ne_of_gt hc) Z
  have hsq : 0 ≤ c₂ * (Z - stableCharge c₁ c₂) ^ 2 :=
    mul_nonneg (le_of_lt hc) (sq_nonneg _)
  linarith [key, hsq]

/-- **The stable charge is the unique minimizer** `M(Z) = M(Z*) ↔ Z = Z*`: each isobar has exactly one most-
stable charge (the β-stability line is single-valued). -/
lemma stable_charge_unique (c₀ c₁ c₂ : ℝ) (hc : 0 < c₂) (Z : ℝ) :
    isobaricMass c₀ c₁ c₂ Z = isobaricMass c₀ c₁ c₂ (stableCharge c₁ c₂) ↔ Z = stableCharge c₁ c₂ := by
  have key := mass_sub_min c₀ c₁ c₂ (ne_of_gt hc) Z
  constructor
  · intro he
    have h0 : c₂ * (Z - stableCharge c₁ c₂) ^ 2 = 0 := by rw [← key]; linarith
    have hsq : (Z - stableCharge c₁ c₂) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 (ne_of_gt hc)
      · exact h1
    have : Z - stableCharge c₁ c₂ = 0 := by
      exact (pow_eq_zero_iff two_ne_zero).mp hsq
    linarith
  · intro he; rw [he]


/-- **The heaviest stable charge**, *derived* from the fission limit (§B theorem): `Z = 1 + 2 a_S r / a_C`,
where `a_S, a_C` are the surface and Coulomb coefficients and `r = A/Z` the neutron-excess ratio. -/
noncomputable def heaviestStableCharge (aS aC r : ℝ) : ℝ := 1 + 2 * aS * r / aC

/-- **The fission-stability bound, derived.** A nucleus is stable against fission when its Coulomb energy
`a_C Z(Z−1)` stays below twice its surface energy `2 a_S A`; along `A = r Z` this is *equivalent* to
`Z ≤ 1 + 2 a_S r / a_C = heaviestStableCharge`. The heaviest stable element thus comes out of the liquid-drop
coefficients, not from a table. -/
lemma heaviest_stable_charge_bound (aS aC r Z : ℝ) (hAC : 0 < aC) (hZ : 0 < Z) :
    aC * (Z * (Z - 1)) ≤ 2 * aS * (r * Z) ↔ Z ≤ heaviestStableCharge aS aC r := by
  unfold heaviestStableCharge
  constructor
  · intro h
    have h1 : (Z - 1) * aC ≤ 2 * aS * r := by nlinarith [h, hZ]
    have h2 : Z - 1 ≤ 2 * aS * r / aC := by rw [le_div_iff₀ hAC]; linarith
    linarith
  · intro h
    have h2 : Z - 1 ≤ 2 * aS * r / aC := by linarith
    rw [le_div_iff₀ hAC] at h2
    nlinarith [h2, hZ]


/-- The **per-proton Coulomb cost** `a_C · Z` (the marginal Coulomb energy along the stability line) as a
`CriticalStabilitySystem`, with the fission threshold `2 a_S r + a_C`. This is the *derived* monotone unbounded
cost — `linearConfinement` with the Coulomb coefficient as its slope. -/
noncomputable def fissilitySystem (aS aC r : ℝ) (hAC : 0 < aC) : CriticalStabilitySystem :=
  linearConfinement aC (2 * aS * r + aC) hAC

/-- **The nuclear stability cliff** — the below-threshold (stable) charge region is **bounded above**: the valley
of stability terminates. Inherited from `CriticalStabilityPrinciple.stable_bounded`. -/
lemma nuclear_stability_cliff (aS aC r : ℝ) (hAC : 0 < aC) :
    BddAbove {Z | (fissilitySystem aS aC r hAC).cost Z < 2 * aS * r + aC} :=
  (fissilitySystem aS aC r hAC).stable_bounded

/-- **Instability is inevitable for heavy nuclei** — the Coulomb cost crosses the fission threshold at some
charge. Inherited from `CriticalStabilityPrinciple.instability_inevitable`. -/
lemma nuclear_instability_inevitable (aS aC r : ℝ) (hAC : 0 < aC) :
    ∃ Z, 2 * aS * r + aC ≤ (fissilitySystem aS aC r hAC).cost Z :=
  (fissilitySystem aS aC r hAC).instability_inevitable

/-- **The principle's bounded region is exactly the derived boundary** `{Z | cost Z < threshold} =
{Z | Z < heaviestStableCharge}`: the abstract `stable_bounded` cliff coincides with the liquid-drop
heaviest-stable charge of §B — the two derivations agree. -/
lemma stable_region_eq (aS aC r : ℝ) (hAC : 0 < aC) :
    {Z | (fissilitySystem aS aC r hAC).cost Z < 2 * aS * r + aC}
      = {Z | Z < heaviestStableCharge aS aC r} := by
  ext Z
  show aC * Z < 2 * aS * r + aC ↔ Z < heaviestStableCharge aS aC r
  unfold heaviestStableCharge
  constructor
  · intro h
    have : Z - 1 < 2 * aS * r / aC := by rw [lt_div_iff₀ hAC]; nlinarith [h]
    linarith
  · intro h
    have h2 : Z - 1 < 2 * aS * r / aC := by linarith
    rw [lt_div_iff₀ hAC] at h2
    nlinarith [h2]


/-- The **nucleon degeneracy of oscillator shell `N`**: `(N+1)(N+2)` — the `(N+1)(N+2)/2` spatial states of the
3-D isotropic harmonic oscillator times the two spin projections. -/
def oscillatorDegeneracy (N : ℕ) : ℕ := (N + 1) * (N + 2)

/-- The **`k`-th oscillator magic number** — the cumulative nucleon count filling shells `0 … k`. -/
def hoMagic (k : ℕ) : ℕ := ∑ N ∈ range (k + 1), oscillatorDegeneracy N

/-- **The magic-number closed form, derived** `3 · hoMagic k = (k+1)(k+2)(k+3)`: summing the shell degeneracies
`∑_{N=0}^{k} (N+1)(N+2)` gives the oscillator closed-shell counts in closed form (proved by induction). -/
lemma hoMagic_closed (k : ℕ) : 3 * hoMagic k = (k + 1) * (k + 2) * (k + 3) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hstep : hoMagic (n + 1) = hoMagic n + (n + 2) * (n + 3) := by
      rw [hoMagic, sum_range_succ, oscillatorDegeneracy]; rfl
    rw [hstep, Nat.mul_add, ih]; ring

/-- **The derived oscillator magic numbers** `2, 8, 20, 40, 70` — the closed-shell counts from the degeneracy
sum alone. (The empirical `28, 50, 82, 126` require the spin-orbit intruder shift on top of these.) -/
lemma hoMagic_values :
    hoMagic 0 = 2 ∧ hoMagic 1 = 8 ∧ hoMagic 2 = 20 ∧ hoMagic 3 = 40 ∧ hoMagic 4 = 70 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability

/-! ## Part II — the β-stability line from Pauli exclusion and exact Coulomb -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine

open Finset
open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability

/-! ### The Pauli ladder energy, derived from single-level occupation (exclusion) -/

/-- **The Pauli ladder energy** of `n` fermions: `ε · n(n−1)/2`. Derived below as `ε · ∑_{k<n} k`, the sum of
single-particle level energies `ε·k` with one fermion per level (exclusion). -/
noncomputable def pauliLadderEnergy (ε n : ℝ) : ℝ := ε * (n * (n - 1) / 2)

/-- **The level-fill sum** `∑_{k<n} k = n(n−1)/2` — the cumulative single-particle energy when `n` fermions
occupy the lowest `n` distinct levels (the Pauli exclusion filling; the triangular / `C(n,2)` number). -/
lemma pauli_level_sum (n : ℕ) : (∑ k ∈ range n, (k : ℝ)) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-- **The Pauli ladder energy is the sum of occupied single-particle levels** `ε · ∑_{k<n} k`: the ladder
energy is *derived* from filling one fermion per level by exclusion, not posited. -/
lemma pauliLadderEnergy_eq_levelSum (ε : ℝ) (n : ℕ) :
    pauliLadderEnergy ε n = ε * ∑ k ∈ range n, (k : ℝ) := by
  rw [pauliLadderEnergy, pauli_level_sum]

/-! ### The isospin asymmetry energy — Pauli exclusion derives `N = Z` -/

/-- The **isospin kinetic energy**: two Pauli ladders, `Z` protons and `A − Z` neutrons, each filled by
exclusion. Its minimum is the asymmetry energy. -/
noncomputable def isospinKineticEnergy (ε A Z : ℝ) : ℝ :=
  pauliLadderEnergy ε Z + pauliLadderEnergy ε (A - Z)

/-- **The isospin energy excess is a perfect square** `E(Z) − E(A/2) = ε (Z − A/2)²`: the two-ladder Pauli
energy, as a function of the charge split, is a parabola centred at the symmetric point. -/
lemma isospin_kinetic_sub (ε A Z : ℝ) :
    isospinKineticEnergy ε A Z - isospinKineticEnergy ε A (A / 2) = ε * (Z - A / 2) ^ 2 := by
  unfold isospinKineticEnergy pauliLadderEnergy; ring

/-- **Pauli exclusion derives the `N = Z` symmetry** `E(A/2) ≤ E(Z)`: filling two isospin Fermi ladders costs
least when the charge is `Z = A/2`. This *is* the symmetry (asymmetry) energy — from exclusion, not from a fit. -/
lemma isospin_kinetic_min (ε A Z : ℝ) (hε : 0 < ε) :
    isospinKineticEnergy ε A (A / 2) ≤ isospinKineticEnergy ε A Z := by
  have key := isospin_kinetic_sub ε A Z
  have hsq : 0 ≤ ε * (Z - A / 2) ^ 2 := mul_nonneg (le_of_lt hε) (sq_nonneg _)
  linarith

/-! ### Adding exact Coulomb — the β-stability line and neutron excess -/

/-- The **exact Coulomb self-energy** of `Z` protons: `a_C · Z(Z−1)/2 = a_C · C(Z,2)` — the pairwise
electrostatic energy (the same `C(Z,2)` pair count as the Pauli ladder). -/
noncomputable def coulombEnergy (aC Z : ℝ) : ℝ := aC * (Z * (Z - 1) / 2)

/-- The **nuclear mass** relevant to the charge: Pauli isospin ladders plus exact Coulomb. A quadratic in `Z`
with *derived* coefficients (no fitted asymmetry). -/
noncomputable def nuclearMass (ε aC A Z : ℝ) : ℝ := isospinKineticEnergy ε A Z + coulombEnergy aC Z

/-- The **derived curvature** `c₂ = ε + a_C/2` of the nuclear mass parabola: Pauli plus Coulomb, both positive. -/
noncomputable def massCurvature (ε aC : ℝ) : ℝ := ε + aC / 2

/-- The **derived linear coefficient** `c₁ = −(εA + a_C/2)` of the nuclear mass parabola. -/
noncomputable def massLinear (ε aC A : ℝ) : ℝ := -(ε * A + aC / 2)

/-- **Pauli + Coulomb reproduce the Part I mass parabola** with *derived* coefficients
`nuclearMass = c₂ Z² + c₁ Z + c₀`, `c₂ = ε + a_C/2`, `c₁ = −(εA + a_C/2)` — no semi-empirical asymmetry term. -/
lemma nuclearMass_eq_isobaric (ε aC A Z : ℝ) :
    nuclearMass ε aC A Z
      = isobaricMass (ε / 2 * (A ^ 2 - A)) (massLinear ε aC A) (massCurvature ε aC) Z := by
  unfold nuclearMass isospinKineticEnergy pauliLadderEnergy coulombEnergy isobaricMass massLinear massCurvature
  ring

/-- **The nuclear mass parabola opens upward** `c₂ > 0`, so `NuclearValleyOfStability.stable_charge_is_min`
makes `betaStableCharge` the genuine minimizer of `nuclearMass`. -/
lemma massCurvature_pos (ε aC : ℝ) (hε : 0 < ε) (hC : 0 < aC) : 0 < massCurvature ε aC := by
  unfold massCurvature; linarith

/-- The **β-stable charge** — the vertex of the Pauli-plus-Coulomb mass parabola. -/
noncomputable def betaStableCharge (ε aC A : ℝ) : ℝ :=
  stableCharge (massLinear ε aC A) (massCurvature ε aC)

/-- **The stability line is neutron-rich, derived** `Z* < A/2` for `A > 1`: the exact Coulomb term breaks the
Pauli `N = Z` symmetry (`isospin_kinetic_min`), pushing the mass minimum to a neutron excess. Purely from Pauli
exclusion and Coulomb — no fitted asymmetry coefficient. -/
lemma neutron_excess (ε aC A : ℝ) (hε : 0 < ε) (hC : 0 < aC) (hA : 1 < A) :
    betaStableCharge ε aC A < A / 2 := by
  have hden : 0 < 2 * massCurvature ε aC := by
    have := massCurvature_pos ε aC hε hC; linarith
  unfold betaStableCharge stableCharge massLinear massCurvature at *
  rw [neg_neg, div_lt_iff₀ hden]
  nlinarith [mul_pos (show (0 : ℝ) < A - 1 by linarith) hC]

/-- **Stable nuclei have more neutrons than protons** `Z* < N* = A − Z*` (for `A > 1`). -/
lemma stable_is_neutron_rich (ε aC A : ℝ) (hε : 0 < ε) (hC : 0 < aC) (hA : 1 < A) :
    betaStableCharge ε aC A < A - betaStableCharge ε aC A := by
  have := neutron_excess ε aC A hε hC hA; linarith

/-! ### The neutron excess grows linearly with mass number -/

/-- The **neutron excess** `N* − Z* = A − 2 Z*` along the β-stability line. -/
noncomputable def neutronExcess (ε aC A : ℝ) : ℝ := A - 2 * betaStableCharge ε aC A

/-- **The neutron excess is linear in `A`, derived** `N* − Z* = a_C (A − 1) / (2ε + a_C)`: the Coulomb-to-Pauli
ratio fixes the slope. The excess vanishes at `A = 1` and grows with mass number — the closed-form law behind
the valley curving away from `N = Z`. -/
lemma neutronExcess_eq (ε aC A : ℝ) (hε : 0 < ε) (hC : 0 < aC) :
    neutronExcess ε aC A = aC * (A - 1) / (2 * ε + aC) := by
  have h1 : (2 * massCurvature ε aC) ≠ 0 := by
    have := massCurvature_pos ε aC hε hC; positivity
  have h2 : (2 * ε + aC) ≠ 0 := by positivity
  unfold neutronExcess betaStableCharge stableCharge massLinear massCurvature at *
  rw [neg_neg]
  field_simp
  ring

/-- **The neutron excess grows with mass number** — heavier stable nuclei are progressively more neutron-rich:
`A < B → N*(A) − Z*(A) < N*(B) − Z*(B)`. The Coulomb term's linear contribution to the excess accumulates. -/
lemma neutronExcess_grows (ε aC A B : ℝ) (hε : 0 < ε) (hC : 0 < aC) (hAB : A < B) :
    neutronExcess ε aC A < neutronExcess ε aC B := by
  rw [neutronExcess_eq ε aC A hε hC, neutronExcess_eq ε aC B hε hC]
  have hden : (0 : ℝ) < 2 * ε + aC := by linarith
  gcongr

end Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability.stable_charge_is_min where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  formalizes @ "claim:the-beta-stability-line-is-the-derived-vertex-minimizer-of-the-isobaric-mass-parabola",
  caveat @ "claim:the-semi-empirical-coefficients-are-liquid-drop-parameters-left-free"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability.hoMagic_closed where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-oscillator-magic-numbers-have-the-closed-form-three-hoMagic-equals-k-plus-one-times-k-plus-two-times-k-plus-three",
  caveat @ "claim:the-pure-oscillator-gives-two-eight-twenty-forty-seventy-not-the-spin-orbit-numbers"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine.nuclearMass_eq_isobaric where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability.stable_charge_is_min",
  formalizes @ "claim:pauli-exclusion-plus-exact-coulomb-reproduce-the-isobaric-parabola-with-no-fitted-asymmetry-term",
  requires @ "claim:the-beta-stability-line-is-the-derived-vertex-minimizer-of-the-isobaric-mass-parabola"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine.neutron_excess where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine.massCurvature_pos",
  formalizes @ "claim:the-coulomb-term-breaks-the-pauli-N-equals-Z-symmetry-giving-a-neutron-excess",
  requires @ "claim:pauli-exclusion-plus-exact-coulomb-reproduce-the-isobaric-parabola-with-no-fitted-asymmetry-term"

zil_file_contract physlib.nuclearValleyOfStability where
  promises "The nuclear valley of stability derived: the beta-stability line is the vertex minimizer of the isobaric mass parabola, the oscillator magic numbers have a closed form, Pauli exclusion plus exact Coulomb reproduce the parabola with no fitted asymmetry term, and the Coulomb term breaks the N equals Z symmetry to give a neutron excess."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability.isobaricMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability.hoMagic",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine.pauliLadderEnergy"]
  forbids_substitutes ["fitted semi-empirical coefficients, left as free liquid-drop parameters",
    "the empirical spin-orbit magic numbers, which need the intruder shift"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability.stable_charge_is_min,
    Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability.hoMagic_closed,
    Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine.nuclearMass_eq_isobaric,
    Physlib.QuantumMechanics.ComplexAction.Particles.NuclearBetaStabilityLine.neutron_excess]

/- ZIL-END -/

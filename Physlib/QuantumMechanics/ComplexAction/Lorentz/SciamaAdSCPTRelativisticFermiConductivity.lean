/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTEverettBranches

/-!
# The relativistic-Fermi conductivity endpoint: a branch where Au > Ag > Cu

`Physlib.CondensedMatter.NobleMetalBranchTransport` builds the carrier for comparing intrinsic bulk
conductivity of the monovalent fcc noble metals across Everett/vacuum sectors — a continuum transport integral,
the no-reordering-by-charge theorem, the measured reference order `Ag > Cu > Au`, and a conditional crossing
theorem `exists_gold_silver_crossing` — but leaves an **explicit gap**: it supplies no relativistic band
calculation that produces the `Au > Ag > Cu` endpoint sign.  This module supplies that endpoint from the
relativistic Fermi-surface equations.

The physics.  For a monovalent metal the Drude/Sommerfeld conductivity is `σ = n e² τ / m*`, and at the Fermi
level the relativistic effective mass is the Lorentz-enhanced mass `m* = γ_F m_e`, with Lorentz factor
`γ_F(Z) = √(1 + (Zα)²)` — the valence `s`-electron travels at `v/c ≈ Zα`.  The ordering across `Cu, Ag, Au` is
governed by the **relativistic Fermi enhancement**

`E(Z) = γ_F(Z)² = 1 + (Zα)²`,

which increases with the atomic number `Z` (`E(Au=79) > E(Ag=47) > E(Cu=29)`); ordering by `E` is identical to
ordering by `γ_F` (`√` is monotone), so `E` is used throughout to keep the model exact and sqrt-free.  In our
vacuum the relativistic contraction *raises* `m*` for heavy `Z`, so `σ ∝ 1/E` is **suppressed** for gold (gold
worst).  In a counterfactual sector where the relativistic band correction carries the opposite sign — a
*different effective coupling*, not a CPT image, since CPT preserves `α`, the masses, and hence the ordering —
the heavy-`Z` carriers are *enhanced*, `σ ∝ E`, and the ordering **reverses to `Au > Ag > Cu`**.

* `relEnhancement_lt` / `relEnhancement_noble_order` — `E` strictly increases with `Z`.
* `drude_relativistic_suppression` — the Drude conductivity with the relativistic effective mass is
  `(n e² τ / m_e)/E`: the relativistic Fermi enhancement suppresses conduction.
* `branchConductivity_gold_worst_our_sector` — at the sector `λ = 0` (`σ ∝ 1/E`), gold is worst
  (`Cu > Ag > Au`, the reference-like ordering).
* **`branchConductivity_gold_first_flipped_sector`** — at the sector `λ = 1` (`σ ∝ E`), the ordering is
  **`Au > Ag > Cu`** (`GoldFirstOrder`): the endpoint `NobleMetalBranchTransport` was missing.  With both
  endpoint signs supplied and continuity, `NobleMetalBranchTransport.exists_gold_silver_crossing` yields an
  exact `Au = Ag` crossing at an intermediate vacuum parameter.
* `flipped_branch_gold_first` — the `Au > Ag > Cu` sector, a counterfactual opposite-sign coupling *analogous
  to* a `−` branch (`SciamaAdSCPTEverettBranches`), **not** a genuine Everett branch: `α`, the masses, and the
  ordering are CPT- and branch-invariant (`SciamaAdSCPTBranchConfigurationAnalogy`).

Honest scope (matching `NobleMetalBranchTransport`'s framing): this is an **idealized** model — the common
Drude prefactor `σ₀ = n e² τ / m_e` is taken equal across the three metals so the ordering is *purely* the
relativistic Fermi enhancement, isolating the effect (real `Ag > Cu` also involves electron–phonon/band
detail).  The `λ = 1` "flipped" sector is a **hypothetical** opposite-sign coupling (a landscape counterfactual,
*not* a CPT image — CPT preserves the ordering), **not** our world:
the model does not claim our-world physics produces `Au > Ag > Cu`, only that a consistent relativistic-Fermi
branch does — supplying the endpoint sign that turns the crossing into a theorem.  Whether nature realizes that
sector, or gives it nonzero Born weight, remains a separate physical law.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

open Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates

/-! ## A. The relativistic Fermi enhancement -/

set_option backward.isDefEq.respectTransparency false in
/-- The three monovalent fcc noble metals. -/
inductive NobleMetal
  | copper
  | silver
  | gold
deriving DecidableEq, Fintype, Repr

/-- Atomic number `Z`: `Cu = 29`, `Ag = 47`, `Au = 79`. -/
def atomicNumber : NobleMetal → ℝ
  | .copper => 29
  | .silver => 47
  | .gold => 79

/-- The fine-structure constant `α ≈ 1/137`. -/
def fineStructure : ℝ := 1 / 137

/-- The **relativistic Fermi enhancement** `E(Z) = γ_F(Z)² = 1 + (Zα)²` — the square of the valence
`s`-electron Lorentz factor (its speed is `v/c ≈ Zα`).  Ordering by `E` equals ordering by `γ_F`. -/
def relEnhancement (Z : ℝ) : ℝ := 1 + (Z * fineStructure) ^ 2

/-- The **relativistic effective mass** enhancement factor at the Fermi level, `m*/m_e = E`. -/
def relEffectiveMass (me Z : ℝ) : ℝ := relEnhancement Z * me

/-- `E > 0`. -/
theorem relEnhancement_pos (Z : ℝ) : 0 < relEnhancement Z := by
  unfold relEnhancement; positivity

/-- **[`E` strictly increases with `Z`]** heavier atoms have a larger relativistic Fermi enhancement. -/
theorem relEnhancement_lt {Z₁ Z₂ : ℝ} (h : 0 ≤ Z₁) (hlt : Z₁ < Z₂) :
    relEnhancement Z₁ < relEnhancement Z₂ := by
  have hα : (0 : ℝ) < fineStructure := by rw [fineStructure]; norm_num
  have h1 : 0 ≤ Z₁ * fineStructure := mul_nonneg h hα.le
  have h2 : Z₁ * fineStructure < Z₂ * fineStructure := mul_lt_mul_of_pos_right hlt hα
  unfold relEnhancement
  nlinarith [h1, h2]

/-- **`E(Au) > E(Ag) > E(Cu)`.** -/
theorem relEnhancement_noble_order :
    relEnhancement 47 < relEnhancement 79 ∧ relEnhancement 29 < relEnhancement 47 :=
  ⟨relEnhancement_lt (by norm_num) (by norm_num),
    relEnhancement_lt (by norm_num) (by norm_num)⟩

/-! ## B. Drude conductivity with the relativistic Fermi mass -/

/-- The Drude/Sommerfeld conductivity `σ = n e² τ / m*`. -/
def drudeConductivity (n e τ mstar : ℝ) : ℝ := n * e ^ 2 * τ / mstar

/-- **[Relativistic suppression] `σ = (n e² τ / m_e)/E`.**  Using the relativistic effective mass, the Drude
conductivity is the base value divided by the relativistic Fermi enhancement — heavy `Z` conducts less. -/
theorem drude_relativistic_suppression (n e τ me Z : ℝ) :
    drudeConductivity n e τ (relEffectiveMass me Z) = (n * e ^ 2 * τ / me) / relEnhancement Z := by
  rw [drudeConductivity, relEffectiveMass, mul_comm (relEnhancement Z) me, div_mul_eq_div_div]

/-! ## C. The branch-parameterized conductivity and its two endpoints -/

/-- The branch conductivity in vacuum/order sector `λ ∈ [0,1]`, with an idealized common Drude prefactor `σ₀`.
At `λ = 0` (our sector) the relativistic band correction **suppresses** heavy-`Z` carriers (`σ ∝ 1/E`); at
`λ = 1` (the counterfactual opposite-sign sector) it **enhances** them (`σ ∝ E`). -/
def branchConductivity (σ₀ lam : ℝ) (X : NobleMetal) : ℝ :=
  σ₀ * ((1 - lam) / relEnhancement (atomicNumber X) + lam * relEnhancement (atomicNumber X))

/-- The proposed alternative ordering `Au > Ag > Cu`. -/
def GoldFirstOrder (σ : NobleMetal → ℝ) : Prop :=
  σ .gold > σ .silver ∧ σ .silver > σ .copper

@[simp] theorem branchConductivity_zero (σ₀ : ℝ) (X : NobleMetal) :
    branchConductivity σ₀ 0 X = σ₀ / relEnhancement (atomicNumber X) := by
  rw [branchConductivity]; ring

@[simp] theorem branchConductivity_one (σ₀ : ℝ) (X : NobleMetal) :
    branchConductivity σ₀ 1 X = σ₀ * relEnhancement (atomicNumber X) := by
  rw [branchConductivity]; ring

/-- **[Our sector, `λ = 0`: gold is worst] `Cu > Ag > Au`.**  With `σ ∝ 1/E`, the increasing relativistic Fermi
enhancement makes the heaviest noble metal conduct least — the reference-like ordering with gold last. -/
theorem branchConductivity_gold_worst_our_sector (σ₀ : ℝ) (h0 : 0 < σ₀) :
    branchConductivity σ₀ 0 .copper > branchConductivity σ₀ 0 .silver
      ∧ branchConductivity σ₀ 0 .silver > branchConductivity σ₀ 0 .gold := by
  simp only [branchConductivity_zero, atomicNumber]
  refine ⟨?_, ?_⟩
  · rw [gt_iff_lt, div_eq_mul_one_div σ₀ (relEnhancement 47),
        div_eq_mul_one_div σ₀ (relEnhancement 29)]
    exact mul_lt_mul_of_pos_left
      (one_div_lt_one_div_of_lt (relEnhancement_pos 29) relEnhancement_noble_order.2) h0
  · rw [gt_iff_lt, div_eq_mul_one_div σ₀ (relEnhancement 79),
        div_eq_mul_one_div σ₀ (relEnhancement 47)]
    exact mul_lt_mul_of_pos_left
      (one_div_lt_one_div_of_lt (relEnhancement_pos 47) relEnhancement_noble_order.1) h0

/-- **[Flipped sector, `λ = 1`: `Au > Ag > Cu`] `GoldFirstOrder`.**  With `σ ∝ E`, the increasing relativistic
Fermi enhancement makes the heaviest noble metal conduct most — the endpoint `NobleMetalBranchTransport` was
missing. -/
theorem branchConductivity_gold_first_flipped_sector (σ₀ : ℝ) (h0 : 0 < σ₀) :
    GoldFirstOrder (branchConductivity σ₀ 1) := by
  rw [GoldFirstOrder]
  simp only [branchConductivity_one, atomicNumber]
  exact ⟨by nlinarith [relEnhancement_noble_order.1, h0],
    by nlinarith [relEnhancement_noble_order.2, h0]⟩

/-! ## D. The gold-first sector as a counterfactual coupling (analogous to a branch) -/

/-- The illustrative coupling assigned to each branch *label*: `+` ↦ `λ = 0` (our `σ ∝ 1/E` sector), `−` ↦
`λ = 1` (the counterfactual opposite-sign sector).  A per-label modelling choice, not a genuine per-branch
physical constant — `α` is branch-invariant. -/
def sectorParameter : SpinOutcome → ℝ
  | .plus => 0
  | .minus => 1

/-- **[The `Au > Ag > Cu` sector — a counterfactual coupling analogous to a `−` branch].**  The gold-first
ordering is realized only in a hypothetical opposite-sign (`σ ∝ E`) coupling, *analogous to* a `−` branch of
`SciamaAdSCPTEverettBranches` but **not** a genuine Everett branch: CPT and every branch share `α`, the masses,
and hence the ordering (`SciamaAdSCPTBranchConfigurationAnalogy.ordering_branch_invariant_at_shared_coupling`).
A conditional endpoint, not a claim that nature occupies it. -/
theorem flipped_branch_gold_first (σ₀ : ℝ) (h0 : 0 < σ₀) :
    GoldFirstOrder (branchConductivity σ₀ (sectorParameter .minus)) :=
  branchConductivity_gold_first_flipped_sector σ₀ h0

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

end

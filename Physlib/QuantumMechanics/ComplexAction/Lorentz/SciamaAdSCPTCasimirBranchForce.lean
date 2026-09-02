/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-!
# The Casimir force across noble-metal branches: conductivity reorders the vacuum force

The Casimir *effect* is already formalized in this arc as a ζ-regularized vacuum energy:
`SciamaFockZetaCasimir` proves `ζ(−1) = −1/12` and `stringIntercept D = −(D−2)·½·ζ(−1) = (D−2)/24`
(the Casimir vacuum energy per transverse dimension), and `SciamaFockStringCasimir` fixes the critical
dimension `D = 26`.  This module adds the **material** side: the Casimir *force* between real metal plates
depends on the plates' reflectivity, which is fixed by their conductivity — so the relativistic-Fermi branch
that reorders noble-metal conductivity (`SciamaAdSCPTRelativisticFermiConductivity`) also reorders the Casimir
force.

Between ideal parallel plates the Casimir pressure is `P_ideal = −π² ℏ c / (240 a⁴)` (`a` = separation) — the
same vacuum-energy structure the ζ-regularization gives.  For a real metal (Drude/Lifshitz) the force is
*reduced* by a reflectivity factor `η(σ) ∈ (0,1)` that increases with conductivity `σ` and tends to `1` (the
ideal-conductor limit) as `σ → ∞`.  Modelling `η(σ) = σ/(1+σ)` (the leading monotone shape):

* `casimirReduction_lt` — the reflectivity reduction `η` strictly increases with conductivity.
* `casimirForce_mono` — the Casimir force magnitude `|P_ideal|·η(σ)` strictly increases with conductivity: a
  better conductor sits closer to the ideal-conductor Casimir force.
* **`casimirForce_gold_first_flipped`** — in the flipped (CPT-even) vacuum sector where conductivity orders
  `Au > Ag > Cu` (`branchConductivity_gold_first_flipped_sector`), the **Casimir force magnitude orders
  `Au > Ag > Cu`** too: the same branch that inverts the conductivity ordering inverts which metal's plates feel
  the strongest vacuum force.

So the two faces of the vacuum meet: the ζ-regularized zero-point energy (`SciamaFockZetaCasimir`, `D = 26`) and
the material Casimir force are both fixed off the same branch/vacuum sector, and the relativistic Fermi
enhancement `γ_F(Z)` that reorders conduction reorders the Casimir force through the plates' reflectivity.

Honest scope: the monotonicity of the Casimir force in conductivity and the resulting branch ordering, with an
idealized reflectivity `η = σ/(1+σ)` and the ideal prefactor `|P_ideal|` carried abstractly as a positive
constant.  The full Lifshitz formula (frequency-dependent permittivity, the exact plasma/Drude kernel) is the
physical content; here the qualitative conductivity → force ordering is made exact, inheriting the same
"hypothetical flipped sector, not our world" caveat as the conductivity model.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCasimirBranchForce

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-- The Drude/Lifshitz **reflectivity reduction** of the Casimir force for a plate of conductivity `σ`:
`η(σ) = σ/(1+σ) ∈ (0,1)`, increasing in `σ` and tending to `1` (ideal conductor) as `σ → ∞`. -/
def casimirReduction (σ : ℝ) : ℝ := σ / (1 + σ)

/-- The real Casimir force magnitude between plates of conductivity `σ`: the ideal pressure magnitude
`|P_ideal| = π²ℏc/(240a⁴)` (carried as `pref`) times the reflectivity reduction. -/
def casimirForceMagnitude (pref σ : ℝ) : ℝ := pref * casimirReduction σ

/-- `η(σ) = 1 − 1/(1+σ)`. -/
theorem casimirReduction_eq (σ : ℝ) (hσ : (1 : ℝ) + σ ≠ 0) :
    casimirReduction σ = 1 - 1 / (1 + σ) := by
  rw [casimirReduction]
  field_simp
  ring

/-- **[Reflectivity increases with conductivity] `η` is strictly monotone.** -/
theorem casimirReduction_lt {σ₁ σ₂ : ℝ} (h1 : 0 ≤ σ₁) (hlt : σ₁ < σ₂) :
    casimirReduction σ₁ < casimirReduction σ₂ := by
  have hd1 : (0 : ℝ) < 1 + σ₁ := by linarith
  have hd2 : (0 : ℝ) < 1 + σ₂ := by linarith
  rw [casimirReduction_eq σ₁ hd1.ne', casimirReduction_eq σ₂ hd2.ne']
  have hinv : 1 / (1 + σ₂) < 1 / (1 + σ₁) := one_div_lt_one_div_of_lt hd1 (by linarith)
  linarith

/-- **[The Casimir force grows with conductivity]** a better conductor's plates feel a stronger vacuum force
(closer to the ideal-conductor limit). -/
theorem casimirForce_mono (pref : ℝ) (hpref : 0 < pref) {σ₁ σ₂ : ℝ} (h1 : 0 ≤ σ₁) (hlt : σ₁ < σ₂) :
    casimirForceMagnitude pref σ₁ < casimirForceMagnitude pref σ₂ := by
  unfold casimirForceMagnitude
  exact mul_lt_mul_of_pos_left (casimirReduction_lt h1 hlt) hpref

/-- **[The flipped branch reorders the Casimir force] `Au > Ag > Cu`.**  In the CPT-even vacuum sector where the
relativistic Fermi enhancement makes conductivity order `Au > Ag > Cu`, the Casimir force magnitude between
plates of each metal orders `Au > Ag > Cu` as well — the same branch inverts both the conduction and the
vacuum-force ordering. -/
theorem casimirForce_gold_first_flipped (σ₀ pref : ℝ) (h0 : 0 < σ₀) (hpref : 0 < pref) :
    casimirForceMagnitude pref (branchConductivity σ₀ 1 .gold)
        > casimirForceMagnitude pref (branchConductivity σ₀ 1 .silver)
      ∧ casimirForceMagnitude pref (branchConductivity σ₀ 1 .silver)
        > casimirForceMagnitude pref (branchConductivity σ₀ 1 .copper) := by
  have hord := branchConductivity_gold_first_flipped_sector σ₀ h0
  rw [GoldFirstOrder] at hord
  have hpos : ∀ X : NobleMetal, 0 < branchConductivity σ₀ 1 X := by
    intro X
    rw [branchConductivity_one]
    exact mul_pos h0 (relEnhancement_pos _)
  exact ⟨casimirForce_mono pref hpref (hpos .silver).le hord.1,
    casimirForce_mono pref hpref (hpos .copper).le hord.2⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCasimirBranchForce

end

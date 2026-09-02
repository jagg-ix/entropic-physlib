/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.FirstLaw
public import Physlib.ClassicalMechanics.Noether.DissipativeBalance
public import Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge

/-!
# Babourova–Frolov: the dilaton-spin fluid conservation laws as Noether balances

The remaining dynamical content of Babourova–Frolov (1998) — the **Noether quasiconservation
identities** (Eqs. 2.1–2.3) and the **energy conservation / isentropy** along a streamline
(Eqs. 2.7–2.8) — is exactly the repository's `Thermodynamics.FirstLaw.ThermodynamicWorldline` and
`ClassicalMechanics.Noether.DissipativeBalance.NoetherBalance`: a conserved charge whose change is
the integrated defect. This module formalizes them on that existing infrastructure.

* **§A — the isentropic dilaton-spin fluid** (Eqs. 2.7–2.8). A streamline with **no heat flux**
  (`ds = 0`) is an isentropic `ThermodynamicWorldline` whose energy changes only by the work
  `(ε+p)/n dn` (`isentropicFluid_energy_from_work`, Eq. 2.7); a concrete element (`isentropicFluid`)
  projects to a `NoetherBalance` (`isentropicFluidBalance`) whose charge is conserved at equilibrium
  (`isentropicFluid_conserved`, Eq. 2.8).
* **§B — the energy-momentum quasiconservation** (Eq. 2.1). The canonical energy-momentum is a
  `NoetherBalance` whose **defect is the geometric force** (Mathisson + torsion + Weyl, the Eq. 3.2
  decomposition). Corollary 1 — a free particle has zero geometric force
  (`corollary1_geometricForce_zero`) hence conserved energy-momentum
  (`corollary1_energyMomentum_conserved`, via `conserved_of_zero_defect`). Corollary 3 — without
  dilatonic charge the Weyl part of the defect vanishes (`energyMomentumDefect_no_weyl`).

**Honest layering.** Proven: the isentropic fluid instantiates `ThermodynamicWorldline`, its energy
follows the work (Eq. 2.7), it projects to a conserved `NoetherBalance` (Eq. 2.8); and the
energy-momentum defect is the geometric force, vanishing for a free particle / losing its Weyl part
without dilatonic charge. The form-valued Noether identities (Eqs. 2.1–2.3) are represented by the
scalar balance law `dQ = −defect` of `NoetherBalance` (the integrated divergence), not by the full
exterior calculus.

## References

* O. V. Babourova, B. N. Frolov, "Perfect fluid and test particle with spin and dilatonic charge in a
  Weyl-Cartan space", Mod. Phys. Lett. A **13**, 7 (1998) [`Babourova:1998ah`], Eqs. (2.1)–(2.3),
  (2.7)–(2.8). Reuses `Thermodynamics.FirstLaw` (`ThermodynamicWorldline`, `toNoetherBalance`),
  `ClassicalMechanics.Noether.DissipativeBalance` (`NoetherBalance`, `conserved_of_zero_defect`), and
  `WeylCartanDilatonicCharge` (`mathissonForce`, `weylForce`).
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WeylCartanFluidNoether

open Physlib.Thermodynamics.FirstLaw
open Physlib.ClassicalMechanics.Noether.DissipativeBalance
open Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge


/-- **The isentropic energy law** (Babourova–Frolov Eq. 2.7): along a streamline with no heat flux
(`ds = 0`), the fluid's energy changes *only* by the work `(ε+p)/n dn` — reusing
`ThermodynamicWorldline.firstLaw`. -/
lemma isentropicFluid_energy_from_work (T : ThermodynamicWorldline) (hisen : ∀ t, T.dQ_dt t = 0)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    T.U t₂ - T.U t₁ = ∫ t in t₁..t₂, -T.dW_dt t := by
  have hfl := T.firstLaw t₁ t₂ h
  rw [hfl]; congr 1; funext t; rw [hisen t]; ring

/-- **A concrete isentropic dilaton-spin fluid element**: no heat flux (`ds = 0`, Eq. 2.8), energy
changing only by the constant work rate — a `ThermodynamicWorldline`. -/
noncomputable def isentropicFluid (workRate : ℝ) : ThermodynamicWorldline where
  U := fun t => - workRate * t
  dQ_dt := fun _ => 0
  dW_dt := fun _ => workRate
  firstLaw := by
    intro t₁ t₂ h
    simp only [zero_sub, intervalIntegral.integral_neg, intervalIntegral.integral_const,
      smul_eq_mul]
    ring

/-- **The dilaton-spin fluid's Noether balance**: the energy is the reversible Noether charge, the
work rate the defect (`ThermodynamicWorldline.toNoetherBalance`). -/
noncomputable def isentropicFluidBalance (workRate : ℝ) : NoetherBalance :=
  (isentropicFluid workRate).toNoetherBalance

/-- **Streamline conservation** (Babourova–Frolov Eq. 2.8): at equilibrium (no work), the isentropic
fluid's energy — the Noether charge — is conserved, via `conserved_of_zero_defect`. -/
lemma isentropicFluid_conserved {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (isentropicFluidBalance 0).Q t₂ = (isentropicFluidBalance 0).Q t₁ := by
  refine (isentropicFluidBalance 0).conserved_of_zero_defect ?_ h
  intro t; simp [isentropicFluidBalance, ThermodynamicWorldline.toNoetherBalance, isentropicFluid]


/-- **The geometric-force defect** of the canonical energy-momentum (Babourova–Frolov Eq. 2.1): the
sum of the Mathisson (spin), torsion, and Weyl (dilatonic) forces — the Eq. 3.2 decomposition. -/
noncomputable def geometricForceDefect (mathisson torsion weyl : ℝ) : ℝ := mathisson + torsion + weyl

/-- **The canonical energy-momentum as a `NoetherBalance`** (Eq. 2.1): the charge changes by the
integrated geometric-force defect `DΣ_σ = force`. -/
noncomputable def energyMomentumBalance (force Q₀ : ℝ) : NoetherBalance where
  Q := fun t => Q₀ - force * t
  defect := fun _ => force
  balance := by
    intro t₁ t₂ h
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring

/-- **Corollary 1 (Noether form)** — a free particle has zero geometric force: no spin
(`mathissonForce 0`), no dilatonic charge (`weylForce 0`), no torsion. -/
lemma corollary1_geometricForce_zero (C F : ℝ) :
    geometricForceDefect (mathissonForce 0 C) 0 (weylForce 0 F) = 0 := by
  simp [geometricForceDefect, mathissonForce, weylForce]

/-- **Corollary 1 — energy-momentum is conserved for a free particle**: zero geometric force means
zero Noether defect, hence a conserved charge (via `conserved_of_zero_defect`) — the Riemann geodesic
carries a conserved energy-momentum. -/
lemma corollary1_energyMomentum_conserved (Q₀ C F : ℝ) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (energyMomentumBalance (geometricForceDefect (mathissonForce 0 C) 0 (weylForce 0 F)) Q₀).Q t₂
      = (energyMomentumBalance (geometricForceDefect (mathissonForce 0 C) 0 (weylForce 0 F)) Q₀).Q t₁ := by
  refine (energyMomentumBalance (geometricForceDefect (mathissonForce 0 C) 0 (weylForce 0 F))
    Q₀).conserved_of_zero_defect ?_ h
  intro t; simp only [energyMomentumBalance, corollary1_geometricForce_zero]

/-- **Corollary 3 (Noether form)** — without dilatonic charge the Weyl part of the energy-momentum
defect vanishes: the Weyl structure contributes nothing to the quasiconservation of ordinary matter. -/
lemma energyMomentumDefect_no_weyl (mathisson torsion F : ℝ) :
    geometricForceDefect mathisson torsion (weylForce 0 F) = mathisson + torsion := by
  simp [geometricForceDefect, weylForce]

end Physlib.QuantumMechanics.ComplexAction.WeylCartanFluidNoether

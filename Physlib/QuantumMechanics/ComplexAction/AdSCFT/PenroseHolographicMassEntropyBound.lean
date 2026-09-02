/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
public import Physlib.Relativity.SemiClassical.RiemannianPenroseInequality

/-!
# The Penrose inequality is the geometric requirement on the Yukawa-free (horizon-entropy) mass

The Yukawa-free mass constructions source mass and decoherence from the **horizon entropy**
`S_I = (c³/4G) A_H` (`MassOrigin.GravitationalMassHorizonEntropyNoYukawa`) — i.e. from the holographic
information capacity of a region. What constrains that capacity? The **Riemannian Penrose inequality**
(`RiemannianPenroseInequality`, via the Schwarzschild–Verlinde bridge): `m ≥ √(A/16π)`, equivalently the
**area / information capacity is bounded by the mass**, `A ≤ 16π m²` (`area_bound_of_penrose_inequality`).

This file makes the geometric requirement explicit in geometric units (`c = G = 1`):

* `horizonImaginaryAction_le_penrose`: the holographic imaginary action (Bekenstein–Hawking entropy)
  satisfies `S_I = A/4 ≤ 4π m²` — the entropy/information stored is bounded by the mass². The mass-from-area
  mechanism is therefore *required* by Penrose: you cannot encode more horizon information than the mass
  permits.
* `horizonImaginaryAction_schwarzschild`: at the Schwarzschild horizon (`A = 16π m²`) equality holds,
  `S_I = 4π m²` — the black hole **saturates** the information bound for its mass (Penrose quotient `1`).
* `nnPathWeight_norm_ge_penrose`: the Nagao–Nielsen path-weight modulus is bounded *below* by
  `e^{−4π m²/ℏ}` — the gravitational damping cannot exceed the mass-bounded entropy.

So the "geometrized requirement" behind avoiding the Yukawa coupling is the Penrose inequality: mass is the
ceiling on holographic information capacity, the black hole saturates it, and the atomic registers
(`Particles.AtomicShellInformationCapacityOctet`, the octet's 8 bits) sit far below that gravitational bound.

## References

* R. Penrose (1973); G. Huisken, T. Ilmanen / H. Bray (Riemannian Penrose inequality). `Physlib`
  (`RiemannianPenroseInequality`, `MassOrigin.GravitationalMassHorizonEntropyNoYukawa`, `NonHermitianComplexAction.EntropicDampingEquivalence`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.Relativity.SemiClassical.RiemannianPenroseInequality

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.PenroseHolographicMassEntropyBound

/-- **[Penrose bounds the holographic entropy by the mass]** in geometric units (`c = G = 1`) the horizon
imaginary action `S_I = A/4` satisfies `S_I ≤ 4π m²` whenever the Penrose inequality `√(A/16π) ≤ m` holds.
The information capacity stored on the horizon is bounded by the mass² — the geometric requirement on the
mass-from-area construction. -/
lemma horizonImaginaryAction_le_penrose {m A : ℝ} (hA : 0 ≤ A)
    (hmass : blackHoleMassContribution A ≤ m) :
    horizonImaginaryAction 1 1 A ≤ 4 * Real.pi * m ^ 2 := by
  have harea := area_bound_of_penrose_inequality hA hmass
  have h : horizonImaginaryAction 1 1 A = A / 4 := by unfold horizonImaginaryAction; ring
  rw [h]; linarith

/-- **[Schwarzschild saturates the bound]** at the Schwarzschild horizon (`A = 16π m²`) the holographic
imaginary action equals `4π m²` — the black hole maximizes the information capacity for its mass (Penrose
quotient `= 1`). -/
lemma horizonImaginaryAction_schwarzschild (m : ℝ) :
    horizonImaginaryAction 1 1 (riemannianSchwarzschildHorizonArea m) = 4 * Real.pi * m ^ 2 := by
  unfold horizonImaginaryAction riemannianSchwarzschildHorizonArea
  ring

/-- **[The gravitational damping is mass-bounded below]** the Nagao–Nielsen path-weight modulus obeys
`e^{−4π m²/ℏ} ≤ ‖e^{iS/ℏ}‖`, since the horizon entropy that damps it is bounded by `4π m²` (Penrose). The
imaginary action cannot suppress the amplitude beyond the mass-set ceiling. -/
lemma nnPathWeight_norm_ge_penrose {S_R m A ℏ : ℝ} (hA : 0 ≤ A) (hℏ : 0 < ℏ)
    (hmass : blackHoleMassContribution A ≤ m) :
    Real.exp (-(4 * Real.pi * m ^ 2) / ℏ)
      ≤ ‖nnPathWeight S_R (horizonImaginaryAction 1 1 A) ℏ‖ := by
  rw [norm_nnPathWeight]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  exact neg_le_neg ((div_le_div_iff_of_pos_right hℏ).mpr (horizonImaginaryAction_le_penrose hA hmass))

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.PenroseHolographicMassEntropyBound

end

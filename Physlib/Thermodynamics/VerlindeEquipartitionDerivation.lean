/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.StatisticalMechanics.Equipartition
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Verlinde's equipartition hypothesis derived from N quadratic DOFs

Proves that **Verlinde's equipartition hypothesis**
`equipartitionEnergy N kB T = (1/2)·N·k_B·T` is NOT an axiom but a
**derived theorem** of physlib's existing canonical-ensemble
infrastructure when the `N` degrees of freedom are quadratic
(classical) DOFs.

## The derivation

Physlib already has the two pieces required:

* **Single-DOF equipartition**
  (`Physlib/StatisticalMechanics/Equipartition.lean` Eq. 393):

  `(QuadraticDOFEnsemble k hk).meanEnergy T = (1/2)·k_B·T`.

* **N-copy additivity of mean energy**
  (`Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean` Eq. 674):

  `(nsmul N 𝓒).meanEnergy T = N · 𝓒.meanEnergy T`.

Composing them gives:

  `(nsmul N (QuadraticDOFEnsemble k hk)).meanEnergy T
     = N · (1/2)·k_B·T
     = (1/2)·N·k_B·T
     = equipartitionEnergy N k_B T`.

This **identifies Verlinde's `equipartitionEnergy N kB T` with the
mean energy of `N` non-interacting classical quadratic DOFs** —
not a fresh axiom, but the mean energy of a specific ensemble in
the canonical thermodynamic framework.

## Honest scope

* The derivation holds for **classical quadratic DOFs**.  For
  Verlinde's *bits* (quantum two-level systems with energy gap
  `ε`), the classical equipartition `(1/2)·k_B·T` per DOF is the
  **high-temperature limit** `k_B·T ≫ ε`.  At low temperature
  the quantum two-level result `⟨E⟩ = ε/(1 + exp(βε))` differs
  from the classical `(1/2)·k_B·T`.
* So Verlinde's equipartition assumption *for bits* is not
  axiomatic when bits are treated in the classical (high-T) limit;
  in the low-T quantum regime, Verlinde's assumption acquires
  corrections.  This file makes the classical-limit derivation
  explicit; the quantum-regime corrections are a separable scope.

## Contents

* `nQuadraticDOFEnsemble N k hk` — `N` non-interacting quadratic
  degrees of freedom (via `nsmul N (QuadraticDOFEnsemble k hk)`).
* **`equipartition_N_quadraticDOF`** — the load-bearing theorem:
  the mean energy of `N` quadratic DOFs at temperature `T` is
  `(1/2)·N·k_B·T`.
* **`verlinde_equipartition_from_NDOF`** — bridge: this mean
  energy equals `equipartitionEnergy N kB T.val`.

## References

* Verlinde 2011 §2.2 — equipartition assumption (Eq. 9, line 331
  of `NewtonPaper.tex`).
* `Physlib/StatisticalMechanics/Equipartition.lean` — single-DOF
  equipartition theorem.
* `Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean` —
  `meanEnergy_nsmul` and N-copy additivity.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics

open MeasureTheory Constants
  Physlib.StatisticalMechanics
  Physlib.StatisticalMechanics.Equipartition


/-- **N non-interacting quadratic degrees of freedom** — the
canonical ensemble of `N` independent classical harmonic-like
degrees of freedom each with quadratic Hamiltonian `H = (1/2)·k·q²`.

Built as `nsmul N (QuadraticDOFEnsemble k hk)` using physlib's
existing `nsmul` infrastructure for non-interacting copies. -/
def nQuadraticDOFEnsemble (N : ℕ) (k : ℝ) (hk : 0 < k) :
    CanonicalEnsemble (Fin N → ℝ) :=
  CanonicalEnsemble.nsmul N (QuadraticDOFEnsemble k hk)


/-- **N-DOF equipartition theorem**: the mean energy of `N`
non-interacting quadratic degrees of freedom at temperature `T` is
`(1/2)·N·k_B·T`.

Direct composition of:
* `Equipartition.equipartition_quadraticDOF` (single DOF, `(1/2)·k_B·T`),
* `CanonicalEnsemble.meanEnergy_nsmul` (N copies multiply by N).

This is the **statistical-mechanics derivation** of Verlinde's
equipartition formula (Verlinde 2011 Eq. 9, line 331 of
`NewtonPaper.tex`). -/
lemma equipartition_N_quadraticDOF
    (N : ℕ) (k : ℝ) (hk : 0 < k)
    (T : Temperature) (hT_pos : 0 < T.val)
    [MeasureTheory.IsFiniteMeasure ((QuadraticDOFEnsemble k hk).μBolt T)]
    [NeZero (QuadraticDOFEnsemble k hk).μ]
    (h_integrable :
      Integrable (QuadraticDOFEnsemble k hk).energy
        ((QuadraticDOFEnsemble k hk).μProd T)) :
    (nQuadraticDOFEnsemble N k hk).meanEnergy T =
      (1 / 2) * (N : ℝ) * kB * T.val := by
  unfold nQuadraticDOFEnsemble
  rw [(QuadraticDOFEnsemble k hk).meanEnergy_nsmul N T h_integrable]
  rw [equipartition_quadraticDOF k hk T hT_pos]
  ring


/-- **Bridge from `equipartition_N_quadraticDOF` to Verlinde's
`equipartitionEnergy`**:

  `equipartitionEnergy N k_B T = (nQuadraticDOFEnsemble N k hk).meanEnergy T`.

This identifies Verlinde's `equipartitionEnergy` (an algebraic
expression `(1/2)·N·k_B·T` defined in `VerlindeNewtonGravity.lean`)
with the **mean energy in the canonical ensemble** of `N`
quadratic degrees of freedom.

**Verlinde's equipartition hypothesis is therefore a theorem in
the classical quadratic-DOF limit**: it does not require axiomatic
postulation; it follows from the canonical-ensemble framework
plus N-DOF additivity. -/
lemma verlinde_equipartition_from_NDOF
    (N : ℕ) (k : ℝ) (hk : 0 < k)
    (T : Temperature) (hT_pos : 0 < T.val)
    [MeasureTheory.IsFiniteMeasure ((QuadraticDOFEnsemble k hk).μBolt T)]
    [NeZero (QuadraticDOFEnsemble k hk).μ]
    (h_integrable :
      Integrable (QuadraticDOFEnsemble k hk).energy
        ((QuadraticDOFEnsemble k hk).μProd T)) :
    equipartitionEnergy (N : ℝ) kB T.val =
      (nQuadraticDOFEnsemble N k hk).meanEnergy T := by
  rw [equipartition_N_quadraticDOF N k hk T hT_pos h_integrable]
  unfold equipartitionEnergy
  ring

end Physlib.Thermodynamics

end

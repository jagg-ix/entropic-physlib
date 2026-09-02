/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-!
# The Yukawa entropic screening mass is a Bogoliubov quasiparticle energy

Links the Yukawa entropic mass (`Yukawa.ScreenedPotential`, `M_eff = √(m² + λ)`) to the **Bogoliubov /
BCS quasiparticle energy** (`Bogoliubov.Transformation`, `E = √(ξ² + Δ²)`). The two share the same
`√(·² + ·²)` structure, and the identification is exact:

  `M_eff = √(m² + λ) = bogoliubovEnergy m √λ`   (`entropicMass_eq_bogoliubovEnergy`),

so the **Yukawa screening mass is a Bogoliubov quasiparticle energy** with the bare mass `m` as the normal
energy `ξ` and the **entropic action `√λ` as the BCS pairing gap `Δ`**. The imaginary/entropic action `λ`
opens a gap exactly as a BCS pairing gap opens the quasiparticle dispersion: `λ = Δ²` is the screening
mass-squared.

Consequently the entropic-screened Yukawa potential's defining ODE carries the Bogoliubov energy as its
screening mass: the reduced potential `v = e^{−M_eff r}` solves `v'' = (m² + λ) v` with
`m² + λ = bogoliubovEnergy(m, √λ)²` (`yukawa_bogoliubov_screening`), and the Bogoliubov coherence factors
`u² + v² = 1` (`bogoliubov_normalization`) give the screening admixture
(`yukawa_bogoliubov_pairing`). At `λ = 0` (no entropic action, `Δ = 0`) the gap closes — the unscreened,
normal-state limit.

So the Yukawa screening of the complex-action/entropic-time entropic action is a BCS-like pairing: `λ` is the gap squared,
`M_eff` the quasiparticle energy, tying the screened potential to the Bogoliubov / Schmidt-rapidity arc.

* **§A — the entropic mass is a Bogoliubov energy** (`entropicMass_eq_bogoliubovEnergy`).
* **§B — the screened Helmholtz carries the Bogoliubov energy** (`yukawa_bogoliubov_screening`,
  `yukawa_bogoliubov_pairing`).

## References

* The Yukawa potential and the BCS/Bogoliubov gap dispersion `E = √(ξ² + Δ²)` (standard). Carriers:
  `Yukawa.ScreenedPotential` (`entropicMass`, `reducedYukawa`, `yukawa_entropic_screening`),
  `Bogoliubov.Transformation` (`bogoliubovEnergy`, `bogoliubovU2`, `bogoliubovV2`, `bogoliubov_normalization`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreeningBogoliubov

open Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation


/-- **[The Yukawa entropic mass is a Bogoliubov quasiparticle energy] `M_eff = bogoliubovEnergy m √λ`.**
The screening mass `√(m² + λ)` is the BCS/Bogoliubov quasiparticle energy `√(ξ² + Δ²)` with the bare mass
`m` as the normal energy `ξ` and the entropic action `√λ` as the pairing gap `Δ`. The entropic action `λ`
is the gap squared. -/
lemma entropicMass_eq_bogoliubovEnergy (m lam : ℝ) (hlam : 0 ≤ lam) :
    entropicMass m lam = bogoliubovEnergy m (Real.sqrt lam) := by
  rw [entropicMass, bogoliubovEnergy, Real.sq_sqrt hlam]


/-- **[The screened Helmholtz equation carries the Bogoliubov energy] `v'' = (m² + λ) v`,
`m² + λ = bogoliubovEnergy(m, √λ)²`.** The entropic-screened Yukawa potential with the Bogoliubov
quasiparticle mass solves the screened Helmholtz equation with screening mass-squared the Bogoliubov energy
squared `bogoliubovEnergy(m, √λ)² = m² + λ`. -/
lemma yukawa_bogoliubov_screening (m lam r : ℝ) (hlam : 0 ≤ lam) :
    deriv (deriv (reducedYukawa (bogoliubovEnergy m (Real.sqrt lam)))) r
      = (m ^ 2 + lam) * reducedYukawa (bogoliubovEnergy m (Real.sqrt lam)) r := by
  rw [← entropicMass_eq_bogoliubovEnergy m lam hlam]
  exact yukawa_entropic_screening m lam r (add_nonneg (sq_nonneg m) hlam)

/-- **[The Yukawa entropic screening is BCS-like Bogoliubov pairing, assembled].** For the entropic action
`λ ≥ 0`:

* the screening mass is the Bogoliubov quasiparticle energy, `M_eff = bogoliubovEnergy m √λ` (the entropic
  action `√λ` is the pairing gap);
* the screened Yukawa potential solves `v'' = (m² + λ) v` with `m² + λ` the Bogoliubov energy squared;
* the Bogoliubov coherence factors normalise, `u² + v² = 1` (the screening admixture).

The Yukawa screening of the complex-action/entropic-time entropic action is a BCS-like pairing: `λ` is the gap squared, `M_eff`
the quasiparticle energy. -/
lemma yukawa_bogoliubov_pairing (m lam r : ℝ) (hlam : 0 ≤ lam) :
    entropicMass m lam = bogoliubovEnergy m (Real.sqrt lam)
      ∧ deriv (deriv (reducedYukawa (bogoliubovEnergy m (Real.sqrt lam)))) r
          = (m ^ 2 + lam) * reducedYukawa (bogoliubovEnergy m (Real.sqrt lam)) r
      ∧ bogoliubovU2 m (Real.sqrt lam) + bogoliubovV2 m (Real.sqrt lam) = 1 :=
  ⟨entropicMass_eq_bogoliubovEnergy m lam hlam, yukawa_bogoliubov_screening m lam r hlam,
    bogoliubov_normalization m (Real.sqrt lam)⟩

end Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreeningBogoliubov

end

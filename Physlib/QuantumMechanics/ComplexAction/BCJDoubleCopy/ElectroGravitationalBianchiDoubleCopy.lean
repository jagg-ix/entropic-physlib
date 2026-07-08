/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy

/-!
# The electrogravitic Bianchi structure: both EM Bianchi identities double-copy to gravity

Links the EM first/second Bianchi double copy (`Electromagnetic.EMSecondBianchiDoubleCopy`) to the complete
electrogravitic field equations (`ComplexEinstein.ElectroGravitationalFieldEquations`). The electrogravitic system's
**electromagnetic sector** records both Bianchi-type identities, and they are the gauge side of the double
copy whose gravity dual is the system's **gravitational sector**:

* the **EM first Bianchi** — `dF = 0` (`k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0`,
  `ElectroGravitationalFieldEquation.maxwellBianchi`) ↔ the gravity **first Bianchi** (Riemann cyclic);
* the **EM second Bianchi** — current conservation `∂_ν J^ν = 0` (`em_second_bianchi`) ↔ the gravity
  **second Bianchi**, the stress-energy conservation `∇^μ T_{μν} = 0` validated by the §7 Bianchi theorem.

Together with the electrogravitic **Einstein–Maxwell** real sector `G = κT`
(`ElectroGravitationalFieldEquation.einsteinMaxwell`), the electrogravitic field equations have a complete
double-copied Bianchi structure: gauge `(dF = 0, ∂J = 0)` ↔ gravity `(Riemann cyclic, ∇T = 0)`.

* **§A — the Bianchi double copy: gauge `dF = 0` derives gravity `∇^μ T = 0`**
  (`electrogravitational_bianchi_double_copy`).

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson (arXiv:0805.3993); T. Levi-Civita (arXiv:physics/9906004, §7).
  structures: `ComplexEinstein.ElectroGravitationalFieldEquations` (`ElectroGravitationalFieldEquation`, `maxwellBianchi`,
  `einsteinMaxwell`), `Electromagnetic.EMSecondBianchiDoubleCopy` (`em_second_bianchi`),
  `LeviCivita.BianchiDoubleCopy` (`eq12_discharges_bcj`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy

open scoped BigOperators

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

variable {ι : Type*} {Ric : Matrix ι ι ℝ} {scalarR : ℝ} {g Λ T S : Matrix ι ι ℝ}
  {κ m_R m_I c S₁ S₂ : ℝ} {k A : Fin 4 → ℝ}

/-! ## §A — the Bianchi double copy: gauge `dF = 0` derives gravity `∇^μ T = 0` -/

/-- **[The electrogravitic Bianchi double copy] gauge `dF = 0` ⟹ gravity `∇^μ T_{μν} = 0`.** The two
Bianchi contracts of the double copy for an electrogravitic solution:

* **gauge side** — the Maxwell cyclic identity `dF = 0` (`k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0`, the
  BCJ kinematic Jacobi) and current conservation `∂_ν J^ν = 0`;
* **gravity side, derived** — when the gravity second Bianchi holds (`∇^μ G_{μν} = 0`) and is
  Einstein-contracted to the EM stress-energy divergence (`∇^μ G = κ ∇^μ T`), stress-energy conservation
  `∇^μ T_{μν} = 0` *follows* (`ElectroGravitationalFieldEquation.stressEnergyConservation`).

The gravity conservation is not conjoined but derived from its Bianchi identity, dual to the gauge `dF = 0`. -/
theorem electrogravitational_bianchi_double_copy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (lam μ ν : Fin 4) (divG divT : Fin 4 → ℝ)
    (hEinstein : divG = κ • divT) (hSecondBianchi : divG = 0) :
    (k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0)
      ∧ (∑ i, k i * fourCurrent k A i = 0)
      ∧ divT = 0 :=
  ⟨H.maxwellBianchi lam μ ν, em_second_bianchi k A,
    H.stressEnergyConservation divG divT hEinstein hSecondBianchi⟩

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy

end

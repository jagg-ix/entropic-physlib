/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenComplexChernSimonsQuantization

/-!
# Bridges from the Witten complex Chern–Simons formalization to the rest of the repo

Connects the Witten 1991 coupling/reality/branch content
(`ChernSimons.WittenComplexChernSimonsQuantization`) to existing Physlib carriers, so the complex Chern–Simons
formalization is not an island.

* **§A — level quantization ↔ DJT topological mass.** Witten's integer level `k = (t + t̄)/2`
  (`level_eq_half_coupling_sum`) is exactly the Chern–Simons level of the Deser–Jackiw–Templeton
  topological-mass carrier (`wittenCouplingHalfSum_eq_djtLevel`); a **nonzero** level is exactly a
  **massive** gauge boson — the DJT topological mass vanishes iff the Witten level is zero
  (`wittenLevel_zero_iff_topologicalMass_zero`).
* **§B — the `SL(2,ℂ)` gauge group ↔ the double cover of the Lorentz group.** Witten's `SL(2,ℂ)` gauge group
  of 2+1 gravity (§2.1) is realized by the repo's rapidity-parametrized spinor element `bogoSL2C`; under the
  standard double cover `SL2C.toLorentzGroup` it maps to a Lorentz boost whose time component is the
  Bogoliubov energy at doubled rapidity (`witten_sl2c_gauge_doubleCover`).

## References

* E. Witten (1991), *Quantization of Chern–Simons Gauge Theory with Complex Gauge Group*, Commun. Math.
  Phys. 137, 29–66, §2–§2.1. Carriers: `Physlib` (`ChernSimons.TopologicalMassDJT`, `Hopf.SL2CDoubleCover`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
open Physlib.QuantumMechanics.ComplexAction.Hopf.SL2CDoubleCover
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open _root_.Lorentz


/-- **[Witten level = DJT Chern–Simons level].** The half-sum of Witten's couplings `(t + t̄)/2` is exactly
the integer Chern–Simons level fed to the Deser–Jackiw–Templeton topological-mass carrier. -/
lemma wittenCouplingHalfSum_eq_djtLevel (c : HayashiCouplings) (e : ℝ) :
    (holomorphicCoupling c + antiholomorphicCoupling c) / 2 = ((toDJTData c e).level : ℂ) := by
  rw [level_eq_half_coupling_sum, toDJTData_level]

/-- **[Nonzero Witten level ⟺ massive gauge boson].** At nonzero `U(1)` coupling, the DJT topological mass
vanishes exactly when the Witten Chern–Simons level is zero — so the integer level is precisely what makes
the gauge boson massive. -/
lemma wittenLevel_zero_iff_topologicalMass_zero (c : HayashiCouplings) (e : ℝ) (he : e ≠ 0) :
    topologicalMass (toDJTData c e) = 0 ↔ c.level = 0 := by
  have he' : (toDJTData c e).e ≠ 0 := he
  rw [topologicalMass_eq_zero_iff_level_zero he', toDJTData_level]


/-- **The `SL(2,ℂ)` gauge group element of Witten's 2+1 gravity** (§2.1), realized as the repo's
rapidity-parametrized spinor boost `bogoSL2C η`. -/
noncomputable def wittenSL2CGaugeElement (η : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  bogoSL2C η

/-- **[Witten `SL(2,ℂ)` gauge group double-covers the Lorentz group, §2.1].** Under the standard spinor
double cover `SL2C.toLorentzGroup`, the Witten `SL(2,ℂ)` gauge element maps to a Lorentz boost whose
time–time component is the Bogoliubov energy at the doubled rapidity `2η`. -/
lemma witten_sl2c_gauge_doubleCover (η : ℝ) :
    (SL2C.toLorentzGroup (wittenSL2CGaugeElement η)).1 (Sum.inl 0) (Sum.inl 0)
      = bogoliubovEnergy (Real.sinh (2 * η)) 1 :=
  bogoSL2C_doubleCover_rapidity η

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end

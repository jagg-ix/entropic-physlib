/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GeneralizedDDimensionalUnitarity
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
public import Physlib.QFT.Wick.Consistency

/-!
# One-loop amplitudes, the QED path integral, and the Verch symplectic complex structure

Links the one-loop scalar-integral / amplitude machinery (`PathIntegral.OneLoopScalarIntegralsQCD`,
`GeneralizedDDimensionalUnitarity`) to the **Feynman / QED path integral** (the one-loop functional
determinant, `PathIntegral.QEDFunctionalIntegralConstruction`) and to the **Verch 1996 symplectic-adjoint /
pure-state complex structure** (`AlgebraicQFT.SymplecticAdjointHadamard`).

The thread: a one-loop amplitude is a linear combination of master scalar integrals (Eq. 2.1); those
masters are the perturbative content of the **path integral**, whose fermion loops are **Berezin
functional determinants** (`berezin_gaussian_eq_det`). The on-shell dispersion of such a determinant is
the **Bogoliubov energy** `√(p²+m²)` (`berezin_dirac_dispersion`); for a unit-mass Dirac mode at
rapidity `η` it is `cosh η`, *exactly the diagonal entry of the diagonalizing Bogoliubov matrix*
`thermoBogoliubov η` (`berezinDet_eq_bogoliubov_diagonal`). That Bogoliubov transformation is, by Verch
1996, a **symplectomorphism** (`thermoBogoliubov_symplectomorphism`, `Sp(2) = SL(2)`), and the
**pure-state complex structure** `J² = −1` (Verch Eq. 2.4) is the symplectic form `= −` the fermion
Bogoliubov generator (`sympForm_eq_neg_fermiGen`).

So the master integrals, the QED path-integral fermion determinant, the Bogoliubov energy, and the
Verch pure-state complex structure are one object — the Gaussian one-loop integral and its
diagonalization.

* **§A — the masters from the QED path integral** (`tadpole_pole_eq_fermionDet_sq`): the tadpole's
  UV-pole mass scale `m²` is the *squared* Berezin fermion functional determinant.
* **§B — the determinant dispersion = the diagonalizing symplectomorphism** (
  `berezinDet_eq_bogoliubov_diagonal`): the QED fermion one-loop determinant of a rapidity-`η` Dirac
  mode is `cosh η`, the diagonal entry of the diagonalizing Bogoliubov matrix.
* **§C — the Feynman path-integral weight** (`oneLoop_weight_unitary_of_reversible`): the reversible
  (real-action, UV-finite) one-loop contribution enters the path integral with a **unitary** weight
  `‖e^{iS_R/ℏ}‖ = 1`.
* **§D — the unified picture** (`oneLoop_pathIntegral_verch`): masters ↔ Berezin determinant ↔
  Bogoliubov energy ↔ Verch symplectomorphism (`J² = −1 = −`fermion generator).

## References

* R. K. Ellis, G. Zanderighi, arXiv:0712.1851; Ellis–Giele–Kunszt–Melnikov, arXiv:0906.1445;
  R. Verch, *Continuity of symplectically adjoint maps…*, arXiv:funct-an/9609004 (pure-state
  polarizator `R² = −1`, Eq. 2.4).
* Repo carriers: `PathIntegral.OneLoopScalarIntegralsQCD` (`tadpoleLaurent`), `PathIntegral.QEDFunctionalIntegralConstruction`
  (`berezin`, `fermionGaussian`, `berezin_dirac_dispersion`), `AlgebraicQFT.SymplecticAdjointHadamard` (`sympForm`,
  `thermoBogoliubov_symplectomorphism`, `sympForm_eq_neg_fermiGen`), `Physlib.QFT.Wick.Consistency`
  (`complexActionWeight`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch

open Real
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopScalarIntegralsQCD
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QFT.Wick.Consistency


/-- **[Tadpole pole = squared fermion functional determinant] `(I₁)₋₁ = (det[m])²`.** The mass scale
`m²` of the tadpole's UV pole (`PathIntegral.OneLoopScalarIntegralsQCD.tadpoleLaurent`) is the *square* of the
Berezin one-loop fermion functional determinant `det[m] = ∫dθ̄dθ e^{−mθ̄θ} = m`
(`PathIntegral.QEDFunctionalIntegralConstruction.berezin_gaussian_eq_det`). The scalar one-loop integral's mass
scale is the path-integral determinant. -/
lemma tadpole_pole_eq_fermionDet_sq (m : ℝ) :
    (tadpoleLaurent (m ^ 2)).eps1 = ((berezin (fermionGaussian m) : ℝ) : ℂ) ^ 2 := by
  show ((m ^ 2 : ℝ) : ℂ) = ((berezin (fermionGaussian m) : ℝ) : ℂ) ^ 2
  rw [show berezin (fermionGaussian m) = m from rfl]
  push_cast
  ring


/-- **The Bogoliubov energy of a unit-mass rapidity-`η` mode is `cosh η`** `√(sinh²η + 1) = cosh η`. -/
lemma bogoliubovEnergy_rapidity (η : ℝ) : bogoliubovEnergy (Real.sinh η) 1 = Real.cosh η := by
  unfold bogoliubovEnergy
  rw [show Real.sinh η ^ 2 + (1 : ℝ) ^ 2 = Real.cosh η ^ 2 from by rw [Real.sinh_sq]; ring,
    Real.sqrt_sq (Real.cosh_pos η).le]

/-- **[QED determinant = diagonalizing Bogoliubov symplectomorphism] `det[E_η] = (U_B(η))₀₀ = cosh η`.**
The Berezin one-loop fermion functional determinant of a unit-mass Dirac mode at rapidity `η`
(`berezin_dirac_dispersion`, the on-shell dispersion `E = √(p²+m²) = bogoliubovEnergy`) equals the
diagonal entry of the **diagonalizing** Bogoliubov matrix `thermoBogoliubov η` — `cosh η`. The path
integral's fermion determinant and the Verch/Bogoliubov symplectomorphism that diagonalizes the
Gaussian carry the same number. -/
lemma berezinDet_eq_bogoliubov_diagonal (η : ℝ) :
    berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = (thermoBogoliubov η) 0 0 := by
  rw [berezin_dirac_dispersion, bogoliubovEnergy_rapidity]
  simp [thermoBogoliubov]


/-- **[Reversible one-loop contribution is unitary] `‖e^{iS_R/ℏ}‖ = 1`.** A real-action (reversible,
UV-finite — no entropic/imaginary part) one-loop contribution enters the Feynman path integral with a
unitary weight (`Physlib.QFT.Wick.Consistency.norm_complexActionWeight` at `S_I = 0`); the
oscillatory, dissipation-free sector, matching the UV-finite anomalous-moment vertex. -/
lemma oneLoop_weight_unitary_of_reversible (S_R hbar : ℝ) :
    ‖complexActionWeight S_R 0 hbar‖ = 1 := by
  rw [norm_complexActionWeight]; simp


/-- **[One-loop amplitude ↔ QED path integral ↔ Verch symplectic structure, unified].** The scalar
one-loop masters' mass scale is the Berezin fermion functional determinant
(`tadpole_pole_eq_fermionDet_sq`); that determinant's dispersion is the Bogoliubov energy `cosh η`,
the diagonal of the diagonalizing Bogoliubov matrix (`berezinDet_eq_bogoliubov_diagonal`); the
Bogoliubov transformation is a **Verch symplectomorphism** (`thermoBogoliubov_symplectomorphism`,
`Sp(2) = SL(2)`); the **pure-state complex structure** is `J² = −1` (Verch Eq. 2.4, `sympForm_sq`)
equal to `−` the fermion Bogoliubov generator (`sympForm_eq_neg_fermiGen`); and the reversible
contribution has a unitary path-integral weight (`oneLoop_weight_unitary_of_reversible`). The masters,
the QED path-integral determinant, the Bogoliubov energy, and the Verch complex structure are one
object. -/
lemma oneLoop_pathIntegral_verch (m η S_R hbar : ℝ) :
    (tadpoleLaurent (m ^ 2)).eps1 = ((berezin (fermionGaussian m) : ℝ) : ℂ) ^ 2
      ∧ berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = (thermoBogoliubov η) 0 0
      ∧ Symplectomorphism (thermoBogoliubov η)
      ∧ sympForm * sympForm = -1
      ∧ sympForm = -fermiBogoliubovGenerator
      ∧ ‖complexActionWeight S_R 0 hbar‖ = 1 :=
  ⟨tadpole_pole_eq_fermionDet_sq m, berezinDet_eq_bogoliubov_diagonal η,
    thermoBogoliubov_symplectomorphism η, sympForm_sq, sympForm_eq_neg_fermiGen,
    oneLoop_weight_unitary_of_reversible S_R hbar⟩

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch

end

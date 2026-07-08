/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
public import Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-!
# The combined superoperator, the complex Einstein equation, and the complex Dirac mass

Links the combined Lorentz–electromagnetic superoperator (`Electromagnetic.EMLorentzCombinedSuperoperator`,
`covariantLiouvillian = −i[H + F, ·]`) to the **complex Einstein field equation**
`G_μν + iΛ_μν = κ(T_R + iT_I)` and the **complex Dirac terms** `H_C = H_R − iH_I` (the complex mass
`m = m_R + i m_I`). The bridge is one algebraic fact: the Liouvillian of a *complex* Hamiltonian splits into
a **reversible** unitary part and an **entropic** part, and that entropic part is the imaginary Dirac mass /
the imaginary Einstein term `Λ`.

For `H = H_R − iH_I`,

  `𝓛_H = −i[H_R, ·] − [H_I, ·]`,

the first term reversible (unitary, the real energy `H_R`/`T_R`/`G`), the second a real-coefficient
commutator — the **dissipative/entropic** flow encoded in `H_I` (the imaginary mass `m_I`, the imaginary
Einstein `Λ`/`T_I`). When `H_I = 0` (real mass) the evolution is purely reversible — and the Einstein
energy is real.

* **§A — the complex-Hamiltonian Liouvillian splits** (`heisenbergGenerator_complex_decompose`). Generic on
  any `*`-algebra: `𝓛_{H_R − iH_I} = −i[H_R, ·] − [H_I, ·]`.
* **§B — the combined EM superoperator inherits the split** (`covariantLiouvillian_complex_decompose`). For
  a complex generator the combined `𝓛_{(H_R − iH_I) + F}` splits into the reversible `−i[H_R + F, ·]` (EM +
  real energy) and the entropic `−[H_I, ·]`.
* **§C — the complex Dirac instance** (`dirac_liouvillian_complex_decompose`,
  `dirac_liouvillian_reversible`). The Liouvillian of `H_C = H_R − iH_I`
  (`Dirac.StressEnergyComplexHamiltonian.complexDiracHamiltonian`) splits; the entropic part is the imaginary
  Dirac mass `H_I = diracHamiltonian Δ_I 0`, vanishing at `Δ_I = 0` (real mass, reversible Dirac).
* **§D — the imaginary Einstein source** (`dirac_entropic_gap_eq_imaginary_einstein`,
  `reversible_no_entropic`). The entropic gap `Δ_I = m_I c²` is exactly the imaginary part of the complex
  Einstein energy `E = mc² = (m_R + i m_I)c²` (`ComplexEinstein.ComplexMassEinsteinEquations.complexEinsteinEnergy`) — the
  imaginary Einstein term `Λ`. At `m_I = 0` it vanishes: reversible ⟺ real Einstein ⟺ real Dirac.

## References

* The complex Einstein field equation `G_μν + iΛ_μν = κ(T_R + iT_I)`; the Nagao–Nielsen / complex-action complex
  Hamiltonian `H_C = H_R − iH_I` and complex mass `m = m_R + i m_I`.
* Repo dependencies: `Electromagnetic.EMLorentzCombinedSuperoperator` (`covariantLiouvillian`);
  `PTSymmetricQFT.LindbladSuperoperator` (`heisenbergGenerator`);
  `Dirac.StressEnergyComplexHamiltonian` (`complexDiracHamiltonian`, `complexDiracHamiltonian_reversible`);
  `ComplexEinstein.ComplexMassEinsteinEquations` (`complexEinsteinEnergy`, `complexEinsteinEnergy_im`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-! ## §A — the complex-Hamiltonian Liouvillian splits into reversible + entropic -/

/-- **[Reversible + entropic] `𝓛_{H_R − iH_I} = −i[H_R, ·] − [H_I, ·]`.** The Liouvillian of a complex
Hamiltonian on any `*`-algebra splits into the reversible unitary flow `−i[H_R, ·]` and the entropic /
dissipative real-coefficient commutator `−[H_I, ·]`. -/
theorem heisenbergGenerator_complex_decompose (H_R H_I Y : A) :
    heisenbergGenerator (H_R - Complex.I • H_I) Y
      = -Complex.I • (H_R * Y - Y * H_R) - (H_I * Y - Y * H_I) := by
  rw [heisenbergGenerator_apply]
  have hc : (H_R - Complex.I • H_I) * Y - Y * (H_R - Complex.I • H_I)
      = (H_R * Y - Y * H_R) - Complex.I • (H_I * Y - Y * H_I) := by
    rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]; abel
  rw [hc, smul_sub, smul_smul,
    show -Complex.I * Complex.I = (1 : ℂ) by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]

/-! ## §B — the combined EM superoperator inherits the split -/

/-- **[Combined superoperator split] `𝓛_{(H_R − iH_I) + F} = −i[H_R + F, ·] − [H_I, ·]`.** The combined
Lorentz–EM Liouvillian (`covariantLiouvillian`) with a complex (Dirac-mass) generator splits into the
reversible part — the electromagnetic field `F` together with the real energy `H_R` — and the entropic part
`−[H_I, ·]`, the imaginary mass / imaginary Einstein `Λ`. -/
theorem covariantLiouvillian_complex_decompose
    (H_R H_I F Y : Matrix (Fin 4) (Fin 4) ℂ) :
    covariantLiouvillian (H_R - Complex.I • H_I) F Y
      = -Complex.I • ((H_R + F) * Y - Y * (H_R + F)) - (H_I * Y - Y * H_I) := by
  rw [covariantLiouvillian, emLiouvillian,
    show (H_R - Complex.I • H_I) + F = (H_R + F) - Complex.I • H_I by abel]
  exact heisenbergGenerator_complex_decompose (H_R + F) H_I Y

/-! ## §C — the complex Dirac instance -/

/-- **[Complex Dirac] The Liouvillian of `H_C = H_R − iH_I` splits.** With `H_R = diracHamiltonian Δ_R vp`
and the entropic part the **imaginary Dirac mass** `H_I = diracHamiltonian Δ_I 0`
(`Dirac.StressEnergyComplexHamiltonian`). -/
theorem dirac_liouvillian_complex_decompose (Δ_R Δ_I vp : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    heisenbergGenerator (complexDiracHamiltonian Δ_R Δ_I vp) Y
      = -Complex.I • (((diracHamiltonian Δ_R vp).map Complex.ofReal) * Y
                       - Y * ((diracHamiltonian Δ_R vp).map Complex.ofReal))
        - (((diracHamiltonian Δ_I 0).map Complex.ofReal) * Y
            - Y * ((diracHamiltonian Δ_I 0).map Complex.ofReal)) := by
  rw [complexDiracHamiltonian_eq_HR_sub_I_HI]
  exact heisenbergGenerator_complex_decompose _ _ Y

/-- **[Reversible Dirac] At `Δ_I = 0` the Dirac Liouvillian is purely reversible** — the complex Dirac
Hamiltonian reduces to the real one (`complexDiracHamiltonian_reversible`), so there is no entropic part. -/
theorem dirac_liouvillian_reversible (Δ_R vp : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    heisenbergGenerator (complexDiracHamiltonian Δ_R 0 vp) Y
      = heisenbergGenerator ((diracHamiltonian Δ_R vp).map Complex.ofReal) Y := by
  rw [complexDiracHamiltonian_reversible]

/-! ## §D — the entropic gap is the imaginary Einstein energy -/

/-- **[Entropic source = imaginary Einstein] `Δ_I = m_I c² = Im(E)`.** The entropic gap that sources the
dissipative part of the combined superoperator is exactly the imaginary part of the complex Einstein energy
`E = mc² = (m_R + i m_I)c²` — the imaginary Einstein term `Λ` / `T_I`. -/
theorem dirac_entropic_gap_eq_imaginary_einstein (m_R m_I c : ℝ) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im :=
  (complexEinsteinEnergy_im m_R m_I c).symm

/-- **[Reversible ⟺ real Einstein] At `m_I = 0` the imaginary Einstein energy vanishes** — no entropic
source, matching the reversible Dirac Liouvillian of `dirac_liouvillian_reversible`. -/
theorem reversible_no_entropic (m_R c : ℝ) :
    (complexEinsteinEnergy m_R 0 c).im = 0 := by
  rw [complexEinsteinEnergy_im]; ring

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac

end

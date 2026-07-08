/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

/-!
# The electrogravitic superoperator

Constructs the **superoperator (Liouvillian) of the electrogravitic field equations**
(`ComplexEinstein.ElectroGravitationalFieldEquations`). It is the combined Lorentz–electromagnetic Liouvillian
(`Electromagnetic.EMSuperoperatorComplexEinsteinDirac`, `covariantLiouvillian`) of the **complex electrogravitic
Hamiltonian** `H_C = H_R − iH_I` with the electromagnetic field `F`:

  `𝓛^{EG}_{H_R, H_I, F} = covariantLiouvillian (H_R − iH_I) F`   (`electroGravitationalLiouvillian`),

which splits into a reversible and an entropic part exactly along the electrogravitic sectors:

  `𝓛^{EG} = −i[H_R + F, ·] − [H_I, ·]`   (`electroGravitationalLiouvillian_decompose`):

* the **reversible part** `−i[H_R + F, ·]` is the electromagnetic field `F` together with the real
  gravitational/matter energy `H_R` — the **Einstein–Maxwell** sector (`G = κT`), unitary;
* the **entropic part** `−[H_I, ·]` is the imaginary Einstein Hamiltonian `H_I` — the entropic source `S`
  (`Λ = κS`), whose gap is `m_I c² = Im E` (`electroGravitational_entropic_gap`).

At `H_I = 0` (no entropic source) the superoperator is purely reversible Einstein–Maxwell
(`electroGravitationalLiouvillian_reversible`). On an electrogravitic solution
(`ElectroGravitationalFieldEquation`) the entropic gap is the system's imaginary Einstein source, and that
source factorizes as the **BCJ double copy** `exp(−Im E) = exp(−S₁)·exp(−S₂)`
(`electroGravitational_superoperator_entropic_double_copy`).

So the electrogravitic superoperator is the unitary Einstein–Maxwell flow (EM + real gravity) plus the
entropic imaginary-Einstein flow, the entropic source encoded in the gauge double copy.

* **§A — the electrogravitic Liouvillian and its reversible/entropic split**
  (`electroGravitationalLiouvillian`, `electroGravitationalLiouvillian_decompose`,
  `electroGravitationalLiouvillian_reversible`).
* **§B — the entropic gap and its double copy** (`electroGravitational_entropic_gap`,
  `electroGravitational_superoperator_entropic_double_copy`).

## References

* complex-action/entropic-time complex Hamiltonian `H_C = H_R − iH_I`; the complex Einstein–Maxwell coupling. structures:
  `Electromagnetic.EMSuperoperatorComplexEinsteinDirac` (`covariantLiouvillian_complex_decompose`,
  `dirac_entropic_gap_eq_imaginary_einstein`), `Electromagnetic.EMLorentzCombinedSuperoperator` (`covariantLiouvillian`),
  `ComplexEinstein.ElectroGravitationalFieldEquations` (`ElectroGravitationalFieldEquation`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalSuperoperator

open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

/-! ## §A — the electrogravitic Liouvillian and its reversible/entropic split -/

/-- **The electrogravitic superoperator** `𝓛^{EG} = covariantLiouvillian (H_R − iH_I) F` — the combined
Lorentz–electromagnetic Liouvillian of the complex electrogravitic Hamiltonian `H_C = H_R − iH_I` (real
gravity/matter energy `H_R`, entropic imaginary-Einstein `H_I`) with the electromagnetic field `F`. -/
noncomputable def electroGravitationalLiouvillian
    (H_R H_I F Y : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  covariantLiouvillian (H_R - Complex.I • H_I) F Y

/-- **[The electrogravitic superoperator splits] `𝓛^{EG} = −i[H_R + F, ·] − [H_I, ·]`.** The reversible part
`−i[H_R + F, ·]` is the electromagnetic field `F` with the real gravitational energy `H_R` (the
Einstein–Maxwell sector); the entropic part `−[H_I, ·]` is the imaginary Einstein Hamiltonian (the entropic
source `S`). -/
theorem electroGravitationalLiouvillian_decompose (H_R H_I F Y : Matrix (Fin 4) (Fin 4) ℂ) :
    electroGravitationalLiouvillian H_R H_I F Y
      = -Complex.I • ((H_R + F) * Y - Y * (H_R + F)) - (H_I * Y - Y * H_I) :=
  covariantLiouvillian_complex_decompose H_R H_I F Y

/-- **[Reversible Einstein–Maxwell] at `H_I = 0` the electrogravitic superoperator is purely reversible.**
With no entropic source the superoperator reduces to the unitary Einstein–Maxwell Liouvillian
`covariantLiouvillian H_R F` — electromagnetism plus real gravity, reversible. -/
theorem electroGravitationalLiouvillian_reversible (H_R F Y : Matrix (Fin 4) (Fin 4) ℂ) :
    electroGravitationalLiouvillian H_R 0 F Y = covariantLiouvillian H_R F Y := by
  rw [electroGravitationalLiouvillian, smul_zero, sub_zero]

/-! ## §B — the entropic gap and the electrogravitic system -/

/-- **[The entropic gap is the imaginary Einstein source] `m_I c² = Im E`.** The gap that sources the
entropic part `−[H_I, ·]` of the electrogravitic superoperator is exactly the imaginary part of the complex
Einstein energy `E = (m_R + i m_I)c²` — the imaginary Einstein term `Λ`. -/
theorem electroGravitational_entropic_gap (m_R m_I c : ℝ) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im :=
  dirac_entropic_gap_eq_imaginary_einstein m_R m_I c

variable {ι : Type*} {Ric : Matrix ι ι ℝ} {scalarR : ℝ} {g Λ T S : Matrix ι ι ℝ}
  {κ m_R m_I c S₁ S₂ : ℝ} {k A : Fin 4 → ℝ}

/-- **[The electrogravitic superoperator's entropic gap double-copies] `Im E = S₁ + S₂`.** On an
electrogravitic solution the strength of the entropic part `−[H_I, ·]` of the superoperator is the
imaginary Einstein source `m_I c² = Im E`, and by the double copy this is the gauge² sum `S₁ + S₂`; hence
the entropic weight factorizes `exp(−Im E) = exp(−S₁)·exp(−S₂)` — the amplitude double copy
`gravity = gauge²`. The reversible/entropic split of the superoperator itself is the free-matrix identity
`electroGravitationalLiouvillian_decompose`. -/
theorem electroGravitational_superoperator_entropic_double_copy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    (complexEinsteinEnergy m_R m_I c).im = S₁ + S₂
      ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂) := by
  refine ⟨?_, ?_⟩
  · rw [← H.superoperatorEquations.1, H.gravitational.entropicSplit]
  · rw [← H.superoperatorEquations.1, H.gravitational.entropicSplit, neg_add, Real.exp_add]

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalSuperoperator

end

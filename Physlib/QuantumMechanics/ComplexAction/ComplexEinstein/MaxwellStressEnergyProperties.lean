/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
meta import Zil

/-!
# Algebraic properties of the electromagnetic stress-energy tensor

The electrovacuum / Einstein-Maxwell sector (`ElectroGravitationalFieldEquations`) defines the Maxwell
stress-energy tensor `T_{μν} = −F_{μα}F_ν{}^α + ¼ g_{μν}F_{αβ}F^{αβ}` (`maxwellStressEnergy`) and the
coupled equation `G = κ T` (the `.re` of the electrogravitic residual), but only gauge invariance of
`T` was proved.  A stress-energy tensor sourcing the symmetric Einstein tensor must itself be
**symmetric** — this module supplies that structural property.

* `maxwellStressEnergy_symm` — `T_{μν} = T_{νμ}` for a symmetric metric/inverse pair (whatever the
  field `F`), so `T` is a legitimate source for the symmetric Einstein tensor.

Reuses `maxwellStressEnergy`, `raiseSecondIndex`, `maxwellInvariant` and `faraday`
(`ElectroGravitationalFieldEquations` / `MaxwellFaraday`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

open scoped Matrix

/-- **The electromagnetic stress-energy tensor is symmetric** `T_{μν} = T_{νμ}` for a symmetric
metric and inverse metric — the structural requirement for it to source the symmetric Einstein tensor
in `G = κ T`.  (Holds for any field `F`; the antisymmetry of `F = dA` is not needed.) -/
@[zil_level physical_theorem]
theorem maxwellStressEnergy_symm (g gInv F : FourTensor) (hg : gᵀ = g) (hgInv : gInvᵀ = gInv)
    (μ ν : Fin 4) :
    maxwellStressEnergy g gInv F μ ν = maxwellStressEnergy g gInv F ν μ := by
  have hgsym : g μ ν = g ν μ := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hg ν) μ
  have hgisym : ∀ a b, gInv a b = gInv b a := fun a b => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hgInv b) a
  simp only [maxwellStressEnergy, raiseSecondIndex]
  rw [hgsym]
  congr 1
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [hgisym x y]; ring

/-- **The Maxwell stress-energy tensor built from `F = dA` is symmetric.** -/
@[zil_level physical_theorem]
theorem maxwellStressEnergy_faraday_symm (g gInv : FourTensor) (k A : Fin 4 → ℝ)
    (hg : gᵀ = g) (hgInv : gInvᵀ = gInv) (μ ν : Fin 4) :
    maxwellStressEnergy g gInv (faraday k A) μ ν = maxwellStressEnergy g gInv (faraday k A) ν μ :=
  maxwellStressEnergy_symm g gInv (faraday k A) hg hgInv μ ν

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties

zil attach maxwellStressEnergy_symm where
  formalizes @ "claim:the-electromagnetic-maxwell-stress-energy-tensor-is-symmetric-for-a-symmetric-metric-and-inverse-metric-so-it-is-a-legitimate-source-for-the-symmetric-einstein-tensor-in-the-einstein-maxwell-equation"

zil attach maxwellStressEnergy_faraday_symm where
  formalizes @ "claim:the-maxwell-stress-energy-tensor-built-from-the-faraday-field-strength-f-equals-d-a-is-symmetric",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties.maxwellStressEnergy_symm"

zil_file_contract physlib.maxwellStressEnergyProperties where
  promises "The symmetry of the electromagnetic stress-energy tensor of the Einstein-Maxwell sector. The Maxwell stress-energy tensor, minus F mu alpha F nu upper alpha plus one quarter g mu nu times the Maxwell invariant, is symmetric in its two indices for a symmetric metric and inverse metric, whatever the field strength. This is the structural requirement for it to be a legitimate source for the symmetric Einstein tensor in the Einstein-Maxwell equation G equals kappa T. The stress-energy tensor built from the Faraday field strength F equals d A is likewise symmetric. Reuses the Maxwell stress-energy tensor, the raised-index and Maxwell-invariant carriers, and the Faraday field strength of the electrogravitational field equations."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellStressEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.raiseSecondIndex"
  ]
  forbids_substitutes [
    "reading the symmetry of the Maxwell stress-energy tensor as its trace-freeness or its conservation, which are separate properties"
  ]
  witnessed_by [
    maxwellStressEnergy_symm,
    maxwellStressEnergy_faraday_symm
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.maxwellStressEnergyProperties

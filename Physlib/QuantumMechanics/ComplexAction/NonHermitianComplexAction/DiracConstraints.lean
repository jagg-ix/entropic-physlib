/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator

/-!
# Dirac first-class constraints & observables from the Nagao–Nielsen complex action

Constructs the **Dirac constraint machinery of canonical gravity** — the first-class constraint algebra and the
(tidal) **Dirac observables** — from the superoperator/commutant cluster and the **Nagao–Nielsen complex action**
(the complex-action generator `C = C_R − i·C_I`), supplying the Hamiltonian/analytic layer left open by
`CanonicalTetradGravity.TetradADMGravity`.

The bridge is the `collisionStar = ad` superoperator: a first-class constraint `C` generates a gauge
transformation through `ad_C = collisionStar C` (the same Liouville/modular generator as everywhere in this
cluster), and a **Dirac observable** is a gauge-invariant element — one annihilated by *every* constraint
generator. Hence:

  **Dirac observables `= ⋂_C ker(ad_C) = commutant 𝒞`** (`diracObservable_eq_commutant`),

exactly the von Neumann commutant of `AlgebraicQFT.GNSVonNeumannHadamard` / `ThermoFieldDynamics.KazamaTomitaTakesakiModular`. The first-class
property `{C₁,C₂} = a C₁ + b C₂` makes the gauge generators close into a Lie algebra
(`firstClass_flow_closes`, via the `ad`-homomorphism), the **Dirac constraint algebra**. The Nagao–Nielsen
complex constraint `C_R − i·C_I` (the complex-action generator, `NagaoNielsenSchrodinger.complexHamiltonian`)
splits the gauge flow into a **reversible** part `C_R` and an **entropic** part `C_I`
(`complexConstraint_flow_decompose`); observables Dirac for *both* are Dirac for the complex constraint
(`complexConstraint_dirac_of`).

* **§A — Dirac observables = the commutant** (`DiracObservable`, `diracObservable_eq_commutant`,
  `diracObservable_single_iff`).
* **§B — the first-class constraint algebra** (`IsFirstClass`, `firstClass_flow_closes`).
* **§C — the Nagao–Nielsen complex constraint** (`complexConstraint`, `complexConstraint_flow_decompose`,
  `complexConstraint_dirac_of`).

The remaining deep machinery — the York canonical basis diagonalizing York–Lichnerowicz, the explicit tidal
observables of the gravitational field, and the post-Minkowskian linearization — is the analytic/Hamiltonian
layer; the constraint-algebra and Dirac-observable kernel is formalized here. The York time `tr K`
(`CanonicalTetradGravity.TetradADMGravity.yorkTime`) is the inertial gauge variable conjugate to the scalar constraint.

## References

* P. A. M. Dirac, *Lectures on Quantum Mechanics* (first-class constraints, Dirac observables); L. Lusanna,
  IJGMMP 12 (2015) 1530001 (the canonical ADM constraints, York time, tidal Dirac observables).
* K. Nagao, H. B. Nielsen, *complex action theory* (the complex generator `C_R − i C_I`,
  `NagaoNielsenSchrodinger`).
* Repo dependencies: `AlgebraicQFT.GNSVonNeumannHadamard` (`commutant`, `mem_commutant_iff_collisionStar_zero`),
  `CollisionOperatorSl2.CollisionModular` (`collisionStar`, `collisionStar_ad_hom`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.DiracConstraints

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular

/-! ## §A — Dirac observables are the commutant of the constraints -/

section Observables
variable {A : Type*} [Ring A]

/-- **A Dirac observable** — a gauge-invariant element annihilated by every constraint generator `ad_C`:
`collisionStar C O = 0` for all constraints `C ∈ 𝒞`. -/
def DiracObservable (𝒞 : Set A) (O : A) : Prop := ∀ C ∈ 𝒞, collisionStar C O = 0

/-- **[Dirac observables = commutant] `{O | DiracObservable 𝒞 O} = 𝒞'`.** The gauge-invariant observables are
*exactly* the von Neumann commutant of the constraints — the common kernel `⋂_C ker(ad_C)` of the constraint
generators. -/
theorem diracObservable_eq_commutant (𝒞 : Set A) :
    {O | DiracObservable 𝒞 O} = commutant 𝒞 := by
  ext O
  simp only [Set.mem_setOf_eq, DiracObservable, commutant, Set.mem_centralizer_iff]
  constructor
  · intro h C hC; have hh := h C hC; rwa [collisionStar, sub_eq_zero] at hh
  · intro h C hC; rw [collisionStar, sub_eq_zero]; exact h C hC

/-- **[Single constraint] `O` is Dirac for `C ⟺ O ∈ {C}'`** — gauge-invariance under one constraint is
membership in its commutant (the modular fixed-point algebra of `ad_C`,
`mem_commutant_iff_collisionStar_zero`). -/
theorem diracObservable_single_iff (C O : A) :
    collisionStar C O = 0 ↔ O ∈ commutant ({C} : Set A) :=
  (mem_commutant_iff_collisionStar_zero C O).symm

end Observables

/-! ## §B — the first-class constraint algebra -/

section FirstClass
variable {n : ℕ}

/-- **A first-class constraint pair** `{C₁,C₂} = a C₁ + b C₂` — the bracket closes on the constraints (with
structure constants `a, b`), the defining property of Dirac's first-class constraints. -/
def IsFirstClass (C₁ C₂ : Matrix (Fin n) (Fin n) ℂ) (a b : ℂ) : Prop :=
  collisionStar C₁ C₂ = a • C₁ + b • C₂

/-- **[The gauge generators close into a Lie algebra] `[ad_{C₁}, ad_{C₂}] = ad_{aC₁+bC₂}`.** For a first-class
pair the commutator of the two gauge flows is the gauge flow of `a C₁ + b C₂` (`collisionStar_ad_hom`): the
constraint surface is preserved by the gauge transformations — the Dirac constraint algebra. -/
theorem firstClass_flow_closes {C₁ C₂ : Matrix (Fin n) (Fin n) ℂ} {a b : ℂ}
    (h : IsFirstClass C₁ C₂ a b) (O : Matrix (Fin n) (Fin n) ℂ) :
    collisionStar C₁ (collisionStar C₂ O) - collisionStar C₂ (collisionStar C₁ O)
      = collisionStar (a • C₁ + b • C₂) O := by
  rw [collisionStar_ad_hom]; unfold IsFirstClass at h; rw [h]

end FirstClass

/-! ## §C — the Nagao–Nielsen complex constraint -/

section ComplexConstraint
variable {n : ℕ}

/-- **The Nagao–Nielsen complex constraint** `C = C_R − i·C_I` — the complex-action (complex-action) generator, with a
real (reversible) part `C_R` and an imaginary (entropic) part `C_I`. -/
noncomputable def complexConstraint (C_R C_I : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := C_R - Complex.I • C_I

/-- **[Gauge flow splits] `ad_{C_R − iC_I} = ad_{C_R} − i·ad_{C_I}`.** The complex-constraint gauge flow
decomposes into a reversible part `ad_{C_R}` and an entropic part `ad_{C_I}` — the Nagao–Nielsen real/imaginary
split of the complex action at the constraint level. -/
theorem complexConstraint_flow_decompose (C_R C_I O : Matrix (Fin n) (Fin n) ℂ) :
    collisionStar (complexConstraint C_R C_I) O
      = collisionStar C_R O - Complex.I • collisionStar C_I O := by
  simp only [complexConstraint, collisionStar, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_sub]
  module

/-- **[Dirac for both parts ⟹ Dirac for the complex constraint].** An observable invariant under *both* the
reversible `C_R` and the entropic `C_I` constraint flows is a Dirac observable of the Nagao–Nielsen complex
constraint. -/
theorem complexConstraint_dirac_of {C_R C_I O : Matrix (Fin n) (Fin n) ℂ}
    (hR : collisionStar C_R O = 0) (hI : collisionStar C_I O = 0) :
    collisionStar (complexConstraint C_R C_I) O = 0 := by
  rw [complexConstraint_flow_decompose, hR, hI, smul_zero, sub_zero]

end ComplexConstraint

end Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.DiracConstraints

end

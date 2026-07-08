/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.ContinuumCAR

/-!
# The fermionic second-quantization functor `H ↦ Λ(H)` (Mathlib `ExteriorAlgebra` + `contractLeft`)

The Tier-3 file flagged the fermionic Fock-space functor as "not built — Mathlib lacks the layer".
**That was wrong.** Mathlib *does* include the functor: the fermionic Fock space is the **exterior
algebra** `Λ(H) = ExteriorAlgebra ℝ H` (`= CliffordAlgebra 0`), with
- **creation** `a†(m) = ι m · (·)` (left multiplication by `ι`),
- **annihilation** `a(d) = d⌋(·)` (`CliffordAlgebra.contractLeft`),
- the **CAR** `{a(d), a†(m)} = d(m)·id` (`CliffordAlgebra.contractLeft_ι_mul`),
- **Pauli exclusion** `a†(m)² = 0`, `a(d)² = 0` (`ExteriorAlgebra.ι_sq_zero`,
 `CliffordAlgebra.contractLeft_contractLeft`),
- and the **functor on morphisms** `Γ(U) = ExteriorAlgebra.map U` — the second quantization of a
 one-particle map (`ExteriorAlgebra.map_apply_ι` intertwines creation: `Γ(U) a†(m) = a†(Um) Γ(U)`).

This file assembles these into the second-quantization functor and connects it to the Bogoliubov work:
the Bogoliubov **unitary** `U` of `Bogoliubov.ContinuumCAR` (Tier 3, `u²+v²=1`) second-quantizes to the
Fock-space algebra automorphism `Γ(U) = ExteriorAlgebra.map U`.

## The construction (all from Mathlib)

* `creationOp m = ι m · (·)`, `annihilationOp d = d⌋(·)` — creation/annihilation on `Λ(M)`.
* `car` — `{a(d), a†(m)} = d(m)·id`, the canonical anticommutation relation.
* `creationOp_sq`, `annihilationOp_sq` — Pauli exclusion `a†² = a² = 0`.
* `secondQuant U = ExteriorAlgebra.map U` — the functor; `secondQuant_creationOp` intertwines creation.

## How this completes the tier ladder (and where Matsubara / Nagao–Nielsen enter)

The Bogoliubov automorphism of the CAR algebra over the continuum one-particle space (Tier 3, `U`
unitary iff `u²+v²=1`) is now `Γ(U) = ExteriorAlgebra.map U` — an algebra automorphism of the Fock
space `Λ(L²(ℝ³))`. The remaining analytic layer is the **trace / partition function**
`Z = Tr_{Λ(H)}(e^{−βH})`, which is exactly:
- the **Matsubara** thermal circle (`Physlib/QFT/Matsubara`, `ThermalCircle`, `matsubaraOmegaFermion`,
 the KMS-antiperiodic boundary condition, the Boltzmann weight `e^{−βE_R}`);
- equal to the **Nagao–Nielsen complex-action path integral** (`PathIntegral.QFTPathIntegralComplexAction`:
 `thermoActionWeight = complexActionWeight = lorentzianKernel`), Wick-rotated, convergent under
 `Im m > 0` (`PathIntegral.MomentumPathIntegral.momentum_integral_converges_iff`).

So the functor `H ↦ Λ(H)` (Mathlib), its morphisms `Γ(U)` (the Bogoliubov), and the thermal trace
(Matsubara = Nagao–Nielsen path integral) together are the second-quantization layer; this file builds
the algebraic functor and the Bogoliubov morphism.

## Scope

The exterior-algebra Fock functor, the CAR, Pauli exclusion, and the Bogoliubov second-quantization
`Γ(U)` are built here from Mathlib. The **trace** `Tr_{Λ(H)}(e^{−βH})` as the Matsubara / Nagao–Nielsen
partition function (the analytic identity equating the Fock trace to the thermal path integral) is the
next step, using `Physlib/QFT/Matsubara` and `PathIntegral.QFTPathIntegralComplexAction`; it is referenced
here, not yet proved (the Fock-space trace over the infinite-dimensional `Λ(L²)` needs the trace-class
/ KMS-state layer).

## References

* Mathlib `LinearAlgebra/ExteriorAlgebra`, `LinearAlgebra/CliffordAlgebra/Contraction`. This
 development: `Bogoliubov.ContinuumCAR`, `Bogoliubov.FermionicBogoliubovCAR`; physlib `QFT/Matsubara`,
 `PathIntegral.QFTPathIntegralComplexAction`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open CliffordAlgebra

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]

/-! ## §A — the fermionic Fock space `Λ(M)` (the exterior algebra) -/

/-- **The fermionic Fock space** `Λ(M) = ExteriorAlgebra ℝ M` (`= CliffordAlgebra 0`). -/
abbrev Fock (M : Type*) [AddCommGroup M] [Module ℝ M] : Type _ := ExteriorAlgebra ℝ M

/-- **The creation operator** `a†(m) = ι m · (·)` (left wedge multiplication). -/
def creationOp (m : M) (x : Fock M) : Fock M := ι (0 : QuadraticForm ℝ M) m * x

/-- **The annihilation operator** `a(d) = d⌋(·)` (the contraction / interior product). -/
def annihilationOp (d : Module.Dual ℝ M) (x : Fock M) : Fock M := contractLeft d x

/-! ## §B — the canonical anticommutation relations and Pauli exclusion -/

/-- **The canonical anticommutation relation** `{a(d), a†(m)} = d(m)·id`: `a(d)(a†(m) x) + a†(m)(a(d)
x) = d(m)·x` (`CliffordAlgebra.contractLeft_ι_mul`). With `d = ⟪f, ·⟫` and `m = g` this is
`{a(f), a†(g)} = ⟪f, g⟫`. -/
theorem car (d : Module.Dual ℝ M) (m : M) (x : Fock M) :
    annihilationOp d (creationOp m x) + creationOp m (annihilationOp d x) = d m • x := by
  simp only [creationOp, annihilationOp]
  rw [contractLeft_ι_mul]
  abel

/-- **Pauli exclusion for creation** `a†(m)² = 0` (`ExteriorAlgebra.ι_sq_zero`). -/
theorem creationOp_sq (m : M) (x : Fock M) : creationOp m (creationOp m x) = 0 := by
  rw [creationOp, creationOp, ← mul_assoc, ι_sq_scalar]
  simp

/-- **Pauli exclusion for annihilation** `a(d)² = 0` (`CliffordAlgebra.contractLeft_contractLeft`). -/
theorem annihilationOp_sq (d : Module.Dual ℝ M) (x : Fock M) :
    annihilationOp d (annihilationOp d x) = 0 := contractLeft_contractLeft d x

/-! ## §C — the second-quantization functor `Γ(U) = ExteriorAlgebra.map U` -/

/-- **The second-quantization functor on morphisms** `Γ(U) = Λ(U) = ExteriorAlgebra.map U` — a
one-particle linear map `U : M → N` lifts to the Fock-space algebra homomorphism
`Λ(M) →ₐ[ℝ] Λ(N)`. -/
def secondQuant (U : M →ₗ[ℝ] N) : Fock M →ₐ[ℝ] Fock N := ExteriorAlgebra.map U

/-- **The functor intertwines creation** `Γ(U) a†(m) = a†(U m) Γ(U)`: the second quantization of a
one-particle map includes the creation operator of `m` to that of `U m`. -/
theorem secondQuant_creationOp (U : M →ₗ[ℝ] N) (m : M) (x : Fock M) :
    secondQuant U (creationOp m x) = creationOp (U m) (secondQuant U x) := by
  simp only [creationOp, secondQuant]
  rw [map_mul, show (ExteriorAlgebra.map U) (ι (0 : QuadraticForm ℝ M) m)
    = ι (0 : QuadraticForm ℝ N) (U m) from ExteriorAlgebra.map_apply_ι U m]

/-- **The second-quantization functor preserves the identity** `Γ(id) = id`. -/
theorem secondQuant_id : secondQuant (LinearMap.id : M →ₗ[ℝ] M) = AlgHom.id ℝ (Fock M) := by
  rw [secondQuant, ExteriorAlgebra.map_id]

/-- **Functoriality** `Γ(V ∘ U) = Γ(V) ∘ Γ(U)`: the second-quantization functor respects composition. -/
theorem secondQuant_comp {P : Type*} [AddCommGroup P] [Module ℝ P]
    (U : M →ₗ[ℝ] N) (V : N →ₗ[ℝ] P) :
    secondQuant (V ∘ₗ U) = (secondQuant V).comp (secondQuant U) := by
  rw [secondQuant, secondQuant, secondQuant, ExteriorAlgebra.map_comp_map]

end Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor

end

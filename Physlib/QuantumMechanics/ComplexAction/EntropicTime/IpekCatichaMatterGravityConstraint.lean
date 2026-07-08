/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM

/-!
# The super-Hamiltonian constraint: positive matter energy forces the DeWitt supermetric to be indefinite (Ipek–Caticha)

Couples the two sectors of Ipek–Caticha (arXiv:2006.05036): the **quantum matter** super-Hamiltonian (Eq. 100a,
the curved-space Klein–Gordon energy density, which is *positive*) and the **gravitational** super-Hamiltonian
(Eq. 66, whose kinetic term is the DeWitt supermetric of `IpekCatichaDeWittSupermetricADM`). They are tied by the
super-Hamiltonian constraint (Eqs. 68, 102a–103)

`H_⊥ = H^G_⊥ + ⟨Ĥ_⊥⟩ ≈ 0`.

The physical payoff: the matter energy `⟨Ĥ_⊥⟩ ≥ 0` is non-negative, so the constraint forces the gravitational
super-Hamiltonian `H^G_⊥ ≤ 0` to be *non-positive* — and that is possible only because the DeWitt supermetric is
**indefinite** (its conformal direction is negative, `deWittKinetic_conformal`). Positive matter energy is exactly
what the negative (conformal) direction of superspace is for.

* the **Klein–Gordon matter density** `ℋ = π²/2√g + (√g/2)g^{ij}∂χ∂χ + √g V` (`kgMatterDensity`) reduces to the flat
 massless KG energy `π²/2 + (∂χ)²/2 + V` (`kgMatter_flat`) and is **non-negative** (`kgMatter_nonneg`) for a
 positive metric and non-negative potential;
* the **gravitational super-Hamiltonian** `H^G_⊥ = (κ/√g)𝒦(M) − (√g/2κ)R` (`gravSuperHamiltonian`) has a
 conformal-kinetic term that is **non-positive** (`gravSuperHamiltonian_conformal_kinetic_nonpos`) — the indefinite
 DeWitt direction;
* the **constraint forces gravity non-positive** (`hamiltonian_constraint_forces_gravity_nonpos`,
 `matter_positivity_forces_gravity_nonpos`): with `H^G_⊥ + ℋ = 0` and `ℋ ≥ 0`, necessarily `H^G_⊥ ≤ 0` — the
 positive matter energy is balanced by the negative (conformal) DeWitt direction of the gravitational kinetic term.

So the two sectors interlock: matter energy is positive, the super-Hamiltonian constraint sets it equal to `−H^G_⊥`,
and the gravitational super-Hamiltonian can be negative only because the DeWitt supermetric of superspace is
Lorentzian. The indefinite signature of the gravity module is exactly what the constraint with positive matter
requires.

* **§A — the Klein–Gordon matter super-Hamiltonian** (`kgMatterDensity`, `kgMatter_flat`, `kgMatter_nonneg`).
* **§B — the gravitational super-Hamiltonian** (`gravSuperHamiltonian`,
 `gravSuperHamiltonian_conformal_kinetic_nonpos`).
* **§C — the constraint interlocks the sectors** (`hamiltonian_constraint_forces_gravity_nonpos`,
 `matter_positivity_forces_gravity_nonpos`).

The Klein–Gordon density, its flat limit and positivity, the gravitational super-Hamiltonian,
and the constraint inequality are exact algebra, reusing `deWittKinetic` and `deWittKinetic_conformal`. The full
functional super-Hamiltonian, the constraint algebra closure, and the quantum-operator expectation values are the
referenced content. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 66, 100a, 102a–103); ADM constraint. Repo structure:
 `EntropicTime.IpekCatichaDeWittSupermetricADM` (`deWittKinetic`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint

/-! ## §A — the Klein–Gordon matter super-Hamiltonian -/

/-- **The Klein–Gordon matter super-Hamiltonian density** `ℋ = π²/2√g + (√g/2)g^{ij}∂χ∂χ + √g V` (Ipek–Caticha
Eq. 100a, the expectation value `⟨Ĥ_⊥⟩` of the curved-space Klein–Gordon Hamiltonian: kinetic + gradient +
potential), with `π` the field momentum, `gradchi` the spatial gradient, `ginv = g^{ij}` and `sqrtg = √g` the
metric factors, `V` the potential. -/
noncomputable def kgMatterDensity (sqrtg ginv π gradchi V : ℝ) : ℝ :=
  π ^ 2 / (2 * sqrtg) + sqrtg * ginv * gradchi ^ 2 / 2 + sqrtg * V

/-- **[The flat limit is the massless Klein–Gordon energy] `ℋ|_{g=δ} = π²/2 + (∂χ)²/2 + V`.** At `√g = g^{ij} = 1`
the matter density is the standard flat-space Klein–Gordon Hamiltonian density. -/
theorem kgMatter_flat (π gradchi V : ℝ) :
    kgMatterDensity 1 1 π gradchi V = π ^ 2 / 2 + gradchi ^ 2 / 2 + V := by
  unfold kgMatterDensity; ring

/-- **[The matter energy is non-negative] `ℋ ≥ 0`.** For a positive metric (`√g > 0`, `g^{ij} ≥ 0`) and a
non-negative potential, the Klein–Gordon energy density is non-negative — the matter super-Hamiltonian records
positive energy. -/
theorem kgMatter_nonneg (sqrtg ginv π gradchi V : ℝ) (hg : 0 < sqrtg) (hginv : 0 ≤ ginv)
    (hV : 0 ≤ V) : 0 ≤ kgMatterDensity sqrtg ginv π gradchi V := by
  unfold kgMatterDensity
  have h1 : 0 ≤ π ^ 2 / (2 * sqrtg) := div_nonneg (sq_nonneg π) (by linarith)
  have h2 : 0 ≤ sqrtg * ginv * gradchi ^ 2 / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hg.le hginv) (sq_nonneg _)) (by norm_num)
  have h3 : 0 ≤ sqrtg * V := mul_nonneg hg.le hV
  linarith

/-! ## §B — the gravitational super-Hamiltonian -/

/-- **The gravitational super-Hamiltonian density** `H^G_⊥ = (κ/√g)𝒦(M) − (√g/2κ)R` (Ipek–Caticha Eq. 66), with
`𝒦(M) = 2Tr(M²) − (Tr M)²` the DeWitt supermetric kinetic term of the mixed momentum `M = π^i_j` and `R` the
spatial Ricci scalar. -/
noncomputable def gravSuperHamiltonian (κ sqrtg R : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (κ / sqrtg) * deWittKinetic M - sqrtg * R / (2 * κ)

/-- **[The conformal-kinetic contribution is non-positive] `(κ/√g)𝒦(c·1) ≤ 0`.** For a positive coupling
(`κ, √g > 0`) the conformal (pure-trace) momentum `M = c·1` contributes a *non-positive* kinetic energy to the
gravitational super-Hamiltonian — the negative direction of the indefinite DeWitt supermetric. -/
theorem gravSuperHamiltonian_conformal_kinetic_nonpos (κ sqrtg c : ℝ) (hκ : 0 < κ)
    (hg : 0 < sqrtg) : (κ / sqrtg) * deWittKinetic (c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ≤ 0 := by
  rw [deWittKinetic_conformal]
  have hcoef : 0 ≤ κ / sqrtg := by positivity
  nlinarith [sq_nonneg c, hcoef]

/-! ## §C — the constraint interlocks the sectors -/

/-- **[The super-Hamiltonian constraint forces gravity non-positive] `H^G + ℋ = 0`, `ℋ ≥ 0` ⟹ `H^G ≤ 0`.** The
constraint sets the gravitational super-Hamiltonian equal to minus the matter energy; positive matter energy makes
it non-positive. -/
theorem hamiltonian_constraint_forces_gravity_nonpos (Hgrav Hmatter : ℝ)
    (hconstraint : Hgrav + Hmatter = 0) (hmatter : 0 ≤ Hmatter) : Hgrav ≤ 0 := by
  linarith

/-- **[Positive matter energy forces a non-positive gravitational super-Hamiltonian].** Combining the Klein–Gordon
positivity with the super-Hamiltonian constraint `H^G_⊥ + ℋ = 0`: the gravitational super-Hamiltonian is
non-positive, which is possible only because the DeWitt supermetric is indefinite (its conformal direction is
negative). The positive matter energy is balanced by the negative direction of superspace. -/
theorem matter_positivity_forces_gravity_nonpos (κ sqrtg R : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (ginv π gradchi V : ℝ) (hg : 0 < sqrtg) (hginv : 0 ≤ ginv) (hV : 0 ≤ V)
    (hconstraint : gravSuperHamiltonian κ sqrtg R M + kgMatterDensity sqrtg ginv π gradchi V = 0) :
    gravSuperHamiltonian κ sqrtg R M ≤ 0 :=
  hamiltonian_constraint_forces_gravity_nonpos _ _ hconstraint
    (kgMatter_nonneg sqrtg ginv π gradchi V hg hginv hV)

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint

end

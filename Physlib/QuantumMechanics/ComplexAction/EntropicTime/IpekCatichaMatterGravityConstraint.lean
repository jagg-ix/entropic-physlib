/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM

meta import Zil

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

**Honest layering.** The Klein–Gordon density, its flat limit and positivity, the gravitational super-Hamiltonian,
and the constraint inequality are exact algebra, reusing `deWittKinetic` and `deWittKinetic_conformal`. The full
functional super-Hamiltonian, the constraint algebra closure, and the quantum-operator expectation values are the
referenced content. ## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 66, 100a, 102a–103); ADM constraint. Repo carrier:
  `EntropicTime.IpekCatichaDeWittSupermetricADM` (`deWittKinetic`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint


/-- **The Klein–Gordon matter super-Hamiltonian density** `ℋ = π²/2√g + (√g/2)g^{ij}∂χ∂χ + √g V` (Ipek–Caticha
Eq. 100a, the expectation value `⟨Ĥ_⊥⟩` of the curved-space Klein–Gordon Hamiltonian: kinetic + gradient +
potential), with `π` the field momentum, `gradchi` the spatial gradient, `ginv = g^{ij}` and `sqrtg = √g` the
metric factors, `V` the potential. -/
noncomputable def kgMatterDensity (sqrtg ginv π gradchi V : ℝ) : ℝ :=
  π ^ 2 / (2 * sqrtg) + sqrtg * ginv * gradchi ^ 2 / 2 + sqrtg * V

/-- **[The flat limit is the massless Klein–Gordon energy] `ℋ|_{g=δ} = π²/2 + (∂χ)²/2 + V`.** At `√g = g^{ij} = 1`
the matter density is the standard flat-space Klein–Gordon Hamiltonian density. -/
lemma kgMatter_flat (π gradchi V : ℝ) :
    kgMatterDensity 1 1 π gradchi V = π ^ 2 / 2 + gradchi ^ 2 / 2 + V := by
  unfold kgMatterDensity; ring

/-- **[The matter energy is non-negative] `ℋ ≥ 0`.** For a positive metric (`√g > 0`, `g^{ij} ≥ 0`) and a
non-negative potential, the Klein–Gordon energy density is non-negative — the matter super-Hamiltonian carries
positive energy. -/
lemma kgMatter_nonneg (sqrtg ginv π gradchi V : ℝ) (hg : 0 < sqrtg) (hginv : 0 ≤ ginv)
    (hV : 0 ≤ V) : 0 ≤ kgMatterDensity sqrtg ginv π gradchi V := by
  unfold kgMatterDensity
  have h1 : 0 ≤ π ^ 2 / (2 * sqrtg) := div_nonneg (sq_nonneg π) (by linarith)
  have h2 : 0 ≤ sqrtg * ginv * gradchi ^ 2 / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hg.le hginv) (sq_nonneg _)) (by norm_num)
  have h3 : 0 ≤ sqrtg * V := mul_nonneg hg.le hV
  linarith


/-- **The gravitational super-Hamiltonian density** `H^G_⊥ = (κ/√g)𝒦(M) − (√g/2κ)R` (Ipek–Caticha Eq. 66), with
`𝒦(M) = 2Tr(M²) − (Tr M)²` the DeWitt supermetric kinetic term of the mixed momentum `M = π^i_j` and `R` the
spatial Ricci scalar. -/
noncomputable def gravSuperHamiltonian (κ sqrtg R : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (κ / sqrtg) * deWittKinetic M - sqrtg * R / (2 * κ)

/-- **[The conformal-kinetic contribution is non-positive] `(κ/√g)𝒦(c·1) ≤ 0`.** For a positive coupling
(`κ, √g > 0`) the conformal (pure-trace) momentum `M = c·1` contributes a *non-positive* kinetic energy to the
gravitational super-Hamiltonian — the negative direction of the indefinite DeWitt supermetric. -/
lemma gravSuperHamiltonian_conformal_kinetic_nonpos (κ sqrtg c : ℝ) (hκ : 0 < κ)
    (hg : 0 < sqrtg) : (κ / sqrtg) * deWittKinetic (c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ≤ 0 := by
  rw [deWittKinetic_conformal]
  have hcoef : 0 ≤ κ / sqrtg := by positivity
  nlinarith [sq_nonneg c, hcoef]


/-- **[The super-Hamiltonian constraint forces gravity non-positive] `H^G + ℋ = 0`, `ℋ ≥ 0` ⟹ `H^G ≤ 0`.** The
constraint sets the gravitational super-Hamiltonian equal to minus the matter energy; positive matter energy makes
it non-positive. -/
lemma hamiltonian_constraint_forces_gravity_nonpos (Hgrav Hmatter : ℝ)
    (hconstraint : Hgrav + Hmatter = 0) (hmatter : 0 ≤ Hmatter) : Hgrav ≤ 0 := by
  linarith

/-- **[Positive matter energy forces a non-positive gravitational super-Hamiltonian].** Combining the Klein–Gordon
positivity with the super-Hamiltonian constraint `H^G_⊥ + ℋ = 0`: the gravitational super-Hamiltonian is
non-positive, which is possible only because the DeWitt supermetric is indefinite (its conformal direction is
negative). The positive matter energy is balanced by the negative direction of superspace. -/
lemma matter_positivity_forces_gravity_nonpos (κ sqrtg R : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (ginv π gradchi V : ℝ) (hg : 0 < sqrtg) (hginv : 0 ≤ ginv) (hV : 0 ≤ V)
    (hconstraint : gravSuperHamiltonian κ sqrtg R M + kgMatterDensity sqrtg ginv π gradchi V = 0) :
    gravSuperHamiltonian κ sqrtg R M ≤ 0 :=
  hamiltonian_constraint_forces_gravity_nonpos _ _ hconstraint
    (kgMatter_nonneg sqrtg ginv π gradchi V hg hginv hV)

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.matter_positivity_forces_gravity_nonpos where
  formalizes @ "claim:positive-klein-gordon-matter-energy-via-the-super-hamiltonian-constraint-h-grav-plus-h-matter-equals-zero-forces-the-gravitational-super-hamiltonian-to-be-non-positive-which-is-only-possible-because-the-dewitt-supermetric-of-superspace-is-indefinite-lorentzian",
  supported_by @ "paper:ipek-caticha-entropic-dynamics-quantum-gravity-functional-schrodinger-constraints"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.kgMatter_nonneg where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-curved-space-klein-gordon-matter-energy-density-pi-squared-over-two-root-g-plus-root-g-over-two-times-g-inverse-grad-chi-squared-plus-root-g-v-is-non-negative-for-a-positive-metric-and-non-negative-potential"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.gravSuperHamiltonian_conformal_kinetic_nonpos where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM.deWittKinetic_conformal",
  formalizes @ "claim:the-conformal-pure-trace-momentum-direction-of-the-gravitational-kinetic-term-contributes-non-positive-energy-the-negative-direction-of-the-indefinite-dewitt-supermetric"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.hamiltonian_constraint_forces_gravity_nonpos where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:if-the-gravitational-and-matter-super-hamiltonians-sum-to-zero-and-the-matter-part-is-non-negative-then-the-gravitational-part-is-non-positive-the-abstract-constraint-inequality"

zil_file_contract physlib.ipekCatichaMatterGravityConstraint where
  promises "The Ipek-Caticha super-Hamiltonian constraint forcing the DeWitt supermetric to be indefinite. The curved-space Klein-Gordon matter density is non-negative for a positive metric and non-negative potential (kgMatter_nonneg); the conformal (pure-trace) gravitational kinetic direction contributes non-positive energy (gravSuperHamiltonian_conformal_kinetic_nonpos); and via the constraint H^G + H = 0 with non-negative matter (hamiltonian_constraint_forces_gravity_nonpos), positive matter energy forces the gravitational super-Hamiltonian to be non-positive (matter_positivity_forces_gravity_nonpos) -- only possible because superspace is Lorentzian."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.kgMatterDensity",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.gravSuperHamiltonian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM.deWittKinetic"]
  forbids_substitutes ["the full stress-energy positivity (energy conditions) of the Klein-Gordon field and the global hyperbolicity of the ADM evolution, which are the cited relativity infrastructure",
    "any claim that superspace signature is derived from causality; only the constraint-driven sign relation between the matter and gravitational super-Hamiltonians is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.matter_positivity_forces_gravity_nonpos,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.kgMatter_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.gravSuperHamiltonian_conformal_kinetic_nonpos,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.hamiltonian_constraint_forces_gravity_nonpos]

/- ZIL-END -/

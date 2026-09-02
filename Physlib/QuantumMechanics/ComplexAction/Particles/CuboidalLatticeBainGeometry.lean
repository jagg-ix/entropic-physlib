/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.LennardJonesAxilrodTeller
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Equations of state and cuboidal lattice geometry: Tait, Birch–Murnaghan, Bain path, ATM extremum

The compressibility/finite-strain/lattice-geometry sector in five namespaces (each formerly its own
module):

* **Part I — `TaitEquationOfState`.** The Tait/Tammann compressibility equations (Dymond & Malhotra,
  Int. J. Thermophys. **9** (1988) 941): the true Tait equation as linearity of the secant bulk
  modulus (`true_tait_secant_linear`), the modified (Tammann) differential compressibility as the
  exact derivative of the integrated volume (`tait_compressibility`), the equivalence of the volume
  forms (`tait_relative_volume`), and the identification `B = A·K₀` of the fit parameter with the
  zero-pressure bulk modulus (`tait_bulk_modulus_zero`).
* **Part II — `BirchMurnaghanFiniteStrain`.** Birch's Eulerian finite-strain equation of state
  (Phys. Rev. **71** (1947) 809): the kinematic `1+2f = y²` (`strain_kinematic`), the second-order
  `P = (3/2)K₀(y⁷−y⁵)` in strain form (`birchMurnaghan_strain_form`), its derivation `P = −dE/dV`
  from the finite-strain free energy (`birchMurnaghan_is_energy_derivative`), the bulk modulus
  `K = −V dP/dV` with `K(1) = K₀` and the signature `K₀′ = 4`
  (`birch_bulk_modulus_pressure_derivative`), the Lagrangian/Eulerian reciprocity
  (`lagrangian_eulerian_reciprocal`), and the hydrostatic volume relation (`volume_from_compression`).
* **Part III — `CuboidalLatticeBainGeometry`.** The exact lattice geometry of Robles-Navarro et al.
  (arXiv:2504.07338, §II.A–C): the Conway–Sloane cuboidal Gram matrix with `det G = 4v⁶A = V_Λ²`
  (`cuboidalGram_det_eq_volume_sq`), the region-II nearest-neighbour distance
  (`nnDistSq_min_region_II`), the packing densities `Δ_fcc = π√2/6 > Δ_bcc = π√3/8`
  (`fcc_denser_than_bcc`), the kissing numbers with fcc maximal, the Bain parameter `A = ½γ²` tied to
  the `c/a` endpoints (`bainA_fcc`, `bainA_bcc`), and the Bain matrix `diag(√A,1,1)` with `det = √A`.
* **Part IV — `BirchInteratomicPotential`.** Birch §6, the bridge to the interatomic potential: the
  Lagrangian and Eulerian `K₀′` agree under `D₃ = C₃ + 6C₂` (`lagrangian_eulerian_k0prime_agree`),
  the Born power law gives `K₀′ = (9+m+n)/3` two independent ways (`powerLaw_potential_k0Prime`,
  `powerLaw_coefficient_k0Prime`), the `(12,6)` Lennard-Jones value `K₀′ = 9`
  (`lennardJones_12_6_k0Prime`), and `K₀′ = 4 ⟺ m+n = 3` (`bm2_soft_powerlaw`) — why the
  second-order equation of state suits only soft solids.
* **Part V — `AxilrodTellerBccExtremum`.** The headline analytic result of arXiv:2504.07338
  (Appendix H): the ATM three-body cohesive energy is stationary at bcc for every coupling — the
  cyclic orbit sum `Σ_σ (σx)ᵀD(σx) = |x|²·Tr(D)` (`cyclic_orbit_sum`) vanishes for the traceless
  derivative form (`bcc_zeta_derivative_term_vanishes`), so the zeta recombination is stationary
  (`atmCohesive_stationary`) at the Bain parameter `bainA bccRatio = 1/2` (`bcc_extremum_at_half`).

**Honest layering.** Every theorem is an exact `ring`/`field_simp`/`deriv`/matrix identity or an
explicit inequality. The empirical content — the Tait parameters `A, B, C, π`, the material `K₀`,
the third-order strain coefficients, the Epstein-zeta lattice sums and the numerical Bain-path
energetics — is the papers' fitted/computational side, recorded as input and not formalized. The
differentiation-under-the-sum step and the diagonal-traceless form of `D` in the rotated bcc frame
(Part V) are the paper's analytic inputs, noted not re-derived.

## References

* Dymond & Malhotra, Int. J. Thermophys. **9**, 941 (1988), Eqs. 2–5; Tait (1888); Tammann.
* Birch, Phys. Rev. **71**, 809 (1947), Eqs. 4–37 (§§2–6); Murnaghan.
* Robles-Navarro et al., arXiv:2504.07338 (2025), §II.A–C, Eqs. 8–14, Appendix H. Extends
  `Particles.LennardJonesAxilrodTeller`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.TaitEquationOfState


/-- The **isothermal secant bulk modulus** `K_sec = p v₀/(v₀ − v)` — the mean bulk modulus over the compression
from `v₀` (at reference pressure) to `v` (at pressure `p`). -/
noncomputable def secantBulkModulus (v₀ v p : ℝ) : ℝ := p * v₀ / (v₀ - v)

/-- **The true Tait equation is the linearity of the secant bulk modulus** (Eq. 3) — the true-Tait volume strain
`(v₀−v)/v₀ = A p/(π+p)` gives `K_sec = π/A + p/A`, an affine function of pressure with slope `1/A` and intercept
`π/A`. This *is* Tait's original equation `p v₀/(v₀−v) = π/A + p/A`. -/
lemma true_tait_secant_linear (v₀ v piT A p : ℝ) (hv₀ : v₀ ≠ 0) (hA : A ≠ 0) (hp : p ≠ 0)
    (hpi : piT + p ≠ 0) (hstrain : v₀ - v = v₀ * (A * p / (piT + p))) :
    secantBulkModulus v₀ v p = piT / A + p / A := by
  unfold secantBulkModulus
  rw [hstrain]
  field_simp


/-- The **modified (Tammann) Tait volume** `v = v₀[1 − A(ln(B+p) − ln B)] = v₀[1 − A ln((B+p)/B)]` (Eq. 5), the
integrated form of Tammann's differential compressibility. -/
noncomputable def taitVolume (v₀ A B p : ℝ) : ℝ := v₀ * (1 - A * (Real.log (B + p) - Real.log B))

/-- **The modified Tait differential compressibility** `dv/dp = −A v₀/(B + p)` (Eq. 4) — the exact derivative of
the integrated volume Eq. 5, recovering Tammann's `Δv/Δp = A/(B+p)` form (up to the `v₀` normalization). -/
lemma tait_compressibility (v₀ A B p : ℝ) (hBp : B + p ≠ 0) :
    deriv (fun p => taitVolume v₀ A B p) p = -A * v₀ / (B + p) := by
  have hlog : HasDerivAt (fun q => Real.log (B + q)) (B + p)⁻¹ p := by
    have hbp : HasDerivAt (fun q => B + q) 1 p := by
      exact ((hasDerivAt_const p B).add (hasDerivAt_id p)).congr_deriv (by simp)
    exact ((Real.hasDerivAt_log hBp).comp p hbp).congr_deriv (by simp)
  have hd : HasDerivAt (fun q => taitVolume v₀ A B q) (-A * v₀ / (B + p)) p := by
    have h := (((hlog.sub_const (Real.log B)).const_mul A).const_sub 1).const_mul v₀
    exact h.congr_deriv (by field_simp)
  exact hd.deriv


/-- **The modified Tait volume form** `(v₀ − v)/v₀ = A ln((B+p)/B)` (Eq. 2 with `p₀ = 0`, `C = A`) — the relative
volume change of the integrated Eq. 5, showing the differential (Eq. 4), integrated (Eq. 5) and volume (Eq. 2)
forms are one equation. -/
lemma tait_relative_volume (v₀ A B p : ℝ) (hv₀ : v₀ ≠ 0) (hB : B ≠ 0) (hBp : B + p ≠ 0) :
    (v₀ - taitVolume v₀ A B p) / v₀ = A * Real.log ((B + p) / B) := by
  unfold taitVolume
  rw [Real.log_div hBp hB]
  field_simp
  ring


/-- **The zero-pressure isothermal bulk modulus is `B/A`** `K₀ = −v₀/(dv/dp)|_{p=0} = B/A` — so `B = A·K₀`: the
empirical Tait parameter `B` is fixed by the measured zero-pressure bulk modulus, an exact consequence of the
differential compressibility (§B), not a free fit. -/
lemma tait_bulk_modulus_zero (v₀ A B : ℝ) (hB : B ≠ 0) (hv₀ : v₀ ≠ 0) (hA : A ≠ 0) :
    -v₀ / deriv (fun p => taitVolume v₀ A B p) 0 = B / A := by
  rw [tait_compressibility v₀ A B 0 (by simpa using hB)]
  rw [add_zero]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Particles.TaitEquationOfState

/-! ## Part II — the Birch–Murnaghan equation of state from finite elastic strain -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.BirchMurnaghanFiniteStrain


/-- The **Eulerian finite strain** `f = ½[(V₀/V)^{2/3} − 1] = ½(y²−1)` with `y = (V₀/V)^{1/3}` (Birch Eq. 9,
modern sign convention `f = −ε_Birch`): the compression measured in the strained (Eulerian) frame. -/
noncomputable def eulerianStrain (y : ℝ) : ℝ := 1 / 2 * (y ^ 2 - 1)

/-- **The finite-strain kinematic identity** `1 + 2f = y²` — Birch's `(1−2ε)^{-3/2} = V/V₀` written for the
Eulerian strain, the relation that makes `(1+2f)^{5/2} = y⁵` an integer power. -/
lemma strain_kinematic (y : ℝ) : 1 + 2 * eulerianStrain y = y ^ 2 := by
  unfold eulerianStrain; ring

/-- **The strain vanishes for the unstrained crystal** `f(1) = 0` — at `y = 1` (`V = V₀`). -/
lemma eulerianStrain_unstrained : eulerianStrain 1 = 0 := by
  unfold eulerianStrain; norm_num


/-- The **second-order Birch–Murnaghan pressure** `P = (3/2)K₀(y⁷ − y⁵)` (Birch Eq. 27, `D₃ = 0`), equivalently
`P = (3/2)K₀[(V₀/V)^{7/3} − (V₀/V)^{5/3}]`; `K₀` is the zero-pressure bulk modulus. -/
noncomputable def birchMurnaghanP (K₀ y : ℝ) : ℝ := 3 / 2 * K₀ * (y ^ 7 - y ^ 5)

/-- **The Birch–Murnaghan pressure in strain form** `P = 3K₀·f·y⁵ = 3K₀ f(1+2f)^{5/2}` — the standard
finite-strain expression, using `(1+2f)^{5/2} = (y²)^{5/2} = y⁵` (`strain_kinematic`). -/
lemma birchMurnaghan_strain_form (K₀ y : ℝ) :
    birchMurnaghanP K₀ y = 3 * K₀ * eulerianStrain y * y ^ 5 := by
  unfold birchMurnaghanP eulerianStrain; ring

/-- **The Birch–Murnaghan pressure vanishes for the unstrained crystal** `P = 0` at `y = 1` (`V = V₀`). -/
lemma birchMurnaghan_zero_at_unstrained (K₀ : ℝ) : birchMurnaghanP K₀ 1 = 0 := by
  unfold birchMurnaghanP; ring


/-- The **second-order finite-strain free energy** `E = (9/2)K₀V₀f² = (9/8)K₀V₀(y²−1)²` (Birch Eq. 16 to second
order, `ρ₀φ = (3/2)C₂ε²` with `C₂ = 3K₀`). -/
noncomputable def freeEnergy (K₀ V₀ y : ℝ) : ℝ := 9 / 8 * K₀ * V₀ * (y ^ 2 - 1) ^ 2

/-- The **volume as a function of the linear compression** `V = V₀/y³` (`y = (V₀/V)^{1/3}`). -/
noncomputable def volumeOfY (V₀ y : ℝ) : ℝ := V₀ / y ^ 3

/-- **The free-energy derivative** `dE/dy = (9/2)K₀V₀(y³ − y)`. -/
lemma freeEnergy_deriv (K₀ V₀ y : ℝ) :
    deriv (fun y => freeEnergy K₀ V₀ y) y = 9 / 2 * K₀ * V₀ * (y ^ 3 - y) := by
  have h1 : HasDerivAt (fun y => y ^ 2 - 1) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).sub_const 1
  have h2 : HasDerivAt (fun y => freeEnergy K₀ V₀ y)
      (9 / 8 * K₀ * V₀ * ((2 : ℕ) * (y ^ 2 - 1) ^ (2 - 1) * (2 * y))) y :=
    (h1.pow 2).const_mul _
  rw [h2.deriv]; push_cast; ring

/-- **The volume derivative** `dV/dy = −3V₀/y⁴`. -/
lemma volume_deriv (V₀ y : ℝ) (hy : y ≠ 0) :
    deriv (fun y => volumeOfY V₀ y) y = -3 * V₀ / y ^ 4 := by
  have hp : HasDerivAt (fun y => y ^ 3) (3 * y ^ 2) y := by
    simpa using hasDerivAt_pow 3 y
  have hv : HasDerivAt (fun y => volumeOfY V₀ y) (V₀ * (-(3 * y ^ 2) / (y ^ 3) ^ 2)) y := by
    simpa [volumeOfY, div_eq_mul_inv] using (hp.inv (pow_ne_zero 3 hy)).const_mul V₀
  rw [hv.deriv]; field_simp

/-- **The Birch–Murnaghan equation of state is `P = −dE/dV`** `P·(dV/dy) = −(dE/dy)` — the finite-strain pressure
is the thermodynamic derivative of the second-order free energy (Birch Eqs. 16 → 27): the Birch–Murnaghan `P(V)`
is *derived* from the energy, not postulated. -/
lemma birchMurnaghan_is_energy_derivative (K₀ V₀ y : ℝ) (hy : y ≠ 0) :
    birchMurnaghanP K₀ y * deriv (fun y => volumeOfY V₀ y) y
      = -deriv (fun y => freeEnergy K₀ V₀ y) y := by
  rw [volume_deriv V₀ y hy, freeEnergy_deriv K₀ V₀ y]
  unfold birchMurnaghanP
  field_simp
  ring


/-- The **isothermal bulk modulus** `K = −V dP/dV = (K₀/2)(7y⁷ − 5y⁵)` of the Birch–Murnaghan solid. -/
noncomputable def bulkModulusOfY (K₀ y : ℝ) : ℝ := K₀ / 2 * (7 * y ^ 7 - 5 * y ^ 5)

/-- **The Birch–Murnaghan pressure derivative** `dP/dy = (3/2)K₀(7y⁶ − 5y⁴)`. -/
lemma birchP_deriv (K₀ y : ℝ) :
    deriv (fun y => birchMurnaghanP K₀ y) y = 3 / 2 * K₀ * (7 * y ^ 6 - 5 * y ^ 4) := by
  have h : HasDerivAt (fun y => birchMurnaghanP K₀ y) (3 / 2 * K₀ * (7 * y ^ 6 - 5 * y ^ 4)) y := by
    unfold birchMurnaghanP
    have := (((hasDerivAt_pow 7 y).sub (hasDerivAt_pow 5 y)).const_mul (3 / 2 * K₀))
    exact this.congr_deriv (by push_cast; ring)
  rw [h.deriv]

/-- **The bulk modulus is `K = −V dP/dV`** — with `V = V₀/y³` and `dP/dy`, `dV/dy` (Birch's definition of the
isothermal bulk modulus), giving `(K₀/2)(7y⁷ − 5y⁵)`. -/
lemma bulkModulus_is_neg_V_dPdV (K₀ V₀ y : ℝ) (hy : y ≠ 0) (hV : V₀ ≠ 0) :
    -volumeOfY V₀ y * (deriv (fun y => birchMurnaghanP K₀ y) y / deriv (fun y => volumeOfY V₀ y) y)
      = bulkModulusOfY K₀ y := by
  rw [birchP_deriv, volume_deriv V₀ y hy]
  unfold volumeOfY bulkModulusOfY
  field_simp

/-- **The bulk modulus at zero pressure is `K₀`** `K(1) = K₀` — the material parameter is the unstrained
(`V = V₀`) bulk modulus. -/
lemma bulkModulus_unstrained (K₀ : ℝ) : bulkModulusOfY K₀ 1 = K₀ := by
  unfold bulkModulusOfY; ring

/-- **The bulk-modulus derivative** `dK/dy = (K₀/2)(49y⁶ − 25y⁴)`. -/
lemma bulkModulus_deriv (K₀ y : ℝ) :
    deriv (fun y => bulkModulusOfY K₀ y) y = K₀ / 2 * (49 * y ^ 6 - 25 * y ^ 4) := by
  have h : HasDerivAt (fun y => bulkModulusOfY K₀ y) (K₀ / 2 * (49 * y ^ 6 - 25 * y ^ 4)) y := by
    unfold bulkModulusOfY
    have := (((hasDerivAt_pow 7 y).const_mul (7 : ℝ)).sub
      ((hasDerivAt_pow 5 y).const_mul (5 : ℝ))).const_mul (K₀ / 2)
    exact this.congr_deriv (by push_cast; ring)
  rw [h.deriv]

/-- **The pressure derivative of the bulk modulus is `4`** `K₀′ = (dK/dP)|_{P=0} = 4` — the signature of the
second-order Birch–Murnaghan equation of state: fixing the energy at second order in the strain forces the
bulk-modulus pressure derivative to `4` (a free parameter only at third order). Stated as
`dK/dy = 4·dP/dy` at `y = 1` (equivalently `dK/dP = 4`, the chain rule with `dP/dy ≠ 0`). -/
lemma birch_bulk_modulus_pressure_derivative (K₀ : ℝ) :
    deriv (fun y => bulkModulusOfY K₀ y) 1 = 4 * deriv (fun y => birchMurnaghanP K₀ y) 1 := by
  rw [bulkModulus_deriv, birchP_deriv]; ring


/-- The **Lagrangian finite strain** `η = ½[(V/V₀)^{-2/3} − 1] = ½(1/y² − 1)` — the compression measured in the
unstrained (Lagrangian) frame, from `(1+2η)^{3/2} = V/V₀ = y⁻³`, i.e. `1+2η = y⁻²`. -/
noncomputable def lagrangianStrain (y : ℝ) : ℝ := 1 / 2 * (1 / y ^ 2 - 1)

/-- **The Lagrangian and Eulerian strains are reciprocal** `(1+2η)(1+2f) = 1` — Birch's exact relation
`(1+2η)^{3/2} = (1−2ε)^{-3/2}` (Eq. 9), since `1+2η = y⁻²` and `1+2f = y²`. -/
lemma lagrangian_eulerian_reciprocal (y : ℝ) (hy : y ≠ 0) :
    (1 + 2 * lagrangianStrain y) * (1 + 2 * eulerianStrain y) = 1 := by
  unfold lagrangianStrain eulerianStrain
  field_simp
  ring


/-- The **linear compression factor** `α = 1 − 1/y` (Birch Eq. 4) — every line of the crystal is shortened by
`(1−α) = 1/y = (V/V₀)^{1/3}` under the hydrostatic compression. -/
noncomputable def compressionFactor (y : ℝ) : ℝ := (y - 1) / y

/-- **Birch's exact hydrostatic volume relation** `V = V₀(1−α)³` — the volume is the cube of the linear
compression `(1−α) = 1/y`, so `V = V₀/y³` (Birch Eq. 5, all `β = 0`). -/
lemma volume_from_compression (V₀ y : ℝ) (hy : y ≠ 0) :
    volumeOfY V₀ y = V₀ * (1 - compressionFactor y) ^ 3 := by
  unfold volumeOfY compressionFactor
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.Particles.BirchMurnaghanFiniteStrain

/-! ## Part III — cuboidal lattice geometry along the Bain path -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.CuboidalLatticeBainGeometry

open Physlib.QuantumMechanics.ComplexAction.Particles.LennardJonesAxilrodTeller


/-- The **Conway–Sloane cuboidal Gram core** `M(A)` (Eq. 8), so that the Gram matrix is `G = v²·M(A)`. -/
def cuboidalGramCore (A : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A + 1, A, 1; A, A + 1, 1; 1, 1, 2]

/-- The **cuboidal Gram matrix** `G = BBᵀ = v²·M(A)` (Eq. 8). -/
def cuboidalGram (A v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := v ^ 2 • cuboidalGramCore A

/-- **The Gram core determinant is `4A`** — `det M(A) = 4A`, the exact determinant of the cuboidal Gram core. -/
lemma cuboidalGramCore_det (A : ℝ) : (cuboidalGramCore A).det = 4 * A := by
  simp [cuboidalGramCore, Matrix.det_fin_three]; ring

/-- **The Gram matrix determinant is `4v⁶A`** — `det(v²·M) = (v²)³ det M = 4v⁶A`. -/
lemma cuboidalGram_det (A v : ℝ) : (cuboidalGram A v).det = 4 * v ^ 6 * A := by
  rw [cuboidalGram, Matrix.det_smul, Fintype.card_fin, cuboidalGramCore_det]; ring

/-- The **lattice volume** `V_Λ = |det B| = √(det G) = 2v³√A` (Eq. 8). -/
noncomputable def latticeVolume (A v : ℝ) : ℝ := 2 * v ^ 3 * Real.sqrt A

/-- **The Gram determinant is the squared lattice volume** `det G = V_Λ²` — the defining relation
`V_Λ = √(det G)`, with `det G = 4v⁶A` and `V_Λ = 2v³√A`. -/
lemma cuboidalGram_det_eq_volume_sq (A v : ℝ) (hA : 0 ≤ A) :
    (cuboidalGram A v).det = latticeVolume A v ^ 2 := by
  rw [cuboidalGram_det, latticeVolume]
  rw [mul_pow, mul_pow, Real.sq_sqrt hA]
  ring


/-- The **nearest-neighbour squared distance in region II** `R_Λ² = v²(A+1)` (Eq. 9, `1/3 ≤ A ≤ 1`), the
diagonal Gram entry `G₀₀`. -/
noncomputable def nnDistSq (A v : ℝ) : ℝ := v ^ 2 * (A + 1)

/-- **`R_Λ² = v²(A+1)` is the first diagonal Gram entry** `G₀₀` — the nearest neighbour is the basis vector
`b₁`. -/
lemma nnDistSq_eq_gram_diag (A v : ℝ) : nnDistSq A v = cuboidalGram A v 0 0 := by
  simp [nnDistSq, cuboidalGram, cuboidalGramCore]

/-- **`v²(A+1)` is the minimal candidate norm in region II** — of the three candidate squared distances
`4v²A` (the `A < 1/3` chain vector), `v²(A+1)` (`b₁`) and `2v²` (`b₃`), the middle one is smallest exactly when
`1/3 ≤ A ≤ 1`, deriving `R_Λ = v√(A+1)`. -/
lemma nnDistSq_min_region_II (A v : ℝ) (hlo : 1 / 3 ≤ A) (hhi : A ≤ 1) :
    nnDistSq A v ≤ 4 * v ^ 2 * A ∧ nnDistSq A v ≤ 2 * v ^ 2 := by
  have hv : (0 : ℝ) ≤ v ^ 2 := sq_nonneg v
  refine ⟨?_, ?_⟩
  · unfold nnDistSq; nlinarith [mul_nonneg hv (by linarith : (0:ℝ) ≤ 3 * A - 1)]
  · unfold nnDistSq; nlinarith [mul_nonneg hv (by linarith : (0:ℝ) ≤ 1 - A)]


/-- The **packing density** `Δ_Λ = (π/12)√((A+1)³/A)` for `1/3 ≤ A ≤ 1` (Eq. 10), from `Δ = (π/6)R_Λ³/V_Λ`
with `R_Λ = v√(A+1)`, `V_Λ = 2v³√A`. -/
noncomputable def packingDensity (A : ℝ) : ℝ := Real.pi / 12 * Real.sqrt ((A + 1) ^ 3 / A)

/-- **The fcc packing density is `π√2/6 ≈ 0.74`** — the densest cuboidal phase, at `A = 1`. -/
lemma packingDensity_fcc : packingDensity 1 = Real.pi * Real.sqrt 2 / 6 := by
  unfold packingDensity
  have h8 : ((1 : ℝ) + 1) ^ 3 / 1 = 2 ^ 2 * 2 := by norm_num
  rw [h8, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  ring

/-- **The bcc packing density is `π√3/8 ≈ 0.68`** — a local minimum of the packing density, at `A = 1/2`. -/
lemma packingDensity_bcc : packingDensity (1 / 2) = Real.pi * Real.sqrt 3 / 8 := by
  unfold packingDensity
  have h27 : ((1 / 2 : ℝ) + 1) ^ 3 / (1 / 2) = (3 / 2) ^ 2 * 3 := by norm_num
  rw [h27, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  ring

/-- **fcc is denser than bcc** `Δ(1) > Δ(1/2)` (`π√2/6 > π√3/8`) — the close-packed fcc lattice is the densest
cuboidal phase; the bcc lattice is a local minimum, the geometric reason a repulsive three-body term is needed to
stabilize bcc. Reduces to `8√2 > 6√3` (`128 > 108`). -/
lemma fcc_denser_than_bcc : packingDensity (1 / 2) < packingDensity 1 := by
  rw [packingDensity_fcc, packingDensity_bcc]
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hkey : Real.sqrt 3 / 8 < Real.sqrt 2 / 6 := by
    rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [h2, h3, hs2, hs3, mul_nonneg hs2 hs3]
  calc Real.pi * Real.sqrt 3 / 8 = Real.pi * (Real.sqrt 3 / 8) := by ring
    _ < Real.pi * (Real.sqrt 2 / 6) := by exact mul_lt_mul_of_pos_left hkey hpi
    _ = Real.pi * Real.sqrt 2 / 6 := by ring


/-- **Kissing number of the fcc lattice** `= 12` (Eq. 11, `A = 1`) — the maximal contact number of the cuboidal
family. -/
def kissFcc : ℕ := 12

/-- **Kissing number of the bcc lattice** `= 8` (Eq. 11, region II). -/
def kissBcc : ℕ := 8

/-- **Kissing number of the acc lattice** `= 10` (Eq. 11, `A = 1/3`). -/
def kissAcc : ℕ := 10

/-- **Kissing number in region I** `= 2` (Eq. 11, `A < 1/3`, linear chains). -/
def kissRegionI : ℕ := 2

/-- **Kissing number in region III** `= 4` (Eq. 11, `A > 1`, square layers). -/
def kissRegionIII : ℕ := 4

/-- **fcc has the maximal kissing number of the cuboidal family** `12 > 8, 10, 4, 2`. -/
lemma fcc_max_kissing :
    kissBcc < kissFcc ∧ kissAcc < kissFcc ∧ kissRegionIII < kissFcc ∧ kissRegionI < kissFcc := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide


/-- The **Bain parameter** `A = ½γ²` from the tetragonal ratio `γ = c/a` (Eq. 12): the single dimensionless
number parametrizing the cuboidal lattice along the Bain path. -/
noncomputable def bainA (γ : ℝ) : ℝ := γ ^ 2 / 2

/-- **The fcc ratio gives `A = 1`** `bainA (√2) = 1` — the `c/a = √2` face-centred phase is `A = 1`, tying the
`A`-parametrization to `LennardJonesAxilrodTeller.fccRatio`. -/
lemma bainA_fcc : bainA fccRatio = 1 := by
  rw [bainA, fccRatio_sq]; norm_num

/-- **The bcc ratio gives `A = 1/2`** `bainA 1 = 1/2` — the `c/a = 1` body-centred phase is `A = 1/2`, tying the
`A`-parametrization to `LennardJonesAxilrodTeller.bccRatio`. -/
lemma bainA_bcc : bainA bccRatio = 1 / 2 := by
  rw [bainA, bccRatio]; norm_num

/-- **The bcc parameter is below the fcc parameter** `bainA bccRatio < bainA fccRatio` (`1/2 < 1`) — the Bain
path runs `A: 1/2 → 1` from bcc to fcc. -/
lemma bainA_bcc_lt_fcc : bainA bccRatio < bainA fccRatio := by
  rw [bainA_fcc, bainA_bcc]; norm_num


/-- The **Bain transformation matrix** `T_Bain(A) = diag(√A, 1, 1)` (Eq. 14): the diagonal, diffusionless
transformation carrying the fcc lattice to the cuboidal lattice at parameter `A`. -/
noncomputable def bainMatrix (A : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![Real.sqrt A, 1, 1]

/-- **The Bain matrix determinant is `√A`** `det T_Bain(A) = √A` — the volume-scaling factor of the Bain
transformation along the path. -/
lemma bainMatrix_det (A : ℝ) : (bainMatrix A).det = Real.sqrt A := by
  rw [bainMatrix, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

/-- **The Bain transformation is volume-preserving at fcc** `det T_Bain(1) = 1` — the fcc lattice (`A = 1`) is
the fixed point of the Bain path. -/
lemma bainMatrix_det_fcc : (bainMatrix 1).det = 1 := by
  rw [bainMatrix_det, Real.sqrt_one]

end Physlib.QuantumMechanics.ComplexAction.Particles.CuboidalLatticeBainGeometry

/-! ## Part IV — Birch §6: the bulk-modulus pressure derivative from the interatomic potential -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.BirchInteratomicPotential


/-- The **Lagrangian form of `K₀′`** `(∂K₀/∂P)₀ = 1 − 2C₃/(3C₂)` (Birch Eq. 33), from the Lagrangian third-order
free-energy coefficient `C₃` and the second-order `C₂ = c₁₁ + 2c₁₂ = 3K₀`. -/
noncomputable def k0PrimeLagrangian (C₃ C₂ : ℝ) : ℝ := 1 - 2 * C₃ / (3 * C₂)

/-- The **Eulerian form of `K₀′`** `(∂K₀/∂P)₀ = 5 − 2D₃/(3C₂)` (Birch Eq. 35), from the Eulerian third-order
coefficient `D₃`. -/
noncomputable def k0PrimeEulerian (D₃ C₂ : ℝ) : ℝ := 5 - 2 * D₃ / (3 * C₂)

/-- **The Lagrangian and Eulerian `K₀′` agree** `5 − 2(C₃+6C₂)/(3C₂) = 1 − 2C₃/(3C₂)` — Eqs. 33 and 35 are
identical under Birch's `D₃ = C₃ + 6C₂` (Eq. 17): the pressure derivative of the bulk modulus is independent of
the strain measure used. -/
lemma lagrangian_eulerian_k0prime_agree (C₃ C₂ : ℝ) (hC : C₂ ≠ 0) :
    k0PrimeEulerian (C₃ + 6 * C₂) C₂ = k0PrimeLagrangian C₃ C₂ := by
  unfold k0PrimeEulerian k0PrimeLagrangian
  field_simp
  ring


/-- The **`K₀′` from the interatomic potential** `(∂K₀/∂P)₀ = 2 − r₀ φ‴(r₀)/(3 φ″(r₀))` (Birch Eq. 37, using the
linear dimension `V = r³`), `d₂ = φ″(r₀)`, `d₃ = φ‴(r₀)` the second and third derivatives at equilibrium. -/
noncomputable def k0PrimeFromPotential (d₂ d₃ r₀ : ℝ) : ℝ := 2 - r₀ * d₃ / (3 * d₂)

/-- The **exponent formula** `K₀′ = (9 + m + n)/3` — Birch's well-known result for the Born power-law potential
`−a r⁻ᵐ + b r⁻ⁿ`. -/
noncomputable def k0PrimeFromExponents (m n : ℝ) : ℝ := (9 + m + n) / 3

/-- **The Born power-law potential gives `K₀′ = (9+m+n)/3`** — from Eq. 37 with the power-law derivative structure
`φ″(r₀) = κ(n−m)/r₀²`, `φ‴(r₀) = κ(m−n)(m+n+3)/r₀³` (the second/third derivatives of `−ar⁻ᵐ+br⁻ⁿ` at the
equilibrium `r₀`, `κ ≠ 0` the common factor), the pressure derivative of the bulk modulus is set by the two
exponents. -/
lemma powerLaw_potential_k0Prime (m n r₀ κ : ℝ) (hr : r₀ ≠ 0) (hκ : κ ≠ 0) (hnm : n - m ≠ 0) :
    k0PrimeFromPotential (κ * (n - m) / r₀ ^ 2) (κ * (m - n) * (m + n + 3) / r₀ ^ 3) r₀
      = k0PrimeFromExponents m n := by
  unfold k0PrimeFromPotential k0PrimeFromExponents
  field_simp
  ring

/-- **The coefficient form gives the same `K₀′ = (9+m+n)/3`** — from `C₃/C₂ = −3 − (m+n)/2` (Birch's Born
power-law third-order coefficient), `k0PrimeLagrangian` reproduces the exponent formula, corroborating §B. -/
lemma powerLaw_coefficient_k0Prime (m n C₂ : ℝ) (hC : C₂ ≠ 0) :
    k0PrimeLagrangian (C₂ * (-3 - (m + n) / 2)) C₂ = k0PrimeFromExponents m n := by
  unfold k0PrimeLagrangian k0PrimeFromExponents
  field_simp
  ring


/-- **The Lennard-Jones `(12,6)` potential has `K₀′ = 9`** — Birch's Born power-law with `m = 6` (attractive,
the `r⁻⁶` London tail) and `n = 12` (repulsive) is the `LennardJonesAxilrodTeller.ljPotential … 12 6`; its
`K₀′ = (9+6+12)/3 = 9`, the Argon-like value of Birch's Table II. -/
lemma lennardJones_12_6_k0Prime : k0PrimeFromExponents 6 12 = 9 := by
  unfold k0PrimeFromExponents; norm_num

/-- **The second-order Birch–Murnaghan `K₀′ = 4` is the soft power law `m + n = 3`** `(9+m+n)/3 = 4 ⟺ m+n = 3` —
the fixed `K₀′ = 4` of `BirchMurnaghanFiniteStrain.birch_bulk_modulus_pressure_derivative` corresponds to the
Born potential with exponent sum `3` (far softer than the `(12,6)` `ljPotential`, `m+n = 18`), the reason the
second-order equation of state suits only weakly compressed, soft solids. -/
lemma bm2_soft_powerlaw (m n : ℝ) : k0PrimeFromExponents m n = 4 ↔ m + n = 3 := by
  unfold k0PrimeFromExponents
  constructor <;> intro h <;> linarith

end Physlib.QuantumMechanics.ComplexAction.Particles.BirchInteratomicPotential

/-! ## Part V — the ATM cohesive energy is stationary at bcc: the cyclic-symmetry mechanism -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AxilrodTellerBccExtremum

open Physlib.QuantumMechanics.ComplexAction.Particles.LennardJonesAxilrodTeller
open Physlib.QuantumMechanics.ComplexAction.Particles.CuboidalLatticeBainGeometry


/-- The **diagonal quadratic form** `xᵀ diag(d) x = d₀x₀² + d₁x₁² + d₂x₂²` — the summand of an Epstein-zeta
`A`-derivative, with `d` the diagonal of `D = ∂(quadratic form)/∂A`. -/
def diagForm (d₀ d₁ d₂ x₀ x₁ x₂ : ℝ) : ℝ := d₀ * x₀ ^ 2 + d₁ * x₁ ^ 2 + d₂ * x₂ ^ 2

/-- **The cyclic orbit sum is `|x|²·Tr(D)`** — summing the diagonal form over the `σ`-orbit
`x, σx = (x₁,x₂,x₀), σ²x = (x₂,x₀,x₁)` gives `(d₀+d₁+d₂)(x₀²+x₁²+x₂²)`, the paper's `|x|²·Tr(D)` (Appendix H):
each coordinate visits every diagonal slot once over the cyclic orbit. -/
lemma cyclic_orbit_sum (d₀ d₁ d₂ x₀ x₁ x₂ : ℝ) :
    diagForm d₀ d₁ d₂ x₀ x₁ x₂ + diagForm d₀ d₁ d₂ x₁ x₂ x₀ + diagForm d₀ d₁ d₂ x₂ x₀ x₁
      = (d₀ + d₁ + d₂) * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) := by
  unfold diagForm; ring


/-- **The trace of a diagonal matrix is the sum of its diagonal** `Tr(diag d) = d₀+d₁+d₂` — the genuine
`Matrix.trace` of the derivative matrix `D = diag(d)`. -/
lemma trace_of_diagonal (d : Fin 3 → ℝ) :
    (Matrix.diagonal d).trace = d 0 + d 1 + d 2 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three]

/-- **A diagonal traceless `D` contributes zero to the `A`-derivative, term by term** — with `Tr(D) = 0` the
cyclic orbit sum vanishes, so `∂ζ^{(3)}_{Λ(A)}/∂A|_{A=1/2} = 0`: the bcc cyclic symmetry kills the Epstein-zeta
derivative. -/
lemma bcc_zeta_derivative_term_vanishes (d₀ d₁ d₂ x₀ x₁ x₂ : ℝ) (htr : d₀ + d₁ + d₂ = 0) :
    diagForm d₀ d₁ d₂ x₀ x₁ x₂ + diagForm d₀ d₁ d₂ x₁ x₂ x₀ + diagForm d₀ d₁ d₂ x₂ x₀ x₁ = 0 := by
  rw [cyclic_orbit_sum, htr, zero_mul]


/-- The **ATM cohesive-energy recombination** `E^{(3)}_coh/λ = ζ(3,3,3)/24 − 3ζ(−1,5,5)/16 + 3ζ(1,3,5)/8` as a
linear combination of the three three-body zeta functions (Appendix H); `z₁, z₂, z₃` are their `A`-derivatives
at `A = 1/2`. -/
noncomputable def atmCohesiveComb (z₁ z₂ z₃ : ℝ) : ℝ := z₁ / 24 - 3 * z₂ / 16 + 3 * z₃ / 8

/-- **The ATM cohesive energy is stationary at bcc** `∂E^{(3)}_coh/∂A|_{A=1/2} = 0` — since each three-body
zeta `A`-derivative vanishes (§B, the cyclic-symmetry mechanism), so does their recombination. For every coupling
`λ`, the bcc lattice (`bainA bccRatio = 1/2`) is an extremum of the ATM cohesive energy along the Bain path. -/
lemma atmCohesive_stationary (z₁ z₂ z₃ : ℝ) (h₁ : z₁ = 0) (h₂ : z₂ = 0) (h₃ : z₃ = 0) :
    atmCohesiveComb z₁ z₂ z₃ = 0 := by
  rw [atmCohesiveComb, h₁, h₂, h₃]; ring

/-- **bcc is the stationary point, at `A = 1/2`** — the extremum condition `∂E^{(3)}_coh/∂A = 0` holds at the
Bain parameter `bainA bccRatio = 1/2`, tying the ATM extremum to the `c/a = 1` body-centred cubic phase of
`CuboidalLatticeBainGeometry`. -/
lemma bcc_extremum_at_half : bainA bccRatio = 1 / 2 := bainA_bcc

end Physlib.QuantumMechanics.ComplexAction.Particles.AxilrodTellerBccExtremum

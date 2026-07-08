/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The anomalous magnetic moment of the electron (Bennett §VI)

Formalizes the **anomalous magnetic moment** of A. F. Bennett, *First Quantized Electrodynamics*,
arXiv:1406.0750v3, §VI ("One–loop corrections"). Bennett shows that, after the propagator
substitution (84), the vertex of the parametrized Dirac equation is modified by a factor `F` that is
a sum of the four standard Feynman diagrams (vacuum polarization, mass-counterterm, self-mass, vertex
correction), each with symmetry factor `S = 1`; these reduce *precisely* to the Bjorken–Drell
wavenumber integrals, yielding the anomalous magnetic moment "to leading order in the fine structure
constant" — Schwinger's `a = α/(2π)`.

Bennett imports the explicit value from Bjorken–Drell, so the genuinely formalizable content is the
**structure** the anomalous moment lives in, which is built here on the repo's Dirac gamma matrices
(`Physlib.Relativity.CliffordAlgebra`):

* **the Pauli spin tensor** `σ^{μν} = (i/2)[γ^μ, γ^ν]` (`spinTensor`) — the relativistic spin /
  magnetic-moment operator that the anomalous form factor `F₂(q²)` multiplies. Its `z`-component
  `σ^{12} = iγ¹γ²` (`spinTensor_12_eq`) is an **involution** `(σ^{12})² = 1`
  (`spinTensor_12_involution`): the magnetic-moment operator has spin eigenvalues `±1`, and it
  **commutes with the Dirac `β`** (`spinMoment_comm_diracBeta`), so spin is compatible with the
  Dirac energy sign;
* **the Gordon-underlying Clifford decomposition** `γ^μγ^ν = η^{μν}·1 − iσ^{μν}`
  (`gamma_clifford_decomp`, from the anticommutator `{γ^μ,γ^ν} = 2η^{μν}`, `gamma_anticomm`): the
  vertex `γ^μ` splits into a **symmetric** part (the metric `η^{μν}`, giving the charge form factor
  `F₁` via the Gordon identity) and an **antisymmetric** part (the spin tensor `σ^{μν}`, giving the
  magnetic moment `F₂`);
* **the g-factor and Schwinger's value** (`gFactor`, `schwingerAnomaly`): `g = 2(1 + a)` with the
  tree-level Dirac value `g = 2` (`gFactor_dirac`, `a = 0`) and the one-loop correction
  `a = α/(2π)` giving `g = 2 + α/π` (`gFactor_schwinger`). The magnetic moment in Bohr magnetons is
  `μ/μ_B = g/2 = 1 + a` (`magneticMomentRatio`).

So `a = 0 ⟺ g = 2` is the Dirac electron (no radiative correction); the anomalous moment `a = α/(2π)`
is the leading vertex correction (`F₂(0)`) Bennett's four-diagram factor `F` reduces to.

* **§A — the Pauli spin tensor** (`spinTensor`, `spinTensor_antisymm`, `spinTensor_12_involution`,
  `spinMoment_comm_diracBeta`).
* **§B — the Clifford / Gordon decomposition** (`gamma_anticomm`, `gamma_clifford_decomp`).
* **§C — the g-factor and Schwinger anomaly** (`gFactor`, `gFactor_dirac`, `schwingerAnomaly`,
  `gFactor_schwinger`, `magneticMomentRatio`).
* **§D — the unification** (`anomalous_moment_structure`).

## References

* A. F. Bennett, arXiv:1406.0750v3, §VI. J. Schwinger, Phys. Rev. **73** (1948) 416 (`a = α/2π`).
  J. D. Bjorken, S. D. Drell, *Relativistic Quantum Mechanics* (Eqs 8.8, 8.34, 8.49).
* Repo dependencies: `Physlib.Relativity.CliffordAlgebra` (`γ0..γ3`, anticommutators),
  `Dirac.FourSpinorDiracHamiltonian` (`diracBeta = γ⁰`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

open Complex spaceTime
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

noncomputable section

/-! ## §A — the Pauli spin tensor `σ^{μν}` (the magnetic-moment operator) -/

/-- **The Pauli spin tensor** `σ^{μν} = (i/2)(γ^μγ^ν − γ^νγ^μ) = (i/2)[γ^μ, γ^ν]` — the relativistic
spin / magnetic-moment operator that the anomalous form factor `F₂(q²)` multiplies at the QED vertex. -/
def spinTensor (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (I / 2) • (γ μ * γ ν - γ ν * γ μ)

/-- **The spin tensor is antisymmetric** `σ^{μν} = −σ^{νμ}`. -/
theorem spinTensor_antisymm (μ ν : Fin 4) : spinTensor μ ν = - spinTensor ν μ := by
  simp only [spinTensor, ← smul_neg, neg_sub]

/-- **The diagonal spin tensor vanishes** `σ^{μμ} = 0`. -/
theorem spinTensor_self (μ : Fin 4) : spinTensor μ μ = 0 := by simp [spinTensor]

/-- **The `z`-magnetic-moment operator is `σ^{12} = iγ¹γ²`** (the spatial spin `Σ³` in the Dirac
representation). -/
theorem spinTensor_12_eq : spinTensor 1 2 = I • (γ1 * γ2) := by
  show (I / 2) • (γ1 * γ2 - γ2 * γ1) = I • (γ1 * γ2)
  rw [γ2_mul_γ1, sub_neg_eq_add, smul_add, ← add_smul, show I / 2 + I / 2 = I from by ring]

/-- The product `γ¹γ²γ¹γ² = −1` (an intermediate Clifford identity). -/
theorem g1g2_sq : γ1 * γ2 * (γ1 * γ2) = -1 := by
  have e : γ1 * γ2 * (γ1 * γ2) = γ1 * (γ2 * γ1) * γ2 := by noncomm_ring
  rw [e, γ2_mul_γ1]
  have e2 : γ1 * -(γ1 * γ2) * γ2 = -(γ1 * γ1 * (γ2 * γ2)) := by noncomm_ring
  rw [e2, γ1_mul_γ1, γ2_mul_γ2]; simp

/-- **[The magnetic-moment operator is an involution] `(σ^{12})² = 1`** — the spin operator has
eigenvalues `±1`, the two spin states the magnetic moment distinguishes. -/
theorem spinTensor_12_involution : spinTensor 1 2 * spinTensor 1 2 = 1 := by
  rw [spinTensor_12_eq, smul_mul_smul_comm, Complex.I_mul_I, g1g2_sq]; simp

/-- **[Spin compatible with the Dirac energy sign] `[σ^{12}, β] = 0`** — the magnetic-moment operator
commutes with the Dirac `β = γ⁰` (both `γ¹` and `γ²` anticommute with `γ⁰`, so their product
commutes), so spin and the Dirac energy sign are simultaneously diagonalizable. -/
theorem spinMoment_comm_diracBeta : spinTensor 1 2 * diracBeta = diracBeta * spinTensor 1 2 := by
  rw [spinTensor_12_eq, diracBeta, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  have e : γ1 * γ2 * γ0 = γ1 * (γ2 * γ0) := by noncomm_ring
  rw [e, γ2_mul_γ0, mul_neg, ← mul_assoc, γ1_mul_γ0, neg_mul, neg_neg, mul_assoc]

/-! ## §B — the Clifford / Gordon decomposition (charge + magnetic split) -/

/-- **The Minkowski metric** `η^{μν} = diag(1, −1, −1, −1)` matching the gamma-matrix signature
(`γ⁰² = 1`, `γⁱ² = −1`). -/
def minkowskiEta (μ ν : Fin 4) : ℂ := if μ = ν then (if μ = 0 then 1 else -1) else 0

/-- **The Clifford anticommutation relation** `{γ^μ, γ^ν} = 2η^{μν}·1`. -/
theorem gamma_anticomm (μ ν : Fin 4) :
    γ μ * γ ν + γ ν * γ μ = (2 * minkowskiEta μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases μ <;> fin_cases ν <;>
    simp only [γ, minkowskiEta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, γ0_mul_γ0, γ1_mul_γ1, γ2_mul_γ2, γ3_mul_γ3, γ1_mul_γ0, γ2_mul_γ0,
      γ3_mul_γ0, γ2_mul_γ1, γ3_mul_γ1, γ3_mul_γ2, reduceIte] <;>
    simp [two_smul]

/-- **[Gordon-underlying decomposition] `γ^μγ^ν = η^{μν}·1 − iσ^{μν}`.** The vertex product splits
into a **symmetric** part — the metric `η^{μν}` (giving the charge form factor `F₁` via the Gordon
identity) — and an **antisymmetric** part — the spin tensor `σ^{μν}` (giving the magnetic moment
`F₂`, the anomalous-moment structure). -/
theorem gamma_clifford_decomp (μ ν : Fin 4) :
    γ μ * γ ν = (minkowskiEta μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - I • spinTensor μ ν := by
  have hI : I • spinTensor μ ν = (-(1 / 2 : ℂ)) • (γ μ * γ ν - γ ν * γ μ) := by
    rw [spinTensor, smul_smul, ← mul_div_assoc, Complex.I_mul_I]; norm_num
  rw [hI, show γ ν * γ μ
        = (2 * minkowskiEta μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - γ μ * γ ν from
      eq_sub_of_add_eq (by rw [add_comm]; exact gamma_anticomm μ ν)]
  module

/-! ## §C — the g-factor and the Schwinger anomalous moment -/

/-- **The gyromagnetic g-factor** `g = 2(1 + a)` in terms of the anomalous moment `a`. -/
def gFactor (a : ℝ) : ℝ := 2 * (1 + a)

/-- **[Tree-level Dirac value] `g = 2`** at `a = 0` — the Dirac electron, no radiative correction. -/
theorem gFactor_dirac : gFactor 0 = 2 := by rw [gFactor]; ring

/-- **Schwinger's one-loop anomalous magnetic moment** `a = α/(2π)` — the leading-order value
Bennett's four-diagram vertex factor `F` (its `F₂(0)` part) reduces to. -/
def schwingerAnomaly (α : ℝ) : ℝ := α / (2 * Real.pi)

/-- **[Schwinger one-loop g-factor] `g = 2 + α/π`** — the g-factor with the leading anomalous
moment `a = α/(2π)`. -/
theorem gFactor_schwinger (α : ℝ) : gFactor (schwingerAnomaly α) = 2 + α / Real.pi := by
  rw [gFactor, schwingerAnomaly]
  field_simp

/-- **The magnetic moment in Bohr magnetons** `μ/μ_B = g/2 = 1 + a` — the total magnetic moment is
the Dirac value `μ_B` plus the anomalous part `a·μ_B`. -/
def magneticMomentRatio (a : ℝ) : ℝ := 1 + a

/-- **`g = 2·(μ/μ_B)`** — the g-factor is twice the magnetic moment in Bohr magnetons. -/
theorem gFactor_eq_two_mul_ratio (a : ℝ) : gFactor a = 2 * magneticMomentRatio a := by
  rw [gFactor, magneticMomentRatio]

/-! ## §D — the unification -/

/-- **[The anomalous magnetic moment, structurally] one Pauli-tensor + g-factor picture.** The
magnetic-moment operator `σ^{12}` is an **involution** (spin eigenvalues `±1`,
`spinTensor_12_involution`) **compatible with the Dirac energy sign** (`spinMoment_comm_diracBeta`);
the vertex `γ^μγ^ν` decomposes into the metric (charge `F₁`) plus the spin tensor (magnetic `F₂`,
`gamma_clifford_decomp`); and the g-factor is `g = 2(1 + a)`, equal to the **Dirac value `2`** at
`a = 0` (`gFactor_dirac`) and to `2 + α/π` at the **Schwinger value `a = α/(2π)`**
(`gFactor_schwinger`). The anomalous moment `a` is precisely the `F₂(0)` encoded in the
antisymmetric, `σ^{μν}` part of Bennett's four-diagram vertex factor `F`. -/
theorem anomalous_moment_structure (μ ν : Fin 4) (α : ℝ) :
    spinTensor 1 2 * spinTensor 1 2 = 1
      ∧ spinTensor 1 2 * diracBeta = diracBeta * spinTensor 1 2
      ∧ γ μ * γ ν = (minkowskiEta μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - I • spinTensor μ ν
      ∧ gFactor 0 = 2
      ∧ gFactor (schwingerAnomaly α) = 2 + α / Real.pi :=
  ⟨spinTensor_12_involution, spinMoment_comm_diracBeta, gamma_clifford_decomp μ ν,
    gFactor_dirac, gFactor_schwinger α⟩

end

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

end

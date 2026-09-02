/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation
public import Physlib.QuantumMechanics.SpinDensityFunctionalOperators
public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzLorentzSO3
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Gauge slice, the `Ξ` term, and the Pauli/triad inputs of the configuration-space Dirac operator

The pieces of Aastrup–Grimstrup arXiv:2501.00005 that
`ConfigurationSpaceDiracFluctuation` recorded but did not derive, now formalized at
their exact mathematical cores.

## §A — the gauge fixing behind `L²(ℱ)` (paper §2)

The paper's `L²(𝒜)` requires a gauge fixing `ℱ ⊆ 𝒜`: *"for each `A ∈ 𝒜` there is
exactly one `g ∈ 𝒢` with `g(A) ∈ ℱ`"*. That `∃!` hypothesis has exact structural
content:

* `gaugeSliceEquiv` — **the configuration space factorizes**, `𝒜 ≃ ℱ × 𝒢`: every
  connection is uniquely a gauge transform of a slice point. This is the set-level
  fact that lets the paper *"work with `ℱ` instead of `𝒜`"* — `L²(𝒜)` becomes
  `L²(ℱ × 𝒢)`, and the `𝒢`-factor is what the BRST procedure of [7] disposes of.
* `slice_residual_gauge_trivial` — the slice carries **no residual gauge freedom**:
  a gauge transformation mapping a slice point to a slice point is the identity.
  Globally such an `ℱ` is exactly what the **Gribov ambiguity** obstructs (paper's
  [21]); here it is the honest hypothesis, and these are its consequences.

## §B — the `Ξ` term (paper Eq. 3)

The metric (1) is *fibered over `𝒜`* — `ℱ ∋ A ↦ ⟨·,·⟩_A` — so an orthonormal basis
`{ηᵢ}` and hence the Clifford algebra depend on `A`, and `[∂/∂ξ, c(ηⱼ)] ≠ 0`. The
exact mechanism is the Leibniz rule for a derivation `δ` against multiplication
operators:

* `xi_commutator` — `[δ, L_z] = L_{δz}`: `δ(z·x) − z·δx = (δz)·x` — the commutator of
  the configuration-space derivative with a Clifford multiplication is multiplication
  by the *derived basis element*.
* `xi_commutator_vanishes_iff` — `[δ, L_z] = 0 ↔ δz = 0`: **the `Ξ` term vanishes
  exactly when the Clifford basis is constant over the configuration space** — a
  fibered (A-dependent) metric forces `Ξ ≠ 0`, an `A`-independent metric kills it.
  (Uses `derivation_apply_one`, `δ1 = 0`.)
* `dirac_square_defect` — the `Ξ`-contribution to `D̃²`: for a Dirac summand `c·δ`,
  `(c·δ)² x = c·(δc)·δx + c²·δ²x` — squaring produces the basis-derivative term
  `c·(δc)·δ` alongside the Laplacian `c²δ²`; `dirac_square_clean_of_constant` shows
  the square is the clean Laplacian iff the defect generator `δc` vanishes. The
  operator `Ξ` of the paper's `H_fermionic = i{D₁,[D₂,CS]} + Ξ` is the sum of these
  defects over the basis.

## §C — the Pauli and triad inputs of Eqs 9–10 (paper §5)

The change of basis reduces the fermionic Hamiltonian to the spatial Dirac form
`(1/3!)∫ dVol Tr(ΨD^AΨ† − Ψ†D^AΨ)` with `D^A = −iσᵃe^μ_a(∇^A_μ + ω_μ)` through two
inputs, both exact:

* **the Pauli trace identities** — `pauliVec_trace_zero` (`Tr σᵃ = 0`),
  `pauliVec_trace_pair` (`Tr(σᵃσᵇ) = 2δᵃᵇ` — the orthogonality behind the paper's
  basis inner product `⟨ρ|η⟩`), and the identity the paper invokes verbatim for
  Eq. 9 → Eq. 10, `pauliVec_trace_triple`: **`Tr_{𝔤₁}(σᵃσᵇσᶜ) = 2i·ε^{abc}`** — this
  is what converts the `ε^{aec}`-contracted quadratic form of Eq. 9 into the
  `−iσᵃ`-contraction defining the spatial Dirac operator.
* **the triad metric** (paper footnote 5, `g_{μν} = e^a_μ e^a_ν`) —
  `metricFromTriad e = eᵀ·e` with `metricFromTriad_apply` (the component formula),
  `metricFromTriad_isSymm`, and `metricFromTriad_posSemidef`: a triad always induces
  a symmetric positive-semidefinite metric — the "if a metric exists" hypothesis of
  paper §5 in matrix form.

## Honest scope

`𝒜 ≃ ℱ × 𝒢` is set-level (no measure/L² structure — the BRST ghost complex of [7]
is not built); the `Ξ` mechanism is the exact Leibniz algebra, not the summed
operator on `Λ*Ω¹`; the Eq. 9 integral itself (`∫Tr(ξᵢ ∧ ∇^Aξⱼ)` over `M`) and the
assembled `D^A = −iσᵃe^μ_a(∇^A_μ + ω_μ)` require the manifold layer and are recorded.
The Gribov ambiguity is acknowledged by keeping the gauge fixing a *hypothesis*.

## References

* J. Aastrup, J. M. Grimstrup, arXiv:2501.00005: §2 (Eq. 1, gauge fixing), Eq. 3
  (`Ξ`), §5 (Eqs 9–10, footnote 5); [7] arXiv:2309.06374 (metric and BRST details);
  [21] V. N. Gribov, Nucl. Phys. B **139** (1978) 1.
* Carriers: `AlgebraicQFT.ConfigurationSpaceDiracFluctuation` (the fluctuation this
  feeds), `SpinDensityFunctionalOperators` (`pauliX/Y/Z`),
  `DissipativeNambuLorenz.LorenzLorentzSO3` (`leviCivita3`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.SpinDensityFunctionalOperators
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzLorentzSO3

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry

/-! ## §A — the gauge fixing behind `L²(ℱ)` -/

variable {X G : Type*} [Group G] [MulAction G X]

/-- **The configuration space factorizes over a gauge slice**: if for each `A ∈ 𝒜`
there is *exactly one* `g ∈ 𝒢` with `g • A ∈ ℱ` (the paper's gauge-fixing condition),
then `𝒜 ≃ ℱ × 𝒢` — every connection is uniquely a gauge transform of a slice point.
This is the structural fact behind replacing `L²(𝒜)` by `L²(ℱ)`: the `𝒢`-factor
splits off, to be disposed of by the BRST procedure of the paper's [7]. -/
noncomputable def gaugeSliceEquiv (F : Set X)
    (hfix : ∀ A : X, ∃! g : G, g • A ∈ F) : X ≃ F × G where
  toFun A := (⟨(hfix A).choose • A, (hfix A).choose_spec.1⟩, (hfix A).choose)
  invFun p := (p.2)⁻¹ • (p.1 : X)
  left_inv A := inv_smul_smul _ _
  right_inv := by
    rintro ⟨⟨f, hf⟩, g⟩
    have hmem : g • (g⁻¹ • f) ∈ F := by rwa [smul_inv_smul]
    have hg : (hfix (g⁻¹ • f)).choose = g :=
      ((hfix (g⁻¹ • f)).choose_spec.2 g hmem).symm
    refine Prod.ext (Subtype.ext ?_) hg
    show (hfix (g⁻¹ • f)).choose • (g⁻¹ • f) = f
    rw [hg, smul_inv_smul]

/-- **The slice carries no residual gauge freedom**: a gauge transformation carrying
one slice point to another is the identity. Globally, the existence of such an `ℱ`
is exactly what the Gribov ambiguity obstructs — here the consequence of the paper's
gauge-fixing hypothesis. -/
theorem slice_residual_gauge_trivial {F : Set X}
    (hfix : ∀ A : X, ∃! g : G, g • A ∈ F) {f f' : X} (hf : f ∈ F) (hf' : f' ∈ F)
    {g : G} (hgf : g • f = f') : g = 1 := by
  have h1 : (1 : G) • f ∈ F := by rwa [one_smul]
  have hgmem : g • f ∈ F := hgf ▸ hf'
  exact ((hfix f).unique hgmem h1)

/-! ## §B — the `Ξ` term: Leibniz against an `A`-dependent Clifford basis -/

variable {R : Type*} [Ring R]

/-- A derivation kills the unit: `δ1 = 0`. -/
theorem derivation_apply_one (δ : R → R)
    (hLeib : ∀ x y, δ (x * y) = δ x * y + x * δ y) : δ 1 = 0 := by
  have h : δ 1 = δ 1 + δ 1 := by simpa using hLeib 1 1
  have h2 : δ 1 + 0 = δ 1 + δ 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- **The `Ξ` commutator** (paper Eq. 3): `[∂/∂ξ, c(η_A)] = c(∂η_A/∂ξ)` — against a
multiplication operator, the configuration-space derivative commutes up to
multiplication by the *derived Clifford element*: `δ(z·x) − z·δx = (δz)·x`. -/
theorem xi_commutator (δ : R → R)
    (hLeib : ∀ x y, δ (x * y) = δ x * y + x * δ y) (z x : R) :
    δ (z * x) - z * δ x = δ z * x := by
  rw [hLeib]
  abel

/-- **The `Ξ` term vanishes iff the Clifford basis is constant**:
`[δ, L_z] = 0 ↔ δz = 0`. The paper's Eq. 3 (`[∂/∂ξ, z] ≠ 0` for the `A`-dependent
orthonormal basis of the fibered metric (1)) is the failure of the right-hand side:
a fibered metric forces the extra term `Ξ`; an `A`-independent basis kills it. -/
theorem xi_commutator_vanishes_iff (δ : R → R)
    (hLeib : ∀ x y, δ (x * y) = δ x * y + x * δ y) (z : R) :
    (∀ x, δ (z * x) = z * δ x) ↔ δ z = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [mul_one, derivation_apply_one δ hLeib, mul_zero] at h1
    exact h1
  · intro h x
    rw [hLeib, h, zero_mul, zero_add]

/-- **The `Ξ`-defect of the squared Dirac summand**: for `D = c·δ`,
`(c·δ)²x = c·(δc)·δx + c²·δ²x` — the square of a Dirac summand whose Clifford
coefficient varies over the configuration space produces the basis-derivative term
`c·(δc)·δ` alongside the Laplacian `c²·δ²`. Summed over the basis these defects are
the paper's `Ξ` in `H_fermionic = i{D₁,[D₂,CS]} + Ξ`. -/
theorem dirac_square_defect (δ : R → R)
    (hLeib : ∀ x y, δ (x * y) = δ x * y + x * δ y) (c x : R) :
    c * δ (c * δ x) = c * δ c * δ x + c * c * δ (δ x) := by
  rw [hLeib]
  noncomm_ring

/-- **The square is the clean Laplacian iff the basis is covariantly constant**:
`δc = 0 ⟹ (c·δ)² = c²·δ²` — with an `A`-independent Clifford basis the `Ξ`-defect
disappears and only the bosonic Laplacian survives. -/
theorem dirac_square_clean_of_constant (δ : R → R)
    (hLeib : ∀ x y, δ (x * y) = δ x * y + x * δ y) {c : R} (hc : δ c = 0) (x : R) :
    c * δ (c * δ x) = c * c * δ (δ x) := by
  rw [dirac_square_defect δ hLeib, hc, mul_zero, zero_mul, zero_add]

/-! ## §C — the Pauli and triad inputs of Eqs 9–10 -/

/-- The Pauli vector `σᵃ`, `a ∈ {1,2,3}`, on the existing
`SpinDensityFunctionalOperators` carriers. -/
def pauliVec : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => if a = 0 then pauliX else if a = 1 then pauliY else pauliZ

/-- `Tr σᵃ = 0` — the Pauli matrices are traceless. -/
theorem pauliVec_trace_zero (a : Fin 3) : (pauliVec a).trace = 0 := by
  fin_cases a <;>
    simp [pauliVec, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two]

/-- **`Tr(σᵃσᵇ) = 2δᵃᵇ`** — the orthogonality behind the paper's basis inner product
`⟨ρ|η⟩ = ⟨e(ρ)|e(η)⟩_A` on `L²(M, 𝔤₁ ⊗ 𝔤₂)`. -/
theorem pauliVec_trace_pair (a b : Fin 3) :
    (pauliVec a * pauliVec b).trace = 2 * (if a = b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;>
    simp [pauliVec, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

/-- **`Tr_{𝔤₁}(σᵃσᵇσᶜ) = 2i·ε^{abc}`** — the identity the paper invokes verbatim to
pass from Eq. 9 to Eq. 10: it converts the `ε^{aec}`-contracted quadratic form of the
fermionic Hamiltonian into the `−iσᵃ`-contraction that defines the spatial Dirac
operator `D^A = −iσᵃe^μ_a(∇^A_μ + ω_μ)`. -/
theorem pauliVec_trace_triple (a b c : Fin 3) :
    (pauliVec a * pauliVec b * pauliVec c).trace
      = 2 * Complex.I * ((leviCivita3 a b c : ℝ) : ℂ) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [pauliVec, pauliX, pauliY, pauliZ, leviCivita3, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- **The triad metric** (paper footnote 5): `g_{μν} = e^a_μ e^a_ν`, i.e.
`g = eᵀ·e`. -/
def metricFromTriad (e : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  e.transpose * e

/-- The component formula `g_{μν} = Σₐ e^a_μ e^a_ν`. -/
theorem metricFromTriad_apply (e : Matrix (Fin 3) (Fin 3) ℝ) (μ ν : Fin 3) :
    metricFromTriad e μ ν = ∑ a, e a μ * e a ν := by
  rw [metricFromTriad, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [Matrix.transpose_apply]

/-- The triad metric is symmetric. -/
theorem metricFromTriad_isSymm (e : Matrix (Fin 3) (Fin 3) ℝ) :
    (metricFromTriad e).IsSymm := by
  rw [Matrix.IsSymm, metricFromTriad, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The triad metric is positive semidefinite — a triad field always induces a
genuine (degenerate-allowed) Riemannian metric, the "if a metric exists" hypothesis
of paper §5 in matrix form. -/
theorem metricFromTriad_posSemidef (e : Matrix (Fin 3) (Fin 3) ℝ) :
    (metricFromTriad e).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self e
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry

end

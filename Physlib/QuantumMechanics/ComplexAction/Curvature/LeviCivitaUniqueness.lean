/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
public import Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness -/

/-!
# Uniqueness of the Levi-Civita connection (fundamental theorem of Riemannian geometry)

`LeviCivitaFromMetric` builds `christoffelFromMetric` and proves it *is* torsion-free and
metric-compatible (existence).  This module supplies the **uniqueness** half: for a
symmetric invertible metric, `christoffelFromMetric` is the *only* torsion-free
metric-compatible connection —

`IsTorsionFree Γ ∧ IsMetricCompatible Γ  ⟹  Γ = christoffelFromMetric`
(`christoffel_unique_of_torsionFree_metricCompatible`).

The proof is the Koszul combination: metric compatibility written in three cyclic index
permutations, combined with torsion-freeness (`Γ^σ_{μν}=Γ^σ_{νμ}`), determines the fully
lowered symbol `Γ_{νlμ} = g_{νσ}Γ^σ_{lμ}` as `½(∂_l g_{νμ}+∂_μ g_{νl}−∂_ν g_{lμ})` — exactly the
`christoffel_contraction` value — and raising with `g^{−1}` recovers `Γ` itself.

This is the curved-space analogue of the flat-space clock-rigidity results: just as an
injective Compton reading fixes proper time uniquely, a torsion-free metric-compatible
connection is fixed uniquely by the metric.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness

open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-- **The fully lowered connection symbol** `Γ_{νlμ} = ∑_σ Γ^σ_{lμ} g_{σν}` (the connection
contracted against the metric on its upper index). -/
def loweredSymbol (Γ : ι → Matrix ι ι ℝ) (g : Matrix ι ι ℝ) (l μ ν : ι) : ℝ :=
  ∑ σ, (Γ σ) l μ * g σ ν

/-- **Uniqueness of the Levi-Civita connection.**  For a symmetric invertible metric, any
torsion-free metric-compatible connection equals `christoffelFromMetric` — the fundamental
theorem of Riemannian geometry (uniqueness half). -/
@[zil_level bridge_theorem]
theorem christoffel_unique_of_torsionFree_metricCompatible
    [DecidableEq ι] {g gInv : Matrix ι ι ℝ} {Γ : ι → Matrix ι ι ℝ} (dg : ι → Matrix ι ι ℝ)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (hdg : ∀ κ, (dg κ)ᵀ = dg κ)
    (htf : IsTorsionFree Γ) (hmc : IsMetricCompatible Γ dg g) :
    Γ = christoffelFromMetric gInv dg := by
  have hgcomm : g * gInv = 1 := mul_eq_one_comm.mp hinv
  have hgsym : ∀ a b, g a b = g b a := fun a b => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hg b) a
  have hdgsym : ∀ κ a b, dg κ a b = dg κ b a := fun κ a b => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hdg κ) b) a
  have htfsym : ∀ σ a b, (Γ σ) a b = (Γ σ) b a := fun σ a b => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (htf σ) b) a
  -- torsion-freeness makes the lowered symbol symmetric in its first two indices
  have hLsym : ∀ a b c, loweredSymbol Γ g a b c = loweredSymbol Γ g b a c := by
    intro a b c
    unfold loweredSymbol
    exact Finset.sum_congr rfl fun σ _ => by rw [htfsym σ a b]
  -- metric compatibility, in lowered form
  have hmcL : ∀ l μ ν, dg l μ ν = loweredSymbol Γ g l μ ν + loweredSymbol Γ g l ν μ := by
    intro l μ ν
    have h := congrFun (congrFun (hmc l) μ) ν
    simp only [metricCovariantDeriv, Matrix.zero_apply] at h
    have e2 : (∑ σ, (Γ σ) l ν * g μ σ) = ∑ σ, (Γ σ) l ν * g σ μ :=
      Finset.sum_congr rfl fun σ _ => by rw [hgsym μ σ]
    rw [e2] at h
    unfold loweredSymbol
    linarith
  -- Koszul: the lowered symbol is fixed
  have hkoszul : ∀ l μ ν, 2 * loweredSymbol Γ g l μ ν = dg l μ ν + dg μ ν l - dg ν l μ := by
    intro l μ ν
    linarith [hmcL l μ ν, hmcL μ ν l, hmcL ν l μ, hLsym l ν μ, hLsym μ l ν, hLsym μ ν l]
  -- the Christoffel lowered symbol has the same Koszul value
  have hLchr : ∀ l μ ν, loweredSymbol (christoffelFromMetric gInv dg) g l μ ν
      = (1 / 2) * (dg l μ ν + dg μ ν l - dg ν l μ) := by
    intro l μ ν
    unfold loweredSymbol
    rw [christoffel_contraction dg hgi hinv l μ ν, hdgsym l ν μ]
  -- the two lowered symbols agree
  have hLeq : ∀ l μ ν, loweredSymbol Γ g l μ ν
      = loweredSymbol (christoffelFromMetric gInv dg) g l μ ν := by
    intro l μ ν; linarith [hkoszul l μ ν, hLchr l μ ν]
  -- raise the index back with the inverse metric
  have raise : ∀ (M : ι → Matrix ι ι ℝ) (l μ τ : ι),
      ∑ ν, gInv ν τ * loweredSymbol M g l μ ν = (M τ) l μ := by
    intro M l μ τ
    have step : ∀ ν, gInv ν τ * loweredSymbol M g l μ ν
        = ∑ σ, (M σ) l μ * (g σ ν * gInv ν τ) := by
      intro ν
      unfold loweredSymbol
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [Finset.sum_congr rfl fun ν _ => step ν, Finset.sum_comm]
    have step2 : ∀ σ, ∑ ν, (M σ) l μ * (g σ ν * gInv ν τ) = (M σ) l μ * (g * gInv) σ τ := by
      intro σ
      rw [← Finset.mul_sum, Matrix.mul_apply]
    rw [Finset.sum_congr rfl fun σ _ => step2 σ, hgcomm]
    simp [Matrix.one_apply, Finset.sum_ite_eq']
  funext τ
  ext l μ
  rw [← raise Γ l μ τ, ← raise (christoffelFromMetric gInv dg) l μ τ]
  exact Finset.sum_congr rfl fun ν _ => by rw [hLeq l μ ν]

/-- **The Levi-Civita connection is invariant under a constant Weyl rescaling** `g ↦ λg`
(`λ ≠ 0`): the inverse metric scales by `λ⁻¹` and every metric derivative by `λ`, which cancel
in `Γ = ½ g⁻¹(∂g+∂g−∂g)`.  So the connection determines the metric only up to a global constant
factor — the curved-space analogue of Malament's conformal dilation `√c`.  A *position-dependent*
rescaling would leave uncancelled `∂λ` terms (curvature), so the constant is the entire freedom;
fixing the metric at one point removes it. -/
@[zil_level bridge_theorem]
theorem christoffelFromMetric_const_rescale_invariant
    (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    christoffelFromMetric (lam⁻¹ • gInv) (fun κ => lam • dg κ)
      = christoffelFromMetric gInv dg := by
  funext σ
  ext μ ν
  simp only [christoffelFromMetric, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
    smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness

zil attach christoffel_unique_of_torsionFree_metricCompatible where
  formalizes @ "claim:for-a-symmetric-invertible-metric-any-torsion-free-metric-compatible-connection-equals-the-christoffel-connection-the-uniqueness-half-of-the-fundamental-theorem-of-riemannian-geometry",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffel_contraction"

zil attach christoffelFromMetric_const_rescale_invariant where
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:the-levi-civita-connection-is-invariant-under-a-constant-weyl-rescaling-of-the-metric-so-the-connection-determines-the-metric-only-up-to-a-global-constant-factor-the-curved-space-analogue-of-the-malament-conformal-dilation"

zil_file_contract physlib.leviCivitaUniqueness where
  promises "The uniqueness half of the fundamental theorem of Riemannian geometry, the curved-space analogue of the flat-space clock-rigidity results. For a symmetric invertible metric, any torsion-free metric-compatible connection equals the Christoffel connection built from the metric. The proof is the Koszul combination: metric compatibility written in three cyclic index permutations and combined with torsion-freeness determines the fully lowered connection symbol as one half of the metric-derivative combination, exactly the Christoffel contraction value, and raising the index with the inverse metric recovers the connection itself. Just as an injective Compton reading fixes proper time uniquely, a torsion-free metric-compatible connection is fixed uniquely by the metric."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.IsTorsionFree",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.IsMetricCompatible"
  ]
  forbids_substitutes [
    "dropping the symmetry or invertibility of the metric",
    "reading existence of the Christoffel connection as its uniqueness"
  ]
  witnessed_by [
    christoffel_unique_of_torsionFree_metricCompatible,
    christoffelFromMetric_const_rescale_invariant
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.leviCivitaUniqueness

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction -/

/-!
# Einstein–Cartan gravity reduces to Einstein gravity when spin vanishes

Einstein–Cartan gravity uses a general metric-compatible affine connection whose antisymmetric part
(torsion) is sourced by spin, `T^λ_{μν} = κ · s^λ_{μν}` (the tensor Cartan equation).  The repository
carries the torsion tensor (`torsion`), the Levi-Civita connection (`christoffelFromMetric`), and the
fundamental-theorem uniqueness (`christoffel_unique_of_torsionFree_metricCompatible`), but never
assembles them into the physically central statement: **when the spin source vanishes, torsion
vanishes, the connection is Levi-Civita, and Einstein–Cartan gravity collapses to Einstein gravity.**

* `contorsion` — the contorsion `K = Γ − Γ_LC`, the correction of a connection from Levi-Civita;
  `connection_eq_leviCivita_add_contorsion`, `contorsion_zero_iff_eq_leviCivita`.
* `torsionFree_metricCompatible_eq_leviCivita` — a metric-compatible connection with vanishing torsion
  is the Levi-Civita connection (packaging the uniqueness theorem through `torsion`).
* `einsteinCartan_spinless_eq_leviCivita` — under the tensor Cartan equation `torsion = κ · spin`, a
  vanishing spin source forces the metric-compatible Einstein–Cartan connection to be Levi-Civita — so
  the Einstein–Cartan field content reduces to the Einstein one.

Honest scope: this is the connection-level reduction (torsion ⟹ Levi-Civita) that makes the
Einstein–Cartan → Einstein collapse rigorous; the full spin-curvature field equations and the algebraic
elimination of torsion into a four-fermion contact term are carried separately
(`EinsteinCartanAxialTorsion`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction

open scoped Matrix
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness
open Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The contorsion tensor** `K^σ_{μν} = Γ^σ_{μν} − Γ_LC{}^σ_{μν}` — the difference of an affine
connection from the Levi-Civita connection built from the metric. -/
def contorsion (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (Γ : ι → Matrix ι ι ℝ) :
    ι → Matrix ι ι ℝ :=
  fun l => Γ l - (christoffelFromMetric gInv dg) l

/-- **A connection splits as Levi-Civita plus contorsion**, `Γ = Γ_LC + K`. -/
lemma connection_eq_leviCivita_add_contorsion (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) (l : ι) :
    Γ l = (christoffelFromMetric gInv dg) l + contorsion gInv dg Γ l := by
  simp [contorsion]

/-- **The contorsion vanishes exactly when the connection is Levi-Civita.** -/
lemma contorsion_zero_iff_eq_leviCivita (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) :
    (∀ l, contorsion gInv dg Γ l = 0) ↔ Γ = christoffelFromMetric gInv dg := by
  simp only [contorsion, sub_eq_zero]
  exact ⟨fun h => funext h, fun h l => by rw [h]⟩

/-- **A metric-compatible connection with vanishing torsion is Levi-Civita.**  Packaging the
fundamental-theorem uniqueness through the torsion tensor: `torsion Γ = 0` and metric compatibility
force `Γ = christoffelFromMetric`. -/
@[zil_level bridge_theorem]
theorem torsionFree_metricCompatible_eq_leviCivita {g gInv : Matrix ι ι ℝ} {Γ : ι → Matrix ι ι ℝ}
    (dg : ι → Matrix ι ι ℝ) (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    (hdg : ∀ κ, (dg κ)ᵀ = dg κ) (hmc : IsMetricCompatible Γ dg g) (hT : ∀ l, torsion Γ l = 0) :
    Γ = christoffelFromMetric gInv dg :=
  christoffel_unique_of_torsionFree_metricCompatible dg hg hgi hinv hdg
    ((torsion_eq_zero_iff_isTorsionFree Γ).mp hT) hmc

/-- **Einstein–Cartan gravity reduces to Einstein gravity when spin vanishes.**  Under the tensor
Cartan equation `torsion Γ = κ · spin`, a vanishing spin source (`spin = 0`) makes the torsion vanish,
and a metric-compatible connection with vanishing torsion is the Levi-Civita connection.  So a
spinless Einstein–Cartan spacetime has the Levi-Civita connection and its curvature/field content is
exactly the Einstein one. -/
@[zil_level physical_theorem]
theorem einsteinCartan_spinless_eq_leviCivita {g gInv : Matrix ι ι ℝ} {Γ : ι → Matrix ι ι ℝ}
    (dg : ι → Matrix ι ι ℝ) (κ : ℝ) (spin : ι → Matrix ι ι ℝ)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (hdg : ∀ κ', (dg κ')ᵀ = dg κ')
    (hmc : IsMetricCompatible Γ dg g) (hCartan : ∀ l, torsion Γ l = κ • spin l)
    (hSpinless : ∀ l, spin l = 0) :
    Γ = christoffelFromMetric gInv dg := by
  refine torsionFree_metricCompatible_eq_leviCivita dg hg hgi hinv hdg hmc (fun l => ?_)
  rw [hCartan l, hSpinless l, smul_zero]

end Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction

zil attach torsionFree_metricCompatible_eq_leviCivita where
  formalizes @ "claim:a-metric-compatible-affine-connection-with-vanishing-torsion-is-the-levi-civita-connection-the-fundamental-theorem-uniqueness-packaged-through-the-torsion-tensor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.christoffel_unique_of_torsionFree_metricCompatible"

zil attach einsteinCartan_spinless_eq_leviCivita where
  supported_by @ "lean:torsionFree_metricCompatible_eq_leviCivita",
  formalizes @ "claim:einstein-cartan-gravity-reduces-to-einstein-gravity-when-spin-vanishes-under-the-tensor-cartan-equation-torsion-equals-kappa-times-spin-a-vanishing-spin-source-forces-the-metric-compatible-connection-to-be-levi-civita"

zil_file_contract physlib.einsteinCartanReduction where
  promises "Einstein-Cartan gravity reduces to Einstein gravity when spin vanishes, the connection-level reduction assembling the repository's torsion tensor, Levi-Civita connection, and fundamental-theorem uniqueness. The contorsion is the difference of an affine connection from the Levi-Civita connection, a connection splits as Levi-Civita plus contorsion, and the contorsion vanishes exactly when the connection is Levi-Civita. A metric-compatible connection with vanishing torsion is the Levi-Civita connection, packaging the uniqueness theorem through the torsion tensor. Under the tensor Cartan equation torsion equals kappa times spin, a vanishing spin source makes torsion vanish, so a metric-compatible spinless Einstein-Cartan connection is Levi-Civita and its curvature and field content are exactly the Einstein ones. Honest scope: this is the connection-level reduction that makes the Einstein-Cartan to Einstein collapse rigorous; the full spin-curvature field equations and the four-fermion contact-term elimination of torsion are carried separately in the axial-torsion module."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge.torsion",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.christoffel_unique_of_torsionFree_metricCompatible"
  ]
  forbids_substitutes [
    "reading the connection-level torsion-to-Levi-Civita reduction as the full Einstein-Cartan spin-curvature field equations or the four-fermion contact-term elimination"
  ]
  witnessed_by [
    torsionFree_metricCompatible_eq_leviCivita,
    einsteinCartan_spinless_eq_leviCivita
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.einsteinCartanReduction

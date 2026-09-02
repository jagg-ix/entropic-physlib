/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.Lattice.LatticeTopologicalCharge
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GalperinHarmonicSelfDuality
meta import Zil

/-!
# The Hodge star on four-dimensional two-forms

The **Hodge star** `⋆` sends a `k`-form to the `(n−k)`-form obtained by contracting with the volume
form `ε`. In four Euclidean dimensions the star maps two-forms (antisymmetric rank-2 tensors — the
bivectors `∧²ℝ⁴`, the home of any field strength `F_{μν}`) to two-forms:

  `(⋆F)_{μν} = ½ ε_{μνρσ} F^{ρσ}`.

This module builds that operator on `Matrix (Fin 4) (Fin 4) ℝ` from the Levi-Civita volume form
`leviCivita4` (`QFT.Lattice.LatticeTopologicalCharge`) — the real-valued counterpart of the rational
`Particles.MigdalSelfDualLoopSolution.hodge2`, promoted from `ℚ` to `ℝ` and equipped with its algebraic
structure. The star is the concrete realization on `∧²ℝ⁴` of the abstract self-adjoint involution that
`AlgebraicQFT.SelfDualQuaternionYangMills` treats over an arbitrary inner-product space, and the double
star on both index pairs of the Riemann tensor is `Curvature.MoulinDoubleDualCotton.doubleDualRiemann`.

* **§A** the star `hodgeStar2` and its linearity (`hodgeStar2_add`, `hodgeStar2_sub`, `hodgeStar2_smul`).
* **§B** the six independent components of `⋆F` for an antisymmetric `F` (`hodgeStar2_apply_01`, …), the
  antisymmetry `(⋆F)_{νμ} = −(⋆F)_{μν}` (`hodgeStar2_antisymm`) and vanishing diagonal
  (`hodgeStar2_diag`) — `⋆` maps two-forms to two-forms.
* **§C** the star squares to the identity on two-forms — `⋆⋆F = F` in four Euclidean dimensions
  (`hodgeStar2_involutive`), the defining property of the star.
* **§D** the self-dual / anti-self-dual decomposition `F = F₊ + F₋` with `⋆F± = ±F±`
  (`selfDualPart`, `antiSelfDualPart`, `hodgeStar2_selfDualPart`, `hodgeStar2_antiSelfDualPart`) — the
  `⋆`-eigenspace splitting `∧²ℝ⁴ = ∧²₊ ⊕ ∧²₋`.
* **§E** the star of the Faraday tensor `⋆(dA)` and the **inhomogeneous Maxwell equation in dual form**
  `d⋆F = −⋆J`: the homogeneous Bianchi cyclic sum of `⋆F` equals minus the volume-form dual of the
  four-current `J^α = ∂_β F^{αβ}` (`maxwellOp`), so `d⋆F = 0` is exactly the source-free condition
  `J = 0` (`hodgeStar2_bianchi_eq_current`, `sourceFree_iff_hodgeStar2_closed`).
* **§F** harmonic two-forms — the Hodge Laplacian `□ = dδ + δd`, `□F = 0 ⟺ dF = 0 ∧ δF = 0`
  (`IsHarmonic2`), and the fact that both `⋆`-eigenspaces are harmonic: a (anti-)self-dual `F = dA` is
  harmonic (`selfDual_faraday_isHarmonic2`, `antiSelfDual_faraday_isHarmonic2`). This is Zucker's
  Hodge-theorem engine (§2): `δ = −⋆d⋆`, harmonic = closed and co-closed, harmonic forms decompose by
  type — the type split of two-forms in four dimensions being the self-dual/anti-self-dual split §D.
* **§G** electric–magnetic duality — writing `E = (F_{01}, F_{02}, F_{03})`, `B = (F_{23}, F_{31}, F_{12})`,
  the star exchanges them `(E, B) ↦ (B, E)` (`hodgeStar2_swaps_electric_magnetic`), self-duality is
  `E = B` (`selfDual_electric_eq_magnetic`) and anti-self-duality is `E = −B`
  (`antiSelfDual_electric_eq_neg_magnetic`). This is the physical content of the block swap that the
  Gravitas `hodgeDualEM` (catept-main) performs on the Faraday tensor, here in the component form of §B.
* **§H** the 3+1 Cauchy split — the two **Gauss constraints** of the Faraday Cauchy problem
  (Drago–Ginoux–Murro, Lemma 2.2): `∇·B = 0` from `dF = 0` (`magneticGauss_of_closed`,
  `faraday_magneticGauss`) and `∇·E = ρ` from `δF = j` (`chargeDensity_eq_electricDivergence`,
  `sourceFree_electricGauss`). These constrain the Cauchy data and propagate under the evolution because
  the current is conserved (`δj = δ²F = 0`, `CovariantMaxwellLambShift.maxwell_current_conserved`).
* **§I** the variational core of the Cauchy problem — on plane waves `d` and `δ` are **formal adjoints**
  `⟨dα, F⟩ = −2⟨α, δF⟩` (`d_codifferential_adjoint`), so `D = d + δ` is formally self-adjoint; the action
  derivative is `⟨dA, dα⟩ = −2⟨α, δdA⟩` (`maxwell_variational`) and `A` is stationary for every `α` iff
  `δdA = 0` (`maxwell_stationary_iff_sourceFree`), the source-free Maxwell equation. This is the
  linear-analytic identity the Drago–Ginoux–Murro variational principle (Remark 1.2.4) and the
  self-adjointness of `D` behind the Green operators and pre-symplectic form (§5) rest on; the
  functional-analytic existence on manifolds-with-boundary (Ginoux, [17, Thm 1.2]) is an external input.
* **§J** the Maxwell-compactness mechanism — the **Gaffney/Lagrange identity**
  `‖k×u‖² + (k·u)² = ‖k‖²‖u‖²` (`maxwell_gaffney_symbol`): the curl-energy plus divergence-energy of a
  Fourier mode is `‖k‖²` times its L²-energy, so `‖u‖² = (‖k×u‖²+(k·u)²)/‖k‖²` (`maxwell_fieldEnergy_eq`)
  decays as `‖k‖→∞` — the Fourier-decay reason a bounded `H(curl)∩H(div)` sequence is L²-compact. The
  symbol de Rham complex `curl∘grad = 0`, `div∘curl = 0` (`curlGrad_symbol_eq_zero`,
  `divCurl_symbol_eq_zero`) is the pointwise `d²=0` of the complex (1.1) whose smooth form physlib carries
  in `SpaceAndTime.Space.Derivatives.Curl` (`curl_of_grad_eq_zero`, `div_of_curl_eq_zero`,
  `exists_grad_of_curl_zero`). The discrete polytopal (DDR) complex, the commuting quasi-interpolators and
  the compactness proper (Rellich–Kondrachov) are the deep numerical-analysis content, external to this
  algebraic core (Chaumont-Frelet–Droniou–Lemaire, arXiv:2510.18835).
* **§K** Vytheeswaran's Proca/two-form bridge — the vector
  `F_μ = ½ ε_{μνλσ} ∂_ν B_{λσ}` is the existing Maxwell codifferential of `⋆B`, is
  automatically transverse, and is invariant under `B ↦ B + dΛ` at the Fourier-symbol level.
* **§K.1** the mostly-minus Lorentzian Fourier-mode Maxwell--tensor Lagrangian of Eq. (3.27),
  its simultaneous vector/two-form gauge invariance, and the explicitly computed pairwise
  first-class algebra of all eight primary and secondary constraints from Eqs. (3.28), (3.30).
* **§K.2** the gauge-invariant Eq. (3.23) Hamiltonian density, the Eq. (3.25)
  tensor-momentum square completion and unitary-gauge reduction, and the exact reduction of
  Eq. (3.29) to Eq. (3.25) on the secondary-constraint surface.
* **§K.3** the genuine directional derivative of the Cauchy Lagrangian giving the
  canonical vector/tensor momenta of Eq. (3.28), its nonzero-mass Legendre transform to
  Eq. (3.25), and the Dirac--Bergmann derivation of the secondary constraints from
  preservation of the four primary momenta.
* **§K.4** the exact `3+1` decomposition of the full Lorentzian Eq. (3.27) into that
  Cauchy Lagrangian, including the temporal/spatial multiplicities of the three-form.
* **§K.5** the full spacetime-distribution version of the antisymmetric-tensor dual,
  its gauge invariance and its identically vanishing distributional divergence.
* **§K.6** an `L²` Fourier-Cauchy domain, its integrated action and Legendre transform,
  and the almost-everywhere continuum constraint surface.

## References

* S. Zucker, *Hodge theory with degenerating coefficients: L₂ cohomology in the Poincaré metric*,
  Ann. of Math. 109 (1979) 415–476 — §2: the codifferential `δ = −⋆d⋆` (2.3), the Hodge Laplacian
  `□ = dδ + δd` (2.6), harmonic ⟺ closed and co-closed (2.10 iii), decomposition by type (2.7, 2.10 iv).
* `QFT.Lattice.LatticeTopologicalCharge.leviCivita4` — the four-dimensional volume form `ε_{μνρσ}`.
* `Particles.MigdalSelfDualLoopSolution.hodge2` — the rational two-form dual `⋆` promoted here to `ℝ`.
* `AlgebraicQFT.SelfDualQuaternionYangMills` — the abstract `⋆`-involution and `P± = ½(1 ± ⋆)`.
* `PTSymmetricQFT.MaxwellFaraday.faraday`, `PTSymmetricQFT.PTTensorDynamics.maxwellOp` — `F = dA` and
  the four-current `∂_β F^{αβ}`.
* A. S. Vytheeswaran, *Gauge Invariances in the Proca Model*, Int. J. Mod. Phys. A **13**
  (1998) 765--778, Eqs. (3.22)--(3.30).
-/

set_option autoImplicit false

open Matrix
open Physlib.QFT.Lattice.LatticeTopologicalCharge
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector

/-! ## A. The Hodge star on two-forms and its linearity -/

@[expose] public section

/-- **The Hodge star on four-dimensional two-forms** `(⋆F)_{μν} = ½ ε_{μνρσ} F^{ρσ}`. The volume form
`ε` is `leviCivita4`; this is the `ℝ`-valued counterpart of `MigdalSelfDualLoopSolution.hodge2`. -/
noncomputable def hodgeStar2 (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => (1 / 2 : ℝ) * ∑ a, ∑ b, ((leviCivita4 μ ν a b : ℤ) : ℝ) * F a b

end

theorem hodgeStar2_apply (F : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) :
    hodgeStar2 F μ ν = (1 / 2 : ℝ) * ∑ a, ∑ b, ((leviCivita4 μ ν a b : ℤ) : ℝ) * F a b := rfl

/-- The star is additive: `⋆(A + B) = ⋆A + ⋆B`. -/
theorem hodgeStar2_add (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeStar2 (A + B) = hodgeStar2 A + hodgeStar2 B := by
  ext i j
  simp only [hodgeStar2_apply, Matrix.add_apply, Fin.sum_univ_four]
  ring

/-- The star is subtractive: `⋆(A − B) = ⋆A − ⋆B`. -/
theorem hodgeStar2_sub (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeStar2 (A - B) = hodgeStar2 A - hodgeStar2 B := by
  ext i j
  simp only [hodgeStar2_apply, Matrix.sub_apply, Fin.sum_univ_four]
  ring

/-- The star is homogeneous: `⋆(c • A) = c • ⋆A`. -/
theorem hodgeStar2_smul (c : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeStar2 (c • A) = c • hodgeStar2 A := by
  ext i j
  simp only [hodgeStar2_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  ring

/-! ## B. The components of `⋆F`, antisymmetry and vanishing diagonal -/

/-- **`⋆F` is again antisymmetric** `(⋆F)_{νμ} = −(⋆F)_{μν}`: the star maps two-forms to two-forms,
inherited from the antisymmetry of the volume form in its first index pair (`leviCivita4_swap_12`). -/
theorem hodgeStar2_antisymm (F : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) :
    hodgeStar2 F ν μ = - hodgeStar2 F μ ν := by
  simp only [hodgeStar2_apply]
  rw [← mul_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [leviCivita4_swap_12]; push_cast; ring

/-- **The diagonal of `⋆F` vanishes** `(⋆F)_{μμ} = 0` — the volume form vanishes on a repeated index
(`leviCivita4_eq_zero_of_repeat`). -/
theorem hodgeStar2_diag (F : Matrix (Fin 4) (Fin 4) ℝ) (μ : Fin 4) : hodgeStar2 F μ μ = 0 := by
  rw [hodgeStar2_apply]
  have h : (∑ a, ∑ b, ((leviCivita4 μ μ a b : ℤ) : ℝ) * F a b) = 0 := by
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    rw [leviCivita4_eq_zero_of_repeat μ μ a b (Or.inl rfl)]; simp
  rw [h, mul_zero]

section Components
variable (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = - F j i)
include hF

/-- `(⋆F)_{01} = F_{23}`. -/
theorem hodgeStar2_apply_01 : hodgeStar2 F 0 1 = F 2 3 := by
  simp only [hodgeStar2_apply, Fin.sum_univ_four, leviCivita4]; push_cast; linarith [hF 3 2]

/-- `(⋆F)_{02} = −F_{13}`. -/
theorem hodgeStar2_apply_02 : hodgeStar2 F 0 2 = - F 1 3 := by
  simp only [hodgeStar2_apply, Fin.sum_univ_four, leviCivita4]; push_cast; linarith [hF 3 1]

/-- `(⋆F)_{03} = F_{12}`. -/
theorem hodgeStar2_apply_03 : hodgeStar2 F 0 3 = F 1 2 := by
  simp only [hodgeStar2_apply, Fin.sum_univ_four, leviCivita4]; push_cast; linarith [hF 2 1]

/-- `(⋆F)_{12} = F_{03}`. -/
theorem hodgeStar2_apply_12 : hodgeStar2 F 1 2 = F 0 3 := by
  simp only [hodgeStar2_apply, Fin.sum_univ_four, leviCivita4]; push_cast; linarith [hF 3 0]

/-- `(⋆F)_{13} = −F_{02}`. -/
theorem hodgeStar2_apply_13 : hodgeStar2 F 1 3 = - F 0 2 := by
  simp only [hodgeStar2_apply, Fin.sum_univ_four, leviCivita4]; push_cast; linarith [hF 2 0]

/-- `(⋆F)_{23} = F_{01}`. -/
theorem hodgeStar2_apply_23 : hodgeStar2 F 2 3 = F 0 1 := by
  simp only [hodgeStar2_apply, Fin.sum_univ_four, leviCivita4]; push_cast; linarith [hF 1 0]

/-- `(⋆F)_{10} = −F_{23}`. -/
theorem hodgeStar2_apply_10 : hodgeStar2 F 1 0 = - F 2 3 := by
  have h := hodgeStar2_apply_01 F hF; have a := hodgeStar2_antisymm F 0 1; linarith

/-- `(⋆F)_{20} = F_{13}`. -/
theorem hodgeStar2_apply_20 : hodgeStar2 F 2 0 = F 1 3 := by
  have h := hodgeStar2_apply_02 F hF; have a := hodgeStar2_antisymm F 0 2; linarith

/-- `(⋆F)_{30} = −F_{12}`. -/
theorem hodgeStar2_apply_30 : hodgeStar2 F 3 0 = - F 1 2 := by
  have h := hodgeStar2_apply_03 F hF; have a := hodgeStar2_antisymm F 0 3; linarith

/-- `(⋆F)_{21} = −F_{03}`. -/
theorem hodgeStar2_apply_21 : hodgeStar2 F 2 1 = - F 0 3 := by
  have h := hodgeStar2_apply_12 F hF; have a := hodgeStar2_antisymm F 1 2; linarith

/-- `(⋆F)_{31} = F_{02}`. -/
theorem hodgeStar2_apply_31 : hodgeStar2 F 3 1 = F 0 2 := by
  have h := hodgeStar2_apply_13 F hF; have a := hodgeStar2_antisymm F 1 3; linarith

/-- `(⋆F)_{32} = −F_{01}`. -/
theorem hodgeStar2_apply_32 : hodgeStar2 F 3 2 = - F 0 1 := by
  have h := hodgeStar2_apply_23 F hF; have a := hodgeStar2_antisymm F 2 3; linarith

end Components

/-! ## C. The Hodge star squares to the identity on two-forms -/

/-- **The Hodge star squares to the identity on two-forms** `⋆⋆F = F`, for any antisymmetric `F` in
four Euclidean dimensions. This is `⋆⋆ = (−1)^{k(n−k)} = +1` for `k = 2`, `n = 4` — the defining
algebraic property of the star. -/
theorem hodgeStar2_involutive (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ i j, F i j = - F j i) :
    hodgeStar2 (hodgeStar2 F) = F := by
  have hs : ∀ i j, hodgeStar2 F i j = - hodgeStar2 F j i := fun i j => hodgeStar2_antisymm F j i
  have Fd : ∀ i, F i i = 0 := fun i => by have := hF i i; linarith
  -- the sixteen components, on the literal indices where `rw` matches; `⋆⋆F` reduces through the
  -- single-star components applied first to `⋆F` (`hs`) and then to `F` (`hF`).
  have k00 : hodgeStar2 (hodgeStar2 F) 0 0 = F 0 0 := (hodgeStar2_diag _ 0).trans (Fd 0).symm
  have k11 : hodgeStar2 (hodgeStar2 F) 1 1 = F 1 1 := (hodgeStar2_diag _ 1).trans (Fd 1).symm
  have k22 : hodgeStar2 (hodgeStar2 F) 2 2 = F 2 2 := (hodgeStar2_diag _ 2).trans (Fd 2).symm
  have k33 : hodgeStar2 (hodgeStar2 F) 3 3 = F 3 3 := (hodgeStar2_diag _ 3).trans (Fd 3).symm
  have k01 : hodgeStar2 (hodgeStar2 F) 0 1 = F 0 1 := by
    rw [hodgeStar2_apply_01 (hodgeStar2 F) hs, hodgeStar2_apply_23 F hF]
  have k02 : hodgeStar2 (hodgeStar2 F) 0 2 = F 0 2 := by
    rw [hodgeStar2_apply_02 (hodgeStar2 F) hs, hodgeStar2_apply_13 F hF]; ring
  have k03 : hodgeStar2 (hodgeStar2 F) 0 3 = F 0 3 := by
    rw [hodgeStar2_apply_03 (hodgeStar2 F) hs, hodgeStar2_apply_12 F hF]
  have k12 : hodgeStar2 (hodgeStar2 F) 1 2 = F 1 2 := by
    rw [hodgeStar2_apply_12 (hodgeStar2 F) hs, hodgeStar2_apply_03 F hF]
  have k13 : hodgeStar2 (hodgeStar2 F) 1 3 = F 1 3 := by
    rw [hodgeStar2_apply_13 (hodgeStar2 F) hs, hodgeStar2_apply_02 F hF]; ring
  have k23 : hodgeStar2 (hodgeStar2 F) 2 3 = F 2 3 := by
    rw [hodgeStar2_apply_23 (hodgeStar2 F) hs, hodgeStar2_apply_01 F hF]
  have k10 : hodgeStar2 (hodgeStar2 F) 1 0 = F 1 0 := by
    rw [hodgeStar2_apply_10 (hodgeStar2 F) hs, hodgeStar2_apply_23 F hF]; linarith [hF 1 0]
  have k20 : hodgeStar2 (hodgeStar2 F) 2 0 = F 2 0 := by
    rw [hodgeStar2_apply_20 (hodgeStar2 F) hs, hodgeStar2_apply_13 F hF]; linarith [hF 2 0]
  have k30 : hodgeStar2 (hodgeStar2 F) 3 0 = F 3 0 := by
    rw [hodgeStar2_apply_30 (hodgeStar2 F) hs, hodgeStar2_apply_12 F hF]; linarith [hF 3 0]
  have k21 : hodgeStar2 (hodgeStar2 F) 2 1 = F 2 1 := by
    rw [hodgeStar2_apply_21 (hodgeStar2 F) hs, hodgeStar2_apply_03 F hF]; linarith [hF 2 1]
  have k31 : hodgeStar2 (hodgeStar2 F) 3 1 = F 3 1 := by
    rw [hodgeStar2_apply_31 (hodgeStar2 F) hs, hodgeStar2_apply_02 F hF]; linarith [hF 3 1]
  have k32 : hodgeStar2 (hodgeStar2 F) 3 2 = F 3 2 := by
    rw [hodgeStar2_apply_32 (hodgeStar2 F) hs, hodgeStar2_apply_01 F hF]; linarith [hF 3 2]
  ext μ ν
  fin_cases μ <;> fin_cases ν
  · exact k00
  · exact k01
  · exact k02
  · exact k03
  · exact k10
  · exact k11
  · exact k12
  · exact k13
  · exact k20
  · exact k21
  · exact k22
  · exact k23
  · exact k30
  · exact k31
  · exact k32
  · exact k33

/-! ## D. The self-dual / anti-self-dual decomposition `∧²ℝ⁴ = ∧²₊ ⊕ ∧²₋` -/

/-- **The self-dual part** `F₊ = ½(F + ⋆F) = P₊F`, `P₊ = ½(1 + ⋆)`. -/
noncomputable def selfDualPart (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (F + hodgeStar2 F)

/-- **The anti-self-dual part** `F₋ = ½(F − ⋆F) = P₋F`, `P₋ = ½(1 − ⋆)`. -/
noncomputable def antiSelfDualPart (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (F - hodgeStar2 F)

/-- **`P₊ + P₋ = 1`** — a two-form is the sum of its self-dual and anti-self-dual parts. -/
theorem selfDualPart_add_antiSelfDualPart (F : Matrix (Fin 4) (Fin 4) ℝ) :
    selfDualPart F + antiSelfDualPart F = F := by
  ext i j
  simp only [selfDualPart, antiSelfDualPart, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- **A two-form is self-dual** when `⋆F = F`. -/
def IsSelfDual (F : Matrix (Fin 4) (Fin 4) ℝ) : Prop := hodgeStar2 F = F

/-- **A two-form is anti-self-dual** when `⋆F = −F`. -/
def IsAntiSelfDual (F : Matrix (Fin 4) (Fin 4) ℝ) : Prop := hodgeStar2 F = - F

/-- **The self-dual part is self-dual** `⋆F₊ = F₊`: the `+1` eigenvector of the star,
`⋆P₊F = P₊F`. Uses linearity and `⋆⋆F = F`. -/
theorem hodgeStar2_selfDualPart (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = - F j i) :
    IsSelfDual (selfDualPart F) := by
  unfold IsSelfDual selfDualPart
  rw [hodgeStar2_smul, hodgeStar2_add, hodgeStar2_involutive F hF]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- **The anti-self-dual part is anti-self-dual** `⋆F₋ = −F₋`: the `−1` eigenvector of the star,
`⋆P₋F = −P₋F`. -/
theorem hodgeStar2_antiSelfDualPart (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = - F j i) :
    IsAntiSelfDual (antiSelfDualPart F) := by
  unfold IsAntiSelfDual antiSelfDualPart
  rw [hodgeStar2_smul, hodgeStar2_sub, hodgeStar2_involutive F hF]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-! ## E. The Faraday tensor and the inhomogeneous Maxwell equation in dual form -/

/-- **`⋆(dA)` is a two-form** `(⋆F)_{νμ} = −(⋆F)_{μν}` for the Faraday tensor `F = dA`. -/
theorem hodgeStar2_faraday_antisymm (k A : Fin 4 → ℝ) (μ ν : Fin 4) :
    hodgeStar2 (faraday k A) ν μ = - hodgeStar2 (faraday k A) μ ν :=
  hodgeStar2_antisymm _ μ ν

/-- **The dual field strength squares back** `⋆⋆(dA) = dA`: the star is involutive on the physical
field strength `F = dA` (antisymmetric by `faraday_antisymm`). -/
theorem hodgeStar2_faraday_involutive (k A : Fin 4 → ℝ) :
    hodgeStar2 (hodgeStar2 (faraday k A)) = faraday k A :=
  hodgeStar2_involutive _ (fun i j => faraday_antisymm k A i j)

set_option maxHeartbeats 8000000 in
/-- **[Inhomogeneous Maxwell in dual form] `d⋆F = −⋆J`.** The homogeneous Bianchi cyclic sum of the
dual field strength `⋆F` equals minus the volume-form dual of the four-current `J^α = ∂_β F^{αβ}`
(`maxwellOp`):

  `k_λ (⋆F)_{μν} + k_μ (⋆F)_{νλ} + k_ν (⋆F)_{λμ} = − Σ_ρ ε_{λμνρ} (∂_β F^{ρβ})`,

for any antisymmetric `F`. Where `dF = 0` is automatic for `F = dA` (`faraday_bianchi`), the *dual*
cyclic identity `d⋆F` carries the source: it is the Hodge dual of the inhomogeneous Maxwell equation. -/
theorem hodgeStar2_bianchi_eq_current (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ)
    (hF : ∀ i j, F i j = - F j i) (lam μ ν : Fin 4) :
    k lam * hodgeStar2 F μ ν + k μ * hodgeStar2 F ν lam + k ν * hodgeStar2 F lam μ
      = - ∑ ρ, ((leviCivita4 lam μ ν ρ : ℤ) : ℝ) * maxwellOp F k ρ := by
  have Fd : ∀ i, F i i = 0 := fun i => by have := hF i i; linarith
  have a10 : F 1 0 = - F 0 1 := hF 1 0
  have a20 : F 2 0 = - F 0 2 := hF 2 0
  have a30 : F 3 0 = - F 0 3 := hF 3 0
  have a21 : F 2 1 = - F 1 2 := hF 2 1
  have a31 : F 3 1 = - F 1 3 := hF 3 1
  have a32 : F 3 2 = - F 2 3 := hF 3 2
  simp only [hodgeStar2_apply, maxwellOp, Fin.sum_univ_four]
  fin_cases lam <;> fin_cases μ <;> fin_cases ν <;>
    simp only [leviCivita4, Fd, a10, a20, a30, a21, a31, a32] <;>
    push_cast <;> ring

/-- **`d⋆F = 0` is exactly the source-free condition `J = 0`.** For an antisymmetric field strength,
the dual field `⋆F` is closed (its Bianchi cyclic sum vanishes for all `λμν`) if and only if the
four-current `∂_β F^{αβ}` vanishes — the vacuum inhomogeneous Maxwell equation read through the star. -/
theorem sourceFree_iff_hodgeStar2_closed (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ)
    (hF : ∀ i j, F i j = - F j i) :
    (∀ ρ, maxwellOp F k ρ = 0) ↔
      (∀ lam μ ν, k lam * hodgeStar2 F μ ν + k μ * hodgeStar2 F ν lam
        + k ν * hodgeStar2 F lam μ = 0) := by
  constructor
  · intro hJ lam μ ν
    rw [hodgeStar2_bianchi_eq_current F k hF lam μ ν]
    simp only [hJ, mul_zero, Finset.sum_const_zero, neg_zero]
  · intro hClosed ρ
    have h0 := hClosed 1 2 3
    have h1 := hClosed 0 2 3
    have h2 := hClosed 0 1 3
    have h3 := hClosed 0 1 2
    rw [hodgeStar2_bianchi_eq_current F k hF 1 2 3] at h0
    rw [hodgeStar2_bianchi_eq_current F k hF 0 2 3] at h1
    rw [hodgeStar2_bianchi_eq_current F k hF 0 1 3] at h2
    rw [hodgeStar2_bianchi_eq_current F k hF 0 1 2] at h3
    simp only [leviCivita4, Fin.sum_univ_four] at h0 h1 h2 h3
    push_cast at h0 h1 h2 h3
    have j0 : maxwellOp F k 0 = 0 := by linarith
    have j1 : maxwellOp F k 1 = 0 := by linarith
    have j2 : maxwellOp F k 2 = 0 := by linarith
    have j3 : maxwellOp F k 3 = 0 := by linarith
    fin_cases ρ
    · exact j0
    · exact j1
    · exact j2
    · exact j3

/-! ## F. Harmonic two-forms: the Hodge Laplacian and the self-dual type decomposition

Zucker's Hodge-theorem engine (§2): the codifferential `δ = −⋆d⋆` (2.3), the Hodge Laplacian
`□ = dδ + δd` (2.6), a form is harmonic `□F = 0` iff it is closed and co-closed (2.10 iii), and
harmonic forms decompose according to type (2.7, 2.10 iv). In four Euclidean dimensions the type
decomposition of two-forms is the self-dual / anti-self-dual split `∧² = ∧²₊ ⊕ ∧²₋` of §D, so both
`⋆`-eigenspaces consist of harmonic fields. Here `d` is the momentum-space exterior derivative (the
Bianchi cyclic sum) and `δF = ∂_β F^{αβ}` is the codifferential `maxwellOp` — the `−⋆d⋆` adjoint of
`d`, whose relation to `⋆` is `hodgeStar2_bianchi_eq_current` (`d⋆F = −⋆δF`). -/

/-- **Closed** `dF = 0`: the Bianchi cyclic sum vanishes on every index triple. -/
def IsClosed2 (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : Prop :=
  ∀ lam μ ν, k lam * F μ ν + k μ * F ν lam + k ν * F lam μ = 0

/-- **Co-closed (source-free)** `δF = 0`: the codifferential `δF = ∂_β F^{αβ}` (`maxwellOp`, the
`−⋆d⋆` adjoint of `d`, Zucker (2.3)) vanishes. -/
def IsCoclosed2 (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : Prop :=
  ∀ α, maxwellOp F k α = 0

/-- **Harmonic** `□F = 0`: closed and co-closed. The Hodge Laplacian `□ = dδ + δd` annihilates `F`
iff `dF = 0` and `δF = 0` (Zucker (2.6), (2.10)(iii)). -/
def IsHarmonic2 (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : Prop :=
  IsClosed2 F k ∧ IsCoclosed2 F k

/-- **`F = dA` is closed** `dF = 0` — automatic from `d² = 0` (`faraday_bianchi`). -/
theorem faraday_isClosed2 (k A : Fin 4 → ℝ) : IsClosed2 (faraday k A) k := faraday_bianchi k A

/-- **A field strength `F = dA` is harmonic iff it is source-free** `□F = 0 ⟺ δF = 0`: closure is
automatic, so harmonicity is exactly the vacuum Maxwell equation `∂_β F^{αβ} = 0`. -/
theorem faraday_isHarmonic2_iff (k A : Fin 4 → ℝ) :
    IsHarmonic2 (faraday k A) k ↔ IsCoclosed2 (faraday k A) k :=
  ⟨fun h => h.2, fun h => ⟨faraday_isClosed2 k A, h⟩⟩

/-- **A self-dual `F = dA` is harmonic** `⋆F = F ⟹ □F = 0`: self-duality forces co-closure, since
`δF = 0 ⟺ d⋆F = 0` (`sourceFree_iff_hodgeStar2_closed`) and `d⋆F = dF = 0`. The `+1` `⋆`-eigenspace
`∧²₊` — the self-dual sector of Zucker's type decomposition — consists of harmonic fields. -/
theorem selfDual_faraday_isHarmonic2 (k A : Fin 4 → ℝ)
    (hsd : IsSelfDual (faraday k A)) : IsHarmonic2 (faraday k A) k := by
  refine ⟨faraday_isClosed2 k A, ?_⟩
  change ∀ ρ, maxwellOp (faraday k A) k ρ = 0
  rw [sourceFree_iff_hodgeStar2_closed (faraday k A) k (faraday_antisymm k A)]
  intro lam μ ν
  rw [show hodgeStar2 (faraday k A) = faraday k A from hsd]
  exact faraday_bianchi k A lam μ ν

/-- **An anti-self-dual `F = dA` is harmonic** `⋆F = −F ⟹ □F = 0`: the `−1` `⋆`-eigenspace `∧²₋` —
the anti-self-dual sector of Zucker's type decomposition — is equally harmonic. -/
theorem antiSelfDual_faraday_isHarmonic2 (k A : Fin 4 → ℝ)
    (hasd : IsAntiSelfDual (faraday k A)) : IsHarmonic2 (faraday k A) k := by
  refine ⟨faraday_isClosed2 k A, ?_⟩
  change ∀ ρ, maxwellOp (faraday k A) k ρ = 0
  rw [sourceFree_iff_hodgeStar2_closed (faraday k A) k (faraday_antisymm k A)]
  intro lam μ ν
  rw [show hodgeStar2 (faraday k A) = - faraday k A from hasd]
  simp only [Matrix.neg_apply, mul_neg]
  linarith [faraday_bianchi k A lam μ ν]

/-! ## G. Electric–magnetic duality: `⋆` swaps `E` and `B`

The physical content of the Hodge star on the Faraday tensor, ported from the Gravitas `hodgeDualEM`
block swap (catept-main). Writing the electric field `E = (F_{01}, F_{02}, F_{03})` and the magnetic
field `B = (F_{23}, F_{31}, F_{12})`, the star exchanges them `(E, B) ↦ (B, E)` — electric–magnetic
duality (Euclidean convention `⋆⋆ = +1`; the Lorentzian star gives `(E, B) ↦ (B, −E)`). -/

/-- **Electric–magnetic duality** `⋆ : (E, B) ↦ (B, E)`: the star sends the electric field
`E = (F_{01}, F_{02}, F_{03})` to the magnetic field `B = (F_{23}, F_{31}, F_{12})` and back. -/
theorem hodgeStar2_swaps_electric_magnetic (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ i j, F i j = - F j i) :
    (hodgeStar2 F 0 1 = F 2 3 ∧ hodgeStar2 F 0 2 = F 3 1 ∧ hodgeStar2 F 0 3 = F 1 2) ∧
      (hodgeStar2 F 2 3 = F 0 1 ∧ hodgeStar2 F 3 1 = F 0 2 ∧ hodgeStar2 F 1 2 = F 0 3) := by
  refine ⟨⟨hodgeStar2_apply_01 F hF, ?_, hodgeStar2_apply_03 F hF⟩,
    hodgeStar2_apply_23 F hF, hodgeStar2_apply_31 F hF, hodgeStar2_apply_12 F hF⟩
  rw [hodgeStar2_apply_02 F hF]; linarith [hF 3 1]

/-- **A self-dual field has `E = B`** `⋆F = F ⟹ F_{01}=F_{23}, F_{02}=F_{31}, F_{03}=F_{12}`: the
electric and magnetic fields coincide (the self-dual sector `∧²₊`). -/
theorem selfDual_electric_eq_magnetic (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ i j, F i j = - F j i) (hsd : IsSelfDual F) :
    F 0 1 = F 2 3 ∧ F 0 2 = F 3 1 ∧ F 0 3 = F 1 2 := by
  have h01 : F 0 1 = F 2 3 := (congrFun (congrFun hsd 0) 1).symm.trans (hodgeStar2_apply_01 F hF)
  have h03 : F 0 3 = F 1 2 := (congrFun (congrFun hsd 0) 3).symm.trans (hodgeStar2_apply_03 F hF)
  have h02 : F 0 2 = F 3 1 := by
    have h := (congrFun (congrFun hsd 0) 2).symm.trans (hodgeStar2_apply_02 F hF)
    linarith [hF 3 1]
  exact ⟨h01, h02, h03⟩

/-- **An anti-self-dual field has `E = −B`** `⋆F = −F ⟹ F_{01}=−F_{23}, F_{02}=−F_{31}, F_{03}=−F_{12}`:
the electric field is minus the magnetic field (the anti-self-dual sector `∧²₋`). -/
theorem antiSelfDual_electric_eq_neg_magnetic (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ i j, F i j = - F j i) (hasd : IsAntiSelfDual F) :
    F 0 1 = - F 2 3 ∧ F 0 2 = - F 3 1 ∧ F 0 3 = - F 1 2 := by
  have h01 : F 0 1 = - F 2 3 := by
    have h := congrFun (congrFun hasd 0) 1
    rw [hodgeStar2_apply_01 F hF, Matrix.neg_apply] at h; linarith
  have h03 : F 0 3 = - F 1 2 := by
    have h := congrFun (congrFun hasd 0) 3
    rw [hodgeStar2_apply_03 F hF, Matrix.neg_apply] at h; linarith
  have h02 : F 0 2 = - F 3 1 := by
    have h := congrFun (congrFun hasd 0) 2
    rw [hodgeStar2_apply_02 F hF, Matrix.neg_apply] at h; linarith [hF 3 1]
  exact ⟨h01, h02, h03⟩

/-! ## H. The 3+1 Cauchy split: the Gauss constraints

Drago–Ginoux–Murro (*On the Cauchy problem for the Faraday tensor on globally hyperbolic manifolds with
timelike boundary*, arXiv:2306.06896, Lemma 2.2, Remarks 2.3–2.4) recast the Faraday Cauchy problem
`δF = j`, `dF = ζ` into two *dynamical* and two *constraint* equations for the electric field
`E = (F_{01}, F_{02}, F_{03})` (the 1-form `∂_t⌟F`) and the magnetic field `B = (F_{23}, F_{31}, F_{12})`
(the spatial 2-form). In flat momentum space the two constraints are the Gauss laws — `∇·B = 0`
(magnetic, from `dF = 0`) and `∇·E = ρ` (electric, the time component `ρ = J^0` of `δF = j`) — which
carry no time derivative, so they constrain the initial data, and propagate under the evolution because
the current is conserved (`δj = δ²F = 0`, the continuity equation of Remark 2.3,
`CovariantMaxwellLambShift.maxwell_current_conserved`). -/

/-- **Magnetic Gauss constraint** `∇·B = 0`: a closed field strength (`dF = 0`) has
`k·B = k_1 F_{23} + k_2 F_{31} + k_3 F_{12} = 0` — the spatial Bianchi identity, "no magnetic
monopoles", a constraint on the Cauchy data. -/
theorem magneticGauss_of_closed (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ)
    (hc : IsClosed2 F k) : k 1 * F 2 3 + k 2 * F 3 1 + k 3 * F 1 2 = 0 := hc 1 2 3

/-- **Magnetic Gauss for `F = dA`** `∇·B = 0` — automatic from `d² = 0` (`faraday_bianchi`). -/
theorem faraday_magneticGauss (k A : Fin 4 → ℝ) :
    k 1 * faraday k A 2 3 + k 2 * faraday k A 3 1 + k 3 * faraday k A 1 2 = 0 :=
  faraday_bianchi k A 1 2 3

/-- **Electric Gauss constraint** `∇·E = ρ`: the charge density `ρ = J^0 = ∂_β F^{0β}` (`maxwellOp`, the
time component of `δF = j`) is the divergence of the electric field,
`k·E = k_1 F_{01} + k_2 F_{02} + k_3 F_{03}`, for any antisymmetric field strength. -/
theorem chargeDensity_eq_electricDivergence (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ)
    (hF : ∀ i j, F i j = - F j i) :
    maxwellOp F k 0 = k 1 * F 0 1 + k 2 * F 0 2 + k 3 * F 0 3 := by
  have h00 : F 0 0 = 0 := by have := hF 0 0; linarith
  simp only [maxwellOp, Fin.sum_univ_four, h00]
  ring

/-- **Vacuum electric Gauss** `∇·E = 0`: a source-free field strength (`δF = 0`, `IsCoclosed2`) has zero
charge density, so the electric field is divergence-free `k·E = 0`. -/
theorem sourceFree_electricGauss (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ)
    (hF : ∀ i j, F i j = - F j i) (hj : IsCoclosed2 F k) :
    k 1 * F 0 1 + k 2 * F 0 2 + k 3 * F 0 3 = 0 := by
  rw [← chargeDensity_eq_electricDivergence F k hF]; exact hj 0

/-! ## I. The variational core: `d` and `δ` are formal adjoints

The linear-analytic identity the Faraday Cauchy problem's analysis rests on. On plane waves there is no
boundary term, so the exterior derivative `d` and the codifferential `δ` are formal adjoints and
`D = d + δ` is formally self-adjoint — the property behind the variational derivation of Maxwell's
equations (Drago–Ginoux–Murro, Remark 1.2.4) and the self-adjointness of `D` used to build the Green
operators and the pre-symplectic structure (§5). Here `dα = faraday k α = k ∧ α` (the exterior
derivative of the one-form `α`), `δF = maxwellOp F k = ∂_β F^{αβ}` (the codifferential of the two-form
`F`), with the Frobenius pairings `⟨F, G⟩ = ∑_{μν} F_{μν} G_{μν}` on two-forms and
`⟨α, β⟩ = ∑_μ α_μ β_μ` on one-forms.

The functional-analytic well-posedness on globally hyperbolic manifolds with timelike boundary (Ginoux's
symmetric-hyperbolic theorem [17, Thm 1.2], the Green operators and de Rham cohomology of §5) is the one
external analytic input; it is not part of this algebraic core. -/

/-- **`d` and `δ` are formal adjoints** `⟨dα, F⟩ = −2⟨α, δF⟩` (no boundary term on plane waves), for any
antisymmetric field strength `F`. This is the integration by parts behind the variational principle
(Remark 1.2.4) and the formal self-adjointness of `D = d + δ` (§5). -/
theorem d_codifferential_adjoint (α k : Fin 4 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ i j, F i j = - F j i) :
    (∑ μ, ∑ ν, faraday k α μ ν * F μ ν) = - 2 * ∑ ν, α ν * maxwellOp F k ν := by
  have a10 : F 1 0 = - F 0 1 := hF 1 0
  have a20 : F 2 0 = - F 0 2 := hF 2 0
  have a30 : F 3 0 = - F 0 3 := hF 3 0
  have a21 : F 2 1 = - F 1 2 := hF 2 1
  have a31 : F 3 1 = - F 1 3 := hF 3 1
  have a32 : F 3 2 = - F 2 3 := hF 3 2
  have d0 : F 0 0 = 0 := by have := hF 0 0; linarith
  have d1 : F 1 1 = 0 := by have := hF 1 1; linarith
  have d2 : F 2 2 = 0 := by have := hF 2 2; linarith
  have d3 : F 3 3 = 0 := by have := hF 3 3; linarith
  simp only [faraday, maxwellOp, Matrix.of_apply, Fin.sum_univ_four, d0, d1, d2, d3,
    a10, a20, a30, a21, a31, a32]
  ring

@[expose] public section

/-- The Euclidean Maxwell action of one Fourier mode,
`I_k(A) = (1/2) ∑_{μ,ν} F_{μν}(k,A)^2`. -/
noncomputable def maxwellFourierAction (k A : Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ μ, ∑ ν, faraday k A μ ν ^ 2

private lemma faradayLine_hasDerivAt
    (k A α : Fin 4 → ℝ) (μ ν : Fin 4) :
    HasDerivAt
      (fun t : ℝ => faraday k (fun i => A i + t * α i) μ ν)
      (faraday k α μ ν) 0 := by
  have hline : (fun t : ℝ => faraday k (fun i => A i + t * α i) μ ν) =
      fun t : ℝ => faraday k A μ ν + t * faraday k α μ ν := by
    funext t
    simp only [faraday, Matrix.of_apply]
    ring
  rw [hline]
  have h := (hasDerivAt_const (x := (0 : ℝ)) (faraday k A μ ν)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (faraday k α μ ν))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun t => by
      simp only [Pi.add_apply, id_eq]
  · simp

/-- The genuine directional derivative of the Fourier Maxwell action is
`⟨dA,dα⟩`. This constructs the action derivative rather than accepting a
post-integration-by-parts first variation as data. -/
lemma maxwellFourierAction_line_hasDerivAt (k A α : Fin 4 → ℝ) :
    HasDerivAt
      (fun t : ℝ => maxwellFourierAction k (fun i => A i + t * α i))
      (∑ μ, ∑ ν, faraday k A μ ν * faraday k α μ ν) 0 := by
  have hterms : ∀ μ ν : Fin 4,
      HasDerivAt
        (fun t : ℝ => faraday k (fun i => A i + t * α i) μ ν ^ 2)
        (2 * faraday k A μ ν * faraday k α μ ν) 0 := by
    intro μ ν
    have h := (faradayLine_hasDerivAt k A α μ ν).pow 2
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun t => by
        simp only [Pi.pow_apply]
    · norm_num [faraday]
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ μ : Fin 4, ∑ ν : Fin 4,
        faraday k (fun i => A i + t * α i) μ ν ^ 2)
      (∑ μ : Fin 4, ∑ ν : Fin 4,
        2 * faraday k A μ ν * faraday k α μ ν) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => hterms μ ν
  have hscaled := hsum.const_mul (1 / 2 : ℝ)
  have haction : HasDerivAt
      (fun t : ℝ => maxwellFourierAction k (fun i => A i + t * α i))
      ((1 / 2 : ℝ) * ∑ μ, ∑ ν,
        2 * faraday k A μ ν * faraday k α μ ν) 0 := by
    simpa only [maxwellFourierAction] using hscaled
  apply haction.congr_deriv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-- **The variational Maxwell equation** `⟨dA, dα⟩ = −2⟨α, δdA⟩`: the derivative of the action
`I(A) = ½‖dA‖²` in the direction of the one-form `α` is `−2⟨α, δdA⟩` (Remark 1.2.4, boundaryless case). -/
theorem maxwell_variational (A k α : Fin 4 → ℝ) :
    (∑ μ, ∑ ν, faraday k A μ ν * faraday k α μ ν)
      = - 2 * ∑ ν, α ν * maxwellOp (faraday k A) k ν := by
  rw [← d_codifferential_adjoint α k (faraday k A) (fun i j => faraday_antisymm k A i j)]
  exact Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => mul_comm _ _))

/-- **The variational principle yields Maxwell's equation** — `A` is a stationary point of the action
for every direction `α` iff the source-free Maxwell equation `δdA = 0` (`∂_β (dA)^{αβ} = 0`) holds. The
degenerate direction `α = δdA` forces the current to vanish (its squared norm is zero). -/
theorem maxwell_stationary_iff_sourceFree (A k : Fin 4 → ℝ) :
    (∀ α, ∑ μ, ∑ ν, faraday k A μ ν * faraday k α μ ν = 0)
      ↔ (∀ ν, maxwellOp (faraday k A) k ν = 0) := by
  constructor
  · intro h ν
    have hsq : ∑ i, maxwellOp (faraday k A) k i * maxwellOp (faraday k A) k i = 0 := by
      have hv := maxwell_variational A k (maxwellOp (faraday k A) k)
      rw [h (maxwellOp (faraday k A) k)] at hv
      linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (maxwellOp (faraday k A) k i))).mp hsq ν (Finset.mem_univ ν)
    exact mul_self_eq_zero.mp hz
  · intro h α
    rw [maxwell_variational A k α]
    simp only [h, mul_zero, Finset.sum_const_zero]

/-- Stationarity of the constructed Fourier Maxwell action along every
gauge-potential direction is equivalent to the source-free Maxwell equation. -/
@[zil_level physical_theorem]
lemma maxwellFourierAction_stationary_iff_sourceFree (A k : Fin 4 → ℝ) :
    (∀ α : Fin 4 → ℝ, deriv (fun t : ℝ =>
      maxwellFourierAction k (fun i => A i + t * α i)) 0 = 0) ↔
      ∀ ν, maxwellOp (faraday k A) k ν = 0 := by
  constructor
  · intro h
    apply (maxwell_stationary_iff_sourceFree A k).mp
    intro α
    rw [← (maxwellFourierAction_line_hasDerivAt k A α).deriv]
    exact h α
  · intro h α
    rw [(maxwellFourierAction_line_hasDerivAt k A α).deriv]
    exact (maxwell_stationary_iff_sourceFree A k).mpr h α

end

/-! ## J. The Maxwell-compactness mechanism

Why a bounded `H(curl) ∩ H(div)` sequence is `L²`-compact — the algebraic core of Maxwell compactness
(Chaumont-Frelet–Droniou–Lemaire, *Commuting quasi-interpolators and Maxwell compactness for a polytopal
de Rham complex*, arXiv:2510.18835), the driving-operator analogue of Rellich–Kondrachov for the de Rham
complex `0 → H(grad) → H(curl) → H(div) → L² → 0` (1.1). At the Fourier symbol `∂ ↦ i k` the curl is
`k × u`, the divergence is `k · u`, and the **Gaffney/Lagrange identity** ties their energies to the
`L²`-energy: `‖k×u‖² + (k·u)² = ‖k‖²‖u‖²`. Hence `‖u‖²` decays like `‖k‖⁻²` when the curl and divergence
energies are bounded — the mode-wise decay that yields compactness. The continuous complex (1.1) itself
is `SpaceAndTime.Space.Derivatives.Curl` (`curl_of_grad_eq_zero`, `div_of_curl_eq_zero`,
`exists_grad_of_curl_zero`); the discrete polytopal complex, quasi-interpolators and the compactness proof
are the paper's numerical-analysis content, external to this algebraic identity. -/

/-- **The Gaffney/Lagrange identity** `‖k×u‖² + (k·u)² = ‖k‖²‖u‖²`: for the Fourier symbol of the de Rham
complex, the curl-energy plus the divergence-energy of a mode equals `‖k‖²` times its `L²`-energy. This is
the mechanism of Maxwell compactness — it converts a bound on `curl` and `div` into `‖k‖²`-weighted
control of the field. -/
theorem maxwell_gaffney_symbol (k1 k2 k3 u1 u2 u3 : ℝ) :
    ((k2 * u3 - k3 * u2) ^ 2 + (k3 * u1 - k1 * u3) ^ 2 + (k1 * u2 - k2 * u1) ^ 2)
      + (k1 * u1 + k2 * u2 + k3 * u3) ^ 2
      = (k1 ^ 2 + k2 ^ 2 + k3 ^ 2) * (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) := by ring

/-- **Mode-wise `‖k‖⁻²` decay** `‖u‖² = (‖k×u‖² + (k·u)²)/‖k‖²`: at each nonzero frequency the `L²`-energy
of a field is its curl-and-divergence energy divided by `‖k‖²`, so a uniform bound on the latter forces
the high-frequency `L²`-energy to zero — the Fourier-decay condition behind Rellich compactness. -/
theorem maxwell_fieldEnergy_eq (k1 k2 k3 u1 u2 u3 : ℝ) (hk : k1 ^ 2 + k2 ^ 2 + k3 ^ 2 ≠ 0) :
    u1 ^ 2 + u2 ^ 2 + u3 ^ 2
      = (((k2 * u3 - k3 * u2) ^ 2 + (k3 * u1 - k1 * u3) ^ 2 + (k1 * u2 - k2 * u1) ^ 2)
          + (k1 * u1 + k2 * u2 + k3 * u3) ^ 2) / (k1 ^ 2 + k2 ^ 2 + k3 ^ 2) := by
  rw [eq_div_iff hk, maxwell_gaffney_symbol]; ring

/-- **`div ∘ curl = 0`** at the symbol level `k · (k × u) = 0` — the second `d² = 0` of the de Rham
complex (1.1); its smooth form is `Curl.div_of_curl_eq_zero`. -/
theorem divCurl_symbol_eq_zero (k1 k2 k3 u1 u2 u3 : ℝ) :
    k1 * (k2 * u3 - k3 * u2) + k2 * (k3 * u1 - k1 * u3) + k3 * (k1 * u2 - k2 * u1) = 0 := by ring

/-- **`curl ∘ grad = 0`** at the symbol level `k × (φ k) = 0` — the first `d² = 0` of the de Rham complex
(1.1); its smooth form is `Curl.curl_of_grad_eq_zero`. -/
theorem curlGrad_symbol_eq_zero (k1 k2 k3 φ : ℝ) :
    k2 * (k3 * φ) - k3 * (k2 * φ) = 0 ∧ k3 * (k1 * φ) - k1 * (k3 * φ) = 0
      ∧ k1 * (k2 * φ) - k2 * (k1 * φ) = 0 :=
  ⟨by ring, by ring, by ring⟩

/-! ## K. Vytheeswaran's antisymmetric-tensor realization of the Proca vector -/

@[expose] public section

/-- Vytheeswaran Eq. (3.22) on a Fourier mode:
`F_μ = ½ ε_{μνλσ} k_ν B_{λσ}`.  The repository's existing operators express this
without a new tensor calculus as the Maxwell codifferential of the Hodge-dual two-form,
`δ(⋆B)`. -/
noncomputable def vytheeswaranTensorDualVector
    (B : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : Fin 4 → ℝ :=
  maxwellOp (hodgeStar2 B) k

set_option maxHeartbeats 2000000 in
/-- The definition expands to the component formula in paper Eq. (3.22). -/
lemma vytheeswaranTensorDualVector_apply
    (B : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) (μ : Fin 4) :
    vytheeswaranTensorDualVector B k μ =
      (1 / 2 : ℝ) * ∑ ν, ∑ a, ∑ b,
        ((leviCivita4 μ ν a b : ℤ) : ℝ) * k ν * B a b := by
  fin_cases μ <;>
    simp only [vytheeswaranTensorDualVector, maxwellOp, hodgeStar2,
      Matrix.of_apply, Fin.sum_univ_four, leviCivita4] <;>
    push_cast <;> ring

set_option maxHeartbeats 2000000 in
/-- The tensor-dual vector is transverse, `k^μF_μ = 0`.  This is the momentum-space
form of the divergence condition used immediately before paper Eq. (3.22). -/
lemma vytheeswaranTensorDualVector_conserved
    (B : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    ∑ μ, k μ * vytheeswaranTensorDualVector B k μ = 0 := by
  simpa only [vytheeswaranTensorDualVector, maxwellCurrent] using
    maxwell_current_conserved (hodgeStar2 B) k
      (fun μ ν => hodgeStar2_antisymm B ν μ)

set_option maxHeartbeats 2000000 in
/-- An exact two-form `dΛ` contributes no tensor-dual vector: `δ⋆dΛ = 0` at every
Fourier mode. -/
lemma vytheeswaranTensorDualVector_faradayGauge_eq_zero
    (k Λ : Fin 4 → ℝ) : vytheeswaranTensorDualVector (faraday k Λ) k = 0 := by
  funext μ
  fin_cases μ <;>
    simp only [vytheeswaranTensorDualVector, maxwellOp, hodgeStar2, faraday,
      Matrix.of_apply, Fin.sum_univ_four, leviCivita4, Pi.zero_apply] <;>
    push_cast <;> ring

/-- The tensor-dual construction is additive in the two-form potential. -/
lemma vytheeswaranTensorDualVector_add
    (B C : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    vytheeswaranTensorDualVector (B + C) k =
      vytheeswaranTensorDualVector B k + vytheeswaranTensorDualVector C k := by
  funext μ
  simp only [vytheeswaranTensorDualVector, hodgeStar2_add, maxwellOp,
    Matrix.add_apply, add_mul, Finset.sum_add_distrib, Pi.add_apply]

/-- The Eq. (3.22) vector is invariant under the antisymmetric-tensor gauge action
`B ↦ B + dΛ`. -/
lemma vytheeswaranTensorDualVector_gauge_invariant
    (B : Matrix (Fin 4) (Fin 4) ℝ) (k Λ : Fin 4 → ℝ) :
    vytheeswaranTensorDualVector (B + faraday k Λ) k =
      vytheeswaranTensorDualVector B k := by
  rw [vytheeswaranTensorDualVector_add,
    vytheeswaranTensorDualVector_faradayGauge_eq_zero, add_zero]

end

/-! ## K.1. Lorentzian Maxwell--tensor action and its first-class constraints -/

@[expose] public section

/-- The Fourier symbol of the antisymmetric three-form field strength
`G_{μνρ} = ∂_[μ B_{νρ]}` appearing in Vytheeswaran Eqs. (3.22)--(3.30).
The derivative convention omits the Fourier factor `i`, consistently with `faraday`. -/
def vytheeswaranThreeForm
    (B : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun μ ν ρ => k μ * B ν ρ + k ν * B ρ μ + k ρ * B μ ν

/-- The exact two-form gauge shift `B ↦ B + dΛ` leaves `G = dB` unchanged.
This is the Fourier-symbol realization of `d² = 0`. -/
lemma vytheeswaranThreeForm_faradayGauge
    (B : Matrix (Fin 4) (Fin 4) ℝ) (k Λ : Fin 4 → ℝ) :
    vytheeswaranThreeForm (B + faraday k Λ) k =
      vytheeswaranThreeForm B k := by
  funext μ ν ρ
  simp only [vytheeswaranThreeForm, Matrix.add_apply, faraday, Matrix.of_apply]
  ring

/-- The Maxwell Fourier symbol is unchanged by `A ↦ A + λk`. -/
lemma faraday_vectorGauge (A k : Fin 4 → ℝ) (lambda : ℝ) :
    faraday k (A + lambda • k) = faraday k A := by
  ext μ ν
  simp only [faraday, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The mostly-minus Lorentz contraction `F_{μν}F^{μν}`, using the existing
`minkowskiSign4 = (1,-1,-1,-1)` rather than introducing a second metric carrier. -/
def vytheeswaranMinkowskiTwoFormContraction
    (F : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ μ, ∑ ν, minkowskiSign4 μ * minkowskiSign4 ν * F μ ν ^ 2

/-- The mostly-minus Lorentz contraction `G_{μνρ}G^{μνρ}`. -/
def vytheeswaranMinkowskiThreeFormContraction
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ μ, ∑ ν, ∑ ρ, minkowskiSign4 μ * minkowskiSign4 ν *
    minkowskiSign4 ρ * G μ ν ρ ^ 2

set_option maxHeartbeats 4000000 in
/-- The mixed coupling used below is exactly the paper's normalized topological
coupling:
`A_μ (⋆dB)^μ = (1/6) ε^{μνρσ} A_μ G_{νρσ}`.
This proves the coefficient relating Eq. (3.22) to Eq. (3.27), rather than treating
the two displayed forms as interchangeable by convention. -/
lemma vytheeswaranTopologicalCoupling_eq_epsilonThreeForm
    (A k : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    (∑ μ, A μ * vytheeswaranTensorDualVector B k μ) =
      (1 / 6 : ℝ) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
        ((leviCivita4 μ ν ρ σ : ℤ) : ℝ) * A μ *
          vytheeswaranThreeForm B k ν ρ σ := by
  simp only [vytheeswaranTensorDualVector, maxwellOp, hodgeStar2,
    vytheeswaranThreeForm, Matrix.of_apply, Fin.sum_univ_four, leviCivita4]
  push_cast
  ring

/-- Vytheeswaran Eq. (3.27) on a Lorentzian Fourier mode:
`-F²/4 - m² A_μ (⋆dB)^μ + m² G²/12`.
The middle expression reuses `vytheeswaranTensorDualVector`; expanding it gives
`-(m²/6) ε^{μνρσ} A_μ G_{νρσ}`. -/
noncomputable def vytheeswaranMaxwellTensorLagrangian
    (massSq : ℝ) (A k : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  -(1 / 4 : ℝ) * vytheeswaranMinkowskiTwoFormContraction (faraday k A)
    - massSq * ∑ μ, A μ * vytheeswaranTensorDualVector B k μ
    + massSq / 12 * vytheeswaranMinkowskiThreeFormContraction
      (vytheeswaranThreeForm B k)

/-- **Gauge invariance of Eq. (3.27).**  The Lorentzian Fourier-mode action density
is invariant simultaneously under `A ↦ A + λk` and `B ↦ B + dΛ`.
The mixed term uses the already-proved transversality of `⋆dB`. -/
lemma vytheeswaranMaxwellTensorLagrangian_gauge_invariant
    (massSq lambda : ℝ) (A k Λ : Fin 4 → ℝ)
    (B : Matrix (Fin 4) (Fin 4) ℝ) :
    vytheeswaranMaxwellTensorLagrangian massSq (A + lambda • k) k
        (B + faraday k Λ) =
      vytheeswaranMaxwellTensorLagrangian massSq A k B := by
  rw [vytheeswaranMaxwellTensorLagrangian,
    vytheeswaranMaxwellTensorLagrangian, faraday_vectorGauge,
    vytheeswaranTensorDualVector_gauge_invariant,
    vytheeswaranThreeForm_faradayGauge]
  have htrans := vytheeswaranTensorDualVector_conserved B k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib]
  rw [show (∑ x, lambda * k x * vytheeswaranTensorDualVector B k x) =
      lambda * ∑ x, k x * vytheeswaranTensorDualVector B k x by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring]
  rw [htrans]
  ring

/-- Linear canonical observables for one Fourier mode of the Maxwell--tensor phase
space.  Spatial antisymmetric tensors are encoded by their three independent dual
components; the temporal tensor components are retained separately so that the four
primary and four secondary constraints of Eqs. (3.28), (3.30) are represented. -/
structure VytheeswaranCanonicalLinearObservable where
  constant : ℝ
  vectorQ : Fin 4 → ℝ
  vectorP : Fin 4 → ℝ
  tensorSpatialQ : Fin 3 → ℝ
  tensorSpatialP : Fin 3 → ℝ
  tensorTemporalQ : Fin 3 → ℝ
  tensorTemporalP : Fin 3 → ℝ

/-- The canonical Poisson bracket of linear Maxwell--tensor observables. -/
def vytheeswaranCanonicalBracket
    (X Y : VytheeswaranCanonicalLinearObservable) : ℝ :=
  (∑ μ, (X.vectorQ μ * Y.vectorP μ - X.vectorP μ * Y.vectorQ μ)) +
  (∑ i, (X.tensorSpatialQ i * Y.tensorSpatialP i -
    X.tensorSpatialP i * Y.tensorSpatialQ i)) +
  (∑ i, (X.tensorTemporalQ i * Y.tensorTemporalP i -
    X.tensorTemporalP i * Y.tensorTemporalQ i))

/-- The vector primary constraint `π⁰ = 0` from Eq. (3.28). -/
def vytheeswaranPrimaryVectorConstraint : VytheeswaranCanonicalLinearObservable :=
  { constant := 0, vectorQ := 0, vectorP := ![1, 0, 0, 0],
    tensorSpatialQ := 0, tensorSpatialP := 0,
    tensorTemporalQ := 0, tensorTemporalP := 0 }

/-- The three tensor primary constraints `π^{0i} = 0` from Eq. (3.28). -/
def vytheeswaranPrimaryTensorConstraint (j : Fin 3) :
    VytheeswaranCanonicalLinearObservable :=
  { constant := 0, vectorQ := 0, vectorP := 0,
    tensorSpatialQ := 0, tensorSpatialP := 0,
    tensorTemporalQ := 0, tensorTemporalP := fun i => if i = j then 1 else 0 }

/-- The Gauss secondary constraint
`-∂ᵢπⁱ + (m²/2) ε^{ijk}∂ᵢB_{jk}=0` from Eq. (3.30), with the
spatial two-form represented by its Hodge-dual three-vector. -/
def vytheeswaranSecondaryGaussConstraint
    (massSq : ℝ) (k : Fin 3 → ℝ) : VytheeswaranCanonicalLinearObservable :=
  { constant := 0, vectorQ := 0, vectorP := ![0, -k 0, -k 1, -k 2],
    tensorSpatialQ := fun i => massSq * k i, tensorSpatialP := 0,
    tensorTemporalQ := 0, tensorTemporalP := 0 }

/-- The three tensor secondary constraints `∂ᵢπ^{ij}=0` from Eq. (3.30),
written in the independent spatial-dual momentum coordinates. -/
def vytheeswaranSecondaryTensorConstraint
    (k : Fin 3 → ℝ) (j : Fin 3) : VytheeswaranCanonicalLinearObservable :=
  { constant := 0, vectorQ := 0, vectorP := 0,
    tensorSpatialQ := 0,
    tensorSpatialP := fun l => ∑ i,
      ((leviCivita4 0 i.succ j.succ l.succ : ℤ) : ℝ) * k i,
    tensorTemporalQ := 0, tensorTemporalP := 0 }

/-- The ordered family of all eight primary and secondary constraints:
`(π⁰, π⁰¹, π⁰², π⁰³, C, D¹, D², D³)`. -/
def vytheeswaranConstraint
    (massSq : ℝ) (k : Fin 3 → ℝ) (a : Fin 8) :
    VytheeswaranCanonicalLinearObservable :=
  ![vytheeswaranPrimaryVectorConstraint,
    vytheeswaranPrimaryTensorConstraint 0,
    vytheeswaranPrimaryTensorConstraint 1,
    vytheeswaranPrimaryTensorConstraint 2,
    vytheeswaranSecondaryGaussConstraint massSq k,
    vytheeswaranSecondaryTensorConstraint k 0,
    vytheeswaranSecondaryTensorConstraint k 1,
    vytheeswaranSecondaryTensorConstraint k 2] a

@[simp] lemma vytheeswaranBracket_primaryVector_primaryVector :
    vytheeswaranCanonicalBracket vytheeswaranPrimaryVectorConstraint
      vytheeswaranPrimaryVectorConstraint = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryVectorConstraint]

@[simp] lemma vytheeswaranBracket_primaryVector_primaryTensor (j : Fin 3) :
    vytheeswaranCanonicalBracket vytheeswaranPrimaryVectorConstraint
      (vytheeswaranPrimaryTensorConstraint j) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryVectorConstraint,
    vytheeswaranPrimaryTensorConstraint]

@[simp] lemma vytheeswaranBracket_primaryTensor_primaryVector (j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranPrimaryTensorConstraint j)
      vytheeswaranPrimaryVectorConstraint = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryVectorConstraint,
    vytheeswaranPrimaryTensorConstraint]

@[simp] lemma vytheeswaranBracket_primaryTensor_primaryTensor (i j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranPrimaryTensorConstraint i)
      (vytheeswaranPrimaryTensorConstraint j) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryTensorConstraint]

@[simp] lemma vytheeswaranBracket_primaryVector_secondaryGauss
    (massSq : ℝ) (k : Fin 3 → ℝ) :
    vytheeswaranCanonicalBracket vytheeswaranPrimaryVectorConstraint
      (vytheeswaranSecondaryGaussConstraint massSq k) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryVectorConstraint,
    vytheeswaranSecondaryGaussConstraint]

@[simp] lemma vytheeswaranBracket_secondaryGauss_primaryVector
    (massSq : ℝ) (k : Fin 3 → ℝ) :
    vytheeswaranCanonicalBracket (vytheeswaranSecondaryGaussConstraint massSq k)
      vytheeswaranPrimaryVectorConstraint = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryVectorConstraint,
    vytheeswaranSecondaryGaussConstraint]

@[simp] lemma vytheeswaranBracket_primaryTensor_secondaryGauss
    (massSq : ℝ) (k : Fin 3 → ℝ) (j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranPrimaryTensorConstraint j)
      (vytheeswaranSecondaryGaussConstraint massSq k) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryTensorConstraint,
    vytheeswaranSecondaryGaussConstraint]

@[simp] lemma vytheeswaranBracket_secondaryGauss_primaryTensor
    (massSq : ℝ) (k : Fin 3 → ℝ) (j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranSecondaryGaussConstraint massSq k)
      (vytheeswaranPrimaryTensorConstraint j) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryTensorConstraint,
    vytheeswaranSecondaryGaussConstraint]

@[simp] lemma vytheeswaranBracket_primaryVector_secondaryTensor
    (k : Fin 3 → ℝ) (j : Fin 3) :
    vytheeswaranCanonicalBracket vytheeswaranPrimaryVectorConstraint
      (vytheeswaranSecondaryTensorConstraint k j) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryVectorConstraint,
    vytheeswaranSecondaryTensorConstraint]

@[simp] lemma vytheeswaranBracket_secondaryTensor_primaryVector
    (k : Fin 3 → ℝ) (j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranSecondaryTensorConstraint k j)
      vytheeswaranPrimaryVectorConstraint = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryVectorConstraint,
    vytheeswaranSecondaryTensorConstraint]

@[simp] lemma vytheeswaranBracket_primaryTensor_secondaryTensor
    (k : Fin 3 → ℝ) (i j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranPrimaryTensorConstraint i)
      (vytheeswaranSecondaryTensorConstraint k j) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryTensorConstraint,
    vytheeswaranSecondaryTensorConstraint]

@[simp] lemma vytheeswaranBracket_secondaryTensor_primaryTensor
    (k : Fin 3 → ℝ) (i j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranSecondaryTensorConstraint k j)
      (vytheeswaranPrimaryTensorConstraint i) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranPrimaryTensorConstraint,
    vytheeswaranSecondaryTensorConstraint]

@[simp] lemma vytheeswaranBracket_secondaryGauss_secondaryGauss
    (massSq : ℝ) (k : Fin 3 → ℝ) :
    vytheeswaranCanonicalBracket (vytheeswaranSecondaryGaussConstraint massSq k)
      (vytheeswaranSecondaryGaussConstraint massSq k) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranSecondaryGaussConstraint]

@[simp] lemma vytheeswaranBracket_secondaryTensor_secondaryTensor
    (k : Fin 3 → ℝ) (i j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranSecondaryTensorConstraint k i)
      (vytheeswaranSecondaryTensorConstraint k j) = 0 := by
  simp [vytheeswaranCanonicalBracket, vytheeswaranSecondaryTensorConstraint]

@[simp] lemma vytheeswaranBracket_secondaryGauss_secondaryTensor
    (massSq : ℝ) (k : Fin 3 → ℝ) (j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranSecondaryGaussConstraint massSq k)
      (vytheeswaranSecondaryTensorConstraint k j) = 0 := by
  fin_cases j <;>
    simp [vytheeswaranCanonicalBracket, vytheeswaranSecondaryGaussConstraint,
      vytheeswaranSecondaryTensorConstraint, Fin.sum_univ_three, leviCivita4] <;> ring

@[simp] lemma vytheeswaranBracket_secondaryTensor_secondaryGauss
    (massSq : ℝ) (k : Fin 3 → ℝ) (j : Fin 3) :
    vytheeswaranCanonicalBracket (vytheeswaranSecondaryTensorConstraint k j)
      (vytheeswaranSecondaryGaussConstraint massSq k) = 0 := by
  fin_cases j <;>
    simp [vytheeswaranCanonicalBracket, vytheeswaranSecondaryGaussConstraint,
      vytheeswaranSecondaryTensorConstraint, Fin.sum_univ_three, leviCivita4] <;> ring

/-- **Vytheeswaran Eqs. (3.28), (3.30): all eight constraints are first class.**
Every pairwise canonical Poisson bracket vanishes.  The nontrivial Gauss/tensor
cross-bracket cancels because a symmetric product `kᵢkₗ` contracts with
`ε^{ijl}`. -/
lemma vytheeswaranConstraint_firstClass
    (massSq : ℝ) (k : Fin 3 → ℝ) (a b : Fin 8) :
    vytheeswaranCanonicalBracket (vytheeswaranConstraint massSq k a)
      (vytheeswaranConstraint massSq k b) = 0 := by
  fin_cases a <;> fin_cases b <;> simp [vytheeswaranConstraint]

/-! ## K.2. The gauge-invariant and canonical Hamiltonian densities -/

/-- Squared Euclidean norm of a spatial three-vector, used only for the spatial
Cauchy slice of the Lorentzian Hamiltonian. -/
def vytheeswaranSpatialVectorNormSq (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Spatial scalar product on the three independent Cauchy components. -/
def vytheeswaranSpatialDot (u v : Fin 3 → ℝ) : ℝ := ∑ i, u i * v i

/-- Sum of squares of the spatial components of a spacetime two-form. -/
def vytheeswaranSpatialTwoFormNormSq
    (F : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, F i.succ j.succ ^ 2

/-- Sum of squares of the purely spatial components `G_{ijk}`. -/
def vytheeswaranSpatialThreeFormNormSq
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, G i.succ j.succ l.succ ^ 2

/-- Sum of squares of the temporal-spatial components `G_{0ij}`. -/
def vytheeswaranTemporalThreeFormNormSq
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, G 0 i.succ j.succ ^ 2

/-- Spatial Fourier divergence `∂ᵢπⁱ`, with the common Fourier factor suppressed. -/
def vytheeswaranSpatialDivergence
    (k : Fin 4 → ℝ) (pi : Fin 3 → ℝ) : ℝ :=
  ∑ i, k i.succ * pi i

/-- Vytheeswaran Eq. (3.23), the gauge-invariant Hamiltonian density written
entirely using `F = ⋆dB`, its Faraday tensor, and `G=dB`.
This is one Fourier mode; spatial integration and functional domains remain separate. -/
noncomputable def vytheeswaranEq323HamiltonianDensity
    (massSq : ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ)
    (pi : Fin 3 → ℝ) : ℝ :=
  vytheeswaranSpatialVectorNormSq pi / 2 +
    vytheeswaranSpatialTwoFormNormSq
      (faraday k (vytheeswaranTensorDualVector B k)) / 4 +
    vytheeswaranTensorDualVector B k 0 * vytheeswaranSpatialDivergence k pi +
    massSq / 12 *
      vytheeswaranSpatialThreeFormNormSq (vytheeswaranThreeForm B k) +
    massSq / 4 *
      vytheeswaranTemporalThreeFormNormSq (vytheeswaranThreeForm B k)

/-- **Gauge invariance of Eq. (3.23).**  Every occurrence of the tensor potential
factors through either `F=⋆dB` or `G=dB`, so `B ↦ B+dΛ` leaves the full
Hamiltonian density unchanged. -/
lemma vytheeswaranEq323HamiltonianDensity_gauge_invariant
    (massSq : ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) (k Λ : Fin 4 → ℝ)
    (pi : Fin 3 → ℝ) :
    vytheeswaranEq323HamiltonianDensity massSq (B + faraday k Λ) k pi =
      vytheeswaranEq323HamiltonianDensity massSq B k pi := by
  rw [vytheeswaranEq323HamiltonianDensity,
    vytheeswaranEq323HamiltonianDensity,
    vytheeswaranTensorDualVector_gauge_invariant,
    vytheeswaranThreeForm_faradayGauge]

/-- The tensor-momentum correction in Eq. (3.25), in spatial-dual coordinates
`π_{ij}=ε_{ijk}p_k`: `π²/(4m²)+(εAπ)/2 = p²/(2m²)+A·p`. -/
noncomputable def vytheeswaranEq325TensorCorrection
    (massSq : ℝ) (A p : Fin 3 → ℝ) : ℝ :=
  vytheeswaranSpatialVectorNormSq p / (2 * massSq) +
    vytheeswaranSpatialDot A p

/-- Vytheeswaran Eq. (3.25): the Proca density plus its tensor-momentum
gauge-unfixing correction. -/
noncomputable def vytheeswaranEq325HamiltonianDensity
    (procaDensity massSq : ℝ) (A p : Fin 3 → ℝ) : ℝ :=
  procaDensity + vytheeswaranEq325TensorCorrection massSq A p

/-- The unitary gauge `π_{ij}=0`, equivalently `p=0`, reduces Eq. (3.25)
exactly to the original Proca Hamiltonian density. -/
@[simp] lemma vytheeswaranEq325HamiltonianDensity_unitaryGauge
    (procaDensity massSq : ℝ) (A : Fin 3 → ℝ) :
    vytheeswaranEq325HamiltonianDensity procaDensity massSq A 0 =
      procaDensity := by
  simp [vytheeswaranEq325HamiltonianDensity,
    vytheeswaranEq325TensorCorrection,
    vytheeswaranSpatialVectorNormSq, vytheeswaranSpatialDot]

/-- For nonzero mass, the Eq. (3.25) correction is a completed square:
`p²/(2m²)+A·p = |p+m²A|²/(2m²) - m²|A|²/2`.
This is the finite Hamiltonian counterpart of the momentum relation in Eq. (3.24). -/
lemma vytheeswaranEq325TensorCorrection_squareCompletion
    {massSq : ℝ} (hm : massSq ≠ 0) (A p : Fin 3 → ℝ) :
    vytheeswaranEq325TensorCorrection massSq A p =
      vytheeswaranSpatialVectorNormSq (p + massSq • A) / (2 * massSq) -
        massSq / 2 * vytheeswaranSpatialVectorNormSq A := by
  simp only [vytheeswaranEq325TensorCorrection,
    vytheeswaranSpatialVectorNormSq, vytheeswaranSpatialDot,
    Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Vytheeswaran Eq. (3.29) split into Eq. (3.25) plus the secondary
constraint multipliers `-A₀ C + A_{0j}D^j`.  The supplied scalar and vector
constraint values are the evaluations of the constraint observables formalized above. -/
noncomputable def vytheeswaranEq329HamiltonianDensity
    (procaDensity massSq : ℝ) (A p : Fin 3 → ℝ)
    (A0 gauss : ℝ) (A0Tensor tensorConstraint : Fin 3 → ℝ) : ℝ :=
  vytheeswaranEq325HamiltonianDensity procaDensity massSq A p -
    A0 * gauss + vytheeswaranSpatialDot A0Tensor tensorConstraint

/-- **Eq. (3.29) reduces to Eq. (3.25) on the secondary-constraint surface.**
Both Lagrange-multiplier terms vanish when the Gauss and tensor constraints hold. -/
lemma vytheeswaranEq329HamiltonianDensity_onConstraintSurface
    (procaDensity massSq : ℝ) (A p : Fin 3 → ℝ)
    (A0 gauss : ℝ) (A0Tensor tensorConstraint : Fin 3 → ℝ)
    (hgauss : gauss = 0) (htensor : tensorConstraint = 0) :
    vytheeswaranEq329HamiltonianDensity procaDensity massSq A p
        A0 gauss A0Tensor tensorConstraint =
      vytheeswaranEq325HamiltonianDensity procaDensity massSq A p := by
  simp [vytheeswaranEq329HamiltonianDensity,
    vytheeswaranSpatialDot, hgauss, htensor]

/-! ## K.3. Canonical momenta, Legendre transform and Dirac--Bergmann preservation -/

private lemma vytheeswaranAffine_hasDerivAt (a b : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
  have h := (hasDerivAt_const (x := (0 : ℝ)) a).add
    ((hasDerivAt_id (0 : ℝ)).mul_const b)
  have hfun : (fun t : ℝ => a + t * b) =
      (fun _ : ℝ => a) + fun t => t * b := by rfl
  rw [hfun]
  exact h.congr_deriv (by simp)

private lemma vytheeswaranSquare_hasDerivAt (a b : ℝ) :
    HasDerivAt (fun t : ℝ => (a + t * b) ^ 2) (2 * a * b) 0 := by
  have h := (vytheeswaranAffine_hasDerivAt a b).pow 2
  have hfun : (fun t : ℝ => (a + t * b) ^ 2) =
      (fun t : ℝ => a + t * b) ^ 2 := by rfl
  rw [hfun]
  exact h.congr_deriv (by norm_num)

/-- The directional derivative of the spatial norm square.  This reusable
finite-dimensional calculation is the variational engine for the Cauchy momentum
relations below. -/
lemma vytheeswaranSpatialVectorNormSq_hasDerivAt (v d : Fin 3 → ℝ) :
    HasDerivAt
      (fun t : ℝ => vytheeswaranSpatialVectorNormSq (v + t • d))
      (2 * vytheeswaranSpatialDot v d) 0 := by
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => vytheeswaranSquare_hasDerivAt (v i) (d i))
  have hfun : (fun t : ℝ => vytheeswaranSpatialVectorNormSq (v + t • d)) =
      ∑ i : Fin 3, fun t : ℝ => (v i + t * d i) ^ 2 := by
    funext t
    simp only [vytheeswaranSpatialVectorNormSq, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_apply]
  rw [hfun]
  apply hsum.congr_deriv
  simp only [vytheeswaranSpatialDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The velocity-dependent 3+1 block of Eq. (3.27), with the velocity-independent
part recorded as `staticDensity`.  Spatial two-forms use the same three dual
components as §K.1.  The sign in `vB - A` fixes the spatial-dual convention in
which the Eq. (3.25) mixed Hamiltonian term is `+ A·p`. -/
noncomputable def vytheeswaranCauchyLagrangian
    (staticDensity massSq : ℝ) (A vA vB : Fin 3 → ℝ) : ℝ :=
  vytheeswaranSpatialVectorNormSq vA / 2 +
    massSq / 2 * vytheeswaranSpatialVectorNormSq (vB - A) - staticDensity

/-- The vector canonical momentum in the Cauchy split of Eq. (3.28). -/
def vytheeswaranVectorCanonicalMomentum (vA : Fin 3 → ℝ) : Fin 3 → ℝ := vA

/-- The tensor canonical momentum in spatial-dual components, derived below from
the Cauchy Lagrangian. -/
def vytheeswaranTensorCanonicalMomentum
    (massSq : ℝ) (A vB : Fin 3 → ℝ) : Fin 3 → ℝ :=
  massSq • (vB - A)

/-- For nonzero mass the tensor momentum relation is invertible, with velocity
`vB = p/m² + A`. -/
lemma vytheeswaranTensorCanonicalMomentum_inverse
    {massSq : ℝ} (hm : massSq ≠ 0) (A p : Fin 3 → ℝ) :
    vytheeswaranTensorCanonicalMomentum massSq A (massSq⁻¹ • p + A) = p := by
  funext i
  simp only [vytheeswaranTensorCanonicalMomentum, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **Eq. (3.28) is a variational result.**  Along every pair of velocity
directions, the derivative of the Cauchy Lagrangian is the canonical pairing with
the vector and tensor momenta.  Thus these momenta are not merely declared
formulae. -/
lemma vytheeswaranCauchyLagrangian_hasDerivAt
    (staticDensity massSq : ℝ) (A vA vB dA dB : Fin 3 → ℝ) :
    HasDerivAt
      (fun t : ℝ => vytheeswaranCauchyLagrangian staticDensity massSq A
        (vA + t • dA) (vB + t • dB))
      (vytheeswaranSpatialDot (vytheeswaranVectorCanonicalMomentum vA) dA +
        vytheeswaranSpatialDot
          (vytheeswaranTensorCanonicalMomentum massSq A vB) dB) 0 := by
  have hA := (vytheeswaranSpatialVectorNormSq_hasDerivAt vA dA).div_const (2 : ℝ)
  have hB :=
    (vytheeswaranSpatialVectorNormSq_hasDerivAt (vB - A) dB).const_mul (massSq / 2)
  have hC := hA.add hB |>.sub (hasDerivAt_const (x := (0 : ℝ)) staticDensity)
  have hfun : (fun t : ℝ => vytheeswaranCauchyLagrangian staticDensity massSq A
      (vA + t • dA) (vB + t • dB)) =
      (fun t => vytheeswaranSpatialVectorNormSq (vA + t • dA) / 2) +
        (fun t => massSq / 2 *
          vytheeswaranSpatialVectorNormSq ((vB - A) + t • dB)) -
        (fun _ => staticDensity) := by
    funext t
    simp only [vytheeswaranCauchyLagrangian, vytheeswaranSpatialVectorNormSq,
      Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  apply hC.congr_deriv
  simp only [vytheeswaranVectorCanonicalMomentum,
    vytheeswaranTensorCanonicalMomentum, vytheeswaranSpatialDot,
    Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Legendre transform of the Cauchy Lagrangian after solving both regular
velocity equations. -/
noncomputable def vytheeswaranLegendreDensity
    (staticDensity massSq : ℝ) (A pi p : Fin 3 → ℝ) : ℝ :=
  vytheeswaranSpatialDot pi pi +
    vytheeswaranSpatialDot p (massSq⁻¹ • p + A) -
      vytheeswaranCauchyLagrangian staticDensity massSq A pi
        (massSq⁻¹ • p + A)

/-- **The Legendre transform yields Eq. (3.25).**  At nonzero mass, the actual
velocity Legendre transform is exactly the already formalized gauge-unfixed
Hamiltonian density, with the vector kinetic term included in the Proca density. -/
lemma vytheeswaranLegendreDensity_eq_Eq325
    {massSq : ℝ} (hm : massSq ≠ 0) (staticDensity : ℝ)
    (A pi p : Fin 3 → ℝ) :
    vytheeswaranLegendreDensity staticDensity massSq A pi p =
      vytheeswaranEq325HamiltonianDensity
        (staticDensity + vytheeswaranSpatialVectorNormSq pi / 2)
        massSq A p := by
  simp only [vytheeswaranLegendreDensity, vytheeswaranCauchyLagrangian,
    vytheeswaranEq325HamiltonianDensity, vytheeswaranEq325TensorCorrection,
    vytheeswaranSpatialVectorNormSq, vytheeswaranSpatialDot,
    Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The Gauss secondary-constraint value of Eq. (3.30) on canonical Fourier data. -/
def vytheeswaranSecondaryGaussValue
    (massSq : ℝ) (k pi b : Fin 3 → ℝ) : ℝ :=
  -vytheeswaranSpatialDot k pi + massSq * vytheeswaranSpatialDot k b

/-- The three tensor secondary-constraint values `∂ᵢπⁱʲ` of Eq. (3.30). -/
def vytheeswaranSecondaryTensorValue
    (k p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => ∑ l, (∑ i,
    ((leviCivita4 0 i.succ j.succ l.succ : ℤ) : ℝ) * k i) * p l

/-- Hamilton's equation for the primary vector momentum, `π̇⁰ = C`. -/
def vytheeswaranPrimaryVectorMomentumRate (gauss : ℝ) : ℝ := gauss

/-- Hamilton's equation for the three primary tensor momenta, `π̇⁰ʲ = -Dʲ`. -/
def vytheeswaranPrimaryTensorMomentumRate
    (tensor : Fin 3 → ℝ) : Fin 3 → ℝ := -tensor

/-- **Dirac--Bergmann multiplier derivative.**  Varying the scalar and tensor
multipliers in Eq. (3.29) differentiates the Hamiltonian to the negative canonical
pairing with the four primary-momentum rates. -/
lemma vytheeswaranMultiplierHamiltonian_hasDerivAt
    (procaDensity massSq : ℝ) (A p : Fin 3 → ℝ)
    (A0 d0 : ℝ) (A0Tensor d : Fin 3 → ℝ)
    (gauss : ℝ) (tensor : Fin 3 → ℝ) :
    HasDerivAt
      (fun t : ℝ => vytheeswaranEq329HamiltonianDensity procaDensity massSq A p
        (A0 + t * d0) gauss (A0Tensor + t • d) tensor)
      (-(d0 * vytheeswaranPrimaryVectorMomentumRate gauss +
        vytheeswaranSpatialDot d
          (vytheeswaranPrimaryTensorMomentumRate tensor))) 0 := by
  simp only [vytheeswaranPrimaryVectorMomentumRate,
    vytheeswaranPrimaryTensorMomentumRate, vytheeswaranSpatialDot,
    Fin.sum_univ_three, Pi.neg_apply]
  have hA0 := vytheeswaranAffine_hasDerivAt A0 d0
  have ht (i : Fin 3) := vytheeswaranAffine_hasDerivAt (A0Tensor i) (d i)
  have h := ((hasDerivAt_const (x := (0 : ℝ))
      (vytheeswaranEq325HamiltonianDensity procaDensity massSq A p)).sub
        (hA0.mul_const gauss)).add
      ((((ht 0).mul_const (tensor 0)).add ((ht 1).mul_const (tensor 1))).add
        ((ht 2).mul_const (tensor 2)))
  have hfun : (fun t : ℝ =>
      vytheeswaranEq325HamiltonianDensity procaDensity massSq A p -
        (A0 + t * d0) * gauss +
        ((A0Tensor 0 + t * d 0) * tensor 0 +
         (A0Tensor 1 + t * d 1) * tensor 1 +
         (A0Tensor 2 + t * d 2) * tensor 2)) =
      ((fun _ : ℝ => vytheeswaranEq325HamiltonianDensity procaDensity massSq A p) -
        (fun t => (A0 + t * d0) * gauss)) +
        (((fun t => (A0Tensor 0 + t * d 0) * tensor 0) +
          (fun t => (A0Tensor 1 + t * d 1) * tensor 1)) +
          (fun t => (A0Tensor 2 + t * d 2) * tensor 2)) := by rfl
  simp only [vytheeswaranEq329HamiltonianDensity,
    vytheeswaranSpatialDot, Fin.sum_univ_three,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact h.congr_deriv (by ring)

/-- **Preservation of all four primary constraints is equivalent to the four
secondary constraints.**  The values are computed from canonical Fourier data,
not supplied as an abstract certificate. -/
lemma vytheeswaranPrimaryPreservation_iff_secondaryConstraints
    (massSq : ℝ) (k pi b p : Fin 3 → ℝ) :
    vytheeswaranPrimaryVectorMomentumRate
        (vytheeswaranSecondaryGaussValue massSq k pi b) = 0 ∧
      vytheeswaranPrimaryTensorMomentumRate
        (vytheeswaranSecondaryTensorValue k p) = 0 ↔
    vytheeswaranSecondaryGaussValue massSq k pi b = 0 ∧
      vytheeswaranSecondaryTensorValue k p = 0 := by
  simp only [vytheeswaranPrimaryVectorMomentumRate,
    vytheeswaranPrimaryTensorMomentumRate]
  constructor
  · rintro ⟨hg, ht⟩
    exact ⟨hg, neg_eq_zero.mp ht⟩
  · rintro ⟨hg, ht⟩
    exact ⟨hg, by rw [ht, neg_zero]⟩

/-! ## K.4. Exact `3+1` decomposition of the Lorentzian action -/

set_option maxHeartbeats 2000000 in
/-- The Maxwell part of a Lorentzian antisymmetric two-form splits into its
electric Cauchy energy and its purely spatial part. -/
lemma vytheeswaranMinkowskiTwoFormContraction_threePlusOne
    (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ μ ν, F μ ν = -F ν μ) :
    -(1 / 4 : ℝ) * vytheeswaranMinkowskiTwoFormContraction F =
      vytheeswaranSpatialVectorNormSq (fun i => F 0 i.succ) / 2 -
        vytheeswaranSpatialTwoFormNormSq F / 4 := by
  simp [vytheeswaranMinkowskiTwoFormContraction,
    vytheeswaranSpatialVectorNormSq, vytheeswaranSpatialTwoFormNormSq,
    Fin.sum_univ_four, Fin.sum_univ_three, minkowskiSign4]
  have h00 : F 0 0 = 0 := by linarith [hF 0 0]
  rw [h00, hF 1 0, hF 2 0, hF 3 0]
  ring

/-- If the tensor potential is antisymmetric, its three-form field strength is
antisymmetric in its first two indices. -/
lemma vytheeswaranThreeForm_antisymm_first
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : ∀ μ ν, B μ ν = -B ν μ)
    (k : Fin 4 → ℝ) (μ ν ρ : Fin 4) :
    vytheeswaranThreeForm B k ν μ ρ = -vytheeswaranThreeForm B k μ ν ρ := by
  simp only [vytheeswaranThreeForm]
  rw [hB μ ρ, hB ρ ν, hB ν μ]
  ring

/-- If the tensor potential is antisymmetric, its three-form field strength is
antisymmetric in its last two indices. -/
lemma vytheeswaranThreeForm_antisymm_last
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : ∀ μ ν, B μ ν = -B ν μ)
    (k : Fin 4 → ℝ) (μ ν ρ : Fin 4) :
    vytheeswaranThreeForm B k μ ρ ν = -vytheeswaranThreeForm B k μ ν ρ := by
  simp only [vytheeswaranThreeForm]
  rw [hB ρ ν, hB ν μ, hB μ ρ]
  ring

/-- Temporal three-form norm with the temporal index in the middle slot. -/
private def vytheeswaranMiddleTemporalThreeFormNormSq
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, G i.succ 0 j.succ ^ 2

/-- Temporal three-form norm with the temporal index in the last slot. -/
private def vytheeswaranLastTemporalThreeFormNormSq
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, G i.succ j.succ 0 ^ 2

/-- The full Lorentz contraction is the sum of its three temporal placements
minus its purely spatial block when the three-form is alternating. -/
private lemma vytheeswaranMinkowskiThreeFormContraction_partition
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h12 : ∀ μ ν ρ, G ν μ ρ = -G μ ν ρ)
    (h23 : ∀ μ ν ρ, G μ ρ ν = -G μ ν ρ) :
    vytheeswaranMinkowskiThreeFormContraction G =
      vytheeswaranTemporalThreeFormNormSq G +
        vytheeswaranMiddleTemporalThreeFormNormSq G +
        vytheeswaranLastTemporalThreeFormNormSq G -
        vytheeswaranSpatialThreeFormNormSq G := by
  have hr12 (μ ρ : Fin 4) : G μ μ ρ = 0 := by linarith [h12 μ μ ρ]
  have hr23 (μ ν : Fin 4) : G μ ν ν = 0 := by linarith [h23 μ ν ν]
  have hr13 (μ ν : Fin 4) : G μ ν μ = 0 := by
    rw [h23 μ μ ν, hr12]
    simp
  simp [vytheeswaranMinkowskiThreeFormContraction,
    vytheeswaranTemporalThreeFormNormSq,
    vytheeswaranMiddleTemporalThreeFormNormSq,
    vytheeswaranLastTemporalThreeFormNormSq,
    vytheeswaranSpatialThreeFormNormSq, Fin.sum_univ_four,
    Fin.sum_univ_three, minkowskiSign4]
  simp_rw [hr12, hr23, hr13]
  ring

/-- Antisymmetry makes the middle temporal norm equal to the leading temporal
norm. -/
private lemma vytheeswaranMiddleTemporalThreeFormNormSq_eq
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h12 : ∀ μ ν ρ, G ν μ ρ = -G μ ν ρ) :
    vytheeswaranMiddleTemporalThreeFormNormSq G =
      vytheeswaranTemporalThreeFormNormSq G := by
  change (∑ i : Fin 3, ∑ j : Fin 3, G i.succ 0 j.succ ^ 2) =
    ∑ i : Fin 3, ∑ j : Fin 3, G 0 i.succ j.succ ^ 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h12 0 i.succ j.succ]
  ring

/-- Antisymmetry makes the last temporal norm equal to the leading temporal
norm. -/
private lemma vytheeswaranLastTemporalThreeFormNormSq_eq
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h12 : ∀ μ ν ρ, G ν μ ρ = -G μ ν ρ)
    (h23 : ∀ μ ν ρ, G μ ρ ν = -G μ ν ρ) :
    vytheeswaranLastTemporalThreeFormNormSq G =
      vytheeswaranTemporalThreeFormNormSq G := by
  change (∑ i : Fin 3, ∑ j : Fin 3, G i.succ j.succ 0 ^ 2) =
    ∑ i : Fin 3, ∑ j : Fin 3, G 0 i.succ j.succ ^ 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h23 i.succ 0 j.succ, h12 0 i.succ j.succ]
  ring

set_option maxHeartbeats 4000000 in
/-- The Lorentzian three-form contraction has three placements of the temporal
index and one purely spatial block. -/
lemma vytheeswaranMinkowskiThreeFormContraction_threePlusOne
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h12 : ∀ μ ν ρ, G ν μ ρ = -G μ ν ρ)
    (h23 : ∀ μ ν ρ, G μ ρ ν = -G μ ν ρ) :
    vytheeswaranMinkowskiThreeFormContraction G =
      3 * vytheeswaranTemporalThreeFormNormSq G -
        vytheeswaranSpatialThreeFormNormSq G := by
  rw [vytheeswaranMinkowskiThreeFormContraction_partition G h12 h23,
    vytheeswaranMiddleTemporalThreeFormNormSq_eq G h12,
    vytheeswaranLastTemporalThreeFormNormSq_eq G h12 h23]
  ring

/-- The three independent spatial-dual components of the temporal part
`G₀ᵢⱼ` of a three-form. -/
def vytheeswaranTemporalThreeFormDual
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![G 0 2 3, -G 0 1 3, G 0 1 2]

set_option maxHeartbeats 2000000 in
/-- The temporal three-form norm counts each independent spatial-dual component
twice. -/
lemma vytheeswaranTemporalThreeFormNormSq_eq_dual
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h23 : ∀ μ ν ρ, G μ ρ ν = -G μ ν ρ) :
    vytheeswaranTemporalThreeFormNormSq G =
      2 * vytheeswaranSpatialVectorNormSq (vytheeswaranTemporalThreeFormDual G) := by
  simp [vytheeswaranTemporalThreeFormNormSq,
    vytheeswaranSpatialVectorNormSq, vytheeswaranTemporalThreeFormDual,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  have h11 : G 0 1 1 = 0 := by linarith [h23 0 1 1]
  have h22 : G 0 2 2 = 0 := by linarith [h23 0 2 2]
  have h33 : G 0 3 3 = 0 := by linarith [h23 0 3 3]
  rw [h11, h22, h33, h23 0 1 2, h23 0 1 3, h23 0 2 3]
  ring

set_option maxHeartbeats 2000000 in
/-- With the module's lower-index Levi--Civita orientation, the temporal
three-form dual is the negative of the spatial part of the paper's dual vector
`Fμ = ⋆dB`. The sign disappears from its quadratic norm. -/
lemma vytheeswaranTemporalThreeFormDual_eq_neg_tensorDualVector
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : ∀ μ ν, B μ ν = -B ν μ)
    (k : Fin 4 → ℝ) :
    vytheeswaranTemporalThreeFormDual (vytheeswaranThreeForm B k) =
      fun i => -vytheeswaranTensorDualVector B k i.succ := by
  funext i
  fin_cases i
  · change vytheeswaranThreeForm B k 0 2 3 =
      -vytheeswaranTensorDualVector B k 1
    simp only [vytheeswaranThreeForm, vytheeswaranTensorDualVector, maxwellOp,
      Fin.sum_univ_four]
    rw [hodgeStar2_apply_10 B hB, hodgeStar2_diag B 1,
      hodgeStar2_apply_12 B hB, hodgeStar2_apply_13 B hB, hB 3 0]
    ring
  · change -vytheeswaranThreeForm B k 0 1 3 =
      -vytheeswaranTensorDualVector B k 2
    simp only [vytheeswaranThreeForm, vytheeswaranTensorDualVector, maxwellOp,
      Fin.sum_univ_four]
    rw [hodgeStar2_apply_20 B hB, hodgeStar2_apply_21 B hB,
      hodgeStar2_diag B 2, hodgeStar2_apply_23 B hB, hB 3 0]
    ring
  · change vytheeswaranThreeForm B k 0 1 2 =
      -vytheeswaranTensorDualVector B k 3
    simp only [vytheeswaranThreeForm, vytheeswaranTensorDualVector, maxwellOp,
      Fin.sum_univ_four]
    rw [hodgeStar2_apply_30 B hB, hodgeStar2_apply_31 B hB,
      hodgeStar2_apply_32 B hB, hodgeStar2_diag B 3, hB 2 0]
    ring

/-- Spatial part of a four-vector in the fixed Cauchy chart. -/
def vytheeswaranSpatialVector (A : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i => A i.succ

/-- The velocity-independent density needed by the exact `3+1` split of
Eq. (3.27). It contains the spatial Maxwell and three-form blocks, the temporal
topological coupling and the square-completion term. -/
noncomputable def vytheeswaranCauchyStaticDensity
    (massSq : ℝ) (A k : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  vytheeswaranSpatialTwoFormNormSq (faraday k A) / 4 +
    massSq * A 0 * vytheeswaranTensorDualVector B k 0 +
    massSq / 12 * vytheeswaranSpatialThreeFormNormSq
      (vytheeswaranThreeForm B k) +
    massSq / 2 * vytheeswaranSpatialVectorNormSq (vytheeswaranSpatialVector A)

/-- **Exact `3+1` split of Vytheeswaran Eq. (3.27).** The full Lorentzian
Maxwell--tensor density is the Cauchy Lagrangian used in §K.3. The proof fixes
the relative signs and the factors `1/2`, `1/4`, and `1/12`. -/
lemma vytheeswaranMaxwellTensorLagrangian_threePlusOne
    (massSq : ℝ) (A k : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ μ ν, B μ ν = -B ν μ) :
    vytheeswaranMaxwellTensorLagrangian massSq A k B =
      vytheeswaranCauchyLagrangian
        (vytheeswaranCauchyStaticDensity massSq A k B) massSq
        (vytheeswaranSpatialVector A) (fun i => faraday k A 0 i.succ)
        (fun i => vytheeswaranTensorDualVector B k i.succ) := by
  rw [vytheeswaranMaxwellTensorLagrangian]
  rw [vytheeswaranMinkowskiTwoFormContraction_threePlusOne (faraday k A)
    (fun μ ν => by simp only [faraday, Matrix.of_apply]; ring)]
  rw [vytheeswaranMinkowskiThreeFormContraction_threePlusOne
    (vytheeswaranThreeForm B k)
    (vytheeswaranThreeForm_antisymm_first B hB k)
    (vytheeswaranThreeForm_antisymm_last B hB k)]
  rw [vytheeswaranTemporalThreeFormNormSq_eq_dual
    (vytheeswaranThreeForm B k) (vytheeswaranThreeForm_antisymm_last B hB k)]
  rw [vytheeswaranTemporalThreeFormDual_eq_neg_tensorDualVector B hB k]
  simp [vytheeswaranCauchyLagrangian, vytheeswaranCauchyStaticDensity,
    vytheeswaranSpatialVector, vytheeswaranSpatialDot, Fin.sum_univ_four,
    vytheeswaranSpatialVectorNormSq, Fin.sum_univ_three, Pi.sub_apply]
  ring

/-! ## K.5. Continuum antisymmetric-tensor dual on spacetime distributions -/

open Distribution SchwartzMap

/-- Scalar distributions on four-dimensional Minkowski spacetime. -/
abbrev VytheeswaranScalarDistribution := (SpaceTime 3) →d[ℝ] ℝ

/-- A rank-two spacetime field whose components are scalar distributions. -/
abbrev VytheeswaranTensorDistribution :=
  Fin 4 → Fin 4 → VytheeswaranScalarDistribution

/-- A spacetime one-form whose components are scalar distributions. -/
abbrev VytheeswaranOneFormDistribution := Fin 4 → VytheeswaranScalarDistribution

/-- Antisymmetry predicate for a distribution-valued rank-two tensor. -/
def IsVytheeswaranAntisymmetricTensorDistribution
    (B : VytheeswaranTensorDistribution) : Prop :=
  ∀ a b, B b a = -B a b

/-- **Continuum form of Eq. (3.22).** This is
`Fμ = ½ εμναβ ∂ν Bαβ` as a genuine spacetime distribution. The canonical
equivalence `Fin 1 ⊕ Fin 3 ≃ Fin 4` only transports coordinate indices. -/
noncomputable def vytheeswaranContinuumTensorDualVector
    (B : VytheeswaranTensorDistribution) (μ : Fin 4) :
    VytheeswaranScalarDistribution :=
  (1 / 2 : ℝ) • ∑ ν, ∑ a, ∑ b,
    (((leviCivita4 μ ν a b : ℤ) : ℝ) •
      SpaceTime.distDeriv (finSumFinEquiv.symm ν) (B a b))

/-- The continuum two-form gauge shift `dΛ`, formed with distributional
spacetime derivatives. -/
noncomputable def vytheeswaranContinuumTensorGaugeShift
    (Λ : VytheeswaranOneFormDistribution) : VytheeswaranTensorDistribution :=
  fun a b =>
    SpaceTime.distDeriv (finSumFinEquiv.symm a) (Λ b) -
      SpaceTime.distDeriv (finSumFinEquiv.symm b) (Λ a)

/-- Every continuum gauge shift `dΛ` is an antisymmetric tensor distribution. -/
lemma vytheeswaranContinuumTensorGaugeShift_antisymmetric
    (Λ : VytheeswaranOneFormDistribution) :
    IsVytheeswaranAntisymmetricTensorDistribution
      (vytheeswaranContinuumTensorGaugeShift Λ) := by
  intro a b
  simp only [vytheeswaranContinuumTensorGaugeShift]
  abel

/-- A continuum two-form gauge transformation preserves antisymmetry of the
tensor potential. -/
lemma vytheeswaranContinuumTensorGaugeShift_preserves_antisymmetry
    (B : VytheeswaranTensorDistribution)
    (hB : IsVytheeswaranAntisymmetricTensorDistribution B)
    (Λ : VytheeswaranOneFormDistribution) :
    IsVytheeswaranAntisymmetricTensorDistribution
  (fun a b => B a b + vytheeswaranContinuumTensorGaugeShift Λ a b) := by
  intro a b
  change B b a + vytheeswaranContinuumTensorGaugeShift Λ b a =
    -(B a b + vytheeswaranContinuumTensorGaugeShift Λ a b)
  rw [hB a b, vytheeswaranContinuumTensorGaugeShift_antisymmetric Λ a b]
  abel

/-- Time component of the continuum tensor dual, reduced to the three
independent spatial components of an antisymmetric tensor distribution. -/
lemma vytheeswaranContinuumTensorDualVector_apply_zero
    (B : VytheeswaranTensorDistribution)
    (hB : IsVytheeswaranAntisymmetricTensorDistribution B) :
    vytheeswaranContinuumTensorDualVector B 0 =
      SpaceTime.distDeriv (finSumFinEquiv.symm 1) (B 2 3) -
        SpaceTime.distDeriv (finSumFinEquiv.symm 2) (B 1 3) +
        SpaceTime.distDeriv (finSumFinEquiv.symm 3) (B 1 2) := by
  ext φ
  simp [vytheeswaranContinuumTensorDualVector, Fin.sum_univ_four, leviCivita4]
  rw [hB 2 3, hB 1 3, hB 1 2]
  simp
  ring

/-- First spatial component of the continuum tensor dual, reduced to
independent components of an antisymmetric tensor distribution. -/
lemma vytheeswaranContinuumTensorDualVector_apply_one
    (B : VytheeswaranTensorDistribution)
    (hB : IsVytheeswaranAntisymmetricTensorDistribution B) :
    vytheeswaranContinuumTensorDualVector B 1 =
      -SpaceTime.distDeriv (finSumFinEquiv.symm 0) (B 2 3) +
        SpaceTime.distDeriv (finSumFinEquiv.symm 2) (B 0 3) -
        SpaceTime.distDeriv (finSumFinEquiv.symm 3) (B 0 2) := by
  ext φ
  simp [vytheeswaranContinuumTensorDualVector, Fin.sum_univ_four, leviCivita4]
  rw [hB 2 3, hB 0 3, hB 0 2]
  simp
  ring

/-- Second spatial component of the continuum tensor dual, reduced to
independent components of an antisymmetric tensor distribution. -/
lemma vytheeswaranContinuumTensorDualVector_apply_two
    (B : VytheeswaranTensorDistribution)
    (hB : IsVytheeswaranAntisymmetricTensorDistribution B) :
    vytheeswaranContinuumTensorDualVector B 2 =
      SpaceTime.distDeriv (finSumFinEquiv.symm 0) (B 1 3) -
        SpaceTime.distDeriv (finSumFinEquiv.symm 1) (B 0 3) +
        SpaceTime.distDeriv (finSumFinEquiv.symm 3) (B 0 1) := by
  ext φ
  simp [vytheeswaranContinuumTensorDualVector, Fin.sum_univ_four, leviCivita4]
  rw [hB 1 3, hB 0 3, hB 0 1]
  simp
  ring

/-- Third spatial component of the continuum tensor dual, reduced to
independent components of an antisymmetric tensor distribution. -/
lemma vytheeswaranContinuumTensorDualVector_apply_three
    (B : VytheeswaranTensorDistribution)
    (hB : IsVytheeswaranAntisymmetricTensorDistribution B) :
    vytheeswaranContinuumTensorDualVector B 3 =
      -SpaceTime.distDeriv (finSumFinEquiv.symm 0) (B 1 2) +
        SpaceTime.distDeriv (finSumFinEquiv.symm 1) (B 0 2) -
        SpaceTime.distDeriv (finSumFinEquiv.symm 2) (B 0 1) := by
  ext φ
  simp [vytheeswaranContinuumTensorDualVector, Fin.sum_univ_four, leviCivita4]
  rw [hB 1 2, hB 0 2, hB 0 1]
  simp
  ring

set_option maxHeartbeats 2000000 in
/-- The distributional dual of an exact two-form vanishes. This is the
continuum `d² = 0` result and uses the existing commutation theorem for
distributional spacetime derivatives. -/
lemma vytheeswaranContinuumTensorDualVector_gauge_eq_zero
    (Λ : VytheeswaranOneFormDistribution) (μ : Fin 4) :
    vytheeswaranContinuumTensorDualVector
      (vytheeswaranContinuumTensorGaugeShift Λ) μ = 0 := by
  fin_cases μ
  · change vytheeswaranContinuumTensorDualVector
      (vytheeswaranContinuumTensorGaugeShift Λ) 0 = 0
    rw [vytheeswaranContinuumTensorDualVector_apply_zero _
      (vytheeswaranContinuumTensorGaugeShift_antisymmetric Λ)]
    simp only [vytheeswaranContinuumTensorGaugeShift, map_sub]
    rw [SpaceTime.distDeriv_commute (finSumFinEquiv.symm 1) (finSumFinEquiv.symm 2),
      SpaceTime.distDeriv_commute (finSumFinEquiv.symm 1) (finSumFinEquiv.symm 3),
      SpaceTime.distDeriv_commute (finSumFinEquiv.symm 2) (finSumFinEquiv.symm 3)]
    abel
  · change vytheeswaranContinuumTensorDualVector
      (vytheeswaranContinuumTensorGaugeShift Λ) 1 = 0
    rw [vytheeswaranContinuumTensorDualVector_apply_one _
      (vytheeswaranContinuumTensorGaugeShift_antisymmetric Λ)]
    simp only [vytheeswaranContinuumTensorGaugeShift, map_sub]
    rw [SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 2),
      SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 3),
      SpaceTime.distDeriv_commute (finSumFinEquiv.symm 2) (finSumFinEquiv.symm 3)]
    abel
  · change vytheeswaranContinuumTensorDualVector
      (vytheeswaranContinuumTensorGaugeShift Λ) 2 = 0
    rw [vytheeswaranContinuumTensorDualVector_apply_two _
      (vytheeswaranContinuumTensorGaugeShift_antisymmetric Λ)]
    simp only [vytheeswaranContinuumTensorGaugeShift, map_sub]
    rw [SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 1),
      SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 3),
      SpaceTime.distDeriv_commute (finSumFinEquiv.symm 1) (finSumFinEquiv.symm 3)]
    abel
  · change vytheeswaranContinuumTensorDualVector
      (vytheeswaranContinuumTensorGaugeShift Λ) 3 = 0
    rw [vytheeswaranContinuumTensorDualVector_apply_three _
      (vytheeswaranContinuumTensorGaugeShift_antisymmetric Λ)]
    simp only [vytheeswaranContinuumTensorGaugeShift, map_sub]
    rw [SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 1),
      SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 2),
      SpaceTime.distDeriv_commute (finSumFinEquiv.symm 1) (finSumFinEquiv.symm 2)]
    abel

/-- The continuum tensor-dual construction is additive. -/
lemma vytheeswaranContinuumTensorDualVector_add
    (B C : VytheeswaranTensorDistribution) (μ : Fin 4) :
    vytheeswaranContinuumTensorDualVector (fun a b => B a b + C a b) μ =
      vytheeswaranContinuumTensorDualVector B μ +
        vytheeswaranContinuumTensorDualVector C μ := by
  ext φ
  simp [vytheeswaranContinuumTensorDualVector, Finset.smul_sum,
    Finset.sum_add_distrib]

/-- **Continuum tensor gauge invariance.** Eq. (3.22) is invariant under
`B ↦ B + dΛ` for arbitrary distribution-valued fields. -/
lemma vytheeswaranContinuumTensorDualVector_gauge_invariant
    (B : VytheeswaranTensorDistribution) (Λ : VytheeswaranOneFormDistribution)
    (μ : Fin 4) :
    vytheeswaranContinuumTensorDualVector
        (fun a b => B a b + vytheeswaranContinuumTensorGaugeShift Λ a b) μ =
      vytheeswaranContinuumTensorDualVector B μ := by
  rw [vytheeswaranContinuumTensorDualVector_add]
  simp [vytheeswaranContinuumTensorDualVector_gauge_eq_zero]

/-- Distributional divergence of a spacetime one-form. -/
noncomputable def vytheeswaranContinuumDivergence
    (F : VytheeswaranOneFormDistribution) : VytheeswaranScalarDistribution :=
  ∑ μ, SpaceTime.distDeriv (finSumFinEquiv.symm μ) (F μ)

/-- **Continuum transversality of Eq. (3.22).** The dual vector has identically
zero distributional divergence for every antisymmetric tensor distribution,
with no differentiability premise. -/
lemma vytheeswaranContinuumTensorDualVector_conserved
    (B : VytheeswaranTensorDistribution)
    (hB : IsVytheeswaranAntisymmetricTensorDistribution B) :
    vytheeswaranContinuumDivergence
      (vytheeswaranContinuumTensorDualVector B) = 0 := by
  rw [vytheeswaranContinuumDivergence, Fin.sum_univ_four,
    vytheeswaranContinuumTensorDualVector_apply_zero B hB,
    vytheeswaranContinuumTensorDualVector_apply_one B hB,
    vytheeswaranContinuumTensorDualVector_apply_two B hB,
    vytheeswaranContinuumTensorDualVector_apply_three B hB]
  simp only [map_add, map_sub, map_neg]
  rw [SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 1),
    SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 2),
    SpaceTime.distDeriv_commute (finSumFinEquiv.symm 0) (finSumFinEquiv.symm 3),
    SpaceTime.distDeriv_commute (finSumFinEquiv.symm 1) (finSumFinEquiv.symm 2),
    SpaceTime.distDeriv_commute (finSumFinEquiv.symm 1) (finSumFinEquiv.symm 3),
    SpaceTime.distDeriv_commute (finSumFinEquiv.symm 2) (finSumFinEquiv.symm 3)]
  abel

/-! ## K.6. Integrated `L²` Fourier-Cauchy action and constraint domain -/

open MeasureTheory

/-- An admissible `L²` Fourier-Cauchy datum for the Maxwell--tensor action.
Every spatial component is square-integrable and the static density is integrable.
The momentum-space carrier is the Plancherel representation of a spatial Cauchy
slice; stronger Sobolev regularity can be imposed as a subtype of this carrier. -/
structure VytheeswaranL2CauchyDatum where
  A : Space 3 → Fin 3 → ℝ
  vA : Space 3 → Fin 3 → ℝ
  vB : Space 3 → Fin 3 → ℝ
  tensorPotential : Space 3 → Fin 3 → ℝ
  staticDensity : Space 3 → ℝ
  A_memLp : ∀ i, MemLp (fun q => A q i) 2 volume
  vA_memLp : ∀ i, MemLp (fun q => vA q i) 2 volume
  vB_memLp : ∀ i, MemLp (fun q => vB q i) 2 volume
  tensorPotential_memLp : ∀ i, MemLp (fun q => tensorPotential q i) 2 volume
  static_integrable : Integrable staticDensity volume

/-- A componentwise `L²` spatial vector has an integrable quadratic density. -/
lemma vytheeswaranSpatialVectorNormSq_integrable
    (f : Space 3 → Fin 3 → ℝ)
    (hf : ∀ i, MemLp (fun q => f q i) 2 volume) :
    Integrable (fun q => vytheeswaranSpatialVectorNormSq (f q)) volume := by
  simp only [vytheeswaranSpatialVectorNormSq]
  exact integrable_finset_sum Finset.univ (fun i _ => (hf i).integrable_sq)

/-- The Cauchy Lagrangian density of every admissible datum is integrable. -/
lemma VytheeswaranL2CauchyDatum.cauchyDensity_integrable
    (D : VytheeswaranL2CauchyDatum) (massSq : ℝ) :
    Integrable (fun q => vytheeswaranCauchyLagrangian
      (D.staticDensity q) massSq (D.A q) (D.vA q) (D.vB q)) volume := by
  have hvA := vytheeswaranSpatialVectorNormSq_integrable D.vA D.vA_memLp
  have hvBA : ∀ i, MemLp (fun q => (D.vB q - D.A q) i) 2 volume := by
    intro i
    exact (D.vB_memLp i).sub (D.A_memLp i)
  have hvB := vytheeswaranSpatialVectorNormSq_integrable
    (fun q => D.vB q - D.A q) hvBA
  simp only [vytheeswaranCauchyLagrangian]
  exact (hvA.div_const 2).add (hvB.const_mul (massSq / 2)) |>.sub
    D.static_integrable

/-- The spatially integrated Fourier-Cauchy action of Eq. (3.27). -/
noncomputable def vytheeswaranFourierCauchyAction
    (massSq : ℝ) (D : VytheeswaranL2CauchyDatum) : ℝ :=
  ∫ q, vytheeswaranCauchyLagrangian (D.staticDensity q) massSq
    (D.A q) (D.vA q) (D.vB q) ∂volume

/-- The almost-everywhere secondary-constraint surface in the continuum
Fourier-Cauchy carrier. Frequencies are the coordinates of `q : Space 3`; the
momenta are the actual Legendre momenta derived in §K.3. -/
def VytheeswaranL2CauchyDatum.IsOnConstraintSurface
    (D : VytheeswaranL2CauchyDatum) (massSq : ℝ) : Prop :=
  ∀ᵐ q : Space 3 ∂volume,
    vytheeswaranSecondaryGaussValue massSq (fun i => q i)
        (vytheeswaranVectorCanonicalMomentum (D.vA q))
        (D.tensorPotential q) = 0 ∧
      vytheeswaranSecondaryTensorValue (fun i => q i)
        (vytheeswaranTensorCanonicalMomentum massSq (D.A q) (D.vB q)) = 0

/-- On the continuum `L²` domain, the secondary constraints hold almost
everywhere exactly when all four primary momenta are preserved almost everywhere. -/
lemma VytheeswaranL2CauchyDatum.onConstraintSurface_iff_primaryPreserved
    (D : VytheeswaranL2CauchyDatum) (massSq : ℝ) :
    D.IsOnConstraintSurface massSq ↔
      ∀ᵐ q : Space 3 ∂volume,
        vytheeswaranPrimaryVectorMomentumRate
            (vytheeswaranSecondaryGaussValue massSq (fun i => q i)
              (vytheeswaranVectorCanonicalMomentum (D.vA q))
              (D.tensorPotential q)) = 0 ∧
          vytheeswaranPrimaryTensorMomentumRate
            (vytheeswaranSecondaryTensorValue (fun i => q i)
              (vytheeswaranTensorCanonicalMomentum massSq (D.A q) (D.vB q))) = 0 := by
  constructor
  · intro h
    filter_upwards [h] with q hq
    exact (vytheeswaranPrimaryPreservation_iff_secondaryConstraints massSq
      (fun i => q i) (vytheeswaranVectorCanonicalMomentum (D.vA q))
      (D.tensorPotential q)
      (vytheeswaranTensorCanonicalMomentum massSq (D.A q) (D.vB q))).mpr hq
  · intro h
    filter_upwards [h] with q hq
    exact (vytheeswaranPrimaryPreservation_iff_secondaryConstraints massSq
      (fun i => q i) (vytheeswaranVectorCanonicalMomentum (D.vA q))
      (D.tensorPotential q)
      (vytheeswaranTensorCanonicalMomentum massSq (D.A q) (D.vB q))).mp hq

/-- The integrated Legendre transform of the admissible Cauchy datum. -/
noncomputable def vytheeswaranFourierLegendreAction
    (massSq : ℝ) (D : VytheeswaranL2CauchyDatum) : ℝ :=
  ∫ q, vytheeswaranLegendreDensity (D.staticDensity q) massSq (D.A q)
    (vytheeswaranVectorCanonicalMomentum (D.vA q))
    (vytheeswaranTensorCanonicalMomentum massSq (D.A q) (D.vB q)) ∂volume

/-- **Integrated Legendre transform.** For nonzero mass, the continuum
Fourier-Cauchy Legendre action is the integral of the Eq. (3.25) Hamiltonian
density, pointwise in momentum space. -/
lemma vytheeswaranFourierLegendreAction_eq_Eq325
    {massSq : ℝ} (hm : massSq ≠ 0) (D : VytheeswaranL2CauchyDatum) :
    vytheeswaranFourierLegendreAction massSq D =
      ∫ q, vytheeswaranEq325HamiltonianDensity
        (D.staticDensity q +
          vytheeswaranSpatialVectorNormSq
            (vytheeswaranVectorCanonicalMomentum (D.vA q)) / 2)
        massSq (D.A q)
        (vytheeswaranTensorCanonicalMomentum massSq (D.A q) (D.vB q)) ∂volume := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with q
  exact vytheeswaranLegendreDensity_eq_Eq325 hm (D.staticDensity q) (D.A q)
    (vytheeswaranVectorCanonicalMomentum (D.vA q))
    (vytheeswaranTensorCanonicalMomentum massSq (D.A q) (D.vB q))

end

/-! ## L. Galperin's harmonic-analyticity form of self-duality

Galperin–Ivanov–Ogievetsky–Sokatchev (Ann. Phys. **185** (1988), §III) express the self-dual Yang–Mills
constraint as the vanishing of the `u⁺`-projected curvature `F⁺⁺ = u⁺ⁱu⁺ʲ F_{ij}` for every harmonic
`u` on the sphere `S²` — the integrability condition (III.7) for the covariantly analytic (CR) field
`𝒟⁺_μ φ = 0` (III.8). This section solders that harmonic criterion
(`AlgebraicQFT.GalperinHarmonicSelfDuality.harmonicProj`) to the concrete Hodge self-duality `⋆F = F`
of §D. The anti-self-dual `SU(2)` triplet `F_{(ij)}` whose vanishing is Galperin's self-duality equation
(`n = 1 : F_{(ij)} = 0`, page 13) is the `∧²₋` sector §D: its three independent components are `E − B`
(`asdTriplet`). The bridge is that Galperin's harmonic constraint on that triplet is exactly `E = B`
(`harmonicProj_asdTriplet_iff_electric_eq_magnetic`), hence exactly `⋆F = F`
(`selfDual_iff_harmonicProj_asdTriplet`) — the harmonic (§III) and Hodge (§D) self-duality criteria of
physlib agree. It also completes §G to an equivalence: `hodgeStar2_eq_self_of_electric_eq_magnetic` is
the converse of `selfDual_electric_eq_magnetic`. -/

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GalperinHarmonicSelfDuality

/-- **The anti-self-dual `SU(2)` triplet** `F_{(ij)}` (Galperin III.3′) as a symmetric `2×2` array whose
three independent entries are the electric-minus-magnetic components
`E − B = (F_{01} − F_{23}, F_{02} − F_{31}, F_{03} − F_{12})` — the `∧²₋` sector of the Hodge
decomposition §D. -/
def asdTriplet (F : Matrix (Fin 4) (Fin 4) ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![F 0 1 - F 2 3, F 0 2 - F 3 1], ![F 0 2 - F 3 1, F 0 3 - F 1 2]]

theorem asdTriplet_00 (F : Matrix (Fin 4) (Fin 4) ℝ) : asdTriplet F 0 0 = F 0 1 - F 2 3 := by
  simp [asdTriplet]
theorem asdTriplet_11 (F : Matrix (Fin 4) (Fin 4) ℝ) : asdTriplet F 1 1 = F 0 3 - F 1 2 := by
  simp [asdTriplet]
theorem asdTriplet_01 (F : Matrix (Fin 4) (Fin 4) ℝ) : asdTriplet F 0 1 = F 0 2 - F 3 1 := by
  simp [asdTriplet]
theorem asdTriplet_10 (F : Matrix (Fin 4) (Fin 4) ℝ) : asdTriplet F 1 0 = F 0 2 - F 3 1 := by
  simp [asdTriplet]

/-- The ASD triplet is symmetric in its `SU(2)` indices (the `∧²₋` sector is a spin-1 triplet). -/
theorem asdTriplet_symm (F : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 2) :
    asdTriplet F i j = asdTriplet F j i := by
  fin_cases i <;> fin_cases j <;> simp [asdTriplet]

/-- **Galperin's harmonic self-duality criterion for the ASD triplet is exactly `E = B`.** The projected
curvature `F⁺⁺(u) = u⁺ⁱu⁺ʲ (F_{(ij)})` vanishes for every harmonic `u` (Galperin III.7) if and only if
the electric and magnetic fields coincide, `F_{01} = F_{23}`, `F_{02} = F_{31}`, `F_{03} = F_{12}`. -/
theorem harmonicProj_asdTriplet_iff_electric_eq_magnetic (F : Matrix (Fin 4) (Fin 4) ℝ) :
    (∀ u, harmonicProj (asdTriplet F) u = 0)
      ↔ (F 0 1 = F 2 3 ∧ F 0 2 = F 3 1 ∧ F 0 3 = F 1 2) := by
  constructor
  · intro h
    have a0 := h ![1, 0]; have a1 := h ![0, 1]; have a2 := h ![1, 1]
    rw [harmonicProj_eq] at a0 a1 a2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, asdTriplet_00, asdTriplet_01,
      asdTriplet_10, asdTriplet_11, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
      at a0 a1 a2
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨e1, e2, e3⟩ u
    rw [harmonicProj_eq, asdTriplet_00, asdTriplet_01, asdTriplet_10, asdTriplet_11]
    have p1 : F 0 1 - F 2 3 = 0 := by linarith
    have p2 : F 0 2 - F 3 1 = 0 := by linarith
    have p3 : F 0 3 - F 1 2 = 0 := by linarith
    rw [p1, p2, p3]; ring

/-- **Converse of `selfDual_electric_eq_magnetic`** (completing §G to an equivalence): if the electric
and magnetic fields coincide, `E = B`, then the field strength is Hodge self-dual `⋆F = F`. -/
theorem hodgeStar2_eq_self_of_electric_eq_magnetic (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ i j, F i j = - F j i)
    (hEB : F 0 1 = F 2 3 ∧ F 0 2 = F 3 1 ∧ F 0 3 = F 1 2) : hodgeStar2 F = F := by
  obtain ⟨e1, e2, e3⟩ := hEB
  have Fd : ∀ i, F i i = 0 := fun i => by have := hF i i; linarith
  have k00 : hodgeStar2 F 0 0 = F 0 0 := (hodgeStar2_diag F 0).trans (Fd 0).symm
  have k11 : hodgeStar2 F 1 1 = F 1 1 := (hodgeStar2_diag F 1).trans (Fd 1).symm
  have k22 : hodgeStar2 F 2 2 = F 2 2 := (hodgeStar2_diag F 2).trans (Fd 2).symm
  have k33 : hodgeStar2 F 3 3 = F 3 3 := (hodgeStar2_diag F 3).trans (Fd 3).symm
  have k01 : hodgeStar2 F 0 1 = F 0 1 := by rw [hodgeStar2_apply_01 F hF]; linarith
  have k02 : hodgeStar2 F 0 2 = F 0 2 := by rw [hodgeStar2_apply_02 F hF]; linarith [hF 3 1]
  have k03 : hodgeStar2 F 0 3 = F 0 3 := by rw [hodgeStar2_apply_03 F hF]; linarith
  have k10 : hodgeStar2 F 1 0 = F 1 0 := by rw [hodgeStar2_apply_10 F hF]; linarith [hF 1 0]
  have k12 : hodgeStar2 F 1 2 = F 1 2 := by rw [hodgeStar2_apply_12 F hF]; linarith
  have k13 : hodgeStar2 F 1 3 = F 1 3 := by rw [hodgeStar2_apply_13 F hF]; linarith [hF 1 3, hF 3 1]
  have k20 : hodgeStar2 F 2 0 = F 2 0 := by rw [hodgeStar2_apply_20 F hF]; linarith [hF 2 0, hF 3 1]
  have k21 : hodgeStar2 F 2 1 = F 2 1 := by rw [hodgeStar2_apply_21 F hF]; linarith [hF 2 1]
  have k23 : hodgeStar2 F 2 3 = F 2 3 := by rw [hodgeStar2_apply_23 F hF]; linarith
  have k30 : hodgeStar2 F 3 0 = F 3 0 := by rw [hodgeStar2_apply_30 F hF]; linarith [hF 3 0]
  have k31 : hodgeStar2 F 3 1 = F 3 1 := by rw [hodgeStar2_apply_31 F hF]; linarith
  have k32 : hodgeStar2 F 3 2 = F 3 2 := by rw [hodgeStar2_apply_32 F hF]; linarith [hF 3 2]
  ext μ ν
  fin_cases μ <;> fin_cases ν
  · exact k00
  · exact k01
  · exact k02
  · exact k03
  · exact k10
  · exact k11
  · exact k12
  · exact k13
  · exact k20
  · exact k21
  · exact k22
  · exact k23
  · exact k30
  · exact k31
  · exact k32
  · exact k33

/-- **The bridge**: Galperin's harmonic self-duality of the ASD triplet (III.7) ⟺ Hodge self-duality
`⋆F = F` (§D). The `SU(2)`-harmonic (§III) and Hodge-star (§D) formulations of the self-dual Yang–Mills
equation coincide: the `u⁺u⁺`-projected curvature vanishes on the whole sphere iff the field strength is
its own Hodge dual. -/
theorem selfDual_iff_harmonicProj_asdTriplet (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ i j, F i j = - F j i) :
    hodgeStar2 F = F ↔ (∀ u, harmonicProj (asdTriplet F) u = 0) := by
  rw [harmonicProj_asdTriplet_iff_electric_eq_magnetic]
  exact ⟨selfDual_electric_eq_magnetic F hF, hodgeStar2_eq_self_of_electric_eq_magnetic F hF⟩

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.maxwellFourierAction_stationary_iff_sourceFree where
  formalizes @ "claim:the-explicit-quadratic-fourier-maxwell-action-has-directional-derivative-the-faraday-pairing-and-is-stationary-in-every-gauge-potential-direction-if-and-only-if-the-source-free-maxwell-equation-holds",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.maxwellFourierAction_line_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.maxwell_variational",
  caveat @ "epistemic:exact-euclidean-single-fourier-mode-action-and-directional-derivative-not-the-curved-spacetime-integrated-action-its-boundary-domain-or-the-metric-variation-producing-maxwell-stress-energy"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranTensorDualVector_gauge_invariant where
  formalizes @ "claim:vytheeswaran-1998-equation-3.22-the-proca-gauge-unfixed-vector-is-the-codifferential-of-a-hodge-dual-antisymmetric-tensor-and-is-invariant-under-two-form-gauge-shifts",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranTensorDualVector_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranTensorDualVector_conserved",
  caveat @ "epistemic:exact-four-dimensional-fourier-symbol-identity-whose-spacetime-distribution-extension-is-attached-separately-not-an-interacting-quantum-equivalence"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMaxwellTensorLagrangian_gauge_invariant where
  formalizes @ "claim:vytheeswaran-1998-equation-3.27-the-mostly-minus-lorentzian-fourier-mode-maxwell-antisymmetric-tensor-lagrangian-is-invariant-under-the-vector-and-two-form-gauge-actions",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranThreeForm_faradayGauge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranTopologicalCoupling_eq_epsilonThreeForm",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranTensorDualVector_conserved",
  caveat @ "epistemic:exact-lorentzian-fourier-symbol-action-density-with-its-exact-three-plus-one-and-integrated-L2-plancherel-carrier-formalized-separately-not-a-quantized-interacting-measure"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranConstraint_firstClass where
  formalizes @ "claim:vytheeswaran-1998-equations-3.28-and-3.30-the-four-primary-and-four-secondary-maxwell-tensor-constraints-have-pairwise-vanishing-canonical-poisson-brackets",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranCanonicalBracket",
  supported_by @ "paper:vytheeswaran-1998-ijmpa13-765-equations-3.28-3.30",
  caveat @ "epistemic:exact-single-fourier-mode-linear-constraint-algebra-promoted-separately-to-an-almost-everywhere-L2-fourier-constraint-surface-not-a-brst-quantization"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranEq323HamiltonianDensity_gauge_invariant where
  formalizes @ "claim:vytheeswaran-1998-equation-3.23-the-hamiltonian-density-written-through-the-tensor-dual-vector-and-three-form-is-invariant-under-two-form-gauge-shifts",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranTensorDualVector_gauge_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranThreeForm_faradayGauge",
  caveat @ "epistemic:exact-fourier-mode-density-not-the-spatially-integrated-unbounded-hamiltonian-its-self-adjoint-domain-or-the-continuum-legendre-transform"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranEq325TensorCorrection_squareCompletion where
  formalizes @ "claim:vytheeswaran-1998-equations-3.24-3.25-the-antisymmetric-tensor-momentum-correction-is-an-exact-completed-square-and-unitary-gauge-recovers-the-proca-density",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranEq325HamiltonianDensity_unitaryGauge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranCauchyLagrangian_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranLegendreDensity_eq_Eq325",
  caveat @ "epistemic:exact-nonzero-mass-fourier-mode-legendre-algebra-in-the-three-independent-spatial-dual-components-with-the-integrated-L2-transform-attached-separately-not-a-boundary-value-domain"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranEq329HamiltonianDensity_onConstraintSurface where
  formalizes @ "claim:vytheeswaran-1998-equations-3.25-and-3.29-the-canonical-maxwell-tensor-hamiltonian-differs-from-the-gauge-unfixed-hamiltonian-by-secondary-constraint-multipliers-and-agrees-on-the-constraint-surface",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranConstraint_firstClass",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMultiplierHamiltonian_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranPrimaryPreservation_iff_secondaryConstraints",
  caveat @ "epistemic:exact-fourier-mode-dirac-bergmann-multiplier-derivative-with-an-almost-everywhere-continuum-constraint-surface-attached-separately-not-a-distributional-time-flow-or-boundary-term-analysis"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranCauchyLagrangian_hasDerivAt where
  formalizes @ "claim:vytheeswaran-1998-equation-3.28-the-vector-and-antisymmetric-tensor-canonical-momenta-are-the-actual-directional-derivative-of-the-cauchy-lagrangian",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranSpatialVectorNormSq_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranTensorCanonicalMomentum_inverse",
  caveat @ "epistemic:exact-single-fourier-mode-cauchy-velocity-derivative-with-a-fixed-spatial-dual-sign-convention-not-the-integrated-field-space-frechet-derivative"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranLegendreDensity_eq_Eq325 where
  formalizes @ "claim:vytheeswaran-1998-equations-3.25-and-3.27-the-nonzero-mass-legendre-transform-of-the-cauchy-lagrangian-is-the-gauge-unfixed-hamiltonian-density",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranCauchyLagrangian_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranEq325TensorCorrection_squareCompletion",
  caveat @ "epistemic:exact-regular-fourier-mode-legendre-transform-for-nonzero-mass-not-an-unbounded-continuum-hamiltonian-or-quantum-equivalence"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranPrimaryPreservation_iff_secondaryConstraints where
  formalizes @ "claim:vytheeswaran-1998-equations-3.29-3.30-dirac-bergmann-preservation-of-the-four-primary-momenta-is-equivalent-to-the-gauss-and-three-tensor-secondary-constraints",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMultiplierHamiltonian_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranConstraint_firstClass",
  caveat @ "epistemic:exact-single-fourier-mode-primary-preservation-and-secondary-constraint-equivalence-not-the-global-continuum-dirac-bergmann-flow-brst-cohomology-or-boundary-analysis"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMaxwellTensorLagrangian_threePlusOne where
  formalizes @ "claim:vytheeswaran-1998-equation-3.27-the-full-mostly-minus-lorentzian-maxwell-tensor-density-has-the-exact-cauchy-split-whose-velocity-derivative-and-legendre-transform-give-equations-3.28-and-3.25",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMinkowskiTwoFormContraction_threePlusOne",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMinkowskiThreeFormContraction_threePlusOne",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranTemporalThreeFormDual_eq_neg_tensorDualVector",
  caveat @ "epistemic:exact-single-mode-three-plus-one-identity-for-an-antisymmetric-tensor-potential-in-a-fixed-minkowski-cauchy-chart-not-a-curved-spacetime-foliation"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorDualVector_gauge_invariant where
  formalizes @ "claim:vytheeswaran-1998-equation-3.22-the-antisymmetric-tensor-dual-vector-is-defined-on-arbitrary-spacetime-distributions-and-is-invariant-under-the-continuum-two-form-gauge-shift-B-to-B-plus-dLambda",
  supported_by @ "lean:SpaceTime.distDeriv_commute",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorDualVector_gauge_eq_zero",
  caveat @ "epistemic:exact-linear-distributional-minkowski-spacetime-identity-not-a-nonlinear-interacting-or-curved-covariant-two-form-theory"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorDualVector_conserved where
  formalizes @ "claim:vytheeswaran-1998-equation-3.22-the-continuum-dual-vector-has-identically-zero-distributional-divergence",
  supported_by @ "lean:SpaceTime.distDeriv_commute",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumDivergence",
  caveat @ "epistemic:kinematic-conservation-from-commuting-distributional-derivatives-not-a-dynamical-quantum-current-conservation-law"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.VytheeswaranL2CauchyDatum.onConstraintSurface_iff_primaryPreserved where
  formalizes @ "claim:vytheeswaran-1998-equations-3.29-3.30-the-secondary-constraint-surface-and-primary-momentum-preservation-are-equivalent-almost-everywhere-on-the-L2-fourier-cauchy-domain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranPrimaryPreservation_iff_secondaryConstraints",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.VytheeswaranL2CauchyDatum.cauchyDensity_integrable",
  caveat @ "epistemic:almost-everywhere-fourier-constraint-domain-with-derived-canonical-momenta-not-a-construction-of-the-global-dirac-bergmann-time-flow"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranFourierLegendreAction_eq_Eq325 where
  formalizes @ "claim:vytheeswaran-1998-equations-3.25-and-3.27-the-spatially-integrated-L2-fourier-cauchy-legendre-action-equals-the-integral-of-the-gauge-unfixed-hamiltonian-density",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranLegendreDensity_eq_Eq325",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.VytheeswaranL2CauchyDatum.cauchyDensity_integrable",
  caveat @ "epistemic:exact-plancherel-momentum-space-L2-action-for-nonzero-mass-not-a-self-adjoint-unbounded-operator-domain-or-functional-measure-quantization"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector

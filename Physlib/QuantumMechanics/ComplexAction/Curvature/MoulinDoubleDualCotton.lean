/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinFieldEquation

/-!
# The double (Hodge) dual Riemann tensor and the Cotton tensor

Implements §5 of F. Moulin, *Generalization of Einstein's gravitational field equations* (arXiv:2405.03698):
the **double (Hodge) dual Riemann tensor** `*R*_{ijkl}` and the **Cotton tensor** `C_{jkl}`.

* **§A — the double-dual Riemann tensor.** Its closed algebraic form (Eq. 53)

    `*R*_{ijkl} = ¼ e_{ijpq} R^{pqrs} e_{klrs} = −R_{ijkl} + (g_{ik}R_{jl} − g_{il}R_{jk} − g_{jk}R_{il}
      + g_{jl}R_{ik}) − ½(g_{ik}g_{jl} − g_{il}g_{jk}) R`

  contains no covariant derivatives, so it is implemented directly (`doubleDualRiemann`). At the
  energy-conserving value `a = −1/(n−3)` it is `(n−3)` times the generalized Einstein tensor
  (`doubleDualRiemann_eq_fourIndexEinstein`, Moulin Eq. 52), so the field equation reads
  `*R*_{ijkl} = χ(n−3) T_{ijkl}` (`doubleDual_field_eq`, Eq. 54), and its contraction is `(n−3)` times the
  2-index Einstein tensor (`doubleDual_contraction`).

* **§B — the Cotton tensor.** `C_{jkl} = ∇_k R_{jl} − ∇_l R_{jk} + 1/(2(n−1))(g_{jl}∇_k R − g_{jk}∇_l R)`
  (`cottonTensor`). It is **antisymmetric** in its last two indices (`cottonTensor_antisymm`). The Cotton
  tensor controls the divergence of the generalized Einstein tensor, `∇^i G_{ijkl} = −(1+a(n−3))/(n−2) C_{jkl}`
  (Moulin Eq. 50); total energy-momentum conservation `∇^i G_{ijkl} = 0` is therefore the vanishing of its
  coefficient, fixing `a = −1/(n−3)` (`conservation_coefficient_zero`, `conservation_coefficient_iff`,
  Eq. 51).

  Because physlib has no covariant-derivative operator, the covariant derivatives `∇_i R_{jk}` and `∇_i R`
  enter as given fields (`nablaRic`, `nablaR`); the metric/algebraic structure (antisymmetry, the
  conservation coefficient) is exact, while the full `∇`-divergence identity awaits a connection layer.

## References

* F. Moulin (2024), arXiv:2405.03698, §5, Eqs. 50–54; E. Cotton (1899). structure: `Physlib`
  (`GravitationalFieldEquations.MoulinEnergyMomentumDecomposition`, `GravitationalFieldEquations.MoulinFieldEquation`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §A — the double (Hodge) dual Riemann tensor -/

/-- **The double (Hodge) dual Riemann tensor** (Moulin Eq. 53), in closed algebraic form
`*R*_{ijkl} = −R_{ijkl} + (g_{ik}R_{jl} − g_{il}R_{jk} − g_{jk}R_{il} + g_{jl}R_{ik})
− ½(g_{ik}g_{jl} − g_{il}g_{jk}) R`. -/
noncomputable def doubleDualRiemann (g Ric : Matrix ι ι ℝ) (scalarR : ℝ) (Rm : RiemannTensor ι) :
    RiemannTensor ι :=
  fun i j k l => -Rm i j k l
    + (g i k * Ric j l - g i l * Ric j k - g j k * Ric i l + g j l * Ric i k)
    - (1 / 2) * scalarR * (g i k * g j l - g i l * g j k)

variable {g gInv : Matrix ι ι ℝ}

omit [Fintype ι] [DecidableEq ι] in
/-- **[Moulin Eq. 52] `*R*_{ijkl} = (n−3) G_{ijkl}` at `a = −1/(n−3)`.** The double-dual Riemann tensor is
`(n−3)` times the generalized Einstein tensor at the energy-conserving parameter. -/
theorem doubleDualRiemann_eq_fourIndexEinstein (n : ℝ) (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm : RiemannTensor ι) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) (hn3 : n - 3 ≠ 0) :
    doubleDualRiemann g Ric scalarR Rm
      = (n - 3) • fourIndexEinsteinTensor (-1 / (n - 3)) n g Ric scalarR Rm := by
  funext i j k l
  simp only [doubleDualRiemann, fourIndexEinsteinTensor, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **[Contraction of the double-dual] `gᵃᶜ *R*_{abcd} = (n−3)(R_{bd} − ½R g_{bd})`** — `(n−3)` times the
ordinary 2-index Einstein tensor. -/
theorem doubleDual_contraction (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0)
    (hn3 : ((Fintype.card ι : ℝ) - 3) ≠ 0) :
    ricci gInv (doubleDualRiemann g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm)
      = ((Fintype.card ι : ℝ) - 3) • einsteinTensor (ricci gInv Rm) (scalarCurvature gInv Rm) g := by
  rw [doubleDualRiemann_eq_fourIndexEinstein _ _ _ _ hn1 hn2 hn3, ricci_smul,
    fourIndexEinstein_contraction _ hg hgi hinv h hn1 hn2]

omit [DecidableEq ι] in
/-- **[Moulin Eq. 54] `*R*_{ijkl} = χ(n−3) T_{ijkl}`.** If the 4-index field equation holds at the
energy-conserving `a = −1/(n−3)`, the double-dual Riemann tensor is `χ(n−3)` times the energy-momentum
tensor. -/
theorem doubleDual_field_eq (χ : ℝ) (T4 : RiemannTensor ι) (Rm : RiemannTensor ι)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0)
    (hn3 : ((Fintype.card ι : ℝ) - 3) ≠ 0)
    (hfield : FourIndexEinsteinFieldEquation (-1 / ((Fintype.card ι : ℝ) - 3)) g (ricci gInv Rm)
      (scalarCurvature gInv Rm) Rm χ T4) :
    doubleDualRiemann g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm
      = (χ * ((Fintype.card ι : ℝ) - 3)) • T4 := by
  rw [doubleDualRiemann_eq_fourIndexEinstein _ _ _ _ hn1 hn2 hn3,
    show fourIndexEinsteinTensor (-1 / ((Fintype.card ι : ℝ) - 3)) (Fintype.card ι) g
      (ricci gInv Rm) (scalarCurvature gInv Rm) Rm = χ • T4 from hfield, smul_smul, mul_comm]

/-! ## §B — the Cotton tensor -/

/-- **The Cotton tensor** (Moulin Eq. 50) `C_{jkl} = ∇_k R_{jl} − ∇_l R_{jk} + 1/(2(n−1))(g_{jl}∇_k R −
g_{jk}∇_l R)`. The covariant derivatives `∇_i R_{jk} = nablaRic i j k` and `∇_i R = nablaR i` enter as given
fields (physlib has no `∇` operator). -/
noncomputable def cottonTensor (n : ℝ) (g : Matrix ι ι ℝ) (nablaRic : ι → ι → ι → ℝ) (nablaR : ι → ℝ) :
    ι → ι → ι → ℝ :=
  fun j k l => nablaRic k j l - nablaRic l j k
    + (1 / (2 * (n - 1))) * (g j l * nablaR k - g j k * nablaR l)

omit [Fintype ι] [DecidableEq ι] in
/-- **[The Cotton tensor is antisymmetric in its last two indices] `C_{jkl} = −C_{jlk}`.** -/
theorem cottonTensor_antisymm (n : ℝ) (g : Matrix ι ι ℝ) (nablaRic : ι → ι → ι → ℝ) (nablaR : ι → ℝ)
    (j k l : ι) :
    cottonTensor n g nablaRic nablaR j k l = -cottonTensor n g nablaRic nablaR j l k := by
  simp only [cottonTensor]; ring

/-- **[Energy conservation fixes `a = −1/(n−3)`] the divergence coefficient `1 + a(n−3)` vanishes there**
(Moulin Eq. 51). Since `∇^i G_{ijkl} = −(1 + a(n−3))/(n−2) C_{jkl}`, total energy-momentum conservation is the
vanishing of this coefficient. -/
theorem conservation_coefficient_zero (n : ℝ) (hn3 : n - 3 ≠ 0) :
    1 + (-1 / (n - 3)) * (n - 3) = 0 := by
  field_simp; norm_num

/-- **[The conservation coefficient vanishes iff `a = −1/(n−3)`].** -/
theorem conservation_coefficient_iff (a n : ℝ) (hn3 : n - 3 ≠ 0) :
    1 + a * (n - 3) = 0 ↔ a = -1 / (n - 3) := by
  constructor
  · intro hyp
    rw [eq_div_iff hn3]; linarith
  · intro hyp
    rw [hyp]; field_simp; norm_num

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end

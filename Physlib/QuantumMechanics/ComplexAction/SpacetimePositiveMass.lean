/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Mathlib.Analysis.SpecialFunctions.Sqrt
meta import Zil

/-!
# The spacetime positive mass theorem: ADM mass, constraints, dominant energy

Formalization of the algebraic core of H. Bray, S. Hirsch, D. Kazaras, M. Khuri, Y. Zhang, *"Spacetime harmonic
functions and applications to mass"*, arXiv:2102.11421 (2021) — the survey of the level-set / spacetime
harmonic function approach to the positive mass theorem.

The **spacetime positive mass theorem** (Theorem 2.1) states that for an asymptotically flat initial data set
`(M, g, k)` satisfying the dominant energy condition, the ADM energy–momentum `(E, P)` obeys `E ≥ |P|` in each
end, with equality only for Minkowski data. The **ADM mass** is then the Lorentzian length
`m = √(E² − |P|²)` of the 4-momentum (Eq. 2.4) — *real* precisely because `E ≥ |P|`.

* **§A — ADM mass and the 4-momentum (Eq. 2.4).** `admMass E P = √(E² − |P|²)`, identified with the repository's
  Lorentzian rest-mass invariant `restMassSq` (`admMass_sq_eq_restMassSq`); the spacetime-PMT consequences
  `E ≥ |P|`: the 4-momentum is non-spacelike (`momentum_timelike`), `m ≤ E` (`admMass_le_energy`), and the
  rigidity `m = 0 ⟺ E = |P|` (`admMass_eq_zero_iff`, the Minkowski case).
* **§B — Gauss–Codazzi constraints & dominant energy (Eq. 2.2).** the Hamiltonian constraint
  `2μ = R + (Tr k)² − |k|²`; the time-symmetric (`k = 0`) and maximal (`Tr k = 0`) reductions giving `R ≥ 0`
  from `μ ≥ 0`; `DEC ⟹ μ ≥ 0`.
* **§C — spacetime harmonic functions (Eq. 1.2).** `Δu = −(Tr_g k)|∇u|`; on a maximal slice (`Tr k = 0`) this
  reduces to the ordinary harmonic equation `Δu = 0` — Stern's original level-set setting.
* **§D — Gibbons–Wells anti-gravity bound.** The dilatonic effective mass `M + gΣ`, normalized electric
  charge `|Q|/√(4πG)`, and long-range attraction coefficient are packaged exactly as in
  Gibbons–Wells, arXiv:gr-qc/9310002. Their maximal Penrose–Sorkin–Woolgar bound implies that the
  attractive graviton-plus-dilaton force cannot be overwhelmed by vector repulsion
  (`gibbonsWells_bound_implies_no_longRange_repulsion`).
* **§E — five-dimensional null-convergence couplings.** The coefficient conditions of Eq. (1.2) are
  isolated as `GibbonsWellsNullConvergenceCouplings`; the maximal probe charge
  `s = √(1+g²)` is admissible exactly when `g² ≤ 3`, and the Kaluza–Klein endpoint `g²=3, s=2`
  saturates both coefficient inequalities.
* **§F — explicit black holes, independent bounds, and extremal saturation.** The static charged-dilaton
  family obeys Eq. (6.7) for every coupling `g`; explicit witnesses prove that at nonzero dilaton coupling
  neither the causal Gibbons–Wells bound nor the Witten-spinorial bound implies the other; and the
  multi-centre extremal formulas of Eqs. (7.11)–(7.13) saturate the causal bound exactly. The associated
  five-dimensional lift exponents satisfy all three compatibility equations (7.5)–(7.7), make the
  adapted time direction null, and give an explicit inverse for which `S=u` solves the null
  Hamilton–Jacobi equation. The signed physical charge then makes the `γ=0` effective mass vanish.
* **§G — the twisted five-metric and projected Lorentz force.** The covariant quadratic of Eq. (3.1)
  is gauge invariant under the compensated fibre-coordinate shift, and its twisted coframe is proved
  dual to the horizontal momentum used by the inverse metric. The paper's five-momentum
  identification `m=e/κ`, `q=se` derives
  `q/m=sκ`; hence the projected electromagnetic force is the existing matrix Lorentz force scaled by
  `sκ`. Its electromagnetic part does no work, leaving only the scalar-force channel to change the
  dressed mass `m exp(χ−ν)`.
* **§H — the reduced null-Ricci contraction.** The complete field/source normal form of Eq. (5.4) is
  packaged, and the coefficient region of §E proves it nonnegative whenever the source block and the
  electric, magnetic, and scalar squares are nonnegative. Eqs. (4.8)–(4.10) are retained componentwise;
  their mixed, fibre, and base sectors all vanish at the Kaluza–Klein vacuum endpoint. An explicit
  sign-independent source condition strengthens Eqs. (5.8)–(5.9) and discharges the formerly opaque
  source-block premise.
* **§I — BCJ extension.** The projected Lorentz numerator is fed into the repository's existing BCJ
  carrier. Its double copy is `(sκ)²` times the bare Lorentz double copy, is nonnegative and `T`-even,
  and its component sum is the quadratic form of the already-proved `F²` curvature generator. This is
  a repository extension, not a claim made in the 1993 paper.
* **§J — the linearized derivation.** The exact asymptotic `(4,5)` block of Eq. (8.9) is contracted
  with the two null directions `(1,±1)`. Nonnegativity of those two contractions derives
  `s|Q|/√(4πG) ≤ M+gΣ`, rather than merely assuming the displayed bound.
* **§K — asymptotic delay and causal focusing.** The two `γ→0,π` endpoint masses derive the
  absolute charge bound. The physical coefficients derived from `φ∼GΣ/(κr)`,
  `3ν=2gκφ`, and `ν+2χ=0` reproduce the normalized mass carrier exactly when
  `κ²=4πG`; negative `M̂` makes the leading logarithmic time delay tend to `+∞`;
  and the five-dimensional Raychaudhuri equation is reduced by an exact `2/3` rescaling to the
  repository's proved focusing theorem. The global Penrose–Sorkin–Woolgar/generic-condition
  implication remains a visible certificate field.

The deep content — that the harmonic / spacetime-harmonic level-set machinery *proves* `E ≥ |P|` (Theorem 2.1)
and Stern's integral identity (Eq. 1.1) — is the paper's theorem, taken here as the hypothesis from which the
mass algebra follows. The paper's Penrose-inequality thread connects to `RiemannianPenroseInequality`.

## References

* Bray, Hirsch, Kazaras, Khuri, Zhang, arXiv:2102.11421 — Eqs. (1.1), (1.2), (2.1), (2.2), (2.4), Thm. 2.1.
  `Physlib` (`Bogoliubov.RestFrameQIFConsistency.restMassSq`, `RiemannianPenroseInequality`).
* G.W. Gibbons, C.G. Wells, *Anti-Gravity Bounds and the Ricci Tensor*, arXiv:gr-qc/9310002 —
  Eqs. (1.1)–(1.10), (2.4), (5.7), (6.7), and (7.10)–(7.13).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM
open Physlib.Thermodynamics

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass

open Matrix


/-- The **ADM mass** `m = √(E² − |P|²)` — the Lorentzian length of the ADM 4-momentum `(E, P)` (Eq. 2.4),
where `P = |P⃗|`. -/
noncomputable def admMass (E P : ℝ) : ℝ := Real.sqrt (E ^ 2 - P ^ 2)

/-- **[The 4-momentum is non-spacelike]** under the spacetime-PMT inequality `|P| ≤ E` (Thm. 2.1), the
Minkowski norm `E² − |P|²` is nonnegative: the ADM 4-momentum `(E, P)` is timelike or null. -/
lemma momentum_timelike (E P : ℝ) (h : P ≤ E) (hP : 0 ≤ P) : 0 ≤ E ^ 2 - P ^ 2 := by
  nlinarith

/-- **[The ADM mass is the Lorentzian rest-mass invariant]** `m² = E² − |P|² = restMassSq E |P|` — the ADM mass
squared is exactly the repository's Lorentzian rest-mass invariant of the 4-momentum `(E, P)`. -/
lemma admMass_sq_eq_restMassSq (E P : ℝ) (h : P ≤ E) (hP : 0 ≤ P) :
    admMass E P ^ 2 = restMassSq E P := by
  unfold admMass restMassSq
  rw [Real.sq_sqrt (momentum_timelike E P h hP)]

/-- **[Mass does not exceed energy]** `m ≤ E` — the rest mass is at most the ADM energy. -/
lemma admMass_le_energy (E P : ℝ) (h : P ≤ E) (hP : 0 ≤ P) : admMass E P ≤ E := by
  have hE : 0 ≤ E := le_trans hP h
  calc admMass E P = Real.sqrt (E ^ 2 - P ^ 2) := rfl
    _ ≤ Real.sqrt (E ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = E := Real.sqrt_sq hE

/-- **[Rigidity: zero mass ⟺ null 4-momentum]** `m = 0 ⟺ E = |P|` — the ADM mass vanishes exactly when the
4-momentum is null, the equality case of the spacetime PMT (Minkowski data). -/
lemma admMass_eq_zero_iff (E P : ℝ) (h : P ≤ E) (hP : 0 ≤ P) : admMass E P = 0 ↔ E = P := by
  unfold admMass
  rw [Real.sqrt_eq_zero']
  constructor
  · intro hh
    have hE : 0 ≤ E := le_trans hP h
    have hle : E ^ 2 ≤ P ^ 2 := by linarith
    have hge : P ^ 2 ≤ E ^ 2 := by nlinarith
    have h1 : E ^ 2 = P ^ 2 := le_antisymm hle hge
    calc E = Real.sqrt (E ^ 2) := (Real.sqrt_sq hE).symm
      _ = Real.sqrt (P ^ 2) := by rw [h1]
      _ = P := Real.sqrt_sq hP
  · intro hh; subst hh; simp


/-- The **matter (energy) density** from the Hamiltonian constraint `2μ = R + (Tr k)² − |k|²` (Eq. 2.2):
`μ = (R + (Tr k)² − |k|²)/2`. -/
noncomputable def matterDensity (R trK normKSq : ℝ) : ℝ := (R + trK ^ 2 - normKSq) / 2

/-- **[The Hamiltonian constraint]** `2μ = R + (Tr k)² − |k|²` (Eq. 2.2). -/
lemma two_matterDensity (R trK normKSq : ℝ) :
    2 * matterDensity R trK normKSq = R + trK ^ 2 - normKSq := by
  unfold matterDensity; ring

/-- **[Time-symmetric slice: `μ = R/2`]** when `k = 0` (`Tr k = 0`, `|k|² = 0`) the energy density is half the
scalar curvature. -/
lemma timeSymmetric_matterDensity (R : ℝ) : matterDensity R 0 0 = R / 2 := by
  unfold matterDensity; ring

/-- **[Time-symmetric DEC ⟹ nonnegative scalar curvature]** with `k = 0` and `μ ≥ 0`, `R = 2μ ≥ 0` — the
nonnegative-scalar-curvature hypothesis behind the Geroch conjecture and the Riemannian PMT. -/
lemma timeSymmetric_R_nonneg (R : ℝ) (hμ : 0 ≤ matterDensity R 0 0) : 0 ≤ R := by
  rw [timeSymmetric_matterDensity] at hμ; linarith

/-- **[Maximal slice: `R = 2μ + |k|²`]** when `Tr k = 0`, the scalar curvature is `R = 2μ + |k|²`. -/
lemma maximal_scalarCurvature (R normKSq : ℝ) :
    R = 2 * matterDensity R 0 normKSq + normKSq := by
  unfold matterDensity; ring

/-- **[Maximal slice + DEC ⟹ `R ≥ 0`]** with `Tr k = 0`, `μ ≥ 0`, the scalar curvature `R = 2μ + |k|² ≥ 0`. -/
lemma maximal_R_nonneg (R normKSq : ℝ) (hμ : 0 ≤ matterDensity R 0 normKSq) (hk : 0 ≤ normKSq) :
    0 ≤ R := by
  rw [maximal_scalarCurvature R normKSq]; linarith

/-- **[Dominant energy condition ⟹ nonnegative energy density]** `μ ≥ |J| ≥ 0` ⟹ `μ ≥ 0`. -/
lemma dec_implies_matterDensity_nonneg (μ J : ℝ) (hdec : |J| ≤ μ) : 0 ≤ μ :=
  le_trans (abs_nonneg J) hdec


/-- The **spacetime harmonic function equation** `Δu = −(Tr_g k)|∇u|` (Eq. 1.2): `lap = Δu`,
`gradNorm = |∇u|`. -/
def IsSpacetimeHarmonic (lap trK gradNorm : ℝ) : Prop := lap = -(trK * gradNorm)

/-- **[Maximal slice ⟹ ordinary harmonic]** when `Tr k = 0`, the spacetime harmonic equation reduces to
`Δu = 0` — recovering Stern's original harmonic level-set setting. -/
lemma spacetimeHarmonic_maximal_iff (lap gradNorm : ℝ) :
    IsSpacetimeHarmonic lap 0 gradNorm ↔ lap = 0 := by
  unfold IsSpacetimeHarmonic; rw [zero_mul, neg_zero]


/-! ## D. The Gibbons–Wells mass–charge bound and long-range force -/

/-- The mass seen by the auxiliary five-dimensional causal argument:
`M_eff = M + gΣ`, where `M` is ADM mass and `Σ` is scalar charge. -/
def gibbonsWellsEffectiveMass (M Sigma g : ℝ) : ℝ := M + g * Sigma

/-- Electric charge in the gravitational units used by the paper,
`q̂ = |Q| / √(4πG)`. -/
noncomputable def gravitationallyNormalizedCharge (G Q : ℝ) : ℝ :=
  |Q| / Real.sqrt (4 * Real.pi * G)

/-- The Gibbons–Wells causal bound (Eq. (1.1)) for probe coupling `s`:
`M + gΣ ≥ s |Q|/√(4πG)`. -/
def GibbonsWellsBound (G g s M Sigma Q : ℝ) : Prop :=
  s * gravitationallyNormalizedCharge G Q ≤ gibbonsWellsEffectiveMass M Sigma g

/-- The coefficient of the inverse-square long-range force between two identical objects
(Eq. (2.4)): nonnegative means graviton-plus-scalar attraction is at least the vector
repulsion. -/
noncomputable def gibbonsWellsAttractionCoefficient (G M Sigma Q : ℝ) : ℝ :=
  G * (M ^ 2 + Sigma ^ 2) - Q ^ 2 / (4 * Real.pi)

/-- The elementary two-component Cauchy inequality behind the anti-gravity conclusion. -/
lemma gibbonsWells_effectiveMass_sq_le (M Sigma g : ℝ) :
    gibbonsWellsEffectiveMass M Sigma g ^ 2 ≤
      (1 + g ^ 2) * (M ^ 2 + Sigma ^ 2) := by
  unfold gibbonsWellsEffectiveMass
  nlinarith [sq_nonneg (g * M - Sigma)]

/-- In normalized gravitational units, the maximal Gibbons–Wells bound forces
`q̂² ≤ M² + Σ²`. This is the exact algebraic statement that vector repulsion cannot
overwhelm gravitational plus scalar attraction. -/
lemma gibbonsWells_maximal_bound_implies_charge_sq_le
    (g M Sigma qHat : ℝ) (hq : 0 ≤ qHat)
    (hbound : Real.sqrt (1 + g ^ 2) * qHat ≤
      gibbonsWellsEffectiveMass M Sigma g) :
    qHat ^ 2 ≤ M ^ 2 + Sigma ^ 2 := by
  have hsqrt : Real.sqrt (1 + g ^ 2) ^ 2 = 1 + g ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hleft : 0 ≤ Real.sqrt (1 + g ^ 2) * qHat :=
    mul_nonneg (Real.sqrt_nonneg _) hq
  have hsquares : (Real.sqrt (1 + g ^ 2) * qHat) ^ 2 ≤
      gibbonsWellsEffectiveMass M Sigma g ^ 2 := by
    nlinarith
  have hfactor : (1 + g ^ 2) * qHat ^ 2 ≤
      (1 + g ^ 2) * (M ^ 2 + Sigma ^ 2) := by
    calc
      (1 + g ^ 2) * qHat ^ 2 =
          (Real.sqrt (1 + g ^ 2) * qHat) ^ 2 := by
            rw [mul_pow, hsqrt]
      _ ≤ gibbonsWellsEffectiveMass M Sigma g ^ 2 := hsquares
      _ ≤ (1 + g ^ 2) * (M ^ 2 + Sigma ^ 2) :=
        gibbonsWells_effectiveMass_sq_le M Sigma g
  exact le_of_mul_le_mul_left hfactor (by positivity)

/-- Squaring the gravitationally normalized charge and restoring `G` produces exactly
the Coulomb coefficient `Q²/(4π)`. -/
lemma gravitationallyNormalizedCharge_sq_mul_G
    (G Q : ℝ) (hG : 0 < G) :
    G * gravitationallyNormalizedCharge G Q ^ 2 = Q ^ 2 / (4 * Real.pi) := by
  have hrad : 0 ≤ 4 * Real.pi * G := by positivity
  have hsqrt : Real.sqrt (4 * Real.pi * G) ^ 2 = 4 * Real.pi * G :=
    Real.sq_sqrt hrad
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold gravitationallyNormalizedCharge
  rw [div_pow, sq_abs, hsqrt]
  field_simp

/-- **Anti-gravity exclusion.** Under positive Newton coupling, the paper's maximal
causal bound `M + gΣ ≥ √(1+g²)|Q|/√(4πG)` makes the long-range attraction coefficient
nonnegative. Thus the vector force can reach equipoise but cannot dominate. -/
theorem gibbonsWells_bound_implies_no_longRange_repulsion
    (G g M Sigma Q : ℝ) (hG : 0 < G)
    (hbound : GibbonsWellsBound G g (Real.sqrt (1 + g ^ 2)) M Sigma Q) :
    0 ≤ gibbonsWellsAttractionCoefficient G M Sigma Q := by
  have hq : 0 ≤ gravitationallyNormalizedCharge G Q :=
    div_nonneg (abs_nonneg Q) (Real.sqrt_nonneg _)
  have hcharge := gibbonsWells_maximal_bound_implies_charge_sq_le
    g M Sigma (gravitationallyNormalizedCharge G Q) hq hbound
  have hmul := mul_le_mul_of_nonneg_left hcharge (le_of_lt hG)
  rw [gravitationallyNormalizedCharge_sq_mul_G G Q hG] at hmul
  unfold gibbonsWellsAttractionCoefficient
  linarith


/-! ## E. The five-dimensional null-convergence coefficient region -/

/-- The three sufficient coefficient inequalities obtained from the auxiliary
five-dimensional null-convergence calculation (Eqs. (1.2) and (5.7)). Source energy
conditions are deliberately separate from this purely coupling-level predicate. -/
def GibbonsWellsNullConvergenceCouplings (g s : ℝ) : Prop :=
  g ^ 2 ≤ 3 ∧ 2 * (g ^ 2 - 1) ≤ s ^ 2 ∧ s ^ 2 ≤ 1 + g ^ 2

/-- At the maximal probe coupling `s=√(1+g²)`, all coefficient inequalities hold exactly
through `g²≤3`. This isolates the paper's sufficient coupling range without claiming it
is necessary for the physical bound. -/
theorem gibbonsWells_maximalProbe_admissible_iff (g : ℝ) :
    GibbonsWellsNullConvergenceCouplings g (Real.sqrt (1 + g ^ 2)) ↔ g ^ 2 ≤ 3 := by
  have hsqrt : Real.sqrt (1 + g ^ 2) ^ 2 = 1 + g ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold GibbonsWellsNullConvergenceCouplings
  rw [hsqrt]
  constructor
  · exact fun h => h.1
  · intro hg
    constructor
    · exact hg
    constructor <;> nlinarith

/-- The standard five-dimensional Kaluza–Klein endpoint `g²=3, s=2` saturates both
the lower and upper null-convergence coefficient inequalities. -/
theorem gibbonsWells_kaluzaKlein_endpoint
    (g : ℝ) (hg : g ^ 2 = 3) :
    GibbonsWellsNullConvergenceCouplings g 2 := by
  unfold GibbonsWellsNullConvergenceCouplings
  constructor
  · linarith
  constructor <;> norm_num [hg]


/-! ## F. Independence from the spinorial bound and extremal saturation -/

/-- The source-free Witten-spinorial dilaton bound (Eq. (1.8)), written in the same
normalized units: `M ≥ q̂/√(1+g²)`. -/
def GibbonsWellsSpinorialBound (g M qHat : ℝ) : Prop :=
  qHat / Real.sqrt (1 + g ^ 2) ≤ M

/-- At dilaton coupling `g=1`, the causal bound does **not** imply the spinorial bound.
The witness carries its whole effective mass in scalar charge. -/
theorem gibbonsWells_causal_not_imply_spinorial :
    ∃ M Sigma : ℝ,
      Real.sqrt (1 + (1 : ℝ) ^ 2) ≤ gibbonsWellsEffectiveMass M Sigma 1 ∧
      ¬ GibbonsWellsSpinorialBound 1 M 1 := by
  refine ⟨0, Real.sqrt 2, ?_, ?_⟩
  · norm_num [gibbonsWellsEffectiveMass]
  · unfold GibbonsWellsSpinorialBound
    norm_num

/-- Conversely, at `g=1` the source-free spinorial bound does **not** imply the causal
bound. This kernel-checked pair of witnesses formalizes the paper's statement that the
two methods provide independent information when a scalar is present. -/
theorem gibbonsWells_spinorial_not_imply_causal :
    ∃ M Sigma : ℝ,
      GibbonsWellsSpinorialBound 1 M 1 ∧
      ¬ Real.sqrt (1 + (1 : ℝ) ^ 2) ≤ gibbonsWellsEffectiveMass M Sigma 1 := by
  refine ⟨1 / Real.sqrt 2, 0, ?_, ?_⟩
  · norm_num [GibbonsWellsSpinorialBound]
  · norm_num [gibbonsWellsEffectiveMass]
    have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    exact (inv_lt_iff_one_lt_mul₀' hpos).2 (by nlinarith)

/-- ADM mass of the static charged dilaton black-hole family (Eq. (6.4)). -/
noncomputable def gibbonsWellsBlackHoleMass
    (G g rPlus rMinus : ℝ) : ℝ :=
  (rPlus + ((1 - g ^ 2) / (1 + g ^ 2)) * rMinus) / (2 * G)

/-- Scalar charge of the static charged dilaton black-hole family (Eq. (6.6)). -/
noncomputable def gibbonsWellsBlackHoleScalarCharge
    (G g rMinus : ℝ) : ℝ :=
  g * rMinus / (G * (1 + g ^ 2))

/-- Electric-charge magnitude of Eq. (6.5), already divided by `√(4πG)` so it
can be compared directly with `gibbonsWellsEffectiveMass`. -/
noncomputable def gibbonsWellsBlackHoleNormalizedCharge
    (G g rPlus rMinus : ℝ) : ℝ :=
  Real.sqrt (rPlus * rMinus) / (G * Real.sqrt (1 + g ^ 2))

/-- The mass and scalar-charge formulas (6.4), (6.6) collapse to the simple
effective mass `(r₊+r₋)/(2G)` used in Eq. (6.7). -/
lemma gibbonsWells_blackHole_effectiveMass_eq
    (G g rPlus rMinus : ℝ) (hG : G ≠ 0) :
    gibbonsWellsEffectiveMass
      (gibbonsWellsBlackHoleMass G g rPlus rMinus)
      (gibbonsWellsBlackHoleScalarCharge G g rMinus) g =
      (rPlus + rMinus) / (2 * G) := by
  have hg : 1 + g ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold gibbonsWellsEffectiveMass gibbonsWellsBlackHoleMass
    gibbonsWellsBlackHoleScalarCharge
  field_simp
  ring

/-- The arithmetic-geometric mean inequality in the exact horizon-radius form used
in the black-hole comparison: `√(r₊r₋) ≤ (r₊+r₋)/2`. -/
lemma gibbonsWells_sqrt_mul_le_average
    (rPlus rMinus : ℝ) (hrPlus : 0 ≤ rPlus) (hrMinus : 0 ≤ rMinus) :
    Real.sqrt (rPlus * rMinus) ≤ (rPlus + rMinus) / 2 := by
  have hprod : 0 ≤ rPlus * rMinus := mul_nonneg hrPlus hrMinus
  have hsqrt : Real.sqrt (rPlus * rMinus) ^ 2 = rPlus * rMinus :=
    Real.sq_sqrt hprod
  have hroot : 0 ≤ Real.sqrt (rPlus * rMinus) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (rPlus - rMinus)]

/-- **Static black-hole check (Eq. (6.7)).** Every member of the charged dilaton
black-hole family with nonnegative horizon radii satisfies the maximal Gibbons–Wells
bound. Unlike the five-dimensional proof's sufficient coefficient calculation, this
explicit family needs no restriction `g² ≤ 3`. -/
theorem gibbonsWells_blackHole_satisfies_maximal_bound
    (G g rPlus rMinus : ℝ) (hG : 0 < G)
    (hrPlus : 0 ≤ rPlus) (hrMinus : 0 ≤ rMinus) :
    Real.sqrt (1 + g ^ 2) *
        gibbonsWellsBlackHoleNormalizedCharge G g rPlus rMinus ≤
      gibbonsWellsEffectiveMass
        (gibbonsWellsBlackHoleMass G g rPlus rMinus)
        (gibbonsWellsBlackHoleScalarCharge G g rMinus) g := by
  have hsqrt : Real.sqrt (1 + g ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  rw [gibbonsWells_blackHole_effectiveMass_eq G g rPlus rMinus (ne_of_gt hG)]
  unfold gibbonsWellsBlackHoleNormalizedCharge
  have hcancel : Real.sqrt (1 + g ^ 2) *
      (Real.sqrt (rPlus * rMinus) / (G * Real.sqrt (1 + g ^ 2))) =
      Real.sqrt (rPlus * rMinus) / G := by
    field_simp
  rw [hcancel]
  have hamgm := gibbonsWells_sqrt_mul_le_average rPlus rMinus hrPlus hrMinus
  rw [show (rPlus + rMinus) / (2 * G) = ((rPlus + rMinus) / 2) / G by ring]
  exact (div_le_div_iff_of_pos_right hG).2 hamgm

/-- Aggregate mass of the extremal multi-centre family (Eq. (7.11)), with `mu` the sum
of the nonnegative centre strengths. -/
noncomputable def gibbonsWellsExtremeMass (g mu : ℝ) : ℝ := mu / (1 + g ^ 2)

/-- Aggregate scalar charge of the extremal multi-centre family (Eq. (7.13)). -/
noncomputable def gibbonsWellsExtremeScalarCharge (g mu : ℝ) : ℝ :=
  g * mu / (1 + g ^ 2)

/-- Magnitude of the extremal electric charge in gravitational units (Eq. (7.12)). -/
noncomputable def gibbonsWellsExtremeNormalizedCharge (g mu : ℝ) : ℝ :=
  |mu| / Real.sqrt (1 + g ^ 2)

/-- Probe coupling in the extremal five-dimensional lift, Eq. (7.5):
`s = √(1+g²)`. -/
noncomputable def gibbonsWellsExtremeProbeCoupling (g : ℝ) : ℝ :=
  Real.sqrt (1 + g ^ 2)

/-- Fibre-warp exponent of the extremal lift, obtained by solving
Eqs. (7.5)–(7.7). -/
noncomputable def gibbonsWellsExtremeLiftAlpha (g : ℝ) : ℝ :=
  4 * g ^ 2 / (3 * (1 + g ^ 2))

/-- Base-warp exponent of the extremal lift, obtained by solving
Eqs. (7.5)–(7.7). -/
noncomputable def gibbonsWellsExtremeLiftBeta (g : ℝ) : ℝ :=
  -(2 * g ^ 2) / (3 * (1 + g ^ 2))

/-- **Equations (7.5)–(7.7).** The explicit extremal lift parameters jointly
satisfy the charge coupling, lightlike-Killing-vector exponent difference,
and dilaton second-derivative cancellation condition. -/
theorem gibbonsWells_extreme_lift_compatible (g : ℝ) :
    gibbonsWellsExtremeProbeCoupling g ^ 2 = 1 + g ^ 2 ∧
    gibbonsWellsExtremeLiftAlpha g - gibbonsWellsExtremeLiftBeta g =
      2 * g ^ 2 / (1 + g ^ 2) ∧
    gibbonsWellsExtremeLiftAlpha g + 2 * gibbonsWellsExtremeLiftBeta g = 0 := by
  have hden : 1 + g ^ 2 ≠ 0 := ne_of_gt (by positivity)
  constructor
  · unfold gibbonsWellsExtremeProbeCoupling
    exact Real.sq_sqrt (by positivity)
  constructor
  · unfold gibbonsWellsExtremeLiftAlpha gibbonsWellsExtremeLiftBeta
    field_simp
    ring
  · unfold gibbonsWellsExtremeLiftAlpha gibbonsWellsExtremeLiftBeta
    field_simp
    ring

/-- The `g_tt` coefficient of the extremal five-dimensional metric (7.4)
in the adapted coordinate `u=x⁵-t`, before simplifying Eqs. (7.5)–(7.7):
`H^(α-2) s²/(1+g²) - H^(β-2/(1+g²))`. -/
noncomputable def gibbonsWellsExtremeLiftTimeCoefficient
    (H g : ℝ) : ℝ :=
  Real.rpow H (gibbonsWellsExtremeLiftAlpha g - 2) *
      (gibbonsWellsExtremeProbeCoupling g ^ 2 / (1 + g ^ 2)) -
    Real.rpow H
      (gibbonsWellsExtremeLiftBeta g - 2 / (1 + g ^ 2))

/-- **The adapted time direction is null.** Eqs. (7.5)–(7.7) make the
two powers and their coefficients identical, so the full `g_tt` coefficient
of the extremal lift vanishes for every value of the harmonic profile `H`. -/
theorem gibbonsWellsExtremeLiftTimeCoefficient_eq_zero (H g : ℝ) :
    gibbonsWellsExtremeLiftTimeCoefficient H g = 0 := by
  have hden : 1 + g ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hs : gibbonsWellsExtremeProbeCoupling g ^ 2 = 1 + g ^ 2 :=
    (gibbonsWells_extreme_lift_compatible g).1
  have hratio :
      gibbonsWellsExtremeProbeCoupling g ^ 2 / (1 + g ^ 2) = 1 := by
    rw [hs]
    exact div_self hden
  have hexp :
      gibbonsWellsExtremeLiftAlpha g - 2 =
        gibbonsWellsExtremeLiftBeta g - 2 / (1 + g ^ 2) := by
    unfold gibbonsWellsExtremeLiftAlpha gibbonsWellsExtremeLiftBeta
    field_simp
    ring
  unfold gibbonsWellsExtremeLiftTimeCoefficient
  rw [hratio, hexp]
  ring

/-- The adapted `(u,t)` block of the extremal lift (7.4). Its off-diagonal
entry already uses `s=√(1+g²)`, while its time-time entry retains the complete
unsimplified cancellation above. -/
noncomputable def gibbonsWellsExtremeLiftUTBlock
    (H g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.rpow H (gibbonsWellsExtremeLiftAlpha g),
      Real.rpow H (gibbonsWellsExtremeLiftAlpha g - 1);
     Real.rpow H (gibbonsWellsExtremeLiftAlpha g - 1),
      gibbonsWellsExtremeLiftTimeCoefficient H g]

/-- The adapted coordinate vector `∂t` in `(u,t)` order. -/
def gibbonsWellsAdaptedTimeVector : Fin 2 → ℝ := ![0, 1]

/-- The actual adapted metric block evaluates to zero on `∂t`, realizing
the null direction required in Eq. (7.5). -/
theorem gibbonsWellsAdaptedTimeVector_is_null (H g : ℝ) :
    gibbonsWellsAdaptedTimeVector ⬝ᵥ
        (gibbonsWellsExtremeLiftUTBlock H g *ᵥ
          gibbonsWellsAdaptedTimeVector) = 0 := by
  simp [gibbonsWellsAdaptedTimeVector, gibbonsWellsExtremeLiftUTBlock,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    gibbonsWellsExtremeLiftTimeCoefficient_eq_zero]

/-- The explicit inverse of the adapted `(u,t)` metric block. -/
noncomputable def gibbonsWellsExtremeLiftUTInverse
    (H g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := Real.rpow H (gibbonsWellsExtremeLiftAlpha g)
  let b := Real.rpow H (gibbonsWellsExtremeLiftAlpha g - 1)
  !![0, b⁻¹; b⁻¹, -a * b⁻¹ ^ 2]

/-- For positive harmonic profile `H`, the displayed inverse really is the
two-sided-relevant matrix inverse: the adapted block times it is the identity. -/
theorem gibbonsWellsExtremeLiftUTBlock_mul_inverse
    (H g : ℝ) (hH : 0 < H) :
    gibbonsWellsExtremeLiftUTBlock H g *
        gibbonsWellsExtremeLiftUTInverse H g = 1 := by
  have hb : Real.rpow H (gibbonsWellsExtremeLiftAlpha g - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hH _)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gibbonsWellsExtremeLiftUTBlock,
      gibbonsWellsExtremeLiftUTInverse,
      gibbonsWellsExtremeLiftTimeCoefficient_eq_zero, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    field_simp [hb] <;> ring

/-- The covector `du`, i.e. the differential of the exact phase
`S=u=-t+x⁵` from Eq. (7.9). -/
def gibbonsWellsAdaptedDuCovector : Fin 2 → ℝ := ![1, 0]

/-- **Equation (7.9).** The exact phase `S=u` satisfies the null
Hamilton–Jacobi equation for the inverse extremal `(u,t)` block. -/
theorem gibbonsWellsAdaptedDu_solves_nullHamiltonJacobi (H g : ℝ) :
    gibbonsWellsAdaptedDuCovector ⬝ᵥ
        (gibbonsWellsExtremeLiftUTInverse H g *ᵥ
          gibbonsWellsAdaptedDuCovector) = 0 := by
  simp [gibbonsWellsAdaptedDuCovector, gibbonsWellsExtremeLiftUTInverse,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Equation (7.8), adapted form.** For `H>0`, raising the exact normal
`du` with the inverse metric and multiplying by `H^(α-1)` gives `∂t`.
Thus the null direction is explicitly proportional to a gradient, the local
hypersurface-orthogonality statement for the level sets `u=constant`. -/
theorem gibbonsWellsAdaptedDu_gradient_eq_timeVector
    (H g : ℝ) (hH : 0 < H) :
    Real.rpow H (gibbonsWellsExtremeLiftAlpha g - 1) •
        (gibbonsWellsExtremeLiftUTInverse H g *ᵥ
          gibbonsWellsAdaptedDuCovector) =
      gibbonsWellsAdaptedTimeVector := by
  have hb : Real.rpow H (gibbonsWellsExtremeLiftAlpha g - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hH _)
  ext i
  fin_cases i <;>
    simp [gibbonsWellsAdaptedDuCovector, gibbonsWellsAdaptedTimeVector,
      gibbonsWellsExtremeLiftUTInverse] <;>
    field_simp [hb]

/-- The signed electric charge of the extremal multi-centre family,
Eq. (7.12), with `mu=∑ᵢ μᵢ`. -/
noncomputable def gibbonsWellsExtremeSignedElectricCharge
    (kappa g mu : ℝ) : ℝ :=
  -kappa * mu / Real.sqrt (1 + g ^ 2)

/-- **Equation (7.10).** The signed physical charge of Eq. (7.12), together
with the mass and scalar charge of Eqs. (7.11), (7.13), exactly saturates
`M+gΣ=-sQ/κ`. -/
theorem gibbonsWells_extreme_signed_charge_saturates
    (kappa g mu : ℝ) (hkappa : kappa ≠ 0) :
    gibbonsWellsEffectiveMass
        (gibbonsWellsExtremeMass g mu)
        (gibbonsWellsExtremeScalarCharge g mu) g =
      -gibbonsWellsExtremeProbeCoupling g *
        gibbonsWellsExtremeSignedElectricCharge kappa g mu / kappa := by
  have hsqrt : Real.sqrt (1 + g ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  unfold gibbonsWellsEffectiveMass gibbonsWellsExtremeMass
    gibbonsWellsExtremeScalarCharge gibbonsWellsExtremeProbeCoupling
    gibbonsWellsExtremeSignedElectricCharge
  field_simp

/-- The extremal multi-centre family saturates the maximal causal bound
(Eqs. (7.10)–(7.13)). -/
theorem gibbonsWells_extreme_multicentre_saturates
    (g mu : ℝ) (_hmu : 0 ≤ mu) :
    Real.sqrt (1 + g ^ 2) * gibbonsWellsExtremeNormalizedCharge g mu =
      gibbonsWellsEffectiveMass
        (gibbonsWellsExtremeMass g mu)
        (gibbonsWellsExtremeScalarCharge g mu) g := by
  have hsqrt : Real.sqrt (1 + g ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  unfold gibbonsWellsExtremeNormalizedCharge gibbonsWellsEffectiveMass
    gibbonsWellsExtremeMass gibbonsWellsExtremeScalarCharge
  rw [abs_of_nonneg _hmu]
  field_simp

/-- Long-range attraction coefficient for two objects in gravitationally normalized
units, Eq. (2.4) divided by `G`: `M₁M₂+Σ₁Σ₂-q̂₁q̂₂`. -/
def gibbonsWellsNormalizedPairAttraction
    (M1 M2 Sigma1 Sigma2 qHat1 qHat2 : ℝ) : ℝ :=
  M1 * M2 + Sigma1 * Sigma2 - qHat1 * qHat2

/-- Two nonnegative centres of the extremal family are in exact long-range
equipoise: gravitational plus scalar attraction equals vector repulsion. -/
theorem gibbonsWells_extreme_multicentre_pair_equipoise
    (g mu1 mu2 : ℝ) (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2) :
    gibbonsWellsNormalizedPairAttraction
      (gibbonsWellsExtremeMass g mu1) (gibbonsWellsExtremeMass g mu2)
      (gibbonsWellsExtremeScalarCharge g mu1)
      (gibbonsWellsExtremeScalarCharge g mu2)
      (gibbonsWellsExtremeNormalizedCharge g mu1)
      (gibbonsWellsExtremeNormalizedCharge g mu2) = 0 := by
  have hg : 1 + g ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hsqrt : Real.sqrt (1 + g ^ 2) ^ 2 = 1 + g ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold gibbonsWellsNormalizedPairAttraction gibbonsWellsExtremeMass
    gibbonsWellsExtremeScalarCharge gibbonsWellsExtremeNormalizedCharge
  rw [abs_of_nonneg hmu1, abs_of_nonneg hmu2]
  field_simp
  rw [hsqrt]
  ring


/-! ## G. Dilaton medium and the projected Lorentz-force law -/

/-- The dilaton-dependent electric permittivity `ε=exp(2gκφ)` (Eq. (2.10)). -/
noncomputable def gibbonsWellsPermittivity (g kappa phi : ℝ) : ℝ :=
  Real.exp (2 * g * kappa * phi)

/-- The dilaton-dependent magnetic permeability `μ=exp(-2gκφ)` (Eq. (2.11)). -/
noncomputable def gibbonsWellsPermeability (g kappa phi : ℝ) : ℝ :=
  Real.exp (-(2 * g * kappa * phi))

/-- The dilaton medium preserves the local light cone: `εμ=1`. -/
theorem gibbonsWells_permittivity_mul_permeability
    (g kappa phi : ℝ) :
    gibbonsWellsPermittivity g kappa phi *
      gibbonsWellsPermeability g kappa phi = 1 := by
  unfold gibbonsWellsPermittivity gibbonsWellsPermeability
  rw [← Real.exp_add]
  ring_nf
  exact Real.exp_zero

/-- Both constitutive coefficients are strictly positive. -/
theorem gibbonsWells_constitutive_coefficients_pos
    (g kappa phi : ℝ) :
    0 < gibbonsWellsPermittivity g kappa phi ∧
      0 < gibbonsWellsPermeability g kappa phi :=
  ⟨Real.exp_pos _, Real.exp_pos _⟩

/-- Electric displacement `D=εE` in the dilaton medium (Eq. (2.10)). -/
noncomputable def gibbonsWellsElectricDisplacement
    (g kappa phi : ℝ) (E : Fin 3 → ℝ) : Fin 3 → ℝ :=
  gibbonsWellsPermittivity g kappa phi • E

/-- Magnetic intensity `H=B/μ=εB`, using `εμ=1` (Eqs. (2.10)–(2.11)). -/
noncomputable def gibbonsWellsMagneticIntensity
    (g kappa phi : ℝ) (B : Fin 3 → ℝ) : Fin 3 → ℝ :=
  gibbonsWellsPermittivity g kappa phi • B

/-- Local electromagnetic energy density `½(E·D+B·H)` of the dilaton medium. -/
noncomputable def gibbonsWellsElectromagneticEnergyDensity
    (g kappa phi : ℝ) (E B : Fin 3 → ℝ) : ℝ :=
  (E ⬝ᵥ gibbonsWellsElectricDisplacement g kappa phi E +
    B ⬝ᵥ gibbonsWellsMagneticIntensity g kappa phi B) / 2

/-- The constitutive energy is the positive exponential times the Euclidean
electric-plus-magnetic square. -/
theorem gibbonsWellsElectromagneticEnergyDensity_eq
    (g kappa phi : ℝ) (E B : Fin 3 → ℝ) :
    gibbonsWellsElectromagneticEnergyDensity g kappa phi E B =
      gibbonsWellsPermittivity g kappa phi / 2 *
        ((∑ i, E i ^ 2) + ∑ i, B i ^ 2) := by
  simp only [gibbonsWellsElectromagneticEnergyDensity,
    gibbonsWellsElectricDisplacement, gibbonsWellsMagneticIntensity,
    Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_three]
  ring

/-- The dilaton electromagnetic energy density is nonnegative pointwise. -/
theorem gibbonsWellsElectromagneticEnergyDensity_nonneg
    (g kappa phi : ℝ) (E B : Fin 3 → ℝ) :
    0 ≤ gibbonsWellsElectromagneticEnergyDensity g kappa phi E B := by
  rw [gibbonsWellsElectromagneticEnergyDensity_eq]
  exact mul_nonneg (div_nonneg (le_of_lt (Real.exp_pos _)) (by norm_num))
    (add_nonneg
      (Finset.sum_nonneg fun i _ => sq_nonneg (E i))
      (Finset.sum_nonneg fun i _ => sq_nonneg (B i)))

/-- The four-dimensional mass of the projected five-dimensional null ray, `m=e/κ`
(Eq. (3.8)). -/
noncomputable def gibbonsWellsProbeMass (e kappa : ℝ) : ℝ := e / kappa

/-- The electric charge of the projected ray, `q=se` (Eq. (3.9)). -/
def gibbonsWellsProbeCharge (s e : ℝ) : ℝ := s * e

/-- The Kaluza–Klein projection fixes the charge-to-mass ratio:
`q/m=(se)/(e/κ)=sκ`. -/
theorem gibbonsWells_probe_chargeToMass
    (s e kappa : ℝ) (he : e ≠ 0) (hkappa : kappa ≠ 0) :
    gibbonsWellsProbeCharge s e / gibbonsWellsProbeMass e kappa = s * kappa := by
  unfold gibbonsWellsProbeCharge gibbonsWellsProbeMass
  field_simp

/-- The scalar-dressed projected mass `m exp(χ-ν)` read from the reduced
Hamilton–Jacobi equation (3.5). -/
noncomputable def gibbonsWellsScalarDressedMass
    (e kappa chi nu : ℝ) : ℝ :=
  gibbonsWellsProbeMass e kappa * Real.exp (chi - nu)

/-- Positive fifth momentum and positive `κ` give a positive scalar-dressed mass. -/
theorem gibbonsWellsScalarDressedMass_pos
    (e kappa chi nu : ℝ) (he : 0 < e) (hkappa : 0 < kappa) :
    0 < gibbonsWellsScalarDressedMass e kappa chi nu := by
  unfold gibbonsWellsScalarDressedMass gibbonsWellsProbeMass
  exact mul_pos (div_pos he hkappa) (Real.exp_pos _)

/-- The projected electromagnetic force obtained from the five-dimensional ray:
`(q/m) F·V`. -/
noncomputable def gibbonsWellsProbeLorentzForce
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ)
    (s e kappa : ℝ) : Fin 4 → ℝ :=
  (gibbonsWellsProbeCharge s e / gibbonsWellsProbeMass e kappa) • (F *ᵥ V)

/-- Substituting Eqs. (3.8)–(3.9) derives the projected Lorentz coefficient `sκ`. -/
theorem gibbonsWellsProbeLorentzForce_eq
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ)
    (s e kappa : ℝ) (he : e ≠ 0) (hkappa : kappa ≠ 0) :
    gibbonsWellsProbeLorentzForce F V s e kappa = (s * kappa) • (F *ᵥ V) := by
  unfold gibbonsWellsProbeLorentzForce
  rw [gibbonsWells_probe_chargeToMass s e kappa he hkappa]

/-- The projected Lorentz force is orthogonal to the four-velocity for an
antisymmetric field strength. -/
theorem gibbonsWellsProbeLorentzForce_no_work
    (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = -F j i)
    (V : Fin 4 → ℝ) (s e kappa : ℝ) (he : e ≠ 0) (hkappa : kappa ≠ 0) :
    V ⬝ᵥ gibbonsWellsProbeLorentzForce F V s e kappa = 0 := by
  rw [gibbonsWellsProbeLorentzForce_eq F V s e kappa he hkappa,
    dotProduct_smul, smul_eq_mul, antisym_no_work F hF V, mul_zero]

/-- Scalar-coupled projected force: the Lorentz term plus the force generated by
the position-dependent dressed mass. -/
noncomputable def gibbonsWellsProjectedForce
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V scalarForce : Fin 4 → ℝ)
    (s e kappa : ℝ) : Fin 4 → ℝ :=
  gibbonsWellsProbeLorentzForce F V s e kappa + scalarForce

/-- In the projected force law, electromagnetic work vanishes; all change of the
scalar-dressed rest energy is carried by the scalar-force channel. -/
theorem gibbonsWellsProjectedForce_power_eq_scalar
    (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = -F j i)
    (V scalarForce : Fin 4 → ℝ) (s e kappa : ℝ)
    (he : e ≠ 0) (hkappa : kappa ≠ 0) :
    V ⬝ᵥ gibbonsWellsProjectedForce F V scalarForce s e kappa =
      V ⬝ᵥ scalarForce := by
  unfold gibbonsWellsProjectedForce
  rw [dotProduct_add,
    gibbonsWellsProbeLorentzForce_no_work F hF V s e kappa he hkappa, zero_add]

/-- Gauge-covariant four-momentum `p-qA` in the reduced Hamilton–Jacobi
equation (3.5), with the projected charge `q=se`. -/
def gibbonsWellsKineticMomentum
    (p A : Fin 4 → ℝ) (s e : ℝ) : Fin 4 → ℝ :=
  p - gibbonsWellsProbeCharge s e • A

/-- Simultaneously shifting `A ↦ A+dΛ` and canonical momentum
`p ↦ p+q dΛ` leaves the reduced kinetic momentum invariant. -/
theorem gibbonsWellsKineticMomentum_gaugeInvariant
    (p A dLambda : Fin 4 → ℝ) (s e : ℝ) :
    gibbonsWellsKineticMomentum
        (p + gibbonsWellsProbeCharge s e • dLambda) (A + dLambda) s e =
      gibbonsWellsKineticMomentum p A s e := by
  ext i
  simp [gibbonsWellsKineticMomentum]

/-- The scalar-dressed, minimally coupled four-dimensional Hamilton–Jacobi
normal form obtained after fixing the fifth momentum. The inverse metric is an
explicit parameter, so this definition does not pretend to construct a spacetime
metric or solve the Hamilton–Jacobi PDE. -/
noncomputable def gibbonsWellsReducedHamiltonJacobi
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A : Fin 4 → ℝ)
    (s e kappa chi nu : ℝ) : ℝ :=
  let pi := gibbonsWellsKineticMomentum p A s e
  pi ⬝ᵥ (gInv *ᵥ pi) +
    gibbonsWellsScalarDressedMass e kappa chi nu ^ 2

/-- Gauge covariance of the complete reduced Hamilton–Jacobi normal form. -/
theorem gibbonsWellsReducedHamiltonJacobi_gaugeInvariant
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A dLambda : Fin 4 → ℝ)
    (s e kappa chi nu : ℝ) :
    gibbonsWellsReducedHamiltonJacobi gInv
        (p + gibbonsWellsProbeCharge s e • dLambda) (A + dLambda)
        s e kappa chi nu =
      gibbonsWellsReducedHamiltonJacobi gInv p A s e kappa chi nu := by
  unfold gibbonsWellsReducedHamiltonJacobi
  rw [gibbonsWellsKineticMomentum_gaugeInvariant]

/-- The horizontal part of a general five-dimensional covector in the dual
frame of the twisted metric (3.1):
`pμ - sκ p₅ Aμ`. Fixing `p₅=e/κ` recovers `pμ-seAμ`. -/
def gibbonsWellsFiveHorizontalMomentum
    (p A : Fin 4 → ℝ) (p5 s kappa : ℝ) : Fin 4 → ℝ :=
  p - (s * kappa * p5) • A

/-- The Kaluza–Klein gauge transformation simultaneously changes
`A ↦ A+dΛ` and `p ↦ p+sκp₅dΛ`; the horizontal covector is invariant. -/
theorem gibbonsWellsFiveHorizontalMomentum_gaugeInvariant
    (p A dLambda : Fin 4 → ℝ) (p5 s kappa : ℝ) :
    gibbonsWellsFiveHorizontalMomentum
        (p + (s * kappa * p5) • dLambda) (A + dLambda) p5 s kappa =
      gibbonsWellsFiveHorizontalMomentum p A p5 s kappa := by
  ext i
  simp [gibbonsWellsFiveHorizontalMomentum]

/-- The twisted fibre coframe of the covariant five-metric (3.1):
`θ⁵(v)=v⁵+sκ Aμvμ`. -/
def gibbonsWellsTwistedFiberOneForm
    (A v : Fin 4 → ℝ) (v5 s kappa : ℝ) : ℝ :=
  v5 + s * kappa * (A ⬝ᵥ v)

/-- A Kaluza–Klein gauge shift `A ↦ A+dΛ` accompanied by the fibre-coordinate
shift `v⁵ ↦ v⁵-sκ dΛ(v)` leaves the twisted coframe invariant. -/
theorem gibbonsWellsTwistedFiberOneForm_gaugeInvariant
    (A dLambda v : Fin 4 → ℝ) (v5 s kappa : ℝ) :
    gibbonsWellsTwistedFiberOneForm (A + dLambda) v
        (v5 - s * kappa * (dLambda ⬝ᵥ v)) s kappa =
      gibbonsWellsTwistedFiberOneForm A v v5 s kappa := by
  simp [gibbonsWellsTwistedFiberOneForm, add_dotProduct]
  ring

/-- The covariant five-dimensional metric quadratic of Eq. (3.1):
`e²ν θ⁵(v)² + e²χ g(v,v)`.

This is the exact coordinate normal form; `g` remains the supplied
four-dimensional metric matrix, so no separate global atlas is postulated. -/
noncomputable def gibbonsWellsFiveMetricQuadratic
    (g : Matrix (Fin 4) (Fin 4) ℝ) (A v : Fin 4 → ℝ)
    (v5 s kappa nu chi : ℝ) : ℝ :=
  Real.exp (2 * nu) *
      gibbonsWellsTwistedFiberOneForm A v v5 s kappa ^ 2 +
    Real.exp (2 * chi) * (v ⬝ᵥ (g *ᵥ v))

/-- The complete covariant metric quadratic is invariant under the compensated
Kaluza–Klein gauge transformation. -/
theorem gibbonsWellsFiveMetricQuadratic_gaugeInvariant
    (g : Matrix (Fin 4) (Fin 4) ℝ) (A dLambda v : Fin 4 → ℝ)
    (v5 s kappa nu chi : ℝ) :
    gibbonsWellsFiveMetricQuadratic g (A + dLambda) v
        (v5 - s * kappa * (dLambda ⬝ᵥ v)) s kappa nu chi =
      gibbonsWellsFiveMetricQuadratic g A v v5 s kappa nu chi := by
  unfold gibbonsWellsFiveMetricQuadratic
  rw [gibbonsWellsTwistedFiberOneForm_gaugeInvariant]

/-- Natural pairing of a five-covector `(pμ,p₅)` with a five-vector
`(vμ,v⁵)`. -/
def gibbonsWellsFiveCovectorVectorPairing
    (p v : Fin 4 → ℝ) (p5 v5 : ℝ) : ℝ :=
  p ⬝ᵥ v + p5 * v5

/-- The horizontal covector `pμ-sκp₅Aμ` and twisted coframe
`v⁵+sκAμvμ` are exactly dual: their cross terms cancel in the canonical
five-dimensional pairing. This supplies the covariant/contravariant bridge
underlying the Hamilton–Jacobi normal form. -/
theorem gibbonsWells_horizontal_twisted_dual_pairing
    (p A v : Fin 4 → ℝ) (p5 v5 s kappa : ℝ) :
    gibbonsWellsFiveCovectorVectorPairing p v p5 v5 =
      gibbonsWellsFiveHorizontalMomentum p A p5 s kappa ⬝ᵥ v +
        p5 * gibbonsWellsTwistedFiberOneForm A v v5 s kappa := by
  simp [gibbonsWellsFiveCovectorVectorPairing,
    gibbonsWellsFiveHorizontalMomentum, gibbonsWellsTwistedFiberOneForm,
    sub_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

/-- Fixing the conserved fifth momentum to `p₅=e/κ` gives the physical
four-dimensional minimally coupled momentum `p-seA`. -/
theorem gibbonsWellsFiveHorizontalMomentum_fixed
    (p A : Fin 4 → ℝ) (s e kappa : ℝ) (hkappa : kappa ≠ 0) :
    gibbonsWellsFiveHorizontalMomentum p A
        (gibbonsWellsProbeMass e kappa) s kappa =
      gibbonsWellsKineticMomentum p A s e := by
  have hcoef : s * kappa * gibbonsWellsProbeMass e kappa =
      gibbonsWellsProbeCharge s e := by
    unfold gibbonsWellsProbeMass gibbonsWellsProbeCharge
    field_simp
  unfold gibbonsWellsFiveHorizontalMomentum gibbonsWellsKineticMomentum
  rw [hcoef]

/-- The contravariant quadratic of the inverse five-dimensional twisted metric
(3.1), expressed in its dual frame:
`e⁻²ν p₅² + e⁻²χ g⁻¹(p-sκp₅A,p-sκp₅A)`.
This is the exact inverse-metric normal form needed by the Hamilton–Jacobi
equation, without duplicating the repository's global metric infrastructure. -/
noncomputable def gibbonsWellsFiveHamiltonJacobi
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A : Fin 4 → ℝ)
    (p5 s kappa nu chi : ℝ) : ℝ :=
  let pi := gibbonsWellsFiveHorizontalMomentum p A p5 s kappa
  Real.exp (-2 * nu) * p5 ^ 2 +
    Real.exp (-2 * chi) * (pi ⬝ᵥ (gInv *ᵥ pi))

/-- The warp factors in the scalar-dressed rest-mass term cancel exactly:
`e⁻²χ [m e^(χ-ν)]² = e⁻²ν m²`. -/
theorem gibbonsWellsScalarDressedMass_warpCancellation
    (e kappa chi nu : ℝ) :
    Real.exp (-2 * chi) *
        gibbonsWellsScalarDressedMass e kappa chi nu ^ 2 =
      Real.exp (-2 * nu) * gibbonsWellsProbeMass e kappa ^ 2 := by
  have hexpSq :
      Real.exp (chi - nu) ^ 2 = Real.exp (2 * (chi - nu)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold gibbonsWellsScalarDressedMass
  rw [mul_pow, hexpSq]
  calc
    Real.exp (-2 * chi) *
        (gibbonsWellsProbeMass e kappa ^ 2 *
          Real.exp (2 * (chi - nu))) =
        gibbonsWellsProbeMass e kappa ^ 2 *
          (Real.exp (-2 * chi) * Real.exp (2 * (chi - nu))) := by ring
    _ = gibbonsWellsProbeMass e kappa ^ 2 * Real.exp (-2 * nu) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = Real.exp (-2 * nu) * gibbonsWellsProbeMass e kappa ^ 2 := by ring

/-- **Equations (3.3)–(3.5).** Substituting the conserved fifth momentum
`p₅=e/κ` into the exact inverse-metric quadratic gives `e⁻²χ` times the
four-dimensional scalar-dressed Hamilton–Jacobi expression. -/
theorem gibbonsWellsFiveHamiltonJacobi_fixed_eq_reduced
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A : Fin 4 → ℝ)
    (s e kappa nu chi : ℝ) (hkappa : kappa ≠ 0) :
    gibbonsWellsFiveHamiltonJacobi gInv p A
        (gibbonsWellsProbeMass e kappa) s kappa nu chi =
      Real.exp (-2 * chi) *
        gibbonsWellsReducedHamiltonJacobi gInv p A s e kappa chi nu := by
  unfold gibbonsWellsFiveHamiltonJacobi gibbonsWellsReducedHamiltonJacobi
  rw [gibbonsWellsFiveHorizontalMomentum_fixed p A s e kappa hkappa]
  dsimp only
  have hwarp :=
    gibbonsWellsScalarDressedMass_warpCancellation e kappa chi nu
  calc
    Real.exp (-2 * nu) * gibbonsWellsProbeMass e kappa ^ 2 +
        Real.exp (-2 * chi) *
          (gibbonsWellsKineticMomentum p A s e ⬝ᵥ
            (gInv *ᵥ gibbonsWellsKineticMomentum p A s e)) =
        Real.exp (-2 * chi) *
            gibbonsWellsScalarDressedMass e kappa chi nu ^ 2 +
          Real.exp (-2 * chi) *
            (gibbonsWellsKineticMomentum p A s e ⬝ᵥ
              (gInv *ᵥ gibbonsWellsKineticMomentum p A s e)) := by
                rw [hwarp]
    _ = Real.exp (-2 * chi) *
        (gibbonsWellsKineticMomentum p A s e ⬝ᵥ
            (gInv *ᵥ gibbonsWellsKineticMomentum p A s e) +
          gibbonsWellsScalarDressedMass e kappa chi nu ^ 2) := by ring

/-- The five-dimensional null Hamilton–Jacobi equation is equivalent to the
four-dimensional massive, charged, scalar-dressed equation because the warp
factor `e⁻²χ` never vanishes. -/
theorem gibbonsWellsFiveHamiltonJacobi_null_iff_reduced
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A : Fin 4 → ℝ)
    (s e kappa nu chi : ℝ) (hkappa : kappa ≠ 0) :
    gibbonsWellsFiveHamiltonJacobi gInv p A
        (gibbonsWellsProbeMass e kappa) s kappa nu chi = 0 ↔
      gibbonsWellsReducedHamiltonJacobi gInv p A s e kappa chi nu = 0 := by
  rw [gibbonsWellsFiveHamiltonJacobi_fixed_eq_reduced
    gInv p A s e kappa nu chi hkappa]
  exact mul_eq_zero.trans (or_iff_right (ne_of_gt (Real.exp_pos _)))

/-- The projected four-velocity from the inverse metric, Eq. (3.7). -/
noncomputable def gibbonsWellsProjectedVelocity
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A : Fin 4 → ℝ)
    (p5 s kappa chi : ℝ) : Fin 4 → ℝ :=
  Real.exp (-2 * chi) •
    (gInv *ᵥ gibbonsWellsFiveHorizontalMomentum p A p5 s kappa)

/-- The fifth velocity from the inverse metric, Eq. (3.6). -/
noncomputable def gibbonsWellsFifthVelocity
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A : Fin 4 → ℝ)
    (p5 s kappa nu chi : ℝ) : ℝ :=
  Real.exp (-2 * nu) * p5 -
    s * kappa *
      (A ⬝ᵥ gibbonsWellsProjectedVelocity gInv p A p5 s kappa chi)

/-- The projected velocity is invariant under the lifted Kaluza–Klein gauge
transformation. -/
theorem gibbonsWellsProjectedVelocity_gaugeInvariant
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A dLambda : Fin 4 → ℝ)
    (p5 s kappa chi : ℝ) :
    gibbonsWellsProjectedVelocity gInv
        (p + (s * kappa * p5) • dLambda) (A + dLambda)
        p5 s kappa chi =
      gibbonsWellsProjectedVelocity gInv p A p5 s kappa chi := by
  unfold gibbonsWellsProjectedVelocity
  rw [gibbonsWellsFiveHorizontalMomentum_gaugeInvariant]

/-- The fifth velocity transforms by precisely the compensating fibre-coordinate
term, while its four-dimensional projection stays fixed. -/
theorem gibbonsWellsFifthVelocity_gaugeCovariant
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A dLambda : Fin 4 → ℝ)
    (p5 s kappa nu chi : ℝ) :
    gibbonsWellsFifthVelocity gInv
        (p + (s * kappa * p5) • dLambda) (A + dLambda)
        p5 s kappa nu chi =
      gibbonsWellsFifthVelocity gInv p A p5 s kappa nu chi -
        s * kappa *
          (dLambda ⬝ᵥ gibbonsWellsProjectedVelocity
            gInv p A p5 s kappa chi) := by
  unfold gibbonsWellsFifthVelocity
  rw [gibbonsWellsProjectedVelocity_gaugeInvariant]
  rw [add_dotProduct]
  ring

/-- The velocity formulas invert the fibre block of the metric:
`e²ν (v⁵+sκ A·v)=p₅`. This is the conserved fifth momentum used in
Eqs. (3.4)–(3.9). -/
theorem gibbonsWellsFifthVelocity_recovers_fiberMomentum
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A : Fin 4 → ℝ)
    (p5 s kappa nu chi : ℝ) :
    Real.exp (2 * nu) *
        (gibbonsWellsFifthVelocity gInv p A p5 s kappa nu chi +
          s * kappa *
            (A ⬝ᵥ gibbonsWellsProjectedVelocity
              gInv p A p5 s kappa chi)) = p5 := by
  unfold gibbonsWellsFifthVelocity
  have hexp : Real.exp (2 * nu) * Real.exp (-2 * nu) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    Real.exp (2 * nu) *
        (Real.exp (-2 * nu) * p5 -
            s * kappa *
              (A ⬝ᵥ gibbonsWellsProjectedVelocity
                gInv p A p5 s kappa chi) +
          s * kappa *
            (A ⬝ᵥ gibbonsWellsProjectedVelocity
              gInv p A p5 s kappa chi)) =
        (Real.exp (2 * nu) * Real.exp (-2 * nu)) * p5 := by ring
    _ = p5 := by rw [hexp, one_mul]


/-! ## H. The reduced five-dimensional null-Ricci contraction -/

/-- The complete source contribution in the reduced null-Ricci contraction (the
last line of Eq. (5.4)). `matter` is the trace-reversed matter contraction and
`current` is `V·J`. -/
noncomputable def gibbonsWellsNullRicciSourceContribution
    (kappa nu g s V5 scalarSource matter current : ℝ) : ℝ :=
  2 * kappa ^ 2 * Real.exp (2 * nu) * matter +
    V5 ^ 2 * Real.exp nu * g * scalarSource / 3 +
    s * kappa * V5 * current

/-- The source conditions (5.8)–(5.9), at the scalar level needed by Eq. (5.4),
say that the complete source contribution is nonnegative. -/
def GibbonsWellsNullRicciSourceCondition
    (kappa nu g s V5 scalarSource matter current : ℝ) : Prop :=
  0 ≤ gibbonsWellsNullRicciSourceContribution
    kappa nu g s V5 scalarSource matter current

/-- The reduced five-dimensional null-Ricci contraction, Eq. (5.4), after the
field equations and the warp choices `3ν=2gκφ`, `ν+2χ=0` have removed all
uncontrolled second derivatives. -/
noncomputable def gibbonsWellsReducedNullRicci
    (kappa nu g s V5 dilatonDerivativeSq magneticBH electricED
      scalarSource matter current : ℝ) : ℝ :=
  2 * kappa ^ 2 * Real.exp (2 * nu) * (1 - g ^ 2 / 3) * dilatonDerivativeSq +
    kappa ^ 2 * Real.exp (2 * nu) * V5 ^ 2 *
      ((1 - g ^ 2 + s ^ 2 / 2) * magneticBH +
        (1 + g ^ 2 - s ^ 2) * electricED) +
    gibbonsWellsNullRicciSourceContribution
      kappa nu g s V5 scalarSource matter current

/-- **Null convergence from the paper's coefficient and source conditions.** If
the scalar derivative square, `B·H`, and `E·D` are nonnegative, the coupling
region (5.7) makes every field coefficient nonnegative; a nonnegative source
block then proves the complete reduced contraction is nonnegative. -/
theorem gibbonsWells_reducedNullRicci_nonneg
    (kappa nu g s V5 dilatonDerivativeSq magneticBH electricED
      scalarSource matter current : ℝ)
    (hcoupling : GibbonsWellsNullConvergenceCouplings g s)
    (hdilaton : 0 ≤ dilatonDerivativeSq)
    (hmagnetic : 0 ≤ magneticBH) (helectric : 0 ≤ electricED)
    (hsource : GibbonsWellsNullRicciSourceCondition
      kappa nu g s V5 scalarSource matter current) :
    0 ≤ gibbonsWellsReducedNullRicci kappa nu g s V5
      dilatonDerivativeSq magneticBH electricED scalarSource matter current := by
  rcases hcoupling with ⟨hg, hmagCoeff, helecCoeff⟩
  have hdilCoeff : 0 ≤ 1 - g ^ 2 / 3 := by nlinarith
  have hmagCoeff' : 0 ≤ 1 - g ^ 2 + s ^ 2 / 2 := by nlinarith
  have helecCoeff' : 0 ≤ 1 + g ^ 2 - s ^ 2 := by nlinarith
  have hprefDil : 0 ≤ 2 * kappa ^ 2 * Real.exp (2 * nu) := by positivity
  have hprefEM : 0 ≤ kappa ^ 2 * Real.exp (2 * nu) * V5 ^ 2 := by positivity
  have hdilTerm : 0 ≤
      2 * kappa ^ 2 * Real.exp (2 * nu) *
        (1 - g ^ 2 / 3) * dilatonDerivativeSq :=
    mul_nonneg (mul_nonneg hprefDil hdilCoeff) hdilaton
  have hemInner : 0 ≤
      (1 - g ^ 2 + s ^ 2 / 2) * magneticBH +
        (1 + g ^ 2 - s ^ 2) * electricED :=
    add_nonneg (mul_nonneg hmagCoeff' hmagnetic)
      (mul_nonneg helecCoeff' helectric)
  unfold GibbonsWellsNullRicciSourceCondition at hsource
  unfold gibbonsWellsReducedNullRicci
  exact add_nonneg (add_nonneg hdilTerm (mul_nonneg hprefEM hemInner)) hsource

/-- At the vacuum Kaluza–Klein endpoint `g²=3, s=2`, every field coefficient
in the reduced null-Ricci contraction vanishes, reproducing the null contraction
of the paper's `⁵R_AB=0` check (Eqs. (4.11)–(4.13)). This is the contracted
statement, not an equality of all five-dimensional tensor components. -/
theorem gibbonsWells_reducedNullRicci_kaluzaKlein_vacuum
    (kappa nu g V5 dilatonDerivativeSq magneticBH electricED : ℝ)
    (hg : g ^ 2 = 3) :
    gibbonsWellsReducedNullRicci kappa nu g 2 V5
      dilatonDerivativeSq magneticBH electricED 0 0 0 = 0 := by
  unfold gibbonsWellsReducedNullRicci gibbonsWellsNullRicciSourceContribution
  rw [hg]
  norm_num

/-- The reduced mixed Ricci component `⁵R_{α5}` of Eq. (4.8), for one
orthonormal-frame current component `Jα`. -/
noncomputable def gibbonsWellsReducedMixedRicciComponent
    (kappa nu s currentComponent : ℝ) : ℝ :=
  s * kappa * Real.exp (-nu) * currentComponent / 2

/-- The reduced fibre Ricci component `⁵R_{55}` of Eq. (4.9). -/
noncomputable def gibbonsWellsReducedFiberRicciComponent
    (kappa nu g s faradaySq scalarSource : ℝ) : ℝ :=
  kappa ^ 2 * Real.exp (4 * nu) * faradaySq *
      (s ^ 2 / 4 - g ^ 2 / 3) +
    (2 * g * kappa ^ 2 / 3) * Real.exp nu * scalarSource

/-- One reduced base Ricci component `⁵R_{μν}` of Eq. (4.10).

The scalar arguments respectively represent
`∂μφ ∂νφ`, `F_{μβ}F_ν{}^β`, `g_{μν}F²`, and the trace-reversed
matter component. Keeping those contractions explicit avoids duplicating the
repository's global tensor implementation. -/
noncomputable def gibbonsWellsReducedBaseRicciComponent
    (kappa nu g s dilatonGradProduct faradayContraction
      metricFaradaySq traceReversedMatter : ℝ) : ℝ :=
  2 * kappa ^ 2 * (1 - g ^ 2 / 3) * dilatonGradProduct +
    2 * kappa ^ 2 * Real.exp (3 * nu) *
      (faradayContraction - metricFaradaySq / 4) -
    s ^ 2 * kappa ^ 2 * Real.exp (3 * nu) * faradayContraction / 2 +
    g ^ 2 * kappa ^ 2 * Real.exp (3 * nu) * metricFaradaySq / 6 +
    2 * kappa ^ 2 * traceReversedMatter

/-- The three reduced orthonormal-frame Ricci sectors used by the paper. -/
@[ext] structure GibbonsWellsReducedRicciComponents where
  /-- `⁵R_{α5}` for a selected base component. -/
  mixed : ℝ
  /-- `⁵R_{55}`. -/
  fiber : ℝ
  /-- `⁵R_{μν}` for a selected base pair. -/
  base : ℝ

/-- Assemble Eqs. (4.8)–(4.10) into one componentwise carrier. -/
noncomputable def gibbonsWellsReducedRicciComponents
    (kappa nu g s currentComponent faradaySq scalarSource
      dilatonGradProduct faradayContraction metricFaradaySq
      traceReversedMatter : ℝ) : GibbonsWellsReducedRicciComponents where
  mixed :=
    gibbonsWellsReducedMixedRicciComponent kappa nu s currentComponent
  fiber :=
    gibbonsWellsReducedFiberRicciComponent
      kappa nu g s faradaySq scalarSource
  base :=
    gibbonsWellsReducedBaseRicciComponent kappa nu g s
      dilatonGradProduct faradayContraction metricFaradaySq
      traceReversedMatter

/-- At the standard Kaluza–Klein endpoint `g²=3`, `s=2`, the mixed
component vanishes when the vector current vanishes. -/
theorem gibbonsWells_reducedMixedRicci_kaluzaKlein_vacuum
    (kappa nu : ℝ) :
    gibbonsWellsReducedMixedRicciComponent kappa nu 2 0 = 0 := by
  simp [gibbonsWellsReducedMixedRicciComponent]

/-- At `g²=3`, `s=2`, the fibre component vanishes when the scalar
source vanishes, independently of `F²`. -/
theorem gibbonsWells_reducedFiberRicci_kaluzaKlein_vacuum
    (kappa nu g faradaySq : ℝ) (hg : g ^ 2 = 3) :
    gibbonsWellsReducedFiberRicciComponent
      kappa nu g 2 faradaySq 0 = 0 := by
  unfold gibbonsWellsReducedFiberRicciComponent
  rw [hg]
  norm_num

/-- At `g²=3`, `s=2`, all dilaton and Maxwell terms in the base
component cancel; it vanishes in source-free vacuum. -/
theorem gibbonsWells_reducedBaseRicci_kaluzaKlein_vacuum
    (kappa nu g dilatonGradProduct faradayContraction metricFaradaySq : ℝ)
    (hg : g ^ 2 = 3) :
    gibbonsWellsReducedBaseRicciComponent kappa nu g 2
      dilatonGradProduct faradayContraction metricFaradaySq 0 = 0 := by
  unfold gibbonsWellsReducedBaseRicciComponent
  rw [hg]
  norm_num
  ring

/-- Componentwise form of the paper's Kaluza–Klein vacuum check
`⁵R_{AB}=0` (Eqs. (4.11)–(4.13)), at the level of all three reduced
orthonormal-frame sectors. -/
theorem gibbonsWells_reducedRicciComponents_kaluzaKlein_vacuum
    (kappa nu g faradaySq dilatonGradProduct faradayContraction
      metricFaradaySq : ℝ) (hg : g ^ 2 = 3) :
    gibbonsWellsReducedRicciComponents kappa nu g 2
      0 faradaySq 0 dilatonGradProduct faradayContraction
      metricFaradaySq 0 =
        { mixed := 0, fiber := 0, base := 0 } := by
  apply GibbonsWellsReducedRicciComponents.ext <;>
    simp [gibbonsWellsReducedRicciComponents,
      gibbonsWells_reducedMixedRicci_kaluzaKlein_vacuum,
      gibbonsWells_reducedFiberRicci_kaluzaKlein_vacuum kappa nu g faradaySq hg,
      gibbonsWells_reducedBaseRicci_kaluzaKlein_vacuum
        kappa nu g dilatonGradProduct faradayContraction metricFaradaySq hg]

/-- Explicit sufficient source inequalities strengthening Eqs. (5.8)–(5.9):
`g≥0`, scalar source `J≥0`, and the trace-reversed matter contribution
dominates the **absolute value** of the projected vector-current term.

The absolute-value form is deliberately stronger than the paper's directed
inequality, but it is sign-independent and directly sufficient for every
chosen null orientation. -/
structure GibbonsWellsExplicitSourceConditions
    (kappa nu g s V5 scalarSource matter current : ℝ) : Prop where
  /-- Nonnegative dilaton coupling convention. -/
  coupling_nonneg : 0 ≤ g
  /-- Eq. (5.8), `J≥0`. -/
  scalarSource_nonneg : 0 ≤ scalarSource
  /-- Strong scalar form of Eq. (5.9). -/
  matter_dominates_current :
    |s * kappa * V5 * current| ≤
      2 * kappa ^ 2 * Real.exp (2 * nu) * matter

/-- The explicit source inequalities imply nonnegativity of the complete
source block in Eq. (5.4). -/
theorem gibbonsWells_explicitSources_imply_sourceCondition
    (kappa nu g s V5 scalarSource matter current : ℝ)
    (h : GibbonsWellsExplicitSourceConditions
      kappa nu g s V5 scalarSource matter current) :
    GibbonsWellsNullRicciSourceCondition
      kappa nu g s V5 scalarSource matter current := by
  unfold GibbonsWellsNullRicciSourceCondition
  unfold gibbonsWellsNullRicciSourceContribution
  have hcurrent :
      -(2 * kappa ^ 2 * Real.exp (2 * nu) * matter) ≤
        s * kappa * V5 * current :=
    le_trans (neg_le_neg h.matter_dominates_current)
      (neg_abs_le (s * kappa * V5 * current))
  have hscalar :
      0 ≤ V5 ^ 2 * Real.exp nu * g * scalarSource / 3 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg V5) (le_of_lt (Real.exp_pos nu)))
          h.coupling_nonneg)
        h.scalarSource_nonneg)
      (by norm_num)
  nlinarith

/-- The paper's coupling region, nonnegative field squares, and the explicit
source inequalities together imply the complete reduced null convergence
condition. -/
theorem gibbonsWells_reducedNullRicci_nonneg_of_explicitSources
    (kappa nu g s V5 dilatonDerivativeSq magneticBH electricED
      scalarSource matter current : ℝ)
    (hcoupling : GibbonsWellsNullConvergenceCouplings g s)
    (hdilaton : 0 ≤ dilatonDerivativeSq)
    (hmagnetic : 0 ≤ magneticBH) (helectric : 0 ≤ electricED)
    (hsources : GibbonsWellsExplicitSourceConditions
      kappa nu g s V5 scalarSource matter current) :
    0 ≤ gibbonsWellsReducedNullRicci kappa nu g s V5
      dilatonDerivativeSq magneticBH electricED
      scalarSource matter current :=
  gibbonsWells_reducedNullRicci_nonneg
    kappa nu g s V5 dilatonDerivativeSq magneticBH electricED
    scalarSource matter current hcoupling hdilaton hmagnetic helectric
    (gibbonsWells_explicitSources_imply_sourceCondition
      kappa nu g s V5 scalarSource matter current hsources)


/-! ## I. The projected Lorentz force in the existing BCJ double copy -/

/-- A component of the projected Gibbons–Wells Lorentz force, used as a BCJ
kinematic numerator. -/
noncomputable def gibbonsWellsProbeLorentzForceNum
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (mu : Fin 4)
    (s e kappa : ℝ) : ℝ :=
  gibbonsWellsProbeLorentzForce F V s e kappa mu

/-- The projected force numerator is `sκ` times the repository's bare Lorentz
numerator. -/
theorem gibbonsWellsProbeLorentzForceNum_eq
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (mu : Fin 4)
    (s e kappa : ℝ) (he : e ≠ 0) (hkappa : kappa ≠ 0) :
    gibbonsWellsProbeLorentzForceNum F V mu s e kappa =
      (s * kappa) * lorentzForceNum F V mu := by
  unfold gibbonsWellsProbeLorentzForceNum lorentzForceNum
  rw [gibbonsWellsProbeLorentzForce_eq F V s e kappa he hkappa]
  simp [Pi.smul_apply]

/-- The diagonal BCJ double copy of the projected Lorentz-force numerator. -/
noncomputable def gibbonsWellsProbeLorentzForceDual
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (mu : Fin 4)
    (s e kappa D : ℝ) : ℝ :=
  gibbonsWellsProbeLorentzForceNum F V mu s e kappa ^ 2 / D

/-- Coupling factorization: the projected double copy is `(sκ)²` times the
existing Lorentz-force double copy. -/
theorem gibbonsWellsProbeLorentzForceDual_eq
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (mu : Fin 4)
    (s e kappa D : ℝ) (he : e ≠ 0) (hkappa : kappa ≠ 0) :
    gibbonsWellsProbeLorentzForceDual F V mu s e kappa D =
      (s * kappa) ^ 2 * lorentzForceDual F V mu D := by
  unfold gibbonsWellsProbeLorentzForceDual lorentzForceDual
  rw [gibbonsWellsProbeLorentzForceNum_eq F V mu s e kappa he hkappa]
  ring

/-- The projected-force double copy is nonnegative for a positive propagator. -/
theorem gibbonsWellsProbeLorentzForceDual_nonneg
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (mu : Fin 4)
    (s e kappa D : ℝ) (he : e ≠ 0) (hkappa : kappa ≠ 0) (hD : 0 < D) :
    0 ≤ gibbonsWellsProbeLorentzForceDual F V mu s e kappa D := by
  rw [gibbonsWellsProbeLorentzForceDual_eq F V mu s e kappa D he hkappa]
  exact mul_nonneg (sq_nonneg _) (lorentzForceDual_nonneg F V mu D hD)

/-- Summing the squared projected BCJ numerators yields the quadratic form of the
existing operator-level curvature double copy `F²`, scaled by `(sκ)²`. Each
positive-propagator channel is obtained from this numerator identity by division by
its propagator (`gibbonsWellsProbeLorentzForceDual_eq`). -/
theorem gibbonsWellsProbeLorentzForceNum_sq_sum_eq_curvature
    (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = -F j i)
    (V : Fin 4 → ℝ) (s e kappa : ℝ)
    (he : e ≠ 0) (hkappa : kappa ≠ 0) :
    (∑ mu, gibbonsWellsProbeLorentzForceNum F V mu s e kappa ^ 2) =
      -(s * kappa) ^ 2 * (V ⬝ᵥ gravCurvatureGen F V) := by
  rw [gravCurvatureGen_quadratic_lorentz F hF V]
  simp_rw [gibbonsWellsProbeLorentzForceNum_eq F V _ s e kappa he hkappa, mul_pow]
  rw [← Finset.mul_sum]
  ring

/-- The complete algebraic five-to-four-dimensional probe closure. The same
fixed fifth momentum `p₅=e/κ` simultaneously:

1. becomes the minimally coupled momentum `p-seA`;
2. turns the five-dimensional null Hamilton–Jacobi equation into the
   scalar-dressed four-dimensional mass shell;
3. fixes the projected Lorentz coefficient to `sκ`; and
4. fixes its BCJ double-copy coefficient to `(sκ)²`.

This theorem composes exact reductions; it does not assert existence of a global
five-dimensional geodesic or a full gravitational scattering amplitude. -/
theorem gibbonsWells_fiveDimensional_probe_closure
    (gInv : Matrix (Fin 4) (Fin 4) ℝ) (p A : Fin 4 → ℝ)
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (mu : Fin 4)
    (s e kappa nu chi D : ℝ) (he : e ≠ 0) (hkappa : kappa ≠ 0) :
    gibbonsWellsFiveHorizontalMomentum p A
        (gibbonsWellsProbeMass e kappa) s kappa =
        gibbonsWellsKineticMomentum p A s e ∧
      (gibbonsWellsFiveHamiltonJacobi gInv p A
          (gibbonsWellsProbeMass e kappa) s kappa nu chi = 0 ↔
        gibbonsWellsReducedHamiltonJacobi
          gInv p A s e kappa chi nu = 0) ∧
      gibbonsWellsProbeLorentzForce F V s e kappa =
        (s * kappa) • (F *ᵥ V) ∧
      gibbonsWellsProbeLorentzForceDual F V mu s e kappa D =
        (s * kappa) ^ 2 * lorentzForceDual F V mu D := by
  exact ⟨gibbonsWellsFiveHorizontalMomentum_fixed p A s e kappa hkappa,
    gibbonsWellsFiveHamiltonJacobi_null_iff_reduced
      gInv p A s e kappa nu chi hkappa,
    gibbonsWellsProbeLorentzForce_eq F V s e kappa he hkappa,
    gibbonsWellsProbeLorentzForceDual_eq F V mu s e kappa D he hkappa⟩


/-! ## J. The linearized null-vector derivation of the bound -/

/-- The signed charge in gravitational units, `Q/√(4πG)`. Unlike
`gravitationallyNormalizedCharge`, this retains the sign needed by the two
linearized null directions. -/
noncomputable def signedGravitationallyNormalizedCharge (G Q : ℝ) : ℝ :=
  Q / Real.sqrt (4 * Real.pi * G)

/-- For positive Newton coupling, taking the absolute value of the signed
normalized charge recovers the paper's unsigned normalized charge. -/
theorem abs_signedGravitationallyNormalizedCharge
    (G Q : ℝ) (hG : 0 < G) :
    |signedGravitationallyNormalizedCharge G Q| =
      gravitationallyNormalizedCharge G Q := by
  have hden : 0 < Real.sqrt (4 * Real.pi * G) :=
    Real.sqrt_pos.2 (mul_pos (mul_pos (by norm_num) Real.pi_pos) hG)
  unfold signedGravitationallyNormalizedCharge gravitationallyNormalizedCharge
  rw [abs_div, abs_of_pos hden]

/-- The `(4,5)` block of the normalized asymptotic metric coefficient in
Eq. (8.9), with the irrelevant common positive factor `G` removed:
`[[2M+2gΣ/3, sQ̂], [sQ̂, 4gΣ/3]]`. -/
noncomputable def gibbonsWellsLinearizedAsymptoticBlock
    (M Sigma g s qHat : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * M + 2 * g * Sigma / 3, s * qHat;
     s * qHat,                     4 * g * Sigma / 3]

/-- The two constant null directions used below, `(1,sign)`. -/
def gibbonsWellsLinearizedNullVector (sign : ℝ) : Fin 2 → ℝ :=
  ![1, sign]

/-- Eq. (8.9) contracted with `(1,sign)`: for `sign²=1`, the result is
`2(M+gΣ+sign·sQ̂)`. -/
theorem gibbonsWells_linearized_null_contraction
    (M Sigma g s qHat sign : ℝ) (hsign : sign ^ 2 = 1) :
    gibbonsWellsLinearizedNullVector sign ⬝ᵥ
        (gibbonsWellsLinearizedAsymptoticBlock M Sigma g s qHat *ᵥ
          gibbonsWellsLinearizedNullVector sign) =
      2 * (gibbonsWellsEffectiveMass M Sigma g + sign * s * qHat) := by
  calc
    gibbonsWellsLinearizedNullVector sign ⬝ᵥ
        (gibbonsWellsLinearizedAsymptoticBlock M Sigma g s qHat *ᵥ
          gibbonsWellsLinearizedNullVector sign) =
        2 * (gibbonsWellsEffectiveMass M Sigma g + sign * s * qHat) +
          (4 * g * Sigma / 3) * (sign ^ 2 - 1) := by
            simp [gibbonsWellsLinearizedNullVector,
              gibbonsWellsLinearizedAsymptoticBlock,
              gibbonsWellsEffectiveMass, dotProduct, Fin.sum_univ_two]
            ring
    _ = 2 * (gibbonsWellsEffectiveMass M Sigma g + sign * s * qHat) := by
      rw [hsign]
      ring

/-- Linearized null nonnegativity for both constant null directions. -/
def GibbonsWellsLinearizedNullNonnegative
    (M Sigma g s qHat : ℝ) : Prop :=
  ∀ sign : ℝ, sign ^ 2 = 1 →
    0 ≤ gibbonsWellsLinearizedNullVector sign ⬝ᵥ
      (gibbonsWellsLinearizedAsymptoticBlock M Sigma g s qHat *ᵥ
        gibbonsWellsLinearizedNullVector sign)

/-- The paper's Section 8 argument: nonnegativity in the two null directions
derives the absolute-value mass–charge–scalar inequality. -/
theorem gibbonsWells_linearized_null_nonnegative_implies_bound
    (M Sigma g s qHat : ℝ) (hs : 0 ≤ s)
    (hnull : GibbonsWellsLinearizedNullNonnegative M Sigma g s qHat) :
    s * |qHat| ≤ gibbonsWellsEffectiveMass M Sigma g := by
  have hplus := hnull 1 (by norm_num)
  have hminus := hnull (-1) (by norm_num)
  rw [gibbonsWells_linearized_null_contraction M Sigma g s qHat 1 (by norm_num)] at hplus
  rw [gibbonsWells_linearized_null_contraction M Sigma g s qHat (-1) (by norm_num)] at hminus
  have habs : |s * qHat| ≤ gibbonsWellsEffectiveMass M Sigma g := by
    rw [abs_le]
    constructor <;> nlinarith
  calc
    s * |qHat| = |s * qHat| := by rw [abs_mul, abs_of_nonneg hs]
    _ ≤ gibbonsWellsEffectiveMass M Sigma g := habs

/-- With positive `G`, the exact Section 8 matrix argument derives the public
`GibbonsWellsBound` proposition from linearized null nonnegativity. -/
theorem gibbonsWells_linearized_null_nonnegative_derives_physical_bound
    (G M Sigma Q g s : ℝ) (hG : 0 < G) (hs : 0 ≤ s)
    (hnull : GibbonsWellsLinearizedNullNonnegative M Sigma g s
      (signedGravitationallyNormalizedCharge G Q)) :
    GibbonsWellsBound G g s M Sigma Q := by
  unfold GibbonsWellsBound
  rw [← abs_signedGravitationallyNormalizedCharge G Q hG]
  exact gibbonsWells_linearized_null_nonnegative_implies_bound
    M Sigma g s (signedGravitationallyNormalizedCharge G Q) hs hnull


/-! ## K. Asymptotic time delay and five-dimensional null focusing -/

/-- The `1/r` coefficient `ν₀` obtained from the paper's
`3ν=2gκφ` and `φ∼GΣ/(κr)`. -/
noncomputable def gibbonsWellsAsymptoticNuCoefficient
    (G g Sigma : ℝ) : ℝ :=
  2 * g * G * Sigma / 3

/-- The `1/r` coefficient `χ₀` obtained from `ν+2χ=0`. -/
noncomputable def gibbonsWellsAsymptoticChiCoefficient
    (G g Sigma : ℝ) : ℝ :=
  -(g * G * Sigma) / 3

/-- The physical scalar asymptotics simultaneously satisfy Eqs. (3.19)–(3.20)
and give the exact mass shift `χ₀-ν₀=-gGΣ` used in Eq. (3.17). -/
theorem gibbonsWells_asymptotic_warp_coefficients
    (G g Sigma : ℝ) :
    3 * gibbonsWellsAsymptoticNuCoefficient G g Sigma =
        2 * g * G * Sigma ∧
    gibbonsWellsAsymptoticNuCoefficient G g Sigma +
        2 * gibbonsWellsAsymptoticChiCoefficient G g Sigma = 0 ∧
    gibbonsWellsAsymptoticChiCoefficient G g Sigma -
        gibbonsWellsAsymptoticNuCoefficient G g Sigma =
      -g * G * Sigma := by
  unfold gibbonsWellsAsymptoticNuCoefficient
    gibbonsWellsAsymptoticChiCoefficient
  constructor
  · ring
  constructor <;> ring

/-- The physical-units asymptotic effective mass of Eq. (3.17):
`2GM̂ = 2GM-cos²γ(GM+χ₀-ν₀)+(sκQ/4π)cosγ`. -/
noncomputable def gibbonsWellsPhysicalAsymptoticMass
    (G M chi0 nu0 s kappa Q cosGamma : ℝ) : ℝ :=
  (2 * G * M -
      cosGamma ^ 2 * (G * M + chi0 - nu0) +
      (s * kappa * Q / (4 * Real.pi)) * cosGamma) / (2 * G)

/-- When `κ²=4πG`, the electromagnetic coefficient in physical units is
exactly the signed gravitationally normalized charge `Q/κ`. -/
theorem gibbonsWells_kappa_charge_coefficient
    (G kappa Q : ℝ) (hG : G ≠ 0) (hkappa : kappa ≠ 0)
    (hkappaSq : kappa ^ 2 = 4 * Real.pi * G) :
    (kappa * Q / (4 * Real.pi)) / G = Q / kappa := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  rw [hkappaSq]
  ring

/-- The asymptotic effective mass `M̂` of Eq. (3.17), divided by the
common Newton factor and written with signed normalized charge `q̂`.
The argument `cosGamma` is `cos γ`:
`2M̂ = 2M-cos²γ(M-gΣ)+s q̂ cosγ`. -/
noncomputable def gibbonsWellsNormalizedAsymptoticMass
    (M Sigma g s qHat cosGamma : ℝ) : ℝ :=
  (2 * M - cosGamma ^ 2 * (M - g * Sigma) +
    s * qHat * cosGamma) / 2

/-- The paper's physical-units Eq. (3.17), after deriving `χ₀` and `ν₀`
from the dilaton asymptotics and using `κ²=4πG`, is exactly the existing
normalized asymptotic-mass carrier. This closes the units conversion rather
than assuming the normalized formula independently. -/
theorem gibbonsWellsPhysicalAsymptoticMass_eq_normalized
    (G M Sigma g s kappa Q cosGamma : ℝ)
    (hG : G ≠ 0) (hkappa : kappa ≠ 0)
    (hkappaSq : kappa ^ 2 = 4 * Real.pi * G) :
    gibbonsWellsPhysicalAsymptoticMass G M
        (gibbonsWellsAsymptoticChiCoefficient G g Sigma)
        (gibbonsWellsAsymptoticNuCoefficient G g Sigma)
        s kappa Q cosGamma =
      gibbonsWellsNormalizedAsymptoticMass
        M Sigma g s (Q / kappa) cosGamma := by
  have hq := gibbonsWells_kappa_charge_coefficient
    G kappa Q hG hkappa hkappaSq
  unfold gibbonsWellsPhysicalAsymptoticMass
    gibbonsWellsAsymptoticChiCoefficient
    gibbonsWellsAsymptoticNuCoefficient
    gibbonsWellsNormalizedAsymptoticMass
  field_simp at hq ⊢
  linear_combination 3 * s * cosGamma * hq

/-- The exact extremal phase is also visible in the asymptotic carrier:
with the signed charge of Eq. (7.12), the physical effective mass at
`γ=0` is exactly zero. This proves the saturation statement following
Eq. (7.9), rather than retaining only its unsigned charge magnitude. -/
theorem gibbonsWellsPhysicalAsymptoticMass_extreme_cos_one
    (G g mu kappa : ℝ) (hG : G ≠ 0) (hkappa : kappa ≠ 0)
    (hkappaSq : kappa ^ 2 = 4 * Real.pi * G) :
    gibbonsWellsPhysicalAsymptoticMass G
        (gibbonsWellsExtremeMass g mu)
        (gibbonsWellsAsymptoticChiCoefficient G g
          (gibbonsWellsExtremeScalarCharge g mu))
        (gibbonsWellsAsymptoticNuCoefficient G g
          (gibbonsWellsExtremeScalarCharge g mu))
        (gibbonsWellsExtremeProbeCoupling g) kappa
        (gibbonsWellsExtremeSignedElectricCharge kappa g mu) 1 = 0 := by
  rw [gibbonsWellsPhysicalAsymptoticMass_eq_normalized
    G (gibbonsWellsExtremeMass g mu)
      (gibbonsWellsExtremeScalarCharge g mu) g
      (gibbonsWellsExtremeProbeCoupling g) kappa
      (gibbonsWellsExtremeSignedElectricCharge kappa g mu) 1
      hG hkappa hkappaSq]
  calc
    gibbonsWellsNormalizedAsymptoticMass
        (gibbonsWellsExtremeMass g mu)
        (gibbonsWellsExtremeScalarCharge g mu) g
        (gibbonsWellsExtremeProbeCoupling g)
        (gibbonsWellsExtremeSignedElectricCharge kappa g mu / kappa) 1 =
      (gibbonsWellsEffectiveMass
          (gibbonsWellsExtremeMass g mu)
          (gibbonsWellsExtremeScalarCharge g mu) g +
        gibbonsWellsExtremeProbeCoupling g *
          (gibbonsWellsExtremeSignedElectricCharge kappa g mu / kappa)) / 2 := by
            unfold gibbonsWellsNormalizedAsymptoticMass
              gibbonsWellsEffectiveMass
            ring
    _ = 0 := by
      rw [gibbonsWells_extreme_signed_charge_saturates
        kappa g mu hkappa]
      ring

/-- In the `γ→0` endpoint (`cos γ=1`), the asymptotic effective mass is
half of `M+gΣ+s q̂`. -/
theorem gibbonsWellsNormalizedAsymptoticMass_cos_one
    (M Sigma g s qHat : ℝ) :
    gibbonsWellsNormalizedAsymptoticMass M Sigma g s qHat 1 =
      (gibbonsWellsEffectiveMass M Sigma g + s * qHat) / 2 := by
  unfold gibbonsWellsNormalizedAsymptoticMass gibbonsWellsEffectiveMass
  ring

/-- In the `γ→π` endpoint (`cos γ=-1`), the asymptotic effective mass is
half of `M+gΣ-s q̂`. -/
theorem gibbonsWellsNormalizedAsymptoticMass_cos_neg_one
    (M Sigma g s qHat : ℝ) :
    gibbonsWellsNormalizedAsymptoticMass M Sigma g s qHat (-1) =
      (gibbonsWellsEffectiveMass M Sigma g - s * qHat) / 2 := by
  unfold gibbonsWellsNormalizedAsymptoticMass gibbonsWellsEffectiveMass
  ring

/-- Nonnegativity of both endpoint effective masses derives the absolute
mass–scalar–charge inequality of Eq. (3.21). -/
theorem gibbonsWells_asymptotic_endpoints_nonneg_imply_bound
    (M Sigma g s qHat : ℝ) (hs : 0 ≤ s)
    (hzero : 0 ≤
      gibbonsWellsNormalizedAsymptoticMass M Sigma g s qHat 1)
    (hpi : 0 ≤
      gibbonsWellsNormalizedAsymptoticMass M Sigma g s qHat (-1)) :
    s * |qHat| ≤ gibbonsWellsEffectiveMass M Sigma g := by
  rw [gibbonsWellsNormalizedAsymptoticMass_cos_one] at hzero
  rw [gibbonsWellsNormalizedAsymptoticMass_cos_neg_one] at hpi
  have habs : |s * qHat| ≤ gibbonsWellsEffectiveMass M Sigma g := by
    rw [abs_le]
    constructor <;> linarith
  calc
    s * |qHat| = |s * qHat| := by rw [abs_mul, abs_of_nonneg hs]
    _ ≤ gibbonsWellsEffectiveMass M Sigma g := habs

/-- With positive `G`, the endpoint argument gives the physical bound with
`|Q|/√(4πG)`. -/
theorem gibbonsWells_asymptotic_endpoints_derive_physical_bound
    (G M Sigma Q g s : ℝ) (hG : 0 < G) (hs : 0 ≤ s)
    (hzero : 0 ≤ gibbonsWellsNormalizedAsymptoticMass M Sigma g s
      (signedGravitationallyNormalizedCharge G Q) 1)
    (hpi : 0 ≤ gibbonsWellsNormalizedAsymptoticMass M Sigma g s
      (signedGravitationallyNormalizedCharge G Q) (-1)) :
    GibbonsWellsBound G g s M Sigma Q := by
  unfold GibbonsWellsBound
  rw [← abs_signedGravitationallyNormalizedCharge G Q hG]
  exact gibbonsWells_asymptotic_endpoints_nonneg_imply_bound
    M Sigma g s (signedGravitationallyNormalizedCharge G Q) hs hzero hpi

/-- The leading large-impact-parameter time-of-flight term of Eq. (3.18):
`-4G M̂ |csc γ| log(b/b₀)`. The bounded `O(1)` remainder is deliberately
not included in this leading carrier. -/
noncomputable def gibbonsWellsTimeDelayLeading
    (G Mhat cscAbs b0 b : ℝ) : ℝ :=
  (-4 * G * Mhat * cscAbs) * Real.log (b / b0)

/-- A negative effective mass makes the leading time delay diverge to
`+∞` as the impact parameter tends to infinity, for positive `G`, reference
impact parameter, and `|csc γ|`. This is the analytic statement behind the
paper's “arbitrarily large time of flight” step. -/
theorem gibbonsWellsTimeDelayLeading_tendsto_atTop
    (G Mhat cscAbs b0 : ℝ)
    (hG : 0 < G) (hMhat : Mhat < 0) (hcsc : 0 < cscAbs) (hb0 : 0 < b0) :
    Filter.Tendsto
      (gibbonsWellsTimeDelayLeading G Mhat cscAbs b0)
      Filter.atTop Filter.atTop := by
  have harg : Filter.Tendsto (fun b : ℝ => b / b0)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hb0 Filter.tendsto_id
  have hlog : Filter.Tendsto (fun b : ℝ => Real.log (b / b0))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp harg
  have hcoefficient : 0 < -4 * G * Mhat * cscAbs := by
    have hnegM : 0 < -Mhat := neg_pos.mpr hMhat
    have hproduct : 0 < 4 * G * (-Mhat) * cscAbs := by positivity
    have heq : -4 * G * Mhat * cscAbs = 4 * G * (-Mhat) * cscAbs := by ring
    rw [heq]
    exact hproduct
  change Filter.Tendsto
    (fun b : ℝ => (-4 * G * Mhat * cscAbs) * Real.log (b / b0))
    Filter.atTop Filter.atTop
  exact Filter.Tendsto.const_mul_atTop hcoefficient hlog

/-- A future-regular **five-dimensional** null-congruence carrier.
The coefficient `1/3` is the correct Raychaudhuri coefficient
`1/(d-2)` for `d=5`, unlike the repository's four-dimensional `1/2`
carrier. -/
structure FutureRegularFiveDimensionalNullRaychaudhuri where
  /-- Five-dimensional null expansion `θ(λ)`. -/
  expansion : ℝ → ℝ
  /-- Squared shear. -/
  shearSq : ℝ → ℝ
  /-- Five-dimensional null-Ricci contraction. -/
  ricciNull : ℝ → ℝ
  /-- Five-dimensional null Raychaudhuri equation. -/
  expansion_hasDerivAt : ∀ t,
    HasDerivAt expansion
      (-(expansion t) ^ 2 / 3 - shearSq t - ricciNull t) t
  /-- Geometric nonnegativity of shear squared. -/
  shearSq_nonneg : ∀ t, 0 ≤ shearSq t
  /-- Five-dimensional null convergence condition. -/
  ricciNull_nonneg : ∀ t, 0 ≤ ricciNull t

namespace FutureRegularFiveDimensionalNullRaychaudhuri

/-- Exact rescaling from the five-dimensional Raychaudhuri coefficient
`1/3` to the already-proved four-dimensional coefficient `1/2`:
`θ₄=(2/3)θ₅`, with the shear and Ricci terms scaled identically. -/
noncomputable def toFourDimensional
    (R : FutureRegularFiveDimensionalNullRaychaudhuri) :
    FutureRegularNullRaychaudhuri where
  expansion := fun t => (2 / 3 : ℝ) * R.expansion t
  shearSq := fun t => (2 / 3 : ℝ) * R.shearSq t
  ricciNull := fun t => (2 / 3 : ℝ) * R.ricciNull t
  expansion_hasDerivAt := by
    intro t
    have h := (R.expansion_hasDerivAt t).const_mul (2 / 3 : ℝ)
    apply h.congr_deriv
    ring
  shearSq_nonneg := fun t =>
    mul_nonneg (by norm_num) (R.shearSq_nonneg t)
  ricciNull_nonneg := fun t =>
    mul_nonneg (by norm_num) (R.ricciNull_nonneg t)

/-- Future regularity plus five-dimensional null convergence forbids negative
expansion. The proof reuses the repository's full reciprocal-expansion
focusing theorem through `toFourDimensional`; it does not duplicate it. -/
theorem expansion_nonneg
    (R : FutureRegularFiveDimensionalNullRaychaudhuri) (t : ℝ) :
    0 ≤ R.expansion t := by
  have h := R.toFourDimensional.expansion_nonneg t
  change 0 ≤ (2 / 3 : ℝ) * R.expansion t at h
  nlinarith

end FutureRegularFiveDimensionalNullRaychaudhuri

/-- Build the five-dimensional Raychaudhuri carrier directly from the paper's
reduced null-Ricci normal form. This is the local differential-geometric bridge:
the coefficient/source hypotheses already proved in §H discharge the
`ricciNull_nonneg` field pointwise. Future completeness and differentiability of
the expansion remain explicit inputs. -/
noncomputable def gibbonsWellsReducedNullRicciRaychaudhuri
    (expansion shearSq : ℝ → ℝ)
    (kappa nu g s V5 : ℝ)
    (dilatonDerivativeSq magneticBH electricED
      scalarSource matter current : ℝ → ℝ)
    (hcoupling : GibbonsWellsNullConvergenceCouplings g s)
    (hexpansion : ∀ t, HasDerivAt expansion
      (-(expansion t) ^ 2 / 3 - shearSq t -
        gibbonsWellsReducedNullRicci kappa nu g s V5
          (dilatonDerivativeSq t) (magneticBH t) (electricED t)
          (scalarSource t) (matter t) (current t)) t)
    (hshear : ∀ t, 0 ≤ shearSq t)
    (hdilaton : ∀ t, 0 ≤ dilatonDerivativeSq t)
    (hmagnetic : ∀ t, 0 ≤ magneticBH t)
    (helectric : ∀ t, 0 ≤ electricED t)
    (hsource : ∀ t, GibbonsWellsNullRicciSourceCondition
      kappa nu g s V5 (scalarSource t) (matter t) (current t)) :
    FutureRegularFiveDimensionalNullRaychaudhuri where
  expansion := expansion
  shearSq := shearSq
  ricciNull := fun t =>
    gibbonsWellsReducedNullRicci kappa nu g s V5
      (dilatonDerivativeSq t) (magneticBH t) (electricED t)
      (scalarSource t) (matter t) (current t)
  expansion_hasDerivAt := hexpansion
  shearSq_nonneg := hshear
  ricciNull_nonneg := fun t =>
    gibbonsWells_reducedNullRicci_nonneg
      kappa nu g s V5
      (dilatonDerivativeSq t) (magneticBH t) (electricED t)
      (scalarSource t) (matter t) (current t)
      hcoupling (hdilaton t) (hmagnetic t) (helectric t) (hsource t)

/-- The explicitly conditional global causal input in the Gibbons–Wells
argument. Penrose–Sorkin–Woolgar supplies a complete fastest boundary null
ray, while the generic condition turns negative asymptotic effective mass
into negative expansion somewhere on that ray. The local focusing theorem
then provides the contradiction. -/
structure GibbonsWellsCausalFocusingCertificate (Mhat : ℝ) where
  /-- The future-regular five-dimensional fastest null ray. -/
  ray : FutureRegularFiveDimensionalNullRaychaudhuri
  /-- The PSW plus generic-condition implication used by the paper. -/
  negativeMass_generates_negativeExpansion :
    Mhat < 0 → ∃ t, ray.expansion t < 0

/-- A complete causal-focusing certificate forces nonnegative asymptotic
effective mass. This closes the local Raychaudhuri part while keeping the
global PSW/generic-condition construction visible as certificate data. -/
theorem GibbonsWellsCausalFocusingCertificate.effectiveMass_nonneg
    {Mhat : ℝ} (C : GibbonsWellsCausalFocusingCertificate Mhat) :
    0 ≤ Mhat := by
  by_contra h
  rcases C.negativeMass_generates_negativeExpansion (lt_of_not_ge h) with ⟨t, ht⟩
  exact (not_lt_of_ge (C.ray.expansion_nonneg t)) ht


/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach gibbonsWells_bound_implies_no_longRange_repulsion where
  formalizes @ "claim:gibbons-wells-dilaton-bound-excludes-net-long-range-repulsion",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:gibbons-wells-maximal-mass-scalar-electric-charge-bound",
  requires @ "claim:positive-newton-coupling",
  epistemic_status @ "conditional-model",
  caveat @ "claim:global-penrose-sorkin-woolgar-causal-bound-is-an-explicit-premise-not-reproved-here"

zil attach gibbonsWells_maximalProbe_admissible_iff where
  formalizes @ "claim:gibbons-wells-maximal-probe-coupling-admissible-exactly-through-g-squared-le-three",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:five-dimensional-null-convergence-coefficient-reduction",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:sufficient-coefficient-region-not-necessity-of-the-physical-bound"

zil attach gibbonsWells_causal_not_imply_spinorial where
  formalizes @ "claim:gibbons-wells-causal-bound-does-not-imply-witten-spinorial-bound-with-dilaton",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  epistemic_status @ "mathematical-counterexample",
  caveat @ "claim:normalized-g-one-algebraic-witness-not-a-new-spacetime-solution"

zil attach gibbonsWells_spinorial_not_imply_causal where
  formalizes @ "claim:witten-spinorial-bound-does-not-imply-gibbons-wells-causal-bound-with-dilaton",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  epistemic_status @ "mathematical-counterexample",
  caveat @ "claim:normalized-g-one-algebraic-witness-not-a-new-spacetime-solution"

zil attach gibbonsWells_blackHole_satisfies_maximal_bound where
  formalizes @ "claim:static-charged-dilaton-black-holes-satisfy-the-gibbons-wells-maximal-bound",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:charged-dilaton-black-hole-mass-scalar-charge-and-electric-charge-formulas",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-horizon-radius-algebra-given-the-paper-static-black-hole-solution"

zil attach gibbonsWells_extreme_multicentre_saturates where
  formalizes @ "claim:gibbons-wells-extremal-multicentre-family-saturates-dilaton-bound",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:extremal-multicentre-mass-scalar-electric-charge-formulas",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-aggregate-charge-algebra-given-the-paper-extremal-family-formulas"

zil attach gibbonsWells_extreme_multicentre_pair_equipoise where
  formalizes @ "claim:gibbons-wells-extremal-multicentre-pairs-have-zero-net-long-range-force",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:extremal-multicentre-mass-scalar-electric-charge-formulas",
  epistemic_status @ "conditional-model",
  caveat @ "claim:long-range-pair-force-only-not-full-nonlinear-multicentre-stability"

zil attach gibbonsWells_extreme_lift_compatible where
  formalizes @ "claim:gibbons-wells-extremal-five-dimensional-lift-satisfies-equations-seven-five-through-seven-seven",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:extremal-multicentre-harmonic-function-lift-ansatz",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:exact-exponent-and-coupling-algebra-for-the-paper-lift-ansatz-not-a-new-existence-proof-for-the-multicentre-spacetime"

zil attach gibbonsWellsAdaptedTimeVector_is_null where
  formalizes @ "claim:gibbons-wells-extremal-adapted-time-direction-is-null-in-the-explicit-u-t-metric-block",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:gibbons-wells-extremal-five-dimensional-lift-satisfies-equations-seven-five-through-seven-seven",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:exact-pointwise-null-metric-block-and-stationary-lift-ansatz-not-a-global-lie-derivative-proof-that-the-field-is-killing"

zil attach gibbonsWellsAdaptedDu_solves_nullHamiltonJacobi where
  formalizes @ "claim:gibbons-wells-exact-phase-u-solves-the-null-hamilton-jacobi-equation-for-the-extremal-lift",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:displayed-adapted-u-t-inverse-metric-carrier",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:null-quadratic-identity-is-unconditional-but-identifying-the-carrier-as-the-actual-inverse-requires-positive-h-and-does-not-prove-global-geodesic-completeness"

zil attach gibbonsWellsAdaptedDu_gradient_eq_timeVector where
  formalizes @ "claim:gibbons-wells-extremal-null-time-direction-is-proportional-to-the-gradient-of-u",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:positive-extremal-harmonic-profile",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:local-adapted-coordinate-hypersurface-orthogonality-not-a-global-foliation-or-principal-bundle-construction"

zil attach gibbonsWells_permittivity_mul_permeability where
  formalizes @ "claim:gibbons-wells-dilaton-permittivity-times-permeability-is-one",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:local-constitutive-law-in-the-paper-natural-units"

zil attach gibbonsWellsElectromagneticEnergyDensity_nonneg where
  formalizes @ "claim:gibbons-wells-dilaton-electromagnetic-energy-density-is-pointwise-nonnegative",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:gibbons-wells-dilaton-permittivity-times-permeability-is-one",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:pointwise-constitutive-energy-positivity-not-a-global-finite-energy-solution"

zil attach gibbonsWells_probe_chargeToMass where
  formalizes @ "claim:gibbons-wells-five-dimensional-null-ray-projects-to-charge-to-mass-ratio-s-kappa",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:projected-probe-mass-e-over-kappa-and-charge-s-e",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:algebraic-probe-identification-not-a-global-existence-theorem-for-five-dimensional-null-geodesics"

zil attach gibbonsWellsProbeLorentzForce_eq where
  formalizes @ "claim:gibbons-wells-projected-five-dimensional-null-ray-obeys-the-s-kappa-scaled-lorentz-force",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:gibbons-wells-five-dimensional-null-ray-projects-to-charge-to-mass-ratio-s-kappa",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:pointwise-force-coefficient-identification-not-existence-or-completeness-of-worldline-solutions"

zil attach gibbonsWellsProjectedForce_power_eq_scalar where
  formalizes @ "claim:gibbons-wells-projected-lorentz-force-does-no-work-and-only-scalar-channel-changes-dressed-mass",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:antisymmetric-faraday-field-strength",
  epistemic_status @ "conditional-model",
  caveat @ "claim:pointwise-force-decomposition-not-a-solved-worldline-or-field-equation"

zil attach gibbonsWellsReducedHamiltonJacobi_gaugeInvariant where
  formalizes @ "claim:gibbons-wells-reduced-scalar-dressed-hamilton-jacobi-normal-form-is-gauge-invariant",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:minimal-coupling-kinetic-momentum-p-minus-q-a",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:inverse-metric-is-an-explicit-parameter-and-the-hamilton-jacobi-pde-is-not-solved"

zil attach gibbonsWellsFiveHorizontalMomentum_gaugeInvariant where
  formalizes @ "claim:gibbons-wells-five-dimensional-horizontal-momentum-is-invariant-under-the-lifted-kaluza-klein-gauge-transformation",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:twisted-five-dimensional-metric-dx-five-plus-s-kappa-a",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:pointwise-covector-transformation-not-a-global-principal-bundle-construction"

zil attach gibbonsWellsFiveMetricQuadratic_gaugeInvariant where
  formalizes @ "claim:gibbons-wells-covariant-five-dimensional-twisted-metric-quadratic-is-gauge-invariant",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:compensated-fiber-coordinate-shift-under-kaluza-klein-gauge-transformation",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:exact-coordinate-metric-normal-form-with-supplied-four-metric-not-a-global-principal-bundle-or-atlas-construction"

zil attach gibbonsWells_horizontal_twisted_dual_pairing where
  formalizes @ "claim:gibbons-wells-horizontal-momentum-is-dual-to-the-twisted-five-dimensional-fiber-coframe",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:twisted-five-dimensional-metric-dx-five-plus-s-kappa-a",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:canonical-pointwise-covector-vector-pairing-identity-not-a-global-pseudo-riemannian-duality-construction"

zil attach gibbonsWellsFiveHamiltonJacobi_null_iff_reduced where
  formalizes @ "claim:gibbons-wells-five-dimensional-null-hamilton-jacobi-equation-is-equivalent-to-the-four-dimensional-charged-scalar-dressed-mass-shell",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:conserved-fifth-momentum-e-over-kappa",
  requires @ "claim:twisted-five-dimensional-inverse-metric-horizontal-normal-form",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:exact-pointwise-inverse-metric-reduction-not-existence-or-regularity-of-a-global-hamilton-jacobi-solution"

zil attach gibbonsWellsFifthVelocity_recovers_fiberMomentum where
  formalizes @ "claim:gibbons-wells-projected-and-fifth-velocity-formulas-recover-the-conserved-fiber-momentum",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:twisted-five-dimensional-inverse-metric-horizontal-normal-form",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:inverse-fiber-block-identity-not-a-global-null-geodesic-existence-theorem"

zil attach gibbonsWells_reducedNullRicci_nonneg where
  formalizes @ "claim:gibbons-wells-reduced-five-dimensional-null-ricci-contraction-is-nonnegative",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:gibbons-wells-five-dimensional-null-convergence-coefficient-and-source-conditions",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-reduced-equation-five-four-normal-form-with-source-block-premise-not-a-coordinate-free-derivation-of-the-five-dimensional-ricci-tensor"

zil attach gibbonsWells_reducedNullRicci_kaluzaKlein_vacuum where
  formalizes @ "claim:gibbons-wells-kaluza-klein-endpoint-reduced-null-ricci-contraction-vanishes-in-vacuum",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:contracted-null-ricci-normal-form-not-all-components-of-five-dimensional-ricci-flatness"

zil attach gibbonsWells_reducedRicciComponents_kaluzaKlein_vacuum where
  formalizes @ "claim:gibbons-wells-mixed-fiber-and-base-reduced-ricci-components-all-vanish-at-the-source-free-kaluza-klein-endpoint",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:gibbons-wells-reduced-orthonormal-frame-ricci-component-formulas-four-eight-through-four-ten",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:componentwise-reduced-normal-forms-not-a-coordinate-free-derivation-of-the-full-five-dimensional-ricci-tensor"

zil attach gibbonsWells_explicitSources_imply_sourceCondition where
  formalizes @ "claim:gibbons-wells-nonnegative-scalar-source-and-absolute-current-domination-imply-nonnegative-null-ricci-source-block",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:nonnegative-dilaton-coupling-convention",
  epistemic_status @ "conditional-analysis",
  caveat @ "claim:absolute-current-domination-is-sign-independent-and-stronger-than-the-paper-directed-equation-five-nine"

zil attach gibbonsWells_reducedNullRicci_nonneg_of_explicitSources where
  formalizes @ "claim:gibbons-wells-explicit-field-coefficient-and-source-inequalities-imply-five-dimensional-null-convergence",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:gibbons-wells-five-dimensional-null-convergence-coefficient-and-source-conditions",
  requires @ "claim:gibbons-wells-nonnegative-scalar-source-and-absolute-current-domination-imply-nonnegative-null-ricci-source-block",
  epistemic_status @ "conditional-model",
  caveat @ "claim:pointwise-reduced-null-contraction-not-global-causal-completeness-or-a-full-tensor-curvature-construction"

zil attach gibbonsWellsProbeLorentzForceDual_eq where
  formalizes @ "claim:gibbons-wells-projected-lorentz-force-bcj-dual-is-s-kappa-squared-times-bare-dual",
  requires @ "claim:gibbons-wells-five-dimensional-null-ray-projects-to-charge-to-mass-ratio-s-kappa",
  requires @ "claim:bcj-double-copy-dual-of-the-lorentz-force",
  supported_by @ "paper:bern-carrasco-johansson-2008-color-kinematics",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:repository-bcj-extension-not-a-claim-of-the-1993-gibbons-wells-paper"

zil attach gibbonsWellsProbeLorentzForceNum_sq_sum_eq_curvature where
  formalizes @ "claim:gibbons-wells-projected-lorentz-bcj-numerator-square-is-the-f-squared-curvature-quadratic-form",
  requires @ "claim:gibbons-wells-projected-lorentz-force-bcj-dual-is-s-kappa-squared-times-bare-dual",
  requires @ "claim:operator-level-lorentz-force-gravity-double-copy",
  supported_by @ "paper:bern-carrasco-johansson-2008-color-kinematics",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:operator-level-repository-bridge-not-a-derivation-of-full-dilaton-gravity-amplitudes"

zil attach gibbonsWells_fiveDimensional_probe_closure where
  formalizes @ "claim:gibbons-wells-fixed-fifth-momentum-jointly-derives-the-reduced-mass-shell-lorentz-force-and-bcj-coupling",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:gibbons-wells-five-dimensional-null-hamilton-jacobi-equation-is-equivalent-to-the-four-dimensional-charged-scalar-dressed-mass-shell",
  requires @ "claim:gibbons-wells-projected-five-dimensional-null-ray-obeys-the-s-kappa-scaled-lorentz-force",
  requires @ "claim:bcj-double-copy-dual-of-the-lorentz-force",
  epistemic_status @ "bridge-theorem",
  caveat @ "claim:bcj-clause-is-a-later-repository-extension-and-the-conjunction-does-not-supply-global-geodesic-existence-or-gravity-amplitudes"

zil attach gibbonsWells_linearized_null_nonnegative_derives_physical_bound where
  formalizes @ "claim:gibbons-wells-linearized-asymptotic-null-convergence-derives-the-mass-scalar-charge-bound",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:linearized-asymptotic-four-five-metric-block-is-nonnegative-on-both-null-directions",
  requires @ "claim:positive-newton-coupling",
  epistemic_status @ "conditional-model",
  caveat @ "claim:section-eight-linearized-static-derivation-not-the-paper-global-nonlinear-penrose-sorkin-woolgar-causal-proof"

zil attach gibbonsWells_asymptotic_endpoints_derive_physical_bound where
  formalizes @ "claim:gibbons-wells-gamma-zero-and-pi-asymptotic-effective-mass-signs-derive-the-absolute-mass-scalar-charge-bound",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:both-asymptotic-endpoint-effective-masses-are-nonnegative",
  requires @ "claim:positive-newton-coupling",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-endpoint-algebra-given-effective-mass-nonnegativity-not-yet-the-global-causal-proof-of-that-nonnegativity"

zil attach gibbonsWellsPhysicalAsymptoticMass_eq_normalized where
  formalizes @ "claim:gibbons-wells-physical-units-asymptotic-mass-reduces-exactly-to-the-normalized-effective-mass",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:scalar-asymptotics-phi-is-g-sigma-over-kappa-r",
  requires @ "claim:kappa-squared-is-four-pi-g",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:exact-units-and-asymptotic-coefficient-reduction-not-a-proof-that-the-effective-mass-is-nonnegative"

zil attach gibbonsWellsPhysicalAsymptoticMass_extreme_cos_one where
  formalizes @ "claim:gibbons-wells-extremal-signed-charge-makes-the-physical-gamma-zero-asymptotic-effective-mass-vanish",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:extremal-multicentre-mass-scalar-and-signed-electric-charge-formulas",
  requires @ "claim:kappa-squared-is-four-pi-g",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-saturation-for-the-paper-extremal-family-not-a-proof-that-generic-solutions-saturate-the-causal-bound"

zil attach gibbonsWellsTimeDelayLeading_tendsto_atTop where
  formalizes @ "claim:negative-gibbons-wells-asymptotic-effective-mass-makes-the-leading-large-impact-parameter-time-delay-diverge",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:negative-asymptotic-effective-mass-and-positive-impact-parameter-data",
  epistemic_status @ "mathematical-analysis",
  caveat @ "claim:leading-logarithmic-term-only-the-paper-bounded-big-o-remainder-is-not-modeled"

zil attach FutureRegularFiveDimensionalNullRaychaudhuri.expansion_nonneg where
  formalizes @ "claim:future-regular-five-dimensional-null-ray-with-null-convergence-cannot-have-negative-expansion",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:global-future-regularity-five-dimensional-raychaudhuri-equation-and-nonnegative-shear",
  requires @ "claim:five-dimensional-null-ricci-contraction-is-nonnegative",
  epistemic_status @ "conditional-analysis",
  caveat @ "claim:future-regularity-is-a-strong-no-caustic-premise-and-does-not-construct-the-penrose-sorkin-woolgar-boundary-ray"

zil attach GibbonsWellsCausalFocusingCertificate.effectiveMass_nonneg where
  formalizes @ "claim:gibbons-wells-global-causal-focusing-certificate-forces-nonnegative-asymptotic-effective-mass",
  supported_by @ "paper:gibbons-wells-1993-antigravity-bounds-ricci-tensor",
  requires @ "claim:penrose-sorkin-woolgar-fastest-complete-boundary-null-ray",
  requires @ "claim:generic-condition-turns-negative-effective-mass-into-negative-expansion",
  requires @ "claim:future-regular-five-dimensional-null-ray-with-null-convergence-cannot-have-negative-expansion",
  epistemic_status @ "conditional-model",
  caveat @ "claim:global-causal-and-generic-condition-implication-is-explicit-certificate-data-not-reproved-from-a-spacetime-atlas"

zil_file_contract physlib.spacetimePositiveMass where
  promises "ADM positive-mass algebra and the Gibbons-Wells dilatonic anti-gravity extension: the maximal causal mass-scalar-electric-charge bound excludes net long-range repulsion; its auxiliary five-dimensional coefficient range and explicit scalar-source/current-domination conditions prove the reduced null-Ricci contraction nonnegative, while the mixed, fiber and base component normal forms all vanish at the source-free Kaluza-Klein endpoint; maximal probe coupling is admitted exactly through g squared at most three; the explicit static charged-dilaton black-hole family satisfies the bound for every coupling; its causal and Witten-spinorial bounds are independent at nonzero dilaton coupling; the extremal multi-centre family saturates the causal bound and has pairwise long-range equipoise, and its explicit five-dimensional lift parameters satisfy equations seven-five through seven-seven; the resulting adapted metric has a null time direction, an explicit inverse, and the exact phase u solves its null Hamilton-Jacobi equation with gradient proportional to that time direction; the signed physical extremal charge makes the gamma-zero effective mass vanish exactly; the dilaton constitutive medium has nonnegative pointwise electromagnetic energy; the covariant twisted five-metric quadratic is gauge invariant and its coframe is exactly dual to the inverse-metric horizontal momentum; the projected and fifth velocities recover the conserved fiber momentum; fixing that momentum to e over kappa proves equivalence of the five-dimensional null and four-dimensional scalar-dressed Hamilton-Jacobi equations and derives the s-kappa-scaled Lorentz force; the scalar-derived physical asymptotic coefficients and kappa squared equals four pi G reduce equation three-seventeen exactly to the normalized mass carrier; the asymptotic endpoint masses derive the absolute physical bound, negative effective mass produces divergent leading time delay, and the correctly normalized five-dimensional Raychaudhuri carrier reuses the repository focusing theorem; the exact linearized asymptotic four-five block independently derives the physical bound from its two null contractions; and a separately-caveated BCJ adapter identifies the projected squared numerator with the existing F-squared curvature generator."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Real.sqrt", "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency.restMassSq", "lean:Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.expansion_nonneg", "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.lorentzForceDual", "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator.gravCurvatureGen"]
  forbids_substitutes ["a proof of the global Penrose-Sorkin-Woolgar causal theorem from the local coefficient or linearized asymptotic algebra", "an equality of every five-dimensional Ricci component, rather than the proved reduced null contraction", "a solved Hamilton-Jacobi PDE or global charged worldline from the proved pointwise normal forms", "attributing the later BCJ double-copy extension to the 1993 Gibbons-Wells paper"]
  witnessed_by [gibbonsWells_bound_implies_no_longRange_repulsion,
    gibbonsWells_maximalProbe_admissible_iff,
    gibbonsWells_causal_not_imply_spinorial,
    gibbonsWells_spinorial_not_imply_causal,
    gibbonsWells_blackHole_satisfies_maximal_bound,
    gibbonsWells_extreme_lift_compatible,
    gibbonsWellsAdaptedTimeVector_is_null,
    gibbonsWellsExtremeLiftUTBlock_mul_inverse,
    gibbonsWellsAdaptedDu_solves_nullHamiltonJacobi,
    gibbonsWellsAdaptedDu_gradient_eq_timeVector,
    gibbonsWells_extreme_signed_charge_saturates,
    gibbonsWells_extreme_multicentre_saturates,
    gibbonsWells_extreme_multicentre_pair_equipoise,
    gibbonsWells_permittivity_mul_permeability,
    gibbonsWellsElectromagneticEnergyDensity_nonneg,
    gibbonsWells_probe_chargeToMass,
    gibbonsWellsProbeLorentzForce_eq,
    gibbonsWellsProjectedForce_power_eq_scalar,
    gibbonsWellsReducedHamiltonJacobi_gaugeInvariant,
    gibbonsWellsFiveHorizontalMomentum_gaugeInvariant,
    gibbonsWellsFiveMetricQuadratic_gaugeInvariant,
    gibbonsWells_horizontal_twisted_dual_pairing,
    gibbonsWellsFiveHamiltonJacobi_null_iff_reduced,
    gibbonsWellsFifthVelocity_recovers_fiberMomentum,
    gibbonsWells_reducedNullRicci_nonneg,
    gibbonsWells_reducedNullRicci_kaluzaKlein_vacuum,
    gibbonsWells_reducedRicciComponents_kaluzaKlein_vacuum,
    gibbonsWells_explicitSources_imply_sourceCondition,
    gibbonsWells_reducedNullRicci_nonneg_of_explicitSources,
    gibbonsWellsProbeLorentzForceDual_eq,
    gibbonsWellsProbeLorentzForceNum_sq_sum_eq_curvature,
    gibbonsWells_fiveDimensional_probe_closure,
    gibbonsWells_linearized_null_nonnegative_derives_physical_bound,
    gibbonsWellsPhysicalAsymptoticMass_eq_normalized,
    gibbonsWellsPhysicalAsymptoticMass_extreme_cos_one,
    gibbonsWells_asymptotic_endpoints_derive_physical_bound,
    gibbonsWellsTimeDelayLeading_tendsto_atTop,
    FutureRegularFiveDimensionalNullRaychaudhuri.expansion_nonneg,
    GibbonsWellsCausalFocusingCertificate.effectiveMass_nonneg]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.CurvedWorldlinePhase
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GFreeComptonRapidityClock
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
public import Physlib.QuantumMechanics.RelationalTime.QuantizedRelationalClock
public import Physlib.Relativity.Special.HyperbolicBoost
public import Physlib.Relativity.Special.ProperTimeWorldlineIntegral

meta import Zil

/-!
# Planck-cell quantized relational clock

This module connects four existing, previously separate carriers:

1. an actual finite Compton-cell tiling with a natural-number count;
2. the G-free area-per-cell calibration and its Planck--Compton closure;
3. a bounded relational clock with orthonormal history kets;
4. the finite diagonal time operator with a uniform spectral gap.

The clock gap is the counted cell light-crossing time
`deltaTime = sqrt(A/N)/c`. The existing closure then gives
`deltaTime^2 = G_count hbar/c^5`, so the clock spectrum fixes the constructed
area-per-cell coupling as `G_count = c^5 deltaTime^2/hbar`. Each step also
advances the activated area by one counted cell.

The Hamiltonian constraint is nonzero: an ancillary forbidden direction has
eigenvalue one, while every history ket lies in the zero-eigenspace. This closes
the vacuity in the earlier witness that used the zero constraint and the same
zero state at every reading.

This is a conditional Planck-cell relational clock. It does not quantize the
gravitational field, produce a graviton, or derive the one-cell-per-event update
from continuum dynamics.

The gap is an invariant one-radian Compton proper-time tick. At fixed position,
the boosted de Broglie phase reaches one radian in `deltaTime / gamma`; along the
particle's group-velocity worldline, time dilation instead gives the coordinate
interval `deltaTime / sqrt (1 - beta^2)`. The boost factors are explicit in every
rewrite of the invariant gravitational coupling and cell area.

The physical specialization uses `beta = tanh theta` and `gamma = cosh theta`.
It reconstructs a 1+1-dimensional de Broglie four-momentum, proves its Minkowski
mass shell, and identifies the straight-worldline proper-time integral and
Minkowski-paired phase of one tick. The earlier results with a free parameter
`beta` remain algebraic identities; only the rapidity specialization supplies
their physical subluminal Lorentz interpretation.

The rapidity momentum, worldline, proper-time, phase, and area closure is proved
first on `GFreeComptonCellCalibration`. It therefore requires neither an actual
finite tiling nor agreement of a natural-number tiling count. The corresponding
result on `Calibration` is a definitional compatibility specialization. Finite
calibration remains essential only for the bounded clock levels, history states,
register, and finite spectral operators.

The same four-momentum is also represented by the Nagao--Nielsen complex
coordinate `p0 + i p1`; its convergence form is proved equal to the actual
Minkowski self-pairing. Separately, the finite clock readings parameterize
continuum Feynman kernels whose Misra age eigenvalues are exactly those
readings. This is a sampling bridge, not an exact canonical commutator on the
finite clock matrix.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.RelationalTime.PlanckCellRelationalClock

open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.RelationalTime.QuantizedTime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.PropagatorTimeOperator
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.Relativity.Special

/-! # A. Coherent finite cell and G-free calibration data -/

/-- A G-free Compton-cell calibration together with an actual finite tiling
whose natural-number count agrees with the calibration's effective real count. -/
structure Calibration where
  /-- The positive G-free area/count calibration. -/
  base : GFreeComptonCellCalibration
  /-- The exact finite tiling at the calibrated screen mass. -/
  tiling : FiniteComptonScreenTiling base.screenMass base.lightSpeed base.hbar
    base.screenArea
  /-- The finite cardinality is the count used by the G-free calibration. -/
  count_agrees : (tiling.cellCount : ℝ) = base.cellCount

namespace Calibration

/-- Construct a relational-clock calibration whenever the positive `G`-free
cell count is the cast of a positive natural number. The finite tiling is not an
additional hypothesis: it is supplied by the inverse-calibrated screen mass. -/
noncomputable def ofGFreeNatCount
    (base : GFreeComptonCellCalibration) (n : ℕ) (hn : 0 < n)
    (hcount : (n : ℝ) = base.cellCount) : Calibration where
  base := base
  tiling := base.finiteTilingOfNatCount n hn hcount
  count_agrees := hcount

/-- Construct the complete relational-clock calibration directly from a
positive screen area, a positive natural-number cell count, light speed, and
reduced Planck constant. -/
noncomputable def ofPositiveData
    (screenArea : ℝ) (cellCount : ℕ) (lightSpeed hbar : ℝ)
    (hA : 0 < screenArea) (hN : 0 < cellCount)
    (hc : 0 < lightSpeed) (hℏ : 0 < hbar) : Calibration :=
  let base : GFreeComptonCellCalibration :=
    { screenArea := screenArea
      cellCount := cellCount
      lightSpeed := lightSpeed
      hbar := hbar
      screenArea_pos := hA
      cellCount_pos := by exact_mod_cast hN
      lightSpeed_pos := hc
      hbar_pos := hℏ }
  ofGFreeNatCount base cellCount hN rfl

/-- Positive finite screen data always admit a complete relational-clock
calibration with exactly those area, count, and conversion constants. -/
@[zil_level bridge_theorem]
lemma exists_calibration_of_positive_data
    (screenArea : ℝ) (cellCount : ℕ) (lightSpeed hbar : ℝ)
    (hA : 0 < screenArea) (hN : 0 < cellCount)
    (hc : 0 < lightSpeed) (hℏ : 0 < hbar) :
    ∃ C : Calibration,
      C.base.screenArea = screenArea
        ∧ C.tiling.cellCount = cellCount
        ∧ C.base.lightSpeed = lightSpeed
        ∧ C.base.hbar = hbar := by
  exact ⟨ofPositiveData screenArea cellCount lightSpeed hbar hA hN hc hℏ,
    rfl, rfl, rfl, rfl⟩

/-- The finite number of physical cell transitions. -/
def cellCount (C : Calibration) : ℕ := C.tiling.cellCount

/-- The bounded clock has one level for each partial activation, including zero. -/
abbrev Level (C : Calibration) : Type := Fin (C.cellCount + 1)

/-- The finite Euclidean clock space carrying the history basis. -/
abbrev ClockSpace (C : Calibration) : Type := EuclideanSpace ℂ C.Level

/-- Clock levels plus one ancillary forbidden direction. -/
abbrev HistoryIndex (C : Calibration) : Type := C.Level ⊕ Fin 1

/-- An extra ancillary direction makes the Hamiltonian constraint nonzero. -/
abbrev HistorySpace (C : Calibration) : Type := EuclideanSpace ℂ C.HistoryIndex

/-- The derived duration of one relational event: the counted cell crossing time. -/
def deltaTime (C : Calibration) : ℝ := C.base.countedPlanckTime

/-- The area advanced by one cell event. -/
def deltaArea (C : Calibration) : ℝ := C.base.cellArea

/-- The existing exact entropic-time lattice instantiated at the counted
Planck/Compton crossing time. -/
def timeLadder (C : Calibration) : EntropicTimeLadder where
  δ_τ := C.deltaTime
  δ_τ_pos := by
    unfold deltaTime GFreeComptonCellCalibration.countedPlanckTime
      GFreeComptonCellCalibration.countedPlanckLength
    exact div_pos (Real.sqrt_pos.2 C.base.cellArea_pos) C.base.lightSpeed_pos
  reading n := (n : ℝ) * C.deltaTime
  reading_eq _ := rfl

/-- The `k`-th bounded relational-time reading. -/
def timeReading (C : Calibration) (k : C.Level) : ℝ :=
  C.timeLadder.reading k

/-- The area represented by the first `k` activated cells. -/
def areaReading (C : Calibration) (k : C.Level) : ℝ :=
  (k : ℝ) * C.deltaArea

/-- The Boolean prefix register at level `k`: precisely the cells with label
strictly below `k` have been activated. -/
def prefixRegister (C : Calibration) (k : C.Level) : C.tiling.CellRegister :=
  fun i => decide (i.val < k.val)

/-- The terminal clock level, after all finite cells have been activated. -/
def finalLevel (C : Calibration) : C.Level := Fin.last C.cellCount

/-! # B. Nontrivial constrained history states -/

/-- The standard orthonormal clock ket at level `k`. -/
def clockKet (C : Calibration) (k : C.Level) : C.ClockSpace :=
  (EuclideanSpace.basisFun C.Level ℂ) k

/-- The Page--Wootters history state at level `k`, with zero forbidden component. -/
def historyState (C : Calibration) (k : C.Level) : C.HistorySpace :=
  (EuclideanSpace.basisFun C.HistoryIndex ℂ) (Sum.inl k)

/-- The ancillary state excluded by the Hamiltonian constraint. -/
def forbiddenState (C : Calibration) : C.HistorySpace :=
  (EuclideanSpace.basisFun C.HistoryIndex ℂ) (Sum.inr 0)

/-- The algebraic ancillary projection before finite-dimensional continuity is applied. -/
def historyHamiltonianLinear (C : Calibration) : C.HistorySpace →ₗ[ℂ] C.HistorySpace where
  toFun ψ := ψ.ofLp (Sum.inr 0) • C.forbiddenState
  map_add' ψ φ := by
    simp only [PiLp.add_apply, add_smul]
  map_smul' z ψ := by
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul]

/-- A nonzero Hamiltonian constraint: it projects onto the forbidden ancillary
direction and annihilates the clock-history subspace. -/
def historyHamiltonian (C : Calibration) : C.HistorySpace →L[ℂ] C.HistorySpace :=
  LinearMap.toContinuousLinearMap C.historyHamiltonianLinear

/-- The Page--Wootters constraint carried by the Planck-cell clock. -/
def constraint (C : Calibration) : HamiltonianConstraint C.HistorySpace where
  H_total := C.historyHamiltonian

/-- The finite clock kets form an orthonormal family. -/
lemma clockKet_orthonormal (C : Calibration) : Orthonormal ℂ C.clockKet :=
  (EuclideanSpace.basisFun C.Level ℂ).orthonormal

/-- The constrained history states themselves form an orthonormal family in
the enlarged history Hilbert space. -/
lemma historyState_orthonormal (C : Calibration) : Orthonormal ℂ C.historyState := by
  change Orthonormal ℂ
    (fun k : C.Level => (EuclideanSpace.basisFun C.HistoryIndex ℂ) (Sum.inl k))
  exact (EuclideanSpace.basisFun C.HistoryIndex ℂ).orthonormal.comp
    (fun k : C.Level => Sum.inl k) Sum.inl_injective

/-- Every clock-history state satisfies the nontrivial Hamiltonian constraint. -/
lemma historyState_physical (C : Calibration) (k : C.Level) :
    C.constraint.IsPhysical (C.historyState k) := by
  simp [constraint, HamiltonianConstraint.IsPhysical, historyHamiltonian,
    historyHamiltonianLinear, historyState, forbiddenState,
    EuclideanSpace.basisFun_apply]

/-- The physical kernel is exactly the subspace with zero forbidden coordinate. -/
lemma isPhysical_iff_forbiddenCoordinate_zero (C : Calibration) (ψ : C.HistorySpace) :
    C.constraint.IsPhysical ψ ↔ ψ.ofLp (Sum.inr 0) = 0 := by
  simp [constraint, HamiltonianConstraint.IsPhysical, historyHamiltonian,
    historyHamiltonianLinear, forbiddenState, EuclideanSpace.basisFun_apply]

/-- The constraint acts as the identity on its forbidden ancillary direction. -/
lemma historyHamiltonian_forbiddenState (C : Calibration) :
    C.historyHamiltonian C.forbiddenState = C.forbiddenState := by
  simp [historyHamiltonian, historyHamiltonianLinear, forbiddenState,
    EuclideanSpace.basisFun_apply]

/-- The Page--Wootters Hamiltonian constraint is genuinely nonzero. -/
lemma historyHamiltonian_ne_zero (C : Calibration) : C.historyHamiltonian ≠ 0 := by
  intro hzero
  have happ := congrArg (fun H => H C.forbiddenState) hzero
  rw [C.historyHamiltonian_forbiddenState] at happ
  have hforbidden : C.forbiddenState ≠ 0 := by
    intro h
    have hcoord := congrArg (fun ψ : C.HistorySpace => ψ.ofLp (Sum.inr 0)) h
    simp [forbiddenState, EuclideanSpace.basisFun_apply] at hcoord
  exact hforbidden (by simpa using happ)

/-! # C. Cell transitions and shared time/area spectra -/

/-- The finite time observable on the constrained history carrier. The clock
subspace has eigenvalues `k * deltaTime`; the ancillary direction reads zero. -/
def timeOperator (C : Calibration) : Matrix C.HistoryIndex C.HistoryIndex ℂ :=
  Matrix.diagonal fun i => match i with
    | Sum.inl k => (k : ℂ) * (C.deltaTime : ℂ)
    | Sum.inr _ => 0

/-- The cell-area observable on the same constrained history carrier. The
clock subspace has eigenvalues `k * deltaArea`; the ancillary direction reads zero. -/
def areaOperator (C : Calibration) : Matrix C.HistoryIndex C.HistoryIndex ℂ :=
  Matrix.diagonal fun i => match i with
    | Sum.inl k => (k : ℂ) * (C.deltaArea : ℂ)
    | Sum.inr _ => 0

/-- Coordinate form of a constrained history state. -/
def historyCoordinate (C : Calibration) (k : C.Level) : C.HistoryIndex → ℂ :=
  fun i => if i = Sum.inl k then 1 else 0

/-- The matrix coordinate of a history state is its standard basis vector. -/
lemma historyState_coordinate (C : Calibration) (k : C.Level) :
    (C.historyState k).ofLp = C.historyCoordinate k := by
  funext i
  simp [historyState, historyCoordinate, EuclideanSpace.basisFun_apply]

/-- On the clock subspace, the history time observable is exactly the earlier
quantized relational-time operator. -/
lemma timeOperator_clockRestriction (C : Calibration) (i j : C.Level) :
    C.timeOperator (Sum.inl i) (Sum.inl j) =
      entropicTimeOperator C.deltaTime (C.cellCount + 1) i j := by
  by_cases hij : i = j
  · subst hij
    simp [timeOperator, entropicTimeOperator]
  · have hsum : (Sum.inl i : C.HistoryIndex) ≠ Sum.inl j := by
      exact fun h => hij (Sum.inl_injective h)
    simp [timeOperator, entropicTimeOperator, hij, hsum]

/-- On the clock subspace, the history area observable is the same uniform-gap
diagonal family, instantiated with one counted cell area. -/
lemma areaOperator_clockRestriction (C : Calibration) (i j : C.Level) :
    C.areaOperator (Sum.inl i) (Sum.inl j) =
      entropicTimeOperator C.deltaArea (C.cellCount + 1) i j := by
  by_cases hij : i = j
  · subst hij
    simp [areaOperator, entropicTimeOperator]
  · have hsum : (Sum.inl i : C.HistoryIndex) ≠ Sum.inl j := by
      exact fun h => hij (Sum.inl_injective h)
    simp [areaOperator, entropicTimeOperator, hij, hsum]

/-- Every history coordinate is an eigenvector of the time observable with
eigenvalue `k * deltaTime`. -/
lemma timeOperator_eigenvector (C : Calibration) (k : C.Level) :
    C.timeOperator.mulVec (C.historyCoordinate k) =
      ((k : ℂ) * (C.deltaTime : ℂ)) • C.historyCoordinate k := by
  funext i
  rw [timeOperator, Matrix.mulVec_diagonal]
  by_cases h : i = Sum.inl k
  · subst h
    simp [historyCoordinate]
  · simp [historyCoordinate, h, Pi.smul_apply, smul_eq_mul]

/-- Every history coordinate is an eigenvector of the area observable with
eigenvalue `k * deltaArea`. -/
lemma areaOperator_eigenvector (C : Calibration) (k : C.Level) :
    C.areaOperator.mulVec (C.historyCoordinate k) =
      ((k : ℂ) * (C.deltaArea : ℂ)) • C.historyCoordinate k := by
  funext i
  rw [areaOperator, Matrix.mulVec_diagonal]
  by_cases h : i = Sum.inl k
  · subst h
    simp [historyCoordinate]
  · simp [historyCoordinate, h, Pi.smul_apply, smul_eq_mul]

/-- The actual constrained history state is a time-observable eigenstate whose
eigenvalue is exactly its relational clock reading. -/
lemma timeOperator_historyState_eigenvector (C : Calibration) (k : C.Level) :
    C.timeOperator.mulVec (C.historyState k).ofLp =
      (C.timeReading k : ℂ) • (C.historyState k).ofLp := by
  rw [C.historyState_coordinate]
  simpa [timeReading, timeLadder] using C.timeOperator_eigenvector k

/-- The same constrained history state is an area-observable eigenstate whose
eigenvalue is exactly its accumulated activated-cell area. -/
lemma areaOperator_historyState_eigenvector (C : Calibration) (k : C.Level) :
    C.areaOperator.mulVec (C.historyState k).ofLp =
      (C.areaReading k : ℂ) • (C.historyState k).ofLp := by
  rw [C.historyState_coordinate]
  simpa [areaReading] using C.areaOperator_eigenvector k

/-- One bounded clock transition advances the relational reading by exactly
the counted Planck/Compton crossing time. -/
lemma timeReading_step (C : Calibration) (k : Fin C.cellCount) :
    C.timeReading k.succ - C.timeReading k.castSucc = C.deltaTime := by
  unfold timeReading
  simpa [timeLadder] using C.timeLadder.reading_step_eq k

/-- One bounded clock transition advances the area reading by exactly one cell. -/
lemma areaReading_step (C : Calibration) (k : Fin C.cellCount) :
    C.areaReading k.succ - C.areaReading k.castSucc = C.deltaArea := by
  simpa [areaReading] using entropicTimeOperator_gap C.deltaArea k.val

/-- One transition activates exactly the cell whose label is the old level. -/
lemma prefixRegister_step (C : Calibration) (k i : Fin C.cellCount) :
    C.prefixRegister k.succ i = if i = k then true else C.prefixRegister k.castSucc i := by
  simp only [prefixRegister, Fin.val_succ, Fin.val_castSucc]
  by_cases hik : i = k
  · subst hik
    simp
  · have hval : i.val ≠ k.val := fun h => hik (Fin.ext h)
    rw [if_neg hik]
    exact Bool.decide_congr (by omega)

/-- Distinct bounded clock levels encode distinct finite cell registers. -/
lemma prefixRegister_injective (C : Calibration) : Function.Injective C.prefixRegister := by
  intro a b hab
  apply Fin.ext
  by_contra hval
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · let i : Fin C.cellCount := ⟨a.val, by omega⟩
    have hi := congrFun hab i
    simp [prefixRegister, i, hlt] at hi
  · let i : Fin C.cellCount := ⟨b.val, by omega⟩
    have hi := congrFun hab i
    simp [prefixRegister, i, hgt] at hi

/-- At the terminal clock level the accumulated cell area is the supplied
screen area. This is where agreement of the natural and effective counts enters. -/
lemma areaReading_final (C : Calibration) :
    C.areaReading C.finalLevel = C.base.screenArea := by
  unfold areaReading finalLevel deltaArea GFreeComptonCellCalibration.cellArea cellCount
  simp only [Fin.val_last]
  rw [C.count_agrees]
  field_simp [C.base.cellCount_pos.ne']

/-- At the terminal clock level every cell in the finite register is active. -/
lemma prefixRegister_final (C : Calibration) (i : Fin C.cellCount) :
    C.prefixRegister C.finalLevel i = true := by
  change decide (i.val < C.cellCount) = true
  exact (Bool.decide_iff _).2 i.isLt

/-! # D. The gravity scale selected by the clock gap -/

/-- The clock quantum is the inverse Compton angular frequency of the calibrated
screen mass. -/
lemma deltaTime_eq_inv_comptonFrequency (C : Calibration) :
    C.deltaTime =
      1 / comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar :=
  C.base.countedPlanckTime_eq_inv_comptonFrequency

/-- The time spectral gap satisfies the Planck-time equation for the constructed
G-free area-per-cell coupling. -/
lemma deltaTime_sq_eq_gravityCoupling (C : Calibration) :
    C.deltaTime ^ 2 =
      C.base.countedNewtonG * C.base.hbar / C.base.lightSpeed ^ 5 :=
  C.base.countedPlanckTime_sq_eq

/-- The gravitational coupling is uniquely readable from the squared clock gap. -/
lemma gravityCoupling_eq_from_deltaTime (C : Calibration) :
    C.base.countedNewtonG =
      C.base.lightSpeed ^ 5 * C.deltaTime ^ 2 / C.base.hbar := by
  rw [C.deltaTime_sq_eq_gravityCoupling]
  field_simp [C.base.hbar_pos.ne', C.base.lightSpeed_pos.ne']

/-- One time quantum crosses one counted Planck length. -/
lemma lightSpeed_mul_deltaTime_eq_countedPlanckLength (C : Calibration) :
    C.base.lightSpeed * C.deltaTime = C.base.countedPlanckLength := by
  unfold deltaTime GFreeComptonCellCalibration.countedPlanckTime
  field_simp [C.base.lightSpeed_pos.ne']

/-- The squared length crossed in one clock tick is the area quantum and equals
the Planck-area combination of the constructed coupling. -/
lemma tickLength_sq_eq_deltaArea_eq_gravityArea (C : Calibration) :
    (C.base.lightSpeed * C.deltaTime) ^ 2 = C.deltaArea
      ∧ C.deltaArea =
        C.base.countedNewtonG * C.base.hbar / C.base.lightSpeed ^ 3 := by
  constructor
  · rw [C.lightSpeed_mul_deltaTime_eq_countedPlanckLength]
    unfold deltaArea GFreeComptonCellCalibration.countedPlanckLength
    exact Real.sq_sqrt C.base.cellArea_pos.le
  · exact C.base.cellArea_eq_countedPlanckArea

/-- The calibrated screen energy times one relational clock quantum is exactly
one reduced action quantum `hbar`. -/
lemma screenEnergy_mul_deltaTime_eq_hbar (C : Calibration) :
    (C.base.screenMass * C.base.lightSpeed ^ 2) * C.deltaTime = C.base.hbar := by
  rw [C.base.screenMass_energy_eq_hbar_mul_comptonFrequency,
    C.deltaTime_eq_inv_comptonFrequency]
  have hω : comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar ≠ 0 := by
    unfold comptonFrequency
    exact div_ne_zero
      (mul_ne_zero C.base.screenMass_pos.ne'
        (pow_ne_zero 2 C.base.lightSpeed_pos.ne'))
      C.base.hbar_pos.ne'
  field_simp

/-! # E. Compton and de Broglie readings of the invariant tick -/

/-- The fixed-position interval over which a de Broglie phase of boost factor
`gamma` advances by one radian. -/
def deBrogliePhaseTick (C : Calibration) (gamma : ℝ) : ℝ :=
  C.deltaTime / gamma

/-- The coordinate-time interval over which the Compton phase advances by one
radian along a particle worldline of dimensionless velocity `beta`. -/
noncomputable def movingClockCoordinateTick (C : Calibration) (beta : ℝ) : ℝ :=
  C.deltaTime / Real.sqrt (1 - beta ^ 2)

/-- The plane-wave phase advance `(ω - kv) Delta t` evaluated along the group
trajectory `v = beta c`. -/
noncomputable def worldlinePhaseAdvance
    (omega0 c beta deltaT : ℝ) : ℝ :=
  GFreeComptonCellCalibration.worldlinePhaseAdvance omega0 c beta deltaT

/-- One invariant relational tick advances the rest Compton phase by one radian. -/
lemma comptonPhase_deltaTime_eq_one (C : Calibration) :
    comptonPhase C.base.screenMass C.base.lightSpeed C.base.hbar C.deltaTime = 1 := by
  unfold comptonPhase
  rw [C.deltaTime_eq_inv_comptonFrequency]
  have homega :
      comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar ≠ 0 := by
    unfold comptonFrequency
    exact div_ne_zero
      (mul_ne_zero C.base.screenMass_pos.ne'
        (pow_ne_zero 2 C.base.lightSpeed_pos.ne'))
      C.base.hbar_pos.ne'
  field_simp

/-! # E.1. Curved-worldline realization of the calibrated tick -/

section CurvedWorldline

open Bundle FiberBundle
open scoped Manifold
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.CurvedWorldlinePhase

universe v w

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M] [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- The relational clock gap constructed from counted screen data advances the
Levi--Civita covariant Compton phase by one radian on a calibrated geodesic. -/
@[zil_level bridge_theorem]
lemma curvedWorldlinePhase_deltaTime_eq_one
    (C : Calibration) (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : PseudoRiemannianMetric.IsLeviCivitaConnection I g cov)
    (P U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (hP : MDiff (T% P)) (hU : MDiff (T% U))
    (hpair : MDiff (fun x ↦ g.val x (P x) (U x)))
    (hγ : IsMIntegralCurve γ U)
    (hparallelP : ∀ x, cov P x (U x) = 0)
    (hgeodesic : ∀ x, cov U x (U x) = 0) (a : ℝ)
    (hmomentum : P (γ a) = C.base.screenMass • U (γ a))
    (hproper : g.val (γ a) (U (γ a)) (U (γ a)) = C.base.lightSpeed ^ 2) :
    curvedWorldlinePhase I g P U γ C.base.hbar a (a + C.deltaTime) = 1 := by
  rw [curvedWorldlinePhase_eq_comptonPhase I g cov hcov P U γ hP hU hpair hγ
    hparallelP hgeodesic C.base.screenMass C.base.lightSpeed C.base.hbar a
    (a + C.deltaTime) hmomentum hproper]
  simpa using C.comptonPhase_deltaTime_eq_one

/-- The same constructed event is simultaneously one radian of curved
Compton phase and one finite area-eigenvalue step, with the latter equal to the
Planck-area combination of the uniquely counted coupling. -/
@[zil_level bridge_theorem]
lemma curvedPhaseTick_areaQuantum_closure
    (C : Calibration) (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : PseudoRiemannianMetric.IsLeviCivitaConnection I g cov)
    (P U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (hP : MDiff (T% P)) (hU : MDiff (T% U))
    (hpair : MDiff (fun x ↦ g.val x (P x) (U x)))
    (hγ : IsMIntegralCurve γ U)
    (hparallelP : ∀ x, cov P x (U x) = 0)
    (hgeodesic : ∀ x, cov U x (U x) = 0) (a : ℝ)
    (hmomentum : P (γ a) = C.base.screenMass • U (γ a))
    (hproper : g.val (γ a) (U (γ a)) (U (γ a)) = C.base.lightSpeed ^ 2) :
    curvedWorldlinePhase I g P U γ C.base.hbar a (a + C.deltaTime) = 1
      ∧ (C.base.lightSpeed * C.deltaTime) ^ 2 = C.deltaArea
      ∧ C.deltaArea = C.base.countedNewtonG * C.base.hbar / C.base.lightSpeed ^ 3 :=
  ⟨curvedWorldlinePhase_deltaTime_eq_one I C g cov hcov P U γ hP hU hpair hγ
      hparallelP hgeodesic a hmomentum hproper,
    C.tickLength_sq_eq_deltaArea_eq_gravityArea⟩

/-- When four-momentum is constructed as `P = m U`, its differentiability,
parallel transport, and pointwise mass calibration follow from the velocity
field and geodesic equation. Thus no independent momentum-calibration
hypothesis remains in the curved phase/area closure. -/
@[zil_level bridge_theorem]
lemma massScaledCurvedPhaseTick_areaQuantum_closure
    (C : Calibration) (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : PseudoRiemannianMetric.IsLeviCivitaConnection I g cov)
    (U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (hU : MDiff (T% U))
    (hpair : MDiff (fun x ↦
      g.val x (C.base.screenMass • U x) (U x)))
    (hγ : IsMIntegralCurve γ U)
    (hgeodesic : ∀ x, cov U x (U x) = 0) (a : ℝ)
    (hproper : g.val (γ a) (U (γ a)) (U (γ a)) = C.base.lightSpeed ^ 2) :
    curvedWorldlinePhase I g (C.base.screenMass • U) U γ C.base.hbar
        a (a + C.deltaTime) = 1
      ∧ (C.base.lightSpeed * C.deltaTime) ^ 2 = C.deltaArea
      ∧ C.deltaArea = C.base.countedNewtonG * C.base.hbar / C.base.lightSpeed ^ 3 := by
  have hP : MDiff (T% (C.base.screenMass • U)) :=
    mdifferentiable_smul_const_section hU
  have hparallelP : ∀ x, cov (C.base.screenMass • U) x (U x) = 0 := by
    intro x
    rw [cov.isCovariantDerivativeOn.smul_const C.base.screenMass (hU x)]
    simp [hgeodesic x]
  exact ⟨curvedWorldlinePhase_deltaTime_eq_one I C g cov hcov
      (C.base.screenMass • U) U γ hP hU hpair hγ hparallelP hgeodesic a rfl hproper,
    C.tickLength_sq_eq_deltaArea_eq_gravityArea⟩

end CurvedWorldline

/-- At fixed position, the boosted de Broglie phase advances by one radian over
`deltaTime / gamma`. -/
lemma deBroglieFrequency_mul_phaseTick_eq_one
    (C : Calibration) (gamma : ℝ) (hgamma : gamma ≠ 0) :
    deBroglieFrequency
        (gamma * (C.base.screenMass * C.base.lightSpeed ^ 2)) C.base.hbar
      * C.deBrogliePhaseTick gamma = 1 := by
  rw [deBroglie_eq_gamma_compton]
  unfold deBrogliePhaseTick
  rw [C.deltaTime_eq_inv_comptonFrequency]
  have homega :
      comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar ≠ 0 := by
    unfold comptonFrequency
    exact div_ne_zero
      (mul_ne_zero C.base.screenMass_pos.ne'
        (pow_ne_zero 2 C.base.lightSpeed_pos.ne'))
      C.base.hbar_pos.ne'
  field_simp

/-- The dispersion module's boosted phase frequency is exactly the de Broglie
frequency of the calibrated screen mass at the corresponding total energy. -/
lemma phaseFrequency_eq_calibratedDeBroglieFrequency
    (C : Calibration) (beta : ℝ) :
    phaseFrequency
        (comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar) beta =
      deBroglieFrequency
        ((1 / Real.sqrt (1 - beta ^ 2))
          * (C.base.screenMass * C.base.lightSpeed ^ 2)) C.base.hbar := by
  rw [deBroglie_eq_gamma_compton]
  unfold phaseFrequency
  ring

/-- The boosted total energy times its fixed-position one-radian phase interval
is the same reduced action quantum `hbar`. -/
lemma boostedEnergy_mul_deBrogliePhaseTick_eq_hbar
    (C : Calibration) (gamma : ℝ) (hgamma : gamma ≠ 0) :
    (gamma * (C.base.screenMass * C.base.lightSpeed ^ 2))
        * C.deBrogliePhaseTick gamma = C.base.hbar := by
  unfold deBrogliePhaseTick
  calc
    gamma * (C.base.screenMass * C.base.lightSpeed ^ 2)
          * (C.deltaTime / gamma) =
        (C.base.screenMass * C.base.lightSpeed ^ 2) * C.deltaTime := by
          field_simp
    _ = C.base.hbar := C.screenEnergy_mul_deltaTime_eq_hbar

/-- Along the group trajectory, the de Broglie plane-wave phase rate is the
time-dilated Compton rate `omega0 * sqrt (1 - beta^2)`. -/
lemma worldlinePhaseRate_eq_timeDilation
    (omega0 c beta : ℝ) (hc : c ≠ 0) (hbeta : beta ^ 2 < 1) :
    phaseFrequency omega0 beta - phaseWavenumber omega0 c beta * (beta * c)
      = omega0 * Real.sqrt (1 - beta ^ 2) :=
  GFreeComptonCellCalibration.worldlinePhaseRate_eq_timeDilation
    omega0 c beta hc hbeta

/-- The moving clock accumulates one radian of phase over the coordinate-time
interval `deltaTime / sqrt (1 - beta^2)`, while its proper-time advance is the
invariant Compton tick. -/
lemma worldlinePhaseAdvance_movingClockCoordinateTick_eq_one
    (C : Calibration) (beta : ℝ) (hbeta : beta ^ 2 < 1) :
    worldlinePhaseAdvance
        (comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar)
        C.base.lightSpeed beta (C.movingClockCoordinateTick beta) = 1 := by
  unfold worldlinePhaseAdvance
    GFreeComptonCellCalibration.worldlinePhaseAdvance movingClockCoordinateTick
  rw [worldlinePhaseRate_eq_timeDilation _ _ _ C.base.lightSpeed_pos.ne' hbeta,
    C.deltaTime_eq_inv_comptonFrequency]
  have hs : Real.sqrt (1 - beta ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by linarith)).ne'
  have homega :
      comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar ≠ 0 := by
    unfold comptonFrequency
    exact div_ne_zero
      (mul_ne_zero C.base.screenMass_pos.ne'
        (pow_ne_zero 2 C.base.lightSpeed_pos.ne'))
      C.base.hbar_pos.ne'
  field_simp

/-- Multiplying the moving clock's coordinate-time tick by the special-
relativistic proper-time factor recovers the invariant Compton tick. -/
lemma movingClockCoordinateTick_mul_timeDilation_eq_deltaTime
    (C : Calibration) (beta : ℝ) (hbeta : beta ^ 2 < 1) :
    C.movingClockCoordinateTick beta * Real.sqrt (1 - beta ^ 2) = C.deltaTime := by
  unfold movingClockCoordinateTick
  have hs : Real.sqrt (1 - beta ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by linarith)).ne'
  field_simp

/-- Reading the invariant gravitational coupling through the fixed-position
de Broglie phase interval requires the compensating factor `gamma^2`. -/
lemma gravityCoupling_eq_from_deBrogliePhaseTick
    (C : Calibration) (gamma : ℝ) (hgamma : gamma ≠ 0) :
    C.base.countedNewtonG =
      gamma ^ 2 * C.base.lightSpeed ^ 5 * C.deBrogliePhaseTick gamma ^ 2
        / C.base.hbar := by
  rw [C.gravityCoupling_eq_from_deltaTime]
  unfold deBrogliePhaseTick
  field_simp

/-- Omitting the boost compensation from the fixed-position de Broglie phase
tick returns `countedNewtonG / gamma^2`, not the invariant coupling. -/
lemma naiveGravityCoupling_from_deBrogliePhaseTick
    (C : Calibration) (gamma : ℝ) (hgamma : gamma ≠ 0) :
    C.base.lightSpeed ^ 5 * C.deBrogliePhaseTick gamma ^ 2 / C.base.hbar =
      C.base.countedNewtonG / gamma ^ 2 := by
  rw [C.gravityCoupling_eq_from_deltaTime]
  unfold deBrogliePhaseTick
  field_simp

/-- Reading the invariant gravitational coupling through the moving clock's
coordinate-time interval requires the inverse time-dilation factor
`1 - beta^2`. -/
lemma gravityCoupling_eq_from_movingClockCoordinateTick
    (C : Calibration) (beta : ℝ) (hbeta : beta ^ 2 < 1) :
    C.base.countedNewtonG =
      C.base.lightSpeed ^ 5 * C.movingClockCoordinateTick beta ^ 2
        * (1 - beta ^ 2) / C.base.hbar := by
  rw [C.gravityCoupling_eq_from_deltaTime]
  unfold movingClockCoordinateTick
  have hs : Real.sqrt (1 - beta ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by linarith)).ne'
  have hsq : Real.sqrt (1 - beta ^ 2) ^ 2 = 1 - beta ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hone : 1 - beta ^ 2 ≠ 0 := ne_of_gt (by linarith)
  rw [div_pow, hsq]
  field_simp [hone, C.base.hbar_pos.ne']

/-- The invariant cell area written through a fixed-position de Broglie phase
interval carries the compensating spatial factor `gamma`. -/
lemma deltaArea_eq_from_deBrogliePhaseTick
    (C : Calibration) (gamma : ℝ) (hgamma : gamma ≠ 0) :
    C.deltaArea =
      (gamma * C.base.lightSpeed * C.deBrogliePhaseTick gamma) ^ 2 := by
  rw [← C.tickLength_sq_eq_deltaArea_eq_gravityArea.1]
  unfold deBrogliePhaseTick
  field_simp

/-- The invariant cell area written through a moving clock's coordinate-time
tick carries the proper-time factor `sqrt (1 - beta^2)`. -/
lemma deltaArea_eq_from_movingClockCoordinateTick
    (C : Calibration) (beta : ℝ) (hbeta : beta ^ 2 < 1) :
    C.deltaArea =
      (C.base.lightSpeed * C.movingClockCoordinateTick beta
        * Real.sqrt (1 - beta ^ 2)) ^ 2 := by
  rw [← C.tickLength_sq_eq_deltaArea_eq_gravityArea.1]
  unfold movingClockCoordinateTick
  have hs : Real.sqrt (1 - beta ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by linarith)).ne'
  field_simp

/-! # F. Compton--de Broglie clock closure -/

/-- The same invariant relational tick has a unit Compton phase, unit boosted
de Broglie phase after the appropriate coordinate reparametrization, and
boost-corrected gravitational coupling and area readings. -/
lemma comptonDeBroglieClock_closure (C : Calibration) :
    comptonPhase C.base.screenMass C.base.lightSpeed C.base.hbar C.deltaTime = 1
      ∧ (∀ gamma : ℝ, gamma ≠ 0 →
          deBroglieFrequency
              (gamma * (C.base.screenMass * C.base.lightSpeed ^ 2)) C.base.hbar
            * C.deBrogliePhaseTick gamma = 1)
      ∧ (∀ gamma : ℝ, gamma ≠ 0 →
          C.base.countedNewtonG =
            gamma ^ 2 * C.base.lightSpeed ^ 5 * C.deBrogliePhaseTick gamma ^ 2
              / C.base.hbar)
      ∧ (∀ beta : ℝ, beta ^ 2 < 1 →
          worldlinePhaseAdvance
              (comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar)
              C.base.lightSpeed beta (C.movingClockCoordinateTick beta) = 1)
      ∧ (∀ beta : ℝ, beta ^ 2 < 1 →
          C.base.countedNewtonG =
            C.base.lightSpeed ^ 5 * C.movingClockCoordinateTick beta ^ 2
              * (1 - beta ^ 2) / C.base.hbar) :=
  ⟨C.comptonPhase_deltaTime_eq_one,
    C.deBroglieFrequency_mul_phaseTick_eq_one,
    C.gravityCoupling_eq_from_deBrogliePhaseTick,
    C.worldlinePhaseAdvance_movingClockCoordinateTick_eq_one,
    C.gravityCoupling_eq_from_movingClockCoordinateTick⟩

end Calibration

end Physlib.QuantumMechanics.RelationalTime.PlanckCellRelationalClock

namespace Physlib.QuantumMechanics.RelationalTime.PlanckCellRelationalClock

open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.RelationalTime.QuantizedTime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.PropagatorTimeOperator
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.Relativity.Special

namespace Calibration

/-! # G. Finite-calibration compatibility API for rapidity geometry -/

/-- The coordinate-time duration of one moving clock tick at rapidity `theta`,
inherited from the G-free counted screen data. -/
noncomputable def rapidityCoordinateTick (C : Calibration) (theta : ℝ) : ℝ :=
  C.base.rapidityCoordinateTick theta

/-- The de Broglie four-momentum inherited from the G-free counted screen data. -/
noncomputable def deBroglieFourMomentum
    (C : Calibration) (beta : ℝ) : Lorentz.Vector 1 :=
  C.base.deBroglieFourMomentum beta

/-- The inertial worldline displacement inherited from the G-free counted
screen data. -/
def worldlineDisplacement
    (C : Calibration) (beta deltaT : ℝ) : Lorentz.Vector 1 :=
  C.base.worldlineDisplacement beta deltaT

/-- The Minkowski-paired phase inherited from the G-free counted screen data. -/
noncomputable def minkowskiWorldlinePhaseAdvance
    (C : Calibration) (beta deltaT : ℝ) : ℝ :=
  C.base.minkowskiWorldlinePhaseAdvance beta deltaT

/-- The finite-calibration rapidity tick is the standard Lorentz dilation of
the counted proper-time tick. -/
lemma rapidityCoordinateTick_eq_cosh_mul_deltaTime
    (C : Calibration) (theta : ℝ) :
    C.rapidityCoordinateTick theta = Real.cosh theta * C.deltaTime :=
  C.base.rapidityCoordinateTick_eq_cosh_mul_countedPlanckTime theta

/-- The temporal component of the inherited de Broglie momentum is
`m c cosh theta`. -/
lemma deBroglieFourMomentum_tanh_time
    (C : Calibration) (theta : ℝ) :
    C.deBroglieFourMomentum (Real.tanh theta) (Sum.inl 0) =
      C.base.screenMass * C.base.lightSpeed * Real.cosh theta :=
  C.base.deBroglieFourMomentum_tanh_time theta

/-- The spatial component of the inherited de Broglie momentum is
`m c sinh theta`. -/
lemma deBroglieFourMomentum_tanh_space
    (C : Calibration) (theta : ℝ) :
    C.deBroglieFourMomentum (Real.tanh theta) (Sum.inr 0) =
      C.base.screenMass * C.base.lightSpeed * Real.sinh theta :=
  C.base.deBroglieFourMomentum_tanh_space theta

/-- The inherited de Broglie momentum lies on the Minkowski mass shell. -/
lemma deBroglieFourMomentum_tanh_massShell
    (C : Calibration) (theta : ℝ) :
    Lorentz.Vector.minkowskiProduct
        (C.deBroglieFourMomentum (Real.tanh theta))
        (C.deBroglieFourMomentum (Real.tanh theta)) =
      (C.base.screenMass * C.base.lightSpeed) ^ 2 :=
  C.base.deBroglieFourMomentum_tanh_massShell theta

/-- The scalar plane-wave phase equals the inherited Minkowski four-pairing. -/
lemma minkowskiWorldlinePhaseAdvance_eq_worldlinePhaseAdvance
    (C : Calibration) (beta deltaT : ℝ) :
    C.minkowskiWorldlinePhaseAdvance beta deltaT =
      worldlinePhaseAdvance
        (comptonFrequency C.base.screenMass C.base.lightSpeed C.base.hbar)
        C.base.lightSpeed beta deltaT :=
  C.base.minkowskiWorldlinePhaseAdvance_eq_worldlinePhaseAdvance beta deltaT

/-- The inherited Minkowski phase advances by one radian over one rapidity tick. -/
lemma minkowskiWorldlinePhaseAdvance_rapidityTick_eq_one
    (C : Calibration) (theta : ℝ) :
    C.minkowskiWorldlinePhaseAdvance (Real.tanh theta)
      (C.rapidityCoordinateTick theta) = 1 :=
  C.base.minkowskiWorldlinePhaseAdvance_rapidityTick_eq_one theta

/-- The inherited rapidity displacement has the counted Compton proper time. -/
lemma properTime_rapidityTick_eq_lightSpeed_mul_deltaTime
    (C : Calibration) (theta : ℝ) :
    SpaceTime.properTime 0
        (C.worldlineDisplacement (Real.tanh theta)
          (C.rapidityCoordinateTick theta)) =
      C.base.lightSpeed * C.deltaTime :=
  C.base.properTime_rapidityTick_eq_lightSpeed_mul_countedPlanckTime theta

/-- The inherited straight-worldline proper-time integral has the counted
Compton proper time. -/
lemma properTimeIntegral_rapidityTick_eq_lightSpeed_mul_deltaTime
    (C : Calibration) (theta : ℝ) :
    SpaceTime.properTimeIntegral
        (fun lam => lam • C.worldlineDisplacement (Real.tanh theta)
          (C.rapidityCoordinateTick theta)) 1 =
      C.base.lightSpeed * C.deltaTime :=
  C.base.properTimeIntegral_rapidityTick_eq_lightSpeed_mul_countedPlanckTime theta

/-- The constructed coupling depends only on the proper-time part of the
rapidity coordinate tick. -/
lemma gravityCoupling_eq_from_rapidityCoordinateTick
    (C : Calibration) (theta : ℝ) :
    C.base.countedNewtonG =
      C.base.lightSpeed ^ 5 *
          (C.rapidityCoordinateTick theta / Real.cosh theta) ^ 2 /
        C.base.hbar := by
  rw [C.gravityCoupling_eq_from_deltaTime,
    C.rapidityCoordinateTick_eq_cosh_mul_deltaTime]
  field_simp [(Real.cosh_pos theta).ne']

/-- The area carried by the rapidity tick is the inherited G-free cell area. -/
lemma deltaArea_eq_from_rapidityCoordinateTick
    (C : Calibration) (theta : ℝ) :
    C.deltaArea =
      (C.base.lightSpeed *
        (C.rapidityCoordinateTick theta / Real.cosh theta)) ^ 2 :=
  (C.base.rapidityTickLength_sq_eq_cellArea theta).symm

/-! # H. Physical rapidity capstone -/

/-- Every finite calibration inherits the G-free rapidity mass-shell, phase,
proper-time, coupling, and area identities without using its finite tiling. -/
lemma rapidityMinkowskiClock_closure (C : Calibration) (theta : ℝ) :
    C.rapidityCoordinateTick theta = Real.cosh theta * C.deltaTime
      ∧ Lorentz.Vector.minkowskiProduct
          (C.deBroglieFourMomentum (Real.tanh theta))
          (C.deBroglieFourMomentum (Real.tanh theta)) =
        (C.base.screenMass * C.base.lightSpeed) ^ 2
      ∧ SpaceTime.properTimeIntegral
          (fun lam => lam • C.worldlineDisplacement (Real.tanh theta)
            (C.rapidityCoordinateTick theta)) 1 =
        C.base.lightSpeed * C.deltaTime
      ∧ C.minkowskiWorldlinePhaseAdvance (Real.tanh theta)
          (C.rapidityCoordinateTick theta) = 1
      ∧ C.base.countedNewtonG =
        C.base.lightSpeed ^ 5 *
            (C.rapidityCoordinateTick theta / Real.cosh theta) ^ 2 /
          C.base.hbar
      ∧ C.deltaArea =
        (C.base.lightSpeed *
          (C.rapidityCoordinateTick theta / Real.cosh theta)) ^ 2 :=
  ⟨C.rapidityCoordinateTick_eq_cosh_mul_deltaTime theta,
    C.deBroglieFourMomentum_tanh_massShell theta,
    C.properTimeIntegral_rapidityTick_eq_lightSpeed_mul_deltaTime theta,
    C.minkowskiWorldlinePhaseAdvance_rapidityTick_eq_one theta,
    C.gravityCoupling_eq_from_rapidityCoordinateTick theta,
    C.deltaArea_eq_from_rapidityCoordinateTick theta⟩

/-- The finite-calibration statement is definitionally the G-free Minkowski
rapidity phase, proper-time, and area-quantum closure. -/
@[zil_level bridge_theorem]
lemma rapidityMinkowskiPhaseTick_areaQuantum_closure
    (C : Calibration) (theta : ℝ) :
    C.minkowskiWorldlinePhaseAdvance (Real.tanh theta)
        (C.rapidityCoordinateTick theta) = 1
      ∧ SpaceTime.properTimeIntegral
          (fun lam => lam • C.worldlineDisplacement (Real.tanh theta)
            (C.rapidityCoordinateTick theta)) 1 =
        C.base.lightSpeed * C.deltaTime
      ∧ (C.base.lightSpeed *
          (C.rapidityCoordinateTick theta / Real.cosh theta)) ^ 2 = C.deltaArea
      ∧ C.deltaArea =
        C.base.countedNewtonG * C.base.hbar / C.base.lightSpeed ^ 3 :=
  C.base.rapidityMinkowskiPhaseTick_areaQuantum_closure theta

/-! # I. Nagao--Nielsen cone and Misra-age sampling -/

/-- The 1+1 de Broglie four-momentum represented as the Nagao--Nielsen complex
coordinate `p0 + i p1`. -/
noncomputable def nagaoNielsenFourMomentum
    (C : Calibration) (theta : ℝ) : ℂ :=
  ⟨C.deBroglieFourMomentum (Real.tanh theta) (Sum.inl 0),
    C.deBroglieFourMomentum (Real.tanh theta) (Sum.inr 0)⟩

/-- The Nagao--Nielsen convergence form of the complex momentum coordinate is
exactly the Minkowski self-pairing of the reconstructed Lorentz vector. -/
lemma nagaoNielsenFourMomentum_form_eq_minkowski
    (C : Calibration) (theta : ℝ) :
    nnLorentzForm (C.nagaoNielsenFourMomentum theta) =
      Lorentz.Vector.minkowskiProduct
        (C.deBroglieFourMomentum (Real.tanh theta))
        (C.deBroglieFourMomentum (Real.tanh theta)) := by
  rw [Lorentz.Vector.minkowskiProduct_toCoord]
  simp [nagaoNielsenFourMomentum, nnLorentzForm]
  ring

/-- The Nagao--Nielsen complex representation of the physical de Broglie
four-momentum lies on the same mass shell `(mc)^2`. -/
lemma nagaoNielsenFourMomentum_massShell
    (C : Calibration) (theta : ℝ) :
    nnLorentzForm (C.nagaoNielsenFourMomentum theta) =
      (C.base.screenMass * C.base.lightSpeed) ^ 2 := by
  rw [C.nagaoNielsenFourMomentum_form_eq_minkowski,
    C.deBroglieFourMomentum_tanh_massShell]

/-- Positivity of the calibrated mass and light speed places every rapidity
momentum inside the Nagao--Nielsen convergence cone. -/
lemma nagaoNielsenFourMomentum_converges
    (C : Calibration) (theta : ℝ) :
    nnConverges (C.nagaoNielsenFourMomentum theta) := by
  unfold nnConverges
  rw [C.nagaoNielsenFourMomentum_massShell]
  exact sq_pos_of_pos (mul_pos C.base.screenMass_pos C.base.lightSpeed_pos)

/-- The continuum Feynman spectral kernel sampled at the finite clock reading
`t_k`, using the Misra convention whose age eigenvalue is `t / hbar`. -/
noncomputable def misraHistoryKernel
    (C : Calibration) (k : C.Level) : ℝ → ℂ :=
  fpiSpectralKernel C.base.hbar (C.base.hbar * C.timeReading k)

/-- The Misra age operator reads exactly the finite relational-clock value on
the sampled Feynman kernel. -/
lemma misraHistoryKernel_age_eigen
    (C : Calibration) (k : C.Level) (lam : ℝ) :
    ageOperator (C.misraHistoryKernel k) lam =
      (C.timeReading k : ℂ) * C.misraHistoryKernel k lam := by
  unfold misraHistoryKernel
  rw [fpi_ageOperator_eigen]
  congr 1
  push_cast
  field_simp [C.base.hbar_pos.ne']

/-- Adjacent age coefficients sampled by the finite history retain the same
uniform gap `deltaTime` as the diagonal relational clock. -/
lemma misraHistoryKernel_age_gap
    (C : Calibration) (k : Fin C.cellCount) :
    (C.timeReading k.succ : ℂ) - (C.timeReading k.castSucc : ℂ) =
      (C.deltaTime : ℂ) := by
  exact_mod_cast C.timeReading_step k

/-- Both adjacent sampled Feynman kernels are Misra age eigenkernels, and their
eigenvalues differ by exactly the finite relational-clock gap. -/
lemma misraHistoryKernel_adjacent_age_eigen
    (C : Calibration) (k : Fin C.cellCount) (lam : ℝ) :
    ageOperator (C.misraHistoryKernel k.succ) lam =
        (C.timeReading k.succ : ℂ) * C.misraHistoryKernel k.succ lam
      ∧ ageOperator (C.misraHistoryKernel k.castSucc) lam =
        (C.timeReading k.castSucc : ℂ) *
          C.misraHistoryKernel k.castSucc lam
      ∧ (C.timeReading k.succ : ℂ) -
          (C.timeReading k.castSucc : ℂ) = (C.deltaTime : ℂ) :=
  ⟨C.misraHistoryKernel_age_eigen k.succ lam,
    C.misraHistoryKernel_age_eigen k.castSucc lam,
    C.misraHistoryKernel_age_gap k⟩

/-- One positive relational tick, represented in the Misra convention as
Feynman time `hbar * deltaTime`, is a future-pointing timelike age coordinate. -/
lemma misraOneTick_timelikeFuture (C : Calibration) :
    timelikeFuture
      ((((C.base.hbar * C.deltaTime) / C.base.hbar : ℝ) : ℂ) +
        ((0 : ℝ) : ℂ) * Complex.I) := by
  apply misraAge_timelikeFuture C.base.hbar
      (C.base.hbar * C.deltaTime) 0 C.base.hbar_pos
    (mul_pos C.base.hbar_pos C.timeLadder.δ_τ_pos)
  have hquot : 0 < C.base.hbar * C.deltaTime / C.base.hbar := by
    rw [mul_div_cancel_left₀ _ C.base.hbar_pos.ne']
    exact C.timeLadder.δ_τ_pos
  simpa using hquot

/-! # J. Nagao--Nielsen and Misra capstone -/

/-- The rapidity clock has one common flat Lorentzian carrier: its explicit
Minkowski and Nagao--Nielsen mass shells agree, the NN contour converges, and
the continuum Misra kernel samples each finite clock reading with the same
adjacent age gap. -/
lemma nagaoNielsenMisraClock_closure
    (C : Calibration) (theta : ℝ) (k : Fin C.cellCount) (lam : ℝ) :
    nnLorentzForm (C.nagaoNielsenFourMomentum theta) =
        Lorentz.Vector.minkowskiProduct
          (C.deBroglieFourMomentum (Real.tanh theta))
          (C.deBroglieFourMomentum (Real.tanh theta))
      ∧ nnLorentzForm (C.nagaoNielsenFourMomentum theta) =
        (C.base.screenMass * C.base.lightSpeed) ^ 2
      ∧ nnConverges (C.nagaoNielsenFourMomentum theta)
      ∧ ageOperator (C.misraHistoryKernel k.succ) lam =
        (C.timeReading k.succ : ℂ) * C.misraHistoryKernel k.succ lam
      ∧ ageOperator (C.misraHistoryKernel k.castSucc) lam =
        (C.timeReading k.castSucc : ℂ) * C.misraHistoryKernel k.castSucc lam
      ∧ (C.timeReading k.succ : ℂ) -
          (C.timeReading k.castSucc : ℂ) = (C.deltaTime : ℂ) :=
  ⟨C.nagaoNielsenFourMomentum_form_eq_minkowski theta,
    C.nagaoNielsenFourMomentum_massShell theta,
    C.nagaoNielsenFourMomentum_converges theta,
    C.misraHistoryKernel_age_eigen k.succ lam,
    C.misraHistoryKernel_age_eigen k.castSucc lam,
    C.misraHistoryKernel_age_gap k⟩

/-- The bounded history simultaneously has a uniform time gap, uniform cell-area
gap, nonzero constraint, and G-free gravitational closure. -/
lemma planckCellRelationalClock_closure (C : Calibration) :
    C.historyHamiltonian ≠ 0
      ∧ Orthonormal ℂ C.historyState
      ∧ (∀ k : C.Level, C.constraint.IsPhysical (C.historyState k))
      ∧ Function.Injective C.prefixRegister
      ∧ (∀ k : Fin C.cellCount,
          C.timeReading k.succ - C.timeReading k.castSucc = C.deltaTime)
      ∧ (∀ k : Fin C.cellCount,
          C.areaReading k.succ - C.areaReading k.castSucc = C.deltaArea)
      ∧ C.areaReading C.finalLevel = C.base.screenArea
      ∧ C.base.countedNewtonG =
          C.base.lightSpeed ^ 5 * C.deltaTime ^ 2 / C.base.hbar
      ∧ C.deltaArea =
          C.base.countedNewtonG * C.base.hbar / C.base.lightSpeed ^ 3
      ∧ (C.base.screenMass * C.base.lightSpeed ^ 2) * C.deltaTime = C.base.hbar :=
  ⟨C.historyHamiltonian_ne_zero,
    C.historyState_orthonormal,
    C.historyState_physical,
    C.prefixRegister_injective,
    C.timeReading_step,
    C.areaReading_step,
    C.areaReading_final,
    C.gravityCoupling_eq_from_deltaTime,
    C.tickLength_sq_eq_deltaArea_eq_gravityArea.2,
    C.screenEnergy_mul_deltaTime_eq_hbar⟩

end Calibration

end Physlib.QuantumMechanics.RelationalTime.PlanckCellRelationalClock

end

open Physlib.QuantumMechanics.RelationalTime.PlanckCellRelationalClock in
#physlib_axiom_clean_all [
  Calibration.exists_calibration_of_positive_data,
  Calibration.massScaledCurvedPhaseTick_areaQuantum_closure,
  Calibration.rapidityMinkowskiPhaseTick_areaQuantum_closure ]

open Physlib.QuantumMechanics.RelationalTime.PlanckCellRelationalClock in
#physlib_non_vacuous_all [
  Calibration.exists_calibration_of_positive_data,
  Calibration.massScaledCurvedPhaseTick_areaQuantum_closure,
  Calibration.rapidityMinkowskiPhaseTick_areaQuantum_closure ]

/-! # ZIL metadata -/

/- ZIL-BEGIN -/

namespace Physlib.QuantumMechanics.RelationalTime.PlanckCellRelationalClock

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

zil attach Calibration.exists_calibration_of_positive_data where
  formalizes @ "claim:positive-screen-area-positive-natural-cell-count-light-\
speed-and-hbar-construct-a-complete-finite-relational-clock-calibration",
  epistemic_status @ "mathematical-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.GFreeComptonCellCalibration.\
exists_finiteTiling_of_natCount",
  caveat @ "epistemic:existence-removes-the-tiling-witness-as-an-extra-lean-\
hypothesis-but-does-not-predict-the-supplied-positive-area-or-natural-count"

zil attach Calibration.curvedWorldlinePhase_deltaTime_eq_one where
  formalizes @ "claim:the-count-constructed-relational-clock-gap-advances-the-\
levi-civita-covariant-compton-phase-by-one-radian-on-a-curved-geodesic",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
CurvedWorldlinePhase.curvedWorldlinePhase_eq_comptonPhase",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.\
PlanckCellRelationalClock.Calibration.comptonPhase_deltaTime_eq_one"

zil attach Calibration.curvedPhaseTick_areaQuantum_closure where
  formalizes @ "claim:one-curved-geodesic-compton-phase-tick-is-simultaneously-\
one-finite-area-eigenvalue-step-equal-to-the-planck-area-combination-of-the-\
count-constructed-coupling",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.\
PlanckCellRelationalClock.Calibration.curvedWorldlinePhase_deltaTime_eq_one",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.\
PlanckCellRelationalClock.Calibration.tickLength_sq_eq_deltaArea_eq_gravityArea",
  caveat @ "epistemic:this-is-a-kinematical-clock-area-spectrum-on-a-supplied-\
levi-civita-background-not-a-graviton-or-metric-field-quantization"

zil attach Calibration.massScaledCurvedPhaseTick_areaQuantum_closure where
  formalizes @ "claim:constructing-four-momentum-as-mass-times-four-velocity-\
removes-independent-momentum-differentiability-parallel-transport-and-\
pointwise-calibration-hypotheses-from-the-curved-compton-phase-area-closure",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:CovariantDerivative.isCovariantDerivativeOn",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.\
PlanckCellRelationalClock.Calibration.curvedWorldlinePhase_deltaTime_eq_one",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.\
PlanckCellRelationalClock.Calibration.tickLength_sq_eq_deltaArea_eq_gravityArea",
  caveat @ "epistemic:the-levi-civita-background-geodesic-integral-curve-\
regularity-and-proper-time-normalization-remain-geometric-hypotheses-not-\
screen-calibration-inputs"

zil attach Calibration.historyHamiltonian_ne_zero where
  formalizes @ "claim:the-planck-cell-history-states-lie-in-the-kernel-of-a-\
genuinely-nonzero-page-wootters-hamiltonian-constraint",
  epistemic_status @ "conditional-model",
  caveat @ "epistemic:the-ancillary-projection-is-an-explicit-finite-model-not-a-\
derivation-of-the-wheeler-dewitt-hamiltonian"

zil attach Calibration.gravityCoupling_eq_from_deltaTime where
  formalizes @ "claim:the-g-free-area-per-cell-gravitational-coupling-is-c-to-\
the-fifth-times-the-squared-relational-clock-gap-over-hbar",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.GFreeComptonCellCalibration.countedPlanckTime_sq_eq",
  caveat @ "epistemic:this-selects-one-coupling-from-a-supplied-clock-gap-and-\
cell-calibration-it-does-not-give-newton-g-a-discrete-spectrum"

zil attach Calibration.worldlinePhaseAdvance_movingClockCoordinateTick_eq_one where
  formalizes @ "claim:the-de-broglie-plane-wave-phase-advances-by-one-radian-\
along-the-group-velocity-worldline-over-the-time-dilated-coordinate-interval",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
DeBroglieDispersionComptonAnchor.groupVelocity_eq_particleVelocity",
  caveat @ "epistemic:the-fixed-position-de-broglie-phase-frequency-and-the-\
moving-clock-rate-are-distinct-operational-readings"

zil attach Calibration.naiveGravityCoupling_from_deBrogliePhaseTick where
  formalizes @ "claim:using-the-inverse-boosted-de-broglie-frequency-as-if-it-\
were-the-invariant-compton-tick-returns-the-counted-coupling-divided-by-gamma-squared",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
FrequencyTrinity.deBroglie_eq_gamma_compton",
  caveat @ "epistemic:a-boosted-de-broglie-phase-period-cannot-replace-the-\
proper-compton-tick-without-the-explicit-gamma-squared-compensation"

zil attach Calibration.comptonDeBroglieClock_closure where
  formalizes @ "claim:one-invariant-compton-proper-time-tick-has-unit-rest-\
phase-unit-boosted-de-broglie-phase-after-coordinate-reparametrization-and-\
boost-corrected-gravity-readings",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
FrequencyTrinity.deBroglie_eq_gamma_compton",
  caveat @ "epistemic:this-is-covariant-clock-bookkeeping-for-the-constructed-\
coupling-not-a-velocity-dependent-newton-constant"

zil attach Calibration.deBroglieFourMomentum_tanh_massShell where
  formalizes @ "claim:the-rapidity-parametrized-de-broglie-four-momentum-lies-\
on-the-one-plus-one-dimensional-minkowski-mass-shell",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Relativity.Special.HyperbolicBoost.\
gamma_tanh_eq_cosh",
  caveat @ "epistemic:this-is-a-flat-inertial-mass-shell-identity-not-a-curved-\
spacetime-field-equation"

zil attach Calibration.rapidityMinkowskiClock_closure where
  formalizes @ "claim:a-physical-rapidity-tick-simultaneously-has-lorentz-\
coordinate-dilation-on-shell-de-broglie-four-momentum-straight-worldline-\
proper-time-unit-minkowski-phase-and-proper-time-compensated-coupling-and-area",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Relativity.Special.SpaceTime.\
properTimeIntegral_straight",
  caveat @ "epistemic:this-fully-constructed-flat-inertial-realization-is-not-\
a-quantization-of-the-gravitational-field"

zil attach Calibration.rapidityMinkowskiPhaseTick_areaQuantum_closure where
  formalizes @ "claim:the-finite-clock-calibration-inherits-the-g-free-\
constructed-minkowski-rapidity-phase-proper-time-and-area-quantum-closure",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.GFreeComptonCellCalibration.\
rapidityMinkowskiPhaseTick_areaQuantum_closure",
  caveat @ "epistemic:the-proof-uses-only-the-base-g-free-calibration-the-finite-\
tiling-and-natural-count-agreement-fields-are-not-premises-of-this-result"

zil attach Calibration.nagaoNielsenFourMomentum_form_eq_minkowski where
  formalizes @ "claim:the-nagao-nielsen-one-plus-one-complex-momentum-form-is-\
exactly-the-minkowski-self-pairing-of-the-reconstructed-de-broglie-lorentz-vector",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
NagaoNielsenMassShellCone.nnLorentzForm",
  caveat @ "epistemic:this-identifies-the-flat-quadratic-carriers-it-does-not-\
derive-the-nagao-nielsen-contour-integral"

zil attach Calibration.nagaoNielsenMisraClock_closure where
  formalizes @ "claim:the-finite-rapidity-clock-has-the-same-mass-shell-in-\
minkowski-and-nagao-nielsen-coordinates-and-its-readings-sample-continuum-\
misra-age-eigenkernels-with-the-same-adjacent-gap",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.\
NonHermitianComplexAction.PropagatorTimeOperator.fpi_ageOperator_eigen",
  caveat @ "epistemic:this-is-an-explicit-sampling-map-into-continuum-\
generalized-eigenkernels-not-an-exact-ccr-on-the-finite-clock-matrix"

zil attach Calibration.planckCellRelationalClock_closure where
  formalizes @ "claim:a-finite-planck-cell-history-has-orthogonal-clock-levels-\
a-nonzero-constraint-one-cell-and-one-crossing-time-per-step-and-a-g-free-\
planck-area-gravity-closure",
  epistemic_status @ "conditional-model",
  requires @ "assumption:one-causally-ordered-cell-activation-is-one-clock-event",
  caveat @ "epistemic:this-is-a-planck-cell-relational-clock-not-a-graviton-or-\
quantization-of-the-gravitational-field"

zil_file_contract physlib.planckCellRelationalClock where
  promises "An actual finite Compton-cell partition is linked to a bounded \
relational clock on orthonormal history levels. The calibration object itself is \
constructed from any positive area, positive natural count, light speed, and hbar; \
the inverse-calibrated mass proves the exact finite tiling equation. Every history \
state lies in the \
kernel of an explicitly nonzero Hamiltonian constraint, and the time and area \
observables are diagonal on the same level labels with uniform gaps equal to \
the counted cell crossing time and counted cell area. The G-free Planck--Compton \
closure then reads the constructed gravitational coupling from the squared time \
gap, identifies one tick-length squared with the area quantum, and gives one \
reduced action quantum from screen energy times tick duration. The invariant gap \
is one radian of Compton phase. Its fixed-position de Broglie reading is shorter \
by gamma, whereas the coordinate interval along the particle worldline is longer \
by gamma; the coupling and area rewrites retain the compensating boost factors. \
For the physical specialization beta equals tanh theta and gamma equals cosh \
theta: an explicit one-plus-one-dimensional de Broglie four-momentum obeys the \
Minkowski mass shell, its pairing with the inertial worldline gives the scalar \
phase, and the straight-worldline proper-time integral returns the invariant \
Compton tick length. This entire rapidity closure is first proved on the G-free \
counted screen data; the finite calibration theorem inherits it by definitional \
reduction, without using a finite tiling or natural-count agreement. Encoding the \
same four-momentum as a Nagao--Nielsen complex coordinate gives exactly the same \
mass shell and lies in its convergence \
cone. Each finite clock reading also samples a continuum Feynman spectral kernel \
whose Misra age eigenvalue is that reading, so adjacent sampled ages retain the \
finite clock gap. On a Levi-Civita geodesic the same calibrated gap advances the \
covariant Compton phase by one radian and is simultaneously one finite area-\
eigenvalue step equal to the counted Planck-area combination. When momentum is \
constructed as mass times four-velocity, its differentiability, parallel transport, \
and pointwise mass calibration are proved from velocity regularity and the geodesic \
equation rather than supplied separately."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.RelationalTime.QuantizedTime.\
entropicTimeOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.FiniteComptonScreenTiling",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.GFreeComptonCellCalibration.countedCell_planckComptonClosure"]
  forbids_substitutes ["a graviton construction or quantization of the \
gravitational field",
    "a discrete spectrum for Newton's constant",
    "derivation of one-cell-per-event dynamics from a continuum Hamiltonian",
    "substituting one over the boosted de Broglie frequency for the invariant \
Compton proper-time tick without its gamma-squared compensation",
    "calling the fixed-position de Broglie phase frequency the rate of a clock \
moving on the particle worldline",
    "interpreting the free beta algebraic identities as a Lorentz clock without \
the physical subluminal or rapidity specialization",
    "dropping the Levi-Civita, geodesic, or timelike-normalization hypotheses \
from the curved worldline phase theorem; the generic theorem also requires \
parallel momentum unless momentum is constructed by the mass-scaled specialization",
    "reading the Misra generalized-eigenkernel sampling as an exact canonical \
commutator or spectral embedding on the finite clock matrix",
    "claiming the Nagao--Nielsen quadratic-form identity derives its analytic \
contour integral or convergence theorem",
    "claiming a finite tiling or natural-count agreement is required for the \
G-free Minkowski rapidity phase and area closure",
    "identifying one Planck-area mode with one Bekenstein bit without the \
four-log-two entropy normalization"]
  witnessed_by [Calibration.exists_calibration_of_positive_data,
    Calibration.clockKet_orthonormal,
    Calibration.historyState_orthonormal,
    Calibration.historyState_physical,
    Calibration.historyHamiltonian_ne_zero,
    Calibration.timeOperator_clockRestriction,
    Calibration.areaOperator_clockRestriction,
    Calibration.timeOperator_eigenvector,
    Calibration.areaOperator_eigenvector,
    Calibration.timeOperator_historyState_eigenvector,
    Calibration.areaOperator_historyState_eigenvector,
    Calibration.prefixRegister_step,
    Calibration.gravityCoupling_eq_from_deltaTime,
    Calibration.tickLength_sq_eq_deltaArea_eq_gravityArea,
    Calibration.screenEnergy_mul_deltaTime_eq_hbar,
    Calibration.comptonPhase_deltaTime_eq_one,
    Calibration.curvedWorldlinePhase_deltaTime_eq_one,
    Calibration.curvedPhaseTick_areaQuantum_closure,
    Calibration.massScaledCurvedPhaseTick_areaQuantum_closure,
    Calibration.deBroglieFrequency_mul_phaseTick_eq_one,
    Calibration.phaseFrequency_eq_calibratedDeBroglieFrequency,
    Calibration.boostedEnergy_mul_deBrogliePhaseTick_eq_hbar,
    Calibration.worldlinePhaseRate_eq_timeDilation,
    Calibration.worldlinePhaseAdvance_movingClockCoordinateTick_eq_one,
    Calibration.movingClockCoordinateTick_mul_timeDilation_eq_deltaTime,
    Calibration.gravityCoupling_eq_from_deBrogliePhaseTick,
    Calibration.naiveGravityCoupling_from_deBrogliePhaseTick,
    Calibration.gravityCoupling_eq_from_movingClockCoordinateTick,
    Calibration.deltaArea_eq_from_deBrogliePhaseTick,
    Calibration.deltaArea_eq_from_movingClockCoordinateTick,
    Calibration.comptonDeBroglieClock_closure,
    GFreeComptonCellCalibration.rapidityMinkowskiPhaseTick_areaQuantum_closure,
    Calibration.rapidityCoordinateTick_eq_cosh_mul_deltaTime,
    Calibration.deBroglieFourMomentum_tanh_massShell,
    Calibration.minkowskiWorldlinePhaseAdvance_eq_worldlinePhaseAdvance,
    Calibration.properTimeIntegral_rapidityTick_eq_lightSpeed_mul_deltaTime,
    Calibration.minkowskiWorldlinePhaseAdvance_rapidityTick_eq_one,
    Calibration.gravityCoupling_eq_from_rapidityCoordinateTick,
    Calibration.deltaArea_eq_from_rapidityCoordinateTick,
    Calibration.rapidityMinkowskiClock_closure,
    Calibration.rapidityMinkowskiPhaseTick_areaQuantum_closure,
    Calibration.nagaoNielsenFourMomentum_form_eq_minkowski,
    Calibration.nagaoNielsenFourMomentum_massShell,
    Calibration.nagaoNielsenFourMomentum_converges,
    Calibration.misraHistoryKernel_age_eigen,
    Calibration.misraHistoryKernel_age_gap,
    Calibration.misraHistoryKernel_adjacent_age_eigen,
    Calibration.misraOneTick_timelikeFuture,
    Calibration.nagaoNielsenMisraClock_closure,
    Calibration.planckCellRelationalClock_closure]

end Physlib.QuantumMechanics.RelationalTime.PlanckCellRelationalClock

/- ZIL-END -/

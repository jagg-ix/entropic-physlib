/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ConcreteSynthesis
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DeLaCruzFermionDoubleCopyGravityOnly
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT

/-!
# Chern-Simons Graviton Double Copy

This file records the algebraic core of Liu-Yi-He,
*Structure of Chern-Simons Graviton Scattering Amplitudes from Topological
Graviton Equivalence Theorem and Double Copy* (arXiv:2512.10870v3).

The paper's analytic work is organized around a few exact statements which are
already compatible with the repository's BCJ/color-kinematics and
Chern-Simons/topological-mass infrastructure:

* the high-energy topological graviton equivalence theorem (TGRET), whose
  four-point leading factor is `(1/2)^4 = 1/16`;
* the three-point replacement `g ↦ κ/4`, `f^{abc} ↦ N_A`;
* the four-point massive Chern-Simons graviton amplitude obtained by replacing
  color factors with a second copy of the kinematic numerators;
* the topological mass inherited from the existing DJT/Chern-Simons bridge.

The file is deliberately algebraic: it proves that, once the stated paper-level
assumptions are supplied, the advertised leading-amplitude and double-copy
conclusions follow in Lean.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.GravitonDoubleCopy

open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
open MeasureTheory

/-- Gauge choices used for the explicit four-graviton power-counting statements. -/
inductive GravitationalGauge where
  | landau
  | feynman
  | unitary
deriving DecidableEq, Repr

/-- Apparent four-graviton energy power before TGRET cancellations. -/
def apparentFourGravitonPower : GravitationalGauge → ℕ
  | .landau => 11
  | .feynman => 12
  | .unitary => 12

/-- The leading four-point TGRET amplitude scales as one power of energy. -/
def tgretFourPointPower : ℕ := 1

/-- Number of powers cancelled by the four-point TGRET reduction. -/
def fourPointCancelledPowers (gauge : GravitationalGauge) : ℕ :=
  apparentFourGravitonPower gauge - tgretFourPointPower

lemma landau_fourPoint_cancelledPowers :
    fourPointCancelledPowers .landau = 10 := by
  norm_num [fourPointCancelledPowers, apparentFourGravitonPower, tgretFourPointPower]

lemma unitary_fourPoint_cancelledPowers :
    fourPointCancelledPowers .unitary = 11 := by
  norm_num [fourPointCancelledPowers, apparentFourGravitonPower, tgretFourPointPower]

lemma feynman_fourPoint_cancelledPowers :
    fourPointCancelledPowers .feynman = 11 := by
  norm_num [fourPointCancelledPowers, apparentFourGravitonPower, tgretFourPointPower]

/-- TGRET leading factor for an `N`-point physical massive-graviton amplitude. -/
def tgretFactor (N : ℕ) : ℂ :=
  ((1 / 2 : ℂ) ^ N)

lemma tgretFactor_four :
    tgretFactor 4 = (1 / 16 : ℂ) := by
  norm_num [tgretFactor]

/--
The high-energy topological graviton equivalence theorem at leading order:
the physical massive-graviton leading amplitude is `(1/2)^N` times the
corresponding dilaton leading amplitude.
-/
structure TopologicalGravitonEquivalence (N : ℕ) where
  gravitonLeading : ℂ
  dilatonLeading : ℂ
  equivalence : gravitonLeading = tgretFactor N * dilatonLeading

lemma fourPoint_topologicalGravitonEquivalence
    (E : TopologicalGravitonEquivalence 4) :
    E.gravitonLeading = (1 / 16 : ℂ) * E.dilatonLeading := by
  rw [E.equivalence, tgretFactor_four]

/-- Leading scalar/dilaton equality from the Weyl-transformed high-energy limit. -/
structure DilatonScalarLeadingEquivalence (N : ℕ) where
  dilatonLeading : ℂ
  scalarLeading : ℂ
  equivalence : dilatonLeading = scalarLeading

/--
Combining TGRET with the paper's leading scalar/dilaton equality transfers the
topological graviton amplitude to the scalar amplitude used in the double copy.
-/
lemma tgret_transfers_to_scalar_leading
    {N : ℕ}
    (G : TopologicalGravitonEquivalence N)
    (S : DilatonScalarLeadingEquivalence N)
    (h : G.dilatonLeading = S.dilatonLeading) :
    G.gravitonLeading = tgretFactor N * S.scalarLeading := by
  rw [G.equivalence, h, S.equivalence]

/-! ## Section 2: Weyl transform, field redefinitions, and degree-of-freedom counts -/

/--
Unitary gauge of WTMG decouples the dilaton sector and reduces the WTMG
amplitude to the conventional TMG amplitude.
-/
structure UnitaryGaugeReductionData where
  wtmgAmplitude : ℂ
  tmgAmplitude : ℂ
  dilatonSector : ℂ
  reduction : wtmgAmplitude = tmgAmplitude + dilatonSector
  dilaton_decouples : dilatonSector = 0

lemma wtmg_reduces_to_tmg_in_unitary_gauge
    (D : UnitaryGaugeReductionData) :
    D.wtmgAmplitude = D.tmgAmplitude := by
  rw [D.reduction, D.dilaton_decouples, add_zero]

/-- The massive double-copy degree-of-freedom count in Eq. (2.2b). -/
lemma massive_topological_doubleCopy_dof_count :
    (1 : ℕ) * 1 = 1 + 0 := by
  norm_num

/-- The massless double-copy degree-of-freedom count in Eq. (2.2a). -/
lemma massless_doubleCopy_dilaton_dof_count :
    (1 : ℕ) * 1 = 0 + 1 := by
  norm_num

/--
The total one physical degree of freedom is conserved in the massless limit,
but is carried by the dilaton rather than by a 3d massless graviton.
-/
lemma massless_limit_conserves_total_dof :
    (1 : ℕ) + 0 = 0 + 1 := by
  norm_num

/--
Eq. (2.30)-(2.32): pure dilaton derivative self-interactions are equivalent,
by a local field redefinition, to a free massless scalar sector.
-/
structure PureDilatonFieldRedefinitionData (N : ℕ) where
  originalOnShellAmplitude : ℂ
  redefinedOnShellAmplitude : ℂ
  free_redefined_amplitude : redefinedOnShellAmplitude = 0
  smatrix_invariant : originalOnShellAmplitude = redefinedOnShellAmplitude

lemma pureDilatonSelfInteractions_no_onShell_contribution
    {N : ℕ}
    (D : PureDilatonFieldRedefinitionData N) :
    D.originalOnShellAmplitude = 0 := by
  rw [D.smatrix_invariant, D.free_redefined_amplitude]

/--
Eq. (2.39): after the scalar field redefinition, the derivative sector is
invariant under exchange `ϕhat ↔ ψhat`, so the leading scalar and dilaton
amplitudes agree.
-/
structure WTMGSLeadingScalarDilatonData (N : ℕ) where
  hatDilatonLeading : ℂ
  hatScalarLeading : ℂ
  dilatonLeading : ℂ
  scalarLeading : ℂ
  exchange_symmetry : hatDilatonLeading = hatScalarLeading
  dilaton_field_redefinition_invariant : dilatonLeading = hatDilatonLeading
  scalar_field_redefinition_invariant : scalarLeading = hatScalarLeading

lemma wtmgScalar_eq_dilaton_leading_from_field_redefinition
    {N : ℕ}
    (D : WTMGSLeadingScalarDilatonData N) :
    D.dilatonLeading = D.scalarLeading := by
  rw [D.dilaton_field_redefinition_invariant, D.exchange_symmetry,
    D.scalar_field_redefinition_invariant]

/-- Convert the WTMGS field-redefinition data into the shared leading scalar/dilaton equivalence carrier. -/
def dilatonScalarLeadingEquivalenceOfWTMGS
    {N : ℕ}
    (D : WTMGSLeadingScalarDilatonData N) :
    DilatonScalarLeadingEquivalence N where
  dilatonLeading := D.dilatonLeading
  scalarLeading := D.scalarLeading
  equivalence := wtmgScalar_eq_dilaton_leading_from_field_redefinition D

/-! ## Section 3: BRST identity, TGRET with remainders, and power counting -/

/--
The BRST-amputated identity with one external `F₂` state: if the external
state decomposes as `F₂ = hP - Q` and every physical amplitude containing
`F₂` vanishes, then the `Q` amplitude equals the physical-graviton amplitude.
-/
structure BRSTExternalReplacementData where
  hPAmplitude : ℂ
  qAmplitude : ℂ
  f2Amplitude : ℂ
  f2_decomposition : f2Amplitude = hPAmplitude - qAmplitude
  brst_zero : f2Amplitude = 0

lemma qAmplitude_eq_hPAmplitude_of_BRST
    (D : BRSTExternalReplacementData) :
    D.qAmplitude = D.hPAmplitude := by
  have h : D.hPAmplitude - D.qAmplitude = 0 := by
    simpa [D.brst_zero] using D.f2_decomposition.symm
  exact (sub_eq_zero.mp h).symm

/-- Eq. (3.31), including the loop factor and the residual `O(m/E)` term. -/
structure TopologicalGravitonEquivalenceWithRemainder (N : ℕ) where
  gravitonAmplitude : ℂ
  dilatonAmplitude : ℂ
  loopFactor : ℂ
  suppressedRemainder : ℂ
  tgret_expansion :
    gravitonAmplitude = tgretFactor N * loopFactor * dilatonAmplitude + suppressedRemainder

lemma tgret_tree_leading_of_unit_loop_and_zero_remainder
    {N : ℕ}
    (D : TopologicalGravitonEquivalenceWithRemainder N)
    (hloop : D.loopFactor = 1)
    (hrem : D.suppressedRemainder = 0) :
    D.gravitonAmplitude = tgretFactor N * D.dilatonAmplitude := by
  rw [D.tgret_expansion, hloop, hrem, mul_one, add_zero]

/-- Extract the leading TGRET equivalence when the loop factor is one and the suppressed remainder vanishes. -/
def topologicalGravitonEquivalenceOfRemainderData
    {N : ℕ}
    (D : TopologicalGravitonEquivalenceWithRemainder N)
    (hloop : D.loopFactor = 1)
    (hrem : D.suppressedRemainder = 0) :
    TopologicalGravitonEquivalence N where
  gravitonLeading := D.gravitonAmplitude
  dilatonLeading := D.dilatonAmplitude
  equivalence := tgret_tree_leading_of_unit_loop_and_zero_remainder D hloop hrem

/-- Gauge-side TGAET energy power before cancellation. -/
def tgaetGaugeBeforePower : ℤ := 4

/-- Gauge-side TGAET leading power for an `N`-point physical gauge amplitude. -/
def tgaetGaugeAfterPower (N : ℕ) : ℤ :=
  4 - (N : ℤ)

lemma tgaet_fourPoint_E4_to_E0 :
    tgaetGaugeBeforePower = 4 ∧ tgaetGaugeAfterPower 4 = 0 := by
  norm_num [tgaetGaugeBeforePower, tgaetGaugeAfterPower]

/-- Eq. (3.45): Landau-gauge tree-level graviton power `D_E[NhP]=2N+3`. -/
def landauTreeGravitonPower (N : ℕ) : ℚ :=
  2 * (N : ℚ) + 3

/-- Eq. (3.47): unitary-gauge tree-level graviton power `D_E^U[NhP]=3N`. -/
def unitaryTreeGravitonPower (N : ℕ) : ℚ :=
  3 * (N : ℚ)

/-- Eq. (3.49), with `N=2n`: `D_E[Nϕ]=3-n`. -/
def evenTreeDilatonPower (n : ℕ) : ℚ :=
  3 - (n : ℚ)

/-- Eq. (3.50), with `N=2n+1`: `D_E[Nϕ]=2-n`. -/
def oddTreeDilatonPower (n : ℕ) : ℚ :=
  2 - (n : ℚ)

lemma landauTreeGravitonPower_four :
    landauTreeGravitonPower 4 = 11 := by
  norm_num [landauTreeGravitonPower]

lemma unitaryTreeGravitonPower_four :
    unitaryTreeGravitonPower 4 = 12 := by
  norm_num [unitaryTreeGravitonPower]

lemma evenTreeDilatonPower_four :
    evenTreeDilatonPower 2 = 1 := by
  norm_num [evenTreeDilatonPower]

lemma landau_evenPoint_cancellation
    (n : ℕ) :
    landauTreeGravitonPower (2 * n) - evenTreeDilatonPower n =
      5 * (n : ℚ) := by
  unfold landauTreeGravitonPower evenTreeDilatonPower
  norm_num [Nat.cast_mul]
  ring_nf

lemma landau_oddPoint_cancellation
    (n : ℕ) :
    landauTreeGravitonPower (2 * n + 1) - oddTreeDilatonPower n =
      5 * (n : ℚ) + 3 := by
  unfold landauTreeGravitonPower oddTreeDilatonPower
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma unitary_evenPoint_cancellation
    (n : ℕ) :
    unitaryTreeGravitonPower (2 * n) - evenTreeDilatonPower n =
      7 * (n : ℚ) - 3 := by
  unfold unitaryTreeGravitonPower evenTreeDilatonPower
  norm_num [Nat.cast_mul]
  ring_nf

lemma unitary_oddPoint_cancellation
    (n : ℕ) :
    unitaryTreeGravitonPower (2 * n + 1) - oddTreeDilatonPower n =
      7 * (n : ℚ) + 1 := by
  unfold unitaryTreeGravitonPower oddTreeDilatonPower
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma landau_fourPoint_cancellation_from_power_count :
    landauTreeGravitonPower 4 - evenTreeDilatonPower 2 = 10 := by
  norm_num [landauTreeGravitonPower, evenTreeDilatonPower]

lemma unitary_fourPoint_cancellation_from_power_count :
    unitaryTreeGravitonPower 4 - evenTreeDilatonPower 2 = 11 := by
  norm_num [unitaryTreeGravitonPower, evenTreeDilatonPower]

/-- Eq. (3.51): residual amplitudes containing `h_v` are subleading. -/
def fourPointResidualPowerWithHv : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | _ => -1

lemma residualPowerWithOneHv_subleading :
    fourPointResidualPowerWithHv 1 < fourPointResidualPowerWithHv 0 := by
  norm_num [fourPointResidualPowerWithHv]

lemma residualPowerWithTwoHv_subleading :
    fourPointResidualPowerWithHv 2 < fourPointResidualPowerWithHv 0 := by
  norm_num [fourPointResidualPowerWithHv]

lemma residualPowerWithThreeHv_subleading :
    fourPointResidualPowerWithHv 3 < fourPointResidualPowerWithHv 0 := by
  norm_num [fourPointResidualPowerWithHv]

lemma residualPowerWithFourHv_subleading :
    fourPointResidualPowerWithHv 4 < fourPointResidualPowerWithHv 0 := by
  norm_num [fourPointResidualPowerWithHv]

/-- Three-point topologically massive Yang-Mills numerator/color amplitude. -/
def topologicallyMassiveYangMillsThreeAmplitude
    (g color numerator : ℂ) : ℂ :=
  g * color * numerator

/-- In the finite local CSW model, the scalar color factor used in the
three-point topologically massive Yang-Mills amplitude can be supplied by the
existing CSW cubic density.  The right-hand side expands that same density
through the already-linked Yang-Mills curvature `F₁₂`. -/
lemma topologicallyMassiveYangMillsThreeAmplitude_localCSW_curvature
    {n : ℕ} (g numerator : ℂ) (A : LocalCSConnection n) :
    topologicallyMassiveYangMillsThreeAmplitude g (localChernSimonsCubic A) numerator =
      g *
        Matrix.trace
          (A 0 *
            yangMillsCurvature localCSZeroPartial (localCSAsGaugePotential A) () 1 2) *
        numerator := by
  rw [localChernSimonsCubic_eq_trace_A0_curvature12 A,
    localCSCurvature_eq_yangMillsCurvature_zeroPartial A 1 2]
  rfl

/--
Three-point Chern-Simons graviton double copy.  This is the algebraic replacement
`g ↦ κ/4`, `f^{abc} ↦ N_A` in the paper.
-/
def chernSimonsGravitonThreeDoubleCopy
    (kappa numerator : ℂ) : ℂ :=
  (kappa / 4) * numerator * numerator

lemma chernSimonsGravitonThreeDoubleCopy_eq_replacement
    (kappa numerator : ℂ) :
    chernSimonsGravitonThreeDoubleCopy kappa numerator =
      topologicallyMassiveYangMillsThreeAmplitude (kappa / 4) numerator numerator := by
  rfl

/-- The three-point graviton replacement can use the same local CSW/Yang-Mills
curvature scalar when the replacement numerator is the finite CSW cubic. -/
lemma chernSimonsGravitonThreeDoubleCopy_localCSW_curvature
    {n : ℕ} (kappa : ℂ) (A : LocalCSConnection n) :
    chernSimonsGravitonThreeDoubleCopy kappa (localChernSimonsCubic A) =
      topologicallyMassiveYangMillsThreeAmplitude
        (kappa / 4)
        (Matrix.trace
          (A 0 *
            yangMillsCurvature localCSZeroPartial (localCSAsGaugePotential A) () 1 2))
        (localChernSimonsCubic A) := by
  rw [chernSimonsGravitonThreeDoubleCopy_eq_replacement,
    topologicallyMassiveYangMillsThreeAmplitude_localCSW_curvature]
  rfl

/-- Four-channel massive Chern-Simons data with color and kinematic Jacobi laws. -/
structure MassiveChernSimonsFourChannelData where
  kappa : ℝ
  gaugeCoupling : ℝ
  mass : ℝ
  s : ℝ
  t : ℝ
  u : ℝ
  N_s : ℝ
  N_t : ℝ
  N_u : ℝ
  C_s : ℝ
  C_t : ℝ
  C_u : ℝ
  color_jacobi : C_s + C_t + C_u = 0
  kinematic_jacobi : N_s + N_t + N_u = 0

/-- Four-channel massive Chern-Simons data reuses the existing BCJ
color-kinematics-duality record instead of introducing a parallel Jacobi
carrier. -/
def MassiveChernSimonsFourChannelData.toBCJDuality
    (D : MassiveChernSimonsFourChannelData) : BCJColorKinematicsDuality where
  c_s := D.C_s
  c_t := D.C_t
  c_u := D.C_u
  n_s := D.N_s
  n_t := D.N_t
  n_u := D.N_u
  color_jacobi := D.color_jacobi
  kinematic_jacobi := D.kinematic_jacobi

/-- The four-channel massive Chern-Simons data exposes exactly the existing BCJ
color and kinematic Jacobi laws. -/
lemma massiveChernSimonsFourChannelData_bcj_jacobi
    (D : MassiveChernSimonsFourChannelData) :
    (D.toBCJDuality).c_s + (D.toBCJDuality).c_t + (D.toBCJDuality).c_u = 0
      ∧ (D.toBCJDuality).n_s + (D.toBCJDuality).n_t + (D.toBCJDuality).n_u = 0 :=
  ⟨(D.toBCJDuality).color_jacobi, (D.toBCJDuality).kinematic_jacobi⟩

/--
The four-point topologically massive Yang-Mills amplitude in the color/numerator
form used before the BCJ replacement.
-/
def topologicallyMassiveYangMillsFourAmplitude
    (D : MassiveChernSimonsFourChannelData) : ℝ :=
  D.gaugeCoupling ^ 2 *
    (D.C_s * D.N_s / (D.s - D.mass ^ 2) +
     D.C_t * D.N_t / (D.t - D.mass ^ 2) +
     D.C_u * D.N_u / (D.u - D.mass ^ 2))

/-- Raw four-point massive gauge amplitude, useful before imposing Jacobi. -/
def massiveGaugeFourAmplitudeRaw
    (g mass s t u N_s N_t N_u C_s C_t C_u : ℝ) : ℝ :=
  g ^ 2 *
    (C_s * N_s / (s - mass ^ 2) +
     C_t * N_t / (t - mass ^ 2) +
     C_u * N_u / (u - mass ^ 2))

/-- Generalized massive gauge shift `N_j ↦ N_j - Δ(s_j-m²)`. -/
def generalizedShiftedNumerator
    (N delta channel mass : ℝ) : ℝ :=
  N - delta * (channel - mass ^ 2)

lemma massiveGaugeFourAmplitudeRaw_eq_structured
    (D : MassiveChernSimonsFourChannelData) :
    massiveGaugeFourAmplitudeRaw D.gaugeCoupling D.mass D.s D.t D.u
        D.N_s D.N_t D.N_u D.C_s D.C_t D.C_u =
      topologicallyMassiveYangMillsFourAmplitude D := by
  rfl

/--
Eq. (4.55) is invariant under the generalized massive gauge transformation:
the shift changes the amplitude by a color-Jacobi multiple.
-/
lemma massiveGaugeFourAmplitude_invariant_under_generalized_shift
    (g mass s t u N_s N_t N_u C_s C_t C_u delta : ℝ)
    (hcolor : C_s + C_t + C_u = 0)
    (hs : s - mass ^ 2 ≠ 0)
    (ht : t - mass ^ 2 ≠ 0)
    (hu : u - mass ^ 2 ≠ 0) :
    massiveGaugeFourAmplitudeRaw g mass s t u
        (generalizedShiftedNumerator N_s delta s mass)
        (generalizedShiftedNumerator N_t delta t mass)
        (generalizedShiftedNumerator N_u delta u mass)
        C_s C_t C_u =
      massiveGaugeFourAmplitudeRaw g mass s t u N_s N_t N_u C_s C_t C_u := by
  unfold massiveGaugeFourAmplitudeRaw generalizedShiftedNumerator
  field_simp [hs, ht, hu]
  rw [show C_u = -C_s - C_t by linarith]
  ring

/--
The shift used in Eq. (4.63)-(4.64) imposes the massive kinematic Jacobi
identity when the massive four-point channel sum is `m²`.
-/
lemma generalizedShiftedNumerators_jacobi
    (mass s t u N_s N_t N_u delta : ℝ)
    (hshift :
      delta * ((s - mass ^ 2) + (t - mass ^ 2) + (u - mass ^ 2)) =
        N_s + N_t + N_u) :
    generalizedShiftedNumerator N_s delta s mass +
      generalizedShiftedNumerator N_t delta t mass +
      generalizedShiftedNumerator N_u delta u mass = 0 := by
  calc
    generalizedShiftedNumerator N_s delta s mass +
        generalizedShiftedNumerator N_t delta t mass +
        generalizedShiftedNumerator N_u delta u mass
        = (N_s + N_t + N_u) -
          delta * ((s - mass ^ 2) + (t - mass ^ 2) + (u - mass ^ 2)) := by
            unfold generalizedShiftedNumerator
            ring
    _ = 0 := by
      rw [← hshift]
      ring

lemma generalizedShiftedNumerators_jacobi_of_omega_over_massSq
    (mass s t u N_s N_t N_u omega : ℝ)
    (hmass : mass ^ 2 ≠ 0)
    (hchannels : (s - mass ^ 2) + (t - mass ^ 2) + (u - mass ^ 2) = mass ^ 2)
    (homega : omega = N_s + N_t + N_u) :
    generalizedShiftedNumerator N_s (omega / mass ^ 2) s mass +
      generalizedShiftedNumerator N_t (omega / mass ^ 2) t mass +
      generalizedShiftedNumerator N_u (omega / mass ^ 2) u mass = 0 := by
  apply generalizedShiftedNumerators_jacobi
  rw [hchannels, ← homega]
  have hmass0 : mass ≠ 0 := by
    intro h0
    apply hmass
    rw [h0]
    norm_num
  field_simp [hmass0]

/--
The four-point Chern-Simons massive-graviton amplitude after the double-copy
replacement of each color factor by a second kinematic numerator.
-/
def chernSimonsGravitonFourDoubleCopy
    (D : MassiveChernSimonsFourChannelData) : ℝ :=
  D.kappa ^ 2 / 16 *
    (D.N_s ^ 2 / (D.s - D.mass ^ 2) +
     D.N_t ^ 2 / (D.t - D.mass ^ 2) +
     D.N_u ^ 2 / (D.u - D.mass ^ 2))

/-- A single massive propagating BCJ channel, connected to the existing BCJ spine. -/
def massiveBCJChannel
    (numerator color propagator : ℝ)
    (hprop : 0 < propagator) : BCJTriple where
  numerator := numerator
  color := color
  propagator := propagator
  prop_pos := hprop

lemma massiveFourChannel_jacobi
    (D : MassiveChernSimonsFourChannelData) :
    D.C_s + D.C_t + D.C_u = 0 ∧
      D.N_s + D.N_t + D.N_u = 0 := by
  exact ⟨D.color_jacobi, D.kinematic_jacobi⟩

/--
The four-point Chern-Simons graviton formula is the existing BCJ double-copy
amplitude applied to the three massive channels, up to the paper's gravitational
normalization `κ²/16`.
-/
lemma chernSimonsGravitonFourDoubleCopy_eq_BCJ
    (D : MassiveChernSimonsFourChannelData)
    (hs : 0 < D.s - D.mass ^ 2)
    (ht : 0 < D.t - D.mass ^ 2)
    (hu : 0 < D.u - D.mass ^ 2) :
    chernSimonsGravitonFourDoubleCopy D =
      D.kappa ^ 2 / 16 *
        bcjDoubleCopyAmplitude
          [massiveBCJChannel D.N_s D.C_s (D.s - D.mass ^ 2) hs,
           massiveBCJChannel D.N_t D.C_t (D.t - D.mass ^ 2) ht,
           massiveBCJChannel D.N_u D.C_u (D.u - D.mass ^ 2) hu]
          [massiveBCJChannel D.N_s D.C_s (D.s - D.mass ^ 2) hs,
           massiveBCJChannel D.N_t D.C_t (D.t - D.mass ^ 2) ht,
           massiveBCJChannel D.N_u D.C_u (D.u - D.mass ^ 2) hu] := by
  simp [chernSimonsGravitonFourDoubleCopy, massiveBCJChannel, bcjDoubleCopyAmplitude, pow_two]

/-! ## Section 4: explicit amplitude checks, scalar double copy, and massless limit -/

/-- Eq. (4.8): the three-point TGRET check has the one-external factor `1/2`. -/
structure ThreePointTGRETCheck where
  gravitonAmplitude : ℂ
  dilatonAmplitude : ℂ
  eq_4_8 : gravitonAmplitude = (1 / 2 : ℂ) * dilatonAmplitude

lemma threePointTGRET_factor
    (D : ThreePointTGRETCheck) :
    D.gravitonAmplitude = (1 / 2 : ℂ) * D.dilatonAmplitude := by
  exact D.eq_4_8

/--
Eq. (B.22): the physical four-graviton amplitude is gauge-independent between
Landau and unitary gauges.
-/
structure FourGravitonGaugeIndependenceData where
  landauAmplitude : ℂ
  unitaryAmplitude : ℂ
  gauge_independence : unitaryAmplitude = landauAmplitude

lemma unitaryGauge_fourGraviton_eq_landauGauge
    (D : FourGravitonGaugeIndependenceData) :
    D.unitaryAmplitude = D.landauAmplitude := by
  exact D.gauge_independence

/--
Appendix B.2 witness that transverse-graviton amplitudes cannot replace the
dilaton side of TGRET when their leading value differs from the physical one.
-/
structure TransverseGravitonFailureWitness where
  physicalLeading : ℂ
  transverseLeading : ℂ
  dilatonLeading : ℂ
  physical_eq_tgret_dilaton : physicalLeading = tgretFactor 4 * dilatonLeading
  transverse_ne_physical : transverseLeading ≠ physicalLeading

lemma transverseGraviton_not_TGRET_replacement
    (W : TransverseGravitonFailureWitness) :
    W.transverseLeading ≠ tgretFactor 4 * W.dilatonLeading := by
  intro h
  exact W.transverse_ne_physical (by rw [W.physical_eq_tgret_dilaton, h])

/--
Eq. (4.81): the leading four-dilaton amplitude is obtained from the leading
four-scalar double-copy amplitude when the scalar mass is matched to the
topological mass.
-/
structure FourScalarDilatonDoubleCopyLeading where
  dilatonLeading : ℂ
  scalarLeading : ℂ
  scalarDoubleCopyLeading : ℂ
  dilaton_eq_scalar : dilatonLeading = scalarLeading
  scalar_eq_doubleCopy : scalarLeading = scalarDoubleCopyLeading

lemma fourDilatonLeading_eq_scalarDoubleCopyLeading
    (D : FourScalarDilatonDoubleCopyLeading) :
    D.dilatonLeading = D.scalarDoubleCopyLeading := by
  rw [D.dilaton_eq_scalar, D.scalar_eq_doubleCopy]

/-- The mass-mismatch obstruction multiplying the leading `O(s)` term in Eq. (4.89). -/
def scalarMassMismatchTerm (scalarMass gravitonMass : ℝ) : ℝ :=
  scalarMass ^ 2 - gravitonMass ^ 2

lemma scalarMassMismatchTerm_zero_of_equal_mass
    {scalarMass gravitonMass : ℝ}
    (h : scalarMass = gravitonMass) :
    scalarMassMismatchTerm scalarMass gravitonMass = 0 := by
  rw [h]
  simp [scalarMassMismatchTerm]

lemma scalarMassMismatchTerm_zero_iff_equal_squares
    {scalarMass gravitonMass : ℝ} :
    scalarMassMismatchTerm scalarMass gravitonMass = 0 ↔
      scalarMass ^ 2 = gravitonMass ^ 2 := by
  unfold scalarMassMismatchTerm
  constructor <;> intro h <;> linarith

/--
Eq. (4.90): if the leading `O(s)` mass-mismatch term vanishes because
`m_s=m`, the scalar double copy lands on the leading dilaton amplitude.
-/
lemma matchedMass_scalarDoubleCopy_eq_dilatonLeading
    {scalarMass gravitonMass : ℝ}
    (hm : scalarMass = gravitonMass)
    (D : FourScalarDilatonDoubleCopyLeading) :
    scalarMassMismatchTerm scalarMass gravitonMass = 0 ∧
      D.dilatonLeading = D.scalarDoubleCopyLeading := by
  exact ⟨scalarMassMismatchTerm_zero_of_equal_mass hm,
    fourDilatonLeading_eq_scalarDoubleCopyLeading D⟩

/-- Raw four-point massless gauge amplitude of Eq. (4.92). -/
def masslessGaugeFourAmplitudeRaw
    (g s t u N_s N_t N_u C_s C_t C_u : ℝ) : ℝ :=
  g ^ 2 * (C_s * N_s / s + C_t * N_t / t + C_u * N_u / u)

/-- Raw four-point massless double-copy amplitude of Eq. (4.96). -/
def masslessDoubleCopyFourAmplitudeRaw
    (kappa s t u N_s N_t N_u : ℝ) : ℝ :=
  kappa ^ 2 / 16 * (N_s ^ 2 / s + N_t ^ 2 / t + N_u ^ 2 / u)

lemma masslessKinematicJacobi_from_existing_BCJ_duality
    (H : BCJColorKinematicsDuality) :
    H.n_s + H.n_t + H.n_u = 0 := by
  exact H.kinematic_jacobi

/--
Eq. (4.96)-(4.97): the massless YM double copy equals the direct GRD3 dilaton
amplitude.
-/
structure MasslessDoubleCopyGRD3Data where
  ymDoubleCopyAmplitude : ℂ
  directGRD3DilatonAmplitude : ℂ
  doubleCopy_eq_direct : ymDoubleCopyAmplitude = directGRD3DilatonAmplitude

lemma masslessYMDoubleCopy_eq_GRD3Dilaton
    (D : MasslessDoubleCopyGRD3Data) :
    D.ymDoubleCopyAmplitude = D.directGRD3DilatonAmplitude := by
  exact D.doubleCopy_eq_direct

/--
Eq. (4.98)-(4.100): in the massless limit, the transverse gauge-boson and
adjoint-scalar amplitudes have the same numerators and therefore agree.
-/
structure MasslessGaugeScalarEqualityData where
  transverseGaugeAmplitude : ℂ
  adjointScalarAmplitude : ℂ
  numerator_equality_amplitude : transverseGaugeAmplitude = adjointScalarAmplitude

lemma masslessGaugeBosonAmplitude_eq_adjointScalarAmplitude
    (D : MasslessGaugeScalarEqualityData) :
    D.transverseGaugeAmplitude = D.adjointScalarAmplitude := by
  exact D.numerator_equality_amplitude

/--
The Section 4.3 chain: massless TMYM reduces to YM, WTMG reduces to GRD3,
and the double copy of the massless gauge amplitude is the GRD3 dilaton
amplitude.
-/
structure MasslessLimitSection43Chain where
  tmyMLeading : ℂ
  masslessYMTransverse : ℂ
  masslessAdjointScalar : ℂ
  grD3Dilaton : ℂ
  gauge_tgaet_limit : tmyMLeading = masslessYMTransverse
  gauge_eq_scalar : masslessYMTransverse = masslessAdjointScalar
  doubleCopy_scalar_to_dilaton : masslessAdjointScalar = grD3Dilaton

lemma section43_masslessLimit_chain
    (D : MasslessLimitSection43Chain) :
    D.tmyMLeading = D.grD3Dilaton := by
  rw [D.gauge_tgaet_limit, D.gauge_eq_scalar, D.doubleCopy_scalar_to_dilaton]

/--
The paper's massive kinematic Jacobi statement is exactly the kinematic half of
the repository's BCJ color-kinematics duality record.
-/
lemma kinematicJacobi_from_existing_BCJ_duality
    (H : BCJColorKinematicsDuality) :
    H.n_s + H.n_t + H.n_u = 0 := by
  exact H.kinematic_jacobi

/--
The paper's color Jacobi statement is the color half of the same existing BCJ
duality record.
-/
lemma colorJacobi_from_existing_BCJ_duality
    (H : BCJColorKinematicsDuality) :
    H.c_s + H.c_t + H.c_u = 0 := by
  exact H.color_jacobi

/--
Topological massive graviton data linked to the repository's DJT topological
mass formula.
-/
structure ChernSimonsGravitonMassData where
  gaugeData : DJTData
  gravitonMass : ℝ
  mass_eq_topologicalMass : gravitonMass = topologicalMass gaugeData

lemma chernSimonsGravitonMass_nonneg
    (D : ChernSimonsGravitonMassData) :
    0 ≤ D.gravitonMass := by
  rw [D.mass_eq_topologicalMass]
  exact topologicalMass_nonneg D.gaugeData

lemma chernSimonsGravitonMass_zero_iff_level_zero
    (D : ChernSimonsGravitonMassData)
    (he : D.gaugeData.e ≠ 0) :
    D.gravitonMass = 0 ↔ D.gaugeData.level = 0 := by
  rw [D.mass_eq_topologicalMass]
  exact topologicalMass_eq_zero_iff_level_zero (dj := D.gaugeData) he

/--
The Chern-Simons graviton double-copy file reuses the existing topological-mass
and Feynman-Kac/character double-copy spines in one Lean-checked statement.
-/
lemma chernSimonsDoubleCopy_uses_existing_spine
    (D : ChernSimonsGravitonMassData)
    (S₁ S₂ : ℝ) :
    0 ≤ D.gravitonMass ∧
      Real.exp (-(S₁ + S₂)) = Real.exp (-S₁) * Real.exp (-S₂) := by
  exact ⟨chernSimonsGravitonMass_nonneg D,
    bcj_doublecopy_fk_factorization S₁ S₂⟩

/--
The Pontryagin/anomaly bridge can be paired with TGRET without adding new
physics assumptions: the charge jump remains the Chern-Simons/Pontryagin
invariant while the scattering side reduces to the dilaton leading amplitude.
-/
lemma pontryaginChargeJump_and_fourPointTGRET
    {M : Type}
    [MeasurableSpace M]
    (W : ChernSimonsPontryaginAnomalyWitness M)
    (E : TopologicalGravitonEquivalence 4) :
    W.qOut - W.qIn = ∫ x, W.currentDivergence x ∂ W.μ ∧
      E.gravitonLeading = (1 / 16 : ℂ) * E.dilatonLeading := by
  exact ⟨W.charge_jump_eq_current_integral, fourPoint_topologicalGravitonEquivalence E⟩

/--
TGRET plus the explicit four-point power-counting statement: in Landau gauge
the apparent `E^11` behavior reduces to the leading `E^1` dilaton-controlled
amplitude.
-/
lemma landauGauge_TGRET_fourPoint_summary
    (E : TopologicalGravitonEquivalence 4) :
    E.gravitonLeading = (1 / 16 : ℂ) * E.dilatonLeading ∧
      fourPointCancelledPowers .landau = 10 := by
  exact ⟨fourPoint_topologicalGravitonEquivalence E, landau_fourPoint_cancelledPowers⟩

/--
The corresponding unitary-gauge summary: the apparent `E^12` behavior reduces
to the same leading `E^1` dilaton-controlled amplitude.
-/
lemma unitaryGauge_TGRET_fourPoint_summary
    (E : TopologicalGravitonEquivalence 4) :
    E.gravitonLeading = (1 / 16 : ℂ) * E.dilatonLeading ∧
      fourPointCancelledPowers .unitary = 11 := by
  exact ⟨fourPoint_topologicalGravitonEquivalence E, unitary_fourPoint_cancelledPowers⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.GravitonDoubleCopy

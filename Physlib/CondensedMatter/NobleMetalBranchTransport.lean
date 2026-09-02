/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Optics.MaterialTimescales
public import Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
public import QuantumInfo.ClassicalInfo.Distribution
public import Mathlib.Topology.Order.IntermediateValue
meta import Zil


/-!
# Relativistic noble-metal transport across Everett sectors

This module supplies the mathematical carrier for comparing intrinsic bulk
conductivity of pure fcc copper, silver, and gold at one fixed operational
temperature while a decohered vacuum/order parameter changes their effective
relativistic band Hamiltonians.

The exact content is deliberately separated into three layers:

* the Foldy--Wouthuysen spin-averaged band energy and the continuum
  Fermi-surface transport integral;
* order and crossing theorems, including the fact that a common charge
  prefactor cannot reverse a conductivity ordering;
* measured room-temperature reference numbers and a nonzero Everett branch
  certificate, both explicitly carried as inputs rather than predictions.

No theorem below says that changing the fine-structure constant actually
produces `Au > Ag > Cu`.  Establishing that endpoint requires an independent
relativistic band/electron--phonon calculation.  Once endpoint signs and
continuity are supplied, the crossing itself is a theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.CondensedMatter.NobleMetalBranchTransport

open MeasureTheory
open scoped BigOperators
open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
open Physlib.QuantumMechanics.PeriodicSchrodinger

/-! ## A. Relativistic band carrier -/

set_option backward.isDefEq.respectTransparency false in
/-- The three monovalent fcc noble metals compared by the transport model. -/
inductive NobleMetal
  | copper
  | silver
  | gold
deriving DecidableEq, Fintype, Repr

/-- The spin-averaged energy of the existing two-component Foldy--Wouthuysen
Pauli Hamiltonian.  This is a scalar band-energy carrier, not an assertion that
the two spin-resolved eigenvalues coincide. -/
def spinAveragedFWBandEnergy
    (m kinetic potential relCorr lapV : ℝ) (gradV p : Fin 3 → ℝ) : ℝ :=
  (pauliHamiltonianFW m kinetic potential relCorr lapV gradV p).trace.re / 2

/-- The Pauli spin average removes the traceless spin--orbit term and retains
the scalar Foldy--Wouthuysen energy. -/
theorem spinAveragedFWBandEnergy_eq
    (m kinetic potential relCorr lapV : ℝ) (gradV p : Fin 3 → ℝ) :
    spinAveragedFWBandEnergy m kinetic potential relCorr lapV gradV p =
      kinetic + potential + relCorr + lapV / (8 * m ^ 2) := by
  have htrace : (sigmaDot (crossR gradV p)).trace = 0 := by
    simp [sigmaDot]
  rw [spinAveragedFWBandEnergy, pauliHamiltonianFW, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, htrace]
  simp
  rw [show (↑lapV / (8 * ↑m ^ 2) : ℂ) = ((lapV / (8 * m ^ 2) : ℝ) : ℂ) from by
      push_cast; ring, Complex.ofReal_re]

/-- Branch-parameterized Foldy--Wouthuysen input for one noble metal and one
one-dimensional Bloch momentum coordinate.  The scalar transport band is
obtained from the repository's Pauli Hamiltonian rather than postulated as an
unrelated energy function. -/
structure RelativisticBandFamily where
  mass : ℝ
  kinetic : ℝ → ℝ → ℝ
  potential : ℝ → ℝ → ℝ
  relativisticCorrection : ℝ → ℝ → ℝ
  potentialLaplacian : ℝ → ℝ → ℝ
  potentialGradient : ℝ → ℝ → Fin 3 → ℝ
  momentum : ℝ → ℝ → Fin 3 → ℝ

/-- The spin-averaged relativistic Bloch energy at vacuum parameter `λ` and
quasimomentum `k`. -/
def RelativisticBandFamily.energy (B : RelativisticBandFamily) (parameter k : ℝ) : ℝ :=
  spinAveragedFWBandEnergy B.mass (B.kinetic parameter k) (B.potential parameter k)
    (B.relativisticCorrection parameter k) (B.potentialLaplacian parameter k)
    (B.potentialGradient parameter k) (B.momentum parameter k)

/-- The existing band-Hessian definition supplies the transport mass of the
spin-averaged relativistic band without identifying it with a Compton screen
mass. -/
def RelativisticBandFamily.transportMass
    (B : RelativisticBandFamily) (hbar parameter k : ℝ) : ℝ :=
  carrierEffectiveMassFromBand (B.energy parameter) hbar k

/-! ## B. Continuum intrinsic transport -/

/-- Continuum Fermi-surface transport data.  The kernel factors have their
standard roles: group velocity squared, electron--phonon relaxation time, and
the positive thermal Fermi-window weight `-∂f/∂E`. -/
structure FermiSurfaceTransportData (K : Type*) [MeasurableSpace K] where
  measure : Measure K
  velocity : K → ℝ
  relaxationTime : K → ℝ
  fermiWindow : K → ℝ
  relaxationTime_nonneg : ∀ k, 0 ≤ relaxationTime k
  fermiWindow_nonneg : ∀ k, 0 ≤ fermiWindow k

/-- The longitudinal Fermi-surface transport kernel `v² τ (-∂f/∂E)`. -/
def FermiSurfaceTransportData.kernel
    {K : Type*} [MeasurableSpace K] (D : FermiSurfaceTransportData K) (k : K) : ℝ :=
  D.velocity k ^ 2 * D.relaxationTime k * D.fermiWindow k

theorem FermiSurfaceTransportData.kernel_nonneg
    {K : Type*} [MeasurableSpace K] (D : FermiSurfaceTransportData K) (k : K) :
    0 ≤ D.kernel k := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (D.relaxationTime_nonneg k))
    (D.fermiWindow_nonneg k)

/-- The continuum longitudinal transport integral before its universal charge
prefactor. -/
def transportIntegral
    {K : Type*} [MeasurableSpace K] (D : FermiSurfaceTransportData K) : ℝ :=
  ∫ k, D.kernel k ∂D.measure

theorem transportIntegral_nonneg
    {K : Type*} [MeasurableSpace K] (D : FermiSurfaceTransportData K) :
    0 ≤ transportIntegral D := by
  exact integral_nonneg D.kernel_nonneg

/-- Isotropic intrinsic bulk conductivity
`σ = (q²/3) ∫ v² τ (-∂f/∂E)` at the fixed temperature encoded by
`D.fermiWindow` and `D.relaxationTime`. -/
def intrinsicBulkConductivity
    {K : Type*} [MeasurableSpace K] (charge : ℝ)
    (D : FermiSurfaceTransportData K) : ℝ :=
  charge ^ 2 / 3 * transportIntegral D

theorem intrinsicBulkConductivity_nonneg
    {K : Type*} [MeasurableSpace K] (charge : ℝ)
    (D : FermiSurfaceTransportData K) :
    0 ≤ intrinsicBulkConductivity charge D := by
  exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (transportIntegral_nonneg D)

/-- A common nonzero charge prefactor cannot reverse the ordering of two
transport integrals.  Any `Au/Ag` reversal must therefore arise from their
different bands, Fermi surfaces, or relaxation kernels. -/
theorem common_charge_order_iff
    {K : Type*} [MeasurableSpace K] {charge : ℝ} (hcharge : charge ≠ 0)
    (D₁ D₂ : FermiSurfaceTransportData K) :
    intrinsicBulkConductivity charge D₁ < intrinsicBulkConductivity charge D₂ ↔
      transportIntegral D₁ < transportIntegral D₂ := by
  unfold intrinsicBulkConductivity
  have hp : 0 < charge ^ 2 / 3 := div_pos (sq_pos_of_ne_zero hcharge) (by norm_num)
  constructor <;> intro h <;> nlinarith

/-! ## C. Conductivity orders and the measured reference branch -/

/-- A conductivity family indexed by metal and a physical vacuum/order
parameter. -/
abbrev ConductivityFamily := NobleMetal → ℝ → ℝ

/-- The ordinary room-temperature ordering `Ag > Cu > Au`. -/
def ReferenceOrder (sigma : NobleMetal → ℝ) : Prop :=
  sigma .silver > sigma .copper ∧ sigma .copper > sigma .gold

/-- The proposed alternative branch ordering `Au > Ag > Cu`. -/
def GoldFirstOrder (sigma : NobleMetal → ℝ) : Prop :=
  sigma .gold > sigma .silver ∧ sigma .silver > sigma .copper

/-- Representative conductivities in units of `10⁷ S/m`: silver `6.30`,
copper `5.96`, and gold `4.10`.  This is an empirical datum, not a prediction
of the transport definitions. -/
def referenceRoomTemperatureConductivity : NobleMetal → ℝ
  | .silver => 63 / 10
  | .copper => 149 / 25
  | .gold => 41 / 10

theorem referenceRoomTemperatureConductivity_order :
    ReferenceOrder referenceRoomTemperatureConductivity := by
  norm_num [ReferenceOrder, referenceRoomTemperatureConductivity]

/-- If silver remains at its reference value, gold must gain more than the
relative fraction `22/41` (about `53.7%`) to overtake it. -/
theorem gold_relative_gain_threshold_exact :
    (referenceRoomTemperatureConductivity .silver -
        referenceRoomTemperatureConductivity .gold) /
      referenceRoomTemperatureConductivity .gold = 22 / 41 := by
  norm_num [referenceRoomTemperatureConductivity]

theorem gold_overtakes_reference_silver_iff {gain : ℝ} :
    referenceRoomTemperatureConductivity .gold * (1 + gain) >
        referenceRoomTemperatureConductivity .silver ↔
      gain > 22 / 41 := by
  norm_num [referenceRoomTemperatureConductivity]
  constructor <;> intro h <;> linarith

/-! ## D. A crossing theorem, not an endpoint assertion -/

/-- Gold-minus-silver conductivity gap. -/
def goldSilverGap (sigma : ConductivityFamily) (parameter : ℝ) : ℝ :=
  sigma .gold parameter - sigma .silver parameter

/-- If an independently supplied relativistic transport calculation changes
the Au--Ag gap from nonpositive to nonnegative continuously, an exact
Au--Ag crossing occurs at an intermediate vacuum parameter. -/
theorem exists_gold_silver_crossing
    (sigma : ConductivityFamily) {a b : ℝ} (hab : a ≤ b)
    (hcontinuous : ContinuousOn (goldSilverGap sigma) (Set.Icc a b))
    (ha : goldSilverGap sigma a ≤ 0) (hb : 0 ≤ goldSilverGap sigma b) :
    ∃ parameter ∈ Set.Icc a b, sigma .gold parameter = sigma .silver parameter := by
  have hz : (0 : ℝ) ∈ Set.Icc (goldSilverGap sigma a) (goldSilverGap sigma b) := ⟨ha, hb⟩
  obtain ⟨parameter, hparameter, hgap⟩ := intermediate_value_Icc hab hcontinuous hz
  refine ⟨parameter, hparameter, ?_⟩
  unfold goldSilverGap at hgap
  linarith

/-! ## E. Everett support is an additional physical condition -/

/-- A finite decohered branch family carries Born weights, a branch-dependent
vacuum parameter, and a conductivity law evaluated at that parameter. -/
structure EverettConductivityModel (Branch : Type*) [Fintype Branch] where
  branchWeights : ProbDistribution Branch
  vacuumParameter : Branch → ℝ
  conductivity : ConductivityFamily

/-- Conductivity seen in one relative branch. -/
def EverettConductivityModel.branchConductivity
    {Branch : Type*} [Fintype Branch] (M : EverettConductivityModel Branch)
    (b : Branch) (X : NobleMetal) : ℝ :=
  M.conductivity X (M.vacuumParameter b)

/-- The target branch is physically present only when it has nonzero Born
weight.  Under that explicit support condition and an independently proved
transport ordering, its weight is positive and it realizes `Au > Ag > Cu`. -/
theorem EverettConductivityModel.supported_gold_first
    {Branch : Type*} [Fintype Branch] (M : EverettConductivityModel Branch)
    (b : Branch) (hsupport : M.branchWeights b ≠ 0)
    (horder : GoldFirstOrder (M.branchConductivity b)) :
    0 < (M.branchWeights b : ℝ) ∧ GoldFirstOrder (M.branchConductivity b) := by
  exact ⟨Prob.zero_lt_coe hsupport, horder⟩

end Physlib.CondensedMatter.NobleMetalBranchTransport

end

/- ZIL-BEGIN -/

zil attach Physlib.CondensedMatter.NobleMetalBranchTransport.spinAveragedFWBandEnergy_eq where
  formalizes @ "claim:foldy-wouthuysen-spin-average-removes-the-traceless-spin-orbit-term",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit.pauliHamiltonianFW",
  caveat @ "claim:this-is-the-spin-average-not-a-proof-that-the-spin-resolved-bands-are-degenerate"

zil attach Physlib.CondensedMatter.NobleMetalBranchTransport.common_charge_order_iff where
  supported_by @ "lean:Physlib.CondensedMatter.NobleMetalBranchTransport.FermiSurfaceTransportData",
  formalizes @ "claim:a-common-charge-prefactor-cannot-reorder-intrinsic-metal-conductivities",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:any-order-reversal-must-enter-through-element-dependent-band-or-scattering-data"

zil attach Physlib.CondensedMatter.NobleMetalBranchTransport.referenceRoomTemperatureConductivity_order where
  formalizes @ "claim:reference-room-temperature-pure-bulk-conductivity-order-is-silver-then-copper-then-gold",
  epistemic_status @ "data-loaded",
  supported_by @ "measurement:room-temperature-bulk-conductivity-ag-cu-au",
  caveat @ "claim:the-values-are-empirical-inputs-in-units-of-ten-to-the-seven-siemens-per-meter"

zil attach Physlib.CondensedMatter.NobleMetalBranchTransport.gold_relative_gain_threshold_exact where
  discloses @ "lean:Physlib.CondensedMatter.NobleMetalBranchTransport.referenceRoomTemperatureConductivity_order",
  formalizes @ "claim:gold-needs-relative-conductivity-gain-twenty-two-over-forty-one-to-reach-reference-silver",
  epistemic_status @ "consistency-identity",
  requires @ "claim:reference-room-temperature-pure-bulk-conductivity-order-is-silver-then-copper-then-gold",
  caveat @ "claim:this-is-the-exact-gap-implied-by-loaded-reference-values-not-a-dynamical-prediction"

zil attach Physlib.CondensedMatter.NobleMetalBranchTransport.exists_gold_silver_crossing where
  formalizes @ "claim:continuous-relativistic-transport-endpoint-sign-change-implies-an-au-ag-crossing",
  epistemic_status @ "conditional-model",
  requires @ "claim:an-independent-relativistic-band-electron-phonon-calculation-supplies-opposite-endpoint-signs",
  caveat @ "claim:continuity-proves-the-crossing-but-does-not-supply-the-gold-first-endpoint"

zil attach Physlib.CondensedMatter.NobleMetalBranchTransport.EverettConductivityModel.supported_gold_first where
  formalizes @ "claim:a-nonzero-born-weight-branch-with-gold-first-transport-data-realizes-au-ag-cu-order",
  epistemic_status @ "conditional-model",
  requires @ "claim:the-gold-first-branch-has-nonzero-born-weight",
  caveat @ "claim:many-worlds-does-not-by-itself-predict-that-the-required-effective-hamiltonian-sector-exists"

zil_file_contract physlib.nobleMetalBranchTransport where
  promises "A relativistic noble-metal transport carrier, continuum conductivity integral, common-prefactor no-reordering theorem, measured reference gap, conditional Au-Ag crossing theorem, and nonzero Everett-branch certificate."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit.pauliHamiltonianFW",
    "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.carrierEffectiveMassFromBand",
    "lean:ProbDistribution"]
  forbids_substitutes ["claiming-that-everett-branching-alone-changes-material-constants",
    "claiming-that-a-common-charge-rescaling-reverses-the-conductivity-order",
    "presenting-the-loaded-room-temperature-values-as-a-derived-cat-ept-prediction",
    "asserting-au-greater-than-ag-without-an-independent-band-and-electron-phonon-endpoint-calculation"]
  witnessed_by [Physlib.CondensedMatter.NobleMetalBranchTransport.spinAveragedFWBandEnergy_eq,
    Physlib.CondensedMatter.NobleMetalBranchTransport.intrinsicBulkConductivity_nonneg,
    Physlib.CondensedMatter.NobleMetalBranchTransport.common_charge_order_iff,
    Physlib.CondensedMatter.NobleMetalBranchTransport.referenceRoomTemperatureConductivity_order,
    Physlib.CondensedMatter.NobleMetalBranchTransport.gold_relative_gain_threshold_exact,
    Physlib.CondensedMatter.NobleMetalBranchTransport.exists_gold_silver_crossing,
    Physlib.CondensedMatter.NobleMetalBranchTransport.EverettConductivityModel.supported_gold_first]

/- ZIL-END -/

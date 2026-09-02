/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Physlib.Relativity.CliffordAlgebra
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ParametrizedDirac
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.DiracProjectors
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.SpinorNormalization
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTOneLoopScattering
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMomentLinks
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere
public import Physlib.QuantumMechanics.ComplexAction.CartanDecompositionLorentzGroup
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QuantumGravityPathIntegralSynthesis
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell
public import Physlib.Mathematics.TorusPeriodizationMeasure
public import Physlib.QFT.PerturbationTheory.FieldOpFreeAlgebra.TimeOrder
public import Physlib.QFT.PerturbationTheory.WickAlgebra.TimeContraction
public import Physlib.QFT.Wick.Consistency

/-!
# A. Fields on Poincare Homogeneous Spaces for First-Quantized QED

This module formalizes the stable algebraic layer of V. V. Varlamov,
*Towards the Quantum Electrodynamics on the Poincare Group*, arXiv:hep-th/0403070v2.
The paper develops fields on homogeneous spaces of the Poincare group, with the
eight-dimensional space `M8 = R^{1,3} x S^2_C` as the main arena for Dirac and
Maxwell fields.

The module does not duplicate the existing Dirac, Maxwell, or `SL(2,C)` code. It
connects Varlamov's construction to existing Physlib components:

* `FirstQuantizedQED.ParametrizedDirac` supplies the unimodular translation phase.
* `FirstQuantizedQED.DiracProjectors` supplies the Dirac energy projectors.
* `FirstQuantizedQED.SpinorNormalization` supplies Bennett's forward/backward
  spinor orthonormality.
* `FirstQuantizedQED.CPTAntiunitary` supplies the first-quantized `C`, `P`, `T`,
  and `CPT` spinor actions.
* `FirstQuantizedQED.CPTOneLoopScattering` supplies the finite one-loop and
  scattering-side `CPT` invariance lemmas.
* `FirstQuantizedQED.AnomalousMomentLinks` supplies the Pauli
  `sigma^{mu nu} F_{mu nu}` interaction and its gauge-invariance statement.
* `AdSCFT.WeylSpinorPoincareSphere` supplies the Weyl-spinor Mobius action on
  `CP1`.
* `PTSymmetricQFT.MaxwellFaraday` supplies the Faraday tensor, Bianchi identity,
  and gauge invariance.
* `ComptonClock.PoincareCasimirMassShell` supplies the Poincare mass-shell
  terminology.
* `QFT.PerturbationTheory.FieldOpFreeAlgebra` supplies the creation,
  annihilation, supercommutator, and time-ordering algebra.

## A.1. What Is Formalized

* `PoincareM8`, the coordinate-level product `R^{1,3} x C^3` used for the complex
  two-sphere model.
* `VarlamovHomogeneousSpace`, the four homogeneous spaces `M10`, `M8`, `M7`, and
  `M6` from Section 6, with their dimensions and stabilizer labels.
* `translationPlaneWave` and `minkowskiPlaneWave`, with the representation laws
  for one-parameter translations and for the full `T4` translation subgroup.
* `factorizedPoincareField`, Varlamov's separated mode
  `f(x,z) = phi(z) psi(x)`, and its covariance under time translations.
* `SU2PairT4Action` and `FinitePoincareElement`, the finite-dimensional
  `SU(2) x SU(2) ⋉ T4` action layer used in Section 6.1.
* `finitePoincareMatrixElement` and `finitePoincareHarmonicExpansion`, the finite
  matrix-element expansion `e^{i p x} M(g)`.
* `SU2EulerAngles`, `SU11EulerAngles`, and their matrix lemmas, reusing the
  Cartan-decomposition files for Sections 2--4 instead of restating their matrix
  algebra here.
* `SU2FiniteRepresentation`, `SU2PeterWeylMode`, `SU11HarmonicMode`,
  `SL2CSeriesParameter`, and `SL2CHypersphericalSystem`, the finite
  harmonic-analysis interfaces for the paper's Wigner, Peter-Weyl,
  SU(1,1)-series, and SL(2,C) hyperspherical-function layers.
* `poincareHarmonicSeries`, the corresponding countable matrix-element expansion
  for the `SU(2) x SU(2) ⋉ T4` harmonic layer.
* `finiteM8FourierExpansion` and `finiteM8FourierCoefficient`, the finite `M8`
  Fourier-series skeleton reusing the existing `M8` product integral.
* `sl2cMinkowskiAction` and `poincareM8LinearAction`, reusing the existing
  `SL(2,C) -> Lorentz` double-cover map for the Minkowski factor and a
  quadratic-form-preserving ambient action for the complex two-sphere factor.
* `riemannSilberstein`, the Maxwell field vector `E + i B`, with injectivity back
  to real electric and magnetic components.
* `maxwellRiemannSilbersteinBispinor`, the six-component
  Majorana-Oppenheimer field `(E - iB, E + iB)` used in Section 9.
* `finiteSphereModeExpansion`, the finite boundary-mode expansion used before
  the full hyperspherical-harmonic convergence theory is available.
* `varlamovFirstOrderLagrangianDensity`, the finite first-order Lagrangian density
  from Section 7, together with first-variation identities deriving the field equations.
* `varlamovPoincareGroupResidual`, the finite `M10 = R^{1,3} x L6` field equation
  split into spacetime and Lorentz-group derivative directions.
* `SolvesVarlamovM8BoundaryValueProblem`, the finite `M8` boundary-value interface
  with boundary trace and bulk first-order equation.
* `varlamovDiracGamma`, `varlamovSpacetimeDiracResidual`,
  `varlamovGroupDiracResidual`, and `diracRadialBesselResidual`, the Section 8
  Dirac matrices, spacetime/group equations, separated series, and radial
  recurrence layer, all expressed using the existing Clifford matrices.
* `VarlamovBoundaryValueProblem`, the finite boundary-value problem on the complex
  two-sphere.
* `VarlamovLambdaCovariance` and the rotation/boost commutator predicates encoding
  the covariance constraints from Eqs. 104--108.
* `finiteM8ProductIntegral`, the finite-mode product-measure skeleton for
  Section 10's replacement of `d4x` by `d4x d4g` on `M8`, with a proved
  factorization on separated integrands.
* `finiteM8ActionIntegral` and `finiteM8InteractionHamiltonianDensity`, the
  finite form of `A = integral L` and `H_I = -L_I`, with the corresponding
  Dyson-exponent sign identity.
* `poincareQEDIndexedInteractionLagrangian`, the Section 10 operator-valued
  indexed interaction density `psi-bar_a A_m psi_b` in the existing
  `FieldOpFreeAlgebra`.
* `finiteM8OperatorIntegral`, `IsFiniteM8OperatorMeasureInvariant`, and
  `poincareQEDDysonPartialSum`, the operator-valued sampled `M8` integral,
  finite invariant-measure predicate, and finite Dyson/scattering series.
* `PoincareQEDInteractionTensor`, `poincareQEDScatteringOperatorFormalSeries`,
  and `poincareQEDScatteringMatrixElementFormalSeries`, the named Section 10
  vertex/action object and all-order formal Dyson/scattering families.
* `diracVacuumTwoPointFunction` and the `diracPositiveFrequencyKernel` /
  `diracNegativeFrequencyKernel` pair, the Section 8.1 CAR-kernel and
  two-point-function layer connected to the existing Wick algebra.
* `finitePhotonModeOperator`, `PhotonAsymptoticCCRKernelRelation`, and
  `photonDistributionKernel_fintype`, the finite photon operator expansion,
  CCR-kernel interface, and mode-kernel decomposition from Section 9.1.
* `diracDistributionKernel_fintype`, `diracAsymptoticCAROperatorKernel`, and
  the time-ordering lemmas for finite Dirac/Maxwell mode sums, completing the
  finite second-quantized Dirac/Maxwell interface used by the interaction density.
* `finiteDiracAsymptoticCAROperatorKernel` and
  `finitePhotonAsymptoticCCROperatorKernel`, the finite summed CAR/CCR kernels
  obtained directly from the second-quantized mode operators.
* Bridge lemmas reusing Bennett's parametrized `tau` phase, mass shell,
  spinor orthonormality, Dirac projectors, Maxwell Faraday/Bianchi facts,
  Pauli coupling, Weyl-spinor Mobius action, and first-quantized `CPT` algebra.
* `bennettTauInteractionVertex` and
  `poincareQEDBennettTauScatteringOperatorPartial`, the Section 10 interaction
  and finite scattering operators specialized to Bennett's `tau` worldline
  phase and the existing Pauli/anomalous-moment vertex.
* `sl2cHypersphericalSeries_hasSum_of_norm_bound`,
  `realizedDiracElectronPositronOperatorModePartialSum_tendsto_of_norm_bound`,
  `realizedPhotonInOutOperatorModePartialSum_tendsto_of_norm_bound`,
  `realizedPoincareQEDInteractionTensorScatteringSeries_tendsto_of_norm_bound`,
  and `realizedPoincareQEDBennettTauScatteringSeries_tendsto_of_norm_bound`, the
  analytic convergence layer: hyperspherical series, full operator-valued mode
  expansions, Section 10 scattering operators, and Bennett-parametrized
  scattering limits are proved from explicit norm-majorant hypotheses.

## A.2. Remaining Analytic Targets

The remaining analytic work is no longer a missing interface: this file now has
`HasSum` and `Tendsto` theorems for the relevant infinite series.  What remains
for concrete applications is to supply paper-specific estimates showing that the
chosen hyperspherical functions, operator realization, and interaction action
satisfy the stated norm-majorant hypotheses.

## A.3. References

* V. V. Varlamov, *Towards the Quantum Electrodynamics on the Poincare Group*,
  arXiv:hep-th/0403070v2 (2004), especially the factorization
  `f(x,z)=phi_n(z) psi_n(x)`, Sections 6--9.
* A. F. Bennett, *First Quantized Electrodynamics*, arXiv:1406.0750v3, for the
  existing parametrized-QED phase and projector infrastructure.
* L. Silberstein, E. Majorana, and J. R. Oppenheimer on the
  Riemann-Silberstein / Majorana-Oppenheimer representation of Maxwell theory.
-/

set_option autoImplicit false

open scoped BigOperators
open scoped MatrixGroups

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields

open Matrix
open Complex spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ParametrizedDirac
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.DiracProjectors
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.SpinorNormalization
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTOneLoopScattering
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMomentLinks
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere
open Physlib.QuantumMechanics.ComplexAction.CartanDecompositionDoubleCovers
open Physlib.QuantumMechanics.ComplexAction.CartanDecompositionLorentzGroup
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QuantumGravityPathIntegralSynthesis
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QuantumMechanics.SpinDensityFunctionalOperators
open Physlib.QFT.Wick.Consistency
open FieldSpecification
open FieldSpecification.FieldOpFreeAlgebra

/-! ## B. Coordinate Model for `M8` -/

/-- Minkowski coordinates indexed as one time coordinate and three spatial coordinates. -/
abbrev MinkowskiPoint := Sum (Fin 1) (Fin 3) -> ℝ

/-- A point of the ambient coordinate space `C^3` of the complex two-sphere. -/
abbrev ComplexTwoSpherePoint := Fin 3 -> ℂ

/-- Varlamov's `M8 = R^{1,3} x S^2_C` at the coordinate level. -/
abbrev PoincareM8 := MinkowskiPoint × ComplexTwoSpherePoint

/-- Tangent index for the four spacetime directions. -/
abbrev SpaceTimeTangentIndex := Fin 4

/-- Tangent index for the six Lorentz-group directions. -/
abbrev LorentzGroupTangentIndex := Fin 6

/-- Tangent index for the full `M10 = R^{1,3} x L6` Poincare-group space. -/
abbrev PoincareGroupTangentIndex := Sum SpaceTimeTangentIndex LorentzGroupTangentIndex

/-- The time coordinate of a Minkowski point. -/
def timeCoord (x : MinkowskiPoint) : ℝ := x (Sum.inl 0)

/-- Time translation by a real parameter, leaving spatial coordinates fixed. -/
def timeTranslate (a : ℝ) (x : MinkowskiPoint) : MinkowskiPoint
  | Sum.inl 0 => x (Sum.inl 0) + a
  | Sum.inr i => x (Sum.inr i)

/-! ## B.1. Section 6 Homogeneous Spaces -/

/-- The four Poincare homogeneous spaces used in Varlamov Section 6. -/
inductive VarlamovHomogeneousSpace : Type where
  | M10 : VarlamovHomogeneousSpace
  | M8 : VarlamovHomogeneousSpace
  | M7 : VarlamovHomogeneousSpace
  | M6 : VarlamovHomogeneousSpace
deriving DecidableEq, Repr

/-- Dimension of the homogeneous space in Varlamov's Section 6 list. -/
def VarlamovHomogeneousSpace.dimension : VarlamovHomogeneousSpace -> ℕ
  | .M10 => 10
  | .M8 => 8
  | .M7 => 7
  | .M6 => 6

/-- Dimension of the internal Lorentz homogeneous factor after removing `R^{1,3}`. -/
def VarlamovHomogeneousSpace.internalDimension (M : VarlamovHomogeneousSpace) : ℕ :=
  M.dimension - 4

/-- Stabilizer label from Varlamov's Section 6 classification. -/
def VarlamovHomogeneousSpace.stabilizerLabel : VarlamovHomogeneousSpace -> String
  | .M10 => "0"
  | .M8 => "Omega_c_psi"
  | .M7 => "SU(2)"
  | .M6 => "Omega_c_psi, Omega_tau, Omega_epsilon"

/-- All four spaces in Section 6 contain the four-dimensional translation factor. -/
lemma VarlamovHomogeneousSpace.dimension_eq_four_add_internal
    (M : VarlamovHomogeneousSpace) :
    M.dimension = 4 + M.internalDimension := by
  cases M <;> rfl

/-- `M8` has the complex two-sphere internal dimension used by the main construction. -/
@[simp] lemma VarlamovHomogeneousSpace.M8_internalDimension :
    VarlamovHomogeneousSpace.internalDimension .M8 = 4 := rfl

/-! ## C. Translation Modes and Separated Fields -/

/-- The one-parameter translation plane wave `psi_k(x) = exp(i k x)`. -/
noncomputable def translationPlaneWave (k x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((k * x : ℝ)) : ℂ))

/-- Translation plane waves form a representation of the additive translation group. -/
lemma translationPlaneWave_add (k x y : ℝ) :
    translationPlaneWave k (x + y) = translationPlaneWave k x * translationPlaneWave k y := by
  unfold translationPlaneWave
  have harg0 : (((k * (x + y) : ℝ) : ℂ)) =
      (((k * x : ℝ) : ℂ)) + (((k * y : ℝ) : ℂ)) := by
    norm_num
    ring
  rw [harg0, mul_add, Complex.exp_add]

/-- Translation plane waves have unit norm, reusing the existing parametrized-QED phase lemma. -/
lemma translationPlaneWave_norm (k x : ℝ) : ‖translationPlaneWave k x‖ = 1 := by
  simpa [translationPlaneWave] using bennett_tau_phase_unimodular k x

/-- Varlamov's separated field mode `f(x,z)=phi(z) psi(x)` on `M8`. -/
noncomputable def factorizedPoincareField (internal : ComplexTwoSpherePoint -> ℂ) (k : ℝ) :
    PoincareM8 -> ℂ :=
  fun q => internal q.2 * translationPlaneWave k (timeCoord q.1)

/-- A separated Poincare-group field transforms by the translation character. -/
lemma factorizedPoincareField_timeTranslate
    (internal : ComplexTwoSpherePoint -> ℂ) (k a : ℝ) (x : MinkowskiPoint)
    (z : ComplexTwoSpherePoint) :
    factorizedPoincareField internal k (timeTranslate a x, z) =
      factorizedPoincareField internal k (x, z) * translationPlaneWave k a := by
  simp [factorizedPoincareField, timeCoord, timeTranslate, translationPlaneWave_add]
  ring

/-- Time translation preserves the norm of a separated field mode. -/
lemma factorizedPoincareField_norm_timeTranslate
    (internal : ComplexTwoSpherePoint -> ℂ) (k a : ℝ) (x : MinkowskiPoint)
    (z : ComplexTwoSpherePoint) :
    ‖factorizedPoincareField internal k (timeTranslate a x, z)‖ =
      ‖factorizedPoincareField internal k (x, z)‖ := by
  rw [factorizedPoincareField_timeTranslate, norm_mul, translationPlaneWave_norm, mul_one]

/-- Translation by a four-vector on the Minkowski factor. -/
def minkowskiTranslate (a x : MinkowskiPoint) : MinkowskiPoint :=
  fun mu => x mu + a mu

/-- The coordinate dot product used in the `T4` plane-wave phase. -/
def minkowskiDot (p x : MinkowskiPoint) : ℝ :=
  ∑ mu, p mu * x mu

/-- The full translation-subgroup plane wave `exp(i p · x)`. -/
noncomputable def minkowskiPlaneWave (p x : MinkowskiPoint) : ℂ :=
  Complex.exp (Complex.I * (minkowskiDot p x : ℂ))

/-- The coordinate dot product is additive in the translated argument. -/
lemma minkowskiDot_translate (p a x : MinkowskiPoint) :
    minkowskiDot p (minkowskiTranslate a x) = minkowskiDot p x + minkowskiDot p a := by
  simp [minkowskiDot, minkowskiTranslate, mul_add, Finset.sum_add_distrib]

/-- Full `T4` plane waves multiply under addition of translation arguments. -/
lemma minkowskiPlaneWave_add (p x y : MinkowskiPoint) :
    minkowskiPlaneWave p (fun mu => x mu + y mu) =
      minkowskiPlaneWave p x * minkowskiPlaneWave p y := by
  unfold minkowskiPlaneWave minkowskiDot
  have harg :
      ((∑ mu, p mu * (x mu + y mu) : ℝ) : ℂ) =
        ((∑ mu, p mu * x mu : ℝ) : ℂ) + ((∑ mu, p mu * y mu : ℝ) : ℂ) := by
    simp [mul_add, Finset.sum_add_distrib]
  rw [harg, mul_add, Complex.exp_add]

/-- Translation of the argument factors a full `T4` plane wave by the translation phase. -/
lemma minkowskiPlaneWave_translate (p a x : MinkowskiPoint) :
    minkowskiPlaneWave p (minkowskiTranslate a x) =
      minkowskiPlaneWave p x * minkowskiPlaneWave p a := by
  change minkowskiPlaneWave p (fun mu => x mu + a mu) =
    minkowskiPlaneWave p x * minkowskiPlaneWave p a
  exact minkowskiPlaneWave_add p x a

/-- Full `T4` plane waves have unit norm. -/
lemma minkowskiPlaneWave_norm (p x : MinkowskiPoint) :
    ‖minkowskiPlaneWave p x‖ = 1 := by
  simp [minkowskiPlaneWave]

/-- A separated `M8` field with a full `T4` plane wave on the Minkowski factor. -/
noncomputable def factorizedPoincareField4
    (internal : ComplexTwoSpherePoint -> ℂ) (p : MinkowskiPoint) : PoincareM8 -> ℂ :=
  fun q => internal q.2 * minkowskiPlaneWave p q.1

/-- Four-translation of a separated `M8` field factors by the corresponding `T4` phase. -/
lemma factorizedPoincareField4_translate
    (internal : ComplexTwoSpherePoint -> ℂ) (p a : MinkowskiPoint) (q : PoincareM8) :
    factorizedPoincareField4 internal p (minkowskiTranslate a q.1, q.2) =
      factorizedPoincareField4 internal p q * minkowskiPlaneWave p a := by
  simp [factorizedPoincareField4, minkowskiPlaneWave_translate, mul_assoc]

/-- Four-translations preserve the norm of separated `M8` plane-wave fields. -/
lemma factorizedPoincareField4_norm_translate
    (internal : ComplexTwoSpherePoint -> ℂ) (p a : MinkowskiPoint) (q : PoincareM8) :
    ‖factorizedPoincareField4 internal p (minkowskiTranslate a q.1, q.2)‖ =
      ‖factorizedPoincareField4 internal p q‖ := by
  rw [factorizedPoincareField4_translate, norm_mul, minkowskiPlaneWave_norm, mul_one]

/-! ## C.1. Finite `SU(2) x SU(2) ⋉ T4` Harmonic Layer -/

/-- The standard matrix group used for the two finite-dimensional `SU(2)` factors. -/
abbrev SU2Matrix := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- The finite-dimensional Lorentz factor written locally as `SU(2) x SU(2)`. -/
abbrev SU2Pair := SU2Matrix × SU2Matrix

/-- A spinor coordinate for the undotted or dotted `SU(2)` factor. -/
abbrev SpinorCoordinate := Fin 2 -> ℂ

/-- A semidirect action of the finite `SU(2) x SU(2)` Lorentz factor on the translation
group `T4`, stated as the laws needed to model `SU(2) x SU(2) ⋉ T4`. -/
structure SU2PairT4Action where
  /-- Action of a finite Lorentz pair on a translation four-vector. -/
  act : SU2Pair -> MinkowskiPoint -> MinkowskiPoint
  /-- The identity Lorentz pair acts trivially on translations. -/
  act_one : ∀ x, act (1, 1) x = x
  /-- The action respects multiplication in the `SU(2) x SU(2)` factor. -/
  act_mul : ∀ g h x, act (g.1 * h.1, g.2 * h.2) x = act g (act h x)
  /-- Each Lorentz-pair action is additive on the translation group. -/
  act_add : ∀ g x y, act g (fun mu => x mu + y mu) =
    fun mu => act g x mu + act g y mu

/-- An element of the finite-dimensional Poincare model
`SU(2) x SU(2) ⋉ T4`. -/
structure FinitePoincareElement where
  /-- Left `SU(2)` factor. -/
  left : SU2Matrix
  /-- Right `SU(2)` factor. -/
  right : SU2Matrix
  /-- Translation component in `T4`. -/
  translation : MinkowskiPoint

/-- The `SU(2) x SU(2)` part of a finite Poincare element. -/
def FinitePoincareElement.su2Pair (g : FinitePoincareElement) : SU2Pair :=
  (g.left, g.right)

/-- The identity element of the finite `SU(2) x SU(2) ⋉ T4` model. -/
def finitePoincareElementOne : FinitePoincareElement where
  left := 1
  right := 1
  translation := fun _ => 0

/-- The semidirect-product multiplication law
`(a,g)(b,h) = (a + g b, gh)` for the finite Poincare model. -/
def finitePoincareElementMul (D : SU2PairT4Action)
    (g h : FinitePoincareElement) : FinitePoincareElement where
  left := g.left * h.left
  right := g.right * h.right
  translation := fun mu => g.translation mu + D.act g.su2Pair h.translation mu

/-- The finite Poincare element acts on the Minkowski coordinate by the Lorentz-pair
action followed by translation. -/
def finitePoincareElementAct (D : SU2PairT4Action)
    (g : FinitePoincareElement) (x : MinkowskiPoint) : MinkowskiPoint :=
  minkowskiTranslate g.translation (D.act g.su2Pair x)

/-- The identity finite Poincare element fixes every Minkowski coordinate. -/
lemma finitePoincareElementAct_one (D : SU2PairT4Action) (x : MinkowskiPoint) :
    finitePoincareElementAct D finitePoincareElementOne x = x := by
  funext mu
  simp [finitePoincareElementAct, finitePoincareElementOne, minkowskiTranslate,
    FinitePoincareElement.su2Pair, D.act_one]

/-- The finite Poincare action composes according to the semidirect-product law. -/
lemma finitePoincareElementAct_mul (D : SU2PairT4Action)
    (g h : FinitePoincareElement) (x : MinkowskiPoint) :
    finitePoincareElementAct D (finitePoincareElementMul D g h) x =
      finitePoincareElementAct D g (finitePoincareElementAct D h x) := by
  funext mu
  have hadd := congrFun (D.act_add g.su2Pair (D.act h.su2Pair x) h.translation) mu
  have hmul := congrFun (D.act_mul g.su2Pair h.su2Pair x) mu
  have hadd' :
      D.act (g.left, g.right) (minkowskiTranslate h.translation (D.act (h.left, h.right) x))
          mu =
        D.act (g.left, g.right) (D.act (h.left, h.right) x) mu +
          D.act (g.left, g.right) h.translation mu := by
    change
      D.act (g.left, g.right) (fun mu => D.act (h.left, h.right) x mu + h.translation mu)
          mu =
        D.act (g.left, g.right) (D.act (h.left, h.right) x) mu +
          D.act (g.left, g.right) h.translation mu
    simpa [FinitePoincareElement.su2Pair] using hadd
  have hmul' :
      D.act (g.left * h.left, g.right * h.right) x mu =
        D.act (g.left, g.right) (D.act (h.left, h.right) x) mu := by
    simpa [FinitePoincareElement.su2Pair] using hmul
  simp only [finitePoincareElementAct, finitePoincareElementMul, minkowskiTranslate,
    FinitePoincareElement.su2Pair]
  rw [hmul', hadd']
  ring_nf

/-! ### C.1.1. Finite Representation Law -/

/-- A finite linear representation of the semidirect product
`SU(2) x SU(2) ⋉ T4` on a complex vector space.  This packages the representation
law used by the harmonic expansion in Section 6. -/
structure SU2PairT4LinearRepresentation (D : SU2PairT4Action) (V : Type*)
    [AddCommMonoid V] [Module ℂ V] where
  /-- The representation operator assigned to a finite Poincare element. -/
  rho : FinitePoincareElement -> V →ₗ[ℂ] V
  /-- The identity element acts by the identity linear map. -/
  rho_one : rho finitePoincareElementOne = LinearMap.id
  /-- Multiplication in the semidirect product is represented by composition. -/
  rho_mul : ∀ g h, rho (finitePoincareElementMul D g h) = (rho g).comp (rho h)

/-- The representation law in pointwise form. -/
lemma SU2PairT4LinearRepresentation.map_mul_apply {D : SU2PairT4Action}
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (R : SU2PairT4LinearRepresentation D V) (g h : FinitePoincareElement) (v : V) :
    R.rho (finitePoincareElementMul D g h) v = R.rho g (R.rho h v) := by
  rw [R.rho_mul]
  rfl

/-! ### C.1.2. Sections 2 and 2.1: `SU(2)` Euler Coordinates and Matrix Elements -/

/-- Euler-angle coordinates `(phi, theta, psi)` for the compact `SU(2)` factor. -/
structure SU2EulerAngles where
  /-- First maximal-torus angle. -/
  phi : ℝ
  /-- Middle rotation angle. -/
  theta : ℝ
  /-- Second maximal-torus angle. -/
  psi : ℝ

/-- The `2 x 2` Euler matrix for `SU(2)`, delegated to
`CartanDecompositionDoubleCovers.su2Euler`. -/
noncomputable def SU2EulerAngles.matrix (a : SU2EulerAngles) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  su2Euler a.phi a.theta a.psi

/-- The `SU(2)` Euler matrix is unitary. -/
lemma SU2EulerAngles.matrix_unitary (a : SU2EulerAngles) :
    (a.matrix)ᴴ * a.matrix = 1 :=
  su2Euler_unitary a.phi a.theta a.psi

/-- The `SU(2)` Euler matrix has determinant one. -/
lemma SU2EulerAngles.matrix_det (a : SU2EulerAngles) :
    (a.matrix).det = 1 :=
  su2Euler_det a.phi a.theta a.psi

/-- The two phase variables of the `SU(2)` Euler chart form a two-torus. -/
abbrev SU2EulerPhaseTorus := UnitAddTorus (Fin 2)

/-- The existing torus fundamental-domain equivalence used for the two Euler phases. -/
noncomputable def su2EulerPhaseFundamentalDomain :
    SU2EulerPhaseTorus ≃ᵐ (Fin 2 -> Set.Ioc (0 : ℝ) (0 + 1)) :=
  Physlib.Mathematics.TorusPeriodizationMeasure.torusEquivIoc (Fin 2)

/-- The Euler-angle Haar density factor `sin(theta)/(16*pi*pi)` in the compact chart. -/
noncomputable def su2EulerHaarDensity (a : SU2EulerAngles) : ℝ :=
  Real.sin a.theta / (16 * Real.pi * Real.pi)

/-- On the standard `0 <= theta <= pi` interval, the compact Euler density is
non-negative. -/
lemma su2EulerHaarDensity_nonneg (a : SU2EulerAngles)
    (h0 : 0 ≤ a.theta) (hpi : a.theta ≤ Real.pi) :
    0 ≤ su2EulerHaarDensity a := by
  unfold su2EulerHaarDensity
  exact div_nonneg (Real.sin_nonneg_of_mem_Icc ⟨h0, hpi⟩) (by positivity)

/-- A finite-dimensional matrix representation of the compact `SU(2)` factor. -/
structure SU2FiniteRepresentation (n : ℕ) where
  /-- Matrix assigned to a compact group element. -/
  rho : SU2Matrix -> Matrix (Fin n) (Fin n) ℂ
  /-- The identity group element is represented by the identity matrix. -/
  rho_one : rho 1 = 1
  /-- Multiplication is represented by matrix multiplication. -/
  rho_mul : ∀ g h, rho (g * h) = rho g * rho h

/-- The Wigner-type matrix element of a supplied finite `SU(2)` representation. -/
noncomputable def su2WignerMatrixElement {n : ℕ}
    (R : SU2FiniteRepresentation n) (i j : Fin n) : SU2Matrix -> ℂ :=
  fun g => R.rho g i j

/-- At the identity, the Wigner matrix element is the Kronecker matrix entry. -/
lemma su2WignerMatrixElement_one {n : ℕ}
    (R : SU2FiniteRepresentation n) (i j : Fin n) :
    su2WignerMatrixElement R i j 1 = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  simp [su2WignerMatrixElement, R.rho_one]

/-- Matrix-element multiplication follows from the representation law. -/
lemma su2WignerMatrixElement_mul {n : ℕ}
    (R : SU2FiniteRepresentation n) (i j : Fin n) (g h : SU2Matrix) :
    su2WignerMatrixElement R i j (g * h) =
      ∑ k, su2WignerMatrixElement R i k g * su2WignerMatrixElement R k j h := by
  simp [su2WignerMatrixElement, R.rho_mul, Matrix.mul_apply]

/-- A complex-linear integration functional on the compact `SU(2)` factor. -/
abbrev SU2HaarFunctional := (SU2Matrix -> ℂ) →ₗ[ℂ] ℂ

/-- Inner product induced by a supplied compact `SU(2)` integration functional. -/
noncomputable def su2WignerInnerProduct
    (haar : SU2HaarFunctional) (f g : SU2Matrix -> ℂ) : ℂ :=
  haar (fun x => star (f x) * g x)

/-- Orthogonality relation for a finite family of `SU(2)` matrix elements with respect
to a supplied compact-group integration functional. -/
def IsSU2WignerOrthogonal {n : ℕ}
    (haar : (SU2Matrix -> ℂ) -> ℂ) (R : SU2FiniteRepresentation n) : Prop :=
  ∀ i j k l,
    haar (fun g => star (su2WignerMatrixElement R i j g) *
      su2WignerMatrixElement R k l g) =
      if i = k ∧ j = l then (1 : ℂ) else 0

/-- Linear-functional form of the compact `SU(2)` Wigner orthogonality relation. -/
def IsSU2WignerOrthogonalLinear {n : ℕ}
    (haar : SU2HaarFunctional) (R : SU2FiniteRepresentation n) : Prop :=
  IsSU2WignerOrthogonal (fun f => haar f) R

/-- Orthogonality evaluated as the `SU(2)` Wigner inner product. -/
lemma su2WignerInnerProduct_matrixElement {n : ℕ}
    (haar : SU2HaarFunctional) (R : SU2FiniteRepresentation n)
    (horth : IsSU2WignerOrthogonalLinear haar R) (i j k l : Fin n) :
    su2WignerInnerProduct haar (su2WignerMatrixElement R i j)
        (su2WignerMatrixElement R k l) =
      if i = k ∧ j = l then (1 : ℂ) else 0 :=
  horth i j k l

/-- Finite expansion using matrix elements of one fixed compact `SU(2)` representation. -/
noncomputable def finiteSU2MatrixElementExpansion {n : ℕ} {ι : Type*} [Fintype ι]
    (R : SU2FiniteRepresentation n) (coeff : ι -> ℂ)
    (row col : ι -> Fin n) : SU2Matrix -> ℂ :=
  fun g => ∑ a, coeff a * su2WignerMatrixElement R (row a) (col a) g

/-- Coefficient extraction for a finite `SU(2)` Wigner expansion against an
orthogonal matrix-element family. -/
lemma su2WignerCoefficientExtraction {n : ℕ} {ι : Type*} [Fintype ι]
    (haar : SU2HaarFunctional) (R : SU2FiniteRepresentation n)
    (horth : IsSU2WignerOrthogonalLinear haar R)
    (coeff : ι -> ℂ) (row col : ι -> Fin n) (i j : Fin n) :
    su2WignerInnerProduct haar (su2WignerMatrixElement R i j)
        (finiteSU2MatrixElementExpansion R coeff row col) =
      ∑ a, coeff a * (if i = row a ∧ j = col a then (1 : ℂ) else 0) := by
  unfold su2WignerInnerProduct finiteSU2MatrixElementExpansion
  have hsum :
      (fun g => star (su2WignerMatrixElement R i j g) *
          (∑ a, coeff a * su2WignerMatrixElement R (row a) (col a) g)) =
        ∑ a, (coeff a) •
          (fun g => star (su2WignerMatrixElement R i j g) *
            su2WignerMatrixElement R (row a) (col a) g) := by
    funext g
    rw [Finset.mul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    show star (su2WignerMatrixElement R i j g) *
        (coeff a * su2WignerMatrixElement R (row a) (col a) g) =
      coeff a *
        (star (su2WignerMatrixElement R i j g) *
          su2WignerMatrixElement R (row a) (col a) g)
    ring
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [map_smul]
  have h := horth i j (row a) (col a)
  simpa [smul_eq_mul] using congrArg (fun x : ℂ => coeff a * x) h

/-- A single Peter-Weyl mode: one finite `SU(2)` representation and two matrix indices. -/
structure SU2PeterWeylMode where
  /-- Dimension of the finite representation space. -/
  dim : ℕ
  /-- The finite representation used by the mode. -/
  rep : SU2FiniteRepresentation dim
  /-- Row index of the matrix element. -/
  row : Fin dim
  /-- Column index of the matrix element. -/
  col : Fin dim

/-- Evaluation of one finite Peter-Weyl mode. -/
noncomputable def SU2PeterWeylMode.eval (mode : SU2PeterWeylMode) :
    SU2Matrix -> ℂ :=
  su2WignerMatrixElement mode.rep mode.row mode.col

/-- Finite Peter-Weyl expansion by compact `SU(2)` matrix elements. -/
noncomputable def finiteSU2PeterWeylExpansion {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (mode : ι -> SU2PeterWeylMode) : SU2Matrix -> ℂ :=
  fun g => ∑ i, coeff i * (mode i).eval g

/-- The finite Peter-Weyl expansion is linear in its coefficient sequence. -/
lemma finiteSU2PeterWeylExpansion_add_coeff {ι : Type*} [Fintype ι]
    (coeff₁ coeff₂ : ι -> ℂ) (mode : ι -> SU2PeterWeylMode) (g : SU2Matrix) :
    finiteSU2PeterWeylExpansion (fun i => coeff₁ i + coeff₂ i) mode g =
      finiteSU2PeterWeylExpansion coeff₁ mode g +
        finiteSU2PeterWeylExpansion coeff₂ mode g := by
  unfold finiteSU2PeterWeylExpansion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-! ### C.1.3. Sections 3 and 3.1: `SU(1,1)` Euler Coordinates and Series Data -/

/-- Euler/Cartan coordinates `(phi, rapidity, psi)` for the noncompact `SU(1,1)` factor. -/
structure SU11EulerAngles where
  /-- First compact-torus angle. -/
  phi : ℝ
  /-- Middle noncompact boost coordinate. -/
  rapidity : ℝ
  /-- Second compact-torus angle. -/
  psi : ℝ

/-- The `2 x 2` Euler matrix for `SU(1,1)`, delegated to
`CartanDecompositionDoubleCovers.su11Euler`. -/
noncomputable def SU11EulerAngles.matrix (a : SU11EulerAngles) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  su11Euler a.phi a.rapidity a.psi

/-- The `SU(1,1)` Euler matrix preserves the `(1,-1)` form represented by `pauliZ`. -/
lemma SU11EulerAngles.matrix_pseudoUnitary (a : SU11EulerAngles) :
    (a.matrix)ᴴ * pauliZ * a.matrix = pauliZ :=
  su11Euler_pseudoUnitary a.phi a.rapidity a.psi

/-- The `SU(1,1)` Euler matrix has determinant one. -/
lemma SU11EulerAngles.matrix_det (a : SU11EulerAngles) :
    (a.matrix).det = 1 :=
  su11Euler_det a.phi a.rapidity a.psi

/-- A concrete `SU(1,1)` matrix as a matrix preserving `pauliZ` and determinant one. -/
structure SU11Matrix where
  /-- Underlying complex `2 x 2` matrix. -/
  val : Matrix (Fin 2) (Fin 2) ℂ
  /-- Preservation of the indefinite Hermitian form `diag(1,-1)`. -/
  pseudoUnitary : valᴴ * pauliZ * val = pauliZ
  /-- Special condition. -/
  det_one : val.det = 1

/-- The `SU(1,1)` matrix obtained from Euler/Cartan coordinates. -/
noncomputable def SU11EulerAngles.toMatrix (a : SU11EulerAngles) : SU11Matrix where
  val := a.matrix
  pseudoUnitary := a.matrix_pseudoUnitary
  det_one := a.matrix_det

/-- The noncompact Cartan Haar-density factor `sinh(rapidity)` in the `KAK` chart. -/
noncomputable def su11KAKHaarDensity (a : SU11EulerAngles) : ℝ :=
  Real.sinh a.rapidity

/-- On nonnegative rapidity, the `SU(1,1)` Cartan density factor is non-negative. -/
lemma su11KAKHaarDensity_nonneg (a : SU11EulerAngles) (h : 0 ≤ a.rapidity) :
    0 ≤ su11KAKHaarDensity a := by
  simpa [su11KAKHaarDensity] using (Real.sinh_nonneg_iff.mpr h)

/-- Series class used for the `SU(1,1)` harmonic modes in Varlamov Section 3.1. -/
inductive SU11SeriesKind where
  | discrete : SU11SeriesKind
  | principal : SU11SeriesKind
  | supplementary : SU11SeriesKind
deriving DecidableEq, Repr

/-- Descriptor for a noncompact `SU(1,1)` representation-series label. -/
structure SU11SeriesDescriptor where
  /-- Which series the label belongs to. -/
  kind : SU11SeriesKind
  /-- Complex spectral parameter. -/
  spectral : ℂ
  /-- Left `K`-type weight. -/
  leftWeight : ℤ
  /-- Right `K`-type weight. -/
  rightWeight : ℤ

/-- Principal-series condition for an `SU(1,1)` descriptor. -/
def IsSU11PrincipalSeriesDescriptor (p : SU11SeriesDescriptor) : Prop :=
  p.kind = .principal ∧ p.spectral.re = 0

/-- Discrete-series condition for an `SU(1,1)` descriptor. -/
def IsSU11DiscreteSeriesDescriptor (p : SU11SeriesDescriptor) : Prop :=
  p.kind = .discrete ∧ p.leftWeight = p.rightWeight

/-- Supplementary-series condition for an `SU(1,1)` descriptor. -/
def IsSU11SupplementarySeriesDescriptor (p : SU11SeriesDescriptor) : Prop :=
  p.kind = .supplementary ∧ p.spectral.im = 0 ∧ |p.spectral.re| < 1

/-- Principal-series descriptor with spectral parameter `i rho`. -/
def principalSU11SeriesDescriptor (rho : ℝ) (left right : ℤ) : SU11SeriesDescriptor where
  kind := .principal
  spectral := Complex.I * (rho : ℂ)
  leftWeight := left
  rightWeight := right

/-- The principal-series constructor has imaginary spectral parameter. -/
lemma principalSU11SeriesDescriptor_isPrincipal (rho : ℝ) (left right : ℤ) :
    IsSU11PrincipalSeriesDescriptor (principalSU11SeriesDescriptor rho left right) := by
  simp [IsSU11PrincipalSeriesDescriptor, principalSU11SeriesDescriptor]

/-- Discrete-series descriptor with equal left and right `K`-type weights. -/
def discreteSU11SeriesDescriptor (weight : ℤ) (spectral : ℂ) : SU11SeriesDescriptor where
  kind := .discrete
  spectral := spectral
  leftWeight := weight
  rightWeight := weight

/-- The discrete-series constructor has equal left and right weights. -/
lemma discreteSU11SeriesDescriptor_isDiscrete (weight : ℤ) (spectral : ℂ) :
    IsSU11DiscreteSeriesDescriptor (discreteSU11SeriesDescriptor weight spectral) := by
  simp [IsSU11DiscreteSeriesDescriptor, discreteSU11SeriesDescriptor]

/-- Supplementary-series descriptor with real spectral parameter. -/
def supplementarySU11SeriesDescriptor (r : ℝ) (left right : ℤ) : SU11SeriesDescriptor where
  kind := .supplementary
  spectral := (r : ℂ)
  leftWeight := left
  rightWeight := right

/-- The supplementary-series constructor satisfies the standard strip condition
whenever `|r| < 1`. -/
lemma supplementarySU11SeriesDescriptor_isSupplementary
    (r : ℝ) (left right : ℤ) (hr : |r| < 1) :
    IsSU11SupplementarySeriesDescriptor
      (supplementarySU11SeriesDescriptor r left right) := by
  simp [IsSU11SupplementarySeriesDescriptor, supplementarySU11SeriesDescriptor, hr]

/-- A matrix-element mode for a chosen `SU(1,1)` series representation. -/
structure SU11HarmonicMode where
  /-- Series parameter, such as the spectral parameter in principal or discrete series. -/
  parameter : ℂ
  /-- Left weight. -/
  leftWeight : ℤ
  /-- Right weight. -/
  rightWeight : ℤ
  /-- Matrix-element function on concrete `SU(1,1)` matrices. -/
  value : SU11Matrix -> ℂ

/-- Evaluation of an `SU(1,1)` harmonic mode on Euler coordinates. -/
noncomputable def SU11HarmonicMode.evalEuler
    (mode : SU11HarmonicMode) (a : SU11EulerAngles) : ℂ :=
  mode.value a.toMatrix

/-- Finite `SU(1,1)` harmonic expansion over supplied noncompact-series modes. -/
noncomputable def finiteSU11HarmonicExpansion {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (mode : ι -> SU11HarmonicMode) : SU11Matrix -> ℂ :=
  fun g => ∑ i, coeff i * (mode i).value g

/-- The finite `SU(1,1)` harmonic expansion is linear in its coefficients. -/
lemma finiteSU11HarmonicExpansion_add_coeff {ι : Type*} [Fintype ι]
    (coeff₁ coeff₂ : ι -> ℂ) (mode : ι -> SU11HarmonicMode) (g : SU11Matrix) :
    finiteSU11HarmonicExpansion (fun i => coeff₁ i + coeff₂ i) mode g =
      finiteSU11HarmonicExpansion coeff₁ mode g +
        finiteSU11HarmonicExpansion coeff₂ mode g := by
  unfold finiteSU11HarmonicExpansion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- A complex-linear integration functional on the noncompact `SU(1,1)` factor. -/
abbrev SU11HaarFunctional := (SU11Matrix -> ℂ) →ₗ[ℂ] ℂ

/-- Inner product induced by a supplied `SU(1,1)` integration functional. -/
noncomputable def su11HarmonicInnerProduct
    (haar : SU11HaarFunctional) (f g : SU11Matrix -> ℂ) : ℂ :=
  haar (fun x => star (f x) * g x)

/-- Orthogonality relation for a finite list of supplied `SU(1,1)` harmonic modes. -/
def IsSU11HarmonicOrthogonal {ι : Type*} [DecidableEq ι]
    (haar : SU11HaarFunctional) (mode : ι -> SU11HarmonicMode) : Prop :=
  ∀ i j,
    su11HarmonicInnerProduct haar (mode i).value (mode j).value =
      if i = j then (1 : ℂ) else 0

/-- Coefficient extraction for a finite `SU(1,1)` harmonic expansion under the
finite orthogonality relation. -/
lemma su11HarmonicCoefficientExtraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (haar : SU11HaarFunctional) (mode : ι -> SU11HarmonicMode)
    (horth : IsSU11HarmonicOrthogonal haar mode) (coeff : ι -> ℂ) (i : ι) :
    su11HarmonicInnerProduct haar (mode i).value
        (finiteSU11HarmonicExpansion coeff mode) =
      ∑ j, coeff j * (if i = j then (1 : ℂ) else 0) := by
  unfold su11HarmonicInnerProduct finiteSU11HarmonicExpansion
  have hsum :
      (fun g => star ((mode i).value g) *
          (∑ j, coeff j * (mode j).value g)) =
        ∑ j, (coeff j) •
          (fun g => star ((mode i).value g) * (mode j).value g) := by
    funext g
    rw [Finset.mul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    show star ((mode i).value g) * (coeff j * (mode j).value g) =
      coeff j * (star ((mode i).value g) * (mode j).value g)
    ring
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_smul]
  have h := horth i j
  unfold su11HarmonicInnerProduct at h
  simpa [smul_eq_mul] using congrArg (fun x : ℂ => coeff j * x) h

/-! ### C.1.4. Sections 4--4.2: `SL(2,C)` Series and Hyperspherical Data -/

/-- Series parameter for the `SL(2,C)` harmonic-analysis layer. -/
structure SL2CSeriesParameter where
  /-- Integral spin/helicity label. -/
  spin : ℤ
  /-- Complex spectral parameter. -/
  spectral : ℂ

/-- Principal-series condition in the standard form `spectral = i rho`. -/
def IsSL2CPrincipalSeriesParameter (p : SL2CSeriesParameter) : Prop :=
  p.spectral.re = 0

/-- Supplementary-series condition recorded as a real spectral parameter with zero spin
and absolute value below one. -/
def IsSL2CSupplementarySeriesParameter (p : SL2CSeriesParameter) : Prop :=
  p.spin = 0 ∧ p.spectral.im = 0 ∧ |p.spectral.re| < 1

/-- Principal-series parameter with spectral value `i rho`. -/
def principalSL2CSeriesParameter (spin : ℤ) (rho : ℝ) : SL2CSeriesParameter where
  spin := spin
  spectral := Complex.I * (rho : ℂ)

/-- The principal-series constructor has purely imaginary spectral parameter. -/
lemma principalSL2CSeriesParameter_isPrincipal (spin : ℤ) (rho : ℝ) :
    IsSL2CPrincipalSeriesParameter (principalSL2CSeriesParameter spin rho) := by
  simp [IsSL2CPrincipalSeriesParameter, principalSL2CSeriesParameter]

/-- Supplementary-series parameter with real spectral value and zero spin. -/
def supplementarySL2CSeriesParameter (r : ℝ) : SL2CSeriesParameter where
  spin := 0
  spectral := (r : ℂ)

/-- The supplementary-series constructor satisfies the standard strip condition
whenever `|r| < 1`. -/
lemma supplementarySL2CSeriesParameter_isSupplementary (r : ℝ) (hr : |r| < 1) :
    IsSL2CSupplementarySeriesParameter (supplementarySL2CSeriesParameter r) := by
  simp [IsSL2CSupplementarySeriesParameter, supplementarySL2CSeriesParameter, hr]

/-- Six real coordinates for the complex Euler decomposition of `SL(2,C)`. -/
structure SL2CEulerAngles where
  /-- First compact angle. -/
  phi : ℝ
  /-- First noncompact torus parameter. -/
  epsilonLeft : ℝ
  /-- Middle compact angle. -/
  theta : ℝ
  /-- Middle boost parameter. -/
  tau : ℝ
  /-- Second compact angle. -/
  psi : ℝ
  /-- Second noncompact torus parameter. -/
  epsilonRight : ℝ

/-- The `2 x 2` complex Euler matrix from Varlamov Section 4. -/
noncomputable def SL2CEulerAngles.matrix (a : SL2CEulerAngles) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  complexTorusFactor ((a.phi : ℂ) - Complex.I * a.epsilonLeft)
    * complexMiddleRotation ((a.theta : ℂ) - Complex.I * a.tau)
    * complexTorusFactor ((a.psi : ℂ) - Complex.I * a.epsilonRight)

/-- The complex Euler matrix has determinant one, reusing the existing Cartan factors. -/
lemma SL2CEulerAngles.matrix_det (a : SL2CEulerAngles) :
    (a.matrix).det = 1 := by
  unfold SL2CEulerAngles.matrix
  rw [Matrix.det_mul, Matrix.det_mul, complexTorusFactor_det, complexMiddleRotation_det,
    complexTorusFactor_det]
  ring

/-- Matrix element of the existing `SL(2,C) -> LorentzGroup` homomorphism. -/
noncomputable def sl2cLorentzMatrixElement
    (M : SL(2, ℂ)) (mu nu : Sum (Fin 1) (Fin 3)) : ℝ :=
  (Lorentz.SL2C.toLorentzGroup M).1 mu nu

/-- Lorentz matrix elements multiply by summing over the intermediate index. -/
lemma sl2cLorentzMatrixElement_mul
    (M N : SL(2, ℂ)) (mu nu : Sum (Fin 1) (Fin 3)) :
    sl2cLorentzMatrixElement (M * N) mu nu =
      ∑ rho, sl2cLorentzMatrixElement M mu rho *
        sl2cLorentzMatrixElement N rho nu := by
  simp [sl2cLorentzMatrixElement, Matrix.mul_apply]

/-- A finite-dimensional matrix representation of `SL(2,C)`. -/
structure SL2CFiniteRepresentation (n : ℕ) where
  /-- Matrix assigned to an `SL(2,C)` element. -/
  rho : SL(2, ℂ) -> Matrix (Fin n) (Fin n) ℂ
  /-- The identity is represented by the identity matrix. -/
  rho_one : rho 1 = 1
  /-- Multiplication is represented by matrix multiplication. -/
  rho_mul : ∀ M N, rho (M * N) = rho M * rho N

/-- Matrix element of a supplied finite `SL(2,C)` representation. -/
noncomputable def sl2cFiniteMatrixElement {n : ℕ}
    (R : SL2CFiniteRepresentation n) (i j : Fin n) : SL(2, ℂ) -> ℂ :=
  fun M => R.rho M i j

/-- Finite `SL(2,C)` matrix elements multiply by the representation law. -/
lemma sl2cFiniteMatrixElement_mul {n : ℕ}
    (R : SL2CFiniteRepresentation n) (i j : Fin n) (M N : SL(2, ℂ)) :
    sl2cFiniteMatrixElement R i j (M * N) =
      ∑ k, sl2cFiniteMatrixElement R i k M * sl2cFiniteMatrixElement R k j N := by
  simp [sl2cFiniteMatrixElement, R.rho_mul, Matrix.mul_apply]

/-- A complex-linear integration functional on `SL(2,C)`. -/
abbrev SL2CHaarFunctional := (SL(2, ℂ) -> ℂ) →ₗ[ℂ] ℂ

/-- Inner product induced by a supplied `SL(2,C)` integration functional. -/
noncomputable def sl2cMatrixElementInnerProduct
    (haar : SL2CHaarFunctional) (f g : SL(2, ℂ) -> ℂ) : ℂ :=
  haar (fun x => star (f x) * g x)

/-- Orthogonality relation for matrix elements of one finite `SL(2,C)` representation,
with respect to a supplied integration functional. -/
def IsSL2CFiniteMatrixElementOrthogonal {n : ℕ}
    (haar : SL2CHaarFunctional) (R : SL2CFiniteRepresentation n) : Prop :=
  ∀ i j k l,
    sl2cMatrixElementInnerProduct haar (sl2cFiniteMatrixElement R i j)
        (sl2cFiniteMatrixElement R k l) =
      if i = k ∧ j = l then (1 : ℂ) else 0

/-- Finite expansion using matrix elements of one supplied `SL(2,C)` representation. -/
noncomputable def finiteSL2CMatrixElementExpansion {n : ℕ} {ι : Type*} [Fintype ι]
    (R : SL2CFiniteRepresentation n) (coeff : ι -> ℂ)
    (row col : ι -> Fin n) : SL(2, ℂ) -> ℂ :=
  fun M => ∑ a, coeff a * sl2cFiniteMatrixElement R (row a) (col a) M

/-- Coefficient extraction for a finite `SL(2,C)` matrix-element expansion under an
orthogonality relation. -/
lemma sl2cFiniteMatrixElementCoefficientExtraction {n : ℕ} {ι : Type*} [Fintype ι]
    (haar : SL2CHaarFunctional) (R : SL2CFiniteRepresentation n)
    (horth : IsSL2CFiniteMatrixElementOrthogonal haar R)
    (coeff : ι -> ℂ) (row col : ι -> Fin n) (i j : Fin n) :
    sl2cMatrixElementInnerProduct haar (sl2cFiniteMatrixElement R i j)
        (finiteSL2CMatrixElementExpansion R coeff row col) =
      ∑ a, coeff a * (if i = row a ∧ j = col a then (1 : ℂ) else 0) := by
  unfold sl2cMatrixElementInnerProduct finiteSL2CMatrixElementExpansion
  have hsum :
      (fun M => star (sl2cFiniteMatrixElement R i j M) *
          (∑ a, coeff a * sl2cFiniteMatrixElement R (row a) (col a) M)) =
        ∑ a, (coeff a) •
          (fun M => star (sl2cFiniteMatrixElement R i j M) *
            sl2cFiniteMatrixElement R (row a) (col a) M) := by
    funext M
    rw [Finset.mul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    show star (sl2cFiniteMatrixElement R i j M) *
        (coeff a * sl2cFiniteMatrixElement R (row a) (col a) M) =
      coeff a *
        (star (sl2cFiniteMatrixElement R i j M) *
          sl2cFiniteMatrixElement R (row a) (col a) M)
    ring
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [map_smul]
  have h := horth i j (row a) (col a)
  unfold sl2cMatrixElementInnerProduct at h
  simpa [smul_eq_mul] using congrArg (fun x : ℂ => coeff a * x) h

/-- Differential and recurrence data for associated hyperspherical functions on
`SL(2,C)`.  The concrete operators and coefficients are supplied by the analytic
construction; this record fixes the equations consumed by the field expansion. -/
structure SL2CHypersphericalSystem where
  /-- Associated hyperspherical function indexed by representation and weight labels. -/
  Z : SL2CSeriesParameter -> ℤ -> ℤ -> ℂ -> ℂ
  /-- Radial differential operator acting on one complex coordinate. -/
  radialOperator : (ℂ -> ℂ) -> ℂ -> ℂ
  /-- Additivity of the radial operator. -/
  radialOperator_add :
    ∀ f g z, radialOperator (fun w => f w + g w) z =
      radialOperator f z + radialOperator g z
  /-- Homogeneity of the radial operator. -/
  radialOperator_smul :
    ∀ c f z, radialOperator (fun w => c * f w) z = c * radialOperator f z
  /-- Casimir eigenvalue assigned to a series parameter. -/
  casimir : SL2CSeriesParameter -> ℂ
  /-- Left recurrence coefficient. -/
  leftCoeff : SL2CSeriesParameter -> ℤ -> ℤ -> ℂ
  /-- Right recurrence coefficient. -/
  rightCoeff : SL2CSeriesParameter -> ℤ -> ℤ -> ℂ
  /-- Radial differential equation for the associated hyperspherical functions. -/
  radial_equation :
    ∀ p m n z, radialOperator (Z p m n) z = casimir p * Z p m n z
  /-- Left-weight recurrence equation. -/
  left_recurrence :
    ∀ p m n z, Z p (m + 1) n z = leftCoeff p m n * Z p m n z
  /-- Right-weight recurrence equation. -/
  right_recurrence :
    ∀ p m n z, Z p m (n + 1) z = rightCoeff p m n * Z p m n z

/-- The radial equation exposed as a lemma for downstream field-mode proofs. -/
lemma SL2CHypersphericalSystem.radial_eq
    (H : SL2CHypersphericalSystem) (p : SL2CSeriesParameter) (m n : ℤ) (z : ℂ) :
    H.radialOperator (H.Z p m n) z = H.casimir p * H.Z p m n z :=
  H.radial_equation p m n z

/-- The left-weight recurrence exposed as a lemma for downstream mode proofs. -/
lemma SL2CHypersphericalSystem.left_recurrence_eq
    (H : SL2CHypersphericalSystem) (p : SL2CSeriesParameter) (m n : ℤ) (z : ℂ) :
    H.Z p (m + 1) n z = H.leftCoeff p m n * H.Z p m n z :=
  H.left_recurrence p m n z

/-- The right-weight recurrence exposed as a lemma for downstream mode proofs. -/
lemma SL2CHypersphericalSystem.right_recurrence_eq
    (H : SL2CHypersphericalSystem) (p : SL2CSeriesParameter) (m n : ℤ) (z : ℂ) :
    H.Z p m (n + 1) z = H.rightCoeff p m n * H.Z p m n z :=
  H.right_recurrence p m n z

/-- Finite `SL(2,C)` hyperspherical expansion in one complex radial coordinate. -/
noncomputable def finiteSL2CHypersphericalExpansion {ι : Type*} [Fintype ι]
    (H : SL2CHypersphericalSystem) (coeff : ι -> ℂ)
    (param : ι -> SL2CSeriesParameter) (left right : ι -> ℤ) : ℂ -> ℂ :=
  fun z => ∑ i, coeff i * H.Z (param i) (left i) (right i) z

/-- The finite hyperspherical expansion is linear in its coefficient sequence. -/
lemma finiteSL2CHypersphericalExpansion_add_coeff {ι : Type*} [Fintype ι]
    (H : SL2CHypersphericalSystem) (coeff₁ coeff₂ : ι -> ℂ)
    (param : ι -> SL2CSeriesParameter) (left right : ι -> ℤ) (z : ℂ) :
    finiteSL2CHypersphericalExpansion H (fun i => coeff₁ i + coeff₂ i) param left right z =
      finiteSL2CHypersphericalExpansion H coeff₁ param left right z +
        finiteSL2CHypersphericalExpansion H coeff₂ param left right z := by
  unfold finiteSL2CHypersphericalExpansion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The radial operator sends the zero radial profile to zero. -/
lemma SL2CHypersphericalSystem.radialOperator_zero
    (H : SL2CHypersphericalSystem) (z : ℂ) :
    H.radialOperator (fun _ => 0) z = 0 := by
  have h := H.radialOperator_smul (0 : ℂ) (fun _ : ℂ => 0) z
  simpa using h

/-- Applying the radial operator to a finite sum of hyperspherical functions gives
the finite sum of their Casimir eigenvalue equations. -/
lemma SL2CHypersphericalSystem.radialOperator_finset_sum {ι : Type*} [DecidableEq ι]
    (H : SL2CHypersphericalSystem) (s : Finset ι) (coeff : ι -> ℂ)
    (param : ι -> SL2CSeriesParameter) (left right : ι -> ℤ) (z : ℂ) :
    H.radialOperator
        (fun w => ∑ i ∈ s, coeff i * H.Z (param i) (left i) (right i) w) z =
      ∑ i ∈ s, coeff i * H.casimir (param i) *
        H.Z (param i) (left i) (right i) z := by
  induction s using Finset.induction_on with
  | empty =>
      simp [SL2CHypersphericalSystem.radialOperator_zero]
  | insert a s has ih =>
      simp [has, H.radialOperator_add, H.radialOperator_smul, H.radial_equation, ih]
      ring

/-- Applying the radial operator to a finite hyperspherical expansion gives the
finite Casimir-weighted expansion. -/
lemma finiteSL2CHypersphericalExpansion_radialOperator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : SL2CHypersphericalSystem) (coeff : ι -> ℂ)
    (param : ι -> SL2CSeriesParameter) (left right : ι -> ℤ) (z : ℂ) :
    H.radialOperator (finiteSL2CHypersphericalExpansion H coeff param left right) z =
      ∑ i, coeff i * H.casimir (param i) *
        H.Z (param i) (left i) (right i) z := by
  unfold finiteSL2CHypersphericalExpansion
  simpa using
    H.radialOperator_finset_sum (Finset.univ : Finset ι) coeff param left right z

/-- A finite SL(2,C) Plancherel frame consists of modes whose matrix-element
inner products are Kronecker delta functions. -/
def IsFiniteSL2CPlancherelFrame {ι : Type*} [DecidableEq ι]
    (haar : SL2CHaarFunctional) (mode : ι -> SL(2, ℂ) -> ℂ) : Prop :=
  ∀ i j,
    sl2cMatrixElementInnerProduct haar (mode i) (mode j) =
      if i = j then (1 : ℂ) else 0

/-- Finite Fourier transform against an `SL(2,C)` mode family. -/
noncomputable def finiteSL2CFourierTransform {ι : Type*}
    (haar : SL2CHaarFunctional) (mode : ι -> SL(2, ℂ) -> ℂ)
    (f : SL(2, ℂ) -> ℂ) : ι -> ℂ :=
  fun i => sl2cMatrixElementInnerProduct haar (mode i) f

/-- Finite inverse transform associated to a mode family. -/
noncomputable def finiteSL2CFourierSynthesis {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (mode : ι -> SL(2, ℂ) -> ℂ) : SL(2, ℂ) -> ℂ :=
  fun M => ∑ i, coeff i * mode i M

/-- In an orthonormal finite SL(2,C) frame, Fourier transforming a synthesized
finite expansion extracts the expected coefficient sum. -/
lemma finiteSL2CFourierTransform_synthesis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (haar : SL2CHaarFunctional) (mode : ι -> SL(2, ℂ) -> ℂ)
    (hframe : IsFiniteSL2CPlancherelFrame haar mode) (coeff : ι -> ℂ) (i : ι) :
    finiteSL2CFourierTransform haar mode
        (finiteSL2CFourierSynthesis coeff mode) i =
      ∑ j, coeff j * (if i = j then (1 : ℂ) else 0) := by
  unfold finiteSL2CFourierTransform finiteSL2CFourierSynthesis
  unfold sl2cMatrixElementInnerProduct
  have hsum :
      (fun M => star (mode i M) * (∑ j, coeff j * mode j M)) =
        ∑ j, (coeff j) • (fun M => star (mode i M) * mode j M) := by
    funext M
    rw [Finset.mul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    show star (mode i M) * (coeff j * mode j M) =
      coeff j * (star (mode i M) * mode j M)
    ring
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_smul]
  have h := hframe i j
  unfold sl2cMatrixElementInnerProduct at h
  simpa [smul_eq_mul] using congrArg (fun x : ℂ => coeff j * x) h

/-! ### C.1.5. Analytic Hyperspherical Convergence -/

/-- One term of the associated-hyperspherical expansion on the complex radial
coordinate of the complex two-sphere. -/
noncomputable def sl2cHypersphericalTerm
    (H : SL2CHypersphericalSystem) (coeff : ℕ -> ℂ)
    (param : ℕ -> SL2CSeriesParameter) (left right : ℕ -> ℤ) :
    ℕ -> ℂ -> ℂ :=
  fun n z => coeff n * H.Z (param n) (left n) (right n) z

/-- Infinite associated-hyperspherical series on the complex two-sphere radial
coordinate. -/
noncomputable def sl2cHypersphericalSeries
    (H : SL2CHypersphericalSystem) (coeff : ℕ -> ℂ)
    (param : ℕ -> SL2CSeriesParameter) (left right : ℕ -> ℤ) :
    ℂ -> ℂ :=
  fun z => ∑' n, sl2cHypersphericalTerm H coeff param left right n z

/-- Finite truncation of the associated-hyperspherical series. -/
noncomputable def sl2cHypersphericalPartialSum
    (H : SL2CHypersphericalSystem) (coeff : ℕ -> ℂ)
    (param : ℕ -> SL2CSeriesParameter) (left right : ℕ -> ℤ)
    (N : ℕ) : ℂ -> ℂ :=
  fun z => ∑ n ∈ Finset.range N, sl2cHypersphericalTerm H coeff param left right n z

/-- A summable real majorant gives pointwise summability of the complex
hyperspherical expansion. -/
lemma sl2cHypersphericalTerm_summable_of_norm_bound
    (H : SL2CHypersphericalSystem) (coeff : ℕ -> ℂ)
    (param : ℕ -> SL2CSeriesParameter) (left right : ℕ -> ℤ)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant) (z : ℂ)
    (hbound :
      ∀ n, ‖sl2cHypersphericalTerm H coeff param left right n z‖ ≤ majorant n) :
    Summable (fun n => sl2cHypersphericalTerm H coeff param left right n z) :=
  Summable.of_norm_bounded hmajorant hbound

/-- A summable real majorant identifies the infinite hyperspherical series as the
sum of its terms. -/
lemma sl2cHypersphericalSeries_hasSum_of_norm_bound
    (H : SL2CHypersphericalSystem) (coeff : ℕ -> ℂ)
    (param : ℕ -> SL2CSeriesParameter) (left right : ℕ -> ℤ)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant) (z : ℂ)
    (hbound :
      ∀ n, ‖sl2cHypersphericalTerm H coeff param left right n z‖ ≤ majorant n) :
    HasSum (fun n => sl2cHypersphericalTerm H coeff param left right n z)
      (sl2cHypersphericalSeries H coeff param left right z) := by
  exact (sl2cHypersphericalTerm_summable_of_norm_bound H coeff param left right
    majorant hmajorant z hbound).hasSum

/-- Finite hyperspherical truncations converge to the infinite series under the
same summable-majorant hypothesis. -/
lemma sl2cHypersphericalPartialSum_tendsto_of_norm_bound
    (H : SL2CHypersphericalSystem) (coeff : ℕ -> ℂ)
    (param : ℕ -> SL2CSeriesParameter) (left right : ℕ -> ℤ)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant) (z : ℂ)
    (hbound :
      ∀ n, ‖sl2cHypersphericalTerm H coeff param left right n z‖ ≤ majorant n) :
    Filter.Tendsto
      (fun N => sl2cHypersphericalPartialSum H coeff param left right N z)
      Filter.atTop
      (nhds (sl2cHypersphericalSeries H coeff param left right z)) := by
  have hsum := sl2cHypersphericalSeries_hasSum_of_norm_bound H coeff param left right
    majorant hmajorant z hbound
  simpa [sl2cHypersphericalPartialSum] using hsum.tendsto_sum_nat

/-- The spinor monomial
`z_{alpha_1} ... z_{alpha_k} zdot_{alpha_dot_1} ... zdot_{alpha_dot_r}`
appearing in Varlamov Eq. 93. -/
noncomputable def finiteSpinorMonomial {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (undotted : κ -> Fin 2) (dotted : ρ -> Fin 2)
    (z zdot : SpinorCoordinate) : ℂ :=
  (∏ a, z (undotted a)) * (∏ b, zdot (dotted b))

/-- Finite symmetric-polynomial field on the `SU(2) x SU(2)` spinor variables, with
coefficients depending on the translation coordinate as in Varlamov Eq. 93. -/
noncomputable def finiteSpinorPolynomial {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    [Fintype ρ] (coeff : ι -> MinkowskiPoint -> ℂ)
    (undotted : ι -> κ -> Fin 2) (dotted : ι -> ρ -> Fin 2)
    (x : MinkowskiPoint) (z zdot : SpinorCoordinate) : ℂ :=
  ∑ i, coeff i x * finiteSpinorMonomial (undotted i) (dotted i) z zdot

/-- The finite spinor-polynomial expansion is linear in its coefficient functions. -/
lemma finiteSpinorPolynomial_add_coeff {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    [Fintype ρ] (coeff₁ coeff₂ : ι -> MinkowskiPoint -> ℂ)
    (undotted : ι -> κ -> Fin 2) (dotted : ι -> ρ -> Fin 2)
    (x : MinkowskiPoint) (z zdot : SpinorCoordinate) :
    finiteSpinorPolynomial (fun i y => coeff₁ i y + coeff₂ i y) undotted dotted x z zdot =
      finiteSpinorPolynomial coeff₁ undotted dotted x z zdot
        + finiteSpinorPolynomial coeff₂ undotted dotted x z zdot := by
  unfold finiteSpinorPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The finite Poincare matrix element `e^{i p x} M(g)` from Varlamov Eq. 94,
with `M(g)` represented by a supplied finite `SU(2) x SU(2)` mode. -/
noncomputable def finitePoincareMatrixElement
    (p : MinkowskiPoint) (lorentzMode : SU2Pair -> ℂ) :
    MinkowskiPoint -> SU2Pair -> ℂ :=
  fun x g => minkowskiPlaneWave p x * lorentzMode g

/-- Translation of a finite Poincare matrix element factors through the `T4`
character. -/
lemma finitePoincareMatrixElement_translate
    (p a x : MinkowskiPoint) (lorentzMode : SU2Pair -> ℂ) (g : SU2Pair) :
    finitePoincareMatrixElement p lorentzMode (minkowskiTranslate a x) g =
      finitePoincareMatrixElement p lorentzMode x g * minkowskiPlaneWave p a := by
  simp [finitePoincareMatrixElement, minkowskiPlaneWave_translate]
  ring

/-- Finite harmonic expansion on `SU(2) x SU(2) ⋉ T4` by matrix elements
`e^{i p_i x} M_i(g)`. -/
noncomputable def finitePoincareHarmonicExpansion {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (lorentzMode : ι -> SU2Pair -> ℂ) :
    MinkowskiPoint -> SU2Pair -> ℂ :=
  fun x g => ∑ i, coeff i * finitePoincareMatrixElement (momentum i) (lorentzMode i) x g

/-- The finite Poincare harmonic expansion is linear in the coefficient sequence. -/
lemma finitePoincareHarmonicExpansion_add_coeff {ι : Type*} [Fintype ι]
    (coeff₁ coeff₂ : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (lorentzMode : ι -> SU2Pair -> ℂ) (x : MinkowskiPoint) (g : SU2Pair) :
    finitePoincareHarmonicExpansion (fun i => coeff₁ i + coeff₂ i) momentum lorentzMode x g =
      finitePoincareHarmonicExpansion coeff₁ momentum lorentzMode x g
        + finitePoincareHarmonicExpansion coeff₂ momentum lorentzMode x g := by
  unfold finitePoincareHarmonicExpansion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Translating the spacetime coordinate in a finite Poincare harmonic expansion
multiplies each summand by the corresponding `T4` character. -/
lemma finitePoincareHarmonicExpansion_translate {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (lorentzMode : ι -> SU2Pair -> ℂ) (a x : MinkowskiPoint) (g : SU2Pair) :
    finitePoincareHarmonicExpansion coeff momentum lorentzMode (minkowskiTranslate a x) g =
      ∑ i, coeff i * finitePoincareMatrixElement (momentum i) (lorentzMode i) x g
        * minkowskiPlaneWave (momentum i) a := by
  unfold finitePoincareHarmonicExpansion
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finitePoincareMatrixElement_translate]
  ring

/-- Full formal harmonic series on `SU(2) x SU(2) ⋉ T4`, written as the topological
sum of Varlamov Eq. 94 matrix elements.  Finite truncations are provided by
`finitePoincareHarmonicExpansion`. -/
noncomputable def poincareHarmonicSeries {ι : Type*}
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (lorentzMode : ι -> SU2Pair -> ℂ) :
    MinkowskiPoint -> SU2Pair -> ℂ :=
  fun x g => ∑' i, coeff i * finitePoincareMatrixElement (momentum i) (lorentzMode i) x g

/-- Translating the spacetime coordinate in the full Poincare harmonic series acts
termwise by the corresponding `T4` character. -/
lemma poincareHarmonicSeries_translate {ι : Type*}
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (lorentzMode : ι -> SU2Pair -> ℂ) (a x : MinkowskiPoint) (g : SU2Pair) :
    poincareHarmonicSeries coeff momentum lorentzMode (minkowskiTranslate a x) g =
      ∑' i, coeff i * finitePoincareMatrixElement (momentum i) (lorentzMode i) x g
        * minkowskiPlaneWave (momentum i) a := by
  unfold poincareHarmonicSeries
  apply tsum_congr
  intro i
  rw [finitePoincareMatrixElement_translate]
  ring

/-- A finite `M8` Fourier mode from Varlamov Eq. 95:
`e^{i p x}` times a complex-two-sphere mode. -/
noncomputable def finiteM8FourierMode
    (p : MinkowskiPoint) (sphereMode : ComplexTwoSpherePoint -> ℂ) : PoincareM8 -> ℂ :=
  fun q => minkowskiPlaneWave p q.1 * sphereMode q.2

/-- The finite `M8` Fourier mode is the existing separated Poincare field with the
factors reordered. -/
lemma finiteM8FourierMode_eq_factorizedPoincareField4
    (p : MinkowskiPoint) (sphereMode : ComplexTwoSpherePoint -> ℂ) :
    finiteM8FourierMode p sphereMode = factorizedPoincareField4 sphereMode p := by
  funext q
  simp [finiteM8FourierMode, factorizedPoincareField4]
  ring

/-- Translation of an `M8` Fourier mode factors through the corresponding `T4`
plane-wave character. -/
lemma finiteM8FourierMode_translate
    (p a : MinkowskiPoint) (sphereMode : ComplexTwoSpherePoint -> ℂ) (q : PoincareM8) :
    finiteM8FourierMode p sphereMode (minkowskiTranslate a q.1, q.2) =
      finiteM8FourierMode p sphereMode q * minkowskiPlaneWave p a := by
  simp [finiteM8FourierMode, minkowskiPlaneWave_translate]
  ring

/-- Finite Fourier series on `M8 = R^{1,3} x S^2_C`, the finite truncation of
Varlamov Eq. 95. -/
noncomputable def finiteM8FourierExpansion {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (sphereMode : ι -> ComplexTwoSpherePoint -> ℂ) : PoincareM8 -> ℂ :=
  fun q => ∑ i, coeff i * finiteM8FourierMode (momentum i) (sphereMode i) q

/-- The finite `M8` Fourier series reuses the existing separated-field modes. -/
lemma finiteM8FourierExpansion_eq_sum_factorizedPoincareField4 {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (sphereMode : ι -> ComplexTwoSpherePoint -> ℂ) :
    finiteM8FourierExpansion coeff momentum sphereMode =
      fun q => ∑ i, coeff i * factorizedPoincareField4 (sphereMode i) (momentum i) q := by
  funext q
  unfold finiteM8FourierExpansion
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finiteM8FourierMode_eq_factorizedPoincareField4]

/-- The finite `M8` Fourier series is linear in the coefficient sequence. -/
lemma finiteM8FourierExpansion_add_coeff {ι : Type*} [Fintype ι]
    (coeff₁ coeff₂ : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (sphereMode : ι -> ComplexTwoSpherePoint -> ℂ) (q : PoincareM8) :
    finiteM8FourierExpansion (fun i => coeff₁ i + coeff₂ i) momentum sphereMode q =
      finiteM8FourierExpansion coeff₁ momentum sphereMode q
        + finiteM8FourierExpansion coeff₂ momentum sphereMode q := by
  unfold finiteM8FourierExpansion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Translating the `R^{1,3}` factor in a finite `M8` Fourier expansion multiplies each
summand by its plane-wave character. -/
lemma finiteM8FourierExpansion_translate {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (sphereMode : ι -> ComplexTwoSpherePoint -> ℂ) (a : MinkowskiPoint) (q : PoincareM8) :
    finiteM8FourierExpansion coeff momentum sphereMode (minkowskiTranslate a q.1, q.2) =
      ∑ i, coeff i * finiteM8FourierMode (momentum i) (sphereMode i) q
        * minkowskiPlaneWave (momentum i) a := by
  unfold finiteM8FourierExpansion
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finiteM8FourierMode_translate]
  ring

/-- Full formal Fourier series on `M8 = R^{1,3} x S^2_C`, written as the
topological sum of Varlamov Eq. 95 modes. -/
noncomputable def m8FourierSeries {ι : Type*}
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (sphereMode : ι -> ComplexTwoSpherePoint -> ℂ) : PoincareM8 -> ℂ :=
  fun q => ∑' i, coeff i * finiteM8FourierMode (momentum i) (sphereMode i) q

/-- Translating the spacetime factor in the full `M8` Fourier series acts termwise by
the corresponding plane-wave character. -/
lemma m8FourierSeries_translate {ι : Type*}
    (coeff : ι -> ℂ) (momentum : ι -> MinkowskiPoint)
    (sphereMode : ι -> ComplexTwoSpherePoint -> ℂ) (a : MinkowskiPoint) (q : PoincareM8) :
    m8FourierSeries coeff momentum sphereMode (minkowskiTranslate a q.1, q.2) =
      ∑' i, coeff i * finiteM8FourierMode (momentum i) (sphereMode i) q
        * minkowskiPlaneWave (momentum i) a := by
  unfold m8FourierSeries
  apply tsum_congr
  intro i
  rw [finiteM8FourierMode_translate]
  ring

/-! ## D. Riemann-Silberstein Maxwell Field -/

/-- The Riemann-Silberstein electromagnetic vector `F = E + i B`. -/
noncomputable def riemannSilberstein (E B : Fin 3 -> ℝ) : Fin 3 -> ℂ :=
  fun i => (E i : ℂ) + Complex.I * (B i : ℂ)

/-- The real part of the Riemann-Silberstein vector is the electric field. -/
@[simp] lemma riemannSilberstein_re (E B : Fin 3 -> ℝ) (i : Fin 3) :
    (riemannSilberstein E B i).re = E i := by
  simp [riemannSilberstein]

/-- The imaginary part of the Riemann-Silberstein vector is the magnetic field. -/
@[simp] lemma riemannSilberstein_im (E B : Fin 3 -> ℝ) (i : Fin 3) :
    (riemannSilberstein E B i).im = B i := by
  simp [riemannSilberstein]

/-- Equality of Riemann-Silberstein vectors is equality of electric and magnetic components. -/
lemma riemannSilberstein_ext {E B E' B' : Fin 3 -> ℝ}
    (h : riemannSilberstein E B = riemannSilberstein E' B') : E = E' ∧ B = B' := by
  constructor
  · funext i
    have hi := congrFun h i
    simpa [riemannSilberstein] using (Complex.ext_iff.mp hi).1
  · funext i
    have hi := congrFun h i
    simpa [riemannSilberstein] using (Complex.ext_iff.mp hi).2

/-- The electromagnetic energy-density quadratic form `sum_i (E_i^2 + B_i^2)`. -/
def electromagneticEnergyDensity (E B : Fin 3 -> ℝ) : ℝ :=
  ∑ i, ((E i) ^ 2 + (B i) ^ 2)

/-- The squared modulus of one Riemann-Silberstein component is `E_i^2 + B_i^2`. -/
lemma riemannSilberstein_normSq (E B : Fin 3 -> ℝ) (i : Fin 3) :
    Complex.normSq (riemannSilberstein E B i) = E i ^ 2 + B i ^ 2 := by
  rw [riemannSilberstein, mul_comm Complex.I ((B i : ℝ) : ℂ)]
  exact Complex.normSq_add_mul_I (E i) (B i)

/-- The sum of Riemann-Silberstein squared moduli is the electromagnetic energy density. -/
lemma riemannSilberstein_sum_normSq (E B : Fin 3 -> ℝ) :
    (∑ i, Complex.normSq (riemannSilberstein E B i)) = electromagneticEnergyDensity E B := by
  simp [electromagneticEnergyDensity, riemannSilberstein_normSq]

/-- The electromagnetic energy density is non-negative. -/
lemma electromagneticEnergyDensity_nonneg (E B : Fin 3 -> ℝ) :
    0 ≤ electromagneticEnergyDensity E B := by
  unfold electromagneticEnergyDensity
  apply Finset.sum_nonneg
  intro i _hi
  exact add_nonneg (sq_nonneg (E i)) (sq_nonneg (B i))

/-- The local integrand in Varlamov's photon-charge discussion, `2(E^2+B^2)`. -/
def photonChargeDensityIntegrand (E B : Fin 3 -> ℝ) : ℝ :=
  2 * electromagneticEnergyDensity E B

/-- The photon-charge integrand is twice the Riemann-Silberstein norm-square sum. -/
lemma photonChargeDensityIntegrand_eq_two_riemannSilberstein_normSq (E B : Fin 3 -> ℝ) :
    photonChargeDensityIntegrand E B =
      2 * (∑ i, Complex.normSq (riemannSilberstein E B i)) := by
  rw [photonChargeDensityIntegrand, riemannSilberstein_sum_normSq]

/-- The photon-charge integrand is non-negative as an energy-density multiple. -/
lemma photonChargeDensityIntegrand_nonneg (E B : Fin 3 -> ℝ) :
    0 ≤ photonChargeDensityIntegrand E B := by
  exact mul_nonneg (by norm_num) (electromagneticEnergyDensity_nonneg E B)

/-! ## D.1. Section 9 Maxwell Matrices and Helicity Modes -/

/-- Electric-field component index inside the six-component Maxwell bispinor. -/
def maxwellElectricIndex (i : Fin 3) : Fin 6 :=
  ⟨i.val, by omega⟩

/-- Magnetic-field component index inside the six-component Maxwell bispinor. -/
def maxwellMagneticIndex (i : Fin 3) : Fin 6 :=
  ⟨i.val + 3, by omega⟩

/-- The electric three-vector extracted from a six-component Maxwell bispinor. -/
def maxwellElectricPart (phi : Fin 6 -> ℂ) : Fin 3 -> ℂ :=
  fun i => phi (maxwellElectricIndex i)

/-- The magnetic three-vector extracted from a six-component Maxwell bispinor. -/
def maxwellMagneticPart (phi : Fin 6 -> ℂ) : Fin 3 -> ℂ :=
  fun i => phi (maxwellMagneticIndex i)

/-- Six-component Maxwell bispinor assembled from two three-component fields. -/
def maxwellBispinorFromParts (electric magnetic : Fin 3 -> ℂ) : Fin 6 -> ℂ
  | ⟨0, _⟩ => electric 0
  | ⟨1, _⟩ => electric 1
  | ⟨2, _⟩ => electric 2
  | ⟨3, _⟩ => magnetic 0
  | ⟨4, _⟩ => magnetic 1
  | ⟨5, _⟩ => magnetic 2

/-- The electric projection of an assembled Maxwell bispinor is the first input. -/
@[simp] lemma maxwellElectricPart_bispinorFromParts
    (electric magnetic : Fin 3 -> ℂ) :
    maxwellElectricPart (maxwellBispinorFromParts electric magnetic) = electric := by
  funext i
  fin_cases i <;> rfl

/-- The magnetic projection of an assembled Maxwell bispinor is the second input. -/
@[simp] lemma maxwellMagneticPart_bispinorFromParts
    (electric magnetic : Fin 3 -> ℂ) :
    maxwellMagneticPart (maxwellBispinorFromParts electric magnetic) = magnetic := by
  funext i
  fin_cases i <;> rfl

/-- The six-component Majorana-Oppenheimer field `(E - iB, E + iB)` used in
Varlamov Section 9. -/
noncomputable def maxwellRiemannSilbersteinBispinor (E B : Fin 3 -> ℝ) : Fin 6 -> ℂ :=
  maxwellBispinorFromParts
    (fun i => (E i : ℂ) - Complex.I * (B i : ℂ))
    (riemannSilberstein E B)

/-- The lower three components of the Majorana-Oppenheimer field are `E - iB`. -/
@[simp] lemma maxwellRiemannSilbersteinBispinor_electricPart
    (E B : Fin 3 -> ℝ) :
    maxwellElectricPart (maxwellRiemannSilbersteinBispinor E B) =
      fun i => (E i : ℂ) - Complex.I * (B i : ℂ) := by
  simp [maxwellRiemannSilbersteinBispinor]

/-- The upper three components of the Majorana-Oppenheimer field are `E + iB`. -/
@[simp] lemma maxwellRiemannSilbersteinBispinor_magneticPart
    (E B : Fin 3 -> ℝ) :
    maxwellMagneticPart (maxwellRiemannSilbersteinBispinor E B) =
      riemannSilberstein E B := by
  simp [maxwellRiemannSilbersteinBispinor]

/-- The first spin-one generator in the Majorana-Oppenheimer Maxwell representation. -/
def maxwellSpinMatrix1 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]

/-- The second spin-one generator in the Majorana-Oppenheimer Maxwell representation. -/
def maxwellSpinMatrix2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, Complex.I; 0, 0, 0; -Complex.I, 0, 0]

/-- The third spin-one generator in the Majorana-Oppenheimer Maxwell representation. -/
def maxwellSpinMatrix3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]

/-- The spin-one matrices `S_i` used in Varlamov Section 9. -/
def maxwellSpinMatrix : Fin 3 -> Matrix (Fin 3) (Fin 3) ℂ :=
  ![maxwellSpinMatrix1, maxwellSpinMatrix2, maxwellSpinMatrix3]

/-- The first explicit `6 x 6` Maxwell matrix, with spin-one off-diagonal blocks. -/
def varlamovMaxwellAlpha1 : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -Complex.I;
     0, 0, 0, 0, Complex.I, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, -Complex.I, 0, 0, 0;
     0, Complex.I, 0, 0, 0, 0]

/-- The second explicit `6 x 6` Maxwell matrix, with spin-one off-diagonal blocks. -/
def varlamovMaxwellAlpha2 : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, Complex.I;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, -Complex.I, 0, 0;
     0, 0, Complex.I, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     -Complex.I, 0, 0, 0, 0, 0]

/-- The third explicit `6 x 6` Maxwell matrix, with spin-one off-diagonal blocks. -/
def varlamovMaxwellAlpha3 : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, -Complex.I, 0;
     0, 0, 0, Complex.I, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, -Complex.I, 0, 0, 0, 0;
     Complex.I, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- The three spatial Maxwell matrices from Varlamov Section 9. -/
def varlamovMaxwellAlpha : Fin 3 -> Matrix (Fin 6) (Fin 6) ℂ :=
  ![varlamovMaxwellAlpha1, varlamovMaxwellAlpha2, varlamovMaxwellAlpha3]

/-- The spacetime derivative direction corresponding to a spatial index. -/
def spacetimeSpatialDirection (i : Fin 3) : SpaceTimeTangentIndex :=
  ⟨i.val + 1, by omega⟩

/-- Varlamov's Maxwell gamma system: identity in the time direction and the three
explicit `6 x 6` Maxwell matrices in the spatial directions. -/
def varlamovMaxwellGamma : SpaceTimeTangentIndex -> Matrix (Fin 6) (Fin 6) ℂ :=
  ![1, varlamovMaxwellAlpha1, varlamovMaxwellAlpha2, varlamovMaxwellAlpha3]

/-- The time-direction Maxwell matrix is the identity. -/
@[simp] lemma varlamovMaxwellGamma_time :
    varlamovMaxwellGamma 0 = 1 := rfl

/-- The spatial Maxwell matrices are the `alpha_i` blocks. -/
@[simp] lemma varlamovMaxwellGamma_spatial (i : Fin 3) :
    varlamovMaxwellGamma (spacetimeSpatialDirection i) = varlamovMaxwellAlpha i := by
  fin_cases i <;> simp [varlamovMaxwellGamma, varlamovMaxwellAlpha, spacetimeSpatialDirection]

/-- Spin-one curl expression formed from derivative data of a vector field. -/
noncomputable def maxwellSpinCurl (dF : Fin 3 -> Fin 3 -> ℂ) : Fin 3 -> ℂ :=
  fun k => ∑ i, (maxwellSpinMatrix i *ᵥ dF i) k

/-- The paper's Maxwell first-order residual, the massless member of the Varlamov
first-order family. -/
noncomputable def varlamovMaxwellResidual
    (_phi : Fin 6 -> ℂ) (dphi : SpaceTimeTangentIndex -> Fin 6 -> ℂ) : Fin 6 -> ℂ :=
  ∑ mu, varlamovMaxwellGamma mu *ᵥ dphi mu

/-- Component form of the two three-vector Maxwell equations obtained from the
six-component first-order system. -/
def VarlamovMaxwellComponentEquations
    (dphi : SpaceTimeTangentIndex -> Fin 6 -> ℂ) : Prop :=
  (∀ k, dphi 0 (maxwellElectricIndex k)
      + maxwellSpinCurl (fun i => maxwellMagneticPart (dphi (spacetimeSpatialDirection i))) k = 0)
    ∧
  (∀ k, dphi 0 (maxwellMagneticIndex k)
      + maxwellSpinCurl (fun i => maxwellElectricPart (dphi (spacetimeSpatialDirection i))) k = 0)

/-- The electric projection of the first-order `6 x 6` Maxwell residual. -/
lemma varlamovMaxwellResidual_electric
    (phi : Fin 6 -> ℂ) (dphi : SpaceTimeTangentIndex -> Fin 6 -> ℂ) (k : Fin 3) :
    varlamovMaxwellResidual phi dphi (maxwellElectricIndex k) =
      dphi 0 (maxwellElectricIndex k)
        + maxwellSpinCurl
          (fun i => maxwellMagneticPart (dphi (spacetimeSpatialDirection i))) k := by
  fin_cases k <;>
    simp [varlamovMaxwellResidual, varlamovMaxwellGamma, varlamovMaxwellAlpha1, varlamovMaxwellAlpha2,
      varlamovMaxwellAlpha3, maxwellSpinCurl, maxwellSpinMatrix, maxwellSpinMatrix1,
      maxwellSpinMatrix2, maxwellSpinMatrix3, maxwellElectricIndex, maxwellMagneticIndex,
      maxwellMagneticPart, spacetimeSpatialDirection, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_four, Fin.sum_univ_six] <;> ring

/-- The magnetic projection of the first-order `6 x 6` Maxwell residual. -/
lemma varlamovMaxwellResidual_magnetic
    (phi : Fin 6 -> ℂ) (dphi : SpaceTimeTangentIndex -> Fin 6 -> ℂ) (k : Fin 3) :
    varlamovMaxwellResidual phi dphi (maxwellMagneticIndex k) =
      dphi 0 (maxwellMagneticIndex k)
        + maxwellSpinCurl
          (fun i => maxwellElectricPart (dphi (spacetimeSpatialDirection i))) k := by
  fin_cases k <;>
    simp [varlamovMaxwellResidual, varlamovMaxwellGamma, varlamovMaxwellAlpha1, varlamovMaxwellAlpha2,
      varlamovMaxwellAlpha3, maxwellSpinCurl, maxwellSpinMatrix, maxwellSpinMatrix1,
      maxwellSpinMatrix2, maxwellSpinMatrix3, maxwellElectricIndex, maxwellMagneticIndex,
      maxwellElectricPart, spacetimeSpatialDirection, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_four, Fin.sum_univ_six] <;> ring

/-- Vanishing of the paper's `6 x 6` residual is equivalent to the two three-component
Maxwell equations in spin-one matrix form. -/
lemma varlamovMaxwellResidual_zero_iff_component_equations
    (phi : Fin 6 -> ℂ) (dphi : SpaceTimeTangentIndex -> Fin 6 -> ℂ) :
    varlamovMaxwellResidual phi dphi = 0 ↔
      VarlamovMaxwellComponentEquations dphi := by
  constructor
  · intro h
    constructor
    · intro k
      rw [← varlamovMaxwellResidual_electric phi dphi k]
      exact congrFun h (maxwellElectricIndex k)
    · intro k
      rw [← varlamovMaxwellResidual_magnetic phi dphi k]
      exact congrFun h (maxwellMagneticIndex k)
  · intro h
    funext a
    fin_cases a
    · change varlamovMaxwellResidual phi dphi (maxwellElectricIndex 0) = 0
      rw [varlamovMaxwellResidual_electric phi dphi 0]
      exact h.1 0
    · change varlamovMaxwellResidual phi dphi (maxwellElectricIndex 1) = 0
      rw [varlamovMaxwellResidual_electric phi dphi 1]
      exact h.1 1
    · change varlamovMaxwellResidual phi dphi (maxwellElectricIndex 2) = 0
      rw [varlamovMaxwellResidual_electric phi dphi 2]
      exact h.1 2
    · change varlamovMaxwellResidual phi dphi (maxwellMagneticIndex 0) = 0
      rw [varlamovMaxwellResidual_magnetic phi dphi 0]
      exact h.2 0
    · change varlamovMaxwellResidual phi dphi (maxwellMagneticIndex 1) = 0
      rw [varlamovMaxwellResidual_magnetic phi dphi 1]
      exact h.2 1
    · change varlamovMaxwellResidual phi dphi (maxwellMagneticIndex 2) = 0
      rw [varlamovMaxwellResidual_magnetic phi dphi 2]
      exact h.2 2

/-- Transversality condition for a photon plane wave, `p · epsilon = 0`. -/
def IsPhotonTransverseMode (momentum polarization : Fin 3 -> ℂ) : Prop :=
  ∑ i, momentum i * polarization i = 0

/-- Momentum-space helicity eigenvalue equation for a photon polarization vector. -/
def IsPhotonHelicityEigenmode
    (momentum : Fin 3 -> ℂ) (helicity : ℂ) (polarization : Fin 3 -> ℂ) : Prop :=
  (∑ i, momentum i • (maxwellSpinMatrix i *ᵥ polarization)) = helicity • polarization

/-- Physical photon mode: helicity eigenmode with the transversality condition. -/
def IsPhysicalPhotonHelicityMode
    (momentum : Fin 3 -> ℂ) (helicity : ℂ) (polarization : Fin 3 -> ℂ) : Prop :=
  IsPhotonHelicityEigenmode momentum helicity polarization
    ∧ IsPhotonTransverseMode momentum polarization

/-- Varlamov's plane-wave Maxwell eigenvalue problem from Eq. 166. -/
def VarlamovPhotonPlaneWaveEigenproblem
    (momentum : Fin 3 -> ℂ) (omegaOverC : ℂ) (polarization : Fin 3 -> ℂ) : Prop :=
  IsPhotonHelicityEigenmode momentum omegaOverC polarization

/-- The plane-wave Maxwell eigenvalue problem is the helicity eigenvalue equation. -/
lemma varlamovPhotonPlaneWaveEigenproblem_iff_helicity
    (momentum : Fin 3 -> ℂ) (omegaOverC : ℂ) (polarization : Fin 3 -> ℂ) :
    VarlamovPhotonPlaneWaveEigenproblem momentum omegaOverC polarization ↔
      IsPhotonHelicityEigenmode momentum omegaOverC polarization := by
  rfl

/-- A physical photon mode supplies both the helicity equation and transversality. -/
lemma physicalPhotonHelicityMode_iff
    (momentum : Fin 3 -> ℂ) (helicity : ℂ) (polarization : Fin 3 -> ℂ) :
    IsPhysicalPhotonHelicityMode momentum helicity polarization ↔
      IsPhotonHelicityEigenmode momentum helicity polarization
        ∧ IsPhotonTransverseMode momentum polarization := by
  rfl

/-- Component form of the helicity eigenvalue equation. -/
lemma isPhotonHelicityEigenmode_component
    (momentum : Fin 3 -> ℂ) (helicity : ℂ) (polarization : Fin 3 -> ℂ) :
    IsPhotonHelicityEigenmode momentum helicity polarization ↔
      ∀ k, (∑ i, momentum i * (maxwellSpinMatrix i *ᵥ polarization) k)
        = helicity * polarization k := by
  rw [IsPhotonHelicityEigenmode]
  constructor
  · intro h k
    simpa [Pi.smul_apply] using congrFun h k
  · intro h
    funext k
    simpa [Pi.smul_apply] using h k

/-- Countable helicity-mode expansion for the photon Riemann-Silberstein field on `M8`. -/
noncomputable def photonHelicityModeSeriesM8 {ι : Type*}
    (coeff : ι -> ℂ) (polarization : ι -> Fin 3 -> ℂ)
    (momentum : ι -> MinkowskiPoint)
    (internalMode : ι -> ComplexTwoSpherePoint -> ℂ) :
    PoincareM8 -> Fin 3 -> ℂ :=
  fun q a => ∑' i, coeff i * polarization i a *
    finiteM8FourierMode (momentum i) (internalMode i) q

/-- The photon helicity series is componentwise the Fourier-mode series from Section 9. -/
lemma photonHelicityModeSeriesM8_apply {ι : Type*}
    (coeff : ι -> ℂ) (polarization : ι -> Fin 3 -> ℂ)
    (momentum : ι -> MinkowskiPoint)
    (internalMode : ι -> ComplexTwoSpherePoint -> ℂ)
    (q : PoincareM8) (a : Fin 3) :
    photonHelicityModeSeriesM8 coeff polarization momentum internalMode q a =
      ∑' i, coeff i * polarization i a *
        finiteM8FourierMode (momentum i) (internalMode i) q := rfl

/-- Finite form of the helicity expansion when the mode label is finite. -/
lemma photonHelicityModeSeriesM8_fintype {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (polarization : ι -> Fin 3 -> ℂ)
    (momentum : ι -> MinkowskiPoint)
    (internalMode : ι -> ComplexTwoSpherePoint -> ℂ)
    (q : PoincareM8) (a : Fin 3) :
    photonHelicityModeSeriesM8 coeff polarization momentum internalMode q a =
      ∑ i, coeff i * polarization i a *
        finiteM8FourierMode (momentum i) (internalMode i) q := by
  simp [photonHelicityModeSeriesM8]

/-! ## E. Boundary-Mode Expansions on the Complex Two-Sphere -/

/-- The quadratic equation `z_1^2 + z_2^2 + z_3^2` defining the complex two-sphere. -/
def complexTwoSphereQuadratic (z : ComplexTwoSpherePoint) : ℂ :=
  ∑ i, z i ^ 2

/-- The complex two-sphere of radius `r`, stated as `z_1^2 + z_2^2 + z_3^2 = r^2`. -/
def OnComplexTwoSphere (r : ℂ) (z : ComplexTwoSpherePoint) : Prop :=
  complexTwoSphereQuadratic z = r ^ 2

/-- The origin is on the radius-zero complex two-sphere. -/
lemma onComplexTwoSphere_zero : OnComplexTwoSphere 0 (fun _ => 0) := by
  simp [OnComplexTwoSphere, complexTwoSphereQuadratic]

/-! ## E.1. Linear Homogeneous-Space Actions -/

/-- The `SL(2,C)` Lorentz image acting on the Minkowski coordinate factor. -/
noncomputable def sl2cMinkowskiAction (M : SL(2, ℂ)) (x : MinkowskiPoint) : MinkowskiPoint :=
  (Lorentz.SL2C.toLorentzGroup M).1 *ᵥ x

/-- The identity element of `SL(2,C)` acts trivially on Minkowski coordinates. -/
lemma sl2cMinkowskiAction_one (x : MinkowskiPoint) :
    sl2cMinkowskiAction 1 x = x := by
  simp [sl2cMinkowskiAction]

/-- The `SL(2,C)` Minkowski action composes through the existing Lorentz double cover. -/
lemma sl2cMinkowskiAction_mul (M N : SL(2, ℂ)) (x : MinkowskiPoint) :
    sl2cMinkowskiAction (M * N) x =
      sl2cMinkowskiAction M (sl2cMinkowskiAction N x) := by
  simp [sl2cMinkowskiAction,
    Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks.sl2c_toLorentzGroup_hom,
    Matrix.mulVec_mulVec]

/-- A linear action on the ambient `C^3` coordinates of the complex two-sphere. -/
def complexTwoSphereLinearAction
    (A : Matrix (Fin 3) (Fin 3) ℂ) (z : ComplexTwoSpherePoint) : ComplexTwoSpherePoint :=
  A *ᵥ z

/-- The identity matrix acts trivially on the ambient complex-sphere coordinates. -/
lemma complexTwoSphereLinearAction_one (z : ComplexTwoSpherePoint) :
    complexTwoSphereLinearAction 1 z = z := by
  simp [complexTwoSphereLinearAction]

/-- Linear ambient actions compose by matrix multiplication. -/
lemma complexTwoSphereLinearAction_mul
    (A B : Matrix (Fin 3) (Fin 3) ℂ) (z : ComplexTwoSpherePoint) :
    complexTwoSphereLinearAction (A * B) z =
      complexTwoSphereLinearAction A (complexTwoSphereLinearAction B z) := by
  simp [complexTwoSphereLinearAction, Matrix.mulVec_mulVec]

/-- A linear ambient map preserves the complex-sphere quadratic form. -/
def PreservesComplexTwoSphereQuadratic (A : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ z, complexTwoSphereQuadratic (complexTwoSphereLinearAction A z) =
    complexTwoSphereQuadratic z

/-- A quadratic-form-preserving ambient action maps the complex two-sphere to itself. -/
lemma complexTwoSphereLinearAction_preserves_sphere
    {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : PreservesComplexTwoSphereQuadratic A)
    {r : ℂ} {z : ComplexTwoSpherePoint} (hz : OnComplexTwoSphere r z) :
    OnComplexTwoSphere r (complexTwoSphereLinearAction A z) := by
  rw [OnComplexTwoSphere, hA z]
  exact hz

/-- The product action on `M8`: Lorentz image on `R^{1,3}` and a linear ambient action on `S^2_C`. -/
noncomputable def poincareM8LinearAction
    (M : SL(2, ℂ)) (A : Matrix (Fin 3) (Fin 3) ℂ) (q : PoincareM8) : PoincareM8 :=
  (sl2cMinkowskiAction M q.1, complexTwoSphereLinearAction A q.2)

/-- The identity product action fixes every coordinate-level `M8` point. -/
lemma poincareM8LinearAction_one (q : PoincareM8) :
    poincareM8LinearAction 1 1 q = q := by
  cases q
  simp [poincareM8LinearAction, sl2cMinkowskiAction, complexTwoSphereLinearAction]

/-- Product actions compose componentwise on `M8`. -/
lemma poincareM8LinearAction_mul
    (M N : SL(2, ℂ)) (A B : Matrix (Fin 3) (Fin 3) ℂ) (q : PoincareM8) :
    poincareM8LinearAction (M * N) (A * B) q =
      poincareM8LinearAction M A (poincareM8LinearAction N B q) := by
  cases q
  simp [poincareM8LinearAction, sl2cMinkowskiAction_mul, complexTwoSphereLinearAction_mul]

/-- If the internal linear action preserves the quadratic form, the `M8` action preserves the
complex-sphere constraint in the second component. -/
lemma poincareM8LinearAction_preserves_internal_sphere
    (M : SL(2, ℂ)) {A : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : PreservesComplexTwoSphereQuadratic A) {r : ℂ} {q : PoincareM8}
    (hq : OnComplexTwoSphere r q.2) :
    OnComplexTwoSphere r (poincareM8LinearAction M A q).2 :=
  complexTwoSphereLinearAction_preserves_sphere hA hq

/-- A finite separated radial/spherical expansion
`sum_j c_j f_j(r) Z_j(z)`, the finite-mode version of the paper's hyperspherical
series on the complex two-sphere. -/
noncomputable def finiteSphereModeExpansion {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (radial : ι -> ℂ -> ℂ)
    (harmonic : ι -> ComplexTwoSpherePoint -> ℂ) (r : ℂ) (z : ComplexTwoSpherePoint) : ℂ :=
  ∑ j, coeff j * radial j r * harmonic j z

/-- The corresponding boundary series after evaluating the radial functions at the boundary. -/
noncomputable def finiteBoundaryModeExpansion {ι : Type*} [Fintype ι]
    (coeff boundaryRadial : ι -> ℂ) (harmonic : ι -> ComplexTwoSpherePoint -> ℂ)
    (z : ComplexTwoSpherePoint) : ℂ :=
  ∑ j, coeff j * boundaryRadial j * harmonic j z

/-- A field matches boundary data on the complex two-sphere of radius `r`. -/
def MatchesBoundaryData (field : ℂ -> ComplexTwoSpherePoint -> ℂ)
    (boundary : ComplexTwoSpherePoint -> ℂ) (r : ℂ) : Prop :=
  ∀ z, OnComplexTwoSphere r z -> field r z = boundary z

/-- The finite radial/spherical expansion has the prescribed boundary trace. -/
lemma finiteSphereModeExpansion_boundary {ι : Type*} [Fintype ι]
    (coeff boundaryRadial : ι -> ℂ) (radial : ι -> ℂ -> ℂ)
    (harmonic : ι -> ComplexTwoSpherePoint -> ℂ) (r : ℂ) (z : ComplexTwoSpherePoint)
    (hboundary : ∀ j, radial j r = boundaryRadial j) :
    finiteSphereModeExpansion coeff radial harmonic r z =
      finiteBoundaryModeExpansion coeff boundaryRadial harmonic z := by
  unfold finiteSphereModeExpansion finiteBoundaryModeExpansion
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hboundary j]

/-- The finite radial/spherical expansion solves its finite boundary problem. -/
lemma finiteSphereModeExpansion_matchesBoundaryData {ι : Type*} [Fintype ι]
    (coeff boundaryRadial : ι -> ℂ) (radial : ι -> ℂ -> ℂ)
    (harmonic : ι -> ComplexTwoSpherePoint -> ℂ) (r : ℂ)
    (hboundary : ∀ j, radial j r = boundaryRadial j) :
    MatchesBoundaryData
      (finiteSphereModeExpansion coeff radial harmonic)
      (finiteBoundaryModeExpansion coeff boundaryRadial harmonic) r := by
  intro z _hz
  exact finiteSphereModeExpansion_boundary coeff boundaryRadial radial harmonic r z hboundary

/-- Boundary mode expansion is linear in the coefficient sequence. -/
lemma finiteBoundaryModeExpansion_add_coeff {ι : Type*} [Fintype ι]
    (coeff₁ coeff₂ boundaryRadial : ι -> ℂ)
    (harmonic : ι -> ComplexTwoSpherePoint -> ℂ) (z : ComplexTwoSpherePoint) :
    finiteBoundaryModeExpansion (fun j => coeff₁ j + coeff₂ j) boundaryRadial harmonic z =
      finiteBoundaryModeExpansion coeff₁ boundaryRadial harmonic z
        + finiteBoundaryModeExpansion coeff₂ boundaryRadial harmonic z := by
  unfold finiteBoundaryModeExpansion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Componentwise finite expansion for spinor or Maxwell multiplets. -/
noncomputable def finiteComponentSphereModeExpansion {ν ι : Type*} [Fintype ι]
    (coeff : ν -> ι -> ℂ) (radial : ν -> ι -> ℂ -> ℂ)
    (harmonic : ν -> ι -> ComplexTwoSpherePoint -> ℂ) :
    ν -> ℂ -> ComplexTwoSpherePoint -> ℂ :=
  fun a => finiteSphereModeExpansion (coeff a) (radial a) (harmonic a)

/-- Componentwise boundary expansion for spinor or Maxwell multiplets. -/
noncomputable def finiteComponentBoundaryModeExpansion {ν ι : Type*} [Fintype ι]
    (coeff boundaryRadial : ν -> ι -> ℂ)
    (harmonic : ν -> ι -> ComplexTwoSpherePoint -> ℂ) :
    ν -> ComplexTwoSpherePoint -> ℂ :=
  fun a => finiteBoundaryModeExpansion (coeff a) (boundaryRadial a) (harmonic a)

/-- A component field matches componentwise boundary data on the complex two-sphere. -/
def MatchesComponentBoundaryData {ν : Type*} (field : ν -> ℂ -> ComplexTwoSpherePoint -> ℂ)
    (boundary : ν -> ComplexTwoSpherePoint -> ℂ) (r : ℂ) : Prop :=
  ∀ a z, OnComplexTwoSphere r z -> field a r z = boundary a z

/-- Componentwise finite expansions solve the componentwise finite boundary problem. -/
lemma finiteComponentSphereModeExpansion_matchesBoundaryData {ν ι : Type*} [Fintype ι]
    (coeff boundaryRadial : ν -> ι -> ℂ) (radial : ν -> ι -> ℂ -> ℂ)
    (harmonic : ν -> ι -> ComplexTwoSpherePoint -> ℂ) (r : ℂ)
    (hboundary : ∀ a j, radial a j r = boundaryRadial a j) :
    MatchesComponentBoundaryData
      (finiteComponentSphereModeExpansion coeff radial harmonic)
      (finiteComponentBoundaryModeExpansion coeff boundaryRadial harmonic) r := by
  intro a z _hz
  exact finiteSphereModeExpansion_boundary (coeff a) (boundaryRadial a) (radial a)
    (harmonic a) r z (hboundary a)

/-- A Dirac boundary spinor has four complex components. -/
abbrev DiracBoundarySpinor := Fin 4 -> ComplexTwoSpherePoint -> ℂ

/-- A Majorana-Oppenheimer Maxwell boundary field has six complex components. -/
abbrev MaxwellBoundaryBispinor := Fin 6 -> ComplexTwoSpherePoint -> ℂ

/-! ## E.2. Dirac-Like Field Equations from the Group Lagrangian -/

/-- Varlamov's matrix normalization `Gamma_mu = B_11^{-1} B_mu` from Eq. 98. -/
noncomputable def varlamovGamma {ν : Type*} [Fintype ν] [DecidableEq ν]
    (B11 Bmu : Matrix ν ν ℂ) : Matrix ν ν ℂ :=
  B11⁻¹ * Bmu

/-- If `B_11` has the displayed left inverse, the normalized matrix satisfies
`B_11 Gamma_mu = B_mu`. -/
lemma varlamovGamma_left_mul {ν : Type*} [Fintype ν] [DecidableEq ν]
    (B11 Bmu : Matrix ν ν ℂ) (hB : B11 * B11⁻¹ = 1) :
    B11 * varlamovGamma B11 Bmu = Bmu := by
  rw [varlamovGamma, ← Matrix.mul_assoc, hB, Matrix.one_mul]

/-! ### E.2.1. The Section 7 First-Order Lagrangian -/

/-- The finite component pairing `barPsi psi = sum_a barPsi_a psi_a` used in the
first-order Poincare-group Lagrangian. -/
noncomputable def varlamovPairing {ν : Type*} [Fintype ν]
    (barPsi psi : ν -> ℂ) : ℂ :=
  ∑ a, barPsi a * psi a

/-- Pairing any finite component field with the zero field gives zero. -/
@[simp] lemma varlamovPairing_zero_right {ν : Type*} [Fintype ν]
    (barPsi : ν -> ℂ) :
    varlamovPairing barPsi 0 = 0 := by
  simp [varlamovPairing]

/-- A coordinate basis test field extracts the corresponding component in the finite
component pairing. -/
lemma varlamovPairing_single_left {ν : Type*} [Fintype ν] [DecidableEq ν]
    (a : ν) (psi : ν -> ℂ) :
    varlamovPairing (fun b => if b = a then 1 else 0) psi = psi a := by
  simp [varlamovPairing]

/-- Finite-dimensional fundamental lemma for the component pairing: if every test
field pairs to zero with `psi`, then `psi` is the zero component field. -/
lemma varlamovPairing_ext_zero_of_forall {ν : Type*} [Fintype ν] [DecidableEq ν]
    (psi : ν -> ℂ) (h : ∀ eta : ν -> ℂ, varlamovPairing eta psi = 0) :
    psi = 0 := by
  funext a
  simpa [varlamovPairing_single_left] using h (fun b => if b = a then 1 else 0)

/-- Varlamov's finite first-order Lagrangian density from Eq. 98:
`-1/2 (barPsi Gamma_mu d_mu psi - d_mu barPsi Gamma_mu psi) - kappa barPsi psi`.
The derivative data are kept explicit, so the formula can be used on finite
samples before the analytic tangent-bundle API is supplied. -/
noncomputable def varlamovFirstOrderLagrangianDensity {μ ν : Type*} [Fintype μ]
    [Fintype ν] (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (barPsi psi : ν -> ℂ) (dbarPsi dpsi : μ -> ν -> ℂ) : ℂ :=
  -(1 / 2 : ℂ) *
      (∑ mu, (varlamovPairing barPsi (Gamma mu *ᵥ dpsi mu)
        - varlamovPairing (dbarPsi mu) (Gamma mu *ᵥ psi)))
    - kappa * varlamovPairing barPsi psi

/-- Directional variation density in the independent `barPsi` variable before integrating
derivatives off the test field. -/
noncomputable def varlamovBarDirectionalVariationDensity {μ ν : Type*}
    [Fintype μ] [Fintype ν] (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (eta psi : ν -> ℂ) (deta dpsi : μ -> ν -> ℂ) : ℂ :=
  varlamovFirstOrderLagrangianDensity Gamma kappa eta psi deta dpsi

/-- Directional variation density in the independent `psi` variable before integrating
derivatives off the test field. -/
noncomputable def varlamovPsiDirectionalVariationDensity {μ ν : Type*}
    [Fintype μ] [Fintype ν] (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (barPsi eta : ν -> ℂ) (dbarPsi deta : μ -> ν -> ℂ) : ℂ :=
  varlamovFirstOrderLagrangianDensity Gamma kappa barPsi eta dbarPsi deta

/-- Exact first variation of the displayed first-order Lagrangian density with respect to
the independent adjoint field `barPsi`. -/
lemma varlamovFirstOrderLagrangianDensity_add_bar {μ ν : Type*}
    [Fintype μ] [Fintype ν] (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (barPsi eta psi : ν -> ℂ) (dbarPsi deta dpsi : μ -> ν -> ℂ) :
    varlamovFirstOrderLagrangianDensity Gamma kappa (barPsi + eta) psi
        (fun mu => dbarPsi mu + deta mu) dpsi =
      varlamovFirstOrderLagrangianDensity Gamma kappa barPsi psi dbarPsi dpsi
        + varlamovBarDirectionalVariationDensity Gamma kappa eta psi deta dpsi := by
  simp [varlamovFirstOrderLagrangianDensity, varlamovBarDirectionalVariationDensity,
    varlamovPairing, Matrix.mulVec, Finset.sum_add_distrib, add_mul, Pi.add_apply]
  ring

/-- Exact first variation of the displayed first-order Lagrangian density with respect to
the independent field `psi`. -/
lemma varlamovFirstOrderLagrangianDensity_add_psi {μ ν : Type*}
    [Fintype μ] [Fintype ν] (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (barPsi psi eta : ν -> ℂ) (dbarPsi dpsi deta : μ -> ν -> ℂ) :
    varlamovFirstOrderLagrangianDensity Gamma kappa barPsi (psi + eta)
        dbarPsi (fun mu => dpsi mu + deta mu) =
      varlamovFirstOrderLagrangianDensity Gamma kappa barPsi psi dbarPsi dpsi
        + varlamovPsiDirectionalVariationDensity Gamma kappa barPsi eta dbarPsi deta := by
  simp [varlamovFirstOrderLagrangianDensity, varlamovPsiDirectionalVariationDensity,
    varlamovPairing, Matrix.mulVec, Finset.sum_add_distrib, mul_add, Pi.add_apply]
  ring

/-- The finite residual of Varlamov's first-order equation
`sum_mu Gamma_mu d_mu psi + kappa psi = 0`.  The Dirac equations use `kappa = m`;
the Maxwell equations are the `kappa = 0` member. -/
noncomputable def varlamovDiracLikeResidual {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dpsi : μ -> ν -> ℂ) : ν -> ℂ :=
  (∑ mu, Gamma mu *ᵥ dpsi mu) + kappa • psi

/-- A finite field satisfies Varlamov's Dirac-like first-order equation when the residual
vanishes. -/
def IsVarlamovDiracLikeSolution {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dpsi : μ -> ν -> ℂ) : Prop :=
  varlamovDiracLikeResidual Gamma kappa psi dpsi = 0

/-- The Dirac-like residual is additive in the field and derivative data. -/
lemma varlamovDiracLikeResidual_add {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi₁ psi₂ : ν -> ℂ) (dpsi₁ dpsi₂ : μ -> ν -> ℂ) :
    varlamovDiracLikeResidual Gamma kappa (psi₁ + psi₂) (fun mu => dpsi₁ mu + dpsi₂ mu) =
      varlamovDiracLikeResidual Gamma kappa psi₁ dpsi₁
        + varlamovDiracLikeResidual Gamma kappa psi₂ dpsi₂ := by
  funext a
  simp [varlamovDiracLikeResidual, Matrix.mulVec, Finset.sum_add_distrib, smul_add,
    add_assoc, add_comm, add_left_comm]

/-- The Dirac-like residual is homogeneous under simultaneous scalar multiplication of
the field and derivative data. -/
lemma varlamovDiracLikeResidual_smul {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa a : ℂ)
    (psi : ν -> ℂ) (dpsi : μ -> ν -> ℂ) :
    varlamovDiracLikeResidual Gamma kappa (a • psi) (fun mu => a • dpsi mu) =
      a • varlamovDiracLikeResidual Gamma kappa psi dpsi := by
  funext b
  simp [varlamovDiracLikeResidual, Matrix.mulVec]
  rw [mul_add, Finset.mul_sum]
  ring_nf

/-- Sums of solutions of the same Varlamov first-order equation are again solutions. -/
lemma IsVarlamovDiracLikeSolution.add {μ ν : Type*} [Fintype μ] [Fintype ν]
    {Gamma : μ -> Matrix ν ν ℂ} {kappa : ℂ}
    {psi₁ psi₂ : ν -> ℂ} {dpsi₁ dpsi₂ : μ -> ν -> ℂ}
    (h₁ : IsVarlamovDiracLikeSolution Gamma kappa psi₁ dpsi₁)
    (h₂ : IsVarlamovDiracLikeSolution Gamma kappa psi₂ dpsi₂) :
    IsVarlamovDiracLikeSolution Gamma kappa (psi₁ + psi₂)
      (fun mu => dpsi₁ mu + dpsi₂ mu) := by
  rw [IsVarlamovDiracLikeSolution, varlamovDiracLikeResidual_add, h₁, h₂, add_zero]

/-- Scalar multiples of a solution of Varlamov's first-order equation are again solutions. -/
lemma IsVarlamovDiracLikeSolution.smul {μ ν : Type*} [Fintype μ] [Fintype ν]
    {Gamma : μ -> Matrix ν ν ℂ} {kappa a : ℂ}
    {psi : ν -> ℂ} {dpsi : μ -> ν -> ℂ}
    (h : IsVarlamovDiracLikeSolution Gamma kappa psi dpsi) :
    IsVarlamovDiracLikeSolution Gamma kappa (a • psi) (fun mu => a • dpsi mu) := by
  rw [IsVarlamovDiracLikeSolution, varlamovDiracLikeResidual_smul, h, smul_zero]

/-- The adjoint residual obtained by varying the field `psi` independently:
`sum_mu Gamma_mu^T d_mu barPsi - kappa barPsi = 0`, matching the second equation in
Varlamov Eq. 99 after transposition from row to column notation. -/
noncomputable def varlamovAdjointResidual {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (barPsi : ν -> ℂ) (dbarPsi : μ -> ν -> ℂ) : ν -> ℂ :=
  (∑ mu, (Gamma mu).transpose *ᵥ dbarPsi mu) - kappa • barPsi

/-- A finite adjoint field satisfies Varlamov's adjoint first-order equation when the
adjoint residual vanishes. -/
def IsVarlamovAdjointSolution {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (barPsi : ν -> ℂ) (dbarPsi : μ -> ν -> ℂ) : Prop :=
  varlamovAdjointResidual Gamma kappa barPsi dbarPsi = 0

/-- The integrated-by-parts bulk first variation with respect to `barPsi`.  Its
coefficient is the Dirac-like residual, so stationarity is exactly Eq. 99/100. -/
noncomputable def varlamovBulkBarVariation {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dpsi : μ -> ν -> ℂ) (eta : ν -> ℂ) : ℂ :=
  -varlamovPairing eta (varlamovDiracLikeResidual Gamma kappa psi dpsi)

/-- Stationarity of the finite bulk variation with respect to every `barPsi` test field
is equivalent to Varlamov's first-order field equation. -/
lemma varlamovBulkBarVariation_stationary_iff_diracLike {μ ν : Type*} [Fintype μ]
    [Fintype ν] [DecidableEq ν] (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dpsi : μ -> ν -> ℂ) :
    (∀ eta : ν -> ℂ, varlamovBulkBarVariation Gamma kappa psi dpsi eta = 0) ↔
      IsVarlamovDiracLikeSolution Gamma kappa psi dpsi := by
  constructor
  · intro h
    rw [IsVarlamovDiracLikeSolution]
    apply varlamovPairing_ext_zero_of_forall
    intro eta
    exact neg_eq_zero.mp (h eta)
  · intro h eta
    rw [IsVarlamovDiracLikeSolution] at h
    simp [varlamovBulkBarVariation, h]

/-- The integrated-by-parts bulk first variation with respect to `psi`.  Its coefficient
is the adjoint residual. -/
noncomputable def varlamovBulkPsiVariation {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (barPsi : ν -> ℂ) (dbarPsi : μ -> ν -> ℂ) (eta : ν -> ℂ) : ℂ :=
  varlamovPairing eta (varlamovAdjointResidual Gamma kappa barPsi dbarPsi)

/-- Stationarity of the finite bulk variation with respect to every `psi` test field is
equivalent to the adjoint Varlamov equation. -/
lemma varlamovBulkPsiVariation_stationary_iff_adjoint {μ ν : Type*} [Fintype μ]
    [Fintype ν] [DecidableEq ν] (Gamma : μ -> Matrix ν ν ℂ) (kappa : ℂ)
    (barPsi : ν -> ℂ) (dbarPsi : μ -> ν -> ℂ) :
    (∀ eta : ν -> ℂ, varlamovBulkPsiVariation Gamma kappa barPsi dbarPsi eta = 0) ↔
      IsVarlamovAdjointSolution Gamma kappa barPsi dbarPsi := by
  constructor
  · intro h
    rw [IsVarlamovAdjointSolution]
    exact varlamovPairing_ext_zero_of_forall
      (varlamovAdjointResidual Gamma kappa barPsi dbarPsi) h
  · intro h eta
    rw [IsVarlamovAdjointSolution] at h
    simp [varlamovBulkPsiVariation, h]

/-- The Maxwell-like residual is the massless `kappa = 0` member of the same first-order
family. -/
noncomputable def varlamovMaxwellLikeResidual {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (phi : ν -> ℂ) (dphi : μ -> ν -> ℂ) : ν -> ℂ :=
  varlamovDiracLikeResidual Gamma 0 phi dphi

/-- The Maxwell-like residual contains only the derivative term. -/
lemma varlamovMaxwellLikeResidual_eq_sum {μ ν : Type*} [Fintype μ] [Fintype ν]
    (Gamma : μ -> Matrix ν ν ℂ) (phi : ν -> ℂ) (dphi : μ -> ν -> ℂ) :
    varlamovMaxwellLikeResidual Gamma phi dphi = ∑ mu, Gamma mu *ᵥ dphi mu := by
  funext a
  simp [varlamovMaxwellLikeResidual, varlamovDiracLikeResidual]

/-! ### E.2.2. `M10 = R^{1,3} x L6` Field Equations -/

/-- The finite `M10` residual
`sum_i Gamma_i d_i psi + sum_k Gamma_k d_k psi + kappa psi = 0` before restricting to
the `M8 = R^{1,3} x S^2_C` homogeneous space. -/
noncomputable def varlamovPoincareGroupResidual {ν : Type*} [Fintype ν]
    (GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ)
    (GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dX : SpaceTimeTangentIndex -> ν -> ℂ)
    (dG : LorentzGroupTangentIndex -> ν -> ℂ) : ν -> ℂ :=
  (∑ i, GammaX i *ᵥ dX i) + (∑ k, GammaG k *ᵥ dG k) + kappa • psi

/-- A finite component field satisfies Varlamov's Poincare-group field equation on
`M10` when the split residual vanishes. -/
def IsVarlamovPoincareGroupFieldEquation {ν : Type*} [Fintype ν]
    (GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ)
    (GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dX : SpaceTimeTangentIndex -> ν -> ℂ)
    (dG : LorentzGroupTangentIndex -> ν -> ℂ) : Prop :=
  varlamovPoincareGroupResidual GammaX GammaG kappa psi dX dG = 0

/-- The split group-manifold form of Varlamov's field equations, keeping the spacetime
and Lorentz-group differential equations as two named equations. -/
def VarlamovSplitGroupManifoldEquations {ν : Type*} [Fintype ν]
    (GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ)
    (GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dX : SpaceTimeTangentIndex -> ν -> ℂ)
    (dG : LorentzGroupTangentIndex -> ν -> ℂ) : Prop :=
  IsVarlamovDiracLikeSolution GammaX kappa psi dX
    ∧ IsVarlamovDiracLikeSolution GammaG kappa psi dG

/-- The split group-manifold equations expose the spacetime equation. -/
lemma VarlamovSplitGroupManifoldEquations.spacetime {ν : Type*} [Fintype ν]
    {GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ}
    {GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ} {kappa : ℂ}
    {psi : ν -> ℂ} {dX : SpaceTimeTangentIndex -> ν -> ℂ}
    {dG : LorentzGroupTangentIndex -> ν -> ℂ}
    (h : VarlamovSplitGroupManifoldEquations GammaX GammaG kappa psi dX dG) :
    IsVarlamovDiracLikeSolution GammaX kappa psi dX :=
  h.1

/-- The split group-manifold equations expose the Lorentz-group equation. -/
lemma VarlamovSplitGroupManifoldEquations.lorentzGroup {ν : Type*} [Fintype ν]
    {GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ}
    {GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ} {kappa : ℂ}
    {psi : ν -> ℂ} {dX : SpaceTimeTangentIndex -> ν -> ℂ}
    {dG : LorentzGroupTangentIndex -> ν -> ℂ}
    (h : VarlamovSplitGroupManifoldEquations GammaX GammaG kappa psi dX dG) :
    IsVarlamovDiracLikeSolution GammaG kappa psi dG :=
  h.2

/-- If the Lorentz-group derivative term is zero, the split `M10` residual reduces to
the spacetime equation from Varlamov Eq. 99. -/
lemma varlamovPoincareGroupResidual_eq_spacetime_of_zero_lorentz {ν : Type*}
    [Fintype ν] (GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ)
    (GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dX : SpaceTimeTangentIndex -> ν -> ℂ) :
    varlamovPoincareGroupResidual GammaX GammaG kappa psi dX (fun _ => 0) =
      varlamovDiracLikeResidual GammaX kappa psi dX := by
  funext a
  simp [varlamovPoincareGroupResidual, varlamovDiracLikeResidual, Matrix.mulVec]

/-- If the spacetime derivative term is zero, the split `M10` residual reduces to the
Lorentz-group equation from Varlamov Eq. 100. -/
lemma varlamovPoincareGroupResidual_eq_lorentz_of_zero_spacetime {ν : Type*}
    [Fintype ν] (GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ)
    (GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dG : LorentzGroupTangentIndex -> ν -> ℂ) :
    varlamovPoincareGroupResidual GammaX GammaG kappa psi (fun _ => 0) dG =
      varlamovDiracLikeResidual GammaG kappa psi dG := by
  funext a
  simp [varlamovPoincareGroupResidual, varlamovDiracLikeResidual, Matrix.mulVec]

/-- The finite bulk first variation for the split `M10` Poincare-group equation. -/
noncomputable def varlamovPoincareGroupBulkBarVariation {ν : Type*} [Fintype ν]
    (GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ)
    (GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dX : SpaceTimeTangentIndex -> ν -> ℂ)
    (dG : LorentzGroupTangentIndex -> ν -> ℂ) (eta : ν -> ℂ) : ℂ :=
  -varlamovPairing eta (varlamovPoincareGroupResidual GammaX GammaG kappa psi dX dG)

/-- Stationarity of the split `M10` bulk first variation is equivalent to the finite
Poincare-group field equation. -/
lemma varlamovPoincareGroupBulkBarVariation_stationary_iff {ν : Type*} [Fintype ν]
    [DecidableEq ν] (GammaX : SpaceTimeTangentIndex -> Matrix ν ν ℂ)
    (GammaG : LorentzGroupTangentIndex -> Matrix ν ν ℂ) (kappa : ℂ)
    (psi : ν -> ℂ) (dX : SpaceTimeTangentIndex -> ν -> ℂ)
    (dG : LorentzGroupTangentIndex -> ν -> ℂ) :
    (∀ eta : ν -> ℂ,
        varlamovPoincareGroupBulkBarVariation GammaX GammaG kappa psi dX dG eta = 0) ↔
      IsVarlamovPoincareGroupFieldEquation GammaX GammaG kappa psi dX dG := by
  constructor
  · intro h
    rw [IsVarlamovPoincareGroupFieldEquation]
    apply varlamovPairing_ext_zero_of_forall
    intro eta
    exact neg_eq_zero.mp (h eta)
  · intro h eta
    rw [IsVarlamovPoincareGroupFieldEquation] at h
    simp [varlamovPoincareGroupBulkBarVariation, h]

/-! ### E.2.3. Section 8 Dirac Field on the Poincare Group -/

/-- Spinor component index for the four-component Dirac field in Section 8. -/
abbrev DiracSpinorIndex := Fin 4

/-- A four-component Dirac spinor written as a component function. -/
abbrev DiracSpinorField := DiracSpinorIndex -> ℂ

/-- Varlamov Eq. 123 uses the standard Dirac-representation gamma matrices already
available in Physlib's Clifford-algebra module. -/
def varlamovDiracGamma (mu : SpaceTimeTangentIndex) :
    Matrix DiracSpinorIndex DiracSpinorIndex ℂ :=
  spaceTime.γ mu

/-- The paper's `gamma_0` matrix is the existing `spaceTime.gamma0`. -/
@[simp] lemma varlamovDiracGamma_zero :
    varlamovDiracGamma 0 = spaceTime.γ0 := rfl

/-- The paper's `gamma_1` matrix is the existing `spaceTime.gamma1`. -/
@[simp] lemma varlamovDiracGamma_one :
    varlamovDiracGamma 1 = spaceTime.γ1 := rfl

/-- The paper's `gamma_2` matrix is the existing `spaceTime.gamma2`. -/
@[simp] lemma varlamovDiracGamma_two :
    varlamovDiracGamma 2 = spaceTime.γ2 := rfl

/-- The paper's `gamma_3` matrix is the existing `spaceTime.gamma3`. -/
@[simp] lemma varlamovDiracGamma_three :
    varlamovDiracGamma 3 = spaceTime.γ3 := rfl

/-- Varlamov Eq. 123, `gamma_0`, as an explicit `4 x 4` matrix. -/
lemma varlamovDiracGamma_zero_matrix :
    varlamovDiracGamma 0 =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  rfl

/-- Varlamov Eq. 123, `gamma_1`, as an explicit `4 x 4` matrix. -/
lemma varlamovDiracGamma_one_matrix :
    varlamovDiracGamma 1 =
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0] := by
  rfl

/-- Varlamov Eq. 123, `gamma_2`, as an explicit `4 x 4` matrix. -/
lemma varlamovDiracGamma_two_matrix :
    varlamovDiracGamma 2 =
      !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0;
        0, Complex.I, 0, 0; -Complex.I, 0, 0, 0] := by
  rfl

/-- Varlamov Eq. 123, `gamma_3`, as an explicit `4 x 4` matrix. -/
lemma varlamovDiracGamma_three_matrix :
    varlamovDiracGamma 3 =
      !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0] := by
  rfl

/-- The Varlamov gamma matrices satisfy the standard Clifford anticommutation relation. -/
lemma varlamovDiracGamma_clifford (mu nu : SpaceTimeTangentIndex) :
    varlamovDiracGamma mu * varlamovDiracGamma nu
        + varlamovDiracGamma nu * varlamovDiracGamma mu =
      (2 * minkowskiEta mu nu) • (1 : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) := by
  simpa [varlamovDiracGamma] using gamma_anticomm mu nu

/-- Varlamov Eq. 127, written with the canonical Physlib Dirac matrices. -/
noncomputable def varlamovSpacetimeDiracResidual (kappa : ℂ)
    (psi : DiracSpinorField)
    (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) : DiracSpinorField :=
  varlamovDiracLikeResidual varlamovDiracGamma kappa psi dpsi

/-- The usual first-order Dirac residual
`sum_mu gamma^mu partial_mu psi + kappa psi`, using the canonical Physlib gamma matrices. -/
noncomputable def usualDiracResidual (kappa : ℂ)
    (psi : DiracSpinorField)
    (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) : DiracSpinorField :=
  (∑ mu, spaceTime.γ mu *ᵥ dpsi mu) + kappa • psi

/-- A spinor solves Varlamov Eq. 127 when the spacetime Dirac residual vanishes. -/
def IsVarlamovSpacetimeDiracSolution (kappa : ℂ)
    (psi : DiracSpinorField)
    (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) : Prop :=
  varlamovSpacetimeDiracResidual kappa psi dpsi = 0

/-- A spinor solves the usual finite-component Dirac equation when the canonical residual vanishes. -/
def IsUsualDiracEquation (kappa : ℂ)
    (psi : DiracSpinorField)
    (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) : Prop :=
  usualDiracResidual kappa psi dpsi = 0

/-- Varlamov Eq. 127 is definitionally the usual Dirac residual after identifying the
paper's gamma matrices with `spaceTime.gamma`. -/
lemma varlamovSpacetimeDiracResidual_eq_usualDiracResidual (kappa : ℂ)
    (psi : DiracSpinorField) (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) :
    varlamovSpacetimeDiracResidual kappa psi dpsi =
      usualDiracResidual kappa psi dpsi := by
  rfl

/-- The paper's spacetime Dirac equation is equivalent to the usual Dirac equation. -/
lemma isVarlamovSpacetimeDiracSolution_iff_usualDiracEquation (kappa : ℂ)
    (psi : DiracSpinorField) (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) :
    IsVarlamovSpacetimeDiracSolution kappa psi dpsi ↔
      IsUsualDiracEquation kappa psi dpsi := by
  rfl

/-- Component form of Varlamov Eq. 127. -/
def VarlamovDiracComponentEquation (kappa : ℂ)
    (psi : DiracSpinorField)
    (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) : Prop :=
  ∀ a, ((∑ mu, varlamovDiracGamma mu *ᵥ dpsi mu) + kappa • psi) a = 0

/-- Vanishing of the Dirac residual is equivalent to the four displayed component equations. -/
lemma isVarlamovSpacetimeDiracSolution_iff_component_equations (kappa : ℂ)
    (psi : DiracSpinorField) (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) :
    IsVarlamovSpacetimeDiracSolution kappa psi dpsi ↔
      VarlamovDiracComponentEquation kappa psi dpsi := by
  rw [IsVarlamovSpacetimeDiracSolution, VarlamovDiracComponentEquation,
    varlamovSpacetimeDiracResidual]
  constructor
  · intro h a
    simpa [varlamovDiracLikeResidual] using congrFun h a
  · intro h
    funext a
    simpa [varlamovDiracLikeResidual] using h a

/-- Varlamov Eq. 127 is the generic first-order residual specialized to the standard
Dirac gamma matrices. -/
lemma isVarlamovSpacetimeDiracSolution_iff_diracLike (kappa : ℂ)
    (psi : DiracSpinorField) (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) :
    IsVarlamovSpacetimeDiracSolution kappa psi dpsi ↔
      IsVarlamovDiracLikeSolution varlamovDiracGamma kappa psi dpsi := by
  rfl

/-- The six Lorentz-group matrices `Upsilon_k` appearing in Varlamov Eq. 128. -/
abbrev VarlamovDiracGroupMatrix :=
  LorentzGroupTangentIndex -> Matrix DiracSpinorIndex DiracSpinorIndex ℂ

/-- Varlamov Eq. 128, the internal Lorentz-group Dirac equation. -/
noncomputable def varlamovGroupDiracResidual (Upsilon : VarlamovDiracGroupMatrix)
    (kappa : ℂ) (psi : DiracSpinorField)
    (dgpsi : LorentzGroupTangentIndex -> DiracSpinorField) : DiracSpinorField :=
  varlamovDiracLikeResidual Upsilon kappa psi dgpsi

/-- A spinor solves Varlamov Eq. 128 when the group residual vanishes. -/
def IsVarlamovGroupDiracSolution (Upsilon : VarlamovDiracGroupMatrix)
    (kappa : ℂ) (psi : DiracSpinorField)
    (dgpsi : LorentzGroupTangentIndex -> DiracSpinorField) : Prop :=
  varlamovGroupDiracResidual Upsilon kappa psi dgpsi = 0

/-- If the Lorentz-group derivative term is absent, Varlamov's split `M10` Dirac
equation reduces to the usual spacetime Dirac equation. -/
lemma varlamovPoincareGroupResidual_eq_spacetime_dirac_of_zero_lorentz
    (Upsilon : VarlamovDiracGroupMatrix) (kappa : ℂ)
    (psi : DiracSpinorField) (dpsi : SpaceTimeTangentIndex -> DiracSpinorField) :
    varlamovPoincareGroupResidual varlamovDiracGamma Upsilon kappa psi dpsi (fun _ => 0) =
      varlamovSpacetimeDiracResidual kappa psi dpsi := by
  simpa [varlamovSpacetimeDiracResidual] using
    (varlamovPoincareGroupResidual_eq_spacetime_of_zero_lorentz
      varlamovDiracGamma Upsilon kappa psi dpsi)

/-- If the spacetime derivative term is absent, Varlamov's split `M10` Dirac equation
reduces to the internal Lorentz-group equation. -/
lemma varlamovPoincareGroupResidual_eq_group_dirac_of_zero_spacetime
    (Upsilon : VarlamovDiracGroupMatrix) (kappa : ℂ)
    (psi : DiracSpinorField)
    (dgpsi : LorentzGroupTangentIndex -> DiracSpinorField) :
    varlamovPoincareGroupResidual varlamovDiracGamma Upsilon kappa psi (fun _ => 0) dgpsi =
      varlamovGroupDiracResidual Upsilon kappa psi dgpsi := by
  simpa [varlamovGroupDiracResidual] using
    (varlamovPoincareGroupResidual_eq_lorentz_of_zero_spacetime
      varlamovDiracGamma Upsilon kappa psi dgpsi)

/-- A separated Dirac field on `M8`, with spacetime and complex-two-sphere factors. -/
structure VarlamovSeparatedDiracField where
  /-- Spacetime spinor factor. -/
  spacetime : MinkowskiPoint -> DiracSpinorField
  /-- Internal complex-two-sphere spinor factor. -/
  internal : ComplexTwoSpherePoint -> DiracSpinorField

/-- Componentwise product of the spacetime and internal factors of a separated Dirac field. -/
noncomputable def VarlamovSeparatedDiracField.eval
    (F : VarlamovSeparatedDiracField) : PoincareM8 -> DiracSpinorField :=
  fun q a => F.spacetime q.1 a * F.internal q.2 a

/-- Evaluation of a separated Dirac field is componentwise multiplication of its factors. -/
@[simp] lemma VarlamovSeparatedDiracField.eval_apply
    (F : VarlamovSeparatedDiracField) (q : PoincareM8) (a : DiracSpinorIndex) :
    F.eval q a = F.spacetime q.1 a * F.internal q.2 a := rfl

/-- Finite separated solution series for Varlamov Eqs. 134--137: a sum of spinor
amplitudes times `M8` Fourier modes. -/
noncomputable def finiteDiracSeparatedModeSeries {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (amplitude : ι -> DiracSpinorField)
    (momentum : ι -> MinkowskiPoint)
    (internalMode : ι -> ComplexTwoSpherePoint -> ℂ) :
    PoincareM8 -> DiracSpinorField :=
  fun q a => ∑ i, coeff i * amplitude i a *
    finiteM8FourierMode (momentum i) (internalMode i) q

/-- The finite separated Dirac series is linear in the scalar coefficients. -/
lemma finiteDiracSeparatedModeSeries_add_coeff {ι : Type*} [Fintype ι]
    (coeff₁ coeff₂ : ι -> ℂ) (amplitude : ι -> DiracSpinorField)
    (momentum : ι -> MinkowskiPoint)
    (internalMode : ι -> ComplexTwoSpherePoint -> ℂ) :
    finiteDiracSeparatedModeSeries (fun i => coeff₁ i + coeff₂ i) amplitude momentum
        internalMode =
      fun q a => finiteDiracSeparatedModeSeries coeff₁ amplitude momentum internalMode q a
        + finiteDiracSeparatedModeSeries coeff₂ amplitude momentum internalMode q a := by
  funext q a
  unfold finiteDiracSeparatedModeSeries
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Translation of the finite separated Dirac series multiplies each mode by its
translation character. -/
lemma finiteDiracSeparatedModeSeries_translate {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (amplitude : ι -> DiracSpinorField)
    (momentum : ι -> MinkowskiPoint)
    (internalMode : ι -> ComplexTwoSpherePoint -> ℂ)
    (b : MinkowskiPoint) (q : PoincareM8) (a : DiracSpinorIndex) :
    finiteDiracSeparatedModeSeries coeff amplitude momentum internalMode
        (minkowskiTranslate b q.1, q.2) a =
      ∑ i, coeff i * amplitude i a *
        (finiteM8FourierMode (momentum i) (internalMode i) q *
          minkowskiPlaneWave (momentum i) b) := by
  unfold finiteDiracSeparatedModeSeries
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finiteM8FourierMode_translate]

/-- Countable separated Dirac solution series for the mode expansions in
Varlamov Eqs. 134--137. -/
noncomputable def diracSeparatedModeSeries {ι : Type*}
    (coeff : ι -> ℂ) (amplitude : ι -> DiracSpinorField)
    (momentum : ι -> MinkowskiPoint)
    (internalMode : ι -> ComplexTwoSpherePoint -> ℂ) :
    PoincareM8 -> DiracSpinorField :=
  fun q a => ∑' i, coeff i * amplitude i a *
    finiteM8FourierMode (momentum i) (internalMode i) q

/-- Varlamov Eq. 132, the radial Bessel-type residual obtained from the separated
Dirac system. -/
def diracRadialBesselResidual (ell kappaC kappaCDot z f f' f'' : ℂ) : ℂ :=
  z ^ 2 * f'' - z * f' - (ell ^ 2 - 1 - 4 * kappaC * kappaCDot * z ^ 2) * f

/-- A radial factor satisfies the separated Dirac radial equation when the residual is zero. -/
def SatisfiesDiracRadialBesselEquation
    (ell kappaC kappaCDot z f f' f'' : ℂ) : Prop :=
  diracRadialBesselResidual ell kappaC kappaCDot z f f' f'' = 0

/-- The separated radial residual is additive in a pair of radial factors. -/
lemma diracRadialBesselResidual_add
    (ell kappaC kappaCDot z f g f' g' f'' g'' : ℂ) :
    diracRadialBesselResidual ell kappaC kappaCDot z (f + g) (f' + g') (f'' + g'') =
      diracRadialBesselResidual ell kappaC kappaCDot z f f' f''
        + diracRadialBesselResidual ell kappaC kappaCDot z g g' g'' := by
  unfold diracRadialBesselResidual
  ring

/-- The separated radial residual is homogeneous in a scalar multiple of a radial factor. -/
lemma diracRadialBesselResidual_smul
    (ell kappaC kappaCDot z c f f' f'' : ℂ) :
    diracRadialBesselResidual ell kappaC kappaCDot z (c * f) (c * f') (c * f'') =
      c * diracRadialBesselResidual ell kappaC kappaCDot z f f' f'' := by
  unfold diracRadialBesselResidual
  ring

/-- Coefficient recurrence obtained by inserting a power series into Varlamov Eq. 132. -/
def DiracRadialSeriesRecurrence (ell kappaProduct : ℂ) (coeff : ℕ -> ℂ) : Prop :=
  ∀ n : ℕ, ((((n + 1 : ℕ) : ℂ) ^ 2 - ell ^ 2) * coeff (n + 2)
    + 4 * kappaProduct * coeff n = 0)

/-- The radial-series recurrence is preserved by linear combinations. -/
lemma DiracRadialSeriesRecurrence.linear_combination
    (ell kappaProduct c d : ℂ) (a b : ℕ -> ℂ)
    (ha : DiracRadialSeriesRecurrence ell kappaProduct a)
    (hb : DiracRadialSeriesRecurrence ell kappaProduct b) :
    DiracRadialSeriesRecurrence ell kappaProduct (fun n => c * a n + d * b n) := by
  unfold DiracRadialSeriesRecurrence at ha hb ⊢
  intro n
  specialize ha n
  specialize hb n
  linear_combination c * ha + d * hb

/-! ### E.2.4. Boundary-Value Problem on the Complex Two-Sphere -/

/-- The finite boundary-value data for Varlamov's relativistic Dirichlet problem on
the complex two-sphere. -/
structure VarlamovBoundaryValueProblem (μ ν : Type*) [Fintype μ] [Fintype ν] where
  /-- First-order matrices `Gamma_mu` in the field equation. -/
  Gamma : μ -> Matrix ν ν ℂ
  /-- The mass or spectral parameter `kappa`. -/
  kappa : ℂ
  /-- Radius of the complex two-sphere where boundary data are prescribed. -/
  radius : ℂ
  /-- Componentwise boundary data on the complex two-sphere. -/
  boundary : ν -> ComplexTwoSpherePoint -> ℂ

/-- A field solves the finite Varlamov boundary-value problem when it matches the
component boundary data and satisfies the first-order field equation on that boundary. -/
def SolvesVarlamovBoundaryValueProblem {μ ν : Type*} [Fintype μ] [Fintype ν]
    (P : VarlamovBoundaryValueProblem μ ν)
    (field : ν -> ℂ -> ComplexTwoSpherePoint -> ℂ)
    (dfield : ComplexTwoSpherePoint -> μ -> ν -> ℂ) : Prop :=
  MatchesComponentBoundaryData field P.boundary P.radius ∧
    ∀ z, OnComplexTwoSphere P.radius z ->
      IsVarlamovDiracLikeSolution P.Gamma P.kappa (fun a => field a P.radius z) (dfield z)

/-- Boundary trace for component fields on `M8 = R^{1,3} x S^2_C`, with the spacetime
coordinate left free along the boundary sphere. -/
def MatchesM8BoundaryData {ν : Type*}
    (field : ν -> PoincareM8 -> ℂ)
    (boundary : ν -> MinkowskiPoint -> ComplexTwoSpherePoint -> ℂ) (r : ℂ) : Prop :=
  ∀ a x z, OnComplexTwoSphere r z -> field a (x, z) = boundary a x z

/-- The finite `M8` boundary-value data from Section 7: a first-order system, a boundary
sphere, and spacetime-dependent boundary values. -/
structure VarlamovM8BoundaryValueProblem (μ ν : Type*) [Fintype μ] [Fintype ν] where
  /-- First-order matrices in the field equation. -/
  Gamma : μ -> Matrix ν ν ℂ
  /-- Mass or spectral parameter. -/
  kappa : ℂ
  /-- Radius of the complex two-sphere boundary. -/
  radius : ℂ
  /-- Region in `M8` where the bulk equation is imposed. -/
  region : PoincareM8 -> Prop
  /-- Boundary values along `R^{1,3} x S^2_C`. -/
  boundary : ν -> MinkowskiPoint -> ComplexTwoSpherePoint -> ℂ

/-- A component field solves the finite `M8` boundary-value problem when it has the
prescribed boundary trace and satisfies the first-order field equation throughout the region. -/
def SolvesVarlamovM8BoundaryValueProblem {μ ν : Type*} [Fintype μ] [Fintype ν]
    (P : VarlamovM8BoundaryValueProblem μ ν)
    (field : ν -> PoincareM8 -> ℂ)
    (dfield : PoincareM8 -> μ -> ν -> ℂ) : Prop :=
  MatchesM8BoundaryData field P.boundary P.radius ∧
    ∀ q, P.region q ->
      IsVarlamovDiracLikeSolution P.Gamma P.kappa (fun a => field a q) (dfield q)

/-- Constructor lemma for the finite `M8` boundary-value problem. -/
lemma solvesVarlamovM8BoundaryValueProblem_of_boundary_and_bulk {μ ν : Type*}
    [Fintype μ] [Fintype ν] (P : VarlamovM8BoundaryValueProblem μ ν)
    (field : ν -> PoincareM8 -> ℂ) (dfield : PoincareM8 -> μ -> ν -> ℂ)
    (hboundary : MatchesM8BoundaryData field P.boundary P.radius)
    (hbulk : ∀ q, P.region q ->
      IsVarlamovDiracLikeSolution P.Gamma P.kappa (fun a => field a q) (dfield q)) :
    SolvesVarlamovM8BoundaryValueProblem P field dfield :=
  ⟨hboundary, hbulk⟩

/-- Constructor lemma for the finite Varlamov boundary-value problem. -/
lemma solvesVarlamovBoundaryValueProblem_of_matches_and_equation {μ ν : Type*}
    [Fintype μ] [Fintype ν] (P : VarlamovBoundaryValueProblem μ ν)
    (field : ν -> ℂ -> ComplexTwoSpherePoint -> ℂ)
    (dfield : ComplexTwoSpherePoint -> μ -> ν -> ℂ)
    (hboundary : MatchesComponentBoundaryData field P.boundary P.radius)
    (heq : ∀ z, OnComplexTwoSphere P.radius z ->
      IsVarlamovDiracLikeSolution P.Gamma P.kappa (fun a => field a P.radius z) (dfield z)) :
    SolvesVarlamovBoundaryValueProblem P field dfield :=
  ⟨hboundary, heq⟩

/-- A finite component hyperspherical expansion solves the finite boundary part of
Varlamov's boundary-value problem once its coefficients have the prescribed boundary
radial values and its derivative data satisfy the first-order equation. -/
lemma finiteComponentSphereModeExpansion_solves_boundaryValueProblem
    {μ ν ι : Type*} [Fintype μ] [Fintype ν] [Fintype ι]
    (Gamma : μ -> Matrix ν ν ℂ) (kappa r : ℂ)
    (coeff boundaryRadial : ν -> ι -> ℂ) (radial : ν -> ι -> ℂ -> ℂ)
    (harmonic : ν -> ι -> ComplexTwoSpherePoint -> ℂ)
    (dfield : ComplexTwoSpherePoint -> μ -> ν -> ℂ)
    (hboundary : ∀ a j, radial a j r = boundaryRadial a j)
    (heq : ∀ z, OnComplexTwoSphere r z ->
      IsVarlamovDiracLikeSolution Gamma kappa
        (fun a => finiteComponentSphereModeExpansion coeff radial harmonic a r z)
        (dfield z)) :
    SolvesVarlamovBoundaryValueProblem
      { Gamma := Gamma, kappa := kappa, radius := r,
        boundary := finiteComponentBoundaryModeExpansion coeff boundaryRadial harmonic }
      (finiteComponentSphereModeExpansion coeff radial harmonic) dfield := by
  apply solvesVarlamovBoundaryValueProblem_of_matches_and_equation
  · exact finiteComponentSphereModeExpansion_matchesBoundaryData coeff boundaryRadial radial
      harmonic r hboundary
  · exact heq

/-! ### E.2.5. Covariance and Infinitesimal Commutator Constraints -/

/-- Matrix commutator `AB - BA` for finite component matrices. -/
def matrixCommutator {ν : Type*} [Fintype ν] (A B : Matrix ν ν ℂ) : Matrix ν ν ℂ :=
  A * B - B * A

/-- Varlamov Eq. 104: covariance of the `Lambda_i` matrices under a finite Lorentz
representation matrix and the bivector-space metric coefficients. -/
def VarlamovLambdaCovariance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (g : Fin 3 -> Fin 3 -> ℂ) (T : Matrix ν ν ℂ)
    (Lambda : Fin 3 -> Matrix ν ν ℂ) : Prop :=
  ∀ i, ∑ k, g i k • (T * Lambda k * T⁻¹) = Lambda i

/-- The identity Lorentz representation satisfies the covariance condition with the
Kronecker metric coefficients. -/
lemma VarlamovLambdaCovariance_id {ν : Type*} [Fintype ν] [DecidableEq ν]
    (Lambda : Fin 3 -> Matrix ν ν ℂ) :
    VarlamovLambdaCovariance (fun i k => if k = i then 1 else 0) 1 Lambda := by
  intro i
  simp

/-- Varlamov Eq. 105: infinitesimal rotation generators acting on the vector
`Lambda_1,Lambda_2,Lambda_3`. -/
def VarlamovRotationCommutatorRelations {ν : Type*} [Fintype ν]
    (A Lambda : Fin 3 -> Matrix ν ν ℂ) : Prop :=
  matrixCommutator (A 0) (Lambda 0) = 0 ∧
  matrixCommutator (A 0) (Lambda 1) = Lambda 2 ∧
  matrixCommutator (A 0) (Lambda 2) = -Lambda 1 ∧
  matrixCommutator (A 1) (Lambda 0) = -Lambda 2 ∧
  matrixCommutator (A 1) (Lambda 1) = 0 ∧
  matrixCommutator (A 1) (Lambda 2) = Lambda 0 ∧
  matrixCommutator (A 2) (Lambda 0) = Lambda 1 ∧
  matrixCommutator (A 2) (Lambda 1) = -Lambda 0 ∧
  matrixCommutator (A 2) (Lambda 2) = 0

/-- Varlamov Eq. 106: infinitesimal boost generators acting on the vector
`Lambda_1,Lambda_2,Lambda_3`. -/
def VarlamovBoostCommutatorRelations {ν : Type*} [Fintype ν]
    (B Lambda : Fin 3 -> Matrix ν ν ℂ) : Prop :=
  matrixCommutator (B 0) (Lambda 0) = 0 ∧
  matrixCommutator (B 0) (Lambda 1) = (-Complex.I) • Lambda 2 ∧
  matrixCommutator (B 0) (Lambda 2) = Complex.I • Lambda 1 ∧
  matrixCommutator (B 1) (Lambda 0) = Complex.I • Lambda 2 ∧
  matrixCommutator (B 1) (Lambda 1) = 0 ∧
  matrixCommutator (B 1) (Lambda 2) = (-Complex.I) • Lambda 0 ∧
  matrixCommutator (B 2) (Lambda 0) = (-Complex.I) • Lambda 1 ∧
  matrixCommutator (B 2) (Lambda 1) = Complex.I • Lambda 0 ∧
  matrixCommutator (B 2) (Lambda 2) = 0

/-- Varlamov Eqs. 107--108: the dual representation has the same rotation relations
and the opposite boost signs. -/
def VarlamovDualCommutatorRelations {ν : Type*} [Fintype ν]
    (Adual Bdual LambdaStar : Fin 3 -> Matrix ν ν ℂ) : Prop :=
  VarlamovRotationCommutatorRelations Adual LambdaStar ∧
  matrixCommutator (Bdual 0) (LambdaStar 0) = 0 ∧
  matrixCommutator (Bdual 0) (LambdaStar 1) = Complex.I • LambdaStar 2 ∧
  matrixCommutator (Bdual 0) (LambdaStar 2) = (-Complex.I) • LambdaStar 1 ∧
  matrixCommutator (Bdual 1) (LambdaStar 0) = (-Complex.I) • LambdaStar 2 ∧
  matrixCommutator (Bdual 1) (LambdaStar 1) = 0 ∧
  matrixCommutator (Bdual 1) (LambdaStar 2) = Complex.I • LambdaStar 0 ∧
  matrixCommutator (Bdual 2) (LambdaStar 0) = Complex.I • LambdaStar 1 ∧
  matrixCommutator (Bdual 2) (LambdaStar 1) = (-Complex.I) • LambdaStar 0 ∧
  matrixCommutator (Bdual 2) (LambdaStar 2) = 0

/-! ## F. QFT Field-Operator Specification -/

/-- The two field sectors used by the Poincare-group QED bridge. -/
inductive PoincareQEDField : Type where
  | dirac : PoincareQEDField
  | maxwell : PoincareQEDField
deriving DecidableEq

/-- Position labels for the Poincare-group QED sectors. -/
def poincareQEDPositionLabel : PoincareQEDField -> Type
  | PoincareQEDField.dirac => Fin 4
  | PoincareQEDField.maxwell => Fin 6

/-- Asymptotic labels for the Poincare-group QED sectors. -/
def poincareQEDAsymptoticLabel : PoincareQEDField -> Type
  | PoincareQEDField.dirac => Fin 4
  | PoincareQEDField.maxwell => Fin 2

/-- Field statistics for the Poincare-group QED sectors. -/
def poincareQEDStatistic : PoincareQEDField -> FieldStatistic
  | PoincareQEDField.dirac => FieldStatistic.fermionic
  | PoincareQEDField.maxwell => FieldStatistic.bosonic

/-- Field specification for the Dirac and Maxwell sectors in Varlamov's Poincare-group QED. -/
def poincareQEDFieldSpec : FieldSpecification where
  Field := PoincareQEDField
  PositionLabel := poincareQEDPositionLabel
  AsymptoticLabel := poincareQEDAsymptoticLabel
  statistic := poincareQEDStatistic

/-- The Dirac sector of the Poincare-group QED specification is fermionic. -/
@[simp] lemma poincareQEDStatistic_dirac :
    poincareQEDFieldSpec.statistic PoincareQEDField.dirac = FieldStatistic.fermionic :=
  rfl

/-- The Maxwell sector of the Poincare-group QED specification is bosonic. -/
@[simp] lemma poincareQEDStatistic_maxwell :
    poincareQEDFieldSpec.statistic PoincareQEDField.maxwell = FieldStatistic.bosonic :=
  rfl

/-- Dirac position field operator in the shared QFT field-operator API. -/
def diracPositionFieldOp (a : Fin 4) (x : SpaceTime) : poincareQEDFieldSpec.FieldOp :=
  FieldOp.position (⟨PoincareQEDField.dirac, a⟩, x)

/-- Maxwell position field operator in the shared QFT field-operator API. -/
def maxwellPositionFieldOp (a : Fin 6) (x : SpaceTime) : poincareQEDFieldSpec.FieldOp :=
  FieldOp.position (⟨PoincareQEDField.maxwell, a⟩, x)

/-- Incoming Dirac asymptotic operator in the shared QFT field-operator API. -/
def diracIncomingFieldOp (s : Fin 4) (p : Momentum 3) : poincareQEDFieldSpec.FieldOp :=
  FieldOp.inAsymp (⟨PoincareQEDField.dirac, s⟩, p)

/-- Outgoing Dirac asymptotic operator in the shared QFT field-operator API. -/
def diracOutgoingFieldOp (s : Fin 4) (p : Momentum 3) : poincareQEDFieldSpec.FieldOp :=
  FieldOp.outAsymp (⟨PoincareQEDField.dirac, s⟩, p)

/-- Outgoing Maxwell asymptotic operator in the shared QFT field-operator API. -/
def maxwellOutgoingFieldOp (h : Fin 2) (p : Momentum 3) : poincareQEDFieldSpec.FieldOp :=
  FieldOp.outAsymp (⟨PoincareQEDField.maxwell, h⟩, p)

/-- Incoming Maxwell asymptotic operator in the shared QFT field-operator API. -/
def maxwellIncomingFieldOp (h : Fin 2) (p : Momentum 3) : poincareQEDFieldSpec.FieldOp :=
  FieldOp.inAsymp (⟨PoincareQEDField.maxwell, h⟩, p)

/-- A Dirac position field operator has fermionic statistics. -/
@[simp] lemma diracPositionFieldOp_statistic (a : Fin 4) (x : SpaceTime) :
    fieldOpStatistic poincareQEDFieldSpec (diracPositionFieldOp a x) = FieldStatistic.fermionic :=
  rfl

/-- A Maxwell position field operator has bosonic statistics. -/
@[simp] lemma maxwellPositionFieldOp_statistic (a : Fin 6) (x : SpaceTime) :
    fieldOpStatistic poincareQEDFieldSpec (maxwellPositionFieldOp a x) = FieldStatistic.bosonic :=
  rfl

/-- An incoming Dirac asymptotic operator has fermionic statistics. -/
@[simp] lemma diracIncomingFieldOp_statistic (s : Fin 4) (p : Momentum 3) :
    fieldOpStatistic poincareQEDFieldSpec (diracIncomingFieldOp s p) = FieldStatistic.fermionic :=
  rfl

/-- An outgoing Dirac asymptotic operator has fermionic statistics. -/
@[simp] lemma diracOutgoingFieldOp_statistic (s : Fin 4) (p : Momentum 3) :
    fieldOpStatistic poincareQEDFieldSpec (diracOutgoingFieldOp s p) = FieldStatistic.fermionic :=
  rfl

/-- An outgoing Maxwell asymptotic operator has bosonic statistics. -/
@[simp] lemma maxwellOutgoingFieldOp_statistic (h : Fin 2) (p : Momentum 3) :
    fieldOpStatistic poincareQEDFieldSpec (maxwellOutgoingFieldOp h p) = FieldStatistic.bosonic :=
  rfl

/-- An incoming Maxwell asymptotic operator has bosonic statistics. -/
@[simp] lemma maxwellIncomingFieldOp_statistic (h : Fin 2) (p : Momentum 3) :
    fieldOpStatistic poincareQEDFieldSpec (maxwellIncomingFieldOp h p) = FieldStatistic.bosonic :=
  rfl

/-- Varlamov's field-operator layer uses the existing creation/annihilation splitting. -/
lemma poincareQEDFieldOp_eq_create_add_annihilate (φ : poincareQEDFieldSpec.FieldOp) :
    ofFieldOpF φ = crPartF φ + anPartF φ :=
  ofFieldOpF_eq_crPartF_add_anPartF φ

/-- Dirac position operators split into creation and annihilation parts in the shared API. -/
lemma diracPositionFieldOp_eq_create_add_annihilate (a : Fin 4) (x : SpaceTime) :
    ofFieldOpF (diracPositionFieldOp a x) =
      crPartF (diracPositionFieldOp a x) + anPartF (diracPositionFieldOp a x) :=
  poincareQEDFieldOp_eq_create_add_annihilate (diracPositionFieldOp a x)

/-- Maxwell position operators split into creation and annihilation parts in the shared API. -/
lemma maxwellPositionFieldOp_eq_create_add_annihilate (a : Fin 6) (x : SpaceTime) :
    ofFieldOpF (maxwellPositionFieldOp a x) =
      crPartF (maxwellPositionFieldOp a x) + anPartF (maxwellPositionFieldOp a x) :=
  poincareQEDFieldOp_eq_create_add_annihilate (maxwellPositionFieldOp a x)

/-- Incoming Dirac asymptotic operators have no annihilation part in the shared API. -/
@[simp] lemma diracIncomingFieldOp_annihilation_part (s : Fin 4) (p : Momentum 3) :
    anPartF (diracIncomingFieldOp s p) = 0 := by
  simp [diracIncomingFieldOp]

/-- Incoming Dirac asymptotic operators are their creation parts in the shared API. -/
lemma diracIncomingFieldOp_eq_creation_part (s : Fin 4) (p : Momentum 3) :
    ofFieldOpF (diracIncomingFieldOp s p) = crPartF (diracIncomingFieldOp s p) := by
  rw [poincareQEDFieldOp_eq_create_add_annihilate, diracIncomingFieldOp_annihilation_part,
    add_zero]

/-- Outgoing Dirac asymptotic operators have no creation part in the shared API. -/
@[simp] lemma diracOutgoingFieldOp_creation_part (s : Fin 4) (p : Momentum 3) :
    crPartF (diracOutgoingFieldOp s p) = 0 := by
  simp [diracOutgoingFieldOp]

/-- Outgoing Dirac asymptotic operators are their annihilation parts in the shared API. -/
lemma diracOutgoingFieldOp_eq_annihilation_part (s : Fin 4) (p : Momentum 3) :
    ofFieldOpF (diracOutgoingFieldOp s p) = anPartF (diracOutgoingFieldOp s p) := by
  rw [poincareQEDFieldOp_eq_create_add_annihilate, diracOutgoingFieldOp_creation_part,
    zero_add]

/-- Outgoing Maxwell asymptotic operators have no creation part in the shared API. -/
@[simp] lemma maxwellOutgoingFieldOp_creation_part (h : Fin 2) (p : Momentum 3) :
    crPartF (maxwellOutgoingFieldOp h p) = 0 := by
  simp [maxwellOutgoingFieldOp]

/-- Outgoing Maxwell asymptotic operators are their annihilation parts in the shared API. -/
lemma maxwellOutgoingFieldOp_eq_annihilation_part (h : Fin 2) (p : Momentum 3) :
    ofFieldOpF (maxwellOutgoingFieldOp h p) = anPartF (maxwellOutgoingFieldOp h p) := by
  rw [poincareQEDFieldOp_eq_create_add_annihilate, maxwellOutgoingFieldOp_creation_part,
    zero_add]

/-- Incoming Maxwell asymptotic operators have no annihilation part in the shared API. -/
@[simp] lemma maxwellIncomingFieldOp_annihilation_part (h : Fin 2) (p : Momentum 3) :
    anPartF (maxwellIncomingFieldOp h p) = 0 := by
  simp [maxwellIncomingFieldOp]

/-- Incoming Maxwell asymptotic operators are their creation parts in the shared API. -/
lemma maxwellIncomingFieldOp_eq_creation_part (h : Fin 2) (p : Momentum 3) :
    ofFieldOpF (maxwellIncomingFieldOp h p) = crPartF (maxwellIncomingFieldOp h p) := by
  rw [poincareQEDFieldOp_eq_create_add_annihilate, maxwellIncomingFieldOp_annihilation_part,
    add_zero]

/-- A finite truncation of the incoming Dirac mode expansion in Eq. 141. -/
noncomputable def finiteDiracIncomingModeOperator {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ∑ i, coeff i • ofFieldOpF (diracIncomingFieldOp (spin i) (mom i))

/-- A finite truncation of the outgoing Maxwell mode expansion in Eq. 173. -/
noncomputable def finiteMaxwellOutgoingModeOperator {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ∑ i, coeff i • ofFieldOpF (maxwellOutgoingFieldOp (helicity i) (mom i))

/-- A finite truncation of the incoming Maxwell creation-mode expansion in Eq. 173. -/
noncomputable def finiteMaxwellIncomingModeOperator {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ∑ i, coeff i • ofFieldOpF (maxwellIncomingFieldOp (helicity i) (mom i))

/-- A finite truncation of the outgoing Dirac antimode expansion in Eq. 141. -/
noncomputable def finiteDiracOutgoingModeOperator {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ∑ i, coeff i • ofFieldOpF (diracOutgoingFieldOp (spin i) (mom i))

/-- A finite electron/positron split of the Dirac field expansion in Eq. 141. -/
noncomputable def finiteDiracElectronPositronModeOperator {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (electronCoeff : ι -> ℂ) (electronSpin : ι -> Fin 4) (electronMom : ι -> Momentum 3)
    (positronCoeff : κ -> ℂ) (positronSpin : κ -> Fin 4) (positronMom : κ -> Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finiteDiracIncomingModeOperator electronCoeff electronSpin electronMom
    + finiteDiracOutgoingModeOperator positronCoeff positronSpin positronMom

/-- The finite incoming Dirac mode expansion lies in the creation part. -/
lemma finiteDiracIncomingModeOperator_eq_creation_sum {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    finiteDiracIncomingModeOperator coeff spin mom =
      ∑ i, coeff i • crPartF (diracIncomingFieldOp (spin i) (mom i)) := by
  simp [finiteDiracIncomingModeOperator, diracIncomingFieldOp_eq_creation_part]

/-- The finite outgoing Dirac antimode expansion lies in the annihilation part. -/
lemma finiteDiracOutgoingModeOperator_eq_annihilation_sum {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    finiteDiracOutgoingModeOperator coeff spin mom =
      ∑ i, coeff i • anPartF (diracOutgoingFieldOp (spin i) (mom i)) := by
  simp [finiteDiracOutgoingModeOperator, diracOutgoingFieldOp_eq_annihilation_part]

/-- The finite Dirac field split is the sum of its electron creation and positron
annihilation parts. -/
lemma finiteDiracElectronPositronModeOperator_eq_creation_add_annihilation {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (electronCoeff : ι -> ℂ) (electronSpin : ι -> Fin 4) (electronMom : ι -> Momentum 3)
    (positronCoeff : κ -> ℂ) (positronSpin : κ -> Fin 4) (positronMom : κ -> Momentum 3) :
    finiteDiracElectronPositronModeOperator electronCoeff electronSpin electronMom
        positronCoeff positronSpin positronMom =
      (∑ i, electronCoeff i • crPartF (diracIncomingFieldOp (electronSpin i) (electronMom i)))
        + ∑ j, positronCoeff j • anPartF (diracOutgoingFieldOp (positronSpin j)
          (positronMom j)) := by
  simp [finiteDiracElectronPositronModeOperator,
    finiteDiracIncomingModeOperator_eq_creation_sum,
    finiteDiracOutgoingModeOperator_eq_annihilation_sum]

/-- The finite outgoing Maxwell mode expansion lies in the annihilation part. -/
lemma finiteMaxwellOutgoingModeOperator_eq_annihilation_sum {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    finiteMaxwellOutgoingModeOperator coeff helicity mom =
      ∑ i, coeff i • anPartF (maxwellOutgoingFieldOp (helicity i) (mom i)) := by
  simp [finiteMaxwellOutgoingModeOperator, maxwellOutgoingFieldOp_eq_annihilation_part]

/-- The finite incoming Maxwell mode expansion lies in the creation part. -/
lemma finiteMaxwellIncomingModeOperator_eq_creation_sum {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    finiteMaxwellIncomingModeOperator coeff helicity mom =
      ∑ i, coeff i • crPartF (maxwellIncomingFieldOp (helicity i) (mom i)) := by
  simp [finiteMaxwellIncomingModeOperator, maxwellIncomingFieldOp_eq_creation_part]

/-- Finite photon field operator from Eq. 173: annihilation modes plus creation modes. -/
noncomputable def finitePhotonModeOperator {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (annCoeff : ι -> ℂ) (annHelicity : ι -> Fin 2) (annMom : ι -> Momentum 3)
    (creCoeff : κ -> ℂ) (creHelicity : κ -> Fin 2) (creMom : κ -> Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finiteMaxwellOutgoingModeOperator annCoeff annHelicity annMom
    + finiteMaxwellIncomingModeOperator creCoeff creHelicity creMom

/-- The finite photon expansion is the sum of annihilation and creation parts. -/
lemma finitePhotonModeOperator_eq_annihilation_add_creation {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (annCoeff : ι -> ℂ) (annHelicity : ι -> Fin 2) (annMom : ι -> Momentum 3)
    (creCoeff : κ -> ℂ) (creHelicity : κ -> Fin 2) (creMom : κ -> Momentum 3) :
    finitePhotonModeOperator annCoeff annHelicity annMom creCoeff creHelicity creMom =
      (∑ i, annCoeff i • anPartF (maxwellOutgoingFieldOp (annHelicity i) (annMom i)))
        + ∑ j, creCoeff j • crPartF (maxwellIncomingFieldOp (creHelicity j)
          (creMom j)) := by
  simp [finitePhotonModeOperator, finiteMaxwellOutgoingModeOperator_eq_annihilation_sum,
    finiteMaxwellIncomingModeOperator_eq_creation_sum]

/-- The Poincare-group field-operator product uses the existing supercommutator formula. -/
lemma poincareQED_superCommute_ofFieldOpF (φ ψ : poincareQEDFieldSpec.FieldOp) :
    superCommuteF (ofFieldOpF φ) (ofFieldOpF ψ) =
      ofFieldOpF φ * ofFieldOpF ψ
        - FieldStatistic.exchangeSign (fieldOpStatistic poincareQEDFieldSpec φ)
            (fieldOpStatistic poincareQEDFieldSpec ψ) • ofFieldOpF ψ * ofFieldOpF φ := by
  rw [← ofFieldOpListF_singleton ψ]
  simpa using
    (superCommuteF_ofFieldOpF_ofFieldOpFsList (𝓕 := poincareQEDFieldSpec) φ [ψ])

/-- Two Dirac position operators use the fermionic sign in the shared supercommutator. -/
lemma diracPosition_superCommute_ofFieldOpF (a b : Fin 4) (x y : SpaceTime) :
    superCommuteF (ofFieldOpF (diracPositionFieldOp a x))
        (ofFieldOpF (diracPositionFieldOp b y)) =
      ofFieldOpF (diracPositionFieldOp a x) * ofFieldOpF (diracPositionFieldOp b y)
        - FieldStatistic.exchangeSign FieldStatistic.fermionic FieldStatistic.fermionic •
          ofFieldOpF (diracPositionFieldOp b y) * ofFieldOpF (diracPositionFieldOp a x) := by
  simpa only [diracPositionFieldOp_statistic] using poincareQED_superCommute_ofFieldOpF
    (diracPositionFieldOp a x) (diracPositionFieldOp b y)

/-- Incoming Dirac asymptotic operators use the fermionic anticommutator sign. -/
lemma diracIncoming_superCommute_ofFieldOpF (s t : Fin 4) (p q : Momentum 3) :
    superCommuteF (ofFieldOpF (diracIncomingFieldOp s p))
        (ofFieldOpF (diracIncomingFieldOp t q)) =
      ofFieldOpF (diracIncomingFieldOp s p) * ofFieldOpF (diracIncomingFieldOp t q)
        + ofFieldOpF (diracIncomingFieldOp t q) * ofFieldOpF (diracIncomingFieldOp s p) := by
  simpa [diracIncomingFieldOp_statistic, FieldStatistic.fermionic_exchangeSign_fermionic]
    using poincareQED_superCommute_ofFieldOpF
      (diracIncomingFieldOp s p) (diracIncomingFieldOp t q)

/-- Outgoing Dirac asymptotic operators use the fermionic anticommutator sign. -/
lemma diracOutgoing_superCommute_ofFieldOpF (s t : Fin 4) (p q : Momentum 3) :
    superCommuteF (ofFieldOpF (diracOutgoingFieldOp s p))
        (ofFieldOpF (diracOutgoingFieldOp t q)) =
      ofFieldOpF (diracOutgoingFieldOp s p) * ofFieldOpF (diracOutgoingFieldOp t q)
        + ofFieldOpF (diracOutgoingFieldOp t q) * ofFieldOpF (diracOutgoingFieldOp s p) := by
  simpa [diracOutgoingFieldOp_statistic, FieldStatistic.fermionic_exchangeSign_fermionic]
    using poincareQED_superCommute_ofFieldOpF
      (diracOutgoingFieldOp s p) (diracOutgoingFieldOp t q)

/-- Outgoing and incoming Dirac asymptotic operators use the fermionic CAR sign. -/
lemma diracOutgoingIncoming_superCommute_ofFieldOpF (s t : Fin 4) (p q : Momentum 3) :
    superCommuteF (ofFieldOpF (diracOutgoingFieldOp s p))
        (ofFieldOpF (diracIncomingFieldOp t q)) =
      ofFieldOpF (diracOutgoingFieldOp s p) * ofFieldOpF (diracIncomingFieldOp t q)
        + ofFieldOpF (diracIncomingFieldOp t q) * ofFieldOpF (diracOutgoingFieldOp s p) := by
  simpa [diracOutgoingFieldOp_statistic, diracIncomingFieldOp_statistic,
    FieldStatistic.fermionic_exchangeSign_fermionic] using
      poincareQED_superCommute_ofFieldOpF
        (diracOutgoingFieldOp s p) (diracIncomingFieldOp t q)

/-- Outgoing Maxwell asymptotic operators use the bosonic commutator sign. -/
lemma maxwellOutgoing_superCommute_ofFieldOpF (h k : Fin 2) (p q : Momentum 3) :
    superCommuteF (ofFieldOpF (maxwellOutgoingFieldOp h p))
        (ofFieldOpF (maxwellOutgoingFieldOp k q)) =
      ofFieldOpF (maxwellOutgoingFieldOp h p) * ofFieldOpF (maxwellOutgoingFieldOp k q)
        - ofFieldOpF (maxwellOutgoingFieldOp k q) * ofFieldOpF (maxwellOutgoingFieldOp h p) := by
  simpa [maxwellOutgoingFieldOp_statistic, FieldStatistic.exchangeSign_bosonic]
    using poincareQED_superCommute_ofFieldOpF
      (maxwellOutgoingFieldOp h p) (maxwellOutgoingFieldOp k q)

/-- Incoming Maxwell asymptotic operators use the bosonic commutator sign. -/
lemma maxwellIncoming_superCommute_ofFieldOpF (h k : Fin 2) (p q : Momentum 3) :
    superCommuteF (ofFieldOpF (maxwellIncomingFieldOp h p))
        (ofFieldOpF (maxwellIncomingFieldOp k q)) =
      ofFieldOpF (maxwellIncomingFieldOp h p) * ofFieldOpF (maxwellIncomingFieldOp k q)
        - ofFieldOpF (maxwellIncomingFieldOp k q) * ofFieldOpF (maxwellIncomingFieldOp h p) := by
  simpa [maxwellIncomingFieldOp_statistic, FieldStatistic.exchangeSign_bosonic]
    using poincareQED_superCommute_ofFieldOpF
      (maxwellIncomingFieldOp h p) (maxwellIncomingFieldOp k q)

/-- Outgoing and incoming Maxwell asymptotic operators use the bosonic CCR sign. -/
lemma maxwellOutgoingIncoming_superCommute_ofFieldOpF (h k : Fin 2) (p q : Momentum 3) :
    superCommuteF (ofFieldOpF (maxwellOutgoingFieldOp h p))
        (ofFieldOpF (maxwellIncomingFieldOp k q)) =
      ofFieldOpF (maxwellOutgoingFieldOp h p) * ofFieldOpF (maxwellIncomingFieldOp k q)
        - ofFieldOpF (maxwellIncomingFieldOp k q) * ofFieldOpF (maxwellOutgoingFieldOp h p) := by
  simpa [maxwellOutgoingFieldOp_statistic, maxwellIncomingFieldOp_statistic,
    FieldStatistic.exchangeSign_bosonic] using
      poincareQED_superCommute_ofFieldOpF
        (maxwellOutgoingFieldOp h p) (maxwellIncomingFieldOp k q)

/-- A Dirac and Maxwell position operator use the mixed fermion-boson sign. -/
lemma diracMaxwell_superCommute_ofFieldOpF (a : Fin 4) (b : Fin 6) (x y : SpaceTime) :
    superCommuteF (ofFieldOpF (diracPositionFieldOp a x))
        (ofFieldOpF (maxwellPositionFieldOp b y)) =
      ofFieldOpF (diracPositionFieldOp a x) * ofFieldOpF (maxwellPositionFieldOp b y)
        - FieldStatistic.exchangeSign FieldStatistic.fermionic FieldStatistic.bosonic •
          ofFieldOpF (maxwellPositionFieldOp b y) * ofFieldOpF (diracPositionFieldOp a x) := by
  simpa only [diracPositionFieldOp_statistic, maxwellPositionFieldOp_statistic] using
    poincareQED_superCommute_ofFieldOpF
    (diracPositionFieldOp a x) (maxwellPositionFieldOp b y)

/-- Ordered Poincare-group field operators are fixed by the existing time-ordering map. -/
lemma poincareQED_timeOrder_ofFieldOpF_ordered
    {φ ψ : poincareQEDFieldSpec.FieldOp} (h : timeOrderRel φ ψ) :
    timeOrderF (ofFieldOpF φ * ofFieldOpF ψ) = ofFieldOpF φ * ofFieldOpF ψ :=
  timeOrderF_ofFieldOpF_ofFieldOpF_ordered h

/-- Non-ordered Poincare-group field operators are exchanged with the existing statistics sign. -/
lemma poincareQED_timeOrder_ofFieldOpF_not_ordered
    {φ ψ : poincareQEDFieldSpec.FieldOp} (h : ¬ timeOrderRel φ ψ) :
    timeOrderF (ofFieldOpF φ * ofFieldOpF ψ) =
      FieldStatistic.exchangeSign (fieldOpStatistic poincareQEDFieldSpec φ)
        (fieldOpStatistic poincareQEDFieldSpec ψ) • ofFieldOpF ψ * ofFieldOpF φ := by
  simpa using timeOrderF_ofFieldOpF_ofFieldOpF_not_ordered h

/-- Time-ordering fixes a single Poincare-group field operator. -/
lemma poincareQED_timeOrder_ofFieldOpF_singleton (φ : poincareQEDFieldSpec.FieldOp) :
    timeOrderF (ofFieldOpF φ) = ofFieldOpF φ := by
  simpa [ofFieldOpListF_singleton] using
    (timeOrderF_ofFieldOpListF_singleton (𝓕 := poincareQEDFieldSpec) φ)

/-- Time-ordering fixes a finite incoming Dirac creation-mode sum termwise. -/
lemma timeOrderF_finiteDiracIncomingModeOperator {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    timeOrderF (finiteDiracIncomingModeOperator coeff spin mom) =
      finiteDiracIncomingModeOperator coeff spin mom := by
  unfold finiteDiracIncomingModeOperator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, poincareQED_timeOrder_ofFieldOpF_singleton]

/-- Time-ordering fixes a finite outgoing Dirac annihilation-mode sum termwise. -/
lemma timeOrderF_finiteDiracOutgoingModeOperator {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    timeOrderF (finiteDiracOutgoingModeOperator coeff spin mom) =
      finiteDiracOutgoingModeOperator coeff spin mom := by
  unfold finiteDiracOutgoingModeOperator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, poincareQED_timeOrder_ofFieldOpF_singleton]

/-- Time-ordering fixes a finite outgoing photon annihilation-mode sum termwise. -/
lemma timeOrderF_finiteMaxwellOutgoingModeOperator {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    timeOrderF (finiteMaxwellOutgoingModeOperator coeff helicity mom) =
      finiteMaxwellOutgoingModeOperator coeff helicity mom := by
  unfold finiteMaxwellOutgoingModeOperator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, poincareQED_timeOrder_ofFieldOpF_singleton]

/-- Time-ordering fixes a finite incoming photon creation-mode sum termwise. -/
lemma timeOrderF_finiteMaxwellIncomingModeOperator {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    timeOrderF (finiteMaxwellIncomingModeOperator coeff helicity mom) =
      finiteMaxwellIncomingModeOperator coeff helicity mom := by
  unfold finiteMaxwellIncomingModeOperator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, poincareQED_timeOrder_ofFieldOpF_singleton]

/-! ## F.1. Normal Products and Time Contractions -/

/-- Varlamov's relation `T(AB) = N(AB) + contraction(A,B)` is the existing Wick-algebra
definition of `timeContract`, specialized to the Poincare-group QED field specification. -/
lemma poincareQED_timeOrder_eq_normalOrder_add_timeContract
    (φ ψ : poincareQEDFieldSpec.FieldOp) :
    WickAlgebra.timeOrder (WickAlgebra.ofFieldOp φ * WickAlgebra.ofFieldOp ψ) =
      WickAlgebra.normalOrder (WickAlgebra.ofFieldOp φ * WickAlgebra.ofFieldOp ψ)
        + WickAlgebra.timeContract φ ψ := by
  unfold WickAlgebra.timeContract
  abel

/-- Dirac two-point time contractions are central in the shared Wick algebra. -/
lemma diracPosition_timeContract_mem_center (a b : Fin 4) (x y : SpaceTime) :
    WickAlgebra.timeContract (diracPositionFieldOp a x) (diracPositionFieldOp b y) ∈
      Subalgebra.center ℂ poincareQEDFieldSpec.WickAlgebra :=
  WickAlgebra.timeContract_mem_center (diracPositionFieldOp a x) (diracPositionFieldOp b y)

/-- Maxwell two-point time contractions are central in the shared Wick algebra. -/
lemma maxwellPosition_timeContract_mem_center (a b : Fin 6) (x y : SpaceTime) :
    WickAlgebra.timeContract (maxwellPositionFieldOp a x) (maxwellPositionFieldOp b y) ∈
      Subalgebra.center ℂ poincareQEDFieldSpec.WickAlgebra :=
  WickAlgebra.timeContract_mem_center (maxwellPositionFieldOp a x) (maxwellPositionFieldOp b y)

/-- A free Dirac field and a free Maxwell field have zero mixed Wick contraction because their
statistics differ. The interaction is supplied by the Pauli/Faraday coupling, not by a free
two-point contraction. -/
lemma diracMaxwell_timeContract_zero (a : Fin 4) (b : Fin 6) (x y : SpaceTime) :
    WickAlgebra.timeContract (diracPositionFieldOp a x) (maxwellPositionFieldOp b y) = 0 := by
  apply WickAlgebra.timeContract_zero_of_diff_grade
  simp [diracPositionFieldOp_statistic, maxwellPositionFieldOp_statistic]

/-- Incoming Dirac asymptotic operators have zero incoming-incoming Wick contraction. -/
lemma diracIncoming_timeContract_incoming_zero (s t : Fin 4) (p q : Momentum 3) :
    WickAlgebra.timeContract (diracIncomingFieldOp s p) (diracIncomingFieldOp t q) = 0 := by
  simpa [diracIncomingFieldOp] using
    (WickAlgebra.timeContract_inAsymp_inAsymp
      (𝓕 := poincareQEDFieldSpec)
      (⟨PoincareQEDField.dirac, s⟩, p)
      (⟨PoincareQEDField.dirac, t⟩, q))

/-- Outgoing Dirac asymptotic operators have zero outgoing-outgoing Wick contraction. -/
lemma diracOutgoing_timeContract_outgoing_zero (s t : Fin 4) (p q : Momentum 3) :
    WickAlgebra.timeContract (diracOutgoingFieldOp s p) (diracOutgoingFieldOp t q) = 0 := by
  simpa [diracOutgoingFieldOp] using
    (WickAlgebra.timeContract_outAsymp_outAsymp
      (𝓕 := poincareQEDFieldSpec)
      (⟨PoincareQEDField.dirac, s⟩, p)
      (⟨PoincareQEDField.dirac, t⟩, q))

/-- Outgoing Maxwell asymptotic operators have zero outgoing-outgoing Wick contraction. -/
lemma maxwellOutgoing_timeContract_outgoing_zero (h k : Fin 2) (p q : Momentum 3) :
    WickAlgebra.timeContract (maxwellOutgoingFieldOp h p) (maxwellOutgoingFieldOp k q) = 0 := by
  simpa [maxwellOutgoingFieldOp] using
    (WickAlgebra.timeContract_outAsymp_outAsymp
      (𝓕 := poincareQEDFieldSpec)
      (⟨PoincareQEDField.maxwell, h⟩, p)
      (⟨PoincareQEDField.maxwell, k⟩, q))

/-- Incoming Maxwell asymptotic operators have zero incoming-incoming Wick contraction. -/
lemma maxwellIncoming_timeContract_incoming_zero (h k : Fin 2) (p q : Momentum 3) :
    WickAlgebra.timeContract (maxwellIncomingFieldOp h p) (maxwellIncomingFieldOp k q) = 0 := by
  simpa [maxwellIncomingFieldOp] using
    (WickAlgebra.timeContract_inAsymp_inAsymp
      (𝓕 := poincareQEDFieldSpec)
      (⟨PoincareQEDField.maxwell, h⟩, p)
      (⟨PoincareQEDField.maxwell, k⟩, q))

/-! ## F.2. Section 8.1 CAR Kernels and Infinite Mode Series -/

/-- Vacuum two-point function for Dirac position fields, expressed as the existing
Wick time contraction. -/
noncomputable def diracVacuumTwoPointFunction (a b : Fin 4) (x y : SpaceTime) :
    poincareQEDFieldSpec.WickAlgebra :=
  WickAlgebra.timeContract (diracPositionFieldOp a x) (diracPositionFieldOp b y)

/-- The Dirac vacuum two-point function is a central Wick-algebra element. -/
lemma diracVacuumTwoPointFunction_mem_center (a b : Fin 4) (x y : SpaceTime) :
    diracVacuumTwoPointFunction a b x y ∈
      Subalgebra.center ℂ poincareQEDFieldSpec.WickAlgebra := by
  simpa [diracVacuumTwoPointFunction] using
    diracPosition_timeContract_mem_center a b x y

/-- A Wick-algebra-valued CAR distribution kernel for the Dirac field. -/
def DiracCARKernelRelation
    (kernel : Fin 4 -> Fin 4 -> SpaceTime -> SpaceTime -> poincareQEDFieldSpec.WickAlgebra) :
    Prop :=
  ∀ a b x y,
    WickAlgebra.timeContract (diracPositionFieldOp a x) (diracPositionFieldOp b y) =
      kernel a b x y

/-- The vacuum two-point function realizes the Dirac CAR kernel relation. -/
lemma diracVacuumTwoPointFunction_realizes_CAR_kernel :
    DiracCARKernelRelation diracVacuumTwoPointFunction := by
  intro a b x y
  rfl

/-- Operator-valued Dirac CAR kernel, represented by the fermionic supercommutator. -/
noncomputable def diracCAROperatorKernel (a b : Fin 4) (x y : SpaceTime) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  superCommuteF (ofFieldOpF (diracPositionFieldOp a x))
    (ofFieldOpF (diracPositionFieldOp b y))

/-- The Dirac CAR kernel is exactly the shared fermionic supercommutator. -/
lemma diracCAROperatorKernel_eq_superCommute (a b : Fin 4) (x y : SpaceTime) :
    diracCAROperatorKernel a b x y =
      superCommuteF (ofFieldOpF (diracPositionFieldOp a x))
        (ofFieldOpF (diracPositionFieldOp b y)) := rfl

/-- Asymptotic Dirac CAR kernel, represented by the outgoing-incoming fermionic
anticommutator from the second-quantized field algebra. -/
noncomputable def diracAsymptoticCAROperatorKernel (s t : Fin 4) (p q : Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  superCommuteF (ofFieldOpF (diracOutgoingFieldOp s p))
    (ofFieldOpF (diracIncomingFieldOp t q))

/-- Dirac asymptotic CAR kernels are specified by the outgoing-incoming
fermionic supercommutator. -/
def DiracAsymptoticCARKernelRelation
    (kernel : Fin 4 -> Fin 4 -> Momentum 3 -> Momentum 3 ->
      poincareQEDFieldSpec.FieldOpFreeAlgebra) : Prop :=
  ∀ s t p q,
    superCommuteF (ofFieldOpF (diracOutgoingFieldOp s p))
      (ofFieldOpF (diracIncomingFieldOp t q)) = kernel s t p q

/-- The defined Dirac asymptotic CAR kernel realizes the CAR-kernel relation. -/
lemma diracAsymptoticCAROperatorKernel_realizes_CAR :
    DiracAsymptoticCARKernelRelation diracAsymptoticCAROperatorKernel := by
  intro s t p q
  rfl

/-- Component expression for the Dirac asymptotic CAR kernel. -/
lemma diracAsymptoticCAROperatorKernel_eq_anticommutator
    (s t : Fin 4) (p q : Momentum 3) :
    diracAsymptoticCAROperatorKernel s t p q =
      ofFieldOpF (diracOutgoingFieldOp s p) * ofFieldOpF (diracIncomingFieldOp t q)
        + ofFieldOpF (diracIncomingFieldOp t q) * ofFieldOpF (diracOutgoingFieldOp s p) := by
  rw [diracAsymptoticCAROperatorKernel, diracOutgoingIncoming_superCommute_ofFieldOpF]

/-- Countable `M8` Dirac mode expansion with spinor-valued modes. -/
noncomputable def diracFieldModeSeriesM8 {ι : Type*}
    (coeff : ι -> ℂ) (mode : ι -> PoincareM8 -> DiracSpinorField) :
    PoincareM8 -> DiracSpinorField :=
  fun q a => ∑' i, coeff i * mode i q a

/-- The separated mode series is the `M8` mode series with Fourier-mode basis
functions. -/
lemma diracSeparatedModeSeries_eq_fieldModeSeriesM8 {ι : Type*}
    (coeff : ι -> ℂ) (amplitude : ι -> DiracSpinorField)
    (momentum : ι -> MinkowskiPoint)
    (internalMode : ι -> ComplexTwoSpherePoint -> ℂ) :
    diracSeparatedModeSeries coeff amplitude momentum internalMode =
      diracFieldModeSeriesM8 coeff
        (fun i q a => amplitude i a * finiteM8FourierMode (momentum i) (internalMode i) q) := by
  funext q a
  unfold diracSeparatedModeSeries diracFieldModeSeriesM8
  apply tsum_congr
  intro i
  ring

/-- Positive-frequency c-number kernel `S_plus` from a mode family on `M8`. -/
noncomputable def diracPositiveFrequencyKernel {ι : Type*}
    (u uBar : ι -> PoincareM8 -> DiracSpinorField)
    (a b : DiracSpinorIndex) (q q' : PoincareM8) : ℂ :=
  ∑' i, u i q a * uBar i q' b

/-- Finite form of the positive-frequency Dirac kernel. -/
lemma diracPositiveFrequencyKernel_fintype {ι : Type*} [Fintype ι]
    (u uBar : ι -> PoincareM8 -> DiracSpinorField)
    (a b : DiracSpinorIndex) (q q' : PoincareM8) :
    diracPositiveFrequencyKernel u uBar a b q q' =
      ∑ i, u i q a * uBar i q' b := by
  simp [diracPositiveFrequencyKernel]

/-- Negative-frequency c-number kernel `S_minus` from a mode family on `M8`. -/
noncomputable def diracNegativeFrequencyKernel {ι : Type*}
    (v vBar : ι -> PoincareM8 -> DiracSpinorField)
    (a b : DiracSpinorIndex) (q q' : PoincareM8) : ℂ :=
  ∑' i, v i q a * vBar i q' b

/-- Finite form of the negative-frequency Dirac kernel. -/
lemma diracNegativeFrequencyKernel_fintype {ι : Type*} [Fintype ι]
    (v vBar : ι -> PoincareM8 -> DiracSpinorField)
    (a b : DiracSpinorIndex) (q q' : PoincareM8) :
    diracNegativeFrequencyKernel v vBar a b q q' =
      ∑ i, v i q a * vBar i q' b := by
  simp [diracNegativeFrequencyKernel]

/-- The Dirac distribution kernel is the sum `S_plus + S_minus` from Varlamov Eq. 143. -/
noncomputable def diracDistributionKernel {ι κ : Type*}
    (u uBar : ι -> PoincareM8 -> DiracSpinorField)
    (v vBar : κ -> PoincareM8 -> DiracSpinorField)
    (a b : DiracSpinorIndex) (q q' : PoincareM8) : ℂ :=
  diracPositiveFrequencyKernel u uBar a b q q'
    + diracNegativeFrequencyKernel v vBar a b q q'

/-- The distribution kernel decomposes into its positive- and negative-frequency parts. -/
lemma diracDistributionKernel_eq_positive_add_negative {ι κ : Type*}
    (u uBar : ι -> PoincareM8 -> DiracSpinorField)
    (v vBar : κ -> PoincareM8 -> DiracSpinorField)
    (a b : DiracSpinorIndex) (q q' : PoincareM8) :
    diracDistributionKernel u uBar v vBar a b q q' =
      diracPositiveFrequencyKernel u uBar a b q q'
        + diracNegativeFrequencyKernel v vBar a b q q' := rfl

/-- Finite form of the Dirac distribution kernel from the positive- and
negative-frequency mode families. -/
lemma diracDistributionKernel_fintype {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u uBar : ι -> PoincareM8 -> DiracSpinorField)
    (v vBar : κ -> PoincareM8 -> DiracSpinorField)
    (a b : DiracSpinorIndex) (q q' : PoincareM8) :
    diracDistributionKernel u uBar v vBar a b q q' =
      (∑ i, u i q a * uBar i q' b)
        + ∑ j, v j q a * vBar j q' b := by
  rw [diracDistributionKernel_eq_positive_add_negative,
    diracPositiveFrequencyKernel_fintype, diracNegativeFrequencyKernel_fintype]

/-- Finite summed asymptotic CAR kernel for one outgoing Dirac mode sum and one
incoming Dirac mode sum. -/
noncomputable def finiteDiracAsymptoticCAROperatorKernel {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ∑ j, inCoeff j • ∑ i, outCoeff i •
    diracAsymptoticCAROperatorKernel (outSpin i) (inSpin j) (outMom i) (inMom j)

/-- The finite summed Dirac CAR kernel is the supercommutator of the finite
outgoing and incoming Dirac mode operators. -/
lemma finiteDiracMode_superCommute_eq_CAROperatorKernel {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3) :
    superCommuteF
        (finiteDiracOutgoingModeOperator outCoeff outSpin outMom)
        (finiteDiracIncomingModeOperator inCoeff inSpin inMom) =
      finiteDiracAsymptoticCAROperatorKernel outCoeff outSpin outMom
        inCoeff inSpin inMom := by
  simp [finiteDiracOutgoingModeOperator, finiteDiracIncomingModeOperator,
    finiteDiracAsymptoticCAROperatorKernel, diracAsymptoticCAROperatorKernel]

/-! ## F.3. Section 9.1 Maxwell CCR Kernels and Photon Mode Series -/

/-- Vacuum two-point function for Maxwell position fields, expressed as the existing
Wick time contraction. -/
noncomputable def maxwellVacuumTwoPointFunction (a b : Fin 6) (x y : SpaceTime) :
    poincareQEDFieldSpec.WickAlgebra :=
  WickAlgebra.timeContract (maxwellPositionFieldOp a x) (maxwellPositionFieldOp b y)

/-- The Maxwell vacuum two-point function is central in the Wick algebra. -/
lemma maxwellVacuumTwoPointFunction_mem_center (a b : Fin 6) (x y : SpaceTime) :
    maxwellVacuumTwoPointFunction a b x y ∈
      Subalgebra.center ℂ poincareQEDFieldSpec.WickAlgebra := by
  simpa [maxwellVacuumTwoPointFunction] using
    maxwellPosition_timeContract_mem_center a b x y

/-- A Wick-algebra-valued photon two-point kernel for the Maxwell field. -/
def MaxwellTwoPointKernelRelation
    (kernel : Fin 6 -> Fin 6 -> SpaceTime -> SpaceTime -> poincareQEDFieldSpec.WickAlgebra) :
    Prop :=
  ∀ a b x y,
    WickAlgebra.timeContract (maxwellPositionFieldOp a x) (maxwellPositionFieldOp b y) =
      kernel a b x y

/-- The Maxwell vacuum two-point function realizes the photon two-point kernel relation. -/
lemma maxwellVacuumTwoPointFunction_realizes_twoPointKernel :
    MaxwellTwoPointKernelRelation maxwellVacuumTwoPointFunction := by
  intro a b x y
  rfl

/-- Operator-valued Maxwell CCR kernel, represented by the bosonic supercommutator. -/
noncomputable def maxwellCCROperatorKernel (a b : Fin 6) (x y : SpaceTime) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  superCommuteF (ofFieldOpF (maxwellPositionFieldOp a x))
    (ofFieldOpF (maxwellPositionFieldOp b y))

/-- The Maxwell CCR kernel is exactly the shared bosonic supercommutator. -/
lemma maxwellCCROperatorKernel_eq_superCommute (a b : Fin 6) (x y : SpaceTime) :
    maxwellCCROperatorKernel a b x y =
      superCommuteF (ofFieldOpF (maxwellPositionFieldOp a x))
        (ofFieldOpF (maxwellPositionFieldOp b y)) := rfl

/-- Asymptotic photon CCR kernel, represented by the outgoing-incoming bosonic
commutator from Eq. 173. -/
noncomputable def photonAsymptoticCCROperatorKernel (h k : Fin 2) (p q : Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  superCommuteF (ofFieldOpF (maxwellOutgoingFieldOp h p))
    (ofFieldOpF (maxwellIncomingFieldOp k q))

/-- Photon asymptotic CCR kernels are specified by the outgoing-incoming commutator. -/
def PhotonAsymptoticCCRKernelRelation
    (kernel : Fin 2 -> Fin 2 -> Momentum 3 -> Momentum 3 ->
      poincareQEDFieldSpec.FieldOpFreeAlgebra) : Prop :=
  ∀ h k p q,
    superCommuteF (ofFieldOpF (maxwellOutgoingFieldOp h p))
      (ofFieldOpF (maxwellIncomingFieldOp k q)) = kernel h k p q

/-- The defined photon asymptotic CCR kernel realizes the CCR-kernel relation. -/
lemma photonAsymptoticCCROperatorKernel_realizes_CCR :
    PhotonAsymptoticCCRKernelRelation photonAsymptoticCCROperatorKernel := by
  intro h k p q
  rfl

/-- Component expression for the photon asymptotic CCR kernel. -/
lemma photonAsymptoticCCROperatorKernel_eq_commutator (h k : Fin 2) (p q : Momentum 3) :
    photonAsymptoticCCROperatorKernel h k p q =
      ofFieldOpF (maxwellOutgoingFieldOp h p) * ofFieldOpF (maxwellIncomingFieldOp k q)
        - ofFieldOpF (maxwellIncomingFieldOp k q) * ofFieldOpF (maxwellOutgoingFieldOp h p) := by
  rw [photonAsymptoticCCROperatorKernel, maxwellOutgoingIncoming_superCommute_ofFieldOpF]

/-- Positive-frequency c-number photon kernel from helicity modes on `M8`. -/
noncomputable def photonPositiveFrequencyKernel {ι : Type*}
    (mode modeBar : ι -> PoincareM8 -> Fin 3 -> ℂ)
    (a b : Fin 3) (q q' : PoincareM8) : ℂ :=
  ∑' i, mode i q a * modeBar i q' b

/-- Finite form of the positive-frequency photon two-point kernel. -/
lemma photonPositiveFrequencyKernel_fintype {ι : Type*} [Fintype ι]
    (mode modeBar : ι -> PoincareM8 -> Fin 3 -> ℂ)
    (a b : Fin 3) (q q' : PoincareM8) :
    photonPositiveFrequencyKernel mode modeBar a b q q' =
      ∑ i, mode i q a * modeBar i q' b := by
  simp [photonPositiveFrequencyKernel]

/-- Negative-frequency c-number photon kernel from helicity modes on `M8`. -/
noncomputable def photonNegativeFrequencyKernel {ι : Type*}
    (mode modeBar : ι -> PoincareM8 -> Fin 3 -> ℂ)
    (a b : Fin 3) (q q' : PoincareM8) : ℂ :=
  ∑' i, mode i q a * modeBar i q' b

/-- Finite form of the negative-frequency photon two-point kernel. -/
lemma photonNegativeFrequencyKernel_fintype {ι : Type*} [Fintype ι]
    (mode modeBar : ι -> PoincareM8 -> Fin 3 -> ℂ)
    (a b : Fin 3) (q q' : PoincareM8) :
    photonNegativeFrequencyKernel mode modeBar a b q q' =
      ∑ i, mode i q a * modeBar i q' b := by
  simp [photonNegativeFrequencyKernel]

/-- Photon distribution kernel as the sum of positive- and negative-frequency helicity kernels. -/
noncomputable def photonDistributionKernel {ι κ : Type*}
    (u uBar : ι -> PoincareM8 -> Fin 3 -> ℂ)
    (v vBar : κ -> PoincareM8 -> Fin 3 -> ℂ)
    (a b : Fin 3) (q q' : PoincareM8) : ℂ :=
  photonPositiveFrequencyKernel u uBar a b q q'
    + photonNegativeFrequencyKernel v vBar a b q q'

/-- The photon distribution kernel decomposes into positive- and negative-frequency parts. -/
lemma photonDistributionKernel_eq_positive_add_negative {ι κ : Type*}
    (u uBar : ι -> PoincareM8 -> Fin 3 -> ℂ)
    (v vBar : κ -> PoincareM8 -> Fin 3 -> ℂ)
    (a b : Fin 3) (q q' : PoincareM8) :
    photonDistributionKernel u uBar v vBar a b q q' =
      photonPositiveFrequencyKernel u uBar a b q q'
        + photonNegativeFrequencyKernel v vBar a b q q' := rfl

/-- Finite form of the photon commutator kernel from Eq. 174. -/
lemma photonDistributionKernel_fintype {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u uBar : ι -> PoincareM8 -> Fin 3 -> ℂ)
    (v vBar : κ -> PoincareM8 -> Fin 3 -> ℂ)
    (a b : Fin 3) (q q' : PoincareM8) :
    photonDistributionKernel u uBar v vBar a b q q' =
      (∑ i, u i q a * uBar i q' b)
        + ∑ j, v j q a * vBar j q' b := by
  rw [photonDistributionKernel_eq_positive_add_negative,
    photonPositiveFrequencyKernel_fintype, photonNegativeFrequencyKernel_fintype]

/-- Finite summed asymptotic CCR kernel for one outgoing photon mode sum and one
incoming photon mode sum. -/
noncomputable def finitePhotonAsymptoticCCROperatorKernel {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ∑ j, inCoeff j • ∑ i, outCoeff i •
    photonAsymptoticCCROperatorKernel (outHelicity i) (inHelicity j)
      (outMom i) (inMom j)

/-- The finite summed photon CCR kernel is the supercommutator of the finite
outgoing and incoming Maxwell mode operators. -/
lemma finitePhotonMode_superCommute_eq_CCROperatorKernel {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3) :
    superCommuteF
        (finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom)
        (finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom) =
      finitePhotonAsymptoticCCROperatorKernel outCoeff outHelicity outMom
        inCoeff inHelicity inMom := by
  simp [finiteMaxwellOutgoingModeOperator, finiteMaxwellIncomingModeOperator,
    finitePhotonAsymptoticCCROperatorKernel, photonAsymptoticCCROperatorKernel]

/-! ## F.4. Indexed Infinite Operator Expansions -/

/-- Indexed incoming-Dirac operator-mode family.  Finite sums are evaluated by
`finiteDiracIncomingModeOperator`; analytic infinite operator sums require a topology
on the target operator algebra. -/
noncomputable def diracIncomingOperatorModeFamily {ι : Type*}
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    ι -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  fun i => coeff i • ofFieldOpF (diracIncomingFieldOp (spin i) (mom i))

/-- Indexed outgoing-Dirac operator-mode family.  Finite sums are evaluated by
`finiteDiracOutgoingModeOperator`. -/
noncomputable def diracOutgoingOperatorModeFamily {ι : Type*}
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    ι -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  fun i => coeff i • ofFieldOpF (diracOutgoingFieldOp (spin i) (mom i))

/-- Indexed outgoing-Maxwell helicity operator-mode family.  Finite sums are evaluated by
`finiteMaxwellOutgoingModeOperator`; the c-number helicity series is
`photonHelicityModeSeriesM8`. -/
noncomputable def maxwellOutgoingOperatorModeFamily {ι : Type*}
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    ι -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  fun i => coeff i • ofFieldOpF (maxwellOutgoingFieldOp (helicity i) (mom i))

/-- Indexed incoming-Maxwell helicity operator-mode family from the creation part of Eq. 173. -/
noncomputable def maxwellIncomingOperatorModeFamily {ι : Type*}
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    ι -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  fun i => coeff i • ofFieldOpF (maxwellIncomingFieldOp (helicity i) (mom i))

/-- Finite sums of the outgoing Maxwell family are the finite outgoing mode operator. -/
lemma maxwellOutgoingOperatorModeFamily_sum {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    ∑ i, maxwellOutgoingOperatorModeFamily coeff helicity mom i =
      finiteMaxwellOutgoingModeOperator coeff helicity mom := by
  simp [maxwellOutgoingOperatorModeFamily, finiteMaxwellOutgoingModeOperator]

/-- Finite sums of the incoming Maxwell family are the finite incoming mode operator. -/
lemma maxwellIncomingOperatorModeFamily_sum {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (helicity : ι -> Fin 2) (mom : ι -> Momentum 3) :
    ∑ i, maxwellIncomingOperatorModeFamily coeff helicity mom i =
      finiteMaxwellIncomingModeOperator coeff helicity mom := by
  simp [maxwellIncomingOperatorModeFamily, finiteMaxwellIncomingModeOperator]

/-- Finite sums of the incoming Dirac family are the finite incoming mode operator. -/
lemma diracIncomingOperatorModeFamily_sum {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    ∑ i, diracIncomingOperatorModeFamily coeff spin mom i =
      finiteDiracIncomingModeOperator coeff spin mom := by
  simp [diracIncomingOperatorModeFamily, finiteDiracIncomingModeOperator]

/-- Finite sums of the outgoing Dirac family are the finite outgoing mode operator. -/
lemma diracOutgoingOperatorModeFamily_sum {ι : Type*} [Fintype ι]
    (coeff : ι -> ℂ) (spin : ι -> Fin 4) (mom : ι -> Momentum 3) :
    ∑ i, diracOutgoingOperatorModeFamily coeff spin mom i =
      finiteDiracOutgoingModeOperator coeff spin mom := by
  simp [diracOutgoingOperatorModeFamily, finiteDiracOutgoingModeOperator]

/-- Finite sums of the incoming and outgoing Dirac mode families give the
electron/positron split of the second-quantized Dirac field. -/
lemma diracElectronPositronModeFamilies_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (electronCoeff : ι -> ℂ) (electronSpin : ι -> Fin 4) (electronMom : ι -> Momentum 3)
    (positronCoeff : κ -> ℂ) (positronSpin : κ -> Fin 4) (positronMom : κ -> Momentum 3) :
    (∑ i, diracIncomingOperatorModeFamily electronCoeff electronSpin electronMom i)
      + ∑ j, diracOutgoingOperatorModeFamily positronCoeff positronSpin positronMom j =
        finiteDiracElectronPositronModeOperator electronCoeff electronSpin electronMom
          positronCoeff positronSpin positronMom := by
  rw [diracIncomingOperatorModeFamily_sum, diracOutgoingOperatorModeFamily_sum]
  rfl

/-! ## F.5. Realized Infinite Operator-Mode Convergence -/

/-- Infinite operator-mode series after applying an algebraic free-field
realization to a complete normed target space. -/
noncomputable def realizedOperatorModeSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (mode : ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra) : A :=
  ∑' n, realize (mode n)

/-- Finite truncation of a realized operator-mode series. -/
noncomputable def realizedOperatorModePartialSum {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (mode : ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra) (N : ℕ) : A :=
  ∑ n ∈ Finset.range N, realize (mode n)

/-- Realizing an algebraic finite mode sum is the same as summing the realized
finite modes. -/
lemma realizedOperatorModePartialSum_eq_map_range {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (mode : ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra) (N : ℕ) :
    realize (∑ n ∈ Finset.range N, mode n) =
      realizedOperatorModePartialSum realize mode N := by
  simp [realizedOperatorModePartialSum]

/-- A summable real majorant gives summability of the realized operator-mode
series. -/
lemma realizedOperatorModeSeries_summable_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (mode : ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound : ∀ n, ‖realize (mode n)‖ ≤ majorant n) :
    Summable (fun n => realize (mode n)) :=
  Summable.of_norm_bounded hmajorant hbound

/-- A summable real majorant identifies the realized infinite operator-mode
series as the sum of its realized modes. -/
lemma realizedOperatorModeSeries_hasSum_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (mode : ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound : ∀ n, ‖realize (mode n)‖ ≤ majorant n) :
    HasSum (fun n => realize (mode n))
      (realizedOperatorModeSeries realize mode) := by
  exact (realizedOperatorModeSeries_summable_of_norm_bound realize mode
    majorant hmajorant hbound).hasSum

/-- Finite realized operator-mode truncations converge to the realized infinite
operator-mode series. -/
lemma realizedOperatorModePartialSum_tendsto_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (mode : ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound : ∀ n, ‖realize (mode n)‖ ≤ majorant n) :
    Filter.Tendsto (fun N => realizedOperatorModePartialSum realize mode N)
      Filter.atTop (nhds (realizedOperatorModeSeries realize mode)) := by
  have hsum := realizedOperatorModeSeries_hasSum_of_norm_bound realize mode
    majorant hmajorant hbound
  simpa [realizedOperatorModePartialSum] using hsum.tendsto_sum_nat

/-- Realized incoming-Dirac infinite mode series. -/
noncomputable def realizedDiracIncomingOperatorModeSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (coeff : ℕ -> ℂ) (spin : ℕ -> Fin 4) (mom : ℕ -> Momentum 3) : A :=
  realizedOperatorModeSeries realize (diracIncomingOperatorModeFamily coeff spin mom)

/-- Realized outgoing-Dirac infinite mode series. -/
noncomputable def realizedDiracOutgoingOperatorModeSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (coeff : ℕ -> ℂ) (spin : ℕ -> Fin 4) (mom : ℕ -> Momentum 3) : A :=
  realizedOperatorModeSeries realize (diracOutgoingOperatorModeFamily coeff spin mom)

/-- Realized outgoing-Maxwell infinite helicity-mode series. -/
noncomputable def realizedMaxwellOutgoingOperatorModeSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (coeff : ℕ -> ℂ) (helicity : ℕ -> Fin 2) (mom : ℕ -> Momentum 3) : A :=
  realizedOperatorModeSeries realize (maxwellOutgoingOperatorModeFamily coeff helicity mom)

/-- Realized incoming-Maxwell infinite helicity-mode series. -/
noncomputable def realizedMaxwellIncomingOperatorModeSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (coeff : ℕ -> ℂ) (helicity : ℕ -> Fin 2) (mom : ℕ -> Momentum 3) : A :=
  realizedOperatorModeSeries realize (maxwellIncomingOperatorModeFamily coeff helicity mom)

/-- Incoming-Dirac operator modes have a realized infinite sum whenever their
realized terms satisfy a summable norm majorant. -/
lemma realizedDiracIncomingOperatorModeSeries_hasSum_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (coeff : ℕ -> ℂ) (spin : ℕ -> Fin 4) (mom : ℕ -> Momentum 3)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n, ‖realize (diracIncomingOperatorModeFamily coeff spin mom n)‖ ≤ majorant n) :
    HasSum (fun n => realize (diracIncomingOperatorModeFamily coeff spin mom n))
      (realizedDiracIncomingOperatorModeSeries realize coeff spin mom) :=
  realizedOperatorModeSeries_hasSum_of_norm_bound realize
    (diracIncomingOperatorModeFamily coeff spin mom) majorant hmajorant hbound

/-- Outgoing-Dirac operator modes have a realized infinite sum whenever their
realized terms satisfy a summable norm majorant. -/
lemma realizedDiracOutgoingOperatorModeSeries_hasSum_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (coeff : ℕ -> ℂ) (spin : ℕ -> Fin 4) (mom : ℕ -> Momentum 3)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n, ‖realize (diracOutgoingOperatorModeFamily coeff spin mom n)‖ ≤ majorant n) :
    HasSum (fun n => realize (diracOutgoingOperatorModeFamily coeff spin mom n))
      (realizedDiracOutgoingOperatorModeSeries realize coeff spin mom) :=
  realizedOperatorModeSeries_hasSum_of_norm_bound realize
    (diracOutgoingOperatorModeFamily coeff spin mom) majorant hmajorant hbound

/-- Outgoing-Maxwell operator modes have a realized infinite sum whenever their
realized terms satisfy a summable norm majorant. -/
lemma realizedMaxwellOutgoingOperatorModeSeries_hasSum_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (coeff : ℕ -> ℂ) (helicity : ℕ -> Fin 2) (mom : ℕ -> Momentum 3)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n, ‖realize (maxwellOutgoingOperatorModeFamily coeff helicity mom n)‖ ≤
        majorant n) :
    HasSum (fun n => realize (maxwellOutgoingOperatorModeFamily coeff helicity mom n))
      (realizedMaxwellOutgoingOperatorModeSeries realize coeff helicity mom) :=
  realizedOperatorModeSeries_hasSum_of_norm_bound realize
    (maxwellOutgoingOperatorModeFamily coeff helicity mom) majorant hmajorant hbound

/-- Incoming-Maxwell operator modes have a realized infinite sum whenever their
realized terms satisfy a summable norm majorant. -/
lemma realizedMaxwellIncomingOperatorModeSeries_hasSum_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (coeff : ℕ -> ℂ) (helicity : ℕ -> Fin 2) (mom : ℕ -> Momentum 3)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n, ‖realize (maxwellIncomingOperatorModeFamily coeff helicity mom n)‖ ≤
        majorant n) :
    HasSum (fun n => realize (maxwellIncomingOperatorModeFamily coeff helicity mom n))
      (realizedMaxwellIncomingOperatorModeSeries realize coeff helicity mom) :=
  realizedOperatorModeSeries_hasSum_of_norm_bound realize
    (maxwellIncomingOperatorModeFamily coeff helicity mom) majorant hmajorant hbound

/-- Realized electron/positron Dirac field series obtained from incoming electron
and outgoing positron mode families. -/
noncomputable def realizedDiracElectronPositronOperatorModeSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (electronCoeff : ℕ -> ℂ) (electronSpin : ℕ -> Fin 4) (electronMom : ℕ -> Momentum 3)
    (positronCoeff : ℕ -> ℂ) (positronSpin : ℕ -> Fin 4) (positronMom : ℕ -> Momentum 3) :
    A :=
  realizedDiracIncomingOperatorModeSeries realize electronCoeff electronSpin electronMom
    + realizedDiracOutgoingOperatorModeSeries realize positronCoeff positronSpin positronMom

/-- Finite truncation of the realized electron/positron Dirac field series. -/
noncomputable def realizedDiracElectronPositronOperatorModePartialSum {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (electronCoeff : ℕ -> ℂ) (electronSpin : ℕ -> Fin 4) (electronMom : ℕ -> Momentum 3)
    (positronCoeff : ℕ -> ℂ) (positronSpin : ℕ -> Fin 4) (positronMom : ℕ -> Momentum 3)
    (N : ℕ) : A :=
  realizedOperatorModePartialSum realize
      (diracIncomingOperatorModeFamily electronCoeff electronSpin electronMom) N
    + realizedOperatorModePartialSum realize
      (diracOutgoingOperatorModeFamily positronCoeff positronSpin positronMom) N

/-- The realized electron/positron Dirac field truncations converge when both
incoming and outgoing realized mode families have summable norm majorants. -/
lemma realizedDiracElectronPositronOperatorModePartialSum_tendsto_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (electronCoeff : ℕ -> ℂ) (electronSpin : ℕ -> Fin 4) (electronMom : ℕ -> Momentum 3)
    (positronCoeff : ℕ -> ℂ) (positronSpin : ℕ -> Fin 4) (positronMom : ℕ -> Momentum 3)
    (majorantE majorantP : ℕ -> ℝ)
    (hmajorantE : Summable majorantE) (hmajorantP : Summable majorantP)
    (hboundE :
      ∀ n,
        ‖realize (diracIncomingOperatorModeFamily electronCoeff electronSpin electronMom n)‖ ≤
          majorantE n)
    (hboundP :
      ∀ n,
        ‖realize (diracOutgoingOperatorModeFamily positronCoeff positronSpin positronMom n)‖ ≤
          majorantP n) :
    Filter.Tendsto
      (fun N => realizedDiracElectronPositronOperatorModePartialSum realize electronCoeff
        electronSpin electronMom positronCoeff positronSpin positronMom N)
      Filter.atTop
      (nhds (realizedDiracElectronPositronOperatorModeSeries realize electronCoeff
        electronSpin electronMom positronCoeff positronSpin positronMom)) := by
  exact
    (realizedOperatorModePartialSum_tendsto_of_norm_bound realize
      (diracIncomingOperatorModeFamily electronCoeff electronSpin electronMom)
      majorantE hmajorantE hboundE).add
    (realizedOperatorModePartialSum_tendsto_of_norm_bound realize
      (diracOutgoingOperatorModeFamily positronCoeff positronSpin positronMom)
      majorantP hmajorantP hboundP)

/-- Realized photon field series obtained from incoming and outgoing helicity
mode families. -/
noncomputable def realizedPhotonInOutOperatorModeSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (inCoeff : ℕ -> ℂ) (inHelicity : ℕ -> Fin 2) (inMom : ℕ -> Momentum 3)
    (outCoeff : ℕ -> ℂ) (outHelicity : ℕ -> Fin 2) (outMom : ℕ -> Momentum 3) :
    A :=
  realizedMaxwellIncomingOperatorModeSeries realize inCoeff inHelicity inMom
    + realizedMaxwellOutgoingOperatorModeSeries realize outCoeff outHelicity outMom

/-- Finite truncation of the realized incoming/outgoing photon series. -/
noncomputable def realizedPhotonInOutOperatorModePartialSum {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (inCoeff : ℕ -> ℂ) (inHelicity : ℕ -> Fin 2) (inMom : ℕ -> Momentum 3)
    (outCoeff : ℕ -> ℂ) (outHelicity : ℕ -> Fin 2) (outMom : ℕ -> Momentum 3)
    (N : ℕ) : A :=
  realizedOperatorModePartialSum realize
      (maxwellIncomingOperatorModeFamily inCoeff inHelicity inMom) N
    + realizedOperatorModePartialSum realize
      (maxwellOutgoingOperatorModeFamily outCoeff outHelicity outMom) N

/-- The realized photon in/out field truncations converge when both helicity
mode families have summable norm majorants. -/
lemma realizedPhotonInOutOperatorModePartialSum_tendsto_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (inCoeff : ℕ -> ℂ) (inHelicity : ℕ -> Fin 2) (inMom : ℕ -> Momentum 3)
    (outCoeff : ℕ -> ℂ) (outHelicity : ℕ -> Fin 2) (outMom : ℕ -> Momentum 3)
    (majorantIn majorantOut : ℕ -> ℝ)
    (hmajorantIn : Summable majorantIn) (hmajorantOut : Summable majorantOut)
    (hboundIn :
      ∀ n,
        ‖realize (maxwellIncomingOperatorModeFamily inCoeff inHelicity inMom n)‖ ≤
          majorantIn n)
    (hboundOut :
      ∀ n,
        ‖realize (maxwellOutgoingOperatorModeFamily outCoeff outHelicity outMom n)‖ ≤
          majorantOut n) :
    Filter.Tendsto
      (fun N => realizedPhotonInOutOperatorModePartialSum realize inCoeff inHelicity
        inMom outCoeff outHelicity outMom N)
      Filter.atTop
      (nhds (realizedPhotonInOutOperatorModeSeries realize inCoeff inHelicity
        inMom outCoeff outHelicity outMom)) := by
  exact
    (realizedOperatorModePartialSum_tendsto_of_norm_bound realize
      (maxwellIncomingOperatorModeFamily inCoeff inHelicity inMom)
      majorantIn hmajorantIn hboundIn).add
    (realizedOperatorModePartialSum_tendsto_of_norm_bound realize
      (maxwellOutgoingOperatorModeFamily outCoeff outHelicity outMom)
      majorantOut hmajorantOut hboundOut)

/-! ## G. Finite `M8` Interaction Integrals and Dyson Insertions -/

/-- A finite-mode product integral over sampled `M8 = R^{1,3} x S^2_C` points.  This is
the finite algebraic skeleton of the paper's invariant measure replacement
`d4x -> d4x d4g`. -/
noncomputable def finiteM8ProductIntegral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (F : PoincareM8 -> ℂ) : ℂ :=
  ∑ i, ∑ j, weightX i * weightZ j * F (sampleX i, sampleZ j)

/-- The finite `M8` product integral factors on separated Minkowski/sphere integrands. -/
lemma finiteM8ProductIntegral_factorized {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (fx : MinkowskiPoint -> ℂ) (fz : ComplexTwoSpherePoint -> ℂ) :
    finiteM8ProductIntegral weightX weightZ sampleX sampleZ
        (fun q => fx q.1 * fz q.2) =
      (∑ i, weightX i * fx (sampleX i)) *
        (∑ j, weightZ j * fz (sampleZ j)) := by
  unfold finiteM8ProductIntegral
  calc
    ∑ i, ∑ j, weightX i * weightZ j * (fx (sampleX i) * fz (sampleZ j))
        = ∑ i, (weightX i * fx (sampleX i)) *
            (∑ j, weightZ j * fz (sampleZ j)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ = (∑ i, weightX i * fx (sampleX i)) *
        (∑ j, weightZ j * fz (sampleZ j)) := by
          rw [Finset.sum_mul]

/-- Finite sampled Fourier coefficient on `M8`, reusing the finite `M8` product
integral for the coefficient pairing with a dual `M8` Fourier mode. -/
noncomputable def finiteM8FourierCoefficient {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (field : PoincareM8 -> ℂ) (p : MinkowskiPoint)
    (dualSphereMode : ComplexTwoSpherePoint -> ℂ) : ℂ :=
  finiteM8ProductIntegral weightX weightZ sampleX sampleZ
    (fun q => field q * finiteM8FourierMode p dualSphereMode q)

/-- The finite `M8` Fourier coefficient is linear in the sampled field. -/
lemma finiteM8FourierCoefficient_add_field {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (field₁ field₂ : PoincareM8 -> ℂ) (p : MinkowskiPoint)
    (dualSphereMode : ComplexTwoSpherePoint -> ℂ) :
    finiteM8FourierCoefficient weightX weightZ sampleX sampleZ
        (fun q => field₁ q + field₂ q) p dualSphereMode =
      finiteM8FourierCoefficient weightX weightZ sampleX sampleZ field₁ p dualSphereMode
        + finiteM8FourierCoefficient weightX weightZ sampleX sampleZ field₂ p dualSphereMode := by
  unfold finiteM8FourierCoefficient finiteM8ProductIntegral
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The finite `M8` action integral `A = integral L`. -/
noncomputable def finiteM8ActionIntegral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (lagrangianDensity : PoincareM8 -> ℂ) : ℂ :=
  finiteM8ProductIntegral weightX weightZ sampleX sampleZ lagrangianDensity

/-- The finite `M8` action integral factors on separated Lagrangian densities. -/
lemma finiteM8ActionIntegral_factorized {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (lx : MinkowskiPoint -> ℂ) (lz : ComplexTwoSpherePoint -> ℂ) :
    finiteM8ActionIntegral weightX weightZ sampleX sampleZ
        (fun q => lx q.1 * lz q.2) =
      (∑ i, weightX i * lx (sampleX i)) *
        (∑ j, weightZ j * lz (sampleZ j)) :=
  finiteM8ProductIntegral_factorized weightX weightZ sampleX sampleZ lx lz

/-- Section 10's interaction Hamiltonian density for a derivative-free interaction:
`H_I = -L_I`. -/
def finiteM8InteractionHamiltonianDensity
    (interactionLagrangianDensity : PoincareM8 -> ℂ) : PoincareM8 -> ℂ :=
  fun q => -interactionLagrangianDensity q

/-- Integrating `H_I = -L_I` gives the negative finite action integral. -/
lemma finiteM8InteractionIntegral_of_lagrangian {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (interactionLagrangianDensity : PoincareM8 -> ℂ) :
    finiteM8ProductIntegral weightX weightZ sampleX sampleZ
        (finiteM8InteractionHamiltonianDensity interactionLagrangianDensity) =
      -finiteM8ActionIntegral weightX weightZ sampleX sampleZ
        interactionLagrangianDensity := by
  simp [finiteM8ProductIntegral, finiteM8ActionIntegral,
    finiteM8InteractionHamiltonianDensity]

/-- The finite interaction integral used in the `M8` Dyson exponent. -/
noncomputable def finiteM8InteractionIntegral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (interactionHamiltonian : PoincareM8 -> ℂ) : ℂ :=
  finiteM8ProductIntegral weightX weightZ sampleX sampleZ interactionHamiltonian

/-- The scalar exponent coefficient `-i/(hbar*c) * integral(H_I)` from the `M8` Dyson formula. -/
noncomputable def finiteM8DysonExponentCoefficient (hbar c : ℝ) (interactionIntegral : ℂ) : ℂ :=
  (-(Complex.I / ((hbar * c : ℝ) : ℂ))) * interactionIntegral

/-- With `H_I = -L_I`, the finite Dyson exponent coefficient is `i/(hbar*c)` times the
finite interaction action. -/
lemma finiteM8DysonExponentCoefficient_of_lagrangian {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (interactionLagrangianDensity : PoincareM8 -> ℂ) :
    finiteM8DysonExponentCoefficient hbar c
        (finiteM8InteractionIntegral weightX weightZ sampleX sampleZ
          (finiteM8InteractionHamiltonianDensity interactionLagrangianDensity)) =
      (Complex.I / ((hbar * c : ℝ) : ℂ)) *
        finiteM8ActionIntegral weightX weightZ sampleX sampleZ
          interactionLagrangianDensity := by
  rw [finiteM8InteractionIntegral, finiteM8InteractionIntegral_of_lagrangian]
  simp [finiteM8DysonExponentCoefficient]

/-- The finite `M8` Dyson exponent coefficient factors for separated interaction densities. -/
lemma finiteM8DysonExponentCoefficient_factorized {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (hx : MinkowskiPoint -> ℂ) (hz : ComplexTwoSpherePoint -> ℂ) :
    finiteM8DysonExponentCoefficient hbar c
        (finiteM8InteractionIntegral weightX weightZ sampleX sampleZ
          (fun q => hx q.1 * hz q.2)) =
      (-(Complex.I / ((hbar * c : ℝ) : ℂ))) *
        ((∑ i, weightX i * hx (sampleX i)) *
          (∑ j, weightZ j * hz (sampleZ j))) := by
  rw [finiteM8InteractionIntegral, finiteM8ProductIntegral_factorized]
  rfl

/-- The scalar Dyson weight `exp(-i/(hbar*c) * integral(H_I))` for a finite `M8` sample. -/
noncomputable def finiteM8DysonWeight (hbar c : ℝ) (interactionIntegral : ℂ) : ℂ :=
  Complex.exp (finiteM8DysonExponentCoefficient hbar c interactionIntegral)

/-- With `H_I = -L_I`, the finite Dyson weight is the exponential of
`i/(hbar*c)` times the finite interaction action. -/
lemma finiteM8DysonWeight_of_lagrangian {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (interactionLagrangianDensity : PoincareM8 -> ℂ) :
    finiteM8DysonWeight hbar c
        (finiteM8InteractionIntegral weightX weightZ sampleX sampleZ
          (finiteM8InteractionHamiltonianDensity interactionLagrangianDensity)) =
      Complex.exp
        ((Complex.I / ((hbar * c : ℝ) : ℂ)) *
          finiteM8ActionIntegral weightX weightZ sampleX sampleZ
            interactionLagrangianDensity) := by
  rw [finiteM8DysonWeight, finiteM8DysonExponentCoefficient_of_lagrangian]

/-- Zero finite interaction gives the identity scalar Dyson weight. -/
@[simp] lemma finiteM8DysonWeight_zero (hbar c : ℝ) :
    finiteM8DysonWeight hbar c 0 = 1 := by
  simp [finiteM8DysonWeight, finiteM8DysonExponentCoefficient]

/-- The finite `M8` Dyson weight factors through the separated product integral. -/
lemma finiteM8DysonWeight_factorized {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (hx : MinkowskiPoint -> ℂ) (hz : ComplexTwoSpherePoint -> ℂ) :
    finiteM8DysonWeight hbar c
        (finiteM8InteractionIntegral weightX weightZ sampleX sampleZ
          (fun q => hx q.1 * hz q.2)) =
      Complex.exp
        ((-(Complex.I / ((hbar * c : ℝ) : ℂ))) *
          ((∑ i, weightX i * hx (sampleX i)) *
            (∑ j, weightZ j * hz (sampleZ j)))) := by
  rw [finiteM8DysonWeight, finiteM8DysonExponentCoefficient_factorized]

/-- The first-order finite `M8` Dyson insertion in the shared field-operator algebra. -/
noncomputable def poincareQEDDysonFirstOrder
    (coupling : ℂ) (operator : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  timeOrderF (coupling • operator)

/-- First-order `M8` Dyson insertion uses the linearity of the existing time-ordering map. -/
lemma poincareQEDDysonFirstOrder_eq_smul_timeOrder
    (coupling : ℂ) (operator : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDDysonFirstOrder coupling operator = coupling • timeOrderF operator := by
  exact map_smul timeOrderF coupling operator

/-! ## G.1. Dyson Weights, Wick Expansion, and the Shared Complex-Action Weight -/

/-- A real finite interaction Hamiltonian integral gives the existing complex-action weight
with real action `-H` and effective Planck scale `hbar*c`. -/
lemma finiteM8DysonWeight_realHamiltonian_eq_complexActionWeight
    (hbar c interactionHamiltonianIntegral : ℝ) :
    finiteM8DysonWeight hbar c (interactionHamiltonianIntegral : ℂ) =
      complexActionWeight (-interactionHamiltonianIntegral) 0 (hbar * c) := by
  unfold finiteM8DysonWeight finiteM8DysonExponentCoefficient complexActionWeight
  congr 1
  push_cast
  ring

/-- With `H_I = -L_I`, a real finite interaction action gives the existing pure-phase
complex-action weight with action `L_I`. -/
lemma finiteM8DysonWeight_realLagrangian_eq_complexActionWeight
    (hbar c interactionAction : ℝ) :
    finiteM8DysonWeight hbar c (-(interactionAction : ℂ)) =
      complexActionWeight interactionAction 0 (hbar * c) := by
  unfold finiteM8DysonWeight finiteM8DysonExponentCoefficient complexActionWeight
  congr 1
  push_cast
  ring

/-- The Poincare-group QED field specification reuses Physlib's Wick expansion. -/
lemma poincareQED_wicks_theorem (φs : List poincareQEDFieldSpec.FieldOp) :
    WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length, φsΛ.wickTerm := by
  simpa using (wicks_theorem (𝓕 := poincareQEDFieldSpec) φs)

/-- A finite real `M8` interaction action multiplies every Wick-contraction term through
the existing complex-action weighted Wick expansion. -/
lemma poincareQED_dysonWeight_smul_wicks_theorem_realLagrangian
    (hbar c interactionAction : ℝ) (φs : List poincareQEDFieldSpec.FieldOp) :
    finiteM8DysonWeight hbar c (-(interactionAction : ℂ)) •
        WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length,
        finiteM8DysonWeight hbar c (-(interactionAction : ℂ)) • φsΛ.wickTerm := by
  rw [finiteM8DysonWeight_realLagrangian_eq_complexActionWeight]
  exact complexActionWeight_smul_wicks_theorem interactionAction 0 (hbar * c) φs

/-! ## G.2. Operator-Valued Interaction Lagrangian and Scattering Formalism -/

/-- Projection from Varlamov's `M8` coordinate model to the spacetime coordinate used by
the shared QFT field-operator API. -/
def poincareM8SpaceTime (q : PoincareM8) : SpaceTime :=
  q.1

/-- The `M8 -> SpaceTime` projection is the first product component. -/
@[simp] lemma poincareM8SpaceTime_apply (q : PoincareM8) :
    poincareM8SpaceTime q = q.1 :=
  rfl

/-- Finite operator-valued product integral over sampled `M8`.  This is the
`FieldOpFreeAlgebra`-valued analogue of `finiteM8ProductIntegral`. -/
noncomputable def finiteM8OperatorIntegral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (F : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ∑ i, ∑ j, (weightX i * weightZ j) • F (sampleX i, sampleZ j)

/-- The finite operator-valued `M8` integral is additive in its integrand. -/
lemma finiteM8OperatorIntegral_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (F G : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    finiteM8OperatorIntegral weightX weightZ sampleX sampleZ (fun q => F q + G q) =
      finiteM8OperatorIntegral weightX weightZ sampleX sampleZ F
        + finiteM8OperatorIntegral weightX weightZ sampleX sampleZ G := by
  simp [finiteM8OperatorIntegral, smul_add, Finset.sum_add_distrib]

/-- The finite operator-valued `M8` integral is linear over scalar multiplication. -/
lemma finiteM8OperatorIntegral_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (c : ℂ) (F : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
  finiteM8OperatorIntegral weightX weightZ sampleX sampleZ (fun q => c • F q) =
      c • finiteM8OperatorIntegral weightX weightZ sampleX sampleZ F := by
  simp [finiteM8OperatorIntegral, smul_smul, Finset.smul_sum, mul_comm]

/-- Time-ordering commutes with the finite sampled operator-valued `M8` integral. -/
lemma timeOrderF_finiteM8OperatorIntegral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (F : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    timeOrderF (finiteM8OperatorIntegral weightX weightZ sampleX sampleZ F) =
      finiteM8OperatorIntegral weightX weightZ sampleX sampleZ
        (fun q => timeOrderF (F q)) := by
  simp [finiteM8OperatorIntegral, map_sum, map_smul]

/-- Finite scalar measure invariance for an `M8` transformation. -/
def IsFiniteM8ProductMeasureInvariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (T : PoincareM8 -> PoincareM8) : Prop :=
  ∀ F : PoincareM8 -> ℂ,
    finiteM8ProductIntegral weightX weightZ sampleX sampleZ (fun q => F (T q)) =
      finiteM8ProductIntegral weightX weightZ sampleX sampleZ F

/-- Finite operator-valued measure invariance for an `M8` transformation. -/
def IsFiniteM8OperatorMeasureInvariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (T : PoincareM8 -> PoincareM8) : Prop :=
  ∀ F : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra,
    finiteM8OperatorIntegral weightX weightZ sampleX sampleZ (fun q => F (T q)) =
      finiteM8OperatorIntegral weightX weightZ sampleX sampleZ F

/-- The identity transformation preserves the finite scalar `M8` product rule. -/
lemma isFiniteM8ProductMeasureInvariant_id {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) :
    IsFiniteM8ProductMeasureInvariant weightX weightZ sampleX sampleZ (fun q => q) := by
  intro F
  rfl

/-- The identity transformation preserves the finite operator-valued `M8` product rule. -/
lemma isFiniteM8OperatorMeasureInvariant_id {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) :
    IsFiniteM8OperatorMeasureInvariant weightX weightZ sampleX sampleZ (fun q => q) := by
  intro F
  rfl

/-- Finite scalar invariance under a specified linear Poincare-group `M8` action. -/
def IsFiniteM8ProductMeasurePoincareInvariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (M : SL(2, ℂ)) (A : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  IsFiniteM8ProductMeasureInvariant weightX weightZ sampleX sampleZ
    (poincareM8LinearAction M A)

/-- Finite operator-valued invariance under a specified linear Poincare-group `M8` action. -/
def IsFiniteM8OperatorMeasurePoincareInvariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (M : SL(2, ℂ)) (A : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  IsFiniteM8OperatorMeasureInvariant weightX weightZ sampleX sampleZ
    (poincareM8LinearAction M A)

/-- The identity linear Poincare-group action preserves the finite scalar product rule. -/
lemma isFiniteM8ProductMeasurePoincareInvariant_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) :
    IsFiniteM8ProductMeasurePoincareInvariant weightX weightZ sampleX sampleZ 1 1 := by
  intro F
  simp [poincareM8LinearAction_one]

/-- The identity linear Poincare-group action preserves the finite operator-valued product rule. -/
lemma isFiniteM8OperatorMeasurePoincareInvariant_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) :
    IsFiniteM8OperatorMeasurePoincareInvariant weightX weightZ sampleX sampleZ 1 1 := by
  intro F
  simp [poincareM8LinearAction_one]

/-- The ordered field list for the indexed QED vertex
`psi-bar_a(q) A_m(q) psi_b(q)` on `M8`. -/
def poincareQEDInteractionFieldList
    (q : PoincareM8) (a b : DiracSpinorIndex) (m : Fin 6) :
    List poincareQEDFieldSpec.FieldOp :=
  [diracPositionFieldOp a (poincareM8SpaceTime q),
    maxwellPositionFieldOp m (poincareM8SpaceTime q),
    diracPositionFieldOp b (poincareM8SpaceTime q)]

/-- Operator monomial for one indexed QED interaction vertex on `M8`. -/
noncomputable def poincareQEDInteractionMonomial
    (q : PoincareM8) (a b : DiracSpinorIndex) (m : Fin 6) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ofFieldOpListF (poincareQEDInteractionFieldList q a b m)

/-- The indexed interaction monomial is the product of two Dirac fields and one Maxwell field. -/
lemma poincareQEDInteractionMonomial_eq_product
    (q : PoincareM8) (a b : DiracSpinorIndex) (m : Fin 6) :
    poincareQEDInteractionMonomial q a b m =
      ofFieldOpF (diracPositionFieldOp a (poincareM8SpaceTime q)) *
        ofFieldOpF (maxwellPositionFieldOp m (poincareM8SpaceTime q)) *
          ofFieldOpF (diracPositionFieldOp b (poincareM8SpaceTime q)) := by
  simp [poincareQEDInteractionMonomial, poincareQEDInteractionFieldList, ofFieldOpListF]
  rw [mul_assoc]

/-- Section 10's indexed operator-valued interaction Lagrangian density on `M8`.
The coefficient tensor supplies the spinor and Maxwell matrix entries of the vertex. -/
noncomputable def poincareQEDIndexedInteractionLagrangian
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  fun q => ∑ a, ∑ m, ∑ b,
    vertex a m b q • poincareQEDInteractionMonomial q a b m

/-- The indexed interaction density vanishes when every vertex coefficient vanishes. -/
@[simp] lemma poincareQEDIndexedInteractionLagrangian_zero :
    poincareQEDIndexedInteractionLagrangian
      (fun _a _m _b _q => (0 : ℂ)) = fun _q => 0 := by
  funext q
  simp [poincareQEDIndexedInteractionLagrangian]

/-- The indexed interaction density is additive in the vertex tensor. -/
lemma poincareQEDIndexedInteractionLagrangian_add
    (V W : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDIndexedInteractionLagrangian (fun a m b q => V a m b q + W a m b q) =
      fun q => poincareQEDIndexedInteractionLagrangian V q
        + poincareQEDIndexedInteractionLagrangian W q := by
  funext q
  simp [poincareQEDIndexedInteractionLagrangian, add_smul, Finset.sum_add_distrib]

/-- Time-ordering a single indexed interaction monomial uses the existing time-ordering map. -/
lemma poincareQEDInteractionMonomial_timeOrder
    (q : PoincareM8) (a b : DiracSpinorIndex) (m : Fin 6) :
    timeOrderF (poincareQEDInteractionMonomial q a b m) =
      timeOrderSign (poincareQEDInteractionFieldList q a b m) •
        ofFieldOpListF (timeOrderList (poincareQEDInteractionFieldList q a b m)) := by
  simpa [poincareQEDInteractionMonomial] using
    (timeOrderF_ofFieldOpListF (𝓕 := poincareQEDFieldSpec)
      (poincareQEDInteractionFieldList q a b m))

/-- Time-ordering the indexed QED interaction density acts termwise on the
operator-valued vertex monomials. -/
lemma timeOrderF_poincareQEDIndexedInteractionLagrangian
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ)
    (q : PoincareM8) :
    timeOrderF (poincareQEDIndexedInteractionLagrangian vertex q) =
      ∑ a, ∑ m, ∑ b,
        vertex a m b q • timeOrderF (poincareQEDInteractionMonomial q a b m) := by
  simp [poincareQEDIndexedInteractionLagrangian, map_sum, map_smul]

/-- Time-ordering the indexed interaction density gives the explicitly ordered
field list for every spinor/Maxwell index triple. -/
lemma timeOrderF_poincareQEDIndexedInteractionLagrangian_expanded
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ)
    (q : PoincareM8) :
    timeOrderF (poincareQEDIndexedInteractionLagrangian vertex q) =
      ∑ a, ∑ m, ∑ b,
        vertex a m b q •
          (timeOrderSign (poincareQEDInteractionFieldList q a b m) •
            ofFieldOpListF (timeOrderList (poincareQEDInteractionFieldList q a b m))) := by
  rw [timeOrderF_poincareQEDIndexedInteractionLagrangian]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro b _hb
  rw [poincareQEDInteractionMonomial_timeOrder]

/-- Operator-valued finite action integral `A_I = integral_M8 L_I`. -/
noncomputable def finiteM8OperatorActionIntegral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (lagrangianDensity : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finiteM8OperatorIntegral weightX weightZ sampleX sampleZ lagrangianDensity

/-- Operator-valued interaction Hamiltonian density `H_I = -L_I`. -/
def finiteM8OperatorInteractionHamiltonianDensity
    (lagrangianDensity : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  fun q => -lagrangianDensity q

/-- Operator-valued integration of `H_I = -L_I` gives the negative interaction action. -/
lemma finiteM8OperatorInteractionIntegral_of_lagrangian {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (lagrangianDensity : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    finiteM8OperatorIntegral weightX weightZ sampleX sampleZ
        (finiteM8OperatorInteractionHamiltonianDensity lagrangianDensity) =
      -finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ lagrangianDensity := by
  simp [finiteM8OperatorIntegral, finiteM8OperatorActionIntegral,
    finiteM8OperatorInteractionHamiltonianDensity]

/-- Operator-valued action integrals are invariant under any finite `M8` transformation
preserving the sampled operator-valued product rule. -/
lemma finiteM8OperatorActionIntegral_invariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (T : PoincareM8 -> PoincareM8)
    (hT : IsFiniteM8OperatorMeasureInvariant weightX weightZ sampleX sampleZ T)
    (lagrangianDensity : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => lagrangianDensity (T q)) =
      finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ lagrangianDensity := by
  exact hT lagrangianDensity

/-- Time-ordering commutes with the finite sampled action integral. -/
lemma timeOrderF_finiteM8OperatorActionIntegral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (lagrangianDensity : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    timeOrderF
        (finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ lagrangianDensity) =
      finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => timeOrderF (lagrangianDensity q)) := by
  exact timeOrderF_finiteM8OperatorIntegral weightX weightZ sampleX sampleZ lagrangianDensity

/-- Finite operator-valued action for the indexed QED interaction vertex. -/
noncomputable def finiteM8IndexedInteractionAction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
    (poincareQEDIndexedInteractionLagrangian vertex)

/-- The indexed interaction action vanishes for the zero vertex tensor. -/
@[simp] lemma finiteM8IndexedInteractionAction_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) :
    finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ
      (fun _a _m _b _q => (0 : ℂ)) = 0 := by
  simp [finiteM8IndexedInteractionAction, finiteM8OperatorActionIntegral,
    finiteM8OperatorIntegral]

/-- The finite indexed interaction action is additive in the vertex tensor. -/
lemma finiteM8IndexedInteractionAction_add_vertex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (V W : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ
        (fun a m b q => V a m b q + W a m b q) =
      finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ V
        + finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ W := by
  rw [finiteM8IndexedInteractionAction, finiteM8IndexedInteractionAction,
    finiteM8IndexedInteractionAction, poincareQEDIndexedInteractionLagrangian_add]
  exact finiteM8OperatorIntegral_add weightX weightZ sampleX sampleZ
    (poincareQEDIndexedInteractionLagrangian V)
    (poincareQEDIndexedInteractionLagrangian W)

/-- A transformed indexed interaction action is invariant under a finite operator-valued
`M8` measure invariance hypothesis. -/
lemma finiteM8IndexedInteractionAction_invariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (T : PoincareM8 -> PoincareM8)
    (hT : IsFiniteM8OperatorMeasureInvariant weightX weightZ sampleX sampleZ T)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => poincareQEDIndexedInteractionLagrangian vertex (T q)) =
      finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex := by
  exact finiteM8OperatorActionIntegral_invariant weightX weightZ sampleX sampleZ T hT
    (poincareQEDIndexedInteractionLagrangian vertex)

/-- Time-ordering the finite indexed interaction action is the finite action
integral of the time-ordered indexed interaction density. -/
lemma timeOrderF_finiteM8IndexedInteractionAction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    timeOrderF (finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex) =
      finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => timeOrderF (poincareQEDIndexedInteractionLagrangian vertex q)) := by
  exact timeOrderF_finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
    (poincareQEDIndexedInteractionLagrangian vertex)

/-- Dyson coefficient `(-i/(hbar*c))^n / n!` for the operator-valued interaction action. -/
noncomputable def poincareQEDDysonCoefficient (hbar c : ℝ) (n : ℕ) : ℂ :=
  ((-(Complex.I / ((hbar * c : ℝ) : ℂ))) ^ n) / ((Nat.factorial n : ℕ) : ℂ)

/-- The zeroth Dyson coefficient is one. -/
@[simp] lemma poincareQEDDysonCoefficient_zero (hbar c : ℝ) :
    poincareQEDDysonCoefficient hbar c 0 = 1 := by
  simp [poincareQEDDysonCoefficient]

/-- The first Dyson coefficient is `-i/(hbar*c)`. -/
lemma poincareQEDDysonCoefficient_one (hbar c : ℝ) :
    poincareQEDDysonCoefficient hbar c 1 =
      -(Complex.I / ((hbar * c : ℝ) : ℂ)) := by
  simp [poincareQEDDysonCoefficient]

/-- The exact second-order Dyson coefficient is
`-1 / (2 (hbar c)^2)`.  This is perturbative order two; by itself it is not a
claim that the corresponding Wick contractions form a two-loop diagram. -/
lemma poincareQEDDysonCoefficient_two (hbar c : ℝ) :
    poincareQEDDysonCoefficient hbar c 2 =
      -(1 : ℂ) / (2 * (((hbar * c : ℝ) : ℂ) ^ 2)) := by
  simp [poincareQEDDysonCoefficient, div_pow]
  ring

/-- The `n`th formal Dyson term in the existing free field-operator algebra. -/
noncomputable def poincareQEDDysonTerm
    (hbar c : ℝ) (n : ℕ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  timeOrderF (poincareQEDDysonCoefficient hbar c n • interactionAction ^ n)

/-- The zeroth formal Dyson term is the identity operator. -/
@[simp] lemma poincareQEDDysonTerm_zero
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDDysonTerm hbar c 0 interactionAction = 1 := by
  simp [poincareQEDDysonTerm, poincareQEDDysonCoefficient]
  change timeOrderF (𝓕 := poincareQEDFieldSpec)
    (1 : poincareQEDFieldSpec.FieldOpFreeAlgebra) = 1
  rw [← (ofFieldOpListF_nil (𝓕 := poincareQEDFieldSpec))]
  exact timeOrderF_ofFieldOpListF_nil (𝓕 := poincareQEDFieldSpec)

/-- The first formal Dyson term is the existing first-order insertion. -/
lemma poincareQEDDysonTerm_one_eq_firstOrder
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDDysonTerm hbar c 1 interactionAction =
      poincareQEDDysonFirstOrder (poincareQEDDysonCoefficient hbar c 1) interactionAction := by
  simp [poincareQEDDysonTerm, poincareQEDDysonFirstOrder]

/-- The first formal Dyson term is a scalar multiple of the time-ordered interaction action. -/
lemma poincareQEDDysonTerm_one_eq_smul_timeOrder
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDDysonTerm hbar c 1 interactionAction =
      poincareQEDDysonCoefficient hbar c 1 • timeOrderF interactionAction := by
  rw [poincareQEDDysonTerm_one_eq_firstOrder]
  exact poincareQEDDysonFirstOrder_eq_smul_timeOrder
    (poincareQEDDysonCoefficient hbar c 1) interactionAction

/-- The second Dyson term is the exact coefficient multiplying the
time-ordered square of the interaction action.  Diagrammatic loop number
requires a subsequent Wick-contraction classification and is deliberately not
inferred from the Dyson order. -/
lemma poincareQEDDysonTerm_two_eq_timeOrderedSquare
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDDysonTerm hbar c 2 interactionAction =
      poincareQEDDysonCoefficient hbar c 2 •
        timeOrderF (interactionAction ^ 2) := by
  rw [poincareQEDDysonTerm, map_smul]

/-- Formal Dyson term family for the operator-valued interaction action. -/
noncomputable def poincareQEDDysonFormalSeries
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  fun n => poincareQEDDysonTerm hbar c n interactionAction

/-- Finite Dyson partial sum through order `N`. -/
noncomputable def poincareQEDDysonPartialSum
    (hbar c : ℝ) (N : ℕ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  ∑ n : Fin (N + 1), poincareQEDDysonTerm hbar c n.val interactionAction

/-- The order-zero Dyson partial sum is the identity operator. -/
@[simp] lemma poincareQEDDysonPartialSum_zero
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDDysonPartialSum hbar c 0 interactionAction = 1 := by
  simp [poincareQEDDysonPartialSum]

/-- The first nontrivial Dyson partial sum is the free identity plus the first-order
time-ordered interaction action. -/
lemma poincareQEDDysonPartialSum_one
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDDysonPartialSum hbar c 1 interactionAction =
      1 + poincareQEDDysonTerm hbar c 1 interactionAction := by
  simp [poincareQEDDysonPartialSum, Fin.sum_univ_two]

/-- The order-two truncation contains exactly the free, first-order, and
second-order Dyson terms. -/
lemma poincareQEDDysonPartialSum_two
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDDysonPartialSum hbar c 2 interactionAction =
      1 + poincareQEDDysonTerm hbar c 1 interactionAction +
        poincareQEDDysonTerm hbar c 2 interactionAction := by
  simp [poincareQEDDysonPartialSum, Fin.sum_univ_three]

/-- Finite scattering operator obtained from the finite indexed interaction action. -/
noncomputable def poincareQEDScatteringOperatorPartial {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  poincareQEDDysonPartialSum hbar c N
    (finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex)

/-- Order-zero finite scattering operator is the identity, independently of the vertex tensor. -/
@[simp] lemma poincareQEDScatteringOperatorPartial_zero {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDScatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c 0 vertex = 1 := by
  simp [poincareQEDScatteringOperatorPartial]

/-- First-order finite scattering operator from the indexed `M8` interaction action. -/
lemma poincareQEDScatteringOperatorPartial_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDScatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c 1 vertex =
      1 + poincareQEDDysonTerm hbar c 1
        (finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex) := by
  rw [poincareQEDScatteringOperatorPartial, poincareQEDDysonPartialSum_one]

/-- Finite scattering matrix element in the free field-operator algebra. -/
noncomputable def poincareQEDScatteringMatrixElementPartial
    (bra ket scatteringOperator : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  bra * scatteringOperator * ket

/-- The zeroth-order finite scattering matrix element has the free product form. -/
@[simp] lemma poincareQEDScatteringMatrixElementPartial_one
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDScatteringMatrixElementPartial bra ket 1 = bra * ket := by
  simp [poincareQEDScatteringMatrixElementPartial]

/-! ### G.2.1. Section 10 Vertex, Invariant Measure, and Formal Scattering Package -/

/-- Section 10's operator-valued QED vertex tensor on `M8`, with explicit
left-spinor, Maxwell, and right-spinor indices. -/
structure PoincareQEDInteractionTensor where
  /-- Coefficient of the indexed vertex `psi-bar_a A_m psi_b` at an `M8` point. -/
  vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ

/-- The operator-valued Lagrangian density associated to a Section 10 interaction tensor. -/
noncomputable def PoincareQEDInteractionTensor.lagrangianDensity
    (V : PoincareQEDInteractionTensor) :
    PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  poincareQEDIndexedInteractionLagrangian V.vertex

/-- The tensor Lagrangian density is the existing indexed interaction density. -/
lemma PoincareQEDInteractionTensor.lagrangianDensity_eq
    (V : PoincareQEDInteractionTensor) :
    V.lagrangianDensity = poincareQEDIndexedInteractionLagrangian V.vertex :=
  rfl

/-- The finite `M8` action associated to a Section 10 interaction tensor. -/
noncomputable def PoincareQEDInteractionTensor.action {ι κ : Type*} [Fintype ι] [Fintype κ]
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ V.vertex

/-- Tensor actions are the finite operator integral of the tensor Lagrangian density. -/
lemma PoincareQEDInteractionTensor.action_eq_operatorIntegral {ι κ : Type*}
    [Fintype ι] [Fintype κ] (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) :
    V.action weightX weightZ sampleX sampleZ =
      finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ V.lagrangianDensity :=
  rfl

/-- Time-ordering a Section 10 tensor action is the finite action integral of the
time-ordered tensor Lagrangian density. -/
lemma PoincareQEDInteractionTensor.timeOrder_action {ι κ : Type*}
    [Fintype ι] [Fintype κ] (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) :
    timeOrderF (V.action weightX weightZ sampleX sampleZ) =
      finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => timeOrderF (V.lagrangianDensity q)) := by
  exact timeOrderF_finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
    V.lagrangianDensity

/-- Finite scattering operator through order `N` for a Section 10 interaction tensor. -/
noncomputable def PoincareQEDInteractionTensor.scatteringOperatorPartial {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  poincareQEDScatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c N V.vertex

/-- The tensor-level finite scattering operator is the general Section 10 operator
applied to the tensor vertex. -/
lemma PoincareQEDInteractionTensor.scatteringOperatorPartial_eq_general {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ) :
    V.scatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c N =
      poincareQEDScatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c N
        V.vertex :=
  rfl

/-- Zeroth-order tensor scattering is the identity operator. -/
@[simp] lemma PoincareQEDInteractionTensor.scatteringOperatorPartial_zero {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) :
    V.scatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c 0 = 1 := by
  simp [PoincareQEDInteractionTensor.scatteringOperatorPartial]

/-- First-order tensor scattering inserts the finite tensor action. -/
lemma PoincareQEDInteractionTensor.scatteringOperatorPartial_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) :
    V.scatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c 1 =
      1 + poincareQEDDysonTerm hbar c 1
        (V.action weightX weightZ sampleX sampleZ) := by
  rw [PoincareQEDInteractionTensor.scatteringOperatorPartial_eq_general,
    poincareQEDScatteringOperatorPartial_one]
  rfl

/-- All-order formal scattering series for a Section 10 interaction tensor. -/
noncomputable def PoincareQEDInteractionTensor.scatteringOperatorFormalSeries {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) :
    ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  poincareQEDDysonFormalSeries hbar c (V.action weightX weightZ sampleX sampleZ)

/-- A Poincare-invariant sampled operator measure leaves the tensor action invariant. -/
lemma PoincareQEDInteractionTensor.action_poincare_invariant {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (M : SL(2, ℂ)) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hμ : IsFiniteM8OperatorMeasurePoincareInvariant weightX weightZ sampleX sampleZ M A) :
    finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => V.lagrangianDensity (poincareM8LinearAction M A q)) =
      V.action weightX weightZ sampleX sampleZ := by
  exact finiteM8OperatorActionIntegral_invariant weightX weightZ sampleX sampleZ
    (poincareM8LinearAction M A) hμ V.lagrangianDensity

/-- A sampled `M8` operator-valued measure is invariant under every supplied
linear Poincare-group action on the spacetime and internal factors. -/
def IsFiniteM8OperatorMeasureInvariantForPoincareActions {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint) : Prop :=
  ∀ (M : SL(2, ℂ)) (A : Matrix (Fin 3) (Fin 3) ℂ),
    IsFiniteM8OperatorMeasurePoincareInvariant weightX weightZ sampleX sampleZ M A

/-- Invariance under all finite Poincare actions specializes to any fixed action. -/
lemma isFiniteM8OperatorMeasureInvariantForPoincareActions_apply {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hμ : IsFiniteM8OperatorMeasureInvariantForPoincareActions
      weightX weightZ sampleX sampleZ)
    (M : SL(2, ℂ)) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    IsFiniteM8OperatorMeasurePoincareInvariant weightX weightZ sampleX sampleZ M A :=
  hμ M A

/-- Poincare-invariant sampled measures leave finite operator-valued action
integrals unchanged after the corresponding `M8` action. -/
lemma finiteM8OperatorActionIntegral_poincare_invariant {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (M : SL(2, ℂ)) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hμ : IsFiniteM8OperatorMeasurePoincareInvariant weightX weightZ sampleX sampleZ M A)
    (lagrangianDensity : PoincareM8 -> poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => lagrangianDensity (poincareM8LinearAction M A q)) =
      finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ lagrangianDensity := by
  exact finiteM8OperatorActionIntegral_invariant weightX weightZ sampleX sampleZ
    (poincareM8LinearAction M A) hμ lagrangianDensity

/-- Poincare-invariant sampled measures leave the indexed Section 10 interaction
action unchanged. -/
lemma finiteM8IndexedInteractionAction_poincare_invariant {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (M : SL(2, ℂ)) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hμ : IsFiniteM8OperatorMeasurePoincareInvariant weightX weightZ sampleX sampleZ M A)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => poincareQEDIndexedInteractionLagrangian vertex
          (poincareM8LinearAction M A q)) =
      finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex := by
  exact finiteM8IndexedInteractionAction_invariant weightX weightZ sampleX sampleZ
    (poincareM8LinearAction M A) hμ vertex

/-- The all-order formal scattering operator series associated to a Section 10
indexed interaction action.  Analytic convergence is not part of this formal
algebraic object. -/
noncomputable def poincareQEDScatteringOperatorFormalSeries {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  poincareQEDDysonFormalSeries hbar c
    (finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex)

/-- The zeroth formal scattering operator is the identity. -/
@[simp] lemma poincareQEDScatteringOperatorFormalSeries_zero {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDScatteringOperatorFormalSeries weightX weightZ sampleX sampleZ
      hbar c vertex 0 = 1 := by
  simp [poincareQEDScatteringOperatorFormalSeries, poincareQEDDysonFormalSeries]

/-- The first formal scattering operator is the first Dyson insertion of the
indexed `M8` interaction action. -/
lemma poincareQEDScatteringOperatorFormalSeries_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDScatteringOperatorFormalSeries weightX weightZ sampleX sampleZ
      hbar c vertex 1 =
      poincareQEDDysonCoefficient hbar c 1 •
        timeOrderF (finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex) := by
  simp [poincareQEDScatteringOperatorFormalSeries, poincareQEDDysonFormalSeries,
    poincareQEDDysonTerm_one_eq_smul_timeOrder]

/-- Formal scattering matrix-element series obtained by inserting each Dyson term
between a bra and a ket element of the free field-operator algebra. -/
noncomputable def poincareQEDScatteringMatrixElementFormalSeries
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    ℕ -> poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  fun n => poincareQEDScatteringMatrixElementPartial bra ket
    (poincareQEDDysonTerm hbar c n interactionAction)

/-- The zeroth formal scattering matrix element is the free product. -/
@[simp] lemma poincareQEDScatteringMatrixElementFormalSeries_zero
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c interactionAction 0 =
      bra * ket := by
  simp [poincareQEDScatteringMatrixElementFormalSeries]

/-- The first formal scattering matrix element inserts the time-ordered interaction
action between the chosen bra and ket. -/
lemma poincareQEDScatteringMatrixElementFormalSeries_one
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c interactionAction 1 =
      bra * (poincareQEDDysonCoefficient hbar c 1 • timeOrderF interactionAction) * ket := by
  unfold poincareQEDScatteringMatrixElementFormalSeries
  rw [poincareQEDDysonTerm_one_eq_smul_timeOrder]
  rfl

/-! ### G.2.2. Analytic Dyson and Scattering Limits -/

/-- Realized `n`th Dyson scattering term in a complete normed operator target. -/
noncomputable def realizedPoincareQEDDysonScatteringTerm {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    ℕ -> A :=
  fun n => realize (poincareQEDDysonTerm hbar c n interactionAction)

/-- Analytic scattering operator obtained as the infinite realized Dyson series. -/
noncomputable def realizedPoincareQEDDysonScatteringSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) : A :=
  ∑' n, realizedPoincareQEDDysonScatteringTerm realize hbar c interactionAction n

/-- Finite analytic truncation of the realized Dyson scattering series. -/
noncomputable def realizedPoincareQEDDysonScatteringPartialSum {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (N : ℕ) : A :=
  ∑ n ∈ Finset.range N,
    realizedPoincareQEDDysonScatteringTerm realize hbar c interactionAction n

/-- A summable real majorant gives summability of the realized Dyson scattering
series. -/
lemma realizedPoincareQEDDysonScatteringSeries_summable_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realizedPoincareQEDDysonScatteringTerm realize hbar c interactionAction n‖ ≤
          majorant n) :
    Summable (realizedPoincareQEDDysonScatteringTerm realize hbar c interactionAction) :=
  Summable.of_norm_bounded hmajorant hbound

/-- A summable real majorant identifies the realized scattering operator as the
sum of the Dyson term family. -/
lemma realizedPoincareQEDDysonScatteringSeries_hasSum_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realizedPoincareQEDDysonScatteringTerm realize hbar c interactionAction n‖ ≤
          majorant n) :
    HasSum (realizedPoincareQEDDysonScatteringTerm realize hbar c interactionAction)
      (realizedPoincareQEDDysonScatteringSeries realize hbar c interactionAction) := by
  exact (realizedPoincareQEDDysonScatteringSeries_summable_of_norm_bound realize
    hbar c interactionAction majorant hmajorant hbound).hasSum

/-- Finite Dyson truncations converge to the realized analytic scattering
operator under a summable norm-majorant estimate. -/
lemma realizedPoincareQEDDysonScatteringSeries_tendsto_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realizedPoincareQEDDysonScatteringTerm realize hbar c interactionAction n‖ ≤
          majorant n) :
    Filter.Tendsto
      (fun N => realizedPoincareQEDDysonScatteringPartialSum realize hbar c
        interactionAction N)
      Filter.atTop
      (nhds (realizedPoincareQEDDysonScatteringSeries realize hbar c interactionAction)) := by
  have hsum := realizedPoincareQEDDysonScatteringSeries_hasSum_of_norm_bound realize
    hbar c interactionAction majorant hmajorant hbound
  simpa [realizedPoincareQEDDysonScatteringPartialSum] using hsum.tendsto_sum_nat

/-- Realized scattering matrix-element series in a complete normed operator
target. -/
noncomputable def realizedPoincareQEDScatteringMatrixElementSeries {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) : A :=
  ∑' n, realize
    (poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c interactionAction n)

/-- Finite truncation of the realized scattering matrix-element series. -/
noncomputable def realizedPoincareQEDScatteringMatrixElementPartialSum {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (N : ℕ) : A :=
  ∑ n ∈ Finset.range N, realize
    (poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c interactionAction n)

/-- A summable real majorant gives convergence of realized scattering matrix
elements. -/
lemma realizedPoincareQEDScatteringMatrixElementSeries_hasSum_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realize
          (poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c
            interactionAction n)‖ ≤ majorant n) :
    HasSum
      (fun n => realize
        (poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c
          interactionAction n))
      (realizedPoincareQEDScatteringMatrixElementSeries realize bra ket hbar c
        interactionAction) := by
  exact (Summable.of_norm_bounded hmajorant hbound).hasSum

/-- Finite matrix-element truncations converge to the realized analytic
scattering matrix element. -/
lemma realizedPoincareQEDScatteringMatrixElementSeries_tendsto_of_norm_bound {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realize
          (poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c
            interactionAction n)‖ ≤ majorant n) :
    Filter.Tendsto
      (fun N => realizedPoincareQEDScatteringMatrixElementPartialSum realize bra ket
        hbar c interactionAction N)
      Filter.atTop
      (nhds (realizedPoincareQEDScatteringMatrixElementSeries realize bra ket hbar c
        interactionAction)) := by
  have hsum :=
    realizedPoincareQEDScatteringMatrixElementSeries_hasSum_of_norm_bound realize
      bra ket hbar c interactionAction majorant hmajorant hbound
  simpa [realizedPoincareQEDScatteringMatrixElementPartialSum] using hsum.tendsto_sum_nat

/-- Realized analytic scattering operator associated to a Section 10 interaction
tensor. -/
noncomputable def realizedPoincareQEDInteractionTensorScatteringSeries {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) : A :=
  realizedPoincareQEDDysonScatteringSeries realize hbar c
    (V.action weightX weightZ sampleX sampleZ)

/-- Finite analytic truncation of the realized Section 10 tensor scattering
operator. -/
noncomputable def realizedPoincareQEDInteractionTensorScatteringPartialSum {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ) : A :=
  realizedPoincareQEDDysonScatteringPartialSum realize hbar c
    (V.action weightX weightZ sampleX sampleZ) N

/-- Section 10 tensor scattering truncations converge to the realized analytic
scattering operator under a summable norm-majorant estimate. -/
lemma realizedPoincareQEDInteractionTensorScatteringSeries_tendsto_of_norm_bound
    {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realizedPoincareQEDDysonScatteringTerm realize hbar c
          (V.action weightX weightZ sampleX sampleZ) n‖ ≤ majorant n) :
    Filter.Tendsto
      (fun N => realizedPoincareQEDInteractionTensorScatteringPartialSum realize V
        weightX weightZ sampleX sampleZ hbar c N)
      Filter.atTop
      (nhds (realizedPoincareQEDInteractionTensorScatteringSeries realize V
        weightX weightZ sampleX sampleZ hbar c)) := by
  exact realizedPoincareQEDDysonScatteringSeries_tendsto_of_norm_bound realize hbar c
    (V.action weightX weightZ sampleX sampleZ) majorant hmajorant hbound

/-- Realized analytic scattering matrix element for a Section 10 interaction
tensor. -/
noncomputable def realizedPoincareQEDInteractionTensorMatrixElementSeries {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) : A :=
  realizedPoincareQEDScatteringMatrixElementSeries realize bra ket hbar c
    (V.action weightX weightZ sampleX sampleZ)

/-- Finite analytic truncation of a Section 10 tensor scattering matrix
element. -/
noncomputable def realizedPoincareQEDInteractionTensorMatrixElementPartialSum {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ) : A :=
  realizedPoincareQEDScatteringMatrixElementPartialSum realize bra ket hbar c
    (V.action weightX weightZ sampleX sampleZ) N

/-- Section 10 tensor matrix-element truncations converge to the realized
analytic matrix element under a summable norm-majorant estimate. -/
lemma realizedPoincareQEDInteractionTensorMatrixElementSeries_tendsto_of_norm_bound
    {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (V : PoincareQEDInteractionTensor)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realize
          (poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c
            (V.action weightX weightZ sampleX sampleZ) n)‖ ≤ majorant n) :
    Filter.Tendsto
      (fun N => realizedPoincareQEDInteractionTensorMatrixElementPartialSum realize
        bra ket V weightX weightZ sampleX sampleZ hbar c N)
      Filter.atTop
      (nhds (realizedPoincareQEDInteractionTensorMatrixElementSeries realize bra ket V
        weightX weightZ sampleX sampleZ hbar c)) := by
  exact realizedPoincareQEDScatteringMatrixElementSeries_tendsto_of_norm_bound realize
    bra ket hbar c (V.action weightX weightZ sampleX sampleZ) majorant hmajorant hbound

/-! ### G.2.3. External Second-Quantized Mode Insertions -/

/-- Finite Dirac external-mode scattering matrix element: outgoing finite Dirac
mode, scattering operator, incoming finite Dirac mode. -/
noncomputable def finiteDiracExternalScatteringMatrixElementPartial {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3)
    (scatteringOperator : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  poincareQEDScatteringMatrixElementPartial
    (finiteDiracOutgoingModeOperator outCoeff outSpin outMom)
    (finiteDiracIncomingModeOperator inCoeff inSpin inMom)
    scatteringOperator

/-- Zeroth-order finite Dirac external scattering reduces to the product of the
outgoing and incoming finite mode operators. -/
@[simp] lemma finiteDiracExternalScatteringMatrixElementPartial_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3) :
    finiteDiracExternalScatteringMatrixElementPartial outCoeff outSpin outMom
        inCoeff inSpin inMom 1 =
      finiteDiracOutgoingModeOperator outCoeff outSpin outMom *
        finiteDiracIncomingModeOperator inCoeff inSpin inMom := by
  simp [finiteDiracExternalScatteringMatrixElementPartial]

/-- First-order finite Dirac external scattering inserts the time-ordered
interaction action between outgoing and incoming Dirac mode sums. -/
lemma finiteDiracExternalScatteringMatrixElementFormalSeries_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDScatteringMatrixElementFormalSeries
        (finiteDiracOutgoingModeOperator outCoeff outSpin outMom)
        (finiteDiracIncomingModeOperator inCoeff inSpin inMom)
        hbar c interactionAction 1 =
      finiteDiracOutgoingModeOperator outCoeff outSpin outMom *
        (poincareQEDDysonCoefficient hbar c 1 • timeOrderF interactionAction) *
          finiteDiracIncomingModeOperator inCoeff inSpin inMom := by
  rw [poincareQEDScatteringMatrixElementFormalSeries_one]

/-- Finite Dirac external-mode matrix element for a Section 10 interaction vertex
through Dyson order `N`. -/
noncomputable def finiteDiracExternalScatteringMatrixElementForVertexPartial
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finiteDiracExternalScatteringMatrixElementPartial outCoeff outSpin outMom
    inCoeff inSpin inMom
    (poincareQEDScatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c N vertex)

/-- Zeroth-order Section 10 Dirac external matrix element is the free external product. -/
@[simp] lemma finiteDiracExternalScatteringMatrixElementForVertexPartial_zero
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    finiteDiracExternalScatteringMatrixElementForVertexPartial outCoeff outSpin outMom
        inCoeff inSpin inMom weightX weightZ sampleX sampleZ hbar c 0 vertex =
      finiteDiracOutgoingModeOperator outCoeff outSpin outMom *
        finiteDiracIncomingModeOperator inCoeff inSpin inMom := by
  simp [finiteDiracExternalScatteringMatrixElementForVertexPartial,
    finiteDiracExternalScatteringMatrixElementPartial]

/-- First-order Section 10 Dirac external matrix element inserts the indexed
interaction action. -/
lemma finiteDiracExternalScatteringMatrixElementForVertexPartial_one
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    finiteDiracExternalScatteringMatrixElementForVertexPartial outCoeff outSpin outMom
        inCoeff inSpin inMom weightX weightZ sampleX sampleZ hbar c 1 vertex =
      finiteDiracOutgoingModeOperator outCoeff outSpin outMom *
        (1 + poincareQEDDysonTerm hbar c 1
          (finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex)) *
          finiteDiracIncomingModeOperator inCoeff inSpin inMom := by
  unfold finiteDiracExternalScatteringMatrixElementForVertexPartial
  rw [poincareQEDScatteringOperatorPartial_one]
  rfl

/-- Finite photon external-mode scattering matrix element: outgoing finite photon
mode, scattering operator, incoming finite photon mode. -/
noncomputable def finitePhotonExternalScatteringMatrixElementPartial {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3)
    (scatteringOperator : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  poincareQEDScatteringMatrixElementPartial
    (finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom)
    (finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom)
    scatteringOperator

/-- Zeroth-order finite photon external scattering reduces to the product of the
outgoing and incoming finite photon mode operators. -/
@[simp] lemma finitePhotonExternalScatteringMatrixElementPartial_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3) :
    finitePhotonExternalScatteringMatrixElementPartial outCoeff outHelicity outMom
        inCoeff inHelicity inMom 1 =
      finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom *
        finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom := by
  simp [finitePhotonExternalScatteringMatrixElementPartial]

/-- First-order finite photon external scattering inserts the time-ordered
interaction action between outgoing and incoming photon mode sums. -/
lemma finitePhotonExternalScatteringMatrixElementFormalSeries_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3)
    (hbar c : ℝ) (interactionAction : poincareQEDFieldSpec.FieldOpFreeAlgebra) :
    poincareQEDScatteringMatrixElementFormalSeries
        (finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom)
        (finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom)
        hbar c interactionAction 1 =
      finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom *
        (poincareQEDDysonCoefficient hbar c 1 • timeOrderF interactionAction) *
          finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom := by
  rw [poincareQEDScatteringMatrixElementFormalSeries_one]

/-- Finite photon external-mode matrix element for a Section 10 interaction vertex
through Dyson order `N`. -/
noncomputable def finitePhotonExternalScatteringMatrixElementForVertexPartial
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finitePhotonExternalScatteringMatrixElementPartial outCoeff outHelicity outMom
    inCoeff inHelicity inMom
    (poincareQEDScatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c N vertex)

/-- Zeroth-order Section 10 photon external matrix element is the free external product. -/
@[simp] lemma finitePhotonExternalScatteringMatrixElementForVertexPartial_zero
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    finitePhotonExternalScatteringMatrixElementForVertexPartial outCoeff outHelicity outMom
        inCoeff inHelicity inMom weightX weightZ sampleX sampleZ hbar c 0 vertex =
      finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom *
        finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom := by
  simp [finitePhotonExternalScatteringMatrixElementForVertexPartial,
    finitePhotonExternalScatteringMatrixElementPartial]

/-- First-order Section 10 photon external matrix element inserts the indexed
interaction action. -/
lemma finitePhotonExternalScatteringMatrixElementForVertexPartial_one
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (vertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ) :
    finitePhotonExternalScatteringMatrixElementForVertexPartial outCoeff outHelicity outMom
        inCoeff inHelicity inMom weightX weightZ sampleX sampleZ hbar c 1 vertex =
      finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom *
        (1 + poincareQEDDysonTerm hbar c 1
          (finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ vertex)) *
          finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom := by
  unfold finitePhotonExternalScatteringMatrixElementForVertexPartial
  rw [poincareQEDScatteringOperatorPartial_one]
  rfl

/-! ## H. Bridges to Existing Dirac, Maxwell, and Spinor Infrastructure -/

/-! ### H.1. Bennett Parametrized-Time Modes and Mass Shell -/

/-- The pure Bennett parameter-frequency momentum: only the time component is nonzero. -/
def bennettTauMomentum (m_p : ℝ) : MinkowskiPoint
  | Sum.inl _ => m_p
  | Sum.inr _ => 0

/-- The coordinate point representing the Bennett parameter value in the time slot. -/
def bennettTauPoint (tau : ℝ) : MinkowskiPoint
  | Sum.inl _ => tau
  | Sum.inr _ => 0

/-- The `T4` dot product of the pure Bennett `tau` mode is `m_p * tau`. -/
lemma minkowskiDot_bennettTau (m_p tau : ℝ) :
    minkowskiDot (bennettTauMomentum m_p) (bennettTauPoint tau) = m_p * tau := by
  simp [minkowskiDot, bennettTauMomentum, bennettTauPoint]

/-- The Varlamov `T4` plane wave restricts to Bennett's `exp(i m_p tau)` phase. -/
lemma minkowskiPlaneWave_bennettTau_eq (m_p tau : ℝ) :
    minkowskiPlaneWave (bennettTauMomentum m_p) (bennettTauPoint tau) =
      Complex.exp (Complex.I * ((m_p * tau : ℝ) : ℂ)) := by
  simp [minkowskiPlaneWave, minkowskiDot_bennettTau]

/-- The pure Bennett `tau` plane wave is unimodular by the parametrized-QED phase lemma. -/
lemma minkowskiPlaneWave_bennettTau_norm (m_p tau : ℝ) :
    ‖minkowskiPlaneWave (bennettTauMomentum m_p) (bennettTauPoint tau)‖ = 1 := by
  rw [minkowskiPlaneWave_bennettTau_eq]
  exact bennett_tau_phase_unimodular m_p tau

/-- An `M8` mode whose Minkowski factor is Bennett's parameter-frequency phase. -/
noncomputable def bennettTauM8Mode
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) : PoincareM8 -> ℂ :=
  finiteM8FourierMode (bennettTauMomentum m_p) internal

/-- Evaluating a Bennett `tau` `M8` mode gives the usual `exp(i m_p tau)` factor. -/
lemma bennettTauM8Mode_at_tau
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p tau : ℝ) (z : ComplexTwoSpherePoint) :
    bennettTauM8Mode internal m_p (bennettTauPoint tau, z) =
      Complex.exp (Complex.I * ((m_p * tau : ℝ) : ℂ)) * internal z := by
  simp [bennettTauM8Mode, finiteM8FourierMode, minkowskiPlaneWave_bennettTau_eq]

/-- A Bennett `tau` `M8` mode has the same pointwise norm as its internal
complex-two-sphere factor. -/
lemma bennettTauM8Mode_norm_at_tau
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p tau : ℝ) (z : ComplexTwoSpherePoint) :
    ‖bennettTauM8Mode internal m_p (bennettTauPoint tau, z)‖ = ‖internal z‖ := by
  rw [bennettTauM8Mode_at_tau, norm_mul, bennett_tau_phase_unimodular, one_mul]

/-- Bennett's invariant mass-squared is the existing complex-energy Lorentzian form. -/
lemma poincareGroup_bennett_massSq_eq_lorentzianForm
    (p0 pmag : ℝ) (h : pmag ^ 2 ≤ p0 ^ 2) :
    (Real.sqrt (p0 ^ 2 - pmag ^ 2)) ^ 2 =
      lorentzianForm (complexEnergy p0 pmag) :=
  bennett_massSq_eq_lorentzianForm p0 pmag h

/-- Bennett's on-shell energy is the existing Bogoliubov/Dirac dispersion. -/
lemma poincareGroup_bennett_energy_eq_bogoliubov
    (p0 pmag : ℝ) (h : pmag ^ 2 ≤ p0 ^ 2) :
    |p0| = bogoliubovEnergy pmag (Real.sqrt (p0 ^ 2 - pmag ^ 2)) :=
  bennett_energy_eq_bogoliubov p0 pmag h

/-- Bennett's real-mass condition is the timelike cone of the existing contour variable. -/
lemma poincareGroup_bennett_mass_real_iff_timelike (p0 pmag : ℝ) :
    pmag ^ 2 ≤ p0 ^ 2 ↔ 0 ≤ lorentzianForm (complexEnergy p0 pmag) :=
  bennett_mass_real_iff_timelike p0 pmag

/-- Bennett's parameter clock is the inverse Lorentz factor. -/
lemma poincareGroup_bennett_dt_dtau_eq_sech (m eta : ℝ) (hm : 0 < m) :
    m / bogoliubovEnergy (m * Real.sinh eta) m = 1 / Real.cosh eta :=
  bennett_dt_dtau_eq_sech m eta hm

/-- Bennett's `i epsilon` pole displacement is the existing complex-energy gap. -/
lemma poincareGroup_bennett_iEps_pole_gap (msq epsilon : ℝ) :
    (complexEnergy msq epsilon).im = -epsilon :=
  bennett_iEps_pole_gap msq epsilon

/-! ### H.2. Bennett Spinors and Projectors -/

/-- Bennett's forward/backward spinor orthonormality as a single bridge for
Poincare-group field modes. -/
lemma poincareGroup_bennett_spinor_orthonormality
    (m E K : ℝ) (p : Fin 3 -> ℝ)
    (hMass : dotR p p = E ^ 2 - m ^ 2)
    (hK : K ^ 2 * (2 * m * (m + E)) = 1) :
    (uSpinor m E K p)ᴴ * gamma0Block * (uSpinor m E K p) = 1
      ∧ (vSpinor m E K p)ᴴ * gamma0Block * (vSpinor m E K p) = -1
      ∧ (uSpinor m E K p)ᴴ * gamma0Block * (vSpinor m E K p) = 0
      ∧ (vSpinor m E K p)ᴴ * gamma0Block * (uSpinor m E K p) = 0 :=
  ⟨ubar_u m E K p hMass hK, vbar_v m E K p hMass hK,
    ubar_v m E K p, vbar_u m E K p⟩

/-- The Dirac part of the Poincare-group field uses the existing Dirac energy projectors. -/
lemma poincareGroup_dirac_energy_projectors (p1 p2 p3 m : ℝ)
    (hE : 0 < p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2) :
    let u := diracInvolution (Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2))
      (Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.diracHamiltonian4 p1 p2 p3 m)
    bennettProjU u + bennettProjV u = 1
      ∧ bennettProjU u * bennettProjU u = bennettProjU u
      ∧ bennettProjV u * bennettProjV u = bennettProjV u
      ∧ bennettProjV u * bennettProjU u = 0 := by
  simpa using dirac_energy_projectors p1 p2 p3 m hE

/-- The Poincare-group field uses Bennett's chirality projectors without restating their algebra. -/
lemma poincareGroup_chirality_projectors :
    bennettProjU spaceTime.γ5 + bennettProjV spaceTime.γ5 = 1
      ∧ bennettProjU spaceTime.γ5 * bennettProjU spaceTime.γ5 = bennettProjU spaceTime.γ5
      ∧ bennettProjV spaceTime.γ5 * bennettProjV spaceTime.γ5 = bennettProjV spaceTime.γ5
      ∧ bennettProjV spaceTime.γ5 * bennettProjU spaceTime.γ5 = 0 :=
  chirality_projectors

/-- The Poincare-group field uses Bennett's helicity projectors for unit momentum. -/
lemma poincareGroup_helicity_projectors (p : Fin 3 -> ℝ) (hp : dotR p p = 1) :
    bennettProjU (sigmaDot p) + bennettProjV (sigmaDot p) = 1
      ∧ bennettProjU (sigmaDot p) * bennettProjU (sigmaDot p) = bennettProjU (sigmaDot p)
      ∧ bennettProjV (sigmaDot p) * bennettProjV (sigmaDot p) = bennettProjV (sigmaDot p)
      ∧ bennettProjV (sigmaDot p) * bennettProjU (sigmaDot p) = 0 :=
  helicity_projectors p hp

/-- The Poincare-group field uses Bennett's rest-frame spin projectors. -/
lemma poincareGroup_spin_projectors :
    bennettProjU (spaceTime.γ5 * spaceTime.γ3)
        + bennettProjV (spaceTime.γ5 * spaceTime.γ3) = 1
      ∧ bennettProjU (spaceTime.γ5 * spaceTime.γ3)
          * bennettProjU (spaceTime.γ5 * spaceTime.γ3)
          = bennettProjU (spaceTime.γ5 * spaceTime.γ3)
      ∧ bennettProjV (spaceTime.γ5 * spaceTime.γ3)
          * bennettProjV (spaceTime.γ5 * spaceTime.γ3)
          = bennettProjV (spaceTime.γ5 * spaceTime.γ3)
      ∧ bennettProjV (spaceTime.γ5 * spaceTime.γ3)
          * bennettProjU (spaceTime.γ5 * spaceTime.γ3) = 0 :=
  spin_projectors

/-- The Poincare-group field uses Bennett's spin projectors for any unit spin
direction. -/
lemma poincareGroup_spin_projectors_general
    (s : Fin 3 -> ℝ) (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1) :
    bennettProjU (spaceTime.γ5 * spinSlash s)
        + bennettProjV (spaceTime.γ5 * spinSlash s) = 1
      ∧ bennettProjU (spaceTime.γ5 * spinSlash s)
          * bennettProjU (spaceTime.γ5 * spinSlash s)
          = bennettProjU (spaceTime.γ5 * spinSlash s)
      ∧ bennettProjV (spaceTime.γ5 * spinSlash s)
          * bennettProjV (spaceTime.γ5 * spinSlash s)
          = bennettProjV (spaceTime.γ5 * spinSlash s)
      ∧ bennettProjV (spaceTime.γ5 * spinSlash s)
          * bennettProjU (spaceTime.γ5 * spinSlash s) = 0 :=
  spin_projectors_general s hs

/-- The Maxwell part reuses the existing Faraday/Bianchi identity. -/
lemma poincareGroup_maxwell_bianchi (k A : Fin 4 -> ℝ) (lam μ ν : Fin 4) :
    k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0 :=
  faraday_bianchi k A lam μ ν

/-- The Maxwell part reuses the existing Faraday gauge invariance. -/
lemma poincareGroup_maxwell_gauge_invariant (k A : Fin 4 -> ℝ) (chi : ℝ) :
    faraday k (fun rho => A rho + chi * k rho) = faraday k A :=
  faraday_gauge_invariant k A chi

/-- The spin-tensor Maxwell interaction in Eq. 175 reuses the gauge-invariant Pauli coupling. -/
lemma poincareGroup_pauliCoupling_gauge_invariant (k A : Fin 4 -> ℝ) (chi : ℝ) :
    pauliCoupling (faraday k (fun rho => A rho + chi * k rho)) =
      pauliCoupling (faraday k A) :=
  pauliCoupling_gauge_invariant k A chi

/-- At the Dirac value `g = 2`, the Poincare-group Pauli interaction is the bare Pauli coupling. -/
lemma poincareGroup_magneticInteraction_dirac (F : Matrix (Fin 4) (Fin 4) ℝ) :
    magneticInteraction (gFactor 0) F = pauliCoupling F :=
  magneticInteraction_dirac F

/-- The Poincare-group Pauli interaction splits into the Dirac part plus anomalous coefficient. -/
lemma poincareGroup_magneticInteraction_gFactor
    (a : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ) :
    magneticInteraction (gFactor a) F = ((1 + a : ℂ)) • pauliCoupling F :=
  magneticInteraction_gFactor a F

/-- The spinor coordinate on the complex two-sphere uses the existing `SL(2,C)` Mobius law. -/
lemma poincareGroup_weylSpinor_mobius (M : SL(2, ℂ)) (a b : ℂ) (hb : b ≠ 0)
    (hden : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a
      + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * b ≠ 0) :
    M.toGL • ((a / b : ℂ) : OnePoint ℂ)
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * a
            + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * b)
          / ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a
            + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * b)
          : ℂ) : OnePoint ℂ) :=
  sl2c_weylRatio M a b hb hden

/-! ### H.3. Discrete-Symmetry Bridges -/

/-- The Poincare-group QED spinor parity action reuses the first-quantized involution. -/
lemma poincareGroup_parity_involutive (ψ : Fin 4 -> ℂ) :
    parityOp (parityOp ψ) = ψ :=
  parity_involutive ψ

/-- The Poincare-group QED charge-conjugation action reuses the first-quantized involution. -/
lemma poincareGroup_chargeConj_involutive (ψ : Fin 4 -> ℂ) :
    chargeConj (chargeConj ψ) = ψ :=
  chargeConj_involutive ψ

/-- The Poincare-group QED time-reversal action reuses the spin-half sign. -/
lemma poincareGroup_timeReversal_sq (ψ : Fin 4 -> ℂ) :
    timeReversal (timeReversal ψ) = -ψ :=
  timeReversal_sq ψ

/-- The Poincare-group QED `CPT` action reuses the `-i gamma5` matrix reduction. -/
lemma poincareGroup_cpt_eq_tpcMatrix (ψ : Fin 4 -> ℂ) :
    cpt ψ = ((-Complex.I) • spaceTime.γ5) *ᵥ ψ :=
  cpt_eq_tpcMatrix ψ

/-- The Poincare-group QED `CPT` action reuses the first-quantized square. -/
lemma poincareGroup_cpt_sq (ψ : Fin 4 -> ℂ) :
    cpt (cpt ψ) = -ψ :=
  cpt_sq ψ

/-! ### H.4. One-Loop and Scattering-Side `CPT` Bridges -/

/-- The Poincare-group field reuses the Bennett `CPT` matrix determinant identity. -/
lemma poincareGroup_cptMatrix_det_sq_one :
    (((-Complex.I) • spaceTime.γ5 : Matrix (Fin 4) (Fin 4) ℂ)).det ^ 2 = 1 :=
  cptMatrix_det_sq_one

/-- `CPT` similarity leaves a finite Dirac-index operator determinant unchanged. -/
lemma poincareGroup_cpt_similarity_det (D : Matrix (Fin 4) (Fin 4) ℂ) :
    (((-Complex.I) • spaceTime.γ5) * D * (-((-Complex.I) • spaceTime.γ5))).det = D.det :=
  cpt_similarity_det D

/-- The Bennett/Dirac dispersion is even under momentum reversal. -/
lemma poincareGroup_bogoliubovEnergy_neg (p m : ℝ) :
    bogoliubovEnergy (-p) m = bogoliubovEnergy p m :=
  bogoliubovEnergy_neg p m

/-- The finite one-loop Bennett/Dirac determinant is even under momentum reversal. -/
lemma poincareGroup_cpt_dirac_oneLoop_det_even (p m : ℝ) :
    berezin (fermionGaussian (bogoliubovEnergy (-p) m)) =
      berezin (fermionGaussian (bogoliubovEnergy p m)) :=
  cpt_dirac_oneLoop_det_even p m

/-- The finite photon-exchange amplitude modulus is invariant under simultaneous
Bennett `CPT` momentum reversal. -/
lemma poincareGroup_cpt_exchange_modulus_invariant
    (pf1 pf2 pγ m HI1 HI2 t hbar : ℝ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    ‖Fermion.PhotonExchange.photonExchangeAmplitude
      (-pf1) (-pf2) (-pγ) m HI1 HI2 t hbar h1 h2‖ =
      ‖Fermion.PhotonExchange.photonExchangeAmplitude
        pf1 pf2 pγ m HI1 HI2 t hbar h1 h2‖ :=
  cpt_exchange_modulus_invariant pf1 pf2 pγ m HI1 HI2 t hbar h1 h2

/-- The finite scattering support condition is invariant under the Bennett `CPT`
momentum reversal. -/
lemma poincareGroup_cpt_momentum_conservation_invariant (pf pγ pf' : ℝ) :
    (-pf) + (-pγ) = (-pf') ↔ pf + pγ = pf' :=
  cpt_momentum_conservation_invariant pf pγ pf'

/-! ### H.5. Bennett Path-Integral and Anomalous-Moment Bridges -/

/-- The Poincare-group Bennett worldline energy is the existing one-loop Berezin determinant. -/
lemma poincareGroup_bennett_worldline_eq_berezinDet
    (p0 pmag : ℝ) (h : pmag ^ 2 ≤ p0 ^ 2) :
    berezin (fermionGaussian |p0|) =
      bogoliubovEnergy pmag (Real.sqrt (p0 ^ 2 - pmag ^ 2)) :=
  bennett_worldline_eq_berezinDet p0 pmag h

/-- The Poincare-group Bennett `tau` phase is the existing unitary worldline weight. -/
lemma poincareGroup_bennett_worldline_weight_unitary (m_p tau : ℝ) :
    ‖Complex.exp (Complex.I * ((m_p * tau : ℝ) : ℂ))‖ = 1 :=
  bennett_worldline_weight_unitary m_p tau

/-- A unit-normalized internal `M8` factor leaves the Bennett worldline weight unchanged. -/
lemma poincareGroup_bennettTauM8Mode_norm_eq_worldline
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p tau : ℝ) (z : ComplexTwoSpherePoint)
    (hz : ‖internal z‖ = 1) :
    ‖bennettTauM8Mode internal m_p (bennettTauPoint tau, z)‖ =
      ‖Complex.exp (Complex.I * ((m_p * tau : ℝ) : ℂ))‖ := by
  rw [bennettTauM8Mode_norm_at_tau, hz, poincareGroup_bennett_worldline_weight_unitary]

/-- The Poincare-group Pauli/Faraday sector reuses the existing anomalous-moment bridge. -/
lemma poincareGroup_anomalous_moment_links (k A : Fin 4 -> ℝ) (chi a : ℝ) :
    spaceTime.γ5 * spaceTime.γ3 = -(spaceTime.γ0 * spinTensor 1 2)
      ∧ pauliCoupling (faraday k (fun rho => A rho + chi * k rho)) = pauliCoupling (faraday k A)
      ∧ magneticInteraction (gFactor a) (faraday k A)
          = ((1 + a : ℂ)) • pauliCoupling (faraday k A) :=
  anomalous_moment_links k A chi a

/-- The Poincare-group magnetic-moment sector reuses the existing structural package:
spin tensor involution, Dirac-beta compatibility, Clifford split, and Schwinger g-factor. -/
lemma poincareGroup_anomalous_moment_structure (mu nu : Fin 4) (alpha : ℝ) :
    spinTensor 1 2 * spinTensor 1 2 = 1
      ∧ spinTensor 1 2
          * Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.diracBeta =
        Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.diracBeta
          * spinTensor 1 2
      ∧ spaceTime.γ mu * spaceTime.γ nu =
          (minkowskiEta mu nu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Complex.I • spinTensor mu nu
      ∧ gFactor 0 = 2
      ∧ gFactor (schwingerAnomaly alpha) = 2 + alpha / Real.pi :=
  anomalous_moment_structure mu nu alpha

/-! ### H.6. Bennett-Specialized Section 10 Interaction and Scattering -/

/-- Matrix-valued Pauli vertex converted to the Section 10 indexed coefficient
tensor by assigning a Maxwell-component weight. -/
noncomputable def poincareQEDPauliMatrixVertex
    (componentWeight : Fin 6 -> ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ :=
  fun a m b _q => componentWeight m * M a b

/-- The Pauli matrix vertex with Bennett's anomalous `g` factor is the Dirac Pauli
vertex multiplied by the anomalous coefficient `1 + a`. -/
lemma poincareQEDPauliMatrixVertex_gFactor
    (componentWeight : Fin 6 -> ℂ) (a : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ) :
    poincareQEDPauliMatrixVertex componentWeight (magneticInteraction (gFactor a) F) =
      poincareQEDPauliMatrixVertex componentWeight (((1 + a : ℂ)) • pauliCoupling F) := by
  funext i m j q
  simp [poincareQEDPauliMatrixVertex, magneticInteraction_gFactor]

/-- Bennett-parametrized Section 10 vertex: an indexed spin/Maxwell tensor times
the `M8` mode whose spacetime factor is the Bennett `tau` phase. -/
noncomputable def bennettTauInteractionVertex
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> PoincareM8 -> ℂ :=
  fun a m b q => spinVertex a m b * bennettTauM8Mode internal m_p q

/-- At a Bennett parameter point, the Section 10 vertex has the factor
`exp(i m_p tau)` from the existing parametrized-QED phase. -/
lemma bennettTauInteractionVertex_at_tau
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p tau : ℝ)
    (a : DiracSpinorIndex) (m : Fin 6) (b : DiracSpinorIndex)
    (z : ComplexTwoSpherePoint) :
    bennettTauInteractionVertex spinVertex internal m_p a m b (bennettTauPoint tau, z) =
      spinVertex a m b *
        (Complex.exp (Complex.I * ((m_p * tau : ℝ) : ℂ)) * internal z) := by
  simp [bennettTauInteractionVertex, bennettTauM8Mode_at_tau]

/-- If the internal mode is unit-normalized at `z`, the Bennett-parametrized
vertex has the norm of its spin/Maxwell tensor coefficient. -/
lemma norm_bennettTauInteractionVertex_at_tau
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p tau : ℝ)
    (a : DiracSpinorIndex) (m : Fin 6) (b : DiracSpinorIndex)
    (z : ComplexTwoSpherePoint) (hz : ‖internal z‖ = 1) :
    ‖bennettTauInteractionVertex spinVertex internal m_p a m b
        (bennettTauPoint tau, z)‖ = ‖spinVertex a m b‖ := by
  rw [bennettTauInteractionVertex_at_tau, norm_mul, norm_mul,
    poincareGroup_bennett_worldline_weight_unitary, hz]
  ring

/-- Finite `M8` action for the Bennett-parametrized Section 10 interaction vertex. -/
noncomputable def finiteM8BennettTauInteractionAction {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ
    (bennettTauInteractionVertex spinVertex internal m_p)

/-- Time-ordering the Bennett-parametrized interaction action reuses the finite
Section 10 time-ordering identity. -/
lemma timeOrderF_finiteM8BennettTauInteractionAction {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    timeOrderF (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
        spinVertex internal m_p) =
      finiteM8OperatorActionIntegral weightX weightZ sampleX sampleZ
        (fun q => timeOrderF
          (poincareQEDIndexedInteractionLagrangian
            (bennettTauInteractionVertex spinVertex internal m_p) q)) := by
  exact timeOrderF_finiteM8IndexedInteractionAction weightX weightZ sampleX sampleZ
    (bennettTauInteractionVertex spinVertex internal m_p)

/-- The Bennett-parametrized finite action is the tensor action for the corresponding
Section 10 interaction tensor. -/
lemma finiteM8BennettTauInteractionAction_eq_tensor_action {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
        spinVertex internal m_p =
      (PoincareQEDInteractionTensor.mk
        (bennettTauInteractionVertex spinVertex internal m_p)).action
          weightX weightZ sampleX sampleZ :=
  rfl

/-- Finite scattering operator for the Bennett-parametrized Section 10 interaction. -/
noncomputable def poincareQEDBennettTauScatteringOperatorPartial {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  poincareQEDDysonPartialSum hbar c N
    (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
      spinVertex internal m_p)

/-- Zeroth-order Bennett-parametrized scattering is the identity. -/
@[simp] lemma poincareQEDBennettTauScatteringOperatorPartial_zero {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    poincareQEDBennettTauScatteringOperatorPartial weightX weightZ sampleX sampleZ
      hbar c 0 spinVertex internal m_p = 1 := by
  simp [poincareQEDBennettTauScatteringOperatorPartial]

/-- First-order Bennett-parametrized scattering is the first Dyson insertion of
the Bennett `tau` interaction action. -/
lemma poincareQEDBennettTauScatteringOperatorPartial_one {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    poincareQEDBennettTauScatteringOperatorPartial weightX weightZ sampleX sampleZ
      hbar c 1 spinVertex internal m_p =
      1 + poincareQEDDysonTerm hbar c 1
        (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
          spinVertex internal m_p) := by
  rw [poincareQEDBennettTauScatteringOperatorPartial, poincareQEDDysonPartialSum_one]

/-- Bennett-parametrized scattering is the general Section 10 scattering operator
applied to the Bennett `tau` vertex. -/
lemma poincareQEDBennettTauScatteringOperatorPartial_eq_general {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    poincareQEDBennettTauScatteringOperatorPartial weightX weightZ sampleX sampleZ
        hbar c N spinVertex internal m_p =
      poincareQEDScatteringOperatorPartial weightX weightZ sampleX sampleZ hbar c N
        (bennettTauInteractionVertex spinVertex internal m_p) := by
  rfl

/-- Dirac external-mode matrix element for Bennett-parametrized Section 10 scattering. -/
noncomputable def finiteDiracExternalBennettTauScatteringMatrixElementPartial
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finiteDiracExternalScatteringMatrixElementPartial outCoeff outSpin outMom
    inCoeff inSpin inMom
    (poincareQEDBennettTauScatteringOperatorPartial weightX weightZ sampleX sampleZ
      hbar c N spinVertex internal m_p)

/-- Zeroth-order Bennett Dirac external scattering is the free external product. -/
@[simp] lemma finiteDiracExternalBennettTauScatteringMatrixElementPartial_zero
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    finiteDiracExternalBennettTauScatteringMatrixElementPartial outCoeff outSpin outMom
        inCoeff inSpin inMom weightX weightZ sampleX sampleZ hbar c 0
        spinVertex internal m_p =
      finiteDiracOutgoingModeOperator outCoeff outSpin outMom *
        finiteDiracIncomingModeOperator inCoeff inSpin inMom := by
  simp [finiteDiracExternalBennettTauScatteringMatrixElementPartial,
    finiteDiracExternalScatteringMatrixElementPartial]

/-- First-order Bennett Dirac external scattering inserts the Bennett `tau`
interaction action. -/
lemma finiteDiracExternalBennettTauScatteringMatrixElementPartial_one
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outSpin : ι -> Fin 4) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inSpin : κ -> Fin 4) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    finiteDiracExternalBennettTauScatteringMatrixElementPartial outCoeff outSpin outMom
        inCoeff inSpin inMom weightX weightZ sampleX sampleZ hbar c 1
        spinVertex internal m_p =
      finiteDiracOutgoingModeOperator outCoeff outSpin outMom *
        (1 + poincareQEDDysonTerm hbar c 1
          (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
            spinVertex internal m_p)) *
          finiteDiracIncomingModeOperator inCoeff inSpin inMom := by
  unfold finiteDiracExternalBennettTauScatteringMatrixElementPartial
  rw [poincareQEDBennettTauScatteringOperatorPartial_one]
  rfl

/-- Photon external-mode matrix element for Bennett-parametrized Section 10 scattering. -/
noncomputable def finitePhotonExternalBennettTauScatteringMatrixElementPartial
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ) (N : ℕ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    poincareQEDFieldSpec.FieldOpFreeAlgebra :=
  finitePhotonExternalScatteringMatrixElementPartial outCoeff outHelicity outMom
    inCoeff inHelicity inMom
    (poincareQEDBennettTauScatteringOperatorPartial weightX weightZ sampleX sampleZ
      hbar c N spinVertex internal m_p)

/-- Zeroth-order Bennett photon external scattering is the free external product. -/
@[simp] lemma finitePhotonExternalBennettTauScatteringMatrixElementPartial_zero
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    finitePhotonExternalBennettTauScatteringMatrixElementPartial outCoeff outHelicity outMom
        inCoeff inHelicity inMom weightX weightZ sampleX sampleZ hbar c 0
        spinVertex internal m_p =
      finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom *
        finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom := by
  simp [finitePhotonExternalBennettTauScatteringMatrixElementPartial,
    finitePhotonExternalScatteringMatrixElementPartial]

/-- First-order Bennett photon external scattering inserts the Bennett `tau`
interaction action. -/
lemma finitePhotonExternalBennettTauScatteringMatrixElementPartial_one
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (outCoeff : ι -> ℂ) (outHelicity : ι -> Fin 2) (outMom : ι -> Momentum 3)
    (inCoeff : κ -> ℂ) (inHelicity : κ -> Fin 2) (inMom : κ -> Momentum 3)
    (weightX : α -> ℂ) (weightZ : β -> ℂ)
    (sampleX : α -> MinkowskiPoint) (sampleZ : β -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    finitePhotonExternalBennettTauScatteringMatrixElementPartial outCoeff outHelicity outMom
        inCoeff inHelicity inMom weightX weightZ sampleX sampleZ hbar c 1
        spinVertex internal m_p =
      finiteMaxwellOutgoingModeOperator outCoeff outHelicity outMom *
        (1 + poincareQEDDysonTerm hbar c 1
          (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
            spinVertex internal m_p)) *
          finiteMaxwellIncomingModeOperator inCoeff inHelicity inMom := by
  unfold finitePhotonExternalBennettTauScatteringMatrixElementPartial
  rw [poincareQEDBennettTauScatteringOperatorPartial_one]
  rfl

/-- The all-order formal scattering series for the Bennett-parametrized interaction
is the general Section 10 scattering series applied to the Bennett `tau` vertex. -/
lemma poincareQEDBennettTauScatteringFormalSeries_eq_general {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) :
    (fun n => poincareQEDDysonTerm hbar c n
      (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
        spinVertex internal m_p)) =
      poincareQEDScatteringOperatorFormalSeries weightX weightZ sampleX sampleZ hbar c
        (bennettTauInteractionVertex spinVertex internal m_p) := by
  rfl

/-- Realized analytic scattering operator for the Bennett-parametrized Section 10
interaction. -/
noncomputable def realizedPoincareQEDBennettTauScatteringSeries {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) : A :=
  realizedPoincareQEDDysonScatteringSeries realize hbar c
    (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
      spinVertex internal m_p)

/-- Finite analytic truncation of the realized Bennett-parametrized scattering
operator. -/
noncomputable def realizedPoincareQEDBennettTauScatteringPartialSum {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) (N : ℕ) : A :=
  realizedPoincareQEDDysonScatteringPartialSum realize hbar c
    (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
      spinVertex internal m_p) N

/-- Bennett-parametrized scattering truncations converge to the realized analytic
scattering operator under a summable norm-majorant estimate. -/
lemma realizedPoincareQEDBennettTauScatteringSeries_tendsto_of_norm_bound
    {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realizedPoincareQEDDysonScatteringTerm realize hbar c
          (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
            spinVertex internal m_p) n‖ ≤ majorant n) :
    Filter.Tendsto
      (fun N => realizedPoincareQEDBennettTauScatteringPartialSum realize weightX weightZ
        sampleX sampleZ hbar c spinVertex internal m_p N)
      Filter.atTop
      (nhds (realizedPoincareQEDBennettTauScatteringSeries realize weightX weightZ
        sampleX sampleZ hbar c spinVertex internal m_p)) := by
  exact realizedPoincareQEDDysonScatteringSeries_tendsto_of_norm_bound realize hbar c
    (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
      spinVertex internal m_p) majorant hmajorant hbound

/-- Realized analytic scattering matrix element for the Bennett-parametrized
interaction. -/
noncomputable def realizedPoincareQEDBennettTauMatrixElementSeries {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) : A :=
  realizedPoincareQEDScatteringMatrixElementSeries realize bra ket hbar c
    (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
      spinVertex internal m_p)

/-- Finite analytic truncation of the realized Bennett-parametrized scattering
matrix element. -/
noncomputable def realizedPoincareQEDBennettTauMatrixElementPartialSum {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup A] [NormedSpace ℂ A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ) (N : ℕ) : A :=
  realizedPoincareQEDScatteringMatrixElementPartialSum realize bra ket hbar c
    (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
      spinVertex internal m_p) N

/-- Bennett-parametrized scattering matrix-element truncations converge to the
realized analytic matrix element under a summable norm-majorant estimate. -/
lemma realizedPoincareQEDBennettTauMatrixElementSeries_tendsto_of_norm_bound
    {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (realize : poincareQEDFieldSpec.FieldOpFreeAlgebra →ₗ[ℂ] A)
    (bra ket : poincareQEDFieldSpec.FieldOpFreeAlgebra)
    (weightX : ι -> ℂ) (weightZ : κ -> ℂ)
    (sampleX : ι -> MinkowskiPoint) (sampleZ : κ -> ComplexTwoSpherePoint)
    (hbar c : ℝ)
    (spinVertex : DiracSpinorIndex -> Fin 6 -> DiracSpinorIndex -> ℂ)
    (internal : ComplexTwoSpherePoint -> ℂ) (m_p : ℝ)
    (majorant : ℕ -> ℝ) (hmajorant : Summable majorant)
    (hbound :
      ∀ n,
        ‖realize
          (poincareQEDScatteringMatrixElementFormalSeries bra ket hbar c
            (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
              spinVertex internal m_p) n)‖ ≤ majorant n) :
    Filter.Tendsto
      (fun N => realizedPoincareQEDBennettTauMatrixElementPartialSum realize bra ket
        weightX weightZ sampleX sampleZ hbar c spinVertex internal m_p N)
      Filter.atTop
      (nhds (realizedPoincareQEDBennettTauMatrixElementSeries realize bra ket
        weightX weightZ sampleX sampleZ hbar c spinVertex internal m_p)) := by
  exact realizedPoincareQEDScatteringMatrixElementSeries_tendsto_of_norm_bound realize
    bra ket hbar c
    (finiteM8BennettTauInteractionAction weightX weightZ sampleX sampleZ
      spinVertex internal m_p) majorant hmajorant hbound

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields

end

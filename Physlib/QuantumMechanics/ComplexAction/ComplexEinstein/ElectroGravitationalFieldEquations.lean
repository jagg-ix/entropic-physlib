/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
public import Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
public import Physlib.QFT.Wick.Consistency
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction
meta import Zil

/-!
# The complete electrogravitic field equations

Assembles the **complete electrogravitic field equations** — the coupled electromagnetic + gravitational
system — by joining the complete complex Einstein field equations
(`ComplexEinstein.CompleteComplexEinsteinFieldEquations`, gravity + superoperator + BCJ sector) to the electromagnetic
**Maxwell–Faraday** sector (`PTSymmetricQFT.MaxwellFaraday`). The electromagnetic field supplies the
constructed Maxwell stress source. BCJ data enter through two explicitly separated interfaces:
the Bianchi/Jacobi analogy and the denominated amplitude realization below.

The system `ElectroGravitationalFieldEquation` carries:

* **the gravitational sector** `𝒢 = κ(T + iS)` — the complete complex Einstein field equation with the
  superoperator equations (`m_I c² = Im E`, `Re 𝒜 = A`, `Im 𝒜 = −S`, the complex d'Alembert balance) and
  the entropic factorization `exp(−Im E) = exp(−S₁)·exp(−S₂)`, together with an explicit
  Jacobi-compliant three-channel realization in the repository's genuine BCJ amplitude carrier;
* **the electromagnetic sector** — a gauge field `(k, A)` with its **Maxwell–Faraday Bianchi identity**
  `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` (`maxwellBianchi`, the homogeneous Maxwell equation `dF = 0`),
  the gauge side of the BCJ kinematic Jacobi;
* **the Einstein–Maxwell coupling** — the real sector `G = κT` (`einsteinMaxwell`), the electromagnetic
  stress-energy sourcing gravity.

Thus the module combines gravity `𝒢 = κ(T + iS)`, electromagnetism `dF = 0`, the sourced equation
obtained from gauge stationarity, and an explicit model-level BCJ amplitude adapter. It does not claim
that the Bianchi analogy or scalar entropy split alone derives gravity from Yang--Mills dynamics.

* **§A — the electrogravitic system and its sectors** (`ElectroGravitationalFieldEquation`,
  `superoperatorEquations`, `bcjDoubleCopy`, `einsteinMaxwell`).
* **§B — the Maxwell sector and the construction** (`maxwellBianchi`, `of_einstein_maxwell`).
* **§C — the Bianchi/Jacobi and amplitude adapters**
  (`stressEnergyConservation`, `entropicSourceDoubleCopy`, `reggeEntropicAction_double_copy`,
  `pathWeight_eq_jacobiBCJAmplitude`, `doubleCopy`).
* **§D — variational derivation instead of supplied equations**
  (`maxwellStressEnergy`, `metricStationary_iff_complexEinstein`,
  `bcjEntropicStationary_iff`, `derive_electrogravitic_field_equation`).
* **§E — metric-to-curvature composition**
  (`metricBuiltConnectionField`, `metricBuiltRiemannAt`, `metricBuiltRicciAt`,
  `metricBuiltScalarAt`, `derive_metricBuilt_electrogravitic_field_equation`).
* **§F — invariant complex residual geometry**
  (`electrograviticResidualCoordinate`, `metricStationary_iff_residualCoordinate_zero`,
  `electrograviticResidual_interval_invariant`,
  `metricBuiltStationary_iff_boostedResidual_zero`).

**Honest variational scope.** The historical constructor `of_einstein_maxwell` below only packages a
supplied Einstein equation. Section D is the stronger route: the electromagnetic source is constructed
from `F = dA`; stationarity of the post-integration-by-parts metric first variation for every independent
real and imaginary metric variation forces the two complex Einstein equations; gauge-field stationarity
forces the source-free Maxwell equation by the arbitrary-test-field fundamental lemma; and
`d²A = 0` gives the homogeneous equation. The post-IBP first-variation formula and stationarity remain
physical premises. This finite momentum-space derivation is not advertised as a construction of the
Einstein--Hilbert functional or a general sourced curved-spacetime Maxwell PDE.
The residual boost in Section F acts internally on the real Einstein--Maxwell and imaginary entropic
action components. It is not a spacetime-coordinate Lorentz boost or electric--magnetic duality, and
interval preservation alone is not used as a substitute for the two vanishing field equations.

## References

* complex-action/entropic-time complex Einstein–Maxwell coupling; Z. Bern, J. J. M. Carrasco, H. Johansson (arXiv:0805.3993).
  Carriers: `ComplexEinstein.CompleteComplexEinsteinFieldEquations` (`CompleteComplexEinsteinFieldEquation`),
  `PTSymmetricQFT.MaxwellFaraday` (`faraday`, `faraday_bianchi`),
  `ComplexEinstein.SuperoperatorComplexEinsteinBCJSector` (`superoperator_em_gravity_bianchi_doublecopy`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QFT.Wick.Consistency
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

variable {ι : Type*}


/-- **The complete electrogravitic field equation** — the coupled electromagnetic + gravitational system:
the complete complex Einstein field equation (`CompleteComplexEinsteinFieldEquation`, gravity +
superoperator + BCJ) together with an electromagnetic gauge field `(k, A)` whose Maxwell–Faraday Bianchi
identity is the gauge side of the BCJ double copy. -/
structure ElectroGravitationalFieldEquation (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ m_R m_I c S₁ S₂ : ℝ) (k A : Fin 4 → ℝ) : Prop where
  /-- The gravitational sector: the complete complex Einstein field equation. -/
  gravitational : CompleteComplexEinsteinFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂

variable {Ric : Matrix ι ι ℝ} {scalarR : ℝ} {g Λ T S : Matrix ι ι ℝ} {κ m_R m_I c S₁ S₂ : ℝ}
  {k A : Fin 4 → ℝ}

/-- **[The superoperator equations of the electrogravitic system].** The gravitational sector carries the
fused superoperator's complex gravitational tensor: `m_I c² = Im E`, `Re 𝒜 = A` (Levi-Civita's true
tensor), `Im 𝒜 = −S` (the entropic source), and the complex d'Alembert balance `(T + iS) + 𝒜 = 0`. -/
lemma ElectroGravitationalFieldEquation.superoperatorEquations
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.re
          = gravitationalTensor Ric scalarR g κ
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.im = -S
      ∧ complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0 :=
  H.gravitational.superoperatorEquations

/-- **[The entropic factorization carried by the BCJ sector].** The identity
`exp(−Im E) = exp(−S₁)·exp(−S₂)` is the scalar damping factorization. By itself it is not the
denominated color--kinematics amplitude; `pathWeight_eq_jacobiBCJAmplitude` supplies that separate
adapter below. -/
lemma ElectroGravitationalFieldEquation.bcjDoubleCopy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂) :=
  H.gravitational.bcjDoubleCopy

/-- **[The Einstein–Maxwell coupling]** `G = κT`. The real sector is the standard Einstein equation with the
electromagnetic stress-energy `T` sourcing gravity, together with the entropic curvature `Λ = κS`. -/
lemma ElectroGravitationalFieldEquation.einsteinMaxwell
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    einsteinFieldEquation Ric scalarR g T κ ∧ Λ = κ • S :=
  H.gravitational.realSector


/-- **[The Maxwell–Faraday Bianchi identity]** `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` — the homogeneous
Maxwell equation `dF = 0` of the electromagnetic sector, the gauge side of the BCJ kinematic Jacobi. -/
lemma ElectroGravitationalFieldEquation.maxwellBianchi
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (lam μ ν : Fin 4) :
    k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0 :=
  faraday_bianchi k A lam μ ν

/-!

The following results expose three related but logically distinct interfaces. They must not be read as
a derivation of the gravity dynamics from the gauge Bianchi identity:

* **kinematic** — the gauge Maxwell cyclic identity `dF = 0` *is* the BCJ kinematic Jacobi
  `n_s + n_t + n_u = 0` *is* the gravity first Bianchi (`maxwellBianchi` /
  `bcj_kinematic_jacobi_is_first_bianchi`);
* **conservation** — the gravity second Bianchi `∇^μ G_{μν} = 0`, Einstein-contracted to the EM
  stress-energy `∇^μ G = κ ∇^μ T`, *discharges to* stress-energy conservation `∇^μ T_{μν} = 0`
  (`stressEnergyConservation`, via `contracted_bianchi_conservation`);
* **entropic (Sorkin)** — the entropic source is the model split `m_I c² = S₁ + S₂`, so the
  amplitude factorizes `exp(−m_I c²) = exp(−S₁)·exp(−S₂)`; read through Sorkin (1975), this is the
  entropic defect of the complex Regge action `−½∫R√(−g) = θ`
  (`entropicSourceDoubleCopy`, `reggeEntropicAction_double_copy`);
* **amplitude** — `pathWeight_eq_jacobiBCJAmplitude` realizes the damping product in the repository's
  actual denominated three-channel BCJ amplitude carrier, with matching color and kinematic Jacobi
  identities. -/

/-- **[Gravity conservation is the double copy of the gauge second Bianchi] `∇^μ T_{μν} = 0`.** For an
electrogravitic solution, when the gravity second Bianchi holds (`∇^μ G_{μν} = 0`) and is
Einstein-contracted to the EM stress-energy divergence (`∇^μ G = κ ∇^μ T`), stress-energy conservation
follows — the gravity-side contract of the double copy (`bcjDualBianchi`), dual to the gauge-side first
Bianchi `dF = 0`. -/
lemma ElectroGravitationalFieldEquation.stressEnergyConservation
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (divG divT : Fin 4 → ℝ) (hEinstein : divG = κ • divT) (hSecondBianchi : divG = 0) :
    divT = 0 :=
  contracted_bianchi_conservation κ H.gravitational.kappa_ne divG divT hEinstein hSecondBianchi

/-- **[The scalar entropic split] `m_I c² = S₁ + S₂`.** The imaginary
Einstein mass is the sum of the two gauge entropic actions, so the gravity amplitude factorizes as the
product `exp(−m_I c²) = exp(−S₁)·exp(−S₂)`. This identity is only the scalar factorization shadow;
the amplitude-level carrier is connected separately below. -/
lemma ElectroGravitationalFieldEquation.entropicSourceDoubleCopy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    m_I * c ^ 2 = S₁ + S₂
      ∧ Real.exp (-(m_I * c ^ 2)) = Real.exp (-S₁) * Real.exp (-S₂) := by
  refine ⟨H.gravitational.entropicSplit, ?_⟩
  rw [H.gravitational.entropicSplit, neg_add, Real.exp_add]

/-- **[Sorkin: the entropic Regge action double-copies the gauge action] `−½∫R√(−g)|_{entropic} = S₁ + S₂`.**
By Sorkin (1975) the per-bone gravity action is the integrated curvature `cuspActionPerArea θ = θ`; applied
to the entropic curvature defect `Im E = m_I c²`, it equals the gauge² sum `S₁ + S₂` — the double copy
expressed through the discrete Einstein–Hilbert (Regge) action. -/
lemma ElectroGravitationalFieldEquation.reggeEntropicAction_double_copy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    cuspActionPerArea (complexEinsteinEnergy m_R m_I c).im = S₁ + S₂ := by
  rw [cuspActionPerArea_eq_defect, ← H.superoperatorEquations.1, H.gravitational.entropicSplit]

/-- **[The electrogravitic Bianchi/entropy interface bundle].** For an electrogravitic solution this
packages the gauge first Bianchi `dF = 0`; the derived
stress-energy conservation `∇^μ T = 0` (from the gravity second Bianchi + Einstein contraction); the
entropic split `m_I c² = S₁ + S₂`; and the Einstein–Maxwell real sector `G = κT`. The conjunction is
not itself the dynamical amplitude double copy. -/
lemma ElectroGravitationalFieldEquation.doubleCopy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (lam μ ν : Fin 4) (divG divT : Fin 4 → ℝ)
    (hEinstein : divG = κ • divT) (hSecondBianchi : divG = 0) :
    (k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0)
      ∧ divT = 0
      ∧ m_I * c ^ 2 = S₁ + S₂
      ∧ einsteinFieldEquation Ric scalarR g T κ :=
  ⟨H.maxwellBianchi lam μ ν,
    H.stressEnergyConservation divG divT hEinstein hSecondBianchi,
    H.gravitational.entropicSplit, H.einsteinMaxwell.1⟩

/-- **[The path-integral damping factorization] `‖exp(iS/ℏ)‖ = exp(−S₁/ℏ)·exp(−S₂/ℏ)`.** Since the
entropic source obeys the supplied split `m_I c² = Im E = S₁ + S₂`
(`entropicSourceDoubleCopy`), the electrogravitic gravity path weight (`complexActionWeight`, whose
modulus is the entropic damping `exp(−S_I/ℏ)`) factorizes into a product. The phase `S_R` is arbitrary.
This theorem is elementary exponential algebra; the next theorem is what routes it through actual BCJ
channels and propagator denominators. -/
lemma ElectroGravitationalFieldEquation.pathWeight_double_copy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (S_R ℏ : ℝ) :
    ‖complexActionWeight S_R (complexEinsteinEnergy m_R m_I c).im ℏ‖
      = Real.exp (-(S₁ / ℏ)) * Real.exp (-(S₂ / ℏ)) := by
  rw [norm_complexActionWeight, ← H.superoperatorEquations.1, H.gravitational.entropicSplit,
    ← Real.exp_add]
  congr 1; ring

/-- A concrete three-channel BCJ duality whose two nonzero channels are opposite.
Both the color and kinematic numerators therefore obey the same Jacobi relation.
This is an amplitude carrier for the entropic damping factor, not a claim that
the exponential itself constructs a Yang--Mills numerator representation. -/
noncomputable def entropicJacobiBCJDuality (S ℏ : ℝ) :
    BCJColorKinematicsDuality where
  c_s := Real.exp (-(S / ℏ))
  c_t := 0
  c_u := -Real.exp (-(S / ℏ))
  n_s := Real.exp (-(S / ℏ))
  n_t := 0
  n_u := -Real.exp (-(S / ℏ))
  color_jacobi := by ring
  kinematic_jacobi := by ring

/-- The three denominated channels realizing `entropicJacobiBCJDuality`.
The two nonzero propagators are both `2`, so their diagonal contributions
sum to one product of the two entropic numerators. -/
noncomputable def entropicJacobiBCJChannels (S ℏ : ℝ) : List BCJTriple :=
  [ { numerator := Real.exp (-(S / ℏ))
      color := Real.exp (-(S / ℏ))
      propagator := 2
      prop_pos := by norm_num },
    { numerator := 0
      color := 0
      propagator := 2
      prop_pos := by norm_num },
    { numerator := -Real.exp (-(S / ℏ))
      color := -Real.exp (-(S / ℏ))
      propagator := 2
      prop_pos := by norm_num } ]

/-- The channel numerators used by `entropicJacobiBCJChannels` are exactly the
Jacobi-compliant numerator triple in `entropicJacobiBCJDuality`. -/
lemma entropicJacobiBCJDuality_kinematic_jacobi (S ℏ : ℝ) :
    (entropicJacobiBCJDuality S ℏ).n_s
        + (entropicJacobiBCJDuality S ℏ).n_t
        + (entropicJacobiBCJDuality S ℏ).n_u = 0 :=
  (entropicJacobiBCJDuality S ℏ).kinematic_jacobi

/-- The genuine denominated BCJ gravity amplitude of the two explicit
Jacobi-compliant channel families is their entropic damping product. -/
lemma entropicJacobiBCJAmplitude_eq (S₁ S₂ ℏ : ℝ) :
    bcjDoubleCopyAmplitude
        (entropicJacobiBCJChannels S₁ ℏ)
        (entropicJacobiBCJChannels S₂ ℏ) =
      Real.exp (-(S₁ / ℏ)) * Real.exp (-(S₂ / ℏ)) := by
  simp [bcjDoubleCopyAmplitude, entropicJacobiBCJChannels]

/-- Each explicit entropic single-copy channel family has the genuine
denominated gauge amplitude `exp(-S/ℏ)²`. -/
lemma entropicJacobiGaugeAmplitude_eq_sq (S ℏ : ℝ) :
    bcjGaugeAmplitude (entropicJacobiBCJChannels S ℏ) =
      Real.exp (-(S / ℏ)) ^ 2 := by
  simp [bcjGaugeAmplitude, entropicJacobiBCJChannels]
  ring

/-- For the explicit Jacobi-compliant realization, the square of the gravity
double-copy amplitude is exactly the product of the two gauge amplitudes.
This supplies both single-copy amplitudes rather than only the gravity-side
sum. -/
lemma entropicJacobiDoubleCopy_sq_eq_gauge_product (S₁ S₂ ℏ : ℝ) :
    bcjDoubleCopyAmplitude
        (entropicJacobiBCJChannels S₁ ℏ)
        (entropicJacobiBCJChannels S₂ ℏ) ^ 2 =
      bcjGaugeAmplitude (entropicJacobiBCJChannels S₁ ℏ) *
        bcjGaugeAmplitude (entropicJacobiBCJChannels S₂ ℏ) := by
  rw [entropicJacobiBCJAmplitude_eq, entropicJacobiGaugeAmplitude_eq_sq,
    entropicJacobiGaugeAmplitude_eq_sq]
  ring

/-- **The electrogravitic path weight routed through the actual BCJ amplitude API.**
The earlier exponential factorization is now realized by a denominated
three-channel gravity amplitude whose color and kinematic triples satisfy
Jacobi. This connects the electrogravitic theorem to
`ColorKinematicsDoubleCopy` without identifying the model-specific
exponential numerators with arbitrary Yang--Mills numerators. -/
lemma ElectroGravitationalFieldEquation.pathWeight_eq_jacobiBCJAmplitude
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (S_R ℏ : ℝ) :
    ‖complexActionWeight S_R (complexEinsteinEnergy m_R m_I c).im ℏ‖ =
      bcjDoubleCopyAmplitude
        (entropicJacobiBCJChannels S₁ ℏ)
        (entropicJacobiBCJChannels S₂ ℏ) := by
  calc
    ‖complexActionWeight S_R (complexEinsteinEnergy m_R m_I c).im ℏ‖
        = Real.exp (-(S₁ / ℏ)) * Real.exp (-(S₂ / ℏ)) :=
          H.pathWeight_double_copy S_R ℏ
    _ = bcjDoubleCopyAmplitude
          (entropicJacobiBCJChannels S₁ ℏ)
          (entropicJacobiBCJChannels S₂ ℏ) :=
      (entropicJacobiBCJAmplitude_eq S₁ S₂ ℏ).symm

/-- **[The electrogravitic double copy through Sorkin's complex Regge action].** The entropic source
is realized as the imaginary part of a (single-bone) complex Regge action `Σ_b A(b) θ(b)` with
imaginary defect `Im E` (`LeviCivita.ComplexReggeAction`), so the path-integral double copy factors
through Sorkin's discretized action: the modulus of the complex Regge weight is
`exp(−S₁/ℏ)·exp(−S₂/ℏ)`. This ties the electrogravitic double copy to the (Sorkin) complex Regge
action rather than leaving either floating. -/
lemma ElectroGravitationalFieldEquation.reggeActionPathWeight_double_copy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (θ_R ℏ : ℝ) :
    ‖complexActionWeight
        (complexReggeAction (fun _ : Unit => (1 : ℝ))
          (fun _ => (θ_R : ℂ) + Complex.I * ((complexEinsteinEnergy m_R m_I c).im : ℂ))).re
        (complexReggeAction (fun _ : Unit => (1 : ℝ))
          (fun _ => (θ_R : ℂ) + Complex.I * ((complexEinsteinEnergy m_R m_I c).im : ℂ))).im ℏ‖
      = Real.exp (-(S₁ / ℏ)) * Real.exp (-(S₂ / ℏ)) := by
  rw [reggeAction_complexActionWeight_norm]
  have him : sorkinReggeAction (fun _ : Unit => (1 : ℝ))
      (fun _ => ((θ_R : ℂ) + Complex.I * ((complexEinsteinEnergy m_R m_I c).im : ℂ)).im)
      = (complexEinsteinEnergy m_R m_I c).im := by
    unfold sorkinReggeAction reggeAction; simp
  rw [him, ← H.superoperatorEquations.1, H.gravitational.entropicSplit, ← Real.exp_add]
  congr 1; ring

/-- **[Constructing the electrogravitic field equations] from Einstein–Maxwell + entropic + BCJ.** The
electrogravitic system is assembled from the Einstein equation `G = κT` (electromagnetic source), the
entropic curvature `Λ = κS`, the BCJ entropic split `m_I c² = S₁ + S₂`, and any electromagnetic gauge field
`(k, A)`. -/
lemma ElectroGravitationalFieldEquation.of_einstein_maxwell (hκ : κ ≠ 0)
    (hReal : einsteinFieldEquation Ric scalarR g T κ) (hImag : Λ = κ • S)
    (hsplit : m_I * c ^ 2 = S₁ + S₂) (k A : Fin 4 → ℝ) :
    ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A where
  gravitational :=
    CompleteComplexEinsteinFieldEquation.of_real_and_entropic hκ hReal hImag hsplit

/-! ## D. Derive the electrogravitic equations from stationarity -/

/-- A covariant rank-two tensor in the four-dimensional momentum-space carrier. -/
abbrev FourTensor := Matrix (Fin 4) (Fin 4) ℝ

/-- A four-dimensional coordinate chart carrier. -/
abbrev FourCoordinate := Fin 4 → ℝ

/-- A metric field on the four-dimensional coordinate carrier. -/
abbrev FourMetricField := FourCoordinate → FourTensor

/-- Certificate that `g` and `gInv` are a symmetric two-sided metric/inverse
pair at every point of the chart. This is the algebraic nondegeneracy datum
needed before the Christoffel formula below may be called Levi--Civita. -/
structure IsFourMetricPair (g gInv : FourMetricField) : Prop where
  g_symm : ∀ x, Matrix.transpose (g x) = g x
  gInv_symm : ∀ x, Matrix.transpose (gInv x) = gInv x
  inverse_left : ∀ x, gInv x * g x = 1
  inverse_right : ∀ x, g x * gInv x = 1

/-- The metric-built Levi--Civita connection field. The first metric jet is
the Fréchet coordinate derivative; it is not supplied as unrelated data. -/
noncomputable def metricBuiltConnectionField
    (g gInv : FourMetricField) :
    FourCoordinate → Fin 4 → FourTensor :=
  leviCivitaConnectionField
    (frechetCoordinatePartial (ι := Fin 4)) g gInv

/-- A certified metric pair makes the constructed connection genuinely
Levi--Civita: torsion-free and compatible with the same metric field. -/
lemma metricBuiltConnectionField_isLeviCivita
    (g gInv : FourMetricField) (h : IsFourMetricPair g gInv)
    (x : FourCoordinate) :
    IsTorsionFree (metricBuiltConnectionField g gInv x)
      ∧ IsMetricCompatible
        (metricBuiltConnectionField g gInv x)
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x)
        (g x) := by
  have hjet :
      ∀ κ, Matrix.transpose
          (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x κ) =
        metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x κ :=
    metricFirstJet_transpose_eq
      (frechetCoordinatePartial (ι := Fin 4)) g h.g_symm x
  exact
    ⟨christoffelFromMetric_isTorsionFree (gInv x)
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x) hjet,
      christoffelFromMetric_isMetricCompatible
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x)
        (h.g_symm x) (h.gInv_symm x) (h.inverse_left x) hjet⟩

/-- The Fréchet first jet of the metric-built Levi--Civita connection. -/
noncomputable def metricBuiltConnectionJetAt
    (g gInv : FourMetricField) (x : FourCoordinate) :
    Fin 4 → Fin 4 → FourTensor :=
  connectionFirstJet
    (frechetCoordinatePartial (ι := Fin 4))
    (metricBuiltConnectionField g gInv) x

/-- The full coordinate Riemann tensor constructed from the metric field:
`g → ∂g → Γ[g] → ∂Γ[g] → Riemann[g]`. -/
noncomputable def metricBuiltRiemannAt
    (g gInv : FourMetricField) (x : FourCoordinate)
    (ρ σ μ ν : Fin 4) : ℝ :=
  riemannFromConnection
    (metricBuiltConnectionField g gInv x)
    (metricBuiltConnectionJetAt g gInv x) ρ σ μ ν

/-- The Ricci contraction of the metric-built coordinate Riemann tensor. -/
noncomputable def metricBuiltRicciAt
    (g gInv : FourMetricField) (x : FourCoordinate) : FourTensor :=
  ricciMatrixFromConnection
    (metricBuiltConnectionField g gInv x)
    (metricBuiltConnectionJetAt g gInv x)

/-- The Ricci tensor above is exactly the contraction of
`metricBuiltRiemannAt`; this makes the Riemann-to-Ricci arrow explicit rather
than leaving two merely parallel definitions. -/
lemma metricBuiltRicciAt_apply_eq_sum_riemann
    (g gInv : FourMetricField) (x : FourCoordinate) (σ ν : Fin 4) :
    metricBuiltRicciAt g gInv x σ ν =
      ∑ μ, metricBuiltRiemannAt g gInv x μ σ μ ν := by
  rfl

/-- The Riemann tensor constructed from a symmetric invertible metric obeys
the first algebraic Bianchi identity. Torsion freedom holds at every point,
and differentiating that lower-index symmetry supplies the symmetric
connection jet required by `riemannFromConnection_firstBianchi`. -/
lemma metricBuiltRiemannAt_firstBianchi
    (g gInv : FourMetricField) (h : IsFourMetricPair g gInv)
    (x : FourCoordinate) :
    FirstBianchi (metricBuiltRiemannAt g gInv x) := by
  apply riemannFromConnection_firstBianchi
  · exact (metricBuiltConnectionField_isLeviCivita g gInv h x).1
  · exact connectionFirstJet_transpose_eq_of_torsionFree
      (frechetCoordinatePartial (ι := Fin 4))
      (metricBuiltConnectionField g gInv)
      (fun y => (metricBuiltConnectionField_isLeviCivita g gInv h y).1) x

/-- The scalar curvature `R[g] = tr(g⁻¹ Ric[g])`. -/
noncomputable def metricBuiltScalarAt
    (g gInv : FourMetricField) (x : FourCoordinate) : ℝ :=
  (gInv x * metricBuiltRicciAt g gInv x).trace

/-- The Einstein tensor constructed through the complete chart chain
`g → g⁻¹ → Γ[g] → Riemann[g] → Ric[g] → R[g] → G[g]`. -/
noncomputable def metricBuiltEinsteinAt
    (g gInv : FourMetricField) (x : FourCoordinate) : FourTensor :=
  einsteinTensor
    (metricBuiltRicciAt g gInv x)
    (metricBuiltScalarAt g gInv x) (g x)

/-- Raise the second index of a covariant two-tensor with the supplied inverse metric. -/
noncomputable def raiseSecondIndex (gInv F : FourTensor) : FourTensor :=
  fun μ ν => ∑ α, F μ α * gInv α ν

/-- Raise both indices of a covariant two-tensor. -/
noncomputable def raiseBothIndices (gInv F : FourTensor) : FourTensor :=
  fun μ ν => ∑ α, ∑ β, gInv μ α * gInv ν β * F α β

/-- The Maxwell scalar `F_{αβ} F^{αβ}`. -/
noncomputable def maxwellInvariant (gInv F : FourTensor) : ℝ :=
  ∑ α, ∑ β, F α β * raiseBothIndices gInv F α β

/-- The Maxwell stress-energy tensor in the mostly-minus convention,
`T_{μν} = -F_{μα}F_ν{}^α + 1/4 g_{μν}F_{αβ}F^{αβ}`. The sign convention gives
positive electric energy density for `g = diag(1,-1,-1,-1)`. -/
noncomputable def maxwellStressEnergy (g gInv F : FourTensor) : FourTensor :=
  fun μ ν =>
    -(∑ α, F μ α * raiseSecondIndex gInv F ν α)
      + (1 / 4 : ℝ) * g μ ν * maxwellInvariant gInv F

/-- The Maxwell source constructed from `F = dA` is gauge invariant. -/
lemma maxwellStressEnergy_faraday_gauge_invariant
    (g gInv : FourTensor) (k A : Fin 4 → ℝ) (χ : ℝ) :
    maxwellStressEnergy g gInv (faraday k (fun ρ => A ρ + χ * k ρ)) =
      maxwellStressEnergy g gInv (faraday k A) := by
  rw [faraday_gauge_invariant]

/-- The supplied contravariant metric really is a two-sided matrix inverse of the covariant metric. -/
def AreInverseMetrics (g gInv : FourTensor) : Prop :=
  g * gInv = 1 ∧ gInv * g = 1

/-- The post-integration-by-parts first variation of the Maxwell action in a gauge-potential
direction `α`: `⟨α, δdA⟩`. Overall nonzero normalization is irrelevant to stationarity. -/
noncomputable def electromagneticFirstVariation
    (k A α : Fin 4 → ℝ) : ℝ :=
  ∑ ν, α ν * maxwellOp (faraday k A) k ν

/-- Maxwell stationarity against every gauge-potential variation. -/
def IsElectromagneticStationary (k A : Fin 4 → ℝ) : Prop :=
  ∀ α, electromagneticFirstVariation k A α = 0

/-- **Gauge-potential stationarity is equivalent to the source-free Maxwell equation.**
Each coordinate test variation isolates one component of `δdA`; conversely, a vanishing Maxwell
operator makes every first variation vanish. -/
@[zil_level physical_theorem]
lemma electromagneticStationary_iff_sourceFree (k A : Fin 4 → ℝ) :
    IsElectromagneticStationary k A ↔
      ∀ ν, maxwellOp (faraday k A) k ν = 0 := by
  constructor
  · intro h ν
    have hν := h (Pi.single ν 1)
    simpa [electromagneticFirstVariation, Pi.single_apply, Finset.sum_ite_eq'] using hν
  · intro h α
    simp [electromagneticFirstVariation, h]

/-- Pair a tensor residual with an arbitrary metric variation. -/
noncomputable def tensorPairing (P variation : FourTensor) : ℝ :=
  ∑ μ, ∑ ν, P μ ν * variation μ ν

/-! ## E. Constructed Maxwell metric variation -/

/-- The first variation of the Maxwell invariant when the inverse metric
varies in direction `H`; both inverse-metric factors are differentiated. -/
noncomputable def maxwellInvariantFirstVariation
    (gInv H F : FourTensor) : ℝ :=
  ∑ a, ∑ b, ∑ m, ∑ n,
    F a b * (H a m * gInv b n + gInv a m * H b n) * F m n

private lemma realAffine_hasDerivAt (a b : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- The explicit inverse-metric derivative of
`F_{αβ} F^{αβ}` along `g⁻¹ + tH`. -/
lemma maxwellInvariant_line_hasDerivAt (gInv H F : FourTensor) :
    HasDerivAt
      (fun t : ℝ => maxwellInvariant (gInv + t • H) F)
      (maxwellInvariantFirstVariation gInv H F) 0 := by
  have hterm (a b m n : Fin 4) : HasDerivAt
      (fun t : ℝ => F a b *
        ((gInv a m + t * H a m) * (gInv b n + t * H b n) * F m n))
      (F a b *
        ((H a m * gInv b n + gInv a m * H b n) * F m n)) 0 := by
    have hp := (realAffine_hasDerivAt (gInv a m) (H a m)).mul
      (realAffine_hasDerivAt (gInv b n) (H b n))
    simpa [mul_assoc] using (hp.mul_const (F m n)).const_mul (F a b)
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ a, ∑ b, ∑ m, ∑ n,
        F a b * ((gInv a m + t * H a m) *
          (gInv b n + t * H b n) * F m n))
      (∑ a, ∑ b, ∑ m, ∑ n,
        F a b * ((H a m * gInv b n + gInv a m * H b n) * F m n)) 0 :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
      HasDerivAt.fun_sum fun m _ => HasDerivAt.fun_sum fun n _ => hterm a b m n
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun t => by
      simp only [maxwellInvariant, raiseBothIndices, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  · unfold maxwellInvariantFirstVariation
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    ring

/-- For symmetric inverse-metric variations and antisymmetric field
strength, the invariant derivative is twice the electromagnetic quadratic
form paired with the inverse-metric variation. -/
lemma maxwellInvariantFirstVariation_eq_two_tensorPairing
    (gInv H F : FourTensor)
    (hgInv : ∀ i j, gInv i j = gInv j i)
    (hH : ∀ i j, H i j = H j i)
    (hF : ∀ i j, F i j = -F j i) :
    maxwellInvariantFirstVariation gInv H F =
      2 * tensorPairing
        (fun μ ν => ∑ α, F μ α * raiseSecondIndex gInv F ν α) H := by
  have f00 : F 0 0 = 0 := by have := hF 0 0; linarith
  have f11 : F 1 1 = 0 := by have := hF 1 1; linarith
  have f22 : F 2 2 = 0 := by have := hF 2 2; linarith
  have f33 : F 3 3 = 0 := by have := hF 3 3; linarith
  simp only [maxwellInvariantFirstVariation, tensorPairing,
    raiseSecondIndex, Fin.sum_univ_four]
  rw [f00, f11, f22, f33,
    hF 1 0, hF 2 0, hF 3 0, hF 2 1, hF 3 1, hF 3 2,
    hgInv 1 0, hgInv 2 0, hgInv 3 0, hgInv 2 1, hgInv 3 1, hgInv 3 2,
    hH 1 0, hH 2 0, hH 3 0, hH 2 1, hH 3 1, hH 3 2]
  ring

private lemma tensorPairing_eq_trace_mul_of_right_symm
    (P Q : FourTensor) (hQ : ∀ i j, Q i j = Q j i) :
    tensorPairing P Q = Matrix.trace (P * Q) := by
  simp only [tensorPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hQ j i]

private lemma tensorPairing_inverseVariation_eq_neg_trace
    (g gInv h H : FourTensor)
    (hH : ∀ i j, H i j = H j i)
    (hlinearized : h * gInv + g * H = 0) :
    tensorPairing g H = -Matrix.trace (gInv * h) := by
  rw [tensorPairing_eq_trace_mul_of_right_symm g H hH]
  have hmul : g * H = -(h * gInv) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hlinearized)
  rw [hmul, Matrix.trace_neg, Matrix.trace_mul_comm]

/-- Contracting the Maxwell stress tensor separates its quadratic and trace
terms before the determinant-density variation is included. -/
lemma tensorPairing_maxwellStressEnergy
    (g gInv H F : FourTensor) :
    tensorPairing (maxwellStressEnergy g gInv F) H =
      -tensorPairing
          (fun μ ν => ∑ α, F μ α * raiseSecondIndex gInv F ν α) H +
        (1 / 4 : ℝ) * maxwellInvariant gInv F * tensorPairing g H := by
  simp only [tensorPairing, maxwellStressEnergy, Fin.sum_univ_four]
  ring

/-- The metric-dependent Maxwell density
`-(1/4) √(-det g) F_{αβ}F^{αβ}`. -/
noncomputable def maxwellMetricDensity
    (g gInv F : FourTensor) : ℝ :=
  -(1 / 4 : ℝ) *
    lorentzianVolumeDensity g * maxwellInvariant gInv F

/-- The raw derivative of the Maxwell density, retaining separately the
Lorentzian volume and inverse-metric contributions. -/
lemma maxwellMetricDensity_line_hasDerivAt
    (g gInv h H F : FourTensor)
    (hInv : g * gInv = 1) (hLorentz : Matrix.det g < 0) :
    HasDerivAt
      (fun t : ℝ => maxwellMetricDensity
        (g + t • h) (gInv + t • H) F)
      (-(1 / 4 : ℝ) *
        (lorentzianVolumeDensity g / 2 *
            Matrix.trace (gInv * h) * maxwellInvariant gInv F +
          lorentzianVolumeDensity g *
            maxwellInvariantFirstVariation gInv H F)) 0 := by
  have hvol := hasDerivAt_lorentzianVolumeDensity_affine
    g gInv h hInv hLorentz
  have hinv := maxwellInvariant_line_hasDerivAt gInv H F
  have hderiv := (hvol.mul hinv).const_mul (-(1 / 4 : ℝ))
  refine (hderiv.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun _ => by
      simp only [maxwellMetricDensity, Pi.mul_apply]
      ring
  · simp only [zero_smul, add_zero]

/-- Under the linearized inverse constraint, the raw Maxwell-density
derivative is exactly one half of the volume-weighted Maxwell stress-energy
pairing with the inverse-metric variation. -/
lemma maxwellMetricDensity_derivative_eq_stressEnergy
    (g gInv h H F : FourTensor)
    (hgInv : ∀ i j, gInv i j = gInv j i)
    (hH : ∀ i j, H i j = H j i)
    (hF : ∀ i j, F i j = -F j i)
    (hlinearized : h * gInv + g * H = 0) :
    -(1 / 4 : ℝ) *
        (lorentzianVolumeDensity g / 2 *
            Matrix.trace (gInv * h) * maxwellInvariant gInv F +
          lorentzianVolumeDensity g *
            maxwellInvariantFirstVariation gInv H F) =
      lorentzianVolumeDensity g / 2 *
        tensorPairing (maxwellStressEnergy g gInv F) H := by
  rw [maxwellInvariantFirstVariation_eq_two_tensorPairing gInv H F hgInv hH hF,
    tensorPairing_maxwellStressEnergy,
    tensorPairing_inverseVariation_eq_neg_trace g gInv h H hH hlinearized]
  ring

/-- The constructed Maxwell density has the Maxwell stress tensor as its
genuine metric derivative for every compatible symmetric metric and
inverse-metric direction. -/
lemma maxwellMetricDensity_line_hasDerivAt_stressEnergy
    (g gInv h H F : FourTensor)
    (hInv : g * gInv = 1) (hLorentz : Matrix.det g < 0)
    (hgInv : ∀ i j, gInv i j = gInv j i)
    (hH : ∀ i j, H i j = H j i)
    (hF : ∀ i j, F i j = -F j i)
    (hlinearized : h * gInv + g * H = 0) :
    HasDerivAt
      (fun t : ℝ => maxwellMetricDensity
        (g + t • h) (gInv + t • H) F)
      (lorentzianVolumeDensity g / 2 *
        tensorPairing (maxwellStressEnergy g gInv F) H) 0 :=
  (maxwellMetricDensity_line_hasDerivAt
    g gInv h H F hInv hLorentz).congr_deriv
      (maxwellMetricDensity_derivative_eq_stressEnergy
        g gInv h H F hgInv hH hF hlinearized)

/-- Along a covariant metric direction, the explicitly constructed inverse
variation `-g⁻¹hg⁻¹` makes the derivative of
`-(1/4) √(-det g) F_{αβ}F^{αβ}` exactly the volume-weighted Maxwell
stress-energy pairing. -/
@[zil_level physical_theorem]
lemma maxwellMetricDensity_covariantLine_hasDerivAt_stressEnergy
    (g gInv h F : FourTensor)
    (hInv : g * gInv = 1) (hLorentz : Matrix.det g < 0)
    (hgInv : ∀ i j, gInv i j = gInv j i)
    (hh : ∀ i j, h i j = h j i)
    (hF : ∀ i j, F i j = -F j i) :
    HasDerivAt
      (fun t : ℝ => maxwellMetricDensity
        (g + t • h)
        (gInv + t • inverseMetricVariation gInv h) F)
      (lorentzianVolumeDensity g / 2 *
        tensorPairing (maxwellStressEnergy g gInv F)
          (inverseMetricVariation gInv h)) 0 := by
  apply maxwellMetricDensity_line_hasDerivAt_stressEnergy
  · exact hInv
  · exact hLorentz
  · exact hgInv
  · exact inverseMetricVariation_symm gInv h hgInv hh
  · exact hF
  · exact inverseMetricVariation_linearized_rightInverse g gInv h hInv

/-- The post-integration-by-parts first variation of the coupled complex metric action.

The real residual is the Einstein tensor minus the Maxwell stress-energy source constructed from
`F = dA`. The imaginary residual is the entropic curvature minus its source. This definition is the
finite momentum-space carrier of the usual Einstein--Hilbert + Maxwell first-variation formula. -/
noncomputable def electrograviticMetricFirstVariation
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) (variationReal variationImag : FourTensor) : ℝ :=
  tensorPairing
      (einsteinTensor Ric scalarR g -
        κ • maxwellStressEnergy g gInv (faraday k A)) variationReal
    + tensorPairing (Λ - κ • S) variationImag

/-- **The complex electrogravitic residual at one tensor component.**  Its real component is
the Einstein tensor minus the gauge-invariant Maxwell stress source, while its imaginary component
is the entropic Einstein residual.  This embeds the already-existing two independent metric
variations into the Nagao–Nielsen real/imaginary action plane; it does not identify that plane with
spacetime coordinates. -/
noncomputable def electrograviticResidualCoordinate
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ⟨(einsteinTensor Ric scalarR g -
      κ • maxwellStressEnergy g gInv (faraday k A)) μ ν,
    (Λ - κ • S) μ ν⟩

/-- The real part of the complex residual is exactly the Einstein–Maxwell residual. -/
theorem electrograviticResidualCoordinate_re
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) (μ ν : Fin 4) :
    (electrograviticResidualCoordinate Ric scalarR g gInv Λ S κ k A μ ν).re =
      (einsteinTensor Ric scalarR g -
        κ • maxwellStressEnergy g gInv (faraday k A)) μ ν := rfl

/-- The imaginary part of the complex residual is exactly the entropic Einstein residual. -/
theorem electrograviticResidualCoordinate_im
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) (μ ν : Fin 4) :
    (electrograviticResidualCoordinate Ric scalarR g gInv Λ S κ k A μ ν).im =
      (Λ - κ • S) μ ν := rfl

/-- Stationarity against every independent real and imaginary metric variation. -/
def IsElectrograviticMetricStationary
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) : Prop :=
  ∀ variationReal variationImag,
    electrograviticMetricFirstVariation Ric scalarR g gInv Λ S κ k A
      variationReal variationImag = 0

/-- The finite fundamental lemma: if a tensor pairs to zero with every matrix variation, it vanishes. -/
lemma tensor_eq_zero_of_pairing_all_zero (P : FourTensor)
    (h : ∀ variation, tensorPairing P variation = 0) :
    P = 0 := by
  ext μ ν
  have hμν := h (Matrix.single μ ν 1)
  fin_cases μ <;> fin_cases ν <;>
    simpa [tensorPairing, Matrix.single_apply, Fin.sum_univ_four] using hμν

/-- Real metric stationarity derives the Einstein equation with the constructed Maxwell source. -/
lemma metricStationary_real
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ)
    (h : IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A) :
    einsteinFieldEquation Ric scalarR g
      (maxwellStressEnergy g gInv (faraday k A)) κ := by
  rw [einsteinFieldEquation]
  have hz : einsteinTensor Ric scalarR g -
      κ • maxwellStressEnergy g gInv (faraday k A) = 0 := by
    apply tensor_eq_zero_of_pairing_all_zero
    intro variation
    have hv := h variation 0
    simpa [electrograviticMetricFirstVariation, tensorPairing] using hv
  exact sub_eq_zero.mp hz

/-- Imaginary metric stationarity derives the entropic Einstein equation `Λ = κS`. -/
lemma metricStationary_imag
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ)
    (h : IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A) :
    Λ = κ • S := by
  have hz : Λ - κ • S = 0 := by
    apply tensor_eq_zero_of_pairing_all_zero
    intro variation
    have hv := h 0 variation
    simpa [electrograviticMetricFirstVariation, tensorPairing] using hv
  exact sub_eq_zero.mp hz

/-- **Metric stationarity is equivalent to the complex Einstein equation.**
This is the Euler--Lagrange step which replaces a supplied `G = κT` premise. -/
@[zil_level physical_theorem]
lemma metricStationary_iff_complexEinstein
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) :
    IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A ↔
      complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ
        (maxwellStressEnergy g gInv (faraday k A)) S κ := by
  constructor
  · intro h
    exact (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ
      (maxwellStressEnergy g gInv (faraday k A)) S κ).mpr
        ⟨metricStationary_real Ric scalarR g gInv Λ S κ k A h,
          metricStationary_imag Ric scalarR g gInv Λ S κ k A h⟩
  · intro h variationReal variationImag
    obtain ⟨hreal, himag⟩ :=
      (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ
        (maxwellStressEnergy g gInv (faraday k A)) S κ).mp h
    rw [einsteinFieldEquation] at hreal
    simp [electrograviticMetricFirstVariation, hreal, himag, tensorPairing]

/-- **Electrogravitic stationarity is exactly vanishing of the complex residual.**  This is
the componentwise complex packaging of the already-proved equivalence with the Einstein–Maxwell
and entropic Einstein equations. -/
@[zil_level bridge_theorem]
theorem metricStationary_iff_residualCoordinate_zero
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) :
    IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A ↔
      ∀ μ ν, electrograviticResidualCoordinate
        Ric scalarR g gInv Λ S κ k A μ ν = 0 := by
  constructor
  · intro h μ ν
    have hreal := metricStationary_real Ric scalarR g gInv Λ S κ k A h
    have himag := metricStationary_imag Ric scalarR g gInv Λ S κ k A h
    rw [einsteinFieldEquation] at hreal
    apply Complex.ext
    · simp [electrograviticResidualCoordinate, hreal]
    · simp [electrograviticResidualCoordinate, himag]
  · intro h
    apply (metricStationary_iff_complexEinstein Ric scalarR g gInv Λ S κ k A).2
    apply (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ
      (maxwellStressEnergy g gInv (faraday k A)) S κ).2
    constructor
    · rw [einsteinFieldEquation]
      ext μ ν
      have hμν := congrArg Complex.re (h μ ν)
      exact sub_eq_zero.mp (by
        simpa [electrograviticResidualCoordinate] using hμν)
    · ext μ ν
      have hμν := congrArg Complex.im (h μ ν)
      exact sub_eq_zero.mp (by
        simpa [electrograviticResidualCoordinate] using hμν)

/-- **The electrogravitic residual carries the Nagao–Nielsen invariant interval.**  Mixing its
Einstein–Maxwell and entropic-Einstein components by an internal action rapidity preserves the
difference of their squared residuals exactly. -/
@[zil_level bridge_theorem]
theorem electrograviticResidual_interval_invariant
    (η : ℝ) (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) (μ ν : Fin 4) :
    nnLorentzForm (nnActionBoost η
      (electrograviticResidualCoordinate Ric scalarR g gInv Λ S κ k A μ ν)) =
    nnLorentzForm
      (electrograviticResidualCoordinate Ric scalarR g gInv Λ S κ k A μ ν) :=
  nnActionBoost_preserves_interval η _

/-- **Stationarity is invariant under internal real/imaginary action boosts.**  Because the
opposite rapidity is an exact inverse, every boosted electrogravitic residual vanishes exactly when
the original Einstein–Maxwell and entropic residuals vanish. -/
@[zil_level bridge_theorem]
theorem metricStationary_iff_boostedResidual_zero
    (η : ℝ) (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) :
    IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A ↔
      ∀ μ ν, nnActionBoost η (electrograviticResidualCoordinate
        Ric scalarR g gInv Λ S κ k A μ ν) = 0 := by
  rw [metricStationary_iff_residualCoordinate_zero]
  constructor <;> intro h μ ν
  · exact (nnActionBoost_eq_zero_iff η _).2 (h μ ν)
  · exact (nnActionBoost_eq_zero_iff η _).1 (h μ ν)

/-- **Metric-built stationarity equivalence.** This specializes the
electrogravitic variational equation to the exact Ricci tensor and scalar
constructed from the same metric field and its Fréchet coordinate jets.
Consequently the Einstein tensor in the conclusion is no longer an
independent matrix input. -/
@[zil_level physical_theorem]
lemma metricBuiltStationary_iff_complexEinstein
    (g gInv : FourMetricField) (x : FourCoordinate)
    (Λ S : FourTensor) (κ : ℝ) (k A : Fin 4 → ℝ) :
    IsElectrograviticMetricStationary
        (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
        (g x) (gInv x) Λ S κ k A ↔
      complexEinsteinFieldEquation
        (metricBuiltEinsteinAt g gInv x) Λ
        (maxwellStressEnergy (g x) (gInv x) (faraday k A)) S κ := by
  simpa [metricBuiltEinsteinAt] using
    metricStationary_iff_complexEinstein
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ k A

/-- The complex residual with Ricci, scalar curvature, and Einstein tensor constructed from the
same metric field and its Levi–Civita connection. -/
noncomputable def metricBuiltElectrograviticResidualCoordinate
    (g gInv : FourMetricField) (x : FourCoordinate) (Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  electrograviticResidualCoordinate
    (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
    (g x) (gInv x) Λ S κ k A μ ν

/-- **Metric-built Einstein–Maxwell stationarity has the same boost-invariant zero set.**
Here the gravity residual is no longer supplied: the metric builds its unique Levi–Civita connection,
Riemann and Ricci tensors, scalar curvature, and Einstein tensor before the complex residual is formed. -/
@[zil_level bridge_theorem]
theorem metricBuiltStationary_iff_boostedResidual_zero
    (η : ℝ) (g gInv : FourMetricField) (x : FourCoordinate)
    (Λ S : FourTensor) (κ : ℝ) (k A : Fin 4 → ℝ) :
    IsElectrograviticMetricStationary
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ k A ↔
    ∀ μ ν, nnActionBoost η
      (metricBuiltElectrograviticResidualCoordinate g gInv x Λ S κ k A μ ν) = 0 := by
  simpa [metricBuiltElectrograviticResidualCoordinate] using
    metricStationary_iff_boostedResidual_zero η
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ k A

/-- The scalar first variation whose Euler--Lagrange equation is the entropic BCJ split. -/
def bcjEntropicFirstVariation (mI c S1 S2 variation : ℝ) : ℝ :=
  (mI * c ^ 2 - (S1 + S2)) * variation

/-- Stationarity of the scalar entropic/double-copy sector. -/
def IsBCJEntropicStationary (mI c S1 S2 : ℝ) : Prop :=
  ∀ variation, bcjEntropicFirstVariation mI c S1 S2 variation = 0

/-- Scalar stationarity is equivalent to the entropic split `m_I c² = S₁ + S₂`. -/
@[zil_level physical_theorem]
lemma bcjEntropicStationary_iff (mI c S1 S2 : ℝ) :
    IsBCJEntropicStationary mI c S1 S2 ↔ mI * c ^ 2 = S1 + S2 := by
  constructor
  · intro h
    have h1 := h 1
    have hzero : mI * c ^ 2 - (S1 + S2) = 0 := by
      simpa [bcjEntropicFirstVariation] using h1
    exact sub_eq_zero.mp hzero
  · intro h variation
    simp [bcjEntropicFirstVariation, h]

/-- One variation of all three independent sectors used by the current
electrogravitic first-variation interface. This bundles variations; it does
not manufacture the still-missing underlying Einstein--Hilbert--Maxwell
field functional. -/
structure CoupledElectrograviticVariation where
  metricReal : FourTensor
  metricImag : FourTensor
  gauge : Fin 4 → ℝ
  entropic : ℝ

/-- The direct sum of the already formalized metric, gauge and entropic
first variations. Unlike a field action, this object is explicitly a
first-variation carrier. -/
noncomputable def coupledElectrograviticFirstVariation
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)
    (variation : CoupledElectrograviticVariation) : ℝ :=
  electrograviticMetricFirstVariation Ric scalarR g gInv Λ S κ k A
      variation.metricReal variation.metricImag
    + electromagneticFirstVariation k A variation.gauge
    + bcjEntropicFirstVariation mI c S1 S2 variation.entropic

/-- Joint stationarity of the direct-sum first variation. -/
def IsCoupledElectrograviticStationary
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ) : Prop :=
  ∀ variation,
    coupledElectrograviticFirstVariation
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A variation = 0

/-- Joint stationarity is exactly simultaneous stationarity of the metric,
gauge and entropic sectors. The reverse implication is the direct-sum
composition theorem; the forward implication isolates each sector by
setting the other variations to zero. -/
@[zil_level bridge_theorem]
lemma coupledElectrograviticStationary_iff
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ) :
    IsCoupledElectrograviticStationary
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A ↔
      IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A
        ∧ IsElectromagneticStationary k A
        ∧ IsBCJEntropicStationary mI c S1 S2 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro variationReal variationImag
      simpa [coupledElectrograviticFirstVariation,
        electrograviticMetricFirstVariation, electromagneticFirstVariation,
        bcjEntropicFirstVariation, tensorPairing] using
        h {
          metricReal := variationReal
          metricImag := variationImag
          gauge := 0
          entropic := 0
        }
    · intro variationGauge
      simpa [coupledElectrograviticFirstVariation,
        electrograviticMetricFirstVariation, electromagneticFirstVariation,
        bcjEntropicFirstVariation, tensorPairing] using
        h {
          metricReal := 0
          metricImag := 0
          gauge := variationGauge
          entropic := 0
        }
    · intro variationEntropic
      simpa [coupledElectrograviticFirstVariation,
        electrograviticMetricFirstVariation, electromagneticFirstVariation,
        bcjEntropicFirstVariation, tensorPairing] using
        h {
          metricReal := 0
          metricImag := 0
          gauge := 0
          entropic := variationEntropic
        }
  · rintro ⟨hmetric, hmaxwell, hbcj⟩ variation
    simp [coupledElectrograviticFirstVariation,
      hmetric variation.metricReal variation.metricImag,
      hmaxwell variation.gauge, hbcj variation.entropic]

/-! ### A formally differentiated linearized coupled action germ -/

/-- Normed finite-dimensional product carrier for the four independent
variations. The previously exposed structure remains the named logical
carrier; this product supplies the standard normed-space instances needed by
Fréchet calculus. -/
abbrev CoupledElectrograviticVariationSpace :=
  (FourTensor × FourTensor) × ((Fin 4 → ℝ) × ℝ)

/-- Convert the normed product carrier to the named coupled variation. -/
def coupledVariationOfSpace
    (variation : CoupledElectrograviticVariationSpace) :
    CoupledElectrograviticVariation where
  metricReal := variation.1.1
  metricImag := variation.1.2
  gauge := variation.2.1
  entropic := variation.2.2

private lemma tensorPairing_add_right
    (P V W : FourTensor) :
    tensorPairing P (V + W) = tensorPairing P V + tensorPairing P W := by
  simp [tensorPairing, mul_add, Finset.sum_add_distrib]

private lemma tensorPairing_smul_right
    (r : ℝ) (P V : FourTensor) :
    tensorPairing P (r • V) = r * tensorPairing P V := by
  unfold tensorPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change P i j * (r * V i j) = r * (P i j * V i j)
  ring

private lemma electrograviticMetricFirstVariation_add
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ : ℝ) (k A : Fin 4 → ℝ) (vR vI wR wI : FourTensor) :
    electrograviticMetricFirstVariation Ric scalarR g gInv Λ S κ k A
        (vR + wR) (vI + wI) =
      electrograviticMetricFirstVariation Ric scalarR g gInv Λ S κ k A vR vI +
      electrograviticMetricFirstVariation Ric scalarR g gInv Λ S κ k A wR wI := by
  simp [electrograviticMetricFirstVariation, tensorPairing_add_right]
  ring

private lemma electrograviticMetricFirstVariation_smul
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ r : ℝ) (k A : Fin 4 → ℝ) (vR vI : FourTensor) :
    electrograviticMetricFirstVariation Ric scalarR g gInv Λ S κ k A
        (r • vR) (r • vI) =
      r * electrograviticMetricFirstVariation Ric scalarR g gInv Λ S κ k A vR vI := by
  simp [electrograviticMetricFirstVariation, tensorPairing_smul_right]
  ring

private lemma electromagneticFirstVariation_add
    (k A v w : Fin 4 → ℝ) :
    electromagneticFirstVariation k A (v + w) =
      electromagneticFirstVariation k A v + electromagneticFirstVariation k A w := by
  simp [electromagneticFirstVariation, add_mul, Finset.sum_add_distrib]

private lemma electromagneticFirstVariation_smul
    (r : ℝ) (k A v : Fin 4 → ℝ) :
    electromagneticFirstVariation k A (r • v) =
      r * electromagneticFirstVariation k A v := by
  unfold electromagneticFirstVariation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change r * v i * maxwellOp (faraday k A) k i =
    r * (v i * maxwellOp (faraday k A) k i)
  ring

private lemma bcjEntropicFirstVariation_add
    (mI c S1 S2 v w : ℝ) :
    bcjEntropicFirstVariation mI c S1 S2 (v + w) =
      bcjEntropicFirstVariation mI c S1 S2 v +
        bcjEntropicFirstVariation mI c S1 S2 w := by
  simp [bcjEntropicFirstVariation, mul_add]

private lemma bcjEntropicFirstVariation_smul
    (r mI c S1 S2 v : ℝ) :
    bcjEntropicFirstVariation mI c S1 S2 (r * v) =
      r * bcjEntropicFirstVariation mI c S1 S2 v := by
  simp [bcjEntropicFirstVariation]
  ring

/-- The coupled first variation as an actual linear map on its normed
finite-dimensional variation space. -/
noncomputable def coupledElectrograviticFirstVariationLinear
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ) :
    CoupledElectrograviticVariationSpace →ₗ[ℝ] ℝ where
  toFun variation :=
    coupledElectrograviticFirstVariation
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A
      (coupledVariationOfSpace variation)
  map_add' v w := by
    simp [coupledElectrograviticFirstVariation, coupledVariationOfSpace,
      electrograviticMetricFirstVariation_add,
      electromagneticFirstVariation_add, bcjEntropicFirstVariation_add]
    ring
  map_smul' r v := by
    simp [coupledElectrograviticFirstVariation, coupledVariationOfSpace,
      electrograviticMetricFirstVariation_smul,
      electromagneticFirstVariation_smul, bcjEntropicFirstVariation_smul]
    ring

/-- The linearized action germ whose derivative is the current coupled
post-integration-by-parts first variation. It is intentionally named a
*germ*: this does not construct the nonlinear continuum
Einstein--Hilbert--Maxwell action. -/
noncomputable def linearizedCoupledElectrograviticActionGerm
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ) :
    CoupledElectrograviticVariationSpace → ℝ :=
  coupledElectrograviticFirstVariationLinear
    Ric scalarR g gInv Λ S κ mI c S1 S2 k A

/-- The linearized coupled action germ has a genuine Fréchet derivative,
given by the continuous realization of the coupled first-variation map. -/
@[zil_level bridge_theorem]
lemma linearizedCoupledElectrograviticActionGerm_hasFDerivAt
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)
    (variation : CoupledElectrograviticVariationSpace) :
    HasFDerivAt
      (linearizedCoupledElectrograviticActionGerm
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A)
      (coupledElectrograviticFirstVariationLinear
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A).toContinuousLinearMap
      variation := by
  exact (coupledElectrograviticFirstVariationLinear
    Ric scalarR g gInv Λ S κ mI c S1 S2 k A).toContinuousLinearMap.hasFDerivAt

/-- Evaluating the formal derivative on a direction recovers exactly the
previous coupled first variation, component for component. -/
lemma linearizedCoupledElectrograviticActionGerm_fderiv_apply
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)
    (variation direction : CoupledElectrograviticVariationSpace) :
    fderiv ℝ
      (linearizedCoupledElectrograviticActionGerm
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A)
      variation direction =
      coupledElectrograviticFirstVariation
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A
        (coupledVariationOfSpace direction) := by
  rw [(linearizedCoupledElectrograviticActionGerm_hasFDerivAt
    Ric scalarR g gInv Λ S κ mI c S1 S2 k A variation).fderiv]
  rfl

/-- Joint stationarity can equivalently be expressed by saying that the
coupled first-variation linear map is zero. -/
lemma coupledElectrograviticStationary_iff_linear_eq_zero
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ) :
    IsCoupledElectrograviticStationary
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A ↔
      coupledElectrograviticFirstVariationLinear
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro variation
    exact h (coupledVariationOfSpace variation)
  · intro h variation
    have hv := LinearMap.congr_fun h
      ((variation.metricReal, variation.metricImag),
        (variation.gauge, variation.entropic))
    simpa [coupledElectrograviticFirstVariationLinear,
      coupledVariationOfSpace] using hv

/-- Derivative certificate for a genuine action at a selected background.
The action may be nonlinear. The load-bearing field is a formal
`HasFDerivAt` theorem identifying its derivative with the coupled
electrogravitic first variation; supplying a proposed action without this
proof does not construct this datum. -/
structure ElectrograviticActionDerivativeData
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ) where
  action : CoupledElectrograviticVariationSpace → ℝ
  background : CoupledElectrograviticVariationSpace
  hasFDerivAt : HasFDerivAt action
    (coupledElectrograviticFirstVariationLinear
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A).toContinuousLinearMap
    background

namespace ElectrograviticActionDerivativeData

variable (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
  (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)

/-- An action is stationary when its Fréchet derivative vanishes at the
certified background. -/
def IsStationary
    (D : ElectrograviticActionDerivativeData
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A) : Prop :=
  fderiv ℝ D.action D.background = 0

/-- Once the action derivative is formally identified, action stationarity
is exactly simultaneous metric, Maxwell and entropic stationarity. -/
@[zil_level physical_theorem]
lemma stationary_iff_coupled
    (D : ElectrograviticActionDerivativeData
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A) :
    D.IsStationary ↔
      IsCoupledElectrograviticStationary
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A := by
  constructor
  · intro hstationary
    have hclm :
        (coupledElectrograviticFirstVariationLinear
          Ric scalarR g gInv Λ S κ mI c S1 S2 k A).toContinuousLinearMap = 0 := by
      rw [← D.hasFDerivAt.fderiv]
      exact hstationary
    apply (coupledElectrograviticStationary_iff_linear_eq_zero
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A).mpr
    apply LinearMap.ext
    intro variation
    have hv := congrArg
      (fun L : CoupledElectrograviticVariationSpace →L[ℝ] ℝ => L variation) hclm
    simpa using hv
  · intro hcoupled
    have hlin := (coupledElectrograviticStationary_iff_linear_eq_zero
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A).mp hcoupled
    have hclm :
        (coupledElectrograviticFirstVariationLinear
          Ric scalarR g gInv Λ S κ mI c S1 S2 k A).toContinuousLinearMap = 0 := by
      apply ContinuousLinearMap.ext
      intro variation
      exact LinearMap.congr_fun hlin variation
    rw [IsStationary, D.hasFDerivAt.fderiv, hclm]

/-- The already-proved linearized action germ constructs a derivative
certificate at every background. This is the canonical test instance for
the general nonlinear-action interface. -/
noncomputable def ofLinearizedGerm
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)
    (background : CoupledElectrograviticVariationSpace) :
    ElectrograviticActionDerivativeData
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A where
  action := linearizedCoupledElectrograviticActionGerm
    Ric scalarR g gInv Λ S κ mI c S1 S2 k A
  background := background
  hasFDerivAt :=
    linearizedCoupledElectrograviticActionGerm_hasFDerivAt
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A background

end ElectrograviticActionDerivativeData

/-- **The electrogravitic field equations, derived from variational premises.**

Unlike `of_einstein_maxwell`, this theorem does not take either Einstein equation, the Maxwell
equation, or the entropic split as a premise:

* arbitrary metric stationarity derives `G = κ T[F]` and `Λ = κS`;
* gauge-potential stationarity derives `δdA = 0`;
* `F = dA` derives the homogeneous Maxwell equation `dF = 0`;
* scalar entropic stationarity derives `m_I c² = S₁ + S₂`.

The inverse-metric witness is retained in the conclusion, preventing the raised-index Maxwell source
from being built with an unrelated matrix. -/
@[zil_level physical_theorem]
theorem derive_electrogravitic_field_equation
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mR mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)
    (hκ : κ ≠ 0) (hInv : AreInverseMetrics g gInv)
    (hmetric :
      IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A)
    (hbcj : IsBCJEntropicStationary mI c S1 S2)
    (hmaxwell : IsElectromagneticStationary k A) :
    ElectroGravitationalFieldEquation Ric scalarR g Λ
        (maxwellStressEnergy g gInv (faraday k A)) S
        κ mR mI c S1 S2 k A
      ∧ AreInverseMetrics g gInv
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam
          + k ν * faraday k A lam μ = 0) := by
  refine ⟨?_, hInv,
    (electromagneticStationary_iff_sourceFree k A).mp hmaxwell,
    fun lam μ ν => faraday_bianchi k A lam μ ν⟩
  exact {
    gravitational := {
      kappa_ne := hκ
      fieldEquation :=
        (metricStationary_iff_complexEinstein Ric scalarR g gInv Λ S κ k A).mp hmetric
      entropicSplit := (bcjEntropicStationary_iff mI c S1 S2).mp hbcj
    }
  }

/-- **The variational electrogravitic equation with curvature constructed
from the metric field.** This is the composition missing from the earlier
capstone: its `Ric` and `scalarR` arguments are definitionally the outputs of
the metric's Levi--Civita/Fréchet-jet curvature chain. The remaining physical
premise is still stationarity of the stated post-IBP first variations; this
does not claim to derive that first variation from a continuum
Einstein--Hilbert action. -/
@[zil_level physical_theorem]
theorem derive_metricBuilt_electrogravitic_field_equation
    (g gInv : FourMetricField) (x : FourCoordinate)
    (Λ S : FourTensor) (κ mR mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)
    (hκ : κ ≠ 0) (hGeom : IsFourMetricPair g gInv)
    (hmetric : IsElectrograviticMetricStationary
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ k A)
    (hbcj : IsBCJEntropicStationary mI c S1 S2)
    (hmaxwell : IsElectromagneticStationary k A) :
    ElectroGravitationalFieldEquation
        (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
        (g x) Λ (maxwellStressEnergy (g x) (gInv x) (faraday k A)) S
        κ mR mI c S1 S2 k A
      ∧ AreInverseMetrics (g x) (gInv x)
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam
          + k ν * faraday k A lam μ = 0)
      ∧ IsTorsionFree (metricBuiltConnectionField g gInv x)
      ∧ IsMetricCompatible
        (metricBuiltConnectionField g gInv x)
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x)
        (g x) := by
  have hInv : AreInverseMetrics (g x) (gInv x) :=
    ⟨hGeom.inverse_right x, hGeom.inverse_left x⟩
  obtain ⟨H, hInv', hsourceFree, hhomogeneous⟩ :=
    derive_electrogravitic_field_equation
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ mR mI c S1 S2 k A
      hκ hInv hmetric hbcj hmaxwell
  exact
    ⟨H, hInv', hsourceFree, hhomogeneous,
      (metricBuiltConnectionField_isLeviCivita g gInv hGeom x).1,
      (metricBuiltConnectionField_isLeviCivita g gInv hGeom x).2⟩

/-- The metric-built electrogravitic equations from one joint stationarity
premise on the direct sum of metric, gauge and entropic variations. This
removes the three-predicate interface while deliberately retaining the
distinction between a bundled first variation and an underlying field
action. -/
@[zil_level physical_theorem]
theorem derive_metricBuilt_electrogravitic_field_equation_from_coupled_stationarity
    (g gInv : FourMetricField) (x : FourCoordinate)
    (Λ S : FourTensor) (κ mR mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)
    (hκ : κ ≠ 0) (hGeom : IsFourMetricPair g gInv)
    (hstationary : IsCoupledElectrograviticStationary
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ mI c S1 S2 k A) :
    ElectroGravitationalFieldEquation
        (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
        (g x) Λ (maxwellStressEnergy (g x) (gInv x) (faraday k A)) S
        κ mR mI c S1 S2 k A
      ∧ AreInverseMetrics (g x) (gInv x)
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam
          + k ν * faraday k A lam μ = 0)
      ∧ IsTorsionFree (metricBuiltConnectionField g gInv x)
      ∧ IsMetricCompatible
        (metricBuiltConnectionField g gInv x)
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x)
        (g x)
      ∧ FirstBianchi (metricBuiltRiemannAt g gInv x) := by
  obtain ⟨hmetric, hmaxwell, hbcj⟩ :=
    (coupledElectrograviticStationary_iff
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ mI c S1 S2 k A).mp hstationary
  obtain ⟨H, hInv, hsourceFree, hhomogeneous, htor, hcompat⟩ :=
    derive_metricBuilt_electrogravitic_field_equation
      g gInv x Λ S κ mR mI c S1 S2 k A
      hκ hGeom hmetric hbcj hmaxwell
  exact ⟨H, hInv, hsourceFree, hhomogeneous, htor, hcompat,
    metricBuiltRiemannAt_firstBianchi g gInv hGeom x⟩

/-- **Metric-built electrogravitic equations from a stationary action.**
Unlike the direct-sum premise theorem, this accepts an actual action and a
formal derivative certificate. Vanishing of that derivative produces the
coupled stationarity premise, hence the complex Einstein--Maxwell--entropic
system and its Levi--Civita/Bianchi geometry. The construction of the
specific nonlinear continuum action remains isolated in the certificate's
`hasFDerivAt` field. -/
@[zil_level physical_theorem]
theorem derive_metricBuilt_electrogravitic_field_equation_from_action_stationarity
    (g gInv : FourMetricField) (x : FourCoordinate)
    (Λ S : FourTensor) (κ mR mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ)
    (hκ : κ ≠ 0) (hGeom : IsFourMetricPair g gInv)
    (D : ElectrograviticActionDerivativeData
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ mI c S1 S2 k A)
    (hstationary : D.IsStationary) :
    ElectroGravitationalFieldEquation
        (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
        (g x) Λ (maxwellStressEnergy (g x) (gInv x) (faraday k A)) S
        κ mR mI c S1 S2 k A
      ∧ AreInverseMetrics (g x) (gInv x)
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam
          + k ν * faraday k A lam μ = 0)
      ∧ IsTorsionFree (metricBuiltConnectionField g gInv x)
      ∧ IsMetricCompatible
        (metricBuiltConnectionField g gInv x)
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x)
        (g x)
      ∧ FirstBianchi (metricBuiltRiemannAt g gInv x) := by
  exact
    derive_metricBuilt_electrogravitic_field_equation_from_coupled_stationarity
      g gInv x Λ S κ mR mI c S1 S2 k A hκ hGeom
      (D.stationary_iff_coupled.mp hstationary)

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellMetricDensity_covariantLine_hasDerivAt_stressEnergy where
  formalizes @ "claim:the-explicit-lorentzian-maxwell-density-minus-one-quarter-square-root-minus-det-g-times-f-lower-f-upper-has-a-genuine-covariant-metric-directional-derivative-equal-to-one-half-the-volume-density-times-the-maxwell-stress-energy-paired-with-the-constructed-inverse-metric-variation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.hasDerivAt_lorentzianVolumeDensity_affine",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.inverseMetricVariation_linearized_rightInverse",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellInvariant_line_hasDerivAt",
  caveat @ "epistemic:exact-pointwise-four-dimensional-lorentzian-density-variation-not-yet-the-spacetime-integrated-action-its-boundary-domain-or-the-combined-einstein-hilbert-maxwell-frechet-derivative"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellStressEnergy_faraday_gauge_invariant where
  formalizes @ "claim:the-maxwell-stress-energy-source-constructed-from-faraday-d-a-is-invariant-under-the-momentum-space-gauge-shift-a-to-a-plus-chi-k",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday_gauge_invariant"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_complexEinstein where
  formalizes @ "claim:stationarity-of-the-coupled-real-and-imaginary-metric-first-variation-against-every-four-dimensional-tensor-variation-is-equivalent-to-the-complex-einstein-equation-with-the-maxwell-stress-source-constructed-from-faraday-d-a",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.tensor_eq_zero_of_pairing_all_zero",
  caveat @ "premise:the-post-integration-by-parts-einstein-hilbert-maxwell-first-variation-formula-is-the-action-level-physical-input",
  caveat @ "scope:finite-four-dimensional-momentum-space-tensor-carrier-not-a-new-construction-of-the-global-einstein-hilbert-functional"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.bcjEntropicStationary_iff where
  formalizes @ "claim:stationarity-of-the-scalar-entropic-double-copy-first-variation-is-equivalent-to-m-i-c-squared-equals-s-one-plus-s-two",
  epistemic_status @ "ansatz-loaded",
  caveat @ "scope:scalar-entropic-split-carrier-not-a-derivation-of-full-amplitude-level-bcj-kinematics"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electromagneticStationary_iff_sourceFree where
  formalizes @ "claim:stationarity-of-the-post-integration-by-parts-maxwell-first-variation-against-every-gauge-potential-test-direction-is-equivalent-to-the-source-free-maxwell-equation-delta-d-a-equals-zero",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics.maxwellOp",
  caveat @ "premise:the-post-integration-by-parts-maxwell-first-variation-is-the-action-level-physical-input",
  caveat @ "scope:finite-four-dimensional-momentum-space-source-free-sector"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_electrogravitic_field_equation where
  formalizes @ "claim:the-complete-electrogravitic-field-equation-is-derived-from-metric-gauge-and-entropic-stationarity-with-the-electromagnetic-source-constructed-as-the-gauge-invariant-maxwell-stress-tensor-of-faraday-d-a",
  epistemic_status @ "ansatz-loaded",
  derives @ "claim:einstein-maxwell-g-equals-kappa-t-of-faraday-d-a",
  derives @ "claim:entropic-einstein-lambda-equals-kappa-s",
  derives @ "claim:source-free-maxwell-delta-d-a-equals-zero",
  derives @ "claim:homogeneous-maxwell-d-d-a-equals-zero",
  derives @ "claim:entropic-double-copy-m-i-c-squared-equals-s-one-plus-s-two",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_complexEinstein",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electromagneticStationary_iff_sourceFree",
  caveat @ "premise:stationarity-and-the-post-integration-by-parts-first-variation-are-physical-inputs-whereas-none-of-the-field-equations-is-supplied",
  caveat @ "premise:g-inverse-is-explicitly-required-to-be-a-two-sided-inverse-and-kappa-is-nonzero",
  caveat @ "scope:source-free-four-dimensional-momentum-space-maxwell-sector-not-the-general-sourced-global-curved-spacetime-pde",
  caveat @ "scope:the-bcj-leg-is-the-entropic-scalar-split-not-a-full-amplitude-level-double-copy-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltStationary_iff_complexEinstein where
  formalizes @ "claim:metric-stationarity-specialized-to-the-ricci-scalar-and-einstein-tensors-constructed-from-the-same-metric-field-through-frechet-jets-and-its-levi-civita-connection-is-equivalent-to-the-complex-einstein-equation",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaConnectionField",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltRicciAt_apply_eq_sum_riemann",
  caveat @ "premise:stationarity-of-the-post-integration-by-parts-metric-first-variation-remains-the-physical-input",
  caveat @ "scope:exact-coordinate-chart-metric-curvature-composition-not-yet-a-has-var-gradient-at-derivation-from-one-unified-einstein-hilbert-maxwell-action"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation where
  formalizes @ "claim:the-electrogravitic-equations-are-derived-with-ricci-scalar-and-einstein-tensors-instantiated-by-the-same-metric-built-levi-civita-curvature-chain",
  epistemic_status @ "ansatz-loaded",
  derives @ "claim:metric-to-inverse-to-levi-civita-to-riemann-to-ricci-to-scalar-to-complex-einstein-composition",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltStationary_iff_complexEinstein",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltConnectionField_isLeviCivita",
  caveat @ "premise:post-integration-by-parts-stationarity-a-symmetric-two-sided-metric-pair-and-nonzero-kappa-are-explicit-inputs",
  caveat @ "scope:one-chart-field-equation-composition-not-a-global-einstein-maxwell-cauchy-existence-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.coupledElectrograviticStationary_iff where
  formalizes @ "claim:stationarity-of-the-direct-sum-electrogravitic-first-variation-is-equivalent-to-simultaneous-metric-gauge-and-entropic-stationarity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electrograviticMetricFirstVariation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electromagneticFirstVariation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.bcjEntropicFirstVariation",
  caveat @ "scope:this-bundles-three-existing-first-variation-carriers-and-is-not-a-has-var-gradient-at-derivation-from-one-underlying-continuum-field-action"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation_from_coupled_stationarity where
  formalizes @ "claim:one-joint-stationarity-premise-on-the-direct-sum-variation-carrier-derives-the-metric-built-complex-einstein-maxwell-entropic-system",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.coupledElectrograviticStationary_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation",
  caveat @ "premise:joint-stationarity-of-the-post-integration-by-parts-first-variation-remains-explicit",
  caveat @ "scope:the-direct-sum-first-variation-is-not-the-still-missing-unified-einstein-hilbert-maxwell-field-functional"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.linearizedCoupledElectrograviticActionGerm_hasFDerivAt where
  formalizes @ "claim:the-linearized-coupled-electrogravitic-action-germ-has-a-genuine-frechet-derivative-equal-to-the-direct-sum-metric-maxwell-and-entropic-first-variation",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.coupledElectrograviticFirstVariationLinear",
  caveat @ "scope:this-is-the-exact-derivative-of-the-linearized-action-germ-not-the-nonlinear-continuum-einstein-hilbert-maxwell-action"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectrograviticActionDerivativeData.stationary_iff_coupled where
  formalizes @ "claim:for-any-action-whose-frechet-derivative-is-formally-identified-with-the-coupled-electrogravitic-first-variation-action-stationarity-is-equivalent-to-simultaneous-metric-maxwell-and-entropic-stationarity",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.coupledElectrograviticStationary_iff_linear_eq_zero",
  caveat @ "premise:a-has-fderiv-at-certificate-identifying-the-specific-actions-derivative-is-required-and-is-the-remaining-action-construction-obligation"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation_from_action_stationarity where
  formalizes @ "claim:a-stationary-action-with-a-proved-coupled-electrogravitic-frechet-derivative-derives-the-metric-built-complex-einstein-maxwell-entropic-equations-and-first-bianchi-certificate",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectrograviticActionDerivativeData.stationary_iff_coupled",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation_from_coupled_stationarity",
  caveat @ "premise:the-action-derivative-certificate-is-explicit-and-the-theorem-does-not-conjure-the-nonlinear-einstein-hilbert-determinant-inverse-variation"

zil_file_contract physlib.electrograviticActionDerivativeInterface where
  promises "An arbitrary possibly nonlinear action can enter the metric-built electrogravitic spine only through a genuine HasFDerivAt certificate identifying its derivative with the existing coupled first variation. Vanishing of that derivative is proved equivalent to simultaneous metric, Maxwell and entropic stationarity and derives the chartwise complex Einstein-Maxwell system with Levi-Civita and first-Bianchi certificates. The upstream nonlinear determinant, Lorentzian volume density, inverse metric and Einstein-Hilbert density derivatives are explicit; the existing Einstein-Palatini connection and connection-built curvature now supply the analytic Palatini reduction, while existing GHY and Bochner box-Stokes results remove the boundary term under explicit hypotheses. Atlas-independent action integration and differentiation remain separate."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectrograviticActionDerivativeData",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.coupledElectrograviticFirstVariationLinear",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.hasDerivAt_einsteinHilbertDensity_affine",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.einsteinHilbertDensity_hasDerivAt_palatini",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.integratedEinsteinHilbertPalatiniVariation_eq_bulk_of_boundary"
  ]
  forbids_substitutes [
    "treating an action formula without its derivative proof as a completed variational derivation",
    "claiming the linearized action germ is the nonlinear continuum Einstein-Hilbert-Maxwell functional",
    "hiding the determinant-inverse and boundary-term variation inside an unproved equality"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectrograviticActionDerivativeData.stationary_iff_coupled,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation_from_action_stationarity
  ]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltRiemannAt_firstBianchi where
  formalizes @ "claim:the-riemann-curvature-constructed-from-the-metric-built-levi-civita-connection-satisfies-the-first-algebraic-bianchi-identity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.riemannFromConnection_firstBianchi",
  caveat @ "scope:algebraic-first-bianchi-for-the-chart-curvature-not-the-differential-second-bianchi-or-global-cauchy-evolution"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.entropicJacobiDoubleCopy_sq_eq_gauge_product where
  formalizes @ "claim:for-the-explicit-jacobi-compliant-entropic-channels-the-square-of-the-denominated-gravity-double-copy-amplitude-equals-the-product-of-the-two-denominated-gauge-amplitudes",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.entropicJacobiGaugeAmplitude_eq_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.entropicJacobiBCJAmplitude_eq",
  caveat @ "scope:exact-for-the-models-explicit-three-channel-numerators-not-a-construction-of-general-yang-mills-numerators-from-a-lagrangian"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation.pathWeight_eq_jacobiBCJAmplitude where
  formalizes @ "claim:the-electrogravitic-complex-action-modulus-is-realized-by-the-repositorys-denominated-bcj-gravity-amplitude-on-an-explicit-three-channel-color-kinematics-jacobi-dual-family",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcjDoubleCopyAmplitude",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.entropicJacobiBCJDuality_kinematic_jacobi",
  caveat @ "scope:this-is-a-concrete-jacobi-compliant-amplitude-realization-of-the-entropic-factor-not-a-derivation-of-the-exponential-numerators-from-a-general-yang-mills-lagrangian"

zil_file_contract physlib.electrograviticMetricCurvatureComposition where
  promises "The electrogravitic stationarity theorem is specialized to Ricci and scalar curvature constructed from the same four-dimensional metric field: Frechet metric jets build the Levi-Civita connection, its Frechet jet builds Riemann and Ricci, metric trace builds the scalar, and those exact objects feed the complex Einstein tensor."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltConnectionField",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltConnectionField_isLeviCivita",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltRiemannAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltRicciAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltScalarAt"
  ]
  forbids_substitutes [
    "supplying an unrelated Ricci tensor or scalar curvature to the metric-built theorem",
    "claiming the post-integration-by-parts first variation was derived from one unified continuum action",
    "calling a chartwise variational equation a global nonlinear Cauchy existence theorem"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation
  ]

zil_file_contract physlib.electrograviticBCJAmplitudeAdapter where
  promises "The entropic complex-action modulus is connected to the existing full BCJ amplitude API by a concrete three-channel realization with positive propagator denominators and matching color and kinematic Jacobi identities."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcjDoubleCopyAmplitude",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.entropicJacobiBCJDuality"
  ]
  forbids_substitutes [
    "calling scalar entropy addition by itself a full amplitude-level double copy",
    "claiming the exponential numerator realization is derived from arbitrary Yang-Mills dynamics"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation.pathWeight_eq_jacobiBCJAmplitude
  ]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_residualCoordinate_zero where
  caveat @ "claim:the-iff-composes-through-the-complex-einstein-identification-which-is-ansatz-loaded",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_complexEinstein",
  formalizes @ "claim:electrogravitic-metric-stationarity-is-equivalent-to-componentwise-vanishing-of-one-complex-residual-whose-real-part-is-einstein-minus-kappa-times-maxwell-stress-and-whose-imaginary-part-is-entropic-curvature-minus-kappa-times-entropic-source",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_complexEinstein"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electrograviticResidual_interval_invariant where
  formalizes @ "claim:the-internal-nagao-nielsen-action-boost-mixing-the-einstein-maxwell-and-entropic-einstein-residual-components-preserves-their-lorentzian-difference-of-squares",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnActionBoost_preserves_interval",
  caveat @ "scope:this-is-an-internal-real-imaginary-action-residual-isometry-not-a-spacetime-coordinate-lorentz-transformation-or-electromagnetic-duality-rotation"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_boostedResidual_zero where
  formalizes @ "claim:electrogravitic-stationarity-is-invariant-under-every-internal-nagao-nielsen-action-boost-because-the-boosted-residual-vanishes-if-and-only-if-the-original-complex-einstein-maxwell-entropic-residual-vanishes",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_residualCoordinate_zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnActionBoost_eq_zero_iff"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltStationary_iff_boostedResidual_zero where
  formalizes @ "claim:when-the-metric-builds-its-levi-civita-connection-riemann-ricci-scalar-and-einstein-tensors-the-resulting-einstein-maxwell-entropic-stationarity-zero-set-remains-exactly-invariant-under-every-internal-nagao-nielsen-action-boost",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltStationary_iff_complexEinstein",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_boostedResidual_zero",
  caveat @ "scope:this-is-a-chartwise-metric-built-curvature-and-internal-action-boost-theorem-not-a-new-global-einstein-maxwell-cauchy-development"

zil_file_contract physlib.electrograviticInvariantResidual where
  promises "The real Einstein-Maxwell residual built from the gauge-invariant Faraday stress tensor and the imaginary entropic-Einstein residual are assembled componentwise into one complex action residual. Metric stationarity is equivalent to vanishing of that residual. The Nagao-Nielsen hyperbolic action boost preserves its unique normalized Lorentzian interval and, because opposite rapidity is an exact inverse, preserves its zero set. The result persists when Ricci, scalar curvature and Einstein tensor are constructed from the same metric through its Levi-Civita connection."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellStressEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_complexEinstein",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnInvariantGeometry_unique",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnActionBoost_eq_zero_iff"
  ]
  forbids_substitutes [
    "identifying the internal real-imaginary residual plane with the four-dimensional spacetime tangent space",
    "calling the hyperbolic residual boost an electromagnetic electric-magnetic duality rotation",
    "inferring either field equation from preservation of the indefinite interval alone since null nonzero residuals exist",
    "calling the chartwise metric-built equivalence a global nonlinear Einstein-Maxwell evolution theorem"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_residualCoordinate_zero,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electrograviticResidual_interval_invariant,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_boostedResidual_zero,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltStationary_iff_boostedResidual_zero
  ]

zil_file_contract physlib.electrograviticVariationalDerivation where
  promises "The electrogravitic equation is no longer merely supplied to the constructor. The Maxwell stress tensor is constructed from the gauge-invariant Faraday tensor and an explicit inverse metric. Arbitrary real and imaginary metric stationarity derives the complex Einstein equation; gauge-potential stationarity derives the source-free Maxwell equation; Faraday exactness derives the homogeneous Maxwell equation; and scalar entropic stationarity derives the BCJ entropy split."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_complexEinstein",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electromagneticStationary_iff_sourceFree",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.bcjEntropicStationary_iff"
  ]
  forbids_substitutes [
    "supplying the Einstein equation as a premise",
    "supplying the Maxwell equation as a premise",
    "calling the scalar entropic split a full amplitude-level BCJ derivation",
    "calling the finite momentum-space carrier a general sourced curved-spacetime PDE"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_electrogravitic_field_equation
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.electrograviticInvariantResidual

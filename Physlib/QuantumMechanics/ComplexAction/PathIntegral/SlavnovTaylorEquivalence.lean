/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRegularization
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.Mathematics.FDerivCurry
public import Mathlib.Algebra.Polynomial.Taylor
meta import Zil

/-!
# The equivalence theorem from Slavnov--Taylor identities

This module formalizes the algebraic core of Ferrari--Picariello--Quadri,
*An approach to the equivalence theorem by the Slavnov--Taylor identities*,
JHEP **04** (2002) 033.

It reuses rather than reconstructs the repository's two surrounding layers:

* `ConfigurationSpaceRegularization.gauge_integral_factorizes` supplies the exact
  measure-preserving gauge-slice/change-of-variables pattern;
* `QEDFunctionalIntegralConstruction` supplies the abelian Faddeev--Popov determinant
  and the existing BPHZ counterterm carrier;
* `ComplexActionPathIntegralWeight` supplies the Nagao--Nielsen integrand whose
  reparameterization invariance is needed by the entropic/complex-action program.

The new reusable infrastructure is the missing BRST cohomological middle:

* `BRSTContraction` packages a nilpotent linearized Slavnov--Taylor differential `s`
  and a contracting homotopy `K` with `Ks + sK = 1` (Ferrari Eqs. (5.4)--(5.5));
* `brstDoubletContraction` constructs that data for a decoupled BRST doublet
  `s(ρ,θ) = (θ,0)`, and `brstDoublet_closed_is_exact` proves its cohomology is trivial
  (Appendix B, Lemma B.1 at the isolated-doublet algebraic core);
* `RelativeBRSTContraction` packages the deformation-retract identity
  `Ks + sK = 1 - P`; this proves the exact relative-cohomology conclusion of coupled-doublet
  Lemma B.2 and, with the paper's FP-charge vanishing condition, restores the on-shell ST
  identity at every supplied loop order;
* `ferrari_ST_breaking_exact_and_restorable` proves that a Wess--Zumino-closed
  breaking is exact and that subtracting its primitive restores the ST identity;
* `ferrari_physicalGreen_parameterIndependent` proves that a physical Green
  functional annihilating BRST-exact terms is independent of a BRST-exact
  field-redefinition variation (paper Section 7);
* `complexAction_strongEquivalence_changeOfVariables` proves the Strong Equivalence
  Theorem directly for the repository's complex-action integrand under a measurable
  measure-preserving field equivalence.  The transformed measure contains the
  Jacobian data rather than setting it silently to one.
* finite `n`-point Green functions and whole parameterized families inherit the exact
  change-of-variables identity, while the cutoff-limit QED Ward identity is lifted to
  source partitions, connected generating functionals, normalized expectations,
  infinitesimal parameter identities, and source-derived one-point Green functions.
* `ferrariBVCompletedAction` resums the paper's antifield tower by the existing
  polynomial Taylor/Hasse-derivative infrastructure and proves exact finite termination;
* `FerrariFunctionalBVSystem` lifts the same construction to arbitrary normed
  field/antifield carriers using the repository's Fréchet product calculus and an
  explicit functional-derivative contraction;
* `ferrariStrongDualBVSystem` specializes that carrier to a field space and its
  strong dual, where the contraction is canonically continuous bidual evaluation;
* `massiveQEDFieldEquiv` implements the paper's Proca/Lorentz-gauge field redefinition
  as an actual finite-mode equivalence, with an explicitly unit triangular/paired-phase
  Jacobian.

## Honest scope

The paper assumes the Quasi-Classical Action Principle (QCAP): the first nonzero
loop-order breaking is a local integrated formal power series.  This module does not
claim to prove that conjecture.  Instead, locality/Wess--Zumino closure and the relevant
contracting homotopy are explicit inputs to the abstract restoration theorem.  The
concrete doublet construction proves the decoupled-doublet case.  For the coupled case,
the filtration/locality analysis is represented by an explicit relative deformation-retract
datum; the module proves Lemma B.2 and ST restoration from that datum, but does not claim
to construct it from QCAP locality alone.  Likewise the measure theorem is an exact Bochner-integral
change of variables, not a construction of interacting QED4 or of the full Proca-gauge
renormalized S-matrix.
The BV Taylor construction is the one-component polynomial action sector of Eqs.
(6.17)--(6.23), not a construction of the continuum functional antibracket or quantum
master measure.  The functional BV carrier does define the actual Fréchet partial
derivatives and Ferrari antibracket on arbitrary normed carriers.  For a field space and
its strong dual, bidual evaluation now supplies the contraction canonically; for genuinely
nuclear Schwartz/distribution carriers, a locally convex differential calculus and any
renormalized diagonal kernel remain explicit data.  No ill-defined diagonal contraction
is silently postulated, and the linearized ST differential remains model data.  The
massive-QED carrier is a finite complex mode model: its unit
Jacobian is an exact algebraic result, while infinite-dimensional determinant
regularization and interacting-QED renormalization remain outside its scope.

## References

* R. Ferrari, M. Picariello, A. Quadri, JHEP **04** (2002) 033,
  Eqs. (1.3), (4.6), (5.1)--(5.6), (6.17)--(6.23), (8.1)--(8.15), Section 7 and Appendix B.
-/

set_option autoImplicit false

open MeasureTheory
open Polynomial
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRegularization
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence

/-! ## A. Reusable BRST contraction infrastructure -/

/-- A nilpotent linearized Slavnov--Taylor differential together with a contracting
homotopy.  The identity `Ks + sK = 1` is Ferrari Eq. (5.4); it makes every `s`-closed
element in this carrier `s`-exact. -/
structure BRSTContraction (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  /-- The linearized BRST/Slavnov--Taylor differential. -/
  differential : V →ₗ[R] V
  /-- The contracting homotopy. -/
  homotopy : V →ₗ[R] V
  /-- BRST nilpotence, `s² = 0`. -/
  nilpotent : differential.comp differential = 0
  /-- The contraction equation, `Ks + sK = 1`. -/
  contraction : homotopy.comp differential + differential.comp homotopy = LinearMap.id

namespace BRSTContraction

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Contractible BRST cohomology:** `s x = 0` implies `x = s(Kx)`.  This is the
abstract algebraic step used in Ferrari Eq. (5.5) to turn a Wess--Zumino-consistent
breaking into a removable counterterm. -/
theorem closed_is_exact (C : BRSTContraction R V) {x : V}
    (hx : C.differential x = 0) :
    ∃ y, C.differential y = x := by
  refine ⟨C.homotopy x, ?_⟩
  have h := congrArg (fun f : V →ₗ[R] V => f x) C.contraction
  simpa [LinearMap.add_apply, LinearMap.comp_apply, hx] using h

end BRSTContraction

/-! ### Relative contraction for coupled doublets -/

/-- A relative BRST deformation retract.  The projector `independentPart` is the
evaluation at vanishing doublets `(ρ,θ) = (0,0)` in Ferrari Appendix B, while
`Ks + sK = 1 - P` contracts precisely the doublet-dependent sector.  Unlike a full
`BRSTContraction`, this permits nontrivial cohomology in the independent sector. -/
structure RelativeBRSTContraction (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  /-- The nilpotent linearized Slavnov--Taylor differential. -/
  differential : V →ₗ[R] V
  /-- Projection onto the doublet-independent component. -/
  independentPart : V →ₗ[R] V
  /-- Contracting homotopy on the relative/doublet-dependent component. -/
  homotopy : V →ₗ[R] V
  /-- BRST nilpotence. -/
  nilpotent : differential.comp differential = 0
  /-- Evaluation at zero doublets is a projection. -/
  independentPart_idempotent : independentPart.comp independentPart = independentPart
  /-- The relative contraction equation `Ks + sK = 1 - P`. -/
  contraction : homotopy.comp differential + differential.comp homotopy =
    LinearMap.id - independentPart

namespace RelativeBRSTContraction

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A closed element differs from its doublet-independent component by an exact term. -/
theorem closed_relative_is_exact (C : RelativeBRSTContraction R V) {x : V}
    (hx : C.differential x = 0) :
    ∃ y, C.differential y = x - C.independentPart x := by
  refine ⟨C.homotopy x, ?_⟩
  have h := congrArg (fun f : V →ₗ[R] V => f x) C.contraction
  simpa [LinearMap.add_apply, LinearMap.comp_apply, hx] using h

/-- **Ferrari Appendix B, Lemma B.2.**  If both a local functional and its
doublet-independent component are closed, their difference is simultaneously exact and
closed.  The relative deformation retract is the explicit algebraic form of the paper's
coupled-doublet filtration hypothesis. -/
theorem coupledDoublet_relative_exact (C : RelativeBRSTContraction R V) {x : V}
    (hx : C.differential x = 0)
    (hx0 : C.differential (C.independentPart x) = 0) :
    ∃ y, C.differential y = x - C.independentPart x ∧
      C.differential (x - C.independentPart x) = 0 := by
  obtain ⟨y, hy⟩ := C.closed_relative_is_exact hx
  refine ⟨y, hy, ?_⟩
  rw [map_sub, hx, hx0, sub_self]

/-- **Ferrari Eq. (B.8).**  A closed breaking with vanishing independent component
is exact.  In the paper the vanishing follows because every FP-charge `+1` variable
belongs to a doublet. -/
theorem closed_of_independentPart_eq_zero_is_exact
    (C : RelativeBRSTContraction R V) {x : V}
    (hx : C.differential x = 0) (hx0 : C.independentPart x = 0) :
    ∃ y, C.differential y = x := by
  obtain ⟨y, hy⟩ := C.closed_relative_is_exact hx
  exact ⟨y, by simpa [hx0] using hy⟩

end RelativeBRSTContraction

/-- The BRST differential of a decoupled doublet `(ρ,θ)`: `sρ = θ`, `sθ = 0`
(Ferrari Appendix B, Eq. (B.1)). -/
def brstDoubletDifferential (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :
    V × V →ₗ[R] V × V where
  toFun x := (x.2, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The elementary doublet contracting homotopy `K(ρ,θ) = (0,ρ)`. -/
def brstDoubletHomotopy (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :
    V × V →ₗ[R] V × V where
  toFun x := (0, x.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The doublet BRST differential is nilpotent: `s² = 0`. -/
theorem brstDoubletDifferential_nilpotent
    (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :
    (brstDoubletDifferential R V).comp (brstDoubletDifferential R V) = 0 := by
  apply LinearMap.ext
  intro x
  rfl

/-- The explicit doublet operators obey `Ks + sK = 1`. -/
theorem brstDoublet_contracts
    (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :
    (brstDoubletHomotopy R V).comp (brstDoubletDifferential R V) +
      (brstDoubletDifferential R V).comp (brstDoubletHomotopy R V) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext <;> simp [brstDoubletDifferential, brstDoubletHomotopy]

/-- The explicit Ferrari decoupled doublet as a reusable `BRSTContraction`. -/
def brstDoubletContraction (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :
    BRSTContraction R (V × V) where
  differential := brstDoubletDifferential R V
  homotopy := brstDoubletHomotopy R V
  nilpotent := brstDoubletDifferential_nilpotent R V
  contraction := brstDoublet_contracts R V

/-- **Ferrari Appendix B, isolated decoupled-doublet core:** every closed doublet
element is exact. -/
theorem brstDoublet_closed_is_exact
    (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    {x : V × V} (hx : brstDoubletDifferential R V x = 0) :
    ∃ y, brstDoubletDifferential R V y = x :=
  (brstDoubletContraction R V).closed_is_exact hx

/-! ## B. Wess--Zumino closure and counterterm restoration -/

/-- If a Slavnov--Taylor breaking is exact, subtracting its primitive restores the
identity.  This is the exact counterterm algebra in Ferrari Eqs. (5.5)--(5.6). -/
theorem slavnovTaylor_restored_by_exact_counterterm
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (s : V →ₗ[R] V) (Γ breaking counterterm : V)
    (hbreak : s Γ = breaking) (hexact : s counterterm = breaking) :
    s (Γ - counterterm) = 0 := by
  rw [map_sub, hbreak, hexact, sub_self]

/-- **Ferrari ST restoration theorem, one loop order.**  If the QCAP supplies a
breaking inside a contractible local carrier and the Wess--Zumino condition says it
is `s`-closed, the breaking is `s`-exact and the corresponding counterterm restores
the Slavnov--Taylor identity. -/
theorem ferrari_ST_breaking_exact_and_restorable
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C : BRSTContraction R V) (Γ breaking : V)
    (hbreak : C.differential Γ = breaking)
    (hWZ : C.differential breaking = 0) :
    ∃ counterterm,
      C.differential counterterm = breaking ∧
      C.differential (Γ - counterterm) = 0 := by
  obtain ⟨counterterm, hcounterterm⟩ := C.closed_is_exact hWZ
  exact ⟨counterterm, hcounterterm,
    slavnovTaylor_restored_by_exact_counterterm
      C.differential Γ breaking counterterm hbreak hcounterterm⟩

/-- The same restoration applies pointwise to every perturbative order for which the
QCAP/Wess--Zumino inputs are supplied.  This is the precise reusable content of the
paper's order-by-order argument, without claiming a proof of QCAP locality. -/
theorem ferrari_loopwise_ST_restoration
    {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C : BRSTContraction R V) (Γ breaking : ι → V)
    (hbreak : ∀ n, C.differential (Γ n) = breaking n)
    (hWZ : ∀ n, C.differential (breaking n) = 0) :
    ∀ n, ∃ counterterm,
      C.differential counterterm = breaking n ∧
      C.differential (Γ n - counterterm) = 0 := by
  intro n
  exact ferrari_ST_breaking_exact_and_restorable C (Γ n) (breaking n)
    (hbreak n) (hWZ n)

/-- **Ferrari Sections 6.1 and Appendix B:** coupled-doublet on-shell ST restoration.
The Wess--Zumino condition closes the breaking; the FP-charge condition is expressed by
the vanishing of its doublet-independent component.  Lemma B.2 then supplies the local
counterterm and subtraction restores the identity. -/
theorem ferrari_coupledDoublet_ST_breaking_restorable
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C : RelativeBRSTContraction R V) (Γ breaking : V)
    (hbreak : C.differential Γ = breaking)
    (hWZ : C.differential breaking = 0)
    (hFP : C.independentPart breaking = 0) :
    ∃ counterterm,
      C.differential counterterm = breaking ∧
      C.differential (Γ - counterterm) = 0 := by
  obtain ⟨counterterm, hcounterterm⟩ :=
    C.closed_of_independentPart_eq_zero_is_exact hWZ hFP
  exact ⟨counterterm, hcounterterm,
    slavnovTaylor_restored_by_exact_counterterm
      C.differential Γ breaking counterterm hbreak hcounterterm⟩

/-- Coupled-doublet ST restoration at every loop order for which QCAP locality,
Wess--Zumino closure, the relative contraction, and the FP-charge condition are supplied. -/
theorem ferrari_coupledDoublet_loopwise_ST_restoration
    {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C : RelativeBRSTContraction R V) (Γ breaking : ι → V)
    (hbreak : ∀ n, C.differential (Γ n) = breaking n)
    (hWZ : ∀ n, C.differential (breaking n) = 0)
    (hFP : ∀ n, C.independentPart (breaking n) = 0) :
    ∀ n, ∃ counterterm,
      C.differential counterterm = breaking n ∧
      C.differential (Γ n - counterterm) = 0 := by
  intro n
  exact ferrari_coupledDoublet_ST_breaking_restorable C (Γ n) (breaking n)
    (hbreak n) (hWZ n) (hFP n)

/-! ## C. Physical Green functions and the Strong Equivalence Theorem -/

/-- **Ferrari Section 7:** if a physical Green functional kills BRST-exact terms,
then any field-redefinition-parameter variation that is BRST exact has zero physical
Green function.  This is the algebraic parameter-independence conclusion of the
restored ET Slavnov--Taylor identity. -/
theorem ferrari_physicalGreen_parameterIndependent
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (s : V →ₗ[R] V) (physicalGreen : V →ₗ[R] W)
    (parameterVariation primitive : V)
    (hphysical : physicalGreen.comp s = 0)
    (hvariation : parameterVariation = s primitive) :
    physicalGreen parameterVariation = 0 := by
  rw [hvariation]
  have h := congrArg (fun f : V →ₗ[R] W => f primitive) hphysical
  simpa [LinearMap.comp_apply] using h

/-- Finite BRST-exact variation gives equality of the selected physical Green values,
not merely vanishing of an infinitesimal variation. -/
theorem ferrari_physicalGreen_eq_of_exact_difference
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (s : V →ₗ[R] V) (physicalGreen : V →ₗ[R] W)
    (observable₁ observable₂ primitive : V)
    (hphysical : physicalGreen.comp s = 0)
    (hvariation : observable₁ - observable₂ = s primitive) :
    physicalGreen observable₁ = physicalGreen observable₂ := by
  apply sub_eq_zero.mp
  rw [← map_sub, hvariation]
  have h := congrArg (fun f : V →ₗ[R] W => f primitive) hphysical
  simpa [LinearMap.comp_apply] using h

/-- **Ferrari Section 7, global family form.**  Every selected Green observable in a
parameterized family has the same value when every pairwise variation is BRST exact. -/
theorem ferrari_selectedGreen_family_parameterIndependent
    {R V W P : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (s : V →ₗ[R] V) (physicalGreen : V →ₗ[R] W)
    (observable : P → V)
    (hphysical : physicalGreen.comp s = 0)
    (hvariation : ∀ ρ σ, ∃ primitive, observable ρ - observable σ = s primitive) :
    ∀ ρ σ, physicalGreen (observable ρ) = physicalGreen (observable σ) := by
  intro ρ σ
  obtain ⟨primitive, hp⟩ := hvariation ρ σ
  exact ferrari_physicalGreen_eq_of_exact_difference s physicalGreen
    (observable ρ) (observable σ) primitive hphysical hp

/-- **Strong Equivalence Theorem as exact change of variables.**  A measurable
field equivalence preserving the transformed measure leaves every Bochner-integrable
observable integral unchanged.  The transformed measure `ν` carries the Jacobian of
the field redefinition. -/
theorem strongEquivalence_changeOfVariables
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (hμ : MeasurePreserving e μ ν)
    (observable : X → ℂ) :
    ∫ x, observable x ∂μ = ∫ y, observable (e.symm y) ∂ν := by
  rw [← hμ.integral_comp e.measurableEmbedding (fun y => observable (e.symm y))]
  congr 1
  funext x
  rw [e.symm_apply_apply]

/-- **Strong ET for finite Green functions.**  Every finite product of local
insertions has the same (unnormalized) correlation integral after the exact field
reparameterization. -/
theorem strongEquivalence_nPointGreen
    {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (hμ : MeasurePreserving e μ ν)
    (insertions : ι → X → ℂ) (labels : Finset ι) :
    (∫ x, ∏ i ∈ labels, insertions i x ∂μ) =
      ∫ y, ∏ i ∈ labels, insertions i (e.symm y) ∂ν := by
  exact strongEquivalence_changeOfVariables e hμ _

/-- **Strong ET for a whole field-redefinition family.**  If each parameter value
pushes the common original measure to its correctly transformed measure, the transformed
observable integral is independent of the field-redefinition parameter. -/
theorem strongEquivalence_family_parameterIndependent
    {P X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} (ν : P → Measure Y)
    (e : P → X ≃ᵐ Y) (hμ : ∀ ρ, MeasurePreserving (e ρ) μ (ν ρ))
    (observable : X → ℂ) :
    ∀ ρ σ,
      (∫ y, observable ((e ρ).symm y) ∂(ν ρ)) =
        ∫ y, observable ((e σ).symm y) ∂(ν σ) := by
  intro ρ σ
  rw [← strongEquivalence_changeOfVariables (e ρ) (hμ ρ) observable,
    ← strongEquivalence_changeOfVariables (e σ) (hμ σ) observable]

/-- **Complex-action Strong Equivalence Theorem.**  The Nagao--Nielsen path-integral
weight has the same generating integral before and after a measure-preserving field
reparameterization, with both real and imaginary actions pulled through the inverse
field equivalence. -/
theorem complexAction_strongEquivalence_changeOfVariables
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (hμ : MeasurePreserving e μ ν)
    (S_R S_I : X → ℝ) (ℏ : ℝ) :
    (∫ x, complexActionPathIntegralWeight (S_R x) (S_I x) ℏ ∂μ) =
      ∫ y, complexActionPathIntegralWeight
        (S_R (e.symm y)) (S_I (e.symm y)) ℏ ∂ν :=
  strongEquivalence_changeOfVariables e hμ _

/-- **QED/complex-action capstone.**  In the existing regularized abelian carrier,
the Faddeev--Popov determinant is field independent while the complex-action
functional integral is invariant under the supplied exact field equivalence. -/
theorem qed_FP_and_complexAction_equivalence
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (A A' : Fin n → ℝ)
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (hμ : MeasurePreserving e μ ν)
    (S_R S_I : X → ℝ) (ℏ : ℝ) :
    fpDeterminant M A = fpDeterminant M A' ∧
      (∫ x, complexActionPathIntegralWeight (S_R x) (S_I x) ℏ ∂μ) =
        ∫ y, complexActionPathIntegralWeight
          (S_R (e.symm y)) (S_I (e.symm y)) ℏ ∂ν :=
  ⟨abelian_FP_decouples M A A',
    complexAction_strongEquivalence_changeOfVariables e hμ S_R S_I ℏ⟩

/-- **Gauge-slice/FP/complex-action equivalence chain.**  This capstone connects the
three existing repository carriers used by the Ferrari construction: a gauge-invariant
observable factors through the gauge slice, the abelian Faddeev--Popov determinant is
field independent, and the complex-action functional integral is invariant under the
supplied exact field equivalence.  The gauge volume and transformed measure retain the
two Jacobian factors explicitly. -/
theorem ferrari_gaugeSlice_FP_complexAction_chain
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (A A' : Fin n → ℝ)
    {X F G Y : Type*} [MeasurableSpace X] [MeasurableSpace F]
    [MeasurableSpace G] [MeasurableSpace Y]
    {μ : Measure X} {μF : Measure F} {μG : Measure G} {ν : Measure Y}
    [SigmaFinite μF] [SigmaFinite μG]
    (sliceEquiv : X ≃ᵐ F × G)
    (hslice : MeasurePreserving sliceEquiv μ (μF.prod μG))
    (observable : X → ℝ) (hint : Integrable observable μ) (g₀ : G)
    (hconst : ∀ p g, observable (sliceEquiv.symm (p, g)) =
      observable (sliceEquiv.symm (p, g₀)))
    (fieldEquiv : X ≃ᵐ Y) (hfield : MeasurePreserving fieldEquiv μ ν)
    (S_R S_I : X → ℝ) (ℏ : ℝ) :
    (∫ x, observable x ∂μ) =
        (μG Set.univ).toReal • ∫ p, observable (sliceEquiv.symm (p, g₀)) ∂μF ∧
      fpDeterminant M A = fpDeterminant M A' ∧
      (∫ x, complexActionPathIntegralWeight (S_R x) (S_I x) ℏ ∂μ) =
        ∫ y, complexActionPathIntegralWeight
          (S_R (fieldEquiv.symm y)) (S_I (fieldEquiv.symm y)) ℏ ∂ν := by
  exact ⟨gauge_integral_factorizes sliceEquiv hslice observable hint g₀ hconst,
    abelian_FP_decouples M A A',
    complexAction_strongEquivalence_changeOfVariables fieldEquiv hfield S_R S_I ℏ⟩

/-! ## D. Fréchet-functional Batalin--Vilkovisky carrier -/

/-- A Ferrari BV functional on an arbitrary antighost/antifield configuration carrier. -/
abbrev FerrariBVFunctional (Cbar CbarStar : Type*) := Cbar × CbarStar → ℂ

/-- The functional BV data used in Ferrari Eqs. (6.6)--(6.9).  `contraction` is the
explicit continuous contraction of the antifield and antighost functional derivatives;
for a distributional field space this is where the kernel/renormalization datum belongs.
`delta` is the linearized on-shell Slavnov--Taylor differential. -/
structure FerrariFunctionalBVSystem
    (Cbar CbarStar : Type*)
    [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    [NormedAddCommGroup CbarStar] [NormedSpace ℂ CbarStar] where
  contraction :
    (CbarStar →L[ℂ] ℂ) →L[ℂ] (Cbar →L[ℂ] ℂ) →L[ℂ] ℂ
  delta : FerrariBVFunctional Cbar CbarStar →ₗ[ℂ]
    FerrariBVFunctional Cbar CbarStar

/-- The canonical BV contraction when the antifield carrier is the strong dual of
the field carrier.  An antifield derivative lies in the bidual
`(StrongDual ℂ Cbar) →L[ℂ] ℂ`, while a field derivative lies in
`StrongDual ℂ Cbar`; their contraction is therefore ordinary continuous evaluation.
This supplies a genuine infinite-dimensional Banach-space contraction without a
basis sum or an informal diagonal distribution kernel. -/
noncomputable def ferrariStrongDualContraction
    (Cbar : Type*) [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar] :
    (StrongDual ℂ Cbar →L[ℂ] ℂ) →L[ℂ] (Cbar →L[ℂ] ℂ) →L[ℂ] ℂ :=
  (isBoundedBilinearMap_apply (𝕜 := ℂ)
    (E := StrongDual ℂ Cbar) (F := ℂ)).toContinuousLinearMap

/-- Canonical strong-dual contraction is exactly bidual evaluation. -/
@[simp] theorem ferrariStrongDualContraction_apply
    {Cbar : Type*} [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    (u : StrongDual ℂ (StrongDual ℂ Cbar)) (v : StrongDual ℂ Cbar) :
    ferrariStrongDualContraction Cbar u v = u v := by
  rfl

/-- The canonical BV contraction obeys the sharp operator-norm product bound, so
the field/antifield pairing is jointly continuous on the normed carrier. -/
theorem norm_ferrariStrongDualContraction_le
    {Cbar : Type*} [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    (u : StrongDual ℂ (StrongDual ℂ Cbar)) (v : StrongDual ℂ Cbar) :
    ‖ferrariStrongDualContraction Cbar u v‖ ≤ ‖u‖ * ‖v‖ := by
  exact u.le_opNorm v

/-- A functional BV system whose field/antifield contraction is the canonical
strong-dual evaluation.  Only the linearized ST differential remains model data. -/
noncomputable def ferrariStrongDualBVSystem
    (Cbar : Type*) [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    (delta : FerrariBVFunctional Cbar (StrongDual ℂ Cbar) →ₗ[ℂ]
      FerrariBVFunctional Cbar (StrongDual ℂ Cbar)) :
    FerrariFunctionalBVSystem Cbar (StrongDual ℂ Cbar) where
  contraction := ferrariStrongDualContraction Cbar
  delta := delta

/-- Fréchet functional derivative with respect to the antighost coordinate. -/
noncomputable def ferrariCbarDerivative
    {Cbar CbarStar : Type*}
    [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    [NormedAddCommGroup CbarStar] [NormedSpace ℂ CbarStar]
    (F : FerrariBVFunctional Cbar CbarStar) (z : Cbar × CbarStar) : Cbar →L[ℂ] ℂ :=
  fderiv ℂ (fun cbar => F (cbar, z.2)) z.1

/-- Fréchet functional derivative with respect to the antifield coordinate. -/
noncomputable def ferrariAntifieldDerivative
    {Cbar CbarStar : Type*}
    [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    [NormedAddCommGroup CbarStar] [NormedSpace ℂ CbarStar]
    (F : FerrariBVFunctional Cbar CbarStar) (z : Cbar × CbarStar) : CbarStar →L[ℂ] ℂ :=
  fderiv ℂ (fun cbarStar => F (z.1, cbarStar)) z.2

/-- The repository's product Fréchet calculus proves that the full functional derivative
is exactly the sum of the antighost and antifield partial derivatives. -/
theorem ferrariFunctionalDerivative_split
    {Cbar CbarStar : Type*}
    [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    [NormedAddCommGroup CbarStar] [NormedSpace ℂ CbarStar]
    (F : FerrariBVFunctional Cbar CbarStar) (z : Cbar × CbarStar)
    (hF : DifferentiableAt ℂ F z) :
    fderiv ℂ F z =
      (ferrariCbarDerivative F z).comp (ContinuousLinearMap.fst ℂ Cbar CbarStar) +
      (ferrariAntifieldDerivative F z).comp
        (ContinuousLinearMap.snd ℂ Cbar CbarStar) := by
  exact fderiv_wrt_prod hF

/-- **Ferrari Eq. (6.7):** the on-shell antibracket contracts the derivative of its
first argument with respect to `cbarStar` against the derivative of its second argument
with respect to `cbar`. -/
noncomputable def ferrariFunctionalAntibracket
    {Cbar CbarStar : Type*}
    [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    [NormedAddCommGroup CbarStar] [NormedSpace ℂ CbarStar]
    (B : FerrariFunctionalBVSystem Cbar CbarStar)
    (F G : FerrariBVFunctional Cbar CbarStar) : FerrariBVFunctional Cbar CbarStar :=
  fun z => B.contraction (ferrariAntifieldDerivative F z) (ferrariCbarDerivative G z)

/-- **Ferrari Eq. (6.6):** the functional ST residual `delta Gamma + (Gamma,Gamma)`. -/
noncomputable def ferrariFunctionalSTResidual
    {Cbar CbarStar : Type*}
    [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    [NormedAddCommGroup CbarStar] [NormedSpace ℂ CbarStar]
    (B : FerrariFunctionalBVSystem Cbar CbarStar)
    (Gamma : FerrariBVFunctional Cbar CbarStar) : FerrariBVFunctional Cbar CbarStar :=
  B.delta Gamma + ferrariFunctionalAntibracket B Gamma Gamma

/-- The continuum-capable functional Slavnov--Taylor equation is vanishing of the
Fréchet/antibracket residual. -/
def SatisfiesFerrariFunctionalST
    {Cbar CbarStar : Type*}
    [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    [NormedAddCommGroup CbarStar] [NormedSpace ℂ CbarStar]
    (B : FerrariFunctionalBVSystem Cbar CbarStar)
    (Gamma : FerrariBVFunctional Cbar CbarStar) : Prop :=
  ferrariFunctionalSTResidual B Gamma = 0

/-- Pointwise form of Ferrari's functional master identity.  Unlike the earlier scalar
Taylor shadow, both genuine Fréchet partial derivatives and their supplied contraction
remain visible in the statement. -/
theorem satisfiesFerrariFunctionalST_iff_pointwise
    {Cbar CbarStar : Type*}
    [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    [NormedAddCommGroup CbarStar] [NormedSpace ℂ CbarStar]
    (B : FerrariFunctionalBVSystem Cbar CbarStar)
    (Gamma : FerrariBVFunctional Cbar CbarStar) :
    SatisfiesFerrariFunctionalST B Gamma ↔
      ∀ z, B.delta Gamma z + B.contraction
        (ferrariAntifieldDerivative Gamma z) (ferrariCbarDerivative Gamma z) = 0 := by
  simp only [SatisfiesFerrariFunctionalST, ferrariFunctionalSTResidual,
    ferrariFunctionalAntibracket, Pi.add_apply, Pi.zero_apply, funext_iff]

/-- With the strong-dual carrier, Ferrari's functional antibracket is literally
the antifield derivative evaluated on the antighost derivative.  This is the
Banach-space realization of the contraction in paper Eq. (6.7). -/
theorem ferrariStrongDualAntibracket_apply
    {Cbar : Type*} [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    (delta : FerrariBVFunctional Cbar (StrongDual ℂ Cbar) →ₗ[ℂ]
      FerrariBVFunctional Cbar (StrongDual ℂ Cbar))
    (F G : FerrariBVFunctional Cbar (StrongDual ℂ Cbar))
    (z : Cbar × StrongDual ℂ Cbar) :
    ferrariFunctionalAntibracket (ferrariStrongDualBVSystem Cbar delta) F G z =
      ferrariAntifieldDerivative F z (ferrariCbarDerivative G z) := by
  rfl

/-- An antighost-independent second functional has zero Ferrari antibracket with
every first functional at that configuration. -/
theorem ferrariStrongDualAntibracket_eq_zero_of_cbarDerivative_eq_zero
    {Cbar : Type*} [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    (delta : FerrariBVFunctional Cbar (StrongDual ℂ Cbar) →ₗ[ℂ]
      FerrariBVFunctional Cbar (StrongDual ℂ Cbar))
    (F G : FerrariBVFunctional Cbar (StrongDual ℂ Cbar))
    (z : Cbar × StrongDual ℂ Cbar)
    (hG : ferrariCbarDerivative G z = 0) :
    ferrariFunctionalAntibracket (ferrariStrongDualBVSystem Cbar delta) F G z = 0 := by
  rw [ferrariStrongDualAntibracket_apply, hG]
  exact map_zero _

/-- **Concrete functional ST equation.**  On a normed field carrier and its strong
dual, the master equation has no abstract contraction left: it is exactly
`δΓ + (D_antifield Γ)(D_field Γ) = 0` at every configuration. -/
theorem satisfiesFerrariStrongDualST_iff
    {Cbar : Type*} [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    (delta : FerrariBVFunctional Cbar (StrongDual ℂ Cbar) →ₗ[ℂ]
      FerrariBVFunctional Cbar (StrongDual ℂ Cbar))
    (Gamma : FerrariBVFunctional Cbar (StrongDual ℂ Cbar)) :
    SatisfiesFerrariFunctionalST (ferrariStrongDualBVSystem Cbar delta) Gamma ↔
      ∀ z, delta Gamma z +
        ferrariAntifieldDerivative Gamma z (ferrariCbarDerivative Gamma z) = 0 := by
  rw [satisfiesFerrariFunctionalST_iff_pointwise]
  rfl

/-- A functional that is closed under the supplied linearized ST differential and
independent of the antighost coordinate satisfies the full strong-dual master equation.
This isolates a reusable sufficient condition without assuming a particular QED action. -/
theorem satisfiesFerrariStrongDualST_of_delta_eq_zero_of_cbarDerivative_eq_zero
    {Cbar : Type*} [NormedAddCommGroup Cbar] [NormedSpace ℂ Cbar]
    (delta : FerrariBVFunctional Cbar (StrongDual ℂ Cbar) →ₗ[ℂ]
      FerrariBVFunctional Cbar (StrongDual ℂ Cbar))
    (Gamma : FerrariBVFunctional Cbar (StrongDual ℂ Cbar))
    (hdelta : delta Gamma = 0)
    (hcbar : ∀ z, ferrariCbarDerivative Gamma z = 0) :
    SatisfiesFerrariFunctionalST (ferrariStrongDualBVSystem Cbar delta) Gamma := by
  rw [satisfiesFerrariStrongDualST_iff]
  intro z
  rw [hdelta, Pi.zero_apply, zero_add, hcbar z]
  exact map_zero _

/-! ## E. Polynomial Batalin--Vilkovisky antifield completion -/

/-- The scalar polynomial sector of the on-shell BV completion in Ferrari
Eqs. (6.17)--(6.23).  Expanding at `Φ` and evaluating at `-̅c⁺` produces the
alternating antifield tower without duplicating Taylor/derivative infrastructure. -/
noncomputable def ferrariBVCompletedAction (S : ℂ[X]) (Φ cbarStar : ℂ) : ℂ :=
  (Polynomial.taylor Φ S).eval (-cbarStar)

/-- The BV antifield completion resums exactly to the shifted polynomial action. -/
theorem ferrariBVCompletedAction_eq_shifted
    (S : ℂ[X]) (Φ cbarStar : ℂ) :
    ferrariBVCompletedAction S Φ cbarStar = S.eval (Φ - cbarStar) := by
  rw [ferrariBVCompletedAction, Polynomial.taylor_eval]
  congr 1
  ring

/-- At zero antifield the completion recovers the original action. -/
@[simp] theorem ferrariBVCompletedAction_zero_antifield
    (S : ℂ[X]) (Φ : ℂ) :
    ferrariBVCompletedAction S Φ 0 = S.eval Φ := by
  simp [ferrariBVCompletedAction_eq_shifted]

/-- The coefficient of antifield order `j` is the `j`th Hasse derivative evaluated
at the field.  Over `ℂ`, this is the factorial-normalized derivative appearing in
Ferrari Eq. (6.17). -/
theorem ferrariBV_antifieldCoefficient_eq_hasseDeriv
    (S : ℂ[X]) (Φ : ℂ) (j : ℕ) :
    (Polynomial.taylor Φ S).coeff j = (Polynomial.hasseDeriv j S).eval Φ :=
  Polynomial.taylor_coeff Φ S j

/-- **Ferrari Eq. (6.21):** the full antifield series of a polynomial action is an
actual finite sum, ending at its degree. -/
theorem ferrariBVCompletedAction_eq_finiteTower
    (S : ℂ[X]) (Φ cbarStar : ℂ) :
    ferrariBVCompletedAction S Φ cbarStar =
      ∑ j ∈ Finset.range (S.natDegree + 1),
        (Polynomial.hasseDeriv j S).eval Φ * (-cbarStar) ^ j := by
  rw [ferrariBVCompletedAction, Polynomial.eval_eq_sum_range]
  simp only [Polynomial.natDegree_taylor, Polynomial.taylor_coeff]

/-- **Ferrari Eq. (6.23):** if the action has degree at most `M`, truncation at
antifield number `M` is already exact. -/
theorem ferrariBVCompletedAction_eq_boundedTower
    (S : ℂ[X]) (Φ cbarStar : ℂ) (M : ℕ) (hM : S.natDegree ≤ M) :
    ferrariBVCompletedAction S Φ cbarStar =
      ∑ j ∈ Finset.range (M + 1),
        (Polynomial.hasseDeriv j S).eval Φ * (-cbarStar) ^ j := by
  rw [ferrariBVCompletedAction]
  rw [Polynomial.eval_eq_sum_range' (n := M + 1)]
  · simp only [Polynomial.taylor_coeff]
  · simpa using hM

/-- The completed action is invariant under the simultaneous BV shift of field and
antifield.  This is the finite polynomial translation identity behind cancellation of
the successive terms; it is not relabeled as the full continuum quantum master equation. -/
theorem ferrariBVCompletedAction_diagonalShift_invariant
    (S : ℂ[X]) (Φ cbarStar shift : ℂ) :
    ferrariBVCompletedAction S (Φ + shift) (cbarStar + shift) =
      ferrariBVCompletedAction S Φ cbarStar := by
  simp only [ferrariBVCompletedAction_eq_shifted]
  congr 1
  ring

/-! ## F. Massive-QED Proca/Lorentz-gauge field equivalence -/

/-- A finite regularized mode of the fields in Ferrari Section 8: a `d`-component
gauge field, the auxiliary scalar, and one fermion/antifermion component. -/
@[ext] structure MassiveQEDFiniteField (d : ℕ) where
  gauge : Fin d → ℂ
  auxiliary : ℂ
  fermion : ℂ
  antifermion : ℂ

/-- Ferrari Eqs. (8.4)--(8.6), parameterized as in Eq. (8.10).  `gradient` is the
chosen finite derivative of the auxiliary mode and `kappa` represents `√α/m`. -/
noncomputable def massiveQEDFieldRedefinition {d : ℕ}
    (gradient : Fin d → ℂ) (charge kappa rho : ℂ)
    (F : MassiveQEDFiniteField d) : MassiveQEDFiniteField d where
  gauge μ := F.gauge μ + rho * kappa * F.auxiliary * gradient μ
  auxiliary := F.auxiliary
  fermion := Complex.exp (Complex.I * charge * rho * kappa * F.auxiliary) * F.fermion
  antifermion :=
    Complex.exp (-(Complex.I * charge * rho * kappa * F.auxiliary)) * F.antifermion

/-- The identity parameter leaves every field unchanged. -/
@[simp] theorem massiveQEDFieldRedefinition_zero {d : ℕ}
    (gradient : Fin d → ℂ) (charge kappa : ℂ) (F : MassiveQEDFiniteField d) :
    massiveQEDFieldRedefinition gradient charge kappa 0 F = F := by
  ext μ <;> simp [massiveQEDFieldRedefinition]

/-- The parameterized field redefinitions compose additively. -/
theorem massiveQEDFieldRedefinition_add {d : ℕ}
    (gradient : Fin d → ℂ) (charge kappa rho sigma : ℂ)
    (F : MassiveQEDFiniteField d) :
    massiveQEDFieldRedefinition gradient charge kappa rho
        (massiveQEDFieldRedefinition gradient charge kappa sigma F) =
      massiveQEDFieldRedefinition gradient charge kappa (rho + sigma) F := by
  ext μ
  · simp only [massiveQEDFieldRedefinition]
    ring
  · rfl
  · simp only [massiveQEDFieldRedefinition]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    ring
  · simp only [massiveQEDFieldRedefinition]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    ring

/-- The massive-QED transformation is globally invertible in the finite carrier;
the inverse is the transformation with parameter `-rho`. -/
noncomputable def massiveQEDFieldEquiv {d : ℕ}
    (gradient : Fin d → ℂ) (charge kappa rho : ℂ) :
    MassiveQEDFiniteField d ≃ MassiveQEDFiniteField d where
  toFun := massiveQEDFieldRedefinition gradient charge kappa rho
  invFun := massiveQEDFieldRedefinition gradient charge kappa (-rho)
  left_inv F := by
    rw [massiveQEDFieldRedefinition_add]
    simp
  right_inv F := by
    rw [massiveQEDFieldRedefinition_add]
    simp

/-- The bosonic derivative of `(A,φ) ↦ (A + ρκ dφ,φ)` is block upper
triangular. -/
def massiveQEDBosonicJacobian {d : ℕ}
    (gradient : Fin d → ℂ) (kappa rho : ℂ) :
    Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks 1 (fun μ _ => rho * kappa * gradient μ) 0 1

/-- The finite bosonic block Jacobian has determinant one. -/
@[simp] theorem massiveQEDBosonicJacobian_det {d : ℕ}
    (gradient : Fin d → ℂ) (kappa rho : ℂ) :
    (massiveQEDBosonicJacobian gradient kappa rho).det = 1 := by
  simp [massiveQEDBosonicJacobian]

/-- The opposite fermion and antifermion phases cancel exactly. -/
theorem massiveQEDFermionPhaseJacobian {charge kappa rho auxiliary : ℂ} :
    Complex.exp (Complex.I * charge * rho * kappa * auxiliary) *
      Complex.exp (-(Complex.I * charge * rho * kappa * auxiliary)) = 1 := by
  rw [← Complex.exp_add]
  simp

/-- **Ferrari Section 8 finite Jacobian theorem:** the triangular bosonic determinant
times the paired fermion phase factor is exactly one. -/
theorem massiveQEDFieldRedefinition_unitJacobian {d : ℕ}
    (gradient : Fin d → ℂ) (charge kappa rho auxiliary : ℂ) :
    (massiveQEDBosonicJacobian gradient kappa rho).det *
      (Complex.exp (Complex.I * charge * rho * kappa * auxiliary) *
        Complex.exp (-(Complex.I * charge * rho * kappa * auxiliary))) = 1 := by
  rw [massiveQEDBosonicJacobian_det, massiveQEDFermionPhaseJacobian, mul_one]

/-! ## G. Vytheeswaran gauge unfixing of the Abelian Proca model

This section reuses the finite massive-QED carrier above for the exact algebraic core of
A. S. Vytheeswaran, *Gauge Invariances in the Proca Model*, IJMP A **13** (1998)
765--778.  The paper's distribution-valued equal-time bracket is represented first by
its two-constraint coefficient matrix.  The two gauge-unfixing choices are then actual
idempotent projections on this constraint-value carrier.  Finally, case (ii) is realized
as an invertible Stückelberg gauge action on `MassiveQEDFiniteField`; the combination
`A + dθ`, its quadratic mass term, and the unitary-gauge reduction to Proca are proved
exactly.

The finite carrier isolates the algebra that is independent of a choice of spatial
test-function/distribution space.  It does not identify pointwise multiplication with
the paper's delta-distribution Poisson bracket, construct the continuum Hamiltonian, or
infer Poincaré closure without the projected Dirac-bracket hypotheses used in the paper.
-/

/-- The coefficient carrier for the two Proca constraints `(Q₁,Q₂)`.
`Q₁ = π⁰` is primary and `Q₂ = -∂ᵢπⁱ + m²A⁰` is the Gauss/secondary constraint. -/
abbrev ProcaConstraintPair := Fin 2 → ℂ

/-- The primary constraint basis vector `Q₁`. -/
def procaPrimaryConstraint : ProcaConstraintPair := ![1, 0]

/-- The secondary Gauss constraint basis vector `Q₂`. -/
def procaGaussConstraint : ProcaConstraintPair := ![0, 1]

/-- Vytheeswaran Eq. (2.4) on constraint coefficients:
`{Q₁,Q₂} = -m²`, with the spatial delta distribution factored out. -/
def procaConstraintBracket (massSq : ℂ)
    (u v : ProcaConstraintPair) : ℂ :=
  massSq * (u 1 * v 0 - u 0 * v 1)

/-- Vytheeswaran Eq. (2.5), the antisymmetric second-class constraint matrix
`[[0,-m²],[m²,0]]`, after factoring out the spatial delta distribution. -/
def procaConstraintMatrix (massSq : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -massSq; massSq, 0]

/-- The determinant of the Abelian Proca constraint matrix is `m⁴`. -/
lemma procaConstraintMatrix_det (massSq : ℂ) :
    (procaConstraintMatrix massSq).det = massSq ^ 2 := by
  simp [procaConstraintMatrix, Matrix.det_fin_two]
  ring

/-- Nonzero mass makes the two Proca constraints genuinely second class. -/
lemma procaConstraintMatrix_nonsingular {massSq : ℂ} (hm : massSq ≠ 0) :
    (procaConstraintMatrix massSq).det ≠ 0 := by
  rw [procaConstraintMatrix_det]
  exact pow_ne_zero 2 hm

/-- The explicit inverse of the Proca constraint matrix, corresponding to the kernel
used in the Dirac bracket (paper Eq. (2.6)). -/
noncomputable def procaConstraintMatrixInverse (massSq : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, massSq⁻¹; -massSq⁻¹, 0]

/-- The displayed inverse really is a right inverse whenever `m² ≠ 0`. -/
lemma procaConstraintMatrix_mul_inverse {massSq : ℂ} (hm : massSq ≠ 0) :
    procaConstraintMatrix massSq * procaConstraintMatrixInverse massSq = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [procaConstraintMatrix, procaConstraintMatrixInverse, hm]

/-- The primary/secondary bracket is exactly `-m²` (paper Eq. (2.4)). -/
@[simp] lemma proca_primary_gauss_bracket (massSq : ℂ) :
    procaConstraintBracket massSq procaPrimaryConstraint procaGaussConstraint = -massSq := by
  simp [procaConstraintBracket, procaPrimaryConstraint, procaGaussConstraint]

/-- Case (i), paper Eq. (3.1): `χ = -(m²)⁻¹ Q₁`. -/
noncomputable def procaCaseIChi (massSq : ℂ) : ProcaConstraintPair :=
  (-massSq⁻¹) • procaPrimaryConstraint

/-- Case (i), paper Eq. (3.1): the discarded gauge-fixing constraint `ψ = Q₂`. -/
def procaCaseIPsi : ProcaConstraintPair := procaGaussConstraint

/-- Case (ii), paper Eq. (3.8): `χ' = (m²)⁻¹ Q₂`. -/
noncomputable def procaCaseIIChi (massSq : ℂ) : ProcaConstraintPair :=
  massSq⁻¹ • procaGaussConstraint

/-- Case (ii), paper Eq. (3.8): the discarded gauge-fixing constraint `ψ' = Q₁`. -/
def procaCaseIIPsi : ProcaConstraintPair := procaPrimaryConstraint

/-- The case-(i) normalization makes `(χ,ψ)` a canonical pair. -/
lemma proca_caseI_canonical {massSq : ℂ} (hm : massSq ≠ 0) :
    procaConstraintBracket massSq (procaCaseIChi massSq) procaCaseIPsi = 1 := by
  simp [procaConstraintBracket, procaCaseIChi, procaCaseIPsi,
    procaPrimaryConstraint, procaGaussConstraint, hm]

/-- The case-(ii) normalization makes `(χ',ψ')` a canonical pair. -/
lemma proca_caseII_canonical {massSq : ℂ} (hm : massSq ≠ 0) :
    procaConstraintBracket massSq (procaCaseIIChi massSq) procaCaseIIPsi = 1 := by
  simp [procaConstraintBracket, procaCaseIIChi, procaCaseIIPsi,
    procaPrimaryConstraint, procaGaussConstraint, hm]

/-- Gauge unfixing case (i) on the constraint-value carrier: retain `Q₁` and set
the discarded gauge-fixing value `Q₂` to zero. -/
def procaGaugeUnfixCaseIProjection (q : ProcaConstraintPair) :
    ProcaConstraintPair := ![q 0, 0]

/-- Gauge unfixing case (ii): set the discarded primary value `Q₁` to zero and
retain `Q₂`. -/
def procaGaugeUnfixCaseIIProjection (q : ProcaConstraintPair) :
    ProcaConstraintPair := ![0, q 1]

/-- Appendix A.1 for the case-(i) constraint projection, here as exact equality. -/
lemma procaGaugeUnfixCaseIProjection_idempotent (q : ProcaConstraintPair) :
    procaGaugeUnfixCaseIProjection (procaGaugeUnfixCaseIProjection q) =
      procaGaugeUnfixCaseIProjection q := by
  funext i
  fin_cases i <;> rfl

/-- Appendix A.1 for the case-(ii) constraint projection, here as exact equality. -/
lemma procaGaugeUnfixCaseIIProjection_idempotent (q : ProcaConstraintPair) :
    procaGaugeUnfixCaseIIProjection (procaGaugeUnfixCaseIIProjection q) =
      procaGaugeUnfixCaseIIProjection q := by
  funext i
  fin_cases i <;> rfl

/-- Case (i) kills the discarded Gauss/gauge-fixing constraint. -/
@[simp] lemma procaGaugeUnfixCaseIProjection_discards_gauss (q : ProcaConstraintPair) :
    procaGaugeUnfixCaseIProjection q 1 = 0 := rfl

/-- Case (i) retains the primary/first-class constraint value. -/
@[simp] lemma procaGaugeUnfixCaseIProjection_retains_primary (q : ProcaConstraintPair) :
    procaGaugeUnfixCaseIProjection q 0 = q 0 := rfl

/-- Case (ii) kills the discarded primary/gauge-fixing constraint. -/
@[simp] lemma procaGaugeUnfixCaseIIProjection_discards_primary (q : ProcaConstraintPair) :
    procaGaugeUnfixCaseIIProjection q 0 = 0 := rfl

/-- Case (ii) retains the secondary/first-class constraint value. -/
@[simp] lemma procaGaugeUnfixCaseIIProjection_retains_gauss (q : ProcaConstraintPair) :
    procaGaugeUnfixCaseIIProjection q 1 = q 1 := rfl

/-! ## G.1. Gauge unfixing on affine observables and the Dirac bracket -/

/-- An affine observable on the two-dimensional Proca constraint sector.  The first
component is the constant term and the second component contains the coefficients of
`Q₁` and `Q₂`.  This is the smallest observable carrier on which the paper's ordered
exponential projector and Dirac-bracket comparison are both nontrivial. -/
abbrev ProcaAffineObservable := ℂ × ProcaConstraintPair

/-- Embed a scalar as a constant Proca affine observable. -/
def procaAffineConstant (z : ℂ) : ProcaAffineObservable := (z, 0)

/-- Embed a linear combination of the two constraints as an affine observable. -/
def procaAffineConstraint (q : ProcaConstraintPair) : ProcaAffineObservable := (0, q)

/-- The ordered constraint basis `(Q₁,Q₂)` used in the Dirac correction. -/
def procaConstraintBasis (i : Fin 2) : ProcaConstraintPair :=
  ![if i = 0 then 1 else 0, if i = 1 then 1 else 0]

/-- The Poisson bracket of affine constraint-sector observables.  Constants are central,
so the bracket is the constant observable obtained from the linear coefficients. -/
def procaAffinePoissonBracket (massSq : ℂ)
    (B C : ProcaAffineObservable) : ProcaAffineObservable :=
  procaAffineConstant (procaConstraintBracket massSq B.2 C.2)

/-- The two-constraint Dirac bracket
`{B,C}_D = {B,C} - {B,Qₐ}(C⁻¹)^{ab}{Q_b,C}` on affine observables, using the
explicit inverse of the Proca constraint matrix. -/
noncomputable def procaAffineDiracBracket (massSq : ℂ)
    (B C : ProcaAffineObservable) : ProcaAffineObservable :=
  procaAffineConstant
    (procaConstraintBracket massSq B.2 C.2 -
      ∑ i, ∑ j, procaConstraintBracket massSq B.2 (procaConstraintBasis i) *
        procaConstraintMatrixInverse massSq i j *
          procaConstraintBracket massSq (procaConstraintBasis j) C.2)

/-- Eliminating the complete second-class pair makes its affine constraint-sector
Dirac bracket vanish.  This is an explicit computation with the inverse matrix, not a
declared bracket law. -/
lemma procaAffineDiracBracket_eq_zero (massSq : ℂ) (B C : ProcaAffineObservable) :
    procaAffineDiracBracket massSq B C = 0 := by
  rcases B with ⟨b₀, b⟩
  rcases C with ⟨c₀, c⟩
  apply Prod.ext
  · change _ = (0 : ℂ)
    simp only [procaAffineDiracBracket, procaAffineConstant, procaConstraintBasis,
      procaConstraintBracket, procaConstraintMatrixInverse, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    norm_num
    field_simp
    ring
  · rfl

/-- Case (i) lifted from constraint values to a complex-linear projector on affine
observables. -/
def procaGaugeUnfixCaseIObservableProjection :
    ProcaAffineObservable →ₗ[ℂ] ProcaAffineObservable where
  toFun B := (B.1, procaGaugeUnfixCaseIProjection B.2)
  map_add' B C := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [procaGaugeUnfixCaseIProjection]
  map_smul' z B := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [procaGaugeUnfixCaseIProjection]

/-- Case (ii) lifted from constraint values to a complex-linear projector on affine
observables. -/
def procaGaugeUnfixCaseIIObservableProjection :
    ProcaAffineObservable →ₗ[ℂ] ProcaAffineObservable where
  toFun B := (B.1, procaGaugeUnfixCaseIIProjection B.2)
  map_add' B C := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [procaGaugeUnfixCaseIIProjection]
  map_smul' z B := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [procaGaugeUnfixCaseIIProjection]

/-- The Hamiltonian derivation `χ̂B = {χ,B}` on affine Proca observables. -/
def procaAffineHamiltonianDerivation (massSq : ℂ) (chi : ProcaConstraintPair)
    (B : ProcaAffineObservable) : ProcaAffineObservable :=
  procaAffineConstant (procaConstraintBracket massSq chi B.2)

/-- On affine observables, the case-(i) ordered exponential of paper Eq. (3.2)
terminates after its first correction and is exactly the constructed projector. -/
lemma procaGaugeUnfixCaseIObservableProjection_orderedExponential
    {massSq : ℂ} (hm : massSq ≠ 0) (B : ProcaAffineObservable) :
    procaGaugeUnfixCaseIObservableProjection B =
      B - (procaAffineHamiltonianDerivation massSq (procaCaseIChi massSq) B).1 •
        procaAffineConstraint procaCaseIPsi := by
  rcases B with ⟨b₀, b⟩
  apply Prod.ext
  · simp [procaGaugeUnfixCaseIObservableProjection, procaAffineHamiltonianDerivation,
      procaAffineConstant, procaAffineConstraint]
  · funext i
    fin_cases i <;>
      simp [procaGaugeUnfixCaseIObservableProjection, procaAffineHamiltonianDerivation,
        procaAffineConstant, procaAffineConstraint, procaConstraintBracket, procaCaseIChi,
        procaCaseIPsi, procaPrimaryConstraint, procaGaussConstraint,
        procaGaugeUnfixCaseIProjection, Matrix.vecHead, Matrix.vecTail, hm]

/-- On affine observables, the case-(ii) ordered exponential likewise terminates after
one Hamiltonian-derivation correction. -/
lemma procaGaugeUnfixCaseIIObservableProjection_orderedExponential
    {massSq : ℂ} (hm : massSq ≠ 0) (B : ProcaAffineObservable) :
    procaGaugeUnfixCaseIIObservableProjection B =
      B - (procaAffineHamiltonianDerivation massSq (procaCaseIIChi massSq) B).1 •
        procaAffineConstraint procaCaseIIPsi := by
  rcases B with ⟨b₀, b⟩
  apply Prod.ext
  · simp [procaGaugeUnfixCaseIIObservableProjection, procaAffineHamiltonianDerivation,
      procaAffineConstant, procaAffineConstraint]
  · funext i
    fin_cases i <;>
      simp [procaGaugeUnfixCaseIIObservableProjection, procaAffineHamiltonianDerivation,
        procaAffineConstant, procaAffineConstraint, procaConstraintBracket, procaCaseIIChi,
        procaCaseIIPsi, procaPrimaryConstraint, procaGaussConstraint,
        procaGaugeUnfixCaseIIProjection, Matrix.vecHead, Matrix.vecTail, hm]

/-- The Poisson bracket of two case-(i) projected affine observables vanishes because
both retain only the `Q₁` direction. -/
lemma procaAffinePoissonBracket_caseIProjection_eq_zero (massSq : ℂ)
    (B C : ProcaAffineObservable) :
    procaAffinePoissonBracket massSq
        (procaGaugeUnfixCaseIObservableProjection B)
        (procaGaugeUnfixCaseIObservableProjection C) = 0 := by
  rcases B with ⟨b₀, b⟩
  rcases C with ⟨c₀, c⟩
  apply Prod.ext
  · simp [procaAffinePoissonBracket, procaAffineConstant,
      procaGaugeUnfixCaseIObservableProjection, procaConstraintBracket,
      procaGaugeUnfixCaseIProjection]
  · rfl

/-- The corresponding case-(ii) projected Poisson bracket vanishes because only the
`Q₂` direction remains. -/
lemma procaAffinePoissonBracket_caseIIProjection_eq_zero (massSq : ℂ)
    (B C : ProcaAffineObservable) :
    procaAffinePoissonBracket massSq
        (procaGaugeUnfixCaseIIObservableProjection B)
        (procaGaugeUnfixCaseIIObservableProjection C) = 0 := by
  rcases B with ⟨b₀, b⟩
  rcases C with ⟨c₀, c⟩
  apply Prod.ext
  · simp [procaAffinePoissonBracket, procaAffineConstant,
      procaGaugeUnfixCaseIIObservableProjection, procaConstraintBracket,
      procaGaugeUnfixCaseIIProjection]
  · rfl

/-- **Vytheeswaran Appendix A.6, case (i).**  The Poisson bracket after gauge
unfixing equals the projection of the original second-class Dirac bracket. -/
lemma proca_caseI_projectedPoisson_eq_projectedDirac (massSq : ℂ)
    (B C : ProcaAffineObservable) :
    procaAffinePoissonBracket massSq
        (procaGaugeUnfixCaseIObservableProjection B)
        (procaGaugeUnfixCaseIObservableProjection C) =
      procaGaugeUnfixCaseIObservableProjection
        (procaAffineDiracBracket massSq B C) := by
  rw [procaAffinePoissonBracket_caseIProjection_eq_zero,
    procaAffineDiracBracket_eq_zero, map_zero]

/-- **Vytheeswaran Appendix A.6, case (ii).**  The second gauge-unfixing choice has
the same projected-Poisson/projected-Dirac equivalence. -/
lemma proca_caseII_projectedPoisson_eq_projectedDirac (massSq : ℂ)
    (B C : ProcaAffineObservable) :
    procaAffinePoissonBracket massSq
        (procaGaugeUnfixCaseIIObservableProjection B)
        (procaGaugeUnfixCaseIIObservableProjection C) =
      procaGaugeUnfixCaseIIObservableProjection
        (procaAffineDiracBracket massSq B C) := by
  rw [procaAffinePoissonBracket_caseIIProjection_eq_zero,
    procaAffineDiracBracket_eq_zero, map_zero]

/-- A finite family of generators closes under a bracket with specified structure
constants.  Taking the index family and constants to be those of the Poincaré algebra
gives the algebraic closure statement used in paper Eqs. (3.7) and (3.13). -/
def HasFiniteBracketClosure {I O : Type*} [Fintype I] [AddCommMonoid O] [Module ℂ O]
    (bracket : O → O → O) (generators : I → O)
    (structureConstant : I → I → I → ℂ) : Prop :=
  ∀ a b, bracket (generators a) (generators b) =
    ∑ k, structureConstant a b k • generators k

/-- A linear projection transports a finite bracket algebra whenever the projected
new bracket agrees with the projection of the old bracket.  This is the abstract
Appendix-A.6 mechanism used for the paper's projected Poincaré generators. -/
lemma finiteBracketClosure_map_of_projectedBracket
    {I O : Type*} [Fintype I] [AddCommMonoid O] [Module ℂ O]
    (projection : O →ₗ[ℂ] O) (oldBracket newBracket : O → O → O)
    (generators : I → O) (structureConstant : I → I → I → ℂ)
    (hprojected : ∀ B C,
      newBracket (projection B) (projection C) = projection (oldBracket B C))
    (hclosure : HasFiniteBracketClosure oldBracket generators structureConstant) :
    HasFiniteBracketClosure newBracket (fun a => projection (generators a))
      structureConstant := by
  intro a b
  rw [hprojected, hclosure]
  simp only [map_sum, map_smul]

/-- Any finite symmetry algebra carried by the original Dirac bracket remains closed
after the case-(i) gauge-unfixing projection. -/
lemma proca_caseI_projection_preserves_finiteBracketClosure
    {I : Type*} [Fintype I] (massSq : ℂ)
    (generators : I → ProcaAffineObservable)
    (structureConstant : I → I → I → ℂ)
    (hclosure : HasFiniteBracketClosure (procaAffineDiracBracket massSq)
      generators structureConstant) :
    HasFiniteBracketClosure (procaAffinePoissonBracket massSq)
      (fun a => procaGaugeUnfixCaseIObservableProjection (generators a))
      structureConstant := by
  exact finiteBracketClosure_map_of_projectedBracket
    procaGaugeUnfixCaseIObservableProjection (procaAffineDiracBracket massSq)
      (procaAffinePoissonBracket massSq) generators structureConstant
      (proca_caseI_projectedPoisson_eq_projectedDirac massSq) hclosure

/-- Any finite symmetry algebra carried by the original Dirac bracket remains closed
after the case-(ii) gauge-unfixing projection. -/
lemma proca_caseII_projection_preserves_finiteBracketClosure
    {I : Type*} [Fintype I] (massSq : ℂ)
    (generators : I → ProcaAffineObservable)
    (structureConstant : I → I → I → ℂ)
    (hclosure : HasFiniteBracketClosure (procaAffineDiracBracket massSq)
      generators structureConstant) :
    HasFiniteBracketClosure (procaAffinePoissonBracket massSq)
      (fun a => procaGaugeUnfixCaseIIObservableProjection (generators a))
      structureConstant := by
  exact finiteBracketClosure_map_of_projectedBracket
    procaGaugeUnfixCaseIIObservableProjection (procaAffineDiracBracket massSq)
      (procaAffinePoissonBracket massSq) generators structureConstant
      (proca_caseII_projectedPoisson_eq_projectedDirac massSq) hclosure

/-! ## G.2. Stückelberg realization on the finite massive-QED carrier -/

/-- The case-(ii) Stückelberg gauge action `A ↦ A + λ d`, `θ ↦ θ - λ` on the
existing finite massive-QED carrier.  Fermion components are spectators for this
bosonic Proca embedding. -/
def vytheeswaranStueckelbergTransform {d : ℕ}
    (gradient : Fin d → ℂ) (lambda : ℂ) (F : MassiveQEDFiniteField d) :
    MassiveQEDFiniteField d where
  gauge μ := F.gauge μ + lambda * gradient μ
  auxiliary := F.auxiliary - lambda
  fermion := F.fermion
  antifermion := F.antifermion

/-- Zero gauge parameter acts identically. -/
@[simp] lemma vytheeswaranStueckelbergTransform_zero {d : ℕ}
    (gradient : Fin d → ℂ) (F : MassiveQEDFiniteField d) :
    vytheeswaranStueckelbergTransform gradient 0 F = F := by
  ext mu <;> simp [vytheeswaranStueckelbergTransform]

/-- Stückelberg transformations compose by addition of gauge parameters. -/
lemma vytheeswaranStueckelbergTransform_add {d : ℕ}
    (gradient : Fin d → ℂ) (lambda sigma : ℂ) (F : MassiveQEDFiniteField d) :
    vytheeswaranStueckelbergTransform gradient lambda
        (vytheeswaranStueckelbergTransform gradient sigma F) =
      vytheeswaranStueckelbergTransform gradient (lambda + sigma) F := by
  ext mu <;> simp only [vytheeswaranStueckelbergTransform] <;> ring

/-- Every finite Stückelberg transformation is globally invertible, with inverse
parameter `-λ`. -/
def vytheeswaranStueckelbergEquiv {d : ℕ}
    (gradient : Fin d → ℂ) (lambda : ℂ) :
    Equiv (MassiveQEDFiniteField d) (MassiveQEDFiniteField d) where
  toFun := vytheeswaranStueckelbergTransform gradient lambda
  invFun := vytheeswaranStueckelbergTransform gradient (-lambda)
  left_inv F := by
    rw [vytheeswaranStueckelbergTransform_add]
    simp
  right_inv F := by
    rw [vytheeswaranStueckelbergTransform_add]
    simp

/-- The paper's gauge-invariant combination `Aμ + ∂μθ` (Eq. (3.17)), with
`gradient` carrying the selected regularized derivative mode. -/
def stueckelbergInvariantVector {d : ℕ}
    (gradient : Fin d → ℂ) (F : MassiveQEDFiniteField d) (mu : Fin d) : ℂ :=
  F.gauge mu + F.auxiliary * gradient mu

/-- `A + dθ` is invariant under the full finite Stückelberg gauge action. -/
lemma stueckelbergInvariantVector_gauge_invariant {d : ℕ}
    (gradient : Fin d → ℂ) (lambda : ℂ) (F : MassiveQEDFiniteField d) :
    stueckelbergInvariantVector gradient
        (vytheeswaranStueckelbergTransform gradient lambda F) =
      stueckelbergInvariantVector gradient F := by
  funext mu
  simp only [stueckelbergInvariantVector, vytheeswaranStueckelbergTransform]
  ring

/-- The finite Proca quadratic mass polynomial.  A Lorentz-signature contraction can
be supplied by replacing this sum with the repository's metric carrier; none of the
gauge-invariance argument depends on that choice. -/
noncomputable def procaQuadraticMassTerm {d : ℕ} (massSq : ℂ)
    (F : MassiveQEDFiniteField d) : ℂ :=
  massSq / 2 * ∑ mu, F.gauge mu ^ 2

/-- The Stückelberg completion of the Proca mass polynomial, obtained by replacing
`A` with the invariant vector `A + dθ`. -/
noncomputable def stueckelbergQuadraticMassTerm {d : ℕ} (gradient : Fin d → ℂ)
    (massSq : ℂ) (F : MassiveQEDFiniteField d) : ℂ :=
  massSq / 2 * ∑ mu, stueckelbergInvariantVector gradient F mu ^ 2

/-- The Stückelberg mass term is gauge invariant (paper Eq. (3.17)). -/
lemma stueckelbergQuadraticMassTerm_gauge_invariant {d : ℕ}
    (gradient : Fin d → ℂ) (massSq lambda : ℂ) (F : MassiveQEDFiniteField d) :
    stueckelbergQuadraticMassTerm gradient massSq
        (vytheeswaranStueckelbergTransform gradient lambda F) =
      stueckelbergQuadraticMassTerm gradient massSq F := by
  simp only [stueckelbergQuadraticMassTerm,
    stueckelbergInvariantVector_gauge_invariant]

/-- The unitary-gauge representative uses `λ = θ`, hence has scalar component zero. -/
def stueckelbergUnitaryGauge {d : ℕ} (gradient : Fin d → ℂ)
    (F : MassiveQEDFiniteField d) : MassiveQEDFiniteField d :=
  vytheeswaranStueckelbergTransform gradient F.auxiliary F

/-- The unitary-gauge Stückelberg scalar vanishes exactly. -/
@[simp] lemma stueckelbergUnitaryGauge_auxiliary {d : ℕ}
    (gradient : Fin d → ℂ) (F : MassiveQEDFiniteField d) :
    (stueckelbergUnitaryGauge gradient F).auxiliary = 0 := by
  simp [stueckelbergUnitaryGauge, vytheeswaranStueckelbergTransform]

/-- **Vytheeswaran Eq. (3.17), unitary-gauge theorem.**  The gauge-invariant
Stückelberg mass term is exactly the Proca mass term of its unitary-gauge
representative. -/
lemma stueckelberg_unitaryGauge_recovers_proca {d : ℕ}
    (gradient : Fin d → ℂ) (massSq : ℂ) (F : MassiveQEDFiniteField d) :
    stueckelbergQuadraticMassTerm gradient massSq F =
      procaQuadraticMassTerm massSq (stueckelbergUnitaryGauge gradient F) := by
  simp only [stueckelbergQuadraticMassTerm, procaQuadraticMassTerm,
    stueckelbergUnitaryGauge, vytheeswaranStueckelbergTransform,
    stueckelbergInvariantVector]

/-! ## H. Cutoff-limit QED Green-function consequences -/

namespace ContinuumQED

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral

variable {Field : Type*} [MeasurableSpace Field]

/-- The exact cutoff Ward identity survives the constructed cutoff limit and hence makes
the source partition invariant under the representative gauge transformation. -/
theorem sourcePartition_gauge_invariant
    (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (J : Field → ℂ) (hJ : S.admissible (sourceObservable J)) :
    sourcePartition S I (fun x => J (S.gaugeTransform x)) (S.admissible_gauge hJ) =
      sourcePartition S I J hJ := by
  exact gauge_invariant S I (sourceObservable J) hJ

/-- The connected generating functional `W[J] = log Z[J]` inherits the continuum
Ward/equivalence identity.  Thus every Green function obtained from admissible source
derivatives has the same generating object on the two gauge representatives. -/
theorem connectedGeneratingFunctional_gauge_invariant
    (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (J : Field → ℂ) (hJ : S.admissible (sourceObservable J)) :
    connectedGeneratingFunctional S I (fun x => J (S.gaugeTransform x))
        (S.admissible_gauge hJ) =
      connectedGeneratingFunctional S I J hJ := by
  unfold connectedGeneratingFunctional
  rw [sourcePartition_gauge_invariant S I J hJ]

/-- **Ferrari Eq. (8.15), finite-parameter source form.**  A whole source family whose
members are related by the cutoff system's Ward/gauge representative has a parameter-
independent continuum partition functional.  The constructive-QFT convergence obligations
remain those already exposed by `QEDContinuumCutoffSystem`. -/
theorem sourcePartition_parameterIndependent
    {P : Type*} (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (J : P → Field → ℂ)
    (hJ : ∀ rho, S.admissible (sourceObservable (J rho)))
    (hgauge : ∀ rho sigma x, J rho x = J sigma (S.gaugeTransform x)) :
    ∀ rho sigma,
      sourcePartition S I (J rho) (hJ rho) =
        sourcePartition S I (J sigma) (hJ sigma) := by
  intro rho sigma
  have hfun : J rho = fun x => J sigma (S.gaugeTransform x) := by
    funext x
    exact hgauge rho sigma x
  simpa only [hfun] using sourcePartition_gauge_invariant S I (J sigma) (hJ sigma)

/-- The connected continuum generating functional `W[J] = log Z[J]` is independent
of the field-redefinition parameter for a Ward-related admissible source family. -/
theorem connectedGeneratingFunctional_parameterIndependent
    {P : Type*} (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (J : P → Field → ℂ)
    (hJ : ∀ rho, S.admissible (sourceObservable (J rho)))
    (hgauge : ∀ rho sigma x, J rho x = J sigma (S.gaugeTransform x)) :
    ∀ rho sigma,
      connectedGeneratingFunctional S I (J rho) (hJ rho) =
        connectedGeneratingFunctional S I (J sigma) (hJ sigma) := by
  intro rho sigma
  unfold connectedGeneratingFunctional
  rw [sourcePartition_parameterIndependent S I J hJ hgauge rho sigma]

/-- The continuum Ward identity survives vacuum normalization: normalized Green
expectations agree on gauge-related observables.  No nonzero-partition hypothesis is
needed because the same vacuum denominator occurs on both sides. -/
theorem normalizedExpectation_gauge_invariant
    (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (O : Field → ℂ) (hO : S.admissible O) :
    normalizedExpectation S I (fun x => O (S.gaugeTransform x)) (S.admissible_gauge hO) =
      normalizedExpectation S I O hO := by
  unfold normalizedExpectation
  rw [gauge_invariant S I O hO]

/-- **Ferrari Section 7, normalized finite-parameter form.**  Every admissible
observable family related by the Ward field transformation has the same normalized
continuum expectation. -/
theorem normalizedExpectation_parameterIndependent
    {P : Type*} (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (O : P → Field → ℂ)
    (hO : ∀ rho, S.admissible (O rho))
    (hgauge : ∀ rho sigma x, O rho x = O sigma (S.gaugeTransform x)) :
    ∀ rho sigma,
      normalizedExpectation S I (O rho) (hO rho) =
        normalizedExpectation S I (O sigma) (hO sigma) := by
  intro rho sigma
  have hfun : O rho = fun x => O sigma (S.gaugeTransform x) := by
    funext x
    exact hgauge rho sigma x
  simpa only [hfun] using normalizedExpectation_gauge_invariant S I (O sigma) (hO sigma)

/-- **Infinitesimal ET identity for `Z`.**  Finite parameter independence implies
that the real field-redefinition derivative of the source partition is exactly zero. -/
theorem sourcePartition_hasDerivAt_parameter_zero
    (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (J : ℝ → Field → ℂ)
    (hJ : ∀ rho, S.admissible (sourceObservable (J rho)))
    (hgauge : ∀ rho sigma x, J rho x = J sigma (S.gaugeTransform x))
    (rho : ℝ) :
    HasDerivAt (fun sigma => sourcePartition S I (J sigma) (hJ sigma)) 0 rho := by
  have hfun : (fun sigma => sourcePartition S I (J sigma) (hJ sigma)) =
      fun _ => sourcePartition S I (J rho) (hJ rho) := by
    funext sigma
    exact sourcePartition_parameterIndependent S I J hJ hgauge sigma rho
  rw [hfun]
  exact hasDerivAt_const rho _

/-- **Infinitesimal ET identity for `W`.**  The connected generating functional has
zero derivative with respect to the real field-redefinition parameter. -/
theorem connectedGeneratingFunctional_hasDerivAt_parameter_zero
    (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (J : ℝ → Field → ℂ)
    (hJ : ∀ rho, S.admissible (sourceObservable (J rho)))
    (hgauge : ∀ rho sigma x, J rho x = J sigma (S.gaugeTransform x))
    (rho : ℝ) :
    HasDerivAt
      (fun sigma => connectedGeneratingFunctional S I (J sigma) (hJ sigma)) 0 rho := by
  have hfun : (fun sigma => connectedGeneratingFunctional S I (J sigma) (hJ sigma)) =
      fun _ => connectedGeneratingFunctional S I (J rho) (hJ rho) := by
    funext sigma
    exact connectedGeneratingFunctional_parameterIndependent S I J hJ hgauge sigma rho
  rw [hfun]
  exact hasDerivAt_const rho _

/-- **Selected connected one-point Green function.**  If two parameterizations have
source-direction derivatives of their common connected functional, uniqueness of the
derivative makes those Green values equal.  This is the first actual source-derivative
consequence of the Section 7 generating-functional identity. -/
theorem connectedGeneratingFunctional_sourceDerivative_parameterIndependent
    {P : Type*} (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (J : P → ℂ → Field → ℂ)
    (hJ : ∀ rho source, S.admissible (sourceObservable (J rho source)))
    (hgauge : ∀ rho sigma source x,
      J rho source x = J sigma source (S.gaugeTransform x))
    {rho sigma : P} {source dRho dSigma : ℂ}
    (hRho : HasDerivAt
      (fun s => connectedGeneratingFunctional S I (J rho s) (hJ rho s)) dRho source)
    (hSigma : HasDerivAt
      (fun s => connectedGeneratingFunctional S I (J sigma s) (hJ sigma s)) dSigma source) :
    dRho = dSigma := by
  have hfun :
      (fun s => connectedGeneratingFunctional S I (J rho s) (hJ rho s)) =
      (fun s => connectedGeneratingFunctional S I (J sigma s) (hJ sigma s)) := by
    funext s
    exact connectedGeneratingFunctional_parameterIndependent S I (fun p => J p s)
      (fun p => hJ p s) (fun p q x => hgauge p q s x) rho sigma
  rw [hfun] at hRho
  exact hRho.unique hSigma

/-- **On-shell ET/QED capstone.**  The same explicit hypotheses simultaneously restore
the coupled-doublet ST identity by a counterterm and make the admissible continuum QED
connected-source family parameter independent.  This composes the paper's Sections 6.1,
7 and 8 without hiding QCAP, FP-charge, Ward-family, or cutoff-convergence inputs. -/
theorem restoredST_and_connectedGeneratingFunctional_parameterIndependent
    {R V P : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C : RelativeBRSTContraction R V) (Gamma breaking : V)
    (hbreak : C.differential Gamma = breaking)
    (hWZ : C.differential breaking = 0)
    (hFP : C.independentPart breaking = 0)
    (S : QEDContinuumCutoffSystem Field)
    (I : Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral S)
    (J : P → Field → ℂ)
    (hJ : ∀ rho, S.admissible (sourceObservable (J rho)))
    (hgauge : ∀ rho sigma x, J rho x = J sigma (S.gaugeTransform x)) :
    (∃ counterterm,
      C.differential counterterm = breaking ∧
      C.differential (Gamma - counterterm) = 0) ∧
    ∀ rho sigma,
      connectedGeneratingFunctional S I (J rho) (hJ rho) =
        connectedGeneratingFunctional S I (J sigma) (hJ sigma) := by
  exact ⟨ferrari_coupledDoublet_ST_breaking_restorable C Gamma breaking
      hbreak hWZ hFP,
    connectedGeneratingFunctional_parameterIndependent S I J hJ hgauge⟩

end ContinuumQED

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.brstDoublet_closed_is_exact where
  formalizes @ "claim:an-isolated-decoupled-brst-doublet-has-trivial-cohomology-via-an-explicit-contracting-homotopy",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-appendix-b",
  caveat @ "epistemic:proves-the-isolated-decoupled-doublet-core-not-the-filtered-local-functional-theorem-for-coupled-doublets"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.RelativeBRSTContraction.coupledDoublet_relative_exact where
  formalizes @ "claim:a-closed-functional-differs-from-its-closed-doublet-independent-component-by-a-brst-exact-term",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-appendix-b-lemma-b2",
  caveat @ "epistemic:the-relative-deformation-retract-is-explicit-input-encoding-the-filtered-local-cohomology-analysis-not-derived-from-qcap-locality-alone"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_coupledDoublet_ST_breaking_restorable where
  formalizes @ "ferrari-et-section-6.1:a-wess-zumino-closed-on-shell-breaking-with-vanishing-fp-charge-independent-component-is-exact-and-removable",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equations-6.25-6.31-and-b8",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.RelativeBRSTContraction.coupledDoublet_relative_exact",
  caveat @ "epistemic:proves-restoration-from-qcap-wess-zumino-relative-contraction-and-fp-charge-inputs-not-an-unconditional-qcap-or-interacting-qed4-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_coupledDoublet_loopwise_ST_restoration where
  formalizes @ "claim:coupled-doublet-slavnov-taylor-restoration-at-every-supplied-perturbative-order",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_coupledDoublet_ST_breaking_restorable",
  caveat @ "epistemic:order-indexed-restoration-not-convergence-or-construction-of-the-loop-expansion"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_ST_breaking_exact_and_restorable where
  formalizes @ "claim:a-wess-zumino-closed-slavnov-taylor-breaking-in-a-contractible-brst-carrier-is-exact-and-is-removed-by-subtracting-its-primitive-counterterm",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equations-5.1-5.6",
  caveat @ "epistemic:conditional-on-the-qcap-locality-and-contracting-homotopy-inputs-not-a-proof-of-the-quasi-classical-action-principle"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_loopwise_ST_restoration where
  formalizes @ "claim:the-exact-counterterm-restoration-applies-at-every-supplied-perturbative-order",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_ST_breaking_exact_and_restorable",
  caveat @ "epistemic:pointwise-order-by-order-restoration-given-qcap-wess-zumino-data-not-convergence-or-construction-of-the-perturbation-series"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_physicalGreen_parameterIndependent where
  formalizes @ "claim:a-physical-green-functional-that-annihilates-brst-exact-terms-is-independent-of-a-brst-exact-field-redefinition-parameter-variation",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-section-7",
  caveat @ "epistemic:algebraic-selected-observable-result-not-a-claim-that-every-off-shell-green-function-or-an-anomalous-gauge-theory-is-parameter-independent"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_selectedGreen_family_parameterIndependent where
  formalizes @ "claim:finite-parameter-independence-of-the-entire-selected-green-observable-family-when-pairwise-variations-are-brst-exact",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_physicalGreen_eq_of_exact_difference",
  caveat @ "epistemic:selected-green-functional-family-only-the-et-st-identity-does-not-by-itself-prove-unitarity-or-identify-all-members-with-physical-observables"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.complexAction_strongEquivalence_changeOfVariables where
  formalizes @ "claim:the-nagao-nielsen-generating-integral-is-invariant-under-an-exact-measurable-field-equivalence-with-the-jacobian-encoded-in-the-transformed-measure",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equation-1.3",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight",
  caveat @ "epistemic:exact-bochner-integral-change-of-variables-not-a-construction-of-the-interacting-qed4-measure-renormalized-s-matrix-or-qcap"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.strongEquivalence_nPointGreen where
  formalizes @ "claim:every-finite-product-of-green-function-insertions-is-invariant-under-the-exact-measure-preserving-field-reparameterization",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equations-1.3-and-3.1-3.6",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.strongEquivalence_changeOfVariables",
  caveat @ "epistemic:unnormalized-bochner-correlator-identity-for-a-supplied-measure-equivalence-not-an-interacting-continuum-measure-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.strongEquivalence_family_parameterIndependent where
  formalizes @ "claim:all-correctly-pushforwarded-representatives-of-a-field-redefinition-family-have-the-same-observable-integral",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.strongEquivalence_changeOfVariables",
  caveat @ "epistemic:requires-each-parameterized-field-map-and-its-jacobian-carrying-pushforward-measure-as-data"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_gauge_invariant where
  formalizes @ "claim:the-cutoff-ward-identity-survives-the-supplied-renormalized-continuum-limit-and-makes-the-connected-source-generating-functional-gauge-invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral.gauge_invariant",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-section-7",
  caveat @ "epistemic:conditional-on-the-cutoff-system-continuum-convergence-obligations-and-admissibility-not-an-unconditional-construction-of-interacting-qed4"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.qed_FP_and_complexAction_equivalence where
  formalizes @ "claim:the-existing-abelian-faddeev-popov-determinant-is-field-independent-and-the-complex-action-integral-is-invariant-under-the-supplied-field-equivalence",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction.abelian_FP_decouples",
  caveat @ "epistemic:regularized-abelian-and-measure-theoretic-capstone-not-the-paper-full-massive-qed-proca-gauge-renormalizability-or-unitarity-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_gaugeSlice_FP_complexAction_chain where
  formalizes @ "claim:the-gauge-invariant-integral-factors-through-the-existing-gauge-slice-the-abelian-faddeev-popov-determinant-decouples-and-the-complex-action-integral-is-invariant-under-the-supplied-field-equivalence",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRegularization.gauge_integral_factorizes",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction.abelian_FP_decouples",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.complexAction_strongEquivalence_changeOfVariables",
  caveat @ "epistemic:composes-exact-regularized-measure-identities-under-explicit-measure-preserving-and-gauge-invariance-hypotheses-not-a-construction-of-the-continuum-qed-measure-or-qcap"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariBVCompletedAction_eq_finiteTower where
  formalizes @ "ferrari-et-equations-6.17-6.23:the-polynomial-bv-antifield-completion-is-the-finite-hasse-derivative-taylor-tower",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equations-6.17-6.23",
  supported_by @ "lean:Polynomial.taylor_coeff",
  caveat @ "epistemic:exact-one-component-polynomial-action-sector-not-the-continuum-functional-antibracket-quantum-master-measure-or-qcap"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariBVCompletedAction_eq_boundedTower where
  formalizes @ "ferrari-et-equation-6.23:a-degree-at-most-M-action-has-an-exact-antifield-completion-truncated-at-order-M",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariBVCompletedAction_eq_finiteTower",
  caveat @ "epistemic:polynomial-degree-termination-result-not-a-convergence-theorem-for-a-nonpolynomial-functional-action"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariBVCompletedAction_diagonalShift_invariant where
  formalizes @ "claim:the-resummed-shifted-action-is-invariant-under-simultaneous-field-antifield-translation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariBVCompletedAction_eq_shifted",
  caveat @ "epistemic:finite-translation-cancellation-identity-not-relabeled-as-the-full-continuum-bv-quantum-master-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.massiveQEDFieldRedefinition_add where
  formalizes @ "claim:the-parameterized-massive-qed-proca-lorentz-field-redefinitions-compose-additively-and-have-negative-parameter-inverses",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equations-8.4-8.10",
  caveat @ "epistemic:exact-finite-complex-mode-field-equivalence-not-a-sobolev-space-local-diffeomorphism-or-renormalized-interacting-qed4-equivalence"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.massiveQEDFieldRedefinition_unitJacobian where
  formalizes @ "claim:the-finite-proca-lorentz-field-redefinition-has-unit-bosonic-triangular-determinant-and-cancelling-fermion-antifermion-phases",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equations-8.4-8.10",
  supported_by @ "lean:Matrix.det_fromBlocks_zero₂₁",
  caveat @ "epistemic:exact-finite-regularized-jacobian-not-an-infinite-dimensional-functional-berezinian-determinant-regularization-or-anomaly-cancellation-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaConstraintMatrix_mul_inverse where
  formalizes @ "claim:vytheeswaran-1998-equations-2.4-2.6-the-abelian-proca-primary-and-gauss-constraints-have-an-explicit-invertible-second-class-bracket-matrix-at-nonzero-mass",
  supported_by @ "paper:vytheeswaran-1998-ijmpa13-765-equations-2.4-2.6",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaConstraintMatrix_det",
  caveat @ "epistemic:exact-two-constraint-coefficient-matrix-after-factoring-out-the-spatial-delta-distribution-not-a-construction-of-the-continuum-distributional-poisson-or-dirac-bracket"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseI_canonical where
  formalizes @ "claim:vytheeswaran-1998-equations-3.1-and-3.8-both-choices-of-retained-first-class-proca-constraint-admit-the-paper-canonical-normalization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_primary_gauss_bracket",
  caveat @ "epistemic:exact-normalization-for-nonzero-mass-not-a-proof-that-an-arbitrary-nonabelian-second-class-system-can-be-gauge-unfixed"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaGaugeUnfixCaseIProjection_idempotent where
  formalizes @ "claim:vytheeswaran-1998-appendix-a.1-a.4-the-two-proca-gauge-unfixing-choices-are-idempotent-original-carrier-projections-retaining-one-constraint-and-annihilating-the-discarded-gauge-fixing-value",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaGaugeUnfixCaseIIProjection_idempotent",
  caveat @ "epistemic:constructed-on-the-two-dimensional-constraint-value-carrier-not-the-ordered-exponential-projection-on-the-entire-continuum-poisson-algebra-or-its-poincare-generators"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaGaugeUnfixCaseIObservableProjection_orderedExponential where
  formalizes @ "claim:vytheeswaran-1998-equations-3.2-3.3-the-normal-ordered-gauge-unfixing-exponential-terminates-exactly-on-affine-proca-observables-for-both-canonical-constraint-choices",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaGaugeUnfixCaseIIObservableProjection_orderedExponential",
  caveat @ "epistemic:exact-affine-observable-truncation-not-convergence-or-domain-control-for-the-infinite-ordered-exponential-on-the-continuum-functional-poisson-algebra"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseI_projectedPoisson_eq_projectedDirac where
  formalizes @ "claim:vytheeswaran-1998-appendix-a.6-the-poisson-bracket-of-gauge-unfixed-affine-observables-equals-the-projection-of-the-explicit-two-constraint-dirac-bracket",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaAffineDiracBracket_eq_zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseII_projectedPoisson_eq_projectedDirac",
  caveat @ "epistemic:proved-on-the-affine-two-constraint-sector-with-the-paper-matrix-inverse-not-yet-the-distribution-valued-bracket-of-arbitrary-spacetime-functionals"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseI_projection_preserves_finiteBracketClosure where
  formalizes @ "claim:vytheeswaran-1998-equations-3.7-and-3.13-projection-transports-any-supplied-finite-dirac-bracket-symmetry-algebra-with-its-structure-constants-to-the-gauge-unfixed-poisson-bracket",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.finiteBracketClosure_map_of_projectedBracket",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseII_projection_preserves_finiteBracketClosure",
  caveat @ "epistemic:the-closure-transport-is-proved-but-the-continuum-integrated-proca-energy-momentum-and-angular-momentum-generators-and-their-boundary-terms-remain-explicit-input-data"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.stueckelberg_unitaryGauge_recovers_proca where
  formalizes @ "claim:vytheeswaran-1998-equation-3.17-case-ii-is-an-invertible-stueckelberg-gauge-action-the-vector-a-plus-d-theta-and-its-mass-term-are-invariant-and-unitary-gauge-recovers-proca",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.vytheeswaranStueckelbergTransform_add",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.stueckelbergQuadraticMassTerm_gauge_invariant",
  caveat @ "epistemic:exact-finite-derivative-mode-and-quadratic-mass-polynomial-not-the-continuum-maxwell-kinetic-measure-the-antisymmetric-tensor-dual-or-the-interacting-renormalized-proca-qed-s-matrix"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariFunctionalDerivative_split where
  formalizes @ "ferrari-et-equations-6.6-6.9:the-full-frechet-derivative-on-the-antighost-antifield-product-splits-exactly-into-the-two-functional-partial-derivatives",
  supported_by @ "lean:fderiv_wrt_prod",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equations-6.6-6.9",
  caveat @ "epistemic:genuine-frechet-calculus-on-arbitrary-normed-carriers-while-the-distributional-derivative-contraction-kernel-remains-explicit-system-data"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.norm_ferrariStrongDualContraction_le where
  formalizes @ "ferrari-et-equation-6.7:for-a-normed-field-space-and-its-strong-dual-the-bv-functional-derivative-contraction-is-canonical-bidual-evaluation-and-is-jointly-continuous",
  supported_by @ "lean:ContinuousLinearMap.isBoundedBilinearMap_apply",
  supported_by @ "paper:ferrari-picariello-quadri-2002-jhep04-033-equation-6.7",
  caveat @ "epistemic:infinite-dimensional-banach-strong-dual-pairing-not-a-renormalized-coincident-point-kernel-on-a-nuclear-schwartz-distribution-space"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariStrongDualAntibracket_apply where
  formalizes @ "ferrari-et-equation-6.7:on-the-strong-dual-bv-carrier-the-antibracket-is-exactly-the-antifield-frechet-derivative-evaluated-on-the-antighost-frechet-derivative",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariStrongDualContraction_apply",
  caveat @ "epistemic:the-functional-pairing-is-constructed-but-differentiability-of-a-specific-renormalized-interacting-qed-effective-action-remains-a-separate-obligation"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.satisfiesFerrariStrongDualST_iff where
  formalizes @ "ferrari-et-equations-6.6-6.9:the-functional-slavnov-taylor-master-equation-on-the-strong-dual-carrier-is-the-explicit-pointwise-delta-gamma-plus-derivative-contraction-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariStrongDualAntibracket_apply",
  caveat @ "epistemic:exact-equivalence-for-a-supplied-linearized-st-differential-not-a-proof-that-the-renormalized-qed-effective-action-satisfies-the-master-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariStrongDualAntibracket_eq_zero_of_cbarDerivative_eq_zero where
  formalizes @ "claim:antighost-independence-forces-the-strong-dual-antibracket-to-vanish-at-the-configuration",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariStrongDualAntibracket_apply",
  caveat @ "epistemic:local-sufficient-condition-not-a-derivation-of-antighost-independence-for-the-interacting-effective-action"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.satisfiesFerrariStrongDualST_of_delta_eq_zero_of_cbarDerivative_eq_zero where
  formalizes @ "claim:a-linearized-st-closed-antighost-independent-functional-satisfies-the-full-strong-dual-master-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.satisfiesFerrariStrongDualST_iff",
  caveat @ "epistemic:conditional-reusable-master-equation-criterion-not-an-unconditional-qcap-or-renormalized-qed-effective-action-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.sourcePartition_parameterIndependent where
  formalizes @ "ferrari-et-equation-8.15:an-admissible-ward-related-source-family-has-a-parameter-independent-cutoff-limit-qed-partition-functional",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.sourcePartition_gauge_invariant",
  caveat @ "epistemic:conditional-on-the-explicit-pairwise-ward-source-relation-admissibility-and-cutoff-convergence-data-not-an-unconditional-construction-of-interacting-qed4"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_parameterIndependent where
  formalizes @ "claim:the-connected-continuum-qed-generating-functional-is-independent-of-the-field-redefinition-parameter-for-an-admissible-ward-related-source-family",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.sourcePartition_parameterIndependent",
  caveat @ "epistemic:exact-log-of-partition-consequence-under-the-supplied-ward-family-not-a-claim-about-arbitrary-off-shell-or-anomalous-source-families"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.normalizedExpectation_gauge_invariant where
  formalizes @ "claim:the-cutoff-limit-ward-identity-descends-from-unnormalized-amplitudes-to-normalized-continuum-green-expectations",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral.gauge_invariant",
  caveat @ "epistemic:normalized-selected-observable-identity-under-the-supplied-cutoff-ward-system-not-an-unconditional-qed4-vacuum-measure-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.normalizedExpectation_parameterIndependent where
  formalizes @ "claim:normalized-continuum-green-expectations-of-an-admissible-ward-related-family-are-independent-of-field-parameterization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.normalizedExpectation_gauge_invariant",
  caveat @ "epistemic:selected-admissible-observables-only-not-a-claim-that-all-off-shell-green-functions-are-physical-or-parameter-independent"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.sourcePartition_hasDerivAt_parameter_zero where
  formalizes @ "ferrari-et-equation-8.15:finite-parameter-independence-implies-the-infinitesimal-field-redefinition-derivative-of-z-is-zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.sourcePartition_parameterIndependent",
  caveat @ "epistemic:real-parameter-derivative-of-the-constructed-cutoff-limit-functional-under-the-explicit-ward-family-not-a-functional-source-derivative-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_hasDerivAt_parameter_zero where
  formalizes @ "claim:the-infinitesimal-field-redefinition-derivative-of-the-connected-generating-functional-w-is-zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_parameterIndependent",
  caveat @ "epistemic:derivative-consequence-of-an-exact-ward-family-not-a-proof-of-renormalized-qed4-differentiability-from-first-principles"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_sourceDerivative_parameterIndependent where
  formalizes @ "claim:when-the-source-direction-derivatives-exist-the-selected-connected-one-point-green-functional-is-independent-of-field-parameterization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_parameterIndependent",
  caveat @ "epistemic:one-complex-source-direction-with-differentiability-supplied-not-a-construction-of-all-distribution-valued-n-point-functional-derivatives"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.restoredST_and_connectedGeneratingFunctional_parameterIndependent where
  formalizes @ "ferrari-et-sections-6.1-7-8:coupled-doublet-counterterm-restoration-and-continuum-qed-connected-source-parameter-independence-hold-together",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_coupledDoublet_ST_breaking_restorable",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_parameterIndependent",
  caveat @ "epistemic:capstone-retains-qcap-wess-zumino-fp-charge-relative-contraction-ward-source-admissibility-and-cutoff-limit-hypotheses-explicitly"

zil_file_contract physlib.slavnovTaylorEquivalence where
  promises "A dependency-reusing Ferrari--Picariello--Quadri equivalence-theorem and Vytheeswaran Abelian-Proca gauge-unfixing layer: explicit decoupled and relative coupled-BRST contractions, conditional Wess--Zumino/counterterm restoration at every supplied loop order, genuine Frechet antighost/antifield functional derivatives with canonical continuous strong-dual BV contraction, an exactly terminating polynomial BV antifield tower, an invertible finite massive-QED Proca/Lorentz field map with unit Jacobian, the exact two-constraint Proca bracket matrix, both idempotent gauge-unfixing choices, their exact affine ordered-exponential realization, explicit projected-Poisson/projected-Dirac equivalence, conditional transport of finite symmetry structure constants, an invertible Stueckelberg action with invariant mass term and unitary-gauge Proca recovery, exact complex-action change of variables, and cutoff-limit QED Ward identities for source partitions, connected functionals, normalized expectations, infinitesimal parameter derivatives, and selected source-derived Green functions."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRegularization.gauge_integral_factorizes",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction.abelian_FP_decouples",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight",
    "lean:fderiv_wrt_prod",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral.QEDContinuumCutoffSystem.PathIntegral.ContinuumQEDFunctionalIntegral.gauge_invariant"]
  forbids_substitutes ["claiming a proof of the Quasi-Classical Action Principle",
    "claiming the coupled-doublet relative deformation retract follows automatically from qcap locality",
    "claiming construction or convergence of interacting QED4",
    "claiming the finite polynomial BV translation identity is the continuum quantum master equation",
    "claiming a distributional BV diagonal contraction without an explicit continuous contraction or renormalization datum",
    "claiming the finite unit Jacobian proves an infinite-dimensional anomaly-free functional measure",
    "claiming the affine ordered-exponential projector has established convergence or domain control on the full continuum functional Poisson algebra",
    "claiming Poincare closure without the projected Dirac-bracket hypotheses",
    "claiming the Stueckelberg mass polynomial constructs the continuum antisymmetric-tensor dual or interacting Proca QED",
    "claiming that a field-redefinition ST identity repairs an independent anomalous gauge BRST identity"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.brstDoublet_closed_is_exact,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.RelativeBRSTContraction.coupledDoublet_relative_exact,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_ST_breaking_exact_and_restorable,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_loopwise_ST_restoration,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_coupledDoublet_ST_breaking_restorable,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_coupledDoublet_loopwise_ST_restoration,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_physicalGreen_parameterIndependent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_selectedGreen_family_parameterIndependent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.strongEquivalence_nPointGreen,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.strongEquivalence_family_parameterIndependent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.complexAction_strongEquivalence_changeOfVariables,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.qed_FP_and_complexAction_equivalence,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrari_gaugeSlice_FP_complexAction_chain,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariBVCompletedAction_eq_finiteTower,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariBVCompletedAction_eq_boundedTower,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariBVCompletedAction_diagonalShift_invariant,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.massiveQEDFieldRedefinition_add,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.massiveQEDFieldRedefinition_unitJacobian,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaConstraintMatrix_mul_inverse,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseI_canonical,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseII_canonical,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaGaugeUnfixCaseIProjection_idempotent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaGaugeUnfixCaseIIProjection_idempotent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaGaugeUnfixCaseIObservableProjection_orderedExponential,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.procaGaugeUnfixCaseIIObservableProjection_orderedExponential,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseI_projectedPoisson_eq_projectedDirac,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseII_projectedPoisson_eq_projectedDirac,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.finiteBracketClosure_map_of_projectedBracket,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseI_projection_preserves_finiteBracketClosure,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.proca_caseII_projection_preserves_finiteBracketClosure,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.vytheeswaranStueckelbergTransform_add,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.stueckelbergInvariantVector_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.stueckelbergQuadraticMassTerm_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.stueckelberg_unitaryGauge_recovers_proca,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariFunctionalDerivative_split,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.norm_ferrariStrongDualContraction_le,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariStrongDualAntibracket_apply,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.satisfiesFerrariStrongDualST_iff,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ferrariStrongDualAntibracket_eq_zero_of_cbarDerivative_eq_zero,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.satisfiesFerrariStrongDualST_of_delta_eq_zero_of_cbarDerivative_eq_zero,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.sourcePartition_parameterIndependent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_parameterIndependent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.normalizedExpectation_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.normalizedExpectation_parameterIndependent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.sourcePartition_hasDerivAt_parameter_zero,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_hasDerivAt_parameter_zero,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.connectedGeneratingFunctional_sourceDerivative_parameterIndependent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.SlavnovTaylorEquivalence.ContinuumQED.restoredST_and_connectedGeneratingFunctional_parameterIndependent]

/- ZIL-END -/

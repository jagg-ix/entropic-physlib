/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge
public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeBetheSalpeterOscillator
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
public import Physlib.Mathematics.Distribution.SchwartzNuclear.HermiteTensorProduct
public import Physlib.Mathematics.Distribution.NuclearExtensionComplex
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
meta import Zil

/-!
# Four-dimensional Bethe--Salpeter equation and bound-state completeness

This module closes two gaps left explicit in the earlier Swift--Lee and
Wick--Cutkosky files.

* **The unreduced equation really is four-dimensional.**  The relative
  momentum is `Lorentz.Vector 3`, hence has one temporal and three spatial
  components.  `SatisfiesFourDimensionalDiracBSE` is the homogeneous
  fermion--antifermion equation with the symmetric routing
  `p₁ = P/2 + q`, `p₂ = P/2 - q`, two Dirac factors, and a Bochner integral
  over all four components of the internal momentum.
* **The analytical carrier is `L²(ℝ⁴)`.**  The separable ladder operator is
  the continuum rank-one Cutkosky operator already constructed in
  `BennettCatichaBassettoBridge`, now instantiated on the four-dimensional
  Lorentz-vector measure space.
* **The canonical oscillator basis is constructed explicitly.**  The
  repository's four-dimensional tensor Hermite expansion is included into
  complex `L²`, where Schwartz completeness and density construct a genuine
  Hilbert basis.  A volume-preserving linear isometry transports that basis
  from Euclidean coordinates to `Lorentz.Vector 3`, so the canonical
  diagonal resonance family no longer takes a basis certificate as input.
* **Completeness is a theorem, not a certificate field.**  The symmetric
  separable kernel is compact and self-adjoint.  Mathlib's compact
  self-adjoint spectral theorem therefore proves that the orthogonal
  complement of the supremum of all eigenspaces is bottom
  (`fourDimensional_boundState_complete`).  Thus its bound-state
  eigenspaces are complete in the precise Hilbert-space sense.  Every
  nonzero eigenspace is also finite dimensional.
* **Entropic dynamics supplies a concrete convergence mechanism.**  The
  Caticha transition weight is reused through
  `ed_is_nagaoNielsen_complexAction`: a positive imaginary-action gap gives
  the exact mode coupling `aₙ = exp (-n γ)`.  Uniformly bounded `L²` modes
  then make `∑ₙ |aₙ| ‖uₙ‖²` summable, constructing the compact Hermitian
  interacting kernel and its Fredholm solver without a convergence field.
* **The full complex phase is retained for resonances.**  Replacing the real
  coupling by `exp (i S_R - n γ)` gives a norm-convergent compact
  non-Hermitian kernel.  Its nonzero eigenspaces have finite multiplicity and
  the Fredholm equation is uniquely solvable off spectrum.  In the stronger
  diagonal sector where the four-dimensional Cutkosky modes are supplied as
  a Hilbert basis, the self-adjoint damping companion and the full resonance
  operator share that complete orthonormal eigenbasis.  Phase reversal is
  proved to construct the Hilbert adjoint, hence the full diagonal resonance
  operator is normal.  It is self-adjoint exactly when every mode coupling is
  real; at zero real action it reduces to the Hermitian ED damping operator.
  These conclusions are not inferred from non-Hermitian compactness alone.
* **The Lusanna tetrad is structural.**  The relative-momentum quadratic
  form is computed from `g = EᵀηE`; changing the local Lorentz tetrad
  `E ↦ ΛE` leaves it unchanged.  This is the frame-independent bridge from
  the four-momentum carrier to the repository's ADM tetrad geometry.

The symmetric rank-one kernel is the exactly proved separable ladder sector.
For an interacting Hermitian QED kernel the module now supplies two honest
routes: an arbitrary operator-norm limit of finite Hermitian Cutkosky modes,
and the directly checkable sufficient condition
`∑ₙ |aₙ| ‖uₙ‖² < ∞`, which constructs that limit automatically.  It does
**not** claim that every formal QED kernel satisfies either condition.  The
generic complex-action construction covers compact non-Hermitian resonances
only at the Fredholm and finite-multiplicity level.  The diagonal
specialization promotes its supplied orthonormal Cutkosky modes to a shared
complete eigenbasis, but does not assert such a basis for arbitrary compact
non-Hermitian kernels.  The full Dirac integral equation remains independent
of these spectral specializations.

## References

* E. E. Salpeter and H. A. Bethe, *A Relativistic Equation for Bound-State
  Problems*, Phys. Rev. 84 (1951) 1232.
* A. R. Swift and B. W. Lee, Phys. Rev. 131 (1963) 1857.
* R. E. Cutkosky, Phys. Rev. 96 (1954) 1135.
* L. Lusanna, canonical ADM tetrad gravity (rest-frame instant form).
* S. Ipek, M. Abedi and A. Caticha, arXiv:1803.07493; K. Nagao and
  H. B. Nielsen, complex-action formulation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Matrix
open GaussianField

namespace Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeBetheSalpeterOscillator
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsTransitionProbability
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-! ## A. The unreduced four-dimensional Dirac equation -/

/-- The relative four-momentum carrier: one energy coordinate and three
spatial momentum coordinates. -/
abbrev RelativeMomentum4 := Lorentz.Vector 3

/-- The relative-momentum carrier has exactly four real coordinates. -/
lemma relativeMomentum4_card : Fintype.card (Fin 1 ⊕ Fin 3) = 4 := by
  simp

/-- Convert Physlib's Lorentz-vector indexing to the conventional `Fin 4`
indexing used by the repository's Dirac slash. -/
def relativeMomentumFin (q : RelativeMomentum4) : Fin 4 → ℝ :=
  fun mu => q (finSumFinEquiv.symm mu)

/-- Symmetric Bethe--Salpeter momentum routing `p₁ = P/2 + q`. -/
def constituentMomentumPlus (P : Fin 4 → ℝ) (q : RelativeMomentum4) : Fin 4 → ℝ :=
  fun mu => P mu / 2 + relativeMomentumFin q mu

/-- Symmetric Bethe--Salpeter momentum routing `p₂ = P/2 - q`. -/
def constituentMomentumMinus (P : Fin 4 → ℝ) (q : RelativeMomentum4) : Fin 4 → ℝ :=
  fun mu => P mu / 2 - relativeMomentumFin q mu

/-- The two constituent momenta reconstruct the total momentum pointwise:
`p₁ + p₂ = P`. -/
lemma constituentMomentumPlus_add_minus (P : Fin 4 → ℝ) (q : RelativeMomentum4) :
    constituentMomentumPlus P q + constituentMomentumMinus P q = P := by
  funext mu
  simp [constituentMomentumPlus, constituentMomentumMinus]

/-- The two constituent momenta reconstruct twice the relative momentum:
`p₁ - p₂ = 2q`. -/
lemma constituentMomentumPlus_sub_minus (P : Fin 4 → ℝ) (q : RelativeMomentum4) :
    constituentMomentumPlus P q - constituentMomentumMinus P q =
      2 • relativeMomentumFin q := by
  funext mu
  simp [constituentMomentumPlus, constituentMomentumMinus]
  ring

/-- A four-dimensional Bethe--Salpeter bispinor amplitude. -/
abbrev BispinorAmplitude4 := RelativeMomentum4 → Matrix (Fin 4) (Fin 4) ℂ

/-- The two-sided free Dirac factor in the symmetric momentum routing.
It keeps both spinor indices of the fermion--antifermion amplitude. -/
def twoBodyDiracKinetic
    (P : Fin 4 → ℝ) (m₁ m₂ : ℝ) (q : RelativeMomentum4)
    (Phi : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  diracOp (constituentMomentumPlus P q) m₁ * Phi *
    diracOp (constituentMomentumMinus P q) m₂

/-- The full homogeneous four-dimensional fermion--antifermion
Bethe--Salpeter equation.  The right-hand side is a Bochner integral over
`k : Lorentz.Vector 3`, so the relative energy is not integrated out and no
instantaneous or finite-mode reduction is hidden in the definition. -/
def SatisfiesFourDimensionalDiracBSE
    (P : Fin 4 → ℝ) (m₁ m₂ : ℝ) (lambda : ℂ)
    (kernel : RelativeMomentum4 → RelativeMomentum4 →
      Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (Phi : BispinorAmplitude4) : Prop :=
  ∀ᵐ q ∂(volume : Measure RelativeMomentum4),
    twoBodyDiracKinetic P m₁ m₂ q (Phi q) =
      lambda • Matrix.of (fun i j =>
        ∫ k, kernel q k (Phi k) i j ∂(volume : Measure RelativeMomentum4))

/-! ## B. The actual `L²(ℝ⁴)` separable ladder operator -/

/-- Scalar `L²(ℝ⁴)` relative-momentum wavefunctions.  Spin channels of
the bispinor equation may be projected to this carrier one at a time. -/
abbrev BetheSalpeterL2 :=
  MeasureTheory.Lp ℂ 2 (volume : Measure RelativeMomentum4)

/-! ### B.1. Explicit four-dimensional Hermite carrier -/

/-- Euclidean coordinates for relative four-momentum. -/
abbrev EuclideanRelativeMomentum4 := EuclideanSpace ℝ (Fin 4)

/-- The Lorentz-vector carrier is linearly isometric to four Euclidean
coordinates.  This concerns the positive Hilbert norm and volume used by the
analytical `L²` carrier; it does not identify the Euclidean norm with the
indefinite Minkowski quadratic form. -/
noncomputable def relativeMomentumEuclideanEquiv :
    RelativeMomentum4 ≃ₗᵢ[ℝ] EuclideanRelativeMomentum4 :=
  ({ Lorentz.Vector.equivEuclid 3 with norm_map' := fun _ => rfl } :
      RelativeMomentum4 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin 3)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)

/-- The coordinate basis used by `SpaceTime` is orthonormal for the positive
Hilbert inner product on the Lorentz-vector carrier. -/
lemma relativeMomentumBasis_orthonormal :
    Orthonormal ℝ
      (Lorentz.Vector.basis : (Fin 1 ⊕ Fin 3) → RelativeMomentum4) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [Lorentz.Vector.basis_inner, Lorentz.Vector.basis_apply]
  simp [eq_comm]

/-- The `SpaceTime` Haar measure instance agrees with the canonical volume
of its positive finite-dimensional Hilbert structure. -/
lemma relativeMomentum_volume_eq_innerProductVolume :
    (volume : Measure RelativeMomentum4) =
      @volume RelativeMomentum4 measureSpaceOfInnerProductSpace := by
  let b : OrthonormalBasis (Fin 1 ⊕ Fin 3) ℝ RelativeMomentum4 :=
    Lorentz.Vector.basis.toOrthonormalBasis
      relativeMomentumBasis_orthonormal
  change Lorentz.Vector.basis.addHaar = _
  rw [← b.addHaar_eq_volume]
  exact congrArg Module.Basis.addHaar
    (Module.Basis.toBasis_toOrthonormalBasis
      Lorentz.Vector.basis relativeMomentumBasis_orthonormal)

/-- The coordinate isometry preserves four-dimensional Lebesgue volume. -/
lemma relativeMomentumEuclideanEquiv_measurePreserving :
    MeasurePreserving relativeMomentumEuclideanEquiv volume volume :=
  by
    rw [relativeMomentum_volume_eq_innerProductVolume]
    exact LinearIsometryEquiv.measurePreserving
      relativeMomentumEuclideanEquiv

/-- The inverse coordinate isometry also preserves volume. -/
lemma relativeMomentumEuclideanEquiv_symm_measurePreserving :
    MeasurePreserving relativeMomentumEuclideanEquiv.symm volume volume :=
  by
    rw [relativeMomentum_volume_eq_innerProductVolume]
    exact LinearIsometryEquiv.measurePreserving
      relativeMomentumEuclideanEquiv.symm

/-- Pullback along a two-sided measure-preserving equivalence is a linear
isometric equivalence of `L²` spaces. -/
noncomputable def lpEquivOfMeasurePreserving
    {A B : Type*} [MeasureSpace A] [MeasureSpace B]
    (e : A ≃ B) (he : MeasurePreserving e volume volume)
    (hes : MeasurePreserving e.symm volume volume) :
    Lp ℂ 2 (volume : Measure B) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure A) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ e he)
    (fun g => by
      refine ⟨Lp.compMeasurePreserving e.symm hes g, ?_⟩
      change Lp.compMeasurePreserving e he
        (Lp.compMeasurePreserving e.symm hes g) = g
      rw [← Lp.compMeasurePreserving_comp_apply g hes he]
      apply Lp.ext (μ := volume)
      filter_upwards
        [Lp.coeFn_compMeasurePreserving g (hes.comp he)] with x hx
      simpa only [Function.comp_apply, e.symm_apply_apply] using hx)

/-- Exact `L²` transport from Euclidean four-momentum to the repository's
Bethe--Salpeter relative-momentum carrier. -/
noncomputable def betheSalpeterCarrierEquiv :
    Lp ℂ 2 (volume : Measure EuclideanRelativeMomentum4) ≃ₗᵢ[ℂ]
      BetheSalpeterL2 :=
  lpEquivOfMeasurePreserving relativeMomentumEuclideanEquiv
    relativeMomentumEuclideanEquiv_measurePreserving
    relativeMomentumEuclideanEquiv_symm_measurePreserving

/-- The `n`th real tensor-Hermite Schwartz function in four dimensions,
embedded into the complex Schwartz space. -/
noncomputable def euclideanHermiteSchwartzMode4 (n : ℕ) :
    SchwartzMap EuclideanRelativeMomentum4 ℂ :=
  iotaSchwartz EuclideanRelativeMomentum4 (flatBasisNd 3 n)

/-- The `n`th tensor-Hermite mode as an actual complex `L²(ℝ⁴)` vector. -/
noncomputable def euclideanHermiteL2Mode4 (n : ℕ) :
    Lp ℂ 2 (volume : Measure EuclideanRelativeMomentum4) :=
  SchwartzMap.toLpCLM ℂ (E := EuclideanRelativeMomentum4) ℂ 2
    (μ := volume) (euclideanHermiteSchwartzMode4 n)

lemma euclideanHermiteL2Mode4_coe_ae (n : ℕ) :
    euclideanHermiteL2Mode4 n =ᵐ[volume]
      euclideanHermiteSchwartzMode4 n :=
  SchwartzMap.coeFn_toLp (euclideanHermiteSchwartzMode4 n) 2 volume

/-- The four-dimensional tensor-Hermite `L²` modes have the exact
Kronecker inner product. -/
lemma euclideanHermiteL2Mode4_inner (m n : ℕ) :
    ⟪euclideanHermiteL2Mode4 m, euclideanHermiteL2Mode4 n⟫_ℂ =
      if m = n then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, ⟪euclideanHermiteL2Mode4 m x,
        euclideanHermiteL2Mode4 n x⟫_ℂ) =
        ∫ x, ((flatBasisNd 3 m x * flatBasisNd 3 n x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [euclideanHermiteL2Mode4_coe_ae m,
        euclideanHermiteL2Mode4_coe_ae n] with x hm hn
      rw [hm, hn]
      simp [euclideanHermiteSchwartzMode4, iotaSchwartz, mul_comm]
    _ = if m = n then 1 else 0 := by
      rw [integral_complex_ofReal]
      change ((∫ x, hermiteFunctionNd 4 ((multiIndexEquiv 3).symm m) x *
        hermiteFunctionNd 4 ((multiIndexEquiv 3).symm n) x : ℝ) : ℂ) = _
      rw [hermiteFunctionNd_orthonormal]
      simp only [(multiIndexEquiv 3).symm.injective.eq_iff]
      split_ifs <;> simp

/-- The included four-dimensional Hermite modes are orthonormal in complex
`L²`. -/
lemma euclideanHermiteL2Mode4_orthonormal :
    Orthonormal ℂ euclideanHermiteL2Mode4 := by
  rw [orthonormal_iff_ite]
  exact euclideanHermiteL2Mode4_inner

noncomputable def euclideanSchwartzIncl4 :
    SchwartzMap EuclideanRelativeMomentum4 ℂ →L[ℂ]
      Lp ℂ 2 (volume : Measure EuclideanRelativeMomentum4) :=
  SchwartzMap.toLpCLM ℂ (E := EuclideanRelativeMomentum4) ℂ 2

noncomputable def realEuclideanSchwartzIncl4 :
    SchwartzMap EuclideanRelativeMomentum4 ℝ →L[ℝ]
      Lp ℂ 2 (volume : Measure EuclideanRelativeMomentum4) :=
  (euclideanSchwartzIncl4.restrictScalars ℝ).comp
    (iotaSchwartz EuclideanRelativeMomentum4)

lemma realEuclideanSchwartzIncl4_flatBasis (n : ℕ) :
    realEuclideanSchwartzIncl4 (flatBasisNd 3 n) =
      euclideanHermiteL2Mode4 n := by
  rfl

lemma realEuclideanSchwartzIncl4_mem_hermiteClosure
    (f : SchwartzMap EuclideanRelativeMomentum4 ℝ) :
    realEuclideanSchwartzIncl4 f ∈
      (Submodule.span ℂ
        (Set.range euclideanHermiteL2Mode4)).topologicalClosure := by
  have hsum :=
    (schwartz_hermite_completeness_nd 3 f).map
      realEuclideanSchwartzIncl4 realEuclideanSchwartzIncl4.continuous
  refine mem_closure_of_tendsto hsum (Filter.Eventually.of_forall ?_)
  intro s
  exact Submodule.sum_mem _ fun n _ => by
    change realEuclideanSchwartzIncl4
      (hermiteCoeffNd 4 ((multiIndexEquiv 3).symm n) f •
        flatBasisNd 3 n) ∈ _
    rw [map_smul, realEuclideanSchwartzIncl4_flatBasis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

lemma euclideanSchwartzIncl4_mem_hermiteClosure
    (f : SchwartzMap EuclideanRelativeMomentum4 ℂ) :
    euclideanSchwartzIncl4 f ∈
      (Submodule.span ℂ
        (Set.range euclideanHermiteL2Mode4)).topologicalClosure := by
  rw [schwartz_complex_decomp f, map_add, map_smul]
  exact Submodule.add_mem _
    (realEuclideanSchwartzIncl4_mem_hermiteClosure
      (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM f))
    (Submodule.smul_mem _ _
      (realEuclideanSchwartzIncl4_mem_hermiteClosure
        (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM f)))

/-- The tensor-Hermite modes have dense complex span in `L²(ℝ⁴)`.  This
uses the already proved Schwartz Hermite completeness theorem followed by
the standard dense inclusion of Schwartz functions into `L²`. -/
lemma euclideanHermiteL2Mode4_dense_span :
    (⊤ : Submodule ℂ
      (Lp ℂ 2 (volume : Measure EuclideanRelativeMomentum4))) ≤
      (Submodule.span ℂ
        (Set.range euclideanHermiteL2Mode4)).topologicalClosure := by
  intro psi _
  have hdense : Dense (Set.range euclideanSchwartzIncl4) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.top_ne_ofNat.symm
  have hclosure : psi ∈ closure (Set.range euclideanSchwartzIncl4) := by
    rw [hdense.closure_eq]
    trivial
  exact (closure_minimal
    (fun y hy => by
      obtain ⟨f, rfl⟩ := hy
      exact euclideanSchwartzIncl4_mem_hermiteClosure f)
    (Submodule.isClosed_topologicalClosure _)) hclosure

/-- The explicit four-dimensional tensor-Hermite Hilbert basis. -/
noncomputable def euclideanHermiteHilbertBasis4 :
    HilbertBasis ℕ ℂ
      (Lp ℂ 2 (volume : Measure EuclideanRelativeMomentum4)) :=
  HilbertBasis.mk euclideanHermiteL2Mode4_orthonormal
    euclideanHermiteL2Mode4_dense_span

@[simp]
lemma euclideanHermiteHilbertBasis4_apply (n : ℕ) :
    euclideanHermiteHilbertBasis4 n = euclideanHermiteL2Mode4 n := by
  exact congrFun
    (HilbertBasis.coe_mk euclideanHermiteL2Mode4_orthonormal
      euclideanHermiteL2Mode4_dense_span) n

/-- Transport a Hilbert basis along a linear isometric equivalence. -/
noncomputable def transportHilbertBasis
    {ι 𝕜 H H' : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    (b : HilbertBasis ι 𝕜 H) (e : H ≃ₗᵢ[𝕜] H') :
    HilbertBasis ι 𝕜 H' :=
  HilbertBasis.ofRepr (e.symm.trans b.repr)

@[simp]
lemma transportHilbertBasis_apply
    {ι 𝕜 H H' : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    (b : HilbertBasis ι 𝕜 H) (e : H ≃ₗᵢ[𝕜] H') (i : ι) :
    transportHilbertBasis b e i = e (b i) := by
  classical
  apply (transportHilbertBasis b e).repr.injective
  rw [(transportHilbertBasis b e).repr_self]
  simp [transportHilbertBasis, b.repr_self]

/-- The canonical four-dimensional Hermite Hilbert basis on the exact
Bethe--Salpeter carrier. -/
noncomputable def betheSalpeterHermiteHilbertBasis :
    HilbertBasis ℕ ℂ BetheSalpeterL2 :=
  transportHilbertBasis euclideanHermiteHilbertBasis4
    betheSalpeterCarrierEquiv

@[simp]
lemma betheSalpeterHermiteHilbertBasis_apply (n : ℕ) :
    betheSalpeterHermiteHilbertBasis n =
      betheSalpeterCarrierEquiv (euclideanHermiteL2Mode4 n) := by
  simp [betheSalpeterHermiteHilbertBasis]

/-- The symmetric separable four-dimensional ladder kernel `|u⟩⟨u|`.
This is the self-adjoint specialization of the continuum Cutkosky operator. -/
def fourDimensionalSeparableKernel (u : BetheSalpeterL2) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  cutkoskyContinuumKernelOperator
    (volume : Measure RelativeMomentum4) u u

/-- The four-dimensional separable operator acts by the genuine `d⁴k`
inner-product integral. -/
lemma fourDimensionalSeparableKernel_apply (u psi : BetheSalpeterL2) :
    fourDimensionalSeparableKernel u psi =
      (∫ k, ⟪u k, psi k⟫_ℂ ∂(volume : Measure RelativeMomentum4)) • u := by
  exact cutkoskyContinuumKernelOperator_apply
    (volume : Measure RelativeMomentum4) u u psi

/-- The four-dimensional separable ladder operator is compact. -/
lemma fourDimensionalSeparableKernel_isCompact (u : BetheSalpeterL2) :
    IsCompactOperator (fourDimensionalSeparableKernel u) := by
  exact cutkoskyContinuumKernelOperator_isCompact
    (volume : Measure RelativeMomentum4) u u

/-- The symmetric separable ladder operator is self-adjoint. -/
lemma fourDimensionalSeparableKernel_isSymmetric (u : BetheSalpeterL2) :
    (fourDimensionalSeparableKernel u).IsSymmetric := by
  exact InnerProductSpace.isSymmetric_rankOne_self u

/-- The homogeneous operator form of the four-dimensional scalar
Bethe--Salpeter equation, `K psi = lambda psi`. -/
def SatisfiesFourDimensionalScalarBSE
    (u : BetheSalpeterL2) (lambda : ℂ) (psi : BetheSalpeterL2) : Prop :=
  fourDimensionalSeparableKernel u psi = lambda • psi

/-- The operator equation is exactly the `d⁴k` integral equation. -/
lemma satisfiesFourDimensionalScalarBSE_iff_integral
    (u : BetheSalpeterL2) (lambda : ℂ) (psi : BetheSalpeterL2) :
    SatisfiesFourDimensionalScalarBSE u lambda psi ↔
      (∫ k, ⟪u k, psi k⟫_ℂ ∂(volume : Measure RelativeMomentum4)) • u =
        lambda • psi := by
  rw [SatisfiesFourDimensionalScalarBSE,
    fourDimensionalSeparableKernel_apply]

/-! ## B.1. Interacting Hermitian kernels by Schmidt truncation -/

/-- A finite Hermitian Schmidt truncation of an interacting QED kernel.
Each mode contributes the genuine four-dimensional integral operator
`aᵢ |uᵢ⟩⟨uᵢ|`; the coefficient is real, which is exactly what preserves
Hermiticity. -/
def finiteHermitianQEDKernel {N : ℕ} (coupling : Fin N → ℝ)
    (mode : Fin N → BetheSalpeterL2) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  ∑ i, (coupling i : ℂ) • fourDimensionalSeparableKernel (mode i)

/-- Every finite Hermitian Schmidt truncation is compact.  This is an actual
finite-rank proof assembled from the continuum rank-one Cutkosky operators,
not a finite-dimensional replacement of `L²(ℝ⁴)`. -/
lemma finiteHermitianQEDKernel_isCompact {N : ℕ} (coupling : Fin N → ℝ)
    (mode : Fin N → BetheSalpeterL2) :
    IsCompactOperator (finiteHermitianQEDKernel coupling mode) := by
  classical
  unfold finiteHermitianQEDKernel
  induction (Finset.univ : Finset (Fin N)) using Finset.induction_on with
  | empty =>
      change IsCompactOperator (fun _ : BetheSalpeterL2 => 0)
      exact isCompactOperator_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((fourDimensionalSeparableKernel_isCompact (mode i)).smul
        (coupling i : ℂ)).add ih

/-- Every finite Hermitian Schmidt truncation is symmetric/self-adjoint in
the bounded-operator sense. -/
lemma finiteHermitianQEDKernel_isSymmetric {N : ℕ} (coupling : Fin N → ℝ)
    (mode : Fin N → BetheSalpeterL2) :
    (finiteHermitianQEDKernel coupling mode).IsSymmetric := by
  classical
  unfold finiteHermitianQEDKernel
  simpa only [ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_smul] using
    (LinearMap.isSymmetric_sum Finset.univ fun i _ =>
      (fourDimensionalSeparableKernel_isSymmetric (mode i)).smul (by simp))

/-- Analytical data for a general interacting Hermitian QED kernel on the
four-dimensional Bethe--Salpeter carrier.  The only substantive hypothesis is
operator-norm convergence of finite Hermitian Schmidt truncations.  This is
the standard sufficient condition that exposes exactly what must be proved
for a concrete photon-exchange/renormalized kernel. -/
structure InteractingQEDKernelApproximation where
  /-- The limiting interacting kernel operator. -/
  operator : BetheSalpeterL2 →L[ℂ] BetheSalpeterL2
  /-- Number of retained Schmidt modes at each truncation. -/
  rank : ℕ → ℕ
  /-- Real spectral couplings of the Hermitian truncations. -/
  coupling : (n : ℕ) → Fin (rank n) → ℝ
  /-- Four-dimensional `L²` modes of the truncations. -/
  mode : (n : ℕ) → Fin (rank n) → BetheSalpeterL2
  /-- Operator-norm convergence to the interacting kernel. -/
  tendsto_operator : Filter.Tendsto
    (fun n => finiteHermitianQEDKernel (coupling n) (mode n))
    Filter.atTop (nhds operator)

/-- **Target 1: interacting-kernel compactness.**  An operator-norm limit of
the finite Hermitian Schmidt truncations is compact because compact operators
form an operator-norm closed subspace. -/
theorem InteractingQEDKernelApproximation.isCompact
    (K : InteractingQEDKernelApproximation) :
    IsCompactOperator K.operator := by
  exact isCompactOperator_of_tendsto K.tendsto_operator
    (Filter.Eventually.of_forall fun n =>
      finiteHermitianQEDKernel_isCompact (K.coupling n) (K.mode n))

/-- Symmetry is closed under operator-norm convergence.  This generic lemma
is useful beyond Bethe--Salpeter theory and avoids storing symmetry as an
unproved field in the interacting-kernel data. -/
lemma isSymmetric_of_operatorNorm_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {A : ι → BetheSalpeterL2 →L[ℂ] BetheSalpeterL2}
    {K : BetheSalpeterL2 →L[ℂ] BetheSalpeterL2}
    (hA : Filter.Tendsto A l (nhds K))
    (hSymm : ∀ i, (A i).IsSymmetric) : K.IsSymmetric := by
  intro psi phi
  have hpsi : Filter.Tendsto (fun i => A i psi) l (nhds (K psi)) :=
    ((continuous_id.clm_apply continuous_const).continuousAt.tendsto).comp hA
  have hphi : Filter.Tendsto (fun i => A i phi) l (nhds (K phi)) :=
    ((continuous_id.clm_apply continuous_const).continuousAt.tendsto).comp hA
  have hleft : Filter.Tendsto (fun i => ⟪A i psi, phi⟫_ℂ) l
      (nhds ⟪K psi, phi⟫_ℂ) :=
    hpsi.inner tendsto_const_nhds
  have hright : Filter.Tendsto (fun i => ⟪psi, A i phi⟫_ℂ) l
      (nhds ⟪psi, K phi⟫_ℂ) :=
    tendsto_const_nhds.inner hphi
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun i => (hSymm i psi phi).symm))

/-- **Target 2: interacting-kernel symmetry.**  Hermiticity of every real
Schmidt truncation passes to the operator-norm limit. -/
theorem InteractingQEDKernelApproximation.isSymmetric
    (K : InteractingQEDKernelApproximation) : K.operator.IsSymmetric := by
  exact isSymmetric_of_operatorNorm_tendsto K.tendsto_operator fun n =>
    finiteHermitianQEDKernel_isSymmetric (K.coupling n) (K.mode n)

/-! ## B.2. An intrinsic summability criterion for interacting kernels -/

/-- Concrete analytic data for an infinite Hermitian QED mode expansion.
The condition
`∑ₙ |aₙ| ‖uₙ‖² < ∞`
is directly checkable on the couplings and four-dimensional wavefunctions;
it is stronger than abstract compactness, but unlike a stored convergence
certificate it automatically proves operator-norm convergence of the kernel
series. -/
structure AbsolutelySummableHermitianQEDKernel where
  /-- Real Hermitian spectral couplings. -/
  coupling : ℕ → ℝ
  /-- Four-dimensional Bethe--Salpeter modes. -/
  mode : ℕ → BetheSalpeterL2
  /-- Absolute summability of the rank-one operator norms. -/
  summable_weighted_norm :
    Summable (fun n => |coupling n| * ‖mode n‖ ^ 2)

/-- Operator norm of one diagonal Cutkosky mode. -/
lemma norm_fourDimensionalSeparableKernel (u : BetheSalpeterL2) :
    ‖fourDimensionalSeparableKernel u‖ = ‖u‖ ^ 2 := by
  rw [show fourDimensionalSeparableKernel u =
      InnerProductSpace.rankOne ℂ u u from rfl,
    InnerProductSpace.norm_rankOne, pow_two]

/-- Absolute summability of `|aₙ| ‖uₙ‖²` makes the corresponding series of
Cutkosky rank-one operators summable in operator norm. -/
lemma AbsolutelySummableHermitianQEDKernel.summable_operator
    (K : AbsolutelySummableHermitianQEDKernel) :
    Summable (fun n =>
      (K.coupling n : ℂ) • fourDimensionalSeparableKernel (K.mode n)) := by
  apply Summable.of_norm
  convert K.summable_weighted_norm using 1
  funext n
  rw [norm_smul, norm_fourDimensionalSeparableKernel,
    Complex.norm_real, Real.norm_eq_abs]

/-- The infinite interacting kernel defined by the norm-convergent Hermitian
mode expansion. -/
noncomputable def AbsolutelySummableHermitianQEDKernel.operator
    (K : AbsolutelySummableHermitianQEDKernel) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  ∑' n, (K.coupling n : ℂ) • fourDimensionalSeparableKernel (K.mode n)

/-- **Constructive cutoff theorem.**  Absolute mode summability constructs
the exact approximation interface used above: the `N`th approximant retains
the first `N` genuine `d⁴k` Cutkosky modes, and these finite Hermitian kernels
converge in operator norm to the infinite interacting operator. -/
noncomputable def AbsolutelySummableHermitianQEDKernel.approximation
    (K : AbsolutelySummableHermitianQEDKernel) :
    InteractingQEDKernelApproximation where
  operator := K.operator
  rank := fun n => n
  coupling := fun _ i => K.coupling i
  mode := fun _ i => K.mode i
  tendsto_operator := by
    change Filter.Tendsto
      (fun n => finiteHermitianQEDKernel
        (fun i : Fin n => K.coupling i) (fun i : Fin n => K.mode i))
      Filter.atTop
      (nhds (∑' n, (K.coupling n : ℂ) •
        fourDimensionalSeparableKernel (K.mode n)))
    have hpartial :
        (fun n => finiteHermitianQEDKernel
          (fun i : Fin n => K.coupling i) (fun i : Fin n => K.mode i)) =
        (fun n => ∑ i ∈ Finset.range n,
          (K.coupling i : ℂ) • fourDimensionalSeparableKernel (K.mode i)) := by
      funext n
      rw [finiteHermitianQEDKernel, Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    rw [hpartial]
    exact K.summable_operator.hasSum.tendsto_sum_nat

/-! ## B.3. Entropic-dynamics damping constructs the QED kernel -/

/-- A four-dimensional interacting mode family whose successive channels
carry a strictly positive imaginary-action gap.  The modes are normalized
only by the honest bound `‖uₙ‖ ≤ 1`; their mutual orthogonality is not needed
for compactness.  `phaseAction` records the real Nagao--Nielsen action and
does not affect the damping estimate. -/
structure EntropicDampedQEDModeFamily where
  /-- Positive imaginary-action increment between successive modes. -/
  dampingRate : ℝ
  dampingRate_pos : 0 < dampingRate
  /-- Real-action phase assigned to each mode. -/
  phaseAction : ℕ → ℝ
  /-- Four-dimensional interacting Bethe--Salpeter modes. -/
  mode : ℕ → BetheSalpeterL2
  /-- Uniform mode normalization used in the summability comparison. -/
  mode_norm_le_one : ∀ n, ‖mode n‖ ≤ 1

/-- The `n`th entropic QED coupling is the Caticha transition weight for the
step `Δχₙ = √(n γ)` at `α = 2`, so its imaginary action is `n γ`. -/
noncomputable def EntropicDampedQEDModeFamily.coupling
    (K : EntropicDampedQEDModeFamily) (n : ℕ) : ℝ :=
  edTransitionWeight 2 0 (Real.sqrt ((n : ℝ) * K.dampingRate))

/-- **Target 1a: exact damping law.**  The ED coupling is exactly the
geometric Nagao--Nielsen damping `exp (-n γ)`. -/
lemma EntropicDampedQEDModeFamily.coupling_eq_exp
    (K : EntropicDampedQEDModeFamily) (n : ℕ) :
    K.coupling n = Real.exp (-((n : ℝ) * K.dampingRate)) := by
  unfold EntropicDampedQEDModeFamily.coupling edTransitionWeight edEntropicAction
  have hnonneg : 0 ≤ (n : ℝ) * K.dampingRate :=
    mul_nonneg (Nat.cast_nonneg n) K.dampingRate_pos.le
  rw [sub_zero, Real.sq_sqrt hnonneg]
  congr 1
  ring

/-- **Target 1b: ED and complex action are one mode weight.**  For every QED
mode, the same real coupling is simultaneously the ED transition
probability, the modulus of the Nagao--Nielsen complex-action weight, and its
entropy-damping factor; the ED wave-function phase carries the real action. -/
theorem EntropicDampedQEDModeFamily.coupling_is_ed_nagaoNielsen
    (K : EntropicDampedQEDModeFamily) (n : ℕ) :
    K.coupling n =
        ‖complexActionPathIntegralWeight (K.phaseAction n)
          ((Real.sqrt ((n : ℝ) * K.dampingRate) - 0) ^ 2) (2 / 2)‖
      ∧ K.coupling n =
        entropyDamping
          ((Real.sqrt ((n : ℝ) * K.dampingRate) - 0) ^ 2) (2 / 2)
      ∧ edWaveFunction 1 (K.phaseAction n) =
        Complex.exp (((K.phaseAction n : ℝ) : ℂ) * Complex.I) := by
  exact ed_is_nagaoNielsen_complexAction 2 0
    (Real.sqrt ((n : ℝ) * K.dampingRate))
    (K.phaseAction n) (K.phaseAction n) (by norm_num)

/-- **Target 2a: the physical damping discharges the analytic premise.**
Positive imaginary-action gap and bounded mode norms prove
`∑ₙ |aₙ| ‖uₙ‖² < ∞` by comparison with the geometric series
`∑ₙ exp (-n γ)`. -/
lemma EntropicDampedQEDModeFamily.summable_weighted_norm
    (K : EntropicDampedQEDModeFamily) :
    Summable (fun n => |K.coupling n| * ‖K.mode n‖ ^ 2) := by
  have hs : Summable (fun n : ℕ =>
      Real.exp ((n : ℝ) * (-K.dampingRate))) :=
    Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos K.dampingRate_pos)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (sq_nonneg _)) ?_ hs
  intro n
  rw [K.coupling_eq_exp, abs_of_pos (Real.exp_pos _)]
  have hmode_sq : ‖K.mode n‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (K.mode n), K.mode_norm_le_one n]
  have hexp :
      Real.exp (-((n : ℝ) * K.dampingRate)) =
        Real.exp ((n : ℝ) * (-K.dampingRate)) := by
    congr 1
    ring
  rw [hexp]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) hmode_sq

/-- The entropically damped family automatically supplies the absolute
Hermitian QED kernel data constructed in §B.2. -/
noncomputable def EntropicDampedQEDModeFamily.toAbsolutelySummable
    (K : EntropicDampedQEDModeFamily) :
    AbsolutelySummableHermitianQEDKernel where
  coupling := K.coupling
  mode := K.mode
  summable_weighted_norm := K.summable_weighted_norm

/-- The resulting infinite four-dimensional entropic QED kernel. -/
noncomputable def EntropicDampedQEDModeFamily.operator
    (K : EntropicDampedQEDModeFamily) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  K.toAbsolutelySummable.operator

/-! ## B.4. Full complex-action resonance kernels -/

/-- A four-dimensional QED mode family carrying the full Nagao--Nielsen
complex weight.  Unlike `EntropicDampedQEDModeFamily`, this structure retains
the real-action phase and therefore does not assert Hermiticity.  The same
positive imaginary-action gap and honest mode bound control its operator
norm. -/
structure ComplexActionDampedQEDModeFamily where
  /-- Positive imaginary-action increment between successive modes. -/
  dampingRate : ℝ
  dampingRate_pos : 0 < dampingRate
  /-- Real Nagao--Nielsen action of each four-dimensional mode. -/
  phaseAction : ℕ → ℝ
  /-- Four-dimensional interacting Bethe--Salpeter modes. -/
  mode : ℕ → BetheSalpeterL2
  /-- Uniform mode normalization used in the summability comparison. -/
  mode_norm_le_one : ∀ n, ‖mode n‖ ≤ 1

/-- The full complex coupling of mode `n`, with real action
`phaseAction n`, imaginary action `n γ`, and `ℏ = 1`. -/
noncomputable def ComplexActionDampedQEDModeFamily.coupling
    (K : ComplexActionDampedQEDModeFamily) (n : ℕ) : ℂ :=
  complexActionPathIntegralWeight (K.phaseAction n)
    ((n : ℝ) * K.dampingRate) 1

/-- **Target 1: the full complex coupling has the ED modulus.**  Retaining
the Nagao--Nielsen phase does not change the Caticha transition probability:
both have modulus `exp (-n γ)`. -/
lemma ComplexActionDampedQEDModeFamily.norm_coupling_eq_edTransitionWeight
    (K : ComplexActionDampedQEDModeFamily) (n : ℕ) :
    ‖K.coupling n‖ =
      edTransitionWeight 2 0 (Real.sqrt ((n : ℝ) * K.dampingRate)) := by
  rw [show ‖K.coupling n‖ = Real.exp (-((n : ℝ) * K.dampingRate)) by
    rw [ComplexActionDampedQEDModeFamily.coupling,
      master_modulus_is_kuiken]
    simp [kuikenWeight]]
  exact (EntropicDampedQEDModeFamily.coupling_eq_exp
    { dampingRate := K.dampingRate
      dampingRate_pos := K.dampingRate_pos
      phaseAction := K.phaseAction
      mode := K.mode
      mode_norm_le_one := K.mode_norm_le_one } n).symm

/-- The complex-action mode strengths are absolutely summable in the exact
operator-norm majorant `∑ₙ ‖aₙ‖ ‖uₙ‖²`. -/
lemma ComplexActionDampedQEDModeFamily.summable_weighted_norm
    (K : ComplexActionDampedQEDModeFamily) :
    Summable (fun n => ‖K.coupling n‖ * ‖K.mode n‖ ^ 2) := by
  let H : EntropicDampedQEDModeFamily :=
    { dampingRate := K.dampingRate
      dampingRate_pos := K.dampingRate_pos
      phaseAction := K.phaseAction
      mode := K.mode
      mode_norm_le_one := K.mode_norm_le_one }
  convert H.summable_weighted_norm using 1
  funext n
  rw [K.norm_coupling_eq_edTransitionWeight]
  change edTransitionWeight 2 0 (Real.sqrt ((n : ℝ) * K.dampingRate)) *
      ‖K.mode n‖ ^ 2 =
    |edTransitionWeight 2 0 (Real.sqrt ((n : ℝ) * K.dampingRate))| *
      ‖K.mode n‖ ^ 2
  rw [abs_of_nonneg]
  unfold edTransitionWeight
  exact Real.exp_nonneg _

/-- The finite full-complex-action kernel retaining the first `N` modes. -/
noncomputable def ComplexActionDampedQEDModeFamily.partialKernel
    (K : ComplexActionDampedQEDModeFamily) (N : ℕ) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  ∑ n ∈ Finset.range N,
    K.coupling n • fourDimensionalSeparableKernel (K.mode n)

/-- Every finite full-complex-action truncation is compact even though its
complex coefficients need not define a symmetric operator. -/
lemma ComplexActionDampedQEDModeFamily.partialKernel_isCompact
    (K : ComplexActionDampedQEDModeFamily) (N : ℕ) :
    IsCompactOperator (K.partialKernel N) := by
  induction N with
  | zero =>
      simp only [ComplexActionDampedQEDModeFamily.partialKernel,
        Finset.range_zero, Finset.sum_empty]
      change IsCompactOperator (fun _ : BetheSalpeterL2 => 0)
      exact isCompactOperator_zero
  | succ N ih =>
      rw [ComplexActionDampedQEDModeFamily.partialKernel,
        Finset.sum_range_succ, ← ComplexActionDampedQEDModeFamily.partialKernel]
      exact ih.add ((fourDimensionalSeparableKernel_isCompact (K.mode N)).smul
        (K.coupling N))

/-- The infinite four-dimensional kernel with the complete
Nagao--Nielsen phase-times-damping weight. -/
noncomputable def ComplexActionDampedQEDModeFamily.operator
    (K : ComplexActionDampedQEDModeFamily) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  ∑' n, K.coupling n • fourDimensionalSeparableKernel (K.mode n)

/-- The full complex-action operator series is summable in operator norm. -/
lemma ComplexActionDampedQEDModeFamily.summable_operator
    (K : ComplexActionDampedQEDModeFamily) :
    Summable (fun n =>
      K.coupling n • fourDimensionalSeparableKernel (K.mode n)) := by
  apply Summable.of_norm
  convert K.summable_weighted_norm using 1
  funext n
  rw [norm_smul, norm_fourDimensionalSeparableKernel]

/-- **Target 2: complex-action damping constructs a compact non-Hermitian
kernel.**  Compactness follows from operator-norm convergence of the finite
four-dimensional Cutkosky truncations; symmetry is deliberately absent. -/
lemma ComplexActionDampedQEDModeFamily.isCompact
    (K : ComplexActionDampedQEDModeFamily) :
    IsCompactOperator K.operator := by
  apply isCompactOperator_of_tendsto
    K.summable_operator.hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall K.partialKernel_isCompact

/-- Every nonzero resonance eigenspace of the compact complex-action kernel
has finite multiplicity.  This conclusion needs compactness but not
self-adjointness. -/
lemma ComplexActionDampedQEDModeFamily.nonzero_finiteMultiplicity
    (K : ComplexActionDampedQEDModeFamily) (lambda : ℂ)
    (hlambda : lambda ≠ 0) :
    FiniteDimensional ℂ
      (Module.End.eigenspace K.operator.toLinearMap lambda) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    K.isCompact lambda hlambda

/-- **Target 3: non-Hermitian Fredholm solvability.**  Away from a nonzero
resonance eigenvalue, every source has a unique four-dimensional
Bethe--Salpeter coefficient. -/
theorem ComplexActionDampedQEDModeFamily.uniqueCoefficient_of_not_eigenvalue
    (K : ComplexActionDampedQEDModeFamily) (lambda : ℂ)
    (hlambda : lambda ≠ 0)
    (hnotEigen : ¬ Module.End.HasEigenvalue K.operator.toLinearMap lambda) :
    ∀ source : BetheSalpeterL2, ∃! coefficient : BetheSalpeterL2,
      (lambda • (1 : BetheSalpeterL2 →L[ℂ] BetheSalpeterL2) - K.operator)
        coefficient = source :=
  bassetto_uniqueCoefficient_of_compact_of_not_eigenvalue
    K.operator lambda K.isCompact hlambda hnotEigen

/-! ## B.5. Shared self-adjoint eigenbasis for diagonal resonances -/

/-- A complex-action resonance family whose four-dimensional modes are a
complete orthonormal Hilbert basis.  This is the infinite-dimensional
counterpart of the repository's Nagao--Nielsen `Q`-normal diagonalization:
the self-adjoint damping operator and the full complex resonance operator are
diagonal in the same basis. -/
structure DiagonalComplexActionResonanceFamily where
  /-- Positive imaginary-action increment between successive modes. -/
  dampingRate : ℝ
  dampingRate_pos : 0 < dampingRate
  /-- Real complex-action phase assigned to each resonance mode. -/
  phaseAction : ℕ → ℝ
  /-- Complete orthonormal basis of the four-dimensional relative-momentum
  carrier. -/
  basis : HilbertBasis ℕ ℂ BetheSalpeterL2

/-- The canonical diagonal resonance family built from the explicit
four-dimensional tensor-Hermite basis.  Unlike the general structure above,
this constructor takes no basis or completeness certificate. -/
noncomputable def hermiteDiagonalResonanceFamily
    (dampingRate : ℝ) (hdamping : 0 < dampingRate)
    (phaseAction : ℕ → ℝ) : DiagonalComplexActionResonanceFamily where
  dampingRate := dampingRate
  dampingRate_pos := hdamping
  phaseAction := phaseAction
  basis := betheSalpeterHermiteHilbertBasis

/-- Forgetting orthonormality gives the full complex-action mode family. -/
noncomputable def DiagonalComplexActionResonanceFamily.toComplexAction
    (K : DiagonalComplexActionResonanceFamily) :
    ComplexActionDampedQEDModeFamily where
  dampingRate := K.dampingRate
  dampingRate_pos := K.dampingRate_pos
  phaseAction := K.phaseAction
  mode := K.basis
  mode_norm_le_one := fun n => by
    rw [K.basis.orthonormal.norm_eq_one]

/-- Forgetting the phase gives the Hermitian ED damping family on the same
orthonormal basis. -/
noncomputable def DiagonalComplexActionResonanceFamily.toHermitian
    (K : DiagonalComplexActionResonanceFamily) :
    EntropicDampedQEDModeFamily where
  dampingRate := K.dampingRate
  dampingRate_pos := K.dampingRate_pos
  phaseAction := K.phaseAction
  mode := K.basis
  mode_norm_le_one := fun n => by
    rw [K.basis.orthonormal.norm_eq_one]

/-- The self-adjoint entropy-damping companion of the resonance kernel. -/
noncomputable def DiagonalComplexActionResonanceFamily.hermitianOperator
    (K : DiagonalComplexActionResonanceFamily) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  K.toHermitian.operator

/-- The full phase-carrying non-Hermitian resonance kernel. -/
noncomputable def DiagonalComplexActionResonanceFamily.resonanceOperator
    (K : DiagonalComplexActionResonanceFamily) :
    BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 :=
  K.toComplexAction.operator

/-- The Hermitian damping companion acts diagonally on every basis mode. -/
lemma DiagonalComplexActionResonanceFamily.hermitianOperator_apply_basis
    (K : DiagonalComplexActionResonanceFamily) (n : ℕ) :
    K.hermitianOperator (K.basis n) =
      (K.toHermitian.coupling n : ℂ) • K.basis n := by
  change (∑' i, (K.toHermitian.coupling i : ℂ) •
      fourDimensionalSeparableKernel (K.basis i)) (K.basis n) = _
  calc
    _ = ∑' i, ((K.toHermitian.coupling i : ℂ) •
        fourDimensionalSeparableKernel (K.basis i)) (K.basis n) :=
      (ContinuousLinearMap.apply ℂ BetheSalpeterL2 (K.basis n)).map_tsum
        K.toHermitian.toAbsolutelySummable.summable_operator
    _ = _ := by
      rw [tsum_eq_single n]
      · rw [_root_.smul_apply,
          show fourDimensionalSeparableKernel (K.basis n) =
            InnerProductSpace.rankOne ℂ (K.basis n) (K.basis n) from rfl,
          InnerProductSpace.rankOne_apply,
          orthonormal_iff_ite.mp K.basis.orthonormal]
        simp
      · intro i hi
        rw [_root_.smul_apply,
          show fourDimensionalSeparableKernel (K.basis i) =
            InnerProductSpace.rankOne ℂ (K.basis i) (K.basis i) from rfl,
          InnerProductSpace.rankOne_apply,
          orthonormal_iff_ite.mp K.basis.orthonormal]
        simp [hi]

/-- The full complex resonance operator is diagonal in exactly the same
orthonormal basis as its self-adjoint damping companion. -/
lemma DiagonalComplexActionResonanceFamily.resonanceOperator_apply_basis
    (K : DiagonalComplexActionResonanceFamily) (n : ℕ) :
    K.resonanceOperator (K.basis n) =
      K.toComplexAction.coupling n • K.basis n := by
  change (∑' i, K.toComplexAction.coupling i •
      fourDimensionalSeparableKernel (K.basis i)) (K.basis n) = _
  calc
    _ = ∑' i, (K.toComplexAction.coupling i •
        fourDimensionalSeparableKernel (K.basis i)) (K.basis n) :=
      (ContinuousLinearMap.apply ℂ BetheSalpeterL2 (K.basis n)).map_tsum
        K.toComplexAction.summable_operator
    _ = _ := by
      rw [tsum_eq_single n]
      · rw [_root_.smul_apply,
          show fourDimensionalSeparableKernel (K.basis n) =
            InnerProductSpace.rankOne ℂ (K.basis n) (K.basis n) from rfl,
          InnerProductSpace.rankOne_apply,
          orthonormal_iff_ite.mp K.basis.orthonormal]
        simp
      · intro i hi
        rw [_root_.smul_apply,
          show fourDimensionalSeparableKernel (K.basis i) =
            InnerProductSpace.rankOne ℂ (K.basis i) (K.basis i) from rfl,
          InnerProductSpace.rankOne_apply,
          orthonormal_iff_ite.mp K.basis.orthonormal]
        simp [hi]

/-! ## B.6. Adjoint, normality, and the stable Hermitian sector -/

/-- Two bounded operators that agree on a Hilbert basis agree everywhere.
This local helper uses the already available complete basis expansion and
avoids introducing a separate algebraic Hamel basis. -/
lemma continuousLinearMap_eq_of_apply_hilbertBasis
    (b : HilbertBasis ℕ ℂ BetheSalpeterL2)
    (A B : BetheSalpeterL2 →L[ℂ] BetheSalpeterL2)
    (h : ∀ n, A (b n) = B (b n)) : A = B := by
  apply ContinuousLinearMap.ext
  intro x
  apply HasSum.unique ((b.hasSum_repr x).mapL A)
  convert (b.hasSum_repr x).mapL B using 1
  funext n
  simp only [map_smul]
  rw [h n]

/-- Reverse the real Nagao--Nielsen phase while retaining the same imaginary
action and the same complete four-dimensional mode basis.  This is the
spectral conjugate family; no new carrier or mode hypothesis is introduced. -/
noncomputable def DiagonalComplexActionResonanceFamily.phaseConjugate
    (K : DiagonalComplexActionResonanceFamily) :
    DiagonalComplexActionResonanceFamily where
  dampingRate := K.dampingRate
  dampingRate_pos := K.dampingRate_pos
  phaseAction := fun n => -K.phaseAction n
  basis := K.basis

/-- **Target 1: phase reversal is complex conjugation.**  Reversing the real
action conjugates the full Nagao--Nielsen mode weight while leaving its
entropic damping unchanged. -/
lemma DiagonalComplexActionResonanceFamily.phaseConjugate_coupling
    (K : DiagonalComplexActionResonanceFamily) (n : ℕ) :
    K.phaseConjugate.toComplexAction.coupling n =
      star (K.toComplexAction.coupling n) := by
  unfold DiagonalComplexActionResonanceFamily.phaseConjugate
    DiagonalComplexActionResonanceFamily.toComplexAction
    ComplexActionDampedQEDModeFamily.coupling
  exact show complexActionPathIntegralWeight (-K.phaseAction n)
      ((n : ℝ) * K.dampingRate) 1 =
      star (complexActionPathIntegralWeight (K.phaseAction n)
        ((n : ℝ) * K.dampingRate) 1) by
    unfold complexActionPathIntegralWeight
    let z : ℂ := Complex.I * (((K.phaseAction n / 1 : ℝ) : ℂ)) -
      ((((n : ℝ) * K.dampingRate / 1 : ℝ) : ℂ))
    calc
      Complex.exp (Complex.I * (((-K.phaseAction n / 1 : ℝ) : ℂ)) -
          ((((n : ℝ) * K.dampingRate / 1 : ℝ) : ℂ))) =
          Complex.exp (star z) := by
        congr 1
        dsimp [z]
        push_cast
        simp
      _ = star (Complex.exp z) := Complex.exp_conj z

/-- The adjoint of the diagonal resonance series is obtained termwise by
conjugating every mode coupling. -/
lemma DiagonalComplexActionResonanceFamily.adjoint_eq_tsum_conjugate
    (K : DiagonalComplexActionResonanceFamily) :
    K.resonanceOperator.adjoint =
      ∑' n, star (K.toComplexAction.coupling n) •
        fourDimensionalSeparableKernel (K.basis n) := by
  unfold DiagonalComplexActionResonanceFamily.resonanceOperator
    ComplexActionDampedQEDModeFamily.operator
  calc
    ContinuousLinearMap.adjoint
        (∑' n, K.toComplexAction.coupling n •
          fourDimensionalSeparableKernel (K.toComplexAction.mode n)) =
        ∑' n, ContinuousLinearMap.adjoint
          (K.toComplexAction.coupling n •
            fourDimensionalSeparableKernel (K.toComplexAction.mode n)) :=
      ContinuousLinearMap.adjoint.toContinuousLinearEquiv.map_tsum
    _ = _ := by
      apply tsum_congr
      intro n
      rw [map_smulₛₗ ContinuousLinearMap.adjoint]
      change star (K.toComplexAction.coupling n) •
          (InnerProductSpace.rankOne ℂ (K.basis n) (K.basis n)).adjoint = _
      rw [InnerProductSpace.adjoint_rankOne]
      rfl

/-- **Target 2: the phase-reversed operator is the Hilbert adjoint.**  The
statement is proved on the supplied complete orthonormal basis, so it
identifies the bounded operators globally rather than only comparing their
listed eigenvalues. -/
theorem DiagonalComplexActionResonanceFamily.phaseConjugate_operator_eq_adjoint
    (K : DiagonalComplexActionResonanceFamily) :
    K.phaseConjugate.resonanceOperator = K.resonanceOperator.adjoint := by
  rw [K.adjoint_eq_tsum_conjugate]
  unfold DiagonalComplexActionResonanceFamily.resonanceOperator
    ComplexActionDampedQEDModeFamily.operator
  apply tsum_congr
  intro n
  rw [K.phaseConjugate_coupling]
  rfl

/-- The adjoint resonance operator is diagonal in the same complete basis,
with the conjugate mode coupling. -/
lemma DiagonalComplexActionResonanceFamily.adjoint_apply_basis
    (K : DiagonalComplexActionResonanceFamily) (n : ℕ) :
    K.resonanceOperator.adjoint (K.basis n) =
      star (K.toComplexAction.coupling n) • K.basis n := by
  rw [← K.phaseConjugate_operator_eq_adjoint,
    show K.basis n = K.phaseConjugate.basis n from rfl,
    K.phaseConjugate.resonanceOperator_apply_basis,
    K.phaseConjugate_coupling]

/-- **Target 3: the full phase-carrying resonance operator is normal.**
Although it need not be self-adjoint, it commutes with its Hilbert adjoint
because both are diagonal on the same complete orthonormal basis.  This is
the infinite-dimensional bounded-operator analogue of the repository's
finite-dimensional `Q`-normal diagonal Hamiltonians. -/
theorem DiagonalComplexActionResonanceFamily.resonanceOperator_isStarNormal
    (K : DiagonalComplexActionResonanceFamily) :
    IsStarNormal K.resonanceOperator := by
  rw [isStarNormal_iff, Commute, SemiconjBy]
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply continuousLinearMap_eq_of_apply_hilbertBasis K.basis
  intro n
  change K.resonanceOperator.adjoint
      (K.resonanceOperator (K.basis n)) =
    K.resonanceOperator
      (K.resonanceOperator.adjoint (K.basis n))
  rw [K.resonanceOperator_apply_basis, map_smul,
    K.adjoint_apply_basis, map_smul,
    K.resonanceOperator_apply_basis, smul_smul, smul_smul]
  rw [mul_comm]

/-- Exact criterion for the normal resonance operator to enter the Hermitian
sector: every diagonal complex-action coupling must be fixed by complex
conjugation.  This separates ordinary normal resonance dynamics from the
stronger stable self-adjoint specialization. -/
theorem DiagonalComplexActionResonanceFamily.resonanceOperator_isSelfAdjoint_iff
    (K : DiagonalComplexActionResonanceFamily) :
    IsSelfAdjoint K.resonanceOperator ↔
      ∀ n, star (K.toComplexAction.coupling n) =
        K.toComplexAction.coupling n := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  constructor
  · intro hop n
    have happ := congrArg (fun A : BetheSalpeterL2 →L[ℂ] BetheSalpeterL2 =>
      A (K.basis n)) hop
    rw [K.adjoint_apply_basis, K.resonanceOperator_apply_basis] at happ
    exact smul_left_injective ℂ (K.basis.orthonormal.ne_zero n) happ
  · intro hc
    apply continuousLinearMap_eq_of_apply_hilbertBasis K.basis
    intro n
    rw [K.adjoint_apply_basis, K.resonanceOperator_apply_basis, hc n]

/-- At zero real action the full complex coupling reduces exactly to the
positive entropic-dynamics coupling on every mode. -/
lemma DiagonalComplexActionResonanceFamily.complex_coupling_eq_hermitian_of_phase_zero
    (K : DiagonalComplexActionResonanceFamily)
    (hphase : ∀ n, K.phaseAction n = 0) (n : ℕ) :
    K.toComplexAction.coupling n = (K.toHermitian.coupling n : ℂ) := by
  rw [K.toHermitian.coupling_eq_exp]
  change complexActionPathIntegralWeight (K.phaseAction n)
      ((n : ℝ) * K.dampingRate) 1 =
    ((Real.exp (-((n : ℝ) * K.dampingRate)) : ℝ) : ℂ)
  rw [hphase n]
  simp [complexActionPathIntegralWeight]

/-- **Stable-sector reduction.**  At zero real action the phase-carrying
resonance operator is exactly its self-adjoint ED damping companion. -/
theorem DiagonalComplexActionResonanceFamily.resonanceOperator_eq_hermitian_of_phase_zero
    (K : DiagonalComplexActionResonanceFamily)
    (hphase : ∀ n, K.phaseAction n = 0) :
    K.resonanceOperator = K.hermitianOperator := by
  apply continuousLinearMap_eq_of_apply_hilbertBasis K.basis
  intro n
  rw [K.resonanceOperator_apply_basis, K.hermitianOperator_apply_basis,
    K.complex_coupling_eq_hermitian_of_phase_zero hphase n]

/-- Consequently the zero-phase resonance kernel is self-adjoint, in
addition to compact and diagonal with a complete eigenbasis. -/
theorem DiagonalComplexActionResonanceFamily.resonanceOperator_isSelfAdjoint_of_phase_zero
    (K : DiagonalComplexActionResonanceFamily)
    (hphase : ∀ n, K.phaseAction n = 0) :
    IsSelfAdjoint K.resonanceOperator := by
  rw [K.resonanceOperator_eq_hermitian_of_phase_zero hphase]
  exact K.toHermitian.toAbsolutelySummable.approximation.isSymmetric.isSelfAdjoint

/-- **Target 1: a shared self-adjoint eigenbasis exists in the diagonal
resonance sector.**  The damping companion is compact and self-adjoint; every
basis vector is simultaneously its eigenvector and an eigenvector of the
full complex-action kernel. -/
theorem DiagonalComplexActionResonanceFamily.shared_selfAdjoint_eigenbasis
    (K : DiagonalComplexActionResonanceFamily) :
    (IsCompactOperator K.hermitianOperator ∧
      K.hermitianOperator.IsSymmetric)
      ∧ (∀ n, K.hermitianOperator (K.basis n) =
        (K.toHermitian.coupling n : ℂ) • K.basis n)
      ∧ (∀ n, K.resonanceOperator (K.basis n) =
        K.toComplexAction.coupling n • K.basis n) := by
  exact ⟨⟨K.toHermitian.toAbsolutelySummable.approximation.isCompact,
      K.toHermitian.toAbsolutelySummable.approximation.isSymmetric⟩,
    K.hermitianOperator_apply_basis,
    K.resonanceOperator_apply_basis⟩

/-- **Target 2: the resonance eigenvectors are complete.**  Completeness is
not inferred from non-Hermitian compactness; it follows from the stronger
physical specialization that the Cutkosky modes themselves form the supplied
Hilbert basis. -/
lemma DiagonalComplexActionResonanceFamily.resonance_eigenbasis_complete
    (K : DiagonalComplexActionResonanceFamily) (psi : BetheSalpeterL2) :
    HasSum (fun n => K.basis.repr psi n • K.basis n) psi :=
  K.basis.hasSum_repr psi

/-- **Target 3: Swift--Lee resonance dynamics with the shared eigenbasis.**
The same statement records the Wick convergence prescription, complex
oscillator spacing and width, Regge damping, and the complete basis that
diagonalizes both the self-adjoint damping operator and the complex resonance
operator. -/
theorem DiagonalComplexActionResonanceFamily.swiftLee_shared_eigenbasis_chain
    (K : DiagonalComplexActionResonanceFamily) (m omega J : ℂ)
    {hbar dt : ℝ} (hhbar : 0 < hbar) (hdt : 0 < dt) (hm : m ≠ 0)
    (n : ℕ) (psi : BetheSalpeterL2) :
    (0 < (momentumGaussianCoeff m hbar dt).re ↔ 0 < m.im)
      ∧ oscillatorEnergy hbar omega (n + 1) - oscillatorEnergy hbar omega n =
        (hbar : ℂ) * omega
      ∧ oscillatorEnergy hbar omega 0 = (hbar : ℂ) * omega / 2
      ∧ ((hbar : ℂ) * omega).im = hbar * omega.im
      ∧ (((hbar : ℂ) * omega).im = 0 ↔ omega.im = 0)
      ∧ ‖reggeSignature J‖ = Real.exp (-(Real.pi) * J.im)
      ∧ K.hermitianOperator (K.basis n) =
        (K.toHermitian.coupling n : ℂ) • K.basis n
      ∧ K.resonanceOperator (K.basis n) =
        K.toComplexAction.coupling n • K.basis n
      ∧ HasSum (fun i => K.basis.repr psi i • K.basis i) psi := by
  exact ⟨bsKernel_converges_iff m hhbar hdt hm,
    boundState_level_spacing hbar omega n,
    boundState_ground hbar omega,
    boundState_spacing_im hbar omega,
    boundState_spacing_real_iff hbar omega (ne_of_gt hhbar),
    (boundState_resonance_regge_link hbar omega J).2,
    K.hermitianOperator_apply_basis n,
    K.resonanceOperator_apply_basis n,
    K.resonance_eigenbasis_complete psi⟩

/-- Every Bethe--Salpeter wavefunction has a convergent expansion in the
explicit transported four-dimensional tensor-Hermite basis. -/
lemma betheSalpeterHermite_expansion (psi : BetheSalpeterL2) :
    HasSum (fun n => betheSalpeterHermiteHilbertBasis.repr psi n •
      betheSalpeterCarrierEquiv (euclideanHermiteL2Mode4 n)) psi := by
  simpa using betheSalpeterHermiteHilbertBasis.hasSum_repr psi

/-- **Concrete resonance-sector closure.**  The canonical Hermite family is
normal, its entropy-damping companion is compact and self-adjoint, its modes
are the transported tensor-Hermite functions, and those modes give a complete
expansion.  No supplied eigenbasis hypothesis remains in this specialization. -/
theorem hermiteDiagonalResonance_complete_normal_chain
    (dampingRate : ℝ) (hdamping : 0 < dampingRate)
    (phaseAction : ℕ → ℝ) (psi : BetheSalpeterL2) :
    let K := hermiteDiagonalResonanceFamily dampingRate hdamping phaseAction
    IsStarNormal K.resonanceOperator
      ∧ (IsCompactOperator K.hermitianOperator ∧
        K.hermitianOperator.IsSymmetric)
      ∧ (∀ n, K.basis n =
        betheSalpeterCarrierEquiv (euclideanHermiteL2Mode4 n))
      ∧ HasSum (fun n => K.basis.repr psi n • K.basis n) psi := by
  let K := hermiteDiagonalResonanceFamily dampingRate hdamping phaseAction
  exact ⟨K.resonanceOperator_isStarNormal,
    K.shared_selfAdjoint_eigenbasis.1,
    fun n => by simp [hermiteDiagonalResonanceFamily],
    K.resonance_eigenbasis_complete psi⟩

/-- With vanishing real action, the explicit Hermite resonance family is a
genuine self-adjoint bound-state operator. -/
theorem hermiteDiagonalResonance_zeroPhase_isSelfAdjoint
    (dampingRate : ℝ) (hdamping : 0 < dampingRate) :
    IsSelfAdjoint
      (hermiteDiagonalResonanceFamily dampingRate hdamping
        (fun _ => 0)).resonanceOperator := by
  apply DiagonalComplexActionResonanceFamily.resonanceOperator_isSelfAdjoint_of_phase_zero
  intro n
  rfl

/-! ## C. Bound-state completeness -/

/-- **General four-dimensional compact-kernel completeness criterion.**  Any
compact symmetric Bethe--Salpeter operator on the actual `L²(ℝ⁴)` carrier has
a complete family of eigenspaces.  A later interacting kernel can therefore
reuse this theorem directly once its analytical compactness and symmetry have
been proved. -/
theorem fourDimensional_boundState_complete_of_compact_symmetric
    (K : BetheSalpeterL2 →L[ℂ] BetheSalpeterL2)
    (hK : IsCompactOperator K) (hKsymm : K.IsSymmetric) :
    (⨆ lambda, Module.End.eigenspace K.toLinearMap lambda)ᗮ = ⊥ := by
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hK hKsymm

/-- **Bound-state completeness on `L²(ℝ⁴)`.**  The closed span of all
eigenspaces of the compact self-adjoint four-dimensional ladder kernel is
the entire Hilbert space, expressed equivalently by the vanishing of its
orthogonal complement.  This is the infinite-dimensional compact spectral
theorem, not a discretization or a caller-supplied completeness certificate. -/
theorem fourDimensional_boundState_complete (u : BetheSalpeterL2) :
    (⨆ lambda, Module.End.eigenspace
      ((fourDimensionalSeparableKernel u).toLinearMap) lambda)ᗮ = ⊥ := by
  exact fourDimensional_boundState_complete_of_compact_symmetric
    (fourDimensionalSeparableKernel u)
    (fourDimensionalSeparableKernel_isCompact u)
    (fourDimensionalSeparableKernel_isSymmetric u)

/-- Every nonzero-coupling bound-state eigenspace of the four-dimensional
compact ladder kernel has finite multiplicity. -/
theorem fourDimensional_nonzero_boundState_finiteMultiplicity
    (u : BetheSalpeterL2) (lambda : ℂ) (hlambda : lambda ≠ 0) :
    FiniteDimensional ℂ
      (Module.End.eigenspace (fourDimensionalSeparableKernel u).toLinearMap lambda) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    (fourDimensionalSeparableKernel_isCompact u) lambda hlambda

/-- **Target 3: interacting four-dimensional bound-state completeness.**
Every interacting kernel supplied by an operator-norm convergent Hermitian
Schmidt expansion has eigenspaces with trivial joint orthogonal complement. -/
theorem InteractingQEDKernelApproximation.boundState_complete
    (K : InteractingQEDKernelApproximation) :
    (⨆ lambda, Module.End.eigenspace K.operator.toLinearMap lambda)ᗮ = ⊥ := by
  exact fourDimensional_boundState_complete_of_compact_symmetric
    K.operator K.isCompact K.isSymmetric

/-- Every nonzero interacting bound-state eigenspace has finite
multiplicity. -/
theorem InteractingQEDKernelApproximation.nonzero_finiteMultiplicity
    (K : InteractingQEDKernelApproximation) (lambda : ℂ)
    (hlambda : lambda ≠ 0) :
    FiniteDimensional ℂ
      (Module.End.eigenspace K.operator.toLinearMap lambda) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    K.isCompact lambda hlambda

/-- An absolutely summable interacting Hermitian QED mode expansion is
compact, with no separate compactness or convergence certificate required. -/
theorem AbsolutelySummableHermitianQEDKernel.isCompact
    (K : AbsolutelySummableHermitianQEDKernel) :
    IsCompactOperator K.operator :=
  K.approximation.isCompact

/-- An absolutely summable real-weighted mode expansion is symmetric. -/
theorem AbsolutelySummableHermitianQEDKernel.isSymmetric
    (K : AbsolutelySummableHermitianQEDKernel) :
    K.operator.IsSymmetric :=
  K.approximation.isSymmetric

/-- The infinite absolutely summable interacting kernel has a complete
four-dimensional bound-state eigenspace decomposition. -/
theorem AbsolutelySummableHermitianQEDKernel.boundState_complete
    (K : AbsolutelySummableHermitianQEDKernel) :
    (⨆ lambda, Module.End.eigenspace K.operator.toLinearMap lambda)ᗮ = ⊥ :=
  K.approximation.boundState_complete

/-- Every nonzero eigenspace of the infinite absolutely summable interacting
kernel has finite multiplicity. -/
theorem AbsolutelySummableHermitianQEDKernel.nonzero_finiteMultiplicity
    (K : AbsolutelySummableHermitianQEDKernel) (lambda : ℂ)
    (hlambda : lambda ≠ 0) :
    FiniteDimensional ℂ
      (Module.End.eigenspace K.operator.toLinearMap lambda) :=
  K.approximation.nonzero_finiteMultiplicity lambda hlambda

/-- **Interacting Fredholm target.**  Away from a nonzero eigenvalue, the
full norm-convergent interacting kernel has a unique Bethe--Salpeter
coefficient for every source.  This reuses the repository's Bassetto
Fredholm theorem and discharges its compactness premise analytically. -/
theorem AbsolutelySummableHermitianQEDKernel.uniqueCoefficient_of_not_eigenvalue
    (K : AbsolutelySummableHermitianQEDKernel) (lambda : ℂ)
    (hlambda : lambda ≠ 0)
    (hnotEigen : ¬ Module.End.HasEigenvalue K.operator.toLinearMap lambda) :
    ∀ source : BetheSalpeterL2, ∃! coefficient : BetheSalpeterL2,
      (lambda • (1 : BetheSalpeterL2 →L[ℂ] BetheSalpeterL2) - K.operator)
        coefficient = source :=
  bassetto_uniqueCoefficient_of_compact_of_not_eigenvalue
    K.operator lambda K.isCompact hlambda hnotEigen

/-- **Target 2b: entropic QED compactness and symmetry.**  The positive
imaginary-action gap constructs a compact symmetric interacting kernel; no
compactness, symmetry, or operator-convergence certificate is supplied by
the caller. -/
theorem EntropicDampedQEDModeFamily.compact_and_symmetric
    (K : EntropicDampedQEDModeFamily) :
    IsCompactOperator K.operator ∧ K.operator.IsSymmetric :=
  ⟨K.toAbsolutelySummable.isCompact,
    K.toAbsolutelySummable.isSymmetric⟩

/-- **Target 3a: entropic/complex-action bound-state completeness.**  The
strict entropy damping that makes the mode sum convergent gives a complete
family of four-dimensional Bethe--Salpeter eigenspaces. -/
theorem EntropicDampedQEDModeFamily.boundState_complete
    (K : EntropicDampedQEDModeFamily) :
    (⨆ lambda, Module.End.eigenspace K.operator.toLinearMap lambda)ᗮ = ⊥ :=
  K.toAbsolutelySummable.boundState_complete

/-- Every nonzero entropically damped bound-state eigenspace has finite
multiplicity. -/
theorem EntropicDampedQEDModeFamily.nonzero_finiteMultiplicity
    (K : EntropicDampedQEDModeFamily) (lambda : ℂ)
    (hlambda : lambda ≠ 0) :
    FiniteDimensional ℂ
      (Module.End.eigenspace K.operator.toLinearMap lambda) :=
  K.toAbsolutelySummable.nonzero_finiteMultiplicity lambda hlambda

/-- **Target 3b: entropic Bassetto/Fredholm solvability.**  Away from a
nonzero bound-state pole, the ED--Nagao--Nielsen damped interacting kernel
has a unique coefficient for every source. -/
theorem EntropicDampedQEDModeFamily.uniqueCoefficient_of_not_eigenvalue
    (K : EntropicDampedQEDModeFamily) (lambda : ℂ)
    (hlambda : lambda ≠ 0)
    (hnotEigen : ¬ Module.End.HasEigenvalue K.operator.toLinearMap lambda) :
    ∀ source : BetheSalpeterL2, ∃! coefficient : BetheSalpeterL2,
      (lambda • (1 : BetheSalpeterL2 →L[ℂ] BetheSalpeterL2) - K.operator)
        coefficient = source :=
  K.toAbsolutelySummable.uniqueCoefficient_of_not_eigenvalue
    lambda hlambda hnotEigen

/-- One theorem composing the physical and analytical chain: each mode
weight is simultaneously ED probability, NN modulus and entropy damping;
that damping constructs a complete interacting bound-state spectrum with
finite nonzero multiplicities. -/
theorem EntropicDampedQEDModeFamily.ed_nagaoNielsen_complete_chain
    (K : EntropicDampedQEDModeFamily) (n : ℕ) (lambda : ℂ)
    (hlambda : lambda ≠ 0) :
    (K.coupling n =
        ‖complexActionPathIntegralWeight (K.phaseAction n)
          ((Real.sqrt ((n : ℝ) * K.dampingRate) - 0) ^ 2) (2 / 2)‖
      ∧ K.coupling n =
        entropyDamping
          ((Real.sqrt ((n : ℝ) * K.dampingRate) - 0) ^ 2) (2 / 2)
      ∧ edWaveFunction 1 (K.phaseAction n) =
        Complex.exp (((K.phaseAction n : ℝ) : ℂ) * Complex.I))
      ∧ (⨆ mu, Module.End.eigenspace K.operator.toLinearMap mu)ᗮ = ⊥
      ∧ FiniteDimensional ℂ
        (Module.End.eigenspace K.operator.toLinearMap lambda) := by
  exact ⟨K.coupling_is_ed_nagaoNielsen n,
    K.boundState_complete,
    K.nonzero_finiteMultiplicity lambda hlambda⟩

/-- Hilbert-basis expansion for the four-dimensional carrier.  When a
spectral basis is chosen inside the eigenspaces supplied by the preceding
theorem, this is the convergent bound-state mode expansion. -/
lemma fourDimensional_boundState_expansion
    {iota : Type*} (b : HilbertBasis iota ℂ BetheSalpeterL2)
    (psi : BetheSalpeterL2) :
    HasSum (fun i => b.repr psi i • b i) psi :=
  b.hasSum_repr psi

/-- Parseval identity for the complete four-dimensional mode expansion. -/
lemma fourDimensional_boundState_parseval
    {iota : Type*} (b : HilbertBasis iota ℂ BetheSalpeterL2)
    (psi : BetheSalpeterL2) :
    ∑' i, ⟪psi, b i⟫_ℂ * ⟪b i, psi⟫_ℂ = ⟪psi, psi⟫_ℂ :=
  b.tsum_inner_mul_inner psi psi

/-! ## D. Lusanna tetrad/frame covariance -/

/-- The tetrad-metric quadratic form of a relative four-momentum,
`qᵀ g[E] q`, with `g[E] = Eᵀ eta E`. -/
def tetradRelativeMomentumSq
    (E : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (q : RelativeMomentum4) : ℝ :=
  ∑ i, ∑ j, q i * tetradMetric E i j * q j

/-- Local Lorentz changes of the Lusanna tetrad do not change the
relative-momentum quadratic form.  Consequently the four-dimensional
spectral carrier is not tied to a chosen tetrad representative. -/
lemma tetradRelativeMomentumSq_lorentz_gauge
    {Lambda E : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ}
    (hLambda : Lambda ∈ LorentzGroup 3) (q : RelativeMomentum4) :
    tetradRelativeMomentumSq (Lambda * E) q = tetradRelativeMomentumSq E q := by
  simp only [tetradRelativeMomentumSq,
    tetradMetric_lorentz_gauge hLambda]

/-! ## E. Reuse of the Swift--Lee/Nagao--Nielsen dynamics -/

/-- The analytical four-dimensional completeness result and the previously
proved Swift--Lee dynamics form one reusable statement: spectral completeness
of the compact symmetric `L²(ℝ⁴)` kernel, relative-energy convergence exactly
under the positive-imaginary-mass prescription, complex-oscillator level
spacing, and the imaginary-frequency resonance width. -/
theorem fourDimensional_complete_swiftLee_chain
    (u : BetheSalpeterL2) (m omega : ℂ) {hbar dt : ℝ}
    (hhbar : 0 < hbar) (hdt : 0 < dt) (hm : m ≠ 0) (n : ℕ) :
    (⨆ lambda, Module.End.eigenspace
      (fourDimensionalSeparableKernel u).toLinearMap lambda)ᗮ = ⊥
      ∧ (0 < (momentumGaussianCoeff m hbar dt).re ↔ 0 < m.im)
      ∧ oscillatorEnergy hbar omega (n + 1) - oscillatorEnergy hbar omega n =
        (hbar : ℂ) * omega
      ∧ ((hbar : ℂ) * omega).im = hbar * omega.im := by
  exact ⟨fourDimensional_boundState_complete u,
    swiftLee_betheSalpeter_oscillator m omega hhbar hdt hm n⟩

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach relativeMomentum_volume_eq_innerProductVolume where
  formalizes @ "claim:lorentz-vector-coordinate-haar-measure-equals-positive-hilbert-volume",
  supported_by @ "lean:Lorentz.Vector.basis_inner",
  supported_by @ "theorem:orthonormal-basis-add-haar-equals-volume",
  caveat @ "claim:positive-l2-carrier-volume-identity-not-an-identification-of-euclidean-and-minkowski-quadratic-forms"

zil attach relativeMomentumEuclideanEquiv_measurePreserving where
  formalizes @ "claim:bethe-salpeter-relative-four-momentum-coordinates-preserve-lebesgue-volume",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.relativeMomentum_volume_eq_innerProductVolume",
  supported_by @ "theorem:finite-dimensional-linear-isometries-preserve-volume",
  caveat @ "claim:coordinate-transport-result-not-a-dynamical-wick-rotation"

zil attach euclideanHermiteL2Mode4_orthonormal where
  formalizes @ "claim:four-dimensional-tensor-hermite-modes-are-orthonormal-in-complex-l2",
  supported_by @ "lean:GaussianField.hermiteFunctionNd_orthonormal",
  supported_by @ "lean:SchwartzMap.coeFn_toLp",
  caveat @ "claim:exact-analysis-identity-for-the-canonical-positive-l2-carrier"

zil attach euclideanHermiteL2Mode4_dense_span where
  formalizes @ "claim:four-dimensional-tensor-hermite-modes-have-dense-complex-l2-span",
  supported_by @ "lean:GaussianField.schwartz_hermite_completeness_nd",
  supported_by @ "lean:SchwartzMap.denseRange_toLpCLM",
  caveat @ "claim:hilbert-space-completeness-does-not-by-itself-solve-an-arbitrary-interacting-qed-kernel"

zil attach betheSalpeterHermite_expansion where
  formalizes @ "claim:every-four-dimensional-bethe-salpeter-l2-state-has-a-transported-hermite-expansion",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.euclideanHermiteL2Mode4_dense_span",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.relativeMomentumEuclideanEquiv_measurePreserving",
  supported_by @ "lean:HilbertBasis.hasSum_repr",
  caveat @ "claim:complete-carrier-expansion-not-a-claim-that-an-arbitrary-kernel-is-diagonal-in-this-basis"

zil attach hermiteDiagonalResonance_complete_normal_chain where
  formalizes @ "claim:explicit-four-dimensional-hermite-complex-action-resonance-family-is-complete-and-normal",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.betheSalpeterHermite_expansion",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.resonanceOperator_isStarNormal",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.shared_selfAdjoint_eigenbasis",
  requires @ "claim:strictly-positive-linear-mode-damping-gap",
  caveat @ "claim:canonical-diagonal-oscillator-sector-not-a-diagonalization-theorem-for-arbitrary-interacting-qed-kernels"

zil attach hermiteDiagonalResonance_zeroPhase_isSelfAdjoint where
  formalizes @ "claim:explicit-four-dimensional-hermite-resonance-operator-is-self-adjoint-at-zero-real-action",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.hermiteDiagonalResonance_complete_normal_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.resonanceOperator_isSelfAdjoint_of_phase_zero",
  requires @ "claim:real-complex-action-phase-vanishes-modewise",
  caveat @ "claim:stable-zero-phase-sector-not-a-claim-that-physical-resonances-have-zero-width"

zil attach constituentMomentumPlus_add_minus where
  formalizes @ "claim:bethe-salpeter-symmetric-routing-reconstructs-total-four-momentum",
  supported_by @ "paper:salpeter-bethe-1951",
  caveat @ "claim:exact-kinematic-identity-not-a-dynamical-bound-state-prediction"

zil attach fourDimensionalSeparableKernel_apply where
  formalizes @ "claim:cutkosky-separable-ladder-kernel-is-an-actual-l2-r4-integral-operator",
  supported_by @ "paper:cutkosky-1954",
  requires @ "claim:l2-four-momentum-kernel-factor",
  caveat @ "claim:symmetric-separable-ladder-sector-not-an-arbitrary-interacting-qed-kernel"

zil attach fourDimensional_boundState_complete where
  formalizes @ "claim:four-dimensional-separable-bethe-salpeter-bound-states-are-complete",
  supported_by @ "theorem:compact-self-adjoint-spectral-theorem",
  supported_by @ "paper:cutkosky-1954",
  caveat @ "claim:spectral-completeness-includes-the-zero-eigenspace-and-is-for-the-proved-separable-kernel"

zil attach fourDimensional_boundState_complete_of_compact_symmetric where
  formalizes @ "claim:any-compact-symmetric-four-dimensional-bethe-salpeter-operator-has-complete-eigenspaces",
  supported_by @ "theorem:compact-self-adjoint-spectral-theorem",
  requires @ "claim:kernel-compactness-and-symmetry-must-be-proved",
  caveat @ "claim:criterion-does-not-assert-those-hypotheses-for-an-arbitrary-qed-kernel"

zil attach InteractingQEDKernelApproximation.isCompact where
  formalizes @ "claim:operator-norm-schmidt-limit-gives-compact-four-dimensional-interacting-qed-kernel",
  supported_by @ "theorem:compact-operators-are-operator-norm-closed",
  requires @ "claim:operator-norm-convergence-of-finite-hermitian-schmidt-truncations",
  caveat @ "claim:not-every-formal-kernel-is-compact-the-convergence-hypothesis-is-analytic"

zil attach InteractingQEDKernelApproximation.isSymmetric where
  formalizes @ "claim:hermitian-schmidt-truncations-give-symmetric-interacting-qed-kernel",
  supported_by @ "theorem:inner-product-continuity-under-operator-norm-limits",
  requires @ "claim:real-couplings-and-diagonal-schmidt-modes",
  caveat @ "claim:does-not-cover-non-hermitian-resonance-kernels"

zil attach InteractingQEDKernelApproximation.boundState_complete where
  formalizes @ "claim:compact-hermitian-interacting-qed-kernel-has-complete-four-dimensional-eigenspaces",
  supported_by @ "theorem:compact-self-adjoint-spectral-theorem",
  requires @ "claim:operator-norm-hermitian-schmidt-approximation",
  caveat @ "claim:spectral-completeness-includes-the-zero-eigenspace"

zil attach AbsolutelySummableHermitianQEDKernel.summable_operator where
  formalizes @ "claim:absolute-mode-strength-summability-implies-operator-norm-qed-kernel-summability",
  supported_by @ "theorem:absolute-convergence-in-banach-spaces",
  supported_by @ "lean:InnerProductSpace.norm_rankOne",
  requires @ "claim:sum-absolute-coupling-times-mode-norm-squared-is-finite",
  caveat @ "claim:sufficient-nuclear-mode-criterion-stronger-than-abstract-compactness"

zil attach AbsolutelySummableHermitianQEDKernel.isCompact where
  formalizes @ "claim:absolute-hermitian-mode-expansion-gives-compact-interacting-qed-kernel",
  supported_by @ "theorem:compact-operators-are-operator-norm-closed",
  requires @ "claim:absolute-four-dimensional-mode-strength-summability",
  caveat @ "claim:concrete-photon-exchange-kernel-must-prove-the-summability-bound"

zil attach AbsolutelySummableHermitianQEDKernel.boundState_complete where
  formalizes @ "claim:absolute-hermitian-qed-mode-expansion-has-complete-bound-state-eigenspaces",
  supported_by @ "theorem:compact-self-adjoint-spectral-theorem",
  requires @ "claim:absolute-four-dimensional-mode-strength-summability",
  caveat @ "claim:self-adjoint-bound-state-sector-not-non-hermitian-resonance-completeness"

zil attach AbsolutelySummableHermitianQEDKernel.uniqueCoefficient_of_not_eigenvalue where
  formalizes @ "claim:interacting-bassetto-coefficient-equation-is-uniquely-solvable-off-spectrum",
  supported_by @ "theorem:fredholm-alternative-for-compact-operators",
  requires @ "claim:nonzero-parameter-is-not-an-eigenvalue",
  caveat @ "claim:solvability-off-spectrum-does-not-locate-the-physical-bound-state-poles"

zil attach EntropicDampedQEDModeFamily.coupling_is_ed_nagaoNielsen where
  formalizes @ "claim:each-interacting-qed-mode-weight-is-ed-probability-nn-modulus-and-entropy-damping",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen.ed_is_nagaoNielsen_complexAction",
  supported_by @ "theorem:master-modulus-is-kuiken-entropy-damping",
  requires @ "claim:mode-imaginary-action-is-linear-ladder-n-times-positive-gap",
  caveat @ "claim:identification-is-exact-after-the-stated-mode-action-model-is-chosen"

zil attach EntropicDampedQEDModeFamily.summable_weighted_norm where
  formalizes @ "claim:positive-ed-imaginary-action-gap-makes-the-interacting-qed-mode-kernel-summable",
  supported_by @ "theorem:summability-of-negative-exponential-geometric-series",
  requires @ "claim:strictly-positive-imaginary-action-gap",
  requires @ "claim:four-dimensional-mode-norms-are-bounded-by-one",
  caveat @ "claim:physical-renormalized-qed-modes-must-establish-these-two-analytic-bounds"

zil attach EntropicDampedQEDModeFamily.compact_and_symmetric where
  formalizes @ "claim:ed-nagao-nielsen-entropy-damping-constructs-compact-symmetric-qed-kernel",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.EntropicDampedQEDModeFamily.summable_weighted_norm",
  supported_by @ "theorem:operator-norm-limit-of-finite-hermitian-cutkosky-kernels",
  caveat @ "claim:self-adjoint-entropically-damped-sector-not-an-arbitrary-non-hermitian-resonance-kernel"

zil attach EntropicDampedQEDModeFamily.ed_nagaoNielsen_complete_chain where
  formalizes @ "claim:ed-complex-action-mode-damping-implies-complete-four-dimensional-qed-bound-state-spectrum",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen.ed_is_nagaoNielsen_complexAction",
  supported_by @ "theorem:compact-self-adjoint-spectral-theorem",
  requires @ "claim:positive-action-gap-and-uniform-mode-bound",
  caveat @ "claim:completeness-is-for-the-constructed-hermitian-mode-kernel-and-includes-zero-eigenspace"

zil attach EntropicDampedQEDModeFamily.uniqueCoefficient_of_not_eigenvalue where
  formalizes @ "claim:ed-complex-action-damped-qed-kernel-has-unique-bassetto-coefficients-off-spectrum",
  supported_by @ "theorem:fredholm-alternative-for-compact-operators",
  requires @ "claim:nonzero-parameter-is-not-an-eigenvalue",
  caveat @ "claim:theorem-does-not-predict-the-location-of-bound-state-poles"

zil attach ComplexActionDampedQEDModeFamily.norm_coupling_eq_edTransitionWeight where
  formalizes @ "claim:full-nagao-nielsen-qed-mode-coupling-has-exactly-the-caticha-ed-transition-modulus",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.EntropicDampedQEDModeFamily.coupling_eq_exp",
  requires @ "claim:mode-imaginary-action-is-n-times-a-positive-gap",
  caveat @ "claim:exact-weight-identity-after-the-linear-mode-action-model-is-chosen"

zil attach ComplexActionDampedQEDModeFamily.isCompact where
  formalizes @ "claim:full-phase-times-entropy-damping-constructs-a-compact-non-hermitian-four-dimensional-qed-kernel",
  supported_by @ "theorem:absolute-convergence-in-banach-spaces",
  supported_by @ "theorem:compact-operators-are-operator-norm-closed",
  requires @ "claim:positive-imaginary-action-gap-and-uniform-l2-mode-bound",
  caveat @ "claim:compactness-does-not-imply-a-complete-non-hermitian-eigenbasis"

zil attach ComplexActionDampedQEDModeFamily.uniqueCoefficient_of_not_eigenvalue where
  formalizes @ "claim:complex-action-resonance-kernel-has-unique-bassetto-coefficients-off-spectrum",
  supported_by @ "theorem:fredholm-alternative-for-compact-operators",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.ComplexActionDampedQEDModeFamily.isCompact",
  requires @ "claim:nonzero-parameter-is-not-a-resonance-eigenvalue",
  caveat @ "claim:off-spectrum-solvability-and-finite-multiplicity-do-not-locate-resonance-poles"

zil attach DiagonalComplexActionResonanceFamily.phaseConjugate_operator_eq_adjoint where
  formalizes @ "claim:reversing-real-complex-action-phase-constructs-the-hilbert-adjoint-resonance-kernel",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.phaseConjugate_coupling",
  supported_by @ "lean:InnerProductSpace.adjoint_rankOne",
  requires @ "claim:diagonal-complete-orthonormal-four-dimensional-mode-family",
  caveat @ "claim:operator-adjoint-identity-is-for-the-diagonal-resonance-sector-not-an-arbitrary-qed-kernel"

zil attach DiagonalComplexActionResonanceFamily.resonanceOperator_isStarNormal where
  formalizes @ "claim:full-infinite-dimensional-complex-action-resonance-operator-is-normal",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.phaseConjugate_operator_eq_adjoint",
  supported_by @ "lean:HilbertBasis.hasSum_repr",
  requires @ "claim:resonance-kernel-is-diagonal-in-a-supplied-complete-orthonormal-mode-family",
  caveat @ "claim:normality-is-not-self-adjointness-and-does-not-remove-resonance-widths"

zil attach DiagonalComplexActionResonanceFamily.resonanceOperator_isSelfAdjoint_iff where
  formalizes @ "claim:diagonal-resonance-kernel-is-self-adjoint-exactly-when-all-mode-couplings-are-real",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.adjoint_apply_basis",
  requires @ "claim:complete-diagonal-mode-family",
  caveat @ "claim:criterion-does-not-assert-that-general-nagao-nielsen-phases-are-real"

zil attach DiagonalComplexActionResonanceFamily.resonanceOperator_eq_hermitian_of_phase_zero where
  formalizes @ "claim:zero-real-action-reduces-the-complex-resonance-kernel-to-the-self-adjoint-ed-damping-kernel",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.DiagonalComplexActionResonanceFamily.complex_coupling_eq_hermitian_of_phase_zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness.EntropicDampedQEDModeFamily.coupling_eq_exp",
  requires @ "claim:real-action-phase-vanishes-on-every-mode",
  caveat @ "claim:stable-zero-phase-specialization-not-a-claim-that-physical-resonances-have-zero-width"

zil attach DiagonalComplexActionResonanceFamily.shared_selfAdjoint_eigenbasis where
  formalizes @ "claim:diagonal-complex-action-resonance-sector-has-a-shared-self-adjoint-companion-eigenbasis",
  supported_by @ "lean:InnerProductSpace.rankOne_apply",
  supported_by @ "theorem:compact-self-adjoint-spectral-theory",
  requires @ "claim:four-dimensional-cutkosky-modes-form-a-supplied-orthonormal-hilbert-basis",
  caveat @ "claim:the-damping-companion-is-self-adjoint-the-full-complex-resonance-operator-generally-is-not"

zil attach DiagonalComplexActionResonanceFamily.resonance_eigenbasis_complete where
  formalizes @ "claim:diagonal-four-dimensional-resonance-eigenvectors-expand-every-l2-state",
  supported_by @ "lean:HilbertBasis.hasSum_repr",
  requires @ "claim:resonance-kernel-is-diagonal-in-the-supplied-hilbert-basis",
  caveat @ "claim:completeness-comes-from-the-diagonal-hilbert-basis-hypothesis-not-from-non-hermitian-compactness"

zil attach DiagonalComplexActionResonanceFamily.swiftLee_shared_eigenbasis_chain where
  formalizes @ "claim:swift-lee-wick-oscillator-regge-resonance-chain-shares-a-complete-four-dimensional-mode-basis",
  supported_by @ "paper:swift-lee-1963",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeBetheSalpeterOscillator.boundState_resonance_regge_link",
  supported_by @ "lean:HilbertBasis.hasSum_repr",
  requires @ "claim:complex-oscillator-identification-and-diagonal-orthonormal-cutkosky-mode-sector",
  caveat @ "claim:model-specialization-not-a-bound-state-completeness-theorem-for-arbitrary-interacting-qed-kernels"

zil attach fourDimensional_complete_swiftLee_chain where
  formalizes @ "claim:four-dimensional-spectral-completeness-links-to-swift-lee-nagao-nielsen-dynamics",
  supported_by @ "paper:swift-lee-1963",
  supported_by @ "paper:nagao-nielsen-complex-action",
  requires @ "claim:compact-symmetric-separable-ladder-sector",
  caveat @ "claim:oscillator-spectrum-is-a-model-identification-not-derived-from-the-general-dirac-kernel"

zil attach tetradRelativeMomentumSq_lorentz_gauge where
  formalizes @ "claim:bethe-salpeter-relative-four-momentum-form-is-lusanna-tetrad-gauge-independent",
  supported_by @ "paper:lusanna-canonical-adm-tetrad-gravity",
  caveat @ "claim:local-lorentz-frame-invariance-not-a-curved-space-bethe-salpeter-existence-theorem"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness

end

end

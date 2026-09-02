/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Curvature
meta import Zil

/-!
# The Caticha–Hadamard–AQFT–global-Maxwell microcausality capstone

One conditional theorem at the critical boundary where four independent arcs meet on their shared
carrier — the **Pauli–Jordan causal structure**:

* **(I) Caticha** — the entropic-dynamics functional Hamiltonian preserves the causal Klein–Gordon
  solution space: applying the smeared Schrödinger generator to a retarded-minus-advanced field
  again yields a homogeneous KG field (`caticha_causalPropagator_is_homogeneous`).
* **(II) Hadamard / AQFT observable** — every Hermitian two-point kernel splits as its Hadamard
  (real, symmetric) part plus `i/2` times its Pauli–Jordan (antisymmetric) part, and the
  **observable commutator** recovers exactly the Pauli–Jordan function:
  `W(x,y) − W(y,x) = iΔ(x,y)` — the kernel-level microcausality structure (Sorkin–Johnston
  decomposition, Peierls bracket).
* **(III) global Maxwell** — the intrinsic Maxwell causal propagator (retarded minus advanced
  Green operator on the manifold) is a **global homogeneous solution** of the Ricci-coupled
  Maxwell wave equation (`causalPropagator_solves_homogeneous`).
* **(IV) atlas independence** — that microcausal solution satisfies the same intrinsic equation
  for **every representative of the Levi-Civita atlas**: the Pauli–Jordan solution property is a
  chart-independent, geometric fact (`intrinsicRicciCoupledMaxwellOn_atlas_iff`, applied — not
  merely conjoined — to transport leg III from one atlas representative to another).

The four legs are *conditional* on their respective data (a `ContinuumCatichaKGData`, a Hermitian
kernel, an `IntrinsicMaxwellGreenData` with a Levi-Civita atlas and the differentiability side
conditions); the capstone asserts their conjunction on the common causal-propagator carrier. Leg
IV is the only genuinely *new* consequence assembled here: microcausality of the global Maxwell
field is atlas-independent, obtained by feeding III through the atlas-iff.

What is **not** claimed: Green-hyperbolicity or existence of the Green operators (they are data),
spacelike-support properties of `Δ` (the kernels here are abstract), or any derivation of one leg
from another — the shared carrier is structural, the legs remain independent inputs.

## References

* R. M. Wald, *QFT in curved spacetime*; Hadamard states and the Pauli–Jordan function.
* R. D. Sorkin, S. Johnston — the SJ two-point decomposition. A. Caticha — entropic dynamics.
* Repo carriers: `KleinGordonProgram.ContinuumCatichaKGData`,
  `SorkinJohnstonHermitianDecomposition.hadamardPart/pauliJordanPart`,
  `SorkinJohnstonRegionState.wightmanTwoPoint/wightman_commutator`,
  `PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator`,
  `PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle FiberBundle Module
open scoped Manifold
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open PseudoRiemannianMetric
open PseudoRiemannianMetric.IntrinsicMaxwellGreenData

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaHadamardMaxwellMicrocausality

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

/-- **[The Caticha–Hadamard–AQFT–global-Maxwell microcausality capstone]** — the four arcs meet on
the Pauli–Jordan causal carrier. Conditional on a Caticha continuum KG datum `D`, a Hermitian
two-point kernel `W`, and intrinsic Maxwell Green data `G` over a Levi-Civita atlas `cov` with the
differentiability side conditions:

**(I)** the Caticha functional Hamiltonian preserves the causal KG solution space;
**(II)** `W` is Hadamard-plus-`(i/2)`-Pauli–Jordan, the Pauli–Jordan part is antisymmetric, and the
observable commutator is `W(x,y) − W(y,x) = i·Δ(x,y)` — kernel microcausality;
**(III)** the intrinsic Maxwell causal propagator is a global homogeneous solution for the atlas
representative `cov a`;
**(IV)** the same microcausal field solves the intrinsic equation for the representative `cov b` —
microcausality of the global Maxwell field is **atlas-independent** (III fed through the
atlas-iff, the genuinely new consequence assembled here). -/
theorem caticha_hadamard_maxwell_microcausality
    -- (I) the Caticha continuum KG leg
    {𝓕c 𝓢c : Type*} [AddCommGroup 𝓕c] [Module ℂ 𝓕c] [AddCommGroup 𝓢c] [Module ℂ 𝓢c]
    (D : ContinuumCatichaKGData 𝓕c 𝓢c) (sc : 𝓢c)
    -- (II) the Hadamard/AQFT observable leg
    {α : Type*} (W : α → α → ℂ) (hW : IsHermitianKernel W)
    -- (III)/(IV) the global intrinsic Maxwell leg over a Levi-Civita atlas
    {d : ℕ} (g : PseudoRiemannianMetric E H M n I) {ι : Type*}
    (cov : ι → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : ι)
    (sign : Fin d → ℝ) (frame : Fin d → ∀ x : M, TangentSpace I x)
    {𝓢m 𝓕m : Type*} [AddCommGroup 𝓢m] [Module ℝ 𝓢m] [AddCommGroup 𝓕m] [Module ℝ 𝓕m]
    (G : IntrinsicMaxwellGreenData I g (cov a) sign frame 𝓢m 𝓕m) (sm : 𝓢m)
    (hV : ∀ x, MDiffAt (T% (G.realizeField (causalPropagator I G sm))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x, MDiffAt
      (T% (firstCovariantSection I (cov b) (frame i)
        (G.realizeField (causalPropagator I G sm)))) x)
    (hbracket : ∀ i j x, MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    -- (I)
    (D.kleinGordon (continuumSmearedSchrodingerGenerator D.lapse D.shift D.Hperp D.Hi
        (D.causalPropagator sc)) = 0)
    -- (II)
    ∧ (wightmanTwoPoint (hadamardPart W) (pauliJordanPart W) = W)
    ∧ IsPauliJordan (pauliJordanPart W)
    ∧ (∀ x y, W x y - W y x = Complex.I * ((pauliJordanPart W x y : ℝ) : ℂ))
    -- (III)
    ∧ IntrinsicRicciCoupledMaxwellOn I g (cov a) sign frame
        (G.realizeField (causalPropagator I G sm)) 0
    -- (IV)
    ∧ IntrinsicRicciCoupledMaxwellOn I g (cov b) sign frame
        (G.realizeField (causalPropagator I G sm)) 0 := by
  have hrec := wightmanTwoPoint_hadamardPart_pauliJordanPart W
  have hPJ := pauliJordanPart_isPauliJordan hW
  have hsym := hadamardPart_symmetric hW
  have hIII := causalPropagator_solves_homogeneous I G sm
  refine ⟨D.caticha_causalPropagator_is_homogeneous sc, hrec, hPJ, ?_, hIII, ?_⟩
  · intro x y
    have h := wightman_commutator (hadamardPart W) (pauliJordanPart W) hsym hPJ x y
    rw [hrec] at h
    exact h
  · exact (intrinsicRicciCoupledMaxwellOn_atlas_iff I g cov hatlas a b sign frame
      (G.realizeField (causalPropagator I G sm)) 0 hV hframe hNablaFrame hbracket).mp hIII

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil_theorem_intent caticha_hadamard_maxwell_microcausality where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData,
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition.pauliJordanPart,
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn]

zil attach caticha_hadamard_maxwell_microcausality where
  formalizes @ "claim:caticha-hadamard-aqft-global-maxwell-meet-on-the-pauli-jordan-causal-carrier",
  requires @ "claim:caticha-flow-preserves-causal-kg-solution-space",
  requires @ "claim:hermitian-two-point-splits-hadamard-plus-pauli-jordan",
  requires @ "claim:intrinsic-maxwell-causal-propagator-is-global-homogeneous-solution",
  requires @ "claim:intrinsic-maxwell-equation-is-atlas-independent",
  supported_by @ "paper:sorkin-johnston-two-point",
  supported_by @ "paper:caticha-entropic-dynamics",
  supported_by @ "paper:wald-qft-curved-spacetime-hadamard",
  caveat @ "claim:conditional-conjunction-on-independent-data-only-leg-four-is-newly-assembled",
  caveat @ "claim:no-green-hyperbolicity-or-spacelike-support-of-delta-proven"

zil_file_contract physlib.catichaHadamardMaxwellMicrocausality where
  promises "One conditional capstone where the entropic-dynamics, Hadamard-state, AQFT-observable and global intrinsic Maxwell arcs meet on the Pauli-Jordan causal carrier: the Caticha functional Hamiltonian preserves the causal Klein-Gordon solution space, every Hermitian two-point kernel splits as Hadamard plus i over two Pauli-Jordan with the observable commutator recovering the Pauli-Jordan function, the intrinsic Maxwell causal propagator is a global homogeneous solution, and that microcausal solution is atlas-independent - the last obtained by transporting the solution through the Levi-Civita atlas equivalence rather than merely conjoining it."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition.hadamardPart",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState.wightmanTwoPoint",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator",
    "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff"]
  forbids_substitutes ["Green-hyperbolicity or existence claims for the Green operators, which are data",
    "spacelike-support (true microlocal) properties of the Pauli-Jordan kernel",
    "a derivation of any leg from another - the shared carrier is structural"]
  witnessed_by [caticha_hadamard_maxwell_microcausality]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaHadamardMaxwellMicrocausality

end

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.BigOperators.Fin
meta import Mathlib.Algebra.Quaternion
meta import Mathlib.Data.Fintype.Sum
meta import Mathlib.Data.Fintype.Defs
meta import Mathlib.Data.Finset.Defs

/-!
# The tetrahedral 4+1 frame as a local-Lorentz object (SO(1,3), not GL(4))

The regular tetrahedron with a centre — four legs at the vertices plus one central reference — is a purely
**local-Lorentz** datum: a frame in the tangent space, acted on by SO(1,3,ℝ) (and its spin cover SL(2,ℂ)),
with *no* reference to coordinates or diffeomorphisms. This file records the group-theoretic content of that
object so it can serve the repository's particle-model formalizations as a structural tool. It makes **no**
physical identification of any specific particle; the "four legs + centre" is treated only as a frame.

* **§A — the spatial tight frame (SU(2) closure / SO(3) little group).** `tetraVec` are the four leg
  directions `(±1,±1,±1)` with an even number of minus signs (unnormalized; each has `‖·‖² = 3`).
  `tetra_closure` (`∑ᵢ vᵢ = 0`) is the closure / centre-of-mass condition — the SU(2) gauge-closure
  `∑ᵢ Jᵢ = 0` of a 4-valent spin intertwiner. `tetra_tight_frame` (`∑ᵢ vᵢ vᵢᵀ = 4·I₃`, a resolution of the
  identity) says the four legs form a **tight frame** (Minkowski's theorem: a 4-valent SU(2) intertwiner ⟺ a
  flat tetrahedron with face-normals summing to zero). `tetra_inner_eq` gives the Gram matrix `⟪vᵢ,vⱼ⟫ = 3`
  (`i=j`) / `−1` (`i≠j`): the legs are **equiangular** with `cos θ = −1/3`, i.e. the qubit SIC frame on the
  Bloch sphere.
* **§B — the null tetrad (SO(1,3)).** `nullLeg` lifts each spatial leg to a future-null 4-vector
  `n = (√3, vᵢ)`: `nullLeg_null` (`(n⁰)² = (n¹)²+(n²)²+(n³)²`, i.e. `η(n,n) = 0`) and `nullLeg_sum`
  (`∑ᵢ nᵢ = restFrame = (4√3, 0, 0, 0)`, purely timelike) — the four null legs of a tetrahedron symmetrically
  sum to the rest-frame time axis, the null-tetrad closure. This is the light-cone / celestial-sphere face
  of §A.
* **§C — the binary tetrahedral group 2T ⊂ SU(2) ⊂ SL(2,ℂ).** `binaryTetraCoordinates`, the 24 unit
  quaternions `{±1,±i,±j,±k} ∪ {(±1±i±j±k)/2}` (the unit Hurwitz quaternions / 24-cell vertices), with
  `binaryTetraCoordinates_card = 24`, `binaryTetra_normSq_one` (all lie on `S³ = SU(2)`), and
  `binaryTetra_mul_closed` (closed under quaternion product — it is a group, the binary tetrahedral group
  `2T ≅ SL(2,𝔽₃)`). `hurwitzGen_cube` (`τ³ = −1` for `τ = (1+i+j+k)/2`) is the **spin double-cover** witness:
  the tetrahedron's 3-fold rotation axis (order 3 in SO(3)) lifts to an order-6 element of SU(2) whose cube is
  the central `−1` (the 2π rotation). 2T is the tetrahedral sibling of the binary icosahedral group `2I`
  already built in `CliffordRootSystemInduction` (the E₆ vs E₈ rungs of the McKay correspondence).
* **§D — orbital-frame corollaries.** `tetra_angle_cos` (`⟪v₀,v₁⟫/3 = −1/3`, the 109.47° sp³ bond angle) and
  `binaryTetra_card_eq_su5_dim` (`|2T| = 24 = dim SU(5)`). The atomic-shell reading of these — the valence
  octet as four sp³ directions × spin, and the d-shell / `SU(5)` `10` — lives on the atomic side in
  `Particles.AtomicShellInformationCapacityOctet`.
* **§E — the qubit SIC-POVM.** `tetra_sic_overlap` (`|⟨ψᵢ|ψⱼ⟩|² = 1/3 = 1/(d+1)`, the equiangular
  symmetric-informationally-complete overlap of the four Bloch-tetrahedron states) and
  `tetra_sic_frame_potential` (`∑ᵢⱼ|⟨ψᵢ|ψⱼ⟩|² = 8 = N²/d`, Welch-bound saturation): the tight frame is the
  informationally optimal minimal `4 = d²`-outcome (two-bit) measurement of a qubit.

## Uses for the particle sector

The four legs = four null directions on the celestial sphere (`AdSCFT.WeylSpinorPoincareSphere.weylRatio`,
transforming by `sl2c_weylRatio`); their closure `∑ = 0` is the SU(2) intertwiner condition of the "5 boundary
tetrahedra / 1→4 Pachner" vertex of `SpinNetworkTriangulationEvolution`; the tight frame is the qubit SIC
measurement for a spin-½ Bloch/Poincaré state; and `τ³ = −1` is the same double-cover sign as
`Hopf.SpinHalfDoubleCover` / `ribbonTwist ½ = −1`. Everything here is a subgroup of the **local Lorentz group**
SO(1,3) (via SU(2) ⊂ SL(2,ℂ) and the rest-frame little group `LorentzGroup.Rotations`), never of GL(4).

**Honest layering.** §A and §B are exact finite computations in `ℝ` (tight frame, Gram matrix, null closure).
§C is exact rational quaternion algebra: the 24-element set, its unit-norm and multiplicative closure, and the
order-6 generator are discharged by `native_decide` over `ℍ[ℚ]` (native-evaluation certificates, as in the
existing `2I` construction). No physical identification is asserted — the frame is a structural object.

## References

* Minkowski's theorem on convex polytopes (4-valent SU(2) intertwiner ⟺ tetrahedron); binary polyhedral
  groups / McKay correspondence (`2T = E₆`, `2I = E₈`). Companion to `CliffordRootSystemInduction` (`2I`),
  `SpinNetworkTriangulationEvolution` (4-simplex / 5 tetrahedra), `AdSCFT.WeylSpinorPoincareSphere` (celestial
  sphere), `Hopf.SpinHalfDoubleCover`.
-/

set_option autoImplicit false

open scoped BigOperators Quaternion

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TetrahedralLorentzFrame


/-- The four tetrahedral leg directions `(±1,±1,±1)` with an even number of minus signs (unnormalized; each
has `‖·‖² = 3`). Their normalized versions `vᵢ/√3` point from the centre of a regular tetrahedron to its
vertices. -/
def tetraVec : Fin 4 → Fin 3 → ℝ
  | 0, 0 => 1  | 0, 1 => 1  | 0, 2 => 1
  | 1, 0 => 1  | 1, 1 => -1 | 1, 2 => -1
  | 2, 0 => -1 | 2, 1 => 1  | 2, 2 => -1
  | 3, 0 => -1 | 3, 1 => -1 | 3, 2 => 1

/-- **The tetrahedral closure / centre-of-mass condition** `∑ᵢ vᵢ = 0`: the four legs sum to zero. This is the
SU(2) gauge-closure `∑ᵢ Jᵢ = 0` of a 4-valent spin intertwiner (the vertex sits at the centroid). -/
lemma tetra_closure : ∑ i, tetraVec i = 0 := by
  funext a
  simp only [Finset.sum_apply, Fin.sum_univ_four, Pi.zero_apply]
  fin_cases a <;> simp only [tetraVec] <;> norm_num

/-- The Gram entry `⟪vᵢ, vⱼ⟫ = ∑ₐ vᵢₐ vⱼₐ` of two tetrahedral legs. -/
def tetraInner (i j : Fin 4) : ℝ := ∑ a, tetraVec i a * tetraVec j a

/-- **The tetrahedral Gram matrix** `⟪vᵢ,vⱼ⟫ = 3` if `i=j`, `−1` otherwise: the four legs are **equiangular**,
with normalized inner product `cos θ = −1/3` — the qubit SIC (symmetric informationally-complete) frame on the
Bloch sphere. -/
lemma tetra_inner_eq (i j : Fin 4) : tetraInner i j = if i = j then 3 else -1 := by
  fin_cases i <;> fin_cases j <;>
    simp only [tetraInner, Fin.sum_univ_three, tetraVec] <;> norm_num

/-- The frame operator entry `(∑ᵢ vᵢ vᵢᵀ)ₐᵦ = ∑ᵢ vᵢₐ vᵢᵦ`. -/
def tetraFrame (a b : Fin 3) : ℝ := ∑ i, tetraVec i a * tetraVec i b

/-- **The tetrahedron is a tight frame** `∑ᵢ vᵢ vᵢᵀ = 4·I₃` (a resolution of the identity): the frame operator
is `4` times the identity, so the four legs resolve every vector isotropically. Equivalently (Minkowski's
theorem) this is the closure condition making the four legs a 4-valent SU(2) intertwiner — the isotropy of the
rest-frame little group SO(3) ⊂ SO(1,3). -/
lemma tetra_tight_frame (a b : Fin 3) : tetraFrame a b = if a = b then 4 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp only [tetraFrame, Fin.sum_univ_four, tetraVec] <;> norm_num


/-- The future-null lift of the `i`-th tetrahedral leg to Minkowski `(1,3)`: `nᵢ = (√3, vᵢ)`, with time
component `√3` and spatial part the leg `vᵢ` (`‖vᵢ‖² = 3`). -/
noncomputable def nullLeg (i : Fin 4) : Fin 4 → ℝ
  | 0 => Real.sqrt 3
  | 1 => tetraVec i 0
  | 2 => tetraVec i 1
  | 3 => tetraVec i 2

/-- The purely timelike rest-frame vector `(4√3, 0, 0, 0)` that the four null legs sum to. -/
noncomputable def restFrame : Fin 4 → ℝ
  | 0 => 4 * Real.sqrt 3
  | _ => 0

/-- **Each leg is null** `(n⁰)² = (n¹)² + (n²)² + (n³)²`, i.e. `η(n,n) = 0`: the time component squared equals
the spatial norm squared, so `nᵢ` lies on the light cone — a point of the celestial sphere. -/
lemma nullLeg_null (i : Fin 4) :
    (nullLeg i 0) ^ 2 = (nullLeg i 1) ^ 2 + (nullLeg i 2) ^ 2 + (nullLeg i 3) ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> simp only [nullLeg, tetraVec, h3] <;> norm_num

/-- **The null tetrad closes onto the rest-frame time axis** `∑ᵢ nᵢ = (4√3, 0, 0, 0)`: the four symmetric null
legs sum to a purely timelike vector (the observer's 4-velocity / centre), because the spatial parts close
(`tetra_closure`). This is the null-tetrad face of the SU(2) intertwiner closure. -/
lemma nullLeg_sum : ∑ i, nullLeg i = restFrame := by
  funext a
  fin_cases a <;>
    simp [Finset.sum_apply, Fin.sum_univ_four, nullLeg, tetraVec, restFrame] <;> ring


instance : DecidableEq (ℍ[ℚ]) := fun x y =>
  if hre : x.re = y.re then
    if hi : x.imI = y.imI then
      if hj : x.imJ = y.imJ then
        if hk : x.imK = y.imK then isTrue (QuaternionAlgebra.ext hre hi hj hk)
        else isFalse (fun h => hk (congrArg QuaternionAlgebra.imK h))
      else isFalse (fun h => hj (congrArg QuaternionAlgebra.imJ h))
    else isFalse (fun h => hi (congrArg QuaternionAlgebra.imI h))
  else isFalse (fun h => hre (congrArg QuaternionAlgebra.re h))

/-- A `Bool` sign as a rational `±1`. -/
def signQ (b : Bool) : ℚ := if b then 1 else -1

/-- The eight **Lipschitz** unit quaternions `{±1, ±i, ±j, ±k}` (a signed unit on one of the four axes). -/
def lipschitzPoint (a : Fin 4) (s : Bool) : ℍ[ℚ] :=
  ![(⟨signQ s, 0, 0, 0⟩ : ℍ[ℚ]), ⟨0, signQ s, 0, 0⟩, ⟨0, 0, signQ s, 0⟩, ⟨0, 0, 0, signQ s⟩] a

/-- The sixteen **half** Hurwitz unit quaternions `(±1 ± i ± j ± k)/2`. -/
def halfPoint (s : Fin 4 → Bool) : ℍ[ℚ] :=
  ⟨signQ (s 0) / 2, signQ (s 1) / 2, signQ (s 2) / 2, signQ (s 3) / 2⟩

/-- The `24` labels of the binary tetrahedral group: `8` Lipschitz units `⊕` `16` half-units. -/
abbrev BinaryTetraLabel := (Fin 4 × Bool) ⊕ (Fin 4 → Bool)

/-- The label-to-quaternion map onto the 24 binary-tetrahedral points. -/
def binaryTetraPoint : BinaryTetraLabel → ℍ[ℚ]
  | .inl (a, s) => lipschitzPoint a s
  | .inr s => halfPoint s

/-- The binary tetrahedral group `2T` as a concrete set of `24` unit quaternions. -/
def binaryTetraCoordinates : Finset ℍ[ℚ] := Finset.univ.image binaryTetraPoint

/-- The coordinate map is injective (no duplicate quaternions among the 24 labels). -/
lemma binaryTetraPoint_injective : Function.Injective binaryTetraPoint := by native_decide

/-- **`2T` has exactly `24` elements** — the 24-cell vertices / unit Hurwitz quaternions. -/
lemma binaryTetraCoordinates_card : binaryTetraCoordinates.card = 24 := by
  rw [binaryTetraCoordinates, Finset.card_image_of_injective _ binaryTetraPoint_injective,
    Finset.card_univ]
  native_decide

/-- **Every `2T` element is a unit quaternion** `‖q‖² = 1`: `2T ⊂ S³ = SU(2)`, the spin double cover of
`SO(3) ⊂ SO(1,3)`. -/
lemma binaryTetra_normSq_one :
    ∀ label : BinaryTetraLabel, Quaternion.normSq (binaryTetraPoint label) = 1 := by native_decide

/-- **`2T` is closed under quaternion multiplication** — it is a group (the binary tetrahedral group,
`2T ≅ SL(2,𝔽₃)`), a finite subgroup of `SU(2) ⊂ SL(2,ℂ)`, i.e. of the local Lorentz group's spin cover. -/
lemma binaryTetra_mul_closed :
    ∀ a ∈ binaryTetraCoordinates, ∀ b ∈ binaryTetraCoordinates,
      a * b ∈ binaryTetraCoordinates := by native_decide

/-- The order-6 Hurwitz generator `τ = (1 + i + j + k)/2`. -/
def hurwitzGen : ℍ[ℚ] := ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩

/-- The generator is one of the 24 binary-tetrahedral points. -/
lemma hurwitzGen_mem : hurwitzGen ∈ binaryTetraCoordinates := by native_decide

/-- **The spin double-cover witness** `τ³ = −1`: the tetrahedron's 3-fold rotation axis (order 3 in SO(3))
lifts to the order-6 element `τ ∈ SU(2)`, whose cube is the central `−1` — the `2π` rotation that acts as `−1`
on spinors (the same sign as `Hopf.SpinHalfDoubleCover` and `ribbonTwist ½ = −1`). -/
lemma hurwitzGen_cube : hurwitzGen ^ 3 = -1 := by native_decide


/-- **The tetrahedral bond-angle cosine** `⟪v₀, v₁⟫ / 3 = −1/3` — the `109.47°` angle between two legs
(`⟪vᵢ,vⱼ⟫ = −1`, `‖vᵢ‖² = 3`), i.e. the sp³ / methane / diamond bond angle. The valence-shell reading of this
angle lives on the atomic side (`Particles.AtomicShellInformationCapacityOctet`). -/
lemma tetra_angle_cos : tetraInner 0 1 / 3 = -1 / 3 := by
  rw [tetra_inner_eq, if_neg (by decide)]

/-- **`|2T| = 24 = 5² − 1 = dim SU(5)`**: the binary tetrahedral group (24-cell vertices) has the same order
as the dimension of the `SU(5)` Lie algebra (`Su5TenRepresentation`); the icosahedral sibling `2I` has order
`5! = 120` (`CliffordRootSystemInduction.binaryIcosahedralCoordinates_card`). -/
lemma binaryTetra_card_eq_su5_dim : binaryTetraCoordinates.card = 5 ^ 2 - 1 := by
  rw [binaryTetraCoordinates_card]; decide


/-- The **pure-state overlap** `|⟨ψᵢ|ψⱼ⟩|² = (1 + n̂ᵢ·n̂ⱼ)/2` of the two qubit states with Bloch vectors
`n̂ᵢ = vᵢ/√3` (unit vectors, `n̂ᵢ·n̂ⱼ = ⟪vᵢ,vⱼ⟫/3`) — the Gram matrix of the SIC states. -/
noncomputable def blochOverlap (i j : Fin 4) : ℝ := (1 + tetraInner i j / 3) / 2

/-- **The four Bloch-tetrahedron states are the qubit SIC-POVM** `|⟨ψᵢ|ψⱼ⟩|² = 1/3 = 1/(d+1)` for `i ≠ j`
(`d = 2`): the four states are equiangular with the symmetric informationally-complete overlap, the unique
minimal IC measurement of a qubit. -/
lemma tetra_sic_overlap (i j : Fin 4) : blochOverlap i j = if i = j then 1 else 1 / 3 := by
  by_cases h : i = j <;> simp only [blochOverlap, tetra_inner_eq, h, if_true, if_false] <;> norm_num

/-- **The SIC saturates the Welch bound** `∑ᵢⱼ |⟨ψᵢ|ψⱼ⟩|² = 8 = N²/d` (`N = 4`, `d = 2`): the tetrahedral
frame is an equiangular tight frame of minimal coherence — the informationally optimal `4`-outcome
(`= d²`, two-bit) measurement, the geometric root of the `AtomicShellInformationCapacityOctet` register. -/
lemma tetra_sic_frame_potential : ∑ i, ∑ j, blochOverlap i j = 8 := by
  simp [tetra_sic_overlap, Fin.sum_univ_four]
  norm_num

end Physlib.QuantumMechanics.ComplexAction.TetrahedralLorentzFrame

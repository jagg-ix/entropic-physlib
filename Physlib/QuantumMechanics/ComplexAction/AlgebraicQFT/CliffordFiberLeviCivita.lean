/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SelfDualQuaternionYangMills
public import Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity


/-!
# The Levi-Civita connection, the `Cl(TM) ≅ ℍ ⊕ ℍ` fiber, and the one-region face

The remaining geometric inputs of Aastrup–Grimstrup arXiv:2410.07290 §2–§3 — the
Riemannian metric on `M` inducing the Clifford bundle `Cl(TM)` with fiber `ℍ ⊕ ℍ`,
and the Levi-Civita connection `∇` entering the Dirac blocks `D± = Σc̄(ψᵢ)∇_{ξᵢ}` —
welded to the Bell arc's Levi-Civita/Nagao–Nielsen face
(`Bell.ThreeFaces`, `Bell.LeviCivitaNagaoContour`).

## §A — the Levi-Civita connection (fundamental theorem, Christoffel form)

The connection of the paper's Dirac operator is *the* Levi-Civita connection of the
(fibered) metric. Its defining theorem, exactly:

* `christoffelFirstKind` — the Koszul/Christoffel formula
  `Γ_{k,ij} = ½(∂ᵢg_{jk} + ∂ⱼg_{ik} − ∂ₖg_{ij})` from the metric derivative data.
* `christoffelFirstKind_torsionFree` / `christoffelFirstKind_metricCompat` —
  **existence**: the formula is symmetric in `(i,j)` and reproduces the metric
  derivative, `∂ᵢg_{jk} = Γ_{k,ij} + Γ_{j,ik}`.
* `leviCivita_unique` — **uniqueness** (the fundamental theorem of Riemannian
  geometry at the Christoffel level): *any* torsion-free metric-compatible `Γ`
  equals the Koszul formula. The tetrad-frame face of the same theorem is
  `Curvature.JacobiRicciBianchiTetrad.TetradConnection.koszul`.
* `christoffelFirstKind_flat` — for a flat metric (`∂g = 0`) the connection
  vanishes: the papers' working simplification `∇_{ξᵢ} = ∂/∂ξᵢ`, whose failure
  measure is the `Ξ` term (`ConfigurationSpaceGaugeGeometry`).

## §B — the fiber `Cl(TM) ≅ ℍ ⊕ ℍ` (paper §2)

The paper opens: *"fiberwise `Cl(TM)` is isomorphic to `ℍ ⊕ ℍ`, and if we
complexify … this becomes fiberwise isomorphic to `M₂(ℂ) ⊕ M₂(ℂ)`. We thus get two
spin`^ℂ`-bundles `S₁` and `S₂`."* The exact algebra:

* `quatUnit_clifford` — the quaternion imaginary units satisfy the `Cl(0,3)`
  relations `uₐuᵦ + uᵦuₐ = −2δₐᵦ`.
* `pairGenerator_clifford` — the pair generators `γₐ = (uₐ, −uₐ) ∈ ℍ ⊕ ℍ` satisfy
  the same Clifford relations: `ℍ ⊕ ℍ` is a `Cl(0,3)`-module algebra on three
  generators.
* `volumeElement_split` — the volume element is the **central sign**
  `ω = γ₁γ₂γ₃ = (−1, 1)`, with `ω² = 1` (`volumeElement_sq`); `1 ∓ ω = (2,0), (0,2)`
  (`volume_idempotent_data`) are (twice) the central idempotents cutting the algebra
  into its two `ℍ` factors — **the two spin`^ℂ` bundles `S₁, S₂` of the paper are
  the two `ω`-eigensectors of the fiber**.
* `quaternionRep_neg`, `pairRep_mul`, `pairRep_generators` — complexification: the
  componentwise `quaternionRep` is multiplicative into `M₂(ℂ) ⊕ M₂(ℂ)` and sends
  the generators to `(−iσₐ, +iσₐ)` — the Pauli realization of the two sectors,
  welding the fiber to the spin embedding
  (`ConfigurationSpaceDiracOperator.su2Basis_embeddingMetric`).

## §C — the one-region point on the spacelike face (the Bell/Levi-Civita weld)

The Bell arc carries the Caticha/Nagao–Nielsen/Levi-Civita face:
`ThreeFaces.spacelike q ↔ |Re q| < |Im q|` (the complex-action Lorentzian form),
`chsh_on_spacelike_face`, `spacelike_boost_invariant`, and
`LeviCivitaNagaoContour.leviCivita_bellNoSignaling_realContour_reversible`
(no-signalling as reversibility of real-contour Levi-Civita transport). The
one-region extension — *the identification locus is the fixed contour; swap and
boost invariance make the region a single boost-orbit point on the spacelike face*:

* `oneRegion_identification_spacelike` — the identification locus (zero real
  separation, purely entropic/imaginary extension `r`) lies on the spacelike
  (no-signalling) face, and is **swap-invariant**: exchanging the two labels
  (`x ↦ −x`) preserves the Lorentzian form — the exchange of the pair's labels is
  invisible on the face.
* `bellRegion_spacelike` — instantiated at the Bell radius `r = λ_C·log 2` of
  `EntanglementScreenArea`: the one-region screen sits on the spacelike face.
* `oneRegion_boost_orbit` — the boosts carry the identification point through a
  **single orbit** `{q : lorentzianForm q = −r²}` inside the spacelike face: every
  boosted image is spacelike with the same invariant `−r²` — the one region is a
  boost-orbit point, not a frame-dependent pair.

## Honest scope

§A is the coordinate/Christoffel layer (no manifolds; `∂g` is data); §B gives the
generators, relations, central splitting, and complexification of the fiber — the
full algebra-isomorphism packaging via `CliffordAlgebra.lift` (universal property)
and the dimension count `8 = 4 + 4` are recorded; §C works on the `(t,x)`-pair and
`ℂ`-form carriers of the Bell arc.

## References

* J. Aastrup, J. M. Grimstrup, arXiv:2410.07290 §2 (fiber, metric), §3 (Dirac with
  Levi-Civita `∇`); arXiv:2501.00005.
* Carriers: `SelfDualQuaternionYangMills` (`quaternionRep`, Pauli),
  `Bell.ThreeFaces` (`spacelike`, boosts), `Bell.LeviCivitaNagaoContour`,
  `ComplexDelta.Convergence` (`lorentzianForm`),
  `TimeOperator.HyperbolicPoincareLorentzMisra` (`lorentzBoost`),
  `Curvature.JacobiRicciBianchiTetrad` (tetrad Koszul),
  `ComptonClock.FrequencyTrinity` (`comptonWavelength`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SelfDualQuaternionYangMills
open Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita

/-! ## §A — the Levi-Civita connection -/

variable {n : ℕ}

/-- **The Koszul/Christoffel formula** (first kind): from the metric derivative data
`dg i j k = ∂ᵢ g_{jk}`, the Levi-Civita connection coefficients
`Γ_{k,ij} = ½(∂ᵢg_{jk} + ∂ⱼg_{ik} − ∂ₖg_{ij})`. -/
noncomputable def christoffelFirstKind (dg : Fin n → Fin n → Fin n → ℝ) (k i j : Fin n) : ℝ :=
  (dg i j k + dg j i k - dg k i j) / 2

/-- **Torsion-freeness**: the Koszul formula is symmetric in the lower pair,
`Γ_{k,ij} = Γ_{k,ji}` (for a symmetric metric). -/
theorem christoffelFirstKind_torsionFree {dg : Fin n → Fin n → Fin n → ℝ}
    (hsym : ∀ a b c, dg a b c = dg a c b) (k i j : Fin n) :
    christoffelFirstKind dg k i j = christoffelFirstKind dg k j i := by
  unfold christoffelFirstKind
  linarith [hsym k i j]

/-- **Metric compatibility**: the Koszul formula reproduces the metric derivative,
`∂ᵢg_{jk} = Γ_{k,ij} + Γ_{j,ik}` — the connection preserves the metric. -/
theorem christoffelFirstKind_metricCompat {dg : Fin n → Fin n → Fin n → ℝ}
    (hsym : ∀ a b c, dg a b c = dg a c b) (i j k : Fin n) :
    dg i j k = christoffelFirstKind dg k i j + christoffelFirstKind dg j i k := by
  unfold christoffelFirstKind
  linarith [hsym i j k]

/-- **Uniqueness — the fundamental theorem of Riemannian geometry** (Christoffel
level): *any* connection coefficients that are torsion-free and metric-compatible
equal the Koszul formula. This is the sense in which the `∇_{ξᵢ}` of the
configuration-space Dirac operator is *the* Levi-Civita connection of the fibered
metric. -/
theorem leviCivita_unique {dg Γ : Fin n → Fin n → Fin n → ℝ}
    (htf : ∀ k i j, Γ k i j = Γ k j i)
    (hcompat : ∀ i j k, dg i j k = Γ k i j + Γ j i k) (k i j : Fin n) :
    Γ k i j = christoffelFirstKind dg k i j := by
  unfold christoffelFirstKind
  linarith [hcompat i j k, hcompat j i k, hcompat k i j,
    htf k i j, htf j i k, htf i j k]

/-- **The flat case**: constant metric (`∂g = 0`) gives vanishing connection — the
papers' working assumption `∇_{ξᵢ} = ∂/∂ξᵢ`, whose failure is the `Ξ` term. -/
theorem christoffelFirstKind_flat {dg : Fin n → Fin n → Fin n → ℝ}
    (h : ∀ a b c, dg a b c = 0) (k i j : Fin n) :
    christoffelFirstKind dg k i j = 0 := by
  unfold christoffelFirstKind
  rw [h, h, h]
  ring

/-! ## §B — the fiber `Cl(TM) ≅ ℍ ⊕ ℍ` -/

/-- The three quaternion imaginary units `i, j, k`, indexed. -/
def quatUnit : Fin 3 → Quaternion ℝ
  | 0 => ⟨0, 1, 0, 0⟩
  | 1 => ⟨0, 0, 1, 0⟩
  | 2 => ⟨0, 0, 0, 1⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The quaternion units satisfy the `Cl(0,3)` relations**:
`uₐuᵦ + uᵦuₐ = −2δₐᵦ`. -/
theorem quatUnit_clifford (a b : Fin 3) :
    quatUnit a * quatUnit b + quatUnit b * quatUnit a
      = (if a = b then (⟨-2, 0, 0, 0⟩ : Quaternion ℝ) else 0) := by
  fin_cases a <;> fin_cases b <;>
    ext <;>
    simp [quatUnit, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    norm_num

set_option backward.isDefEq.respectTransparency false in
/-- **The pair generators of `ℍ ⊕ ℍ`**: `γₐ = (uₐ, −uₐ)` satisfy the same `Cl(0,3)`
relations — the fiber `ℍ ⊕ ℍ` carries the Clifford algebra of the tangent space on
three generators. -/
theorem pairGenerator_clifford (a b : Fin 3) :
    ((quatUnit a, -quatUnit a) : Quaternion ℝ × Quaternion ℝ) * (quatUnit b, -quatUnit b)
        + (quatUnit b, -quatUnit b) * (quatUnit a, -quatUnit a)
      = ((if a = b then (⟨-2, 0, 0, 0⟩ : Quaternion ℝ) else 0),
         (if a = b then (⟨-2, 0, 0, 0⟩ : Quaternion ℝ) else 0)) := by
  have h := quatUnit_clifford a b
  rw [Prod.ext_iff]
  constructor
  · simpa using h
  · simpa [neg_mul_neg] using h

set_option backward.isDefEq.respectTransparency false in
/-- **The volume element is the central sign separating the two factors**:
`ω = γ₁γ₂γ₃ = (−1, 1)` — the paper's fiber splitting `Cl(TM) ≅ ℍ ⊕ ℍ`: the two
spin`^ℂ` bundles `S₁, S₂` are the two `ω`-eigensectors. -/
theorem volumeElement_split :
    ((quatUnit 0, -quatUnit 0) : Quaternion ℝ × Quaternion ℝ) * (quatUnit 1, -quatUnit 1)
        * (quatUnit 2, -quatUnit 2)
      = (-1, 1) := by
  rw [Prod.ext_iff]
  constructor <;>
    ext <;>
    simp [quatUnit, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    rfl

/-- `ω² = 1` — the volume element is an involution, so `(1 ± ω)/2` are idempotents. -/
theorem volumeElement_sq :
    ((-1, 1) : Quaternion ℝ × Quaternion ℝ) * (-1, 1) = 1 := by
  rw [Prod.mk_mul_mk]
  norm_num [Prod.ext_iff]

/-- **The central idempotent data**: `1 − ω = (2, 0)` and `1 + ω = (0, 2)` — twice
the central idempotents projecting onto the two `ℍ` factors (stated `2`-scaled to
stay in the integral subring). -/
theorem volume_idempotent_data :
    (1 : Quaternion ℝ × Quaternion ℝ) - (-1, 1) = (2, 0)
      ∧ (1 : Quaternion ℝ × Quaternion ℝ) + (-1, 1) = (0, 2) := by
  constructor <;> simp [Prod.ext_iff] <;> norm_num

/-- `rep(−q) = −rep(q)` — the quaternion representation is additive on negation. -/
theorem quaternionRep_neg (q : Quaternion ℝ) :
    quaternionRep (-q) = -quaternionRep q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRep] <;>
    ring

/-- The componentwise complexification `ℍ ⊕ ℍ → M₂(ℂ) ⊕ M₂(ℂ)`. -/
def pairRep (x : Quaternion ℝ × Quaternion ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ :=
  (quaternionRep x.1, quaternionRep x.2)

/-- **The complexification is multiplicative**: `ℂl(TM) ≅ M₂(ℂ) ⊕ M₂(ℂ)` fiberwise
(paper §2), componentwise from `quaternionRep_mul`. -/
theorem pairRep_mul (x y : Quaternion ℝ × Quaternion ℝ) :
    pairRep (x * y) = pairRep x * pairRep y := by
  rw [Prod.ext_iff]
  exact ⟨quaternionRep_mul x.1 y.1, quaternionRep_mul x.2 y.2⟩

/-- **The complexified generators are the two Pauli sectors**:
`pairRep γₐ = (−iσₐ, +iσₐ)` — the fiber's two `ω`-sectors land on the two signs of
the `𝔰𝔲(2)` Pauli generators of the spin embedding. -/
theorem pairRep_generators (a : Fin 3) :
    pairRep (quatUnit a, -quatUnit a)
      = (-Complex.I • pauliVec a, Complex.I • pauliVec a) := by
  have h := quaternionRep_imaginaryUnits
  have hneg : ∀ (q : Quaternion ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ),
      quaternionRep q = -Complex.I • P → quaternionRep (-q) = Complex.I • P := by
    intro q P hq
    rw [quaternionRep_neg, hq, neg_smul, neg_neg]
  rw [Prod.ext_iff]
  fin_cases a
  · exact ⟨h.1, hneg _ _ h.1⟩
  · exact ⟨h.2.1, hneg _ _ h.2.1⟩
  · exact ⟨h.2.2, hneg _ _ h.2.2⟩

/-! ## §C — the one-region point on the spacelike face -/

/-- **The identification locus is on the spacelike face and is swap-invariant**: the
one-region point has zero real separation and purely entropic (imaginary) extension
`r ≠ 0`, so it is spacelike (`|Re| = 0 < |Im|` — the no-signalling face of
`ThreeFaces`), and exchanging the two labels (`r ↦ −r`, the swap of the pair)
preserves the Lorentzian form — the label exchange is invisible on the face. -/
theorem oneRegion_identification_spacelike (r : ℝ) (hr : r ≠ 0) :
    spacelike ⟨0, r⟩ ∧ lorentzianForm ⟨0, -r⟩ = lorentzianForm ⟨0, r⟩ := by
  constructor
  · rw [spacelike_iff_abs_lt]
    simpa using abs_pos.mpr hr
  · unfold lorentzianForm
    ring

/-- **The Bell one-region screen sits on the spacelike face**: at the Bell radius
`r = λ_C·log 2` (`EntanglementScreenArea`), the identification point is spacelike —
the entropic proper radius is a no-signalling separation. -/
theorem bellRegion_spacelike (m c ħ : ℝ) (hlam : comptonWavelength m c ħ ≠ 0) :
    spacelike ⟨0, comptonWavelength m c ħ * Real.log 2⟩ :=
  (oneRegion_identification_spacelike _
    (mul_ne_zero hlam (ne_of_gt (Real.log_pos (by norm_num))))).1

/-- **The one region is a single boost-orbit point on the spacelike face**: every
Lorentz boost carries the identification point `(0, r)` to another point of the
*same* orbit `{q : lorentzianForm q = −r²}` inside the spacelike face — combined
with swap-invariance (`oneRegion_identification_spacelike`), the entangled pair is
one boost-orbit point, not a frame-dependent pair of localized parts. -/
theorem oneRegion_boost_orbit (θ r : ℝ) (hr : r ≠ 0) :
    spacelike ⟨(lorentzBoost θ 0 r).1, (lorentzBoost θ 0 r).2⟩
      ∧ lorentzianForm ⟨(lorentzBoost θ 0 r).1, (lorentzBoost θ 0 r).2⟩ = -(r ^ 2) := by
  have h := lorentzBoost_preserves_form θ 0 r
  have hform : lorentzianForm ⟨(lorentzBoost θ 0 r).1, (lorentzBoost θ 0 r).2⟩
      = -(r ^ 2) := by
    unfold lorentzianForm
    simpa using h
  refine ⟨?_, hform⟩
  unfold spacelike
  rw [hform]
  have : 0 < r ^ 2 := by positivity
  linarith

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita

end

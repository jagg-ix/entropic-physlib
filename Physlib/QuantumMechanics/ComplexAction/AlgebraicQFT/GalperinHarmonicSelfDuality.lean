/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SelfDualQuaternionYangMills

/-!
# Galperin harmonic analyticity: self-duality as a harmonic-space integrability condition

Galperin–Ivanov–Ogievetsky–Sokatchev reformulate the self-dual Yang–Mills equation as an
*integrability* condition on a harmonic extension of space (Ann. Phys. **185** (1988), §III). Reducing
the `R⁴ⁿ` Lorentz group to `Sp(n) × SU(2)`, the covariant strength splits by its `SU(2)` indices,

  `[𝒟_{μi}, 𝒟_{νj}] = i ε_{ij} F_{(μν)} + i F_{(ij)[μ,ν]}` (III.3′),

into the `SU(2)`-antisymmetric part `F_{(μν)}` and the `SU(2)`-**symmetric** part `F_{(ij)}`; the
self-duality equation is the vanishing of the latter, `n = 1 : F_{(ij)} = 0` (page 13). Introducing the
harmonic variables `u^{±i}` that parametrize the sphere `S² = SU(2)/U(1)` (`u⁺ⁱu⁻ᵢ = 1`, III.6) and
contracting (III.3′) with `u⁺ⁱu⁺ʲ` turns the constraint into

  `[𝒟⁺_μ, 𝒟⁺_ν] = 0`,  `𝒟⁺_μ ≡ u⁺ᵘ 𝒟_{μi}` (III.7),

the integrability condition for the covariantly analytic (CR) field `𝒟⁺_μ φ = 0` (III.8). Because the
`u⁺` are arbitrary, (III.7) "simply means that the part of the full field strength symmetric in its
`SU(2)` indices `i, j` vanishes" — the self-duality condition again.

This module formalizes the algebraic core of that reformulation: the projected strength
`F⁺⁺(u) = u⁺ⁱ u⁺ʲ F_{ij}` (`harmonicProj`), and the equivalence

  `(∀ u, F⁺⁺(u) = 0) ⟺ F antisymmetric in its SU(2) indices` (`harmonicProj_forall_iff_selfDual`),

i.e. the harmonic constraint (III.7) holds for every point of the sphere iff the symmetric triplet
`F_{(ij)}` — the anti-self-dual sector `∧²₋` — vanishes, the self-duality equation. Three points of the
sphere already suffice (`harmonicProj_three_points_selfDual`): the projection `u⁺u⁺` is a degree-two
harmonic, so the triplet is fixed by finitely many `u`. A concrete non-self-dual strength is detected
(`harmonicProj_witness_nonSelfDual`), so the constraint is non-trivial.

## Relation to the self-dual / Bianchi arc

This is the **gauge side** of the correspondence whose **gravity side** is the cyclic-Bianchi / BCJ work:

* The gravity self-duality equation reduces "by the cyclic identity" — the first/second Bianchi identity
  (`Curvature.RiemannLeviCivitaContraction`, `Curvature.SecondBianchiCyclicFamily`,
  `BCJDoubleCopy.SecondBianchiConservation`) — exactly as the gauge one reduces here. Galperin (§II.2,
  page 3) makes the parallel explicit: Kähler/hyper-Kähler holonomy constraints `[𝒟_α, 𝒟_β] = 0` are the
  gravity images of the same integrability conditions.
* The self-duality-plus-Bianchi ⟹ field-equation step (Galperin page 13, `𝒟^{μi} F_{(μν)} = 0`) is, in
  the abelian `n = 1` case, already `Electromagnetic.HodgeStarBivector.selfDual_faraday_isHarmonic2`: a
  self-dual `F = dA` is closed (Bianchi) and hence co-closed (`d⋆F = dF = 0`), i.e. source-free. That is
  the gauge partner of the gravity `∇^μ G_{μν} = 0`.
* The `SU(2)`-symmetric triplet `F_{(ij)}` that `harmonicProj` isolates is the `∧²₋` (anti-self-dual)
  sector of the Hodge decomposition `∧²ℝ⁴ = ∧²₊ ⊕ ∧²₋`; its vanishing is self-duality
  (`Electromagnetic.HodgeStarBivector.IsSelfDual`, `AlgebraicQFT.SelfDualQuaternionYangMills`'s
  `projAntiSelfDual`/`selfDual_iff_asdProj_zero`).

## Honest scope

Formalized: the harmonic-projection algebra — `F⁺⁺(u) = 0` for all `u` iff the `SU(2)`-symmetric part of
`F` vanishes, and the finite-sphere refinement. The `u^{±i}` are taken as real coordinates and the
constraint is quantified over all of them, which subsumes the sphere `u⁺ⁱu⁻ᵢ = 1` (whose `ε`-form and
`u⁺`-nullity `u⁺ⁱu⁺ᵢ = 0` are `symplForm`, `symplForm_self`). Cited, not formalized: the harmonic
superspace proper — the covariant `𝒟⁺_μ`, the CR field `𝒟⁺_μ φ = 0` (III.8), the unconstrained
prepotential/bridge solving it, and the `SU(2)`-triplet ↔ `∧²` soldering `σ_μ^{iα}` that identifies
`F_{(ij)}` with the anti-self-dual matrix strength.

## References

* A. Galperin, E. Ivanov, V. Ogievetsky, E. Sokatchev, *Gauge Field Geometry from Complex and Harmonic
  Analyticities. I. Kähler and Self-Dual Yang–Mills Cases*, Ann. Phys. **185** (1988) 1–21, §III
  (Eqs. III.3′, III.6, III.7, III.8, and the `n = 1 : F_{(ij)} = 0` self-duality of page 13).
* `AlgebraicQFT.SelfDualQuaternionYangMills` — the abstract `⋆`-involution and `P± = ½(1 ± ⋆)`.
* `Electromagnetic.HodgeStarBivector` — the concrete `∧²ℝ⁴ = ∧²₊ ⊕ ∧²₋` split, `IsSelfDual`, and the
  abelian self-dual ⟹ harmonic (page-13 `n = 1`) statement.
* `Curvature.RiemannLeviCivitaContraction`, `BCJDoubleCopy.SecondBianchiConservation` — the gravity-side
  Bianchi/cyclic-identity partner of the double copy.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GalperinHarmonicSelfDuality

/-- **The harmonic-projected field strength** `F⁺⁺(u) = u⁺ⁱ u⁺ʲ F_{ij}` (Galperin III.7): the
contraction of the `SU(2)` curvature `F_{ij}` (one Lie-algebra component) with the harmonic square
`u⁺ⁱ u⁺ʲ`. Its vanishing for all `u` on the sphere is the self-duality constraint. -/
def harmonicProj (F : Fin 2 → Fin 2 → ℝ) (u : Fin 2 → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * u j * F i j

/-- **The `SU(2)` symplectic form** `⟨u, v⟩ = ε^{ij} u_i v_j = u₀ v₁ − u₁ v₀`. The harmonic variables
`u^{±i}` lie on the sphere `⟨u⁺, u⁻⟩ = u⁺ⁱ u⁻ᵢ = 1` (Galperin III.6). -/
def symplForm (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

/-- **`u⁺` is `ε`-null** `u⁺ⁱ u⁺ᵢ = 0` (Galperin III.6): a single harmonic spinor is isotropic for the
`SU(2)` symplectic form. This is what lets `u⁺ⁱ u⁺ʲ` project onto the symmetric (spin-1) part alone. -/
theorem symplForm_self (u : Fin 2 → ℝ) : symplForm u u = 0 := by
  simp only [symplForm]; ring

/-- **The symplectic form is antisymmetric** `⟨u, v⟩ = −⟨v, u⟩` — the defining property of `ε^{ij}`. -/
theorem symplForm_antisymm (u v : Fin 2 → ℝ) : symplForm u v = - symplForm v u := by
  simp only [symplForm]; ring

/-- **Component expansion** of the harmonic projection over `SU(2) = Fin 2`:
`F⁺⁺(u) = u₀² F₀₀ + u₀u₁ F₀₁ + u₁u₀ F₁₀ + u₁² F₁₁`. -/
theorem harmonicProj_eq (F : Fin 2 → Fin 2 → ℝ) (u : Fin 2 → ℝ) :
    harmonicProj F u
      = u 0 * u 0 * F 0 0 + u 0 * u 1 * F 0 1 + u 1 * u 0 * F 1 0 + u 1 * u 1 * F 1 1 := by
  simp only [harmonicProj, Fin.sum_univ_two]; ring

/-- **The projection is additive in the field strength** `(F + G)⁺⁺ = F⁺⁺ + G⁺⁺` — it is linear in the
curvature, as befits the Lie-algebra component of `[𝒟⁺, 𝒟⁺]`. -/
theorem harmonicProj_add (F G : Fin 2 → Fin 2 → ℝ) (u : Fin 2 → ℝ) :
    harmonicProj (fun i j => F i j + G i j) u = harmonicProj F u + harmonicProj G u := by
  simp only [harmonicProj_eq]; ring

/-- **Self-duality is the harmonic integrability condition** (Galperin III.7 ⟺ III.3′, `n = 1`).
The projected curvature `F⁺⁺(u) = u⁺ⁱu⁺ʲF_{ij}` vanishes for *every* harmonic `u` if and only if `F` is
antisymmetric in its `SU(2)` indices — i.e. the symmetric triplet `F_{(ij)}` (the anti-self-dual sector)
vanishes, the self-duality equation `n = 1 : F_{(ij)} = 0`. The projection detects exactly the symmetric
part; quantifying over all points of the sphere forces it to zero. -/
theorem harmonicProj_forall_iff_selfDual (F : Fin 2 → Fin 2 → ℝ) :
    (∀ u, harmonicProj F u = 0) ↔ (∀ i j, F i j = - F j i) := by
  constructor
  · intro h
    have e0 : F 0 0 = 0 := by
      have := h ![1, 0]; rw [harmonicProj_eq] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; linarith
    have e1 : F 1 1 = 0 := by
      have := h ![0, 1]; rw [harmonicProj_eq] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; linarith
    have e2 : F 0 1 + F 1 0 = 0 := by
      have := h ![1, 1]; rw [harmonicProj_eq] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; linarith
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith
  · intro h u
    rw [harmonicProj_eq]
    have h00 : F 0 0 = 0 := by have := h 0 0; linarith
    have h11 : F 1 1 = 0 := by have := h 1 1; linarith
    have h10 : F 1 0 = - F 0 1 := by have := h 0 1; linarith
    rw [h00, h11, h10]; ring

/-- **Three points of the sphere suffice** (the harmonic triplet is degree two). If the projected
strength vanishes at `u = (1,0)`, `(0,1)`, `(1,1)` then `F` is `SU(2)`-antisymmetric, i.e. self-dual —
the `u⁺u⁺` harmonic has only three independent components, so (III.7) at these already gives
`F_{(ij)} = 0`. -/
theorem harmonicProj_three_points_selfDual (F : Fin 2 → Fin 2 → ℝ)
    (h0 : harmonicProj F ![1, 0] = 0) (h1 : harmonicProj F ![0, 1] = 0)
    (h2 : harmonicProj F ![1, 1] = 0) : ∀ i j, F i j = - F j i := by
  rw [harmonicProj_eq] at h0 h1 h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all <;> linarith

/-- **The constraint is non-trivial**: a field strength with a non-vanishing symmetric part is detected
by the harmonic projection. For `F_{ij} = δ_{i0}δ_{j0}` (a pure `F_{(00)}` component, not self-dual),
`F⁺⁺((1,0)) = 1 ≠ 0`, so not every strength satisfies (III.7) — the self-duality equation cuts out a
proper subspace. -/
theorem harmonicProj_witness_nonSelfDual :
    harmonicProj (fun i j => if i = 0 ∧ j = 0 then (1 : ℝ) else 0) ![1, 0] = 1 := by
  rw [harmonicProj_eq]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GalperinHarmonicSelfDuality

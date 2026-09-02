/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The tensor calculations behind the timelike screen (Piazza §2–3)

The index-summation core of the tensor calculation in

> F. Piazza, *"Gauss–Codazzi Thermodynamics on the Timelike Screen"*, arXiv:1005.5151v2 [gr-qc],
> Perimeter Institute (25 Oct 2010).

**Paper's thesis.** Jacobson (PRL 75 (1995) 1260) showed that the flux of matter-energy through a local Rindler
**horizon** obeys the first law of thermodynamics `dE = T dS` (Piazza Eq. 1.1) once `T` is the Unruh
temperature and `dS` the area change of the null generators. Piazza extends this from a null horizon to a
**timelike screen** `ℋ` of observers with *finite* acceleration `A`. Because timelike curves have more freedom
than null geodesics, the extension needs a few geometric conditions (§2) and the Gauss–Codazzi equation (§3),
but it yields a result that relates the **expansion of the observers directly** (not its derivative, as in
Jacobson) to the matter flux.

## The paper's construction and its equations

**§2 — building the screen.** A congruence of observers `V_a` (`V·V = −1`), zero vorticity, decomposes its
gradient as `V_{a;b} = θ_ab − V̇_a V_b` (Eq. 2.1: `θ_ab` the expansion, `V̇_a` the acceleration, `V̇·V = 0`).
The screen `ℋ` is spanned by their worldlines, with unit normal `n_a` along the acceleration: `A n_a = V̇_a`,
`A² = V̇·V̇` (Eq. 2.2). Conditions imposed: (i) `ℋ` is a 3-d timelike hypersurface; (ii) the acceleration is
orthogonal to `ℋ`; (iii) the acceleration is **Fermi-transported** along each worldline,
`V^b V̇_{a;b} − A² V_a = 0` (Eq. 2.3). A differentiation of `V̇_a = V^c V_{a;c}` (Leibniz) together with the
**Ricci identity** `V_{a;cb} − V_{a;bc} = R_{acbd}V^d` gives `V̇_{a;b}` in terms of the expansion and the tidal
tensor `S_ab = R_{acbd}V^c V^d` (Eqs. 2.5, 2.7); by the Riemann symmetries `S_ab` is orthogonal to `V` (lives on
`ℋ`). The expansion splits as `θ_ab = θ̃_ab + θ₃ n_a n_b` (Eq. 2.11), with `θ̃_ab` the **two-dimensional**
expansion on the spacelike screen slice `𝒮`.

**§3 — Gauss–Codazzi on the screen.** The extrinsic curvature is `K_ab = −A V_a V_b + K̃_ab` (Eq. 3.1). The
Gauss–Codazzi equation `(R_{dabc}n^d)_{|ℋ} = (K_{ab;c} − K_{ac;b})_{|ℋ}` (Eq. 3.2) contracts to
`R_{ab}V^a n^b = q^{ab}V^c(K_{ac;b} − K_{ab;c})` (Eq. 3.4); using condition (iii) the first bracket gives
`q^{ab}V^c K_{ac;b} = A θ̃ − θ̃^c_b K̃_{ac}` (Eq. 3.5), where `θ̃ = q^{ab}θ̃_ab = d ln(Δ𝒜)/ds` is the log
derivative of the area element. The matter-energy flux is `dE = T_{ab}V^a n^a Δ𝒜 ds = (8πG)^{-1}R_{ab}V^a n^a
Δ𝒜 ds` by Einstein's equation (Eq. 3.3; the cosmological/metric term drops since `V ⟂ n`).

**The flat screen (§3.1).** Imposing condition (iv-a) `K̃_ab = 0` (Eq. 3.8) collapses Eq. 3.4 to
`R_{ab}V^a n^b = A θ̃`, hence `dE = (8πG)^{-1}A θ̃ Δ𝒜 ds = (8πG)^{-1}A d(Δ𝒜)` (Eq. 3.7) — which is exactly the
first law `dE = T dS` (Eq. 1.1) under `T = A/2π`, `S = 𝒜/4G`.

**The cone (§3.2).** The weaker condition (iv-b) lets the extrinsic curvature be nonzero but evolve as
`K̇̃_ab = −θ̃^c_b K̃_{ac}` (Eqs. 3.9, 3.11): the screen's extrinsic properties are locally those of a cone of
expansion `θ̃_ab`. For a cone section of radius `R(s)`, `k̃ = 1/R`, `Θ = R'/R`, this is `dk̃/ds = −Θ k̃`
(Eq. 3.10).

## Conclusions of the paper (§4)

Jacobson's null construction requires the null generators' initial expansion to vanish (an equilibrium
condition) and, via Raychaudhuri, the *derivative* of the expansion follows the first law. Piazza's timelike
construction is more involved but relates the **expansion itself** — not its derivative — directly to the
matter flux; the result therefore has the character of a **constraint**, not a dynamical equation. One can
follow the screen observers' thermodynamics **indefinitely**, whereas Jacobson's null generators cease to be
useful once they acquire nonzero expansion. The expansion is **positive if the matter flux is along the
acceleration, negative otherwise**. Physical picture: a screen of stationary observers around a star; throwing
in matter increases the enclosed mass, and the screen back-reacts (keeping the observers' acceleration fixed) by
the observers converging and falling inward — a "converging" effect that is **local and contained in Einstein's
equations**. Piazza reads this as a hint that gravity (and spacetime itself) may be **emergent**.

## What is formalized here vs. assumed

The genuinely *differential-geometric* facts — the **Ricci identity** `V_{a;cb} − V_{a;bc} = R_{acbd}V^d`, the
zero-vorticity decomposition (Eq. 2.1), Fermi transport (Eq. 2.3), and the orthogonalities `θ_ab V^b = 0`,
`V̇·V = 0` — are taken as **hypotheses** (they require a full covariant-calculus framework to derive from a
metric). What is mechanized below is the **contraction bookkeeping**: how the indexed terms combine and cancel,
proved by `Finset.sum` algebra over a finite index type. This file extends
`GaussCodazzi.ScreenThermodynamics` (the resulting scalar thermodynamics `dE = T dS`, Eqs. 1.1, 3.3–3.11) *down*
to the tensor manipulations that produce its geometric inputs.

## Correspondence (Lean ↔ paper)

| Lean | Paper | Role |
| --- | --- | --- |
| `symm_antisymm_contraction_zero` | mechanism behind Eqs. 2.7, 2.10 | symmetric × antisymmetric contraction vanishes |
| `riemann_S_orthogonal_V` | Eq. 2.7 (`S_ab` ⟂ `V`) | abstract Riemann antisymmetry version |
| `contraction_eq_2_5` | Eq. 2.5 (spatial part) | the `V`-longitudinal cross terms drop |
| `piazzaS`, `piazzaS_orthogonal_V` | Eq. 2.7 | `S_ab = R_{acbd}V^cV^d` ⟂ `V`, via the repo `Curvature.RiemannCurvatureTensor` |

## References

* F. Piazza, arXiv:1005.5151v2 — Eqs. (1.1), (2.1)–(2.3), (2.5), (2.7), (2.10), (2.11), (3.1)–(3.11).
* T. Jacobson, *"Thermodynamics of Spacetime: The Einstein Equation of State"*, Phys. Rev. Lett. **75** (1995)
  1260, arXiv:gr-qc/9504004 — the null-horizon `dE = T dS` (Piazza Eq. 1.1).
* `Physlib` (`Curvature.RiemannCurvatureTensor.IsRiemannCurvature` — the curvature symmetries proving §D's hypothesis;
  `GaussCodazzi.ScreenThermodynamics` — the scalar first law; `SpacetimePositiveMass` — the Gauss–Codazzi arc).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenTensorCalculus

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

open Finset in
/-- **[Symmetric × antisymmetric contraction vanishes]** `∑_{i,j} R_{ij} W^{ij} = 0` for an antisymmetric `R`
(`R_{ji} = −R_{ij}`) and a symmetric `W` (`W^{ji} = W^{ij}`).

*Reasoning (proof idea).* Relabelling the dummy indices `i ↔ j` (`Finset.sum_comm`) and then applying the
antisymmetry of `R` and symmetry of `W` turns the sum into its own negative, `S = −S`, so `S = 0`.

*Role in Piazza.* This is the algebraic mechanism by which every `V`-longitudinal term drops in the §2–3
calculation: a Riemann index pair is antisymmetric while the contracting `V^i V^j` is symmetric. It powers
`S_ab V^b = 0` (Eq. 2.7), the hypersurface-orthogonality constraint (Eq. 2.10), and `riemann_S_orthogonal_V` /
`piazzaS_orthogonal_V` below. -/
lemma symm_antisymm_contraction_zero {ι : Type*} [Fintype ι] (R W : ι → ι → ℝ)
    (hR : ∀ i j, R j i = -R i j) (hW : ∀ i j, W j i = W i j) :
    ∑ i, ∑ j, R i j * W i j = 0 := by
  have h : (∑ i, ∑ j, R i j * W i j) = -(∑ i, ∑ j, R i j * W i j) := by
    calc (∑ i, ∑ j, R i j * W i j)
        = ∑ i, ∑ j, R j i * W j i := Finset.sum_comm
      _ = ∑ i, ∑ j, -(R i j * W i j) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hR i j, hW i j]; ring
      _ = -(∑ i, ∑ j, R i j * W i j) := by simp only [Finset.sum_neg_distrib]
  linarith

/-- **[`S_ab` is orthogonal to `V` (Eq. 2.7)]** `∑_b (∑_d R_{·bd} V^d) V^b = 0` — the tidal tensor
`S_{ab} = R_{acbd}V^c V^d` contracted with `V^b` vanishes.

*Reasoning.* In Eq. 2.7 Piazza defines `S_ab = R_{acbd}V^c V^d` and remarks it "has components only in the
subspace orthogonal to `V`". Here the `(c,a)` indices are folded into `Riem`, leaving the antisymmetry in the
`(b,d)` pair (`Riem_{db} = −Riem_{bd}`); contracting it with the symmetric `V^b V^d` gives zero by
`symm_antisymm_contraction_zero`. Geometrically: `S_ab` lives on the spacelike screen slice `𝒮`, which is what
lets the calculation project the extrinsic curvature `K̃_ab` (Eq. 3.1). This is the abstract-hypothesis form;
`piazzaS_orthogonal_V` (§D) re-derives it from the genuine Riemann tensor. -/
lemma riemann_S_orthogonal_V {ι : Type*} [Fintype ι] (Riem : ι → ι → ℝ) (V : ι → ℝ)
    (hAnti : ∀ b d, Riem d b = -Riem b d) :
    ∑ b, (∑ d, Riem b d * V d) * V b = 0 := by
  have hstep : (∑ b, (∑ d, Riem b d * V d) * V b) = ∑ b, ∑ d, Riem b d * (V b * V d) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hstep]
  exact symm_antisymm_contraction_zero Riem (fun b d => V b * V d) hAnti (fun b d => by ring)

/-- **[The spatial contraction of Eq. 2.5]** `∑_c V^c_{;b} V_{a;c} = θ^c_b θ_ac − θ_ac V̇^c V_b`.

*Reasoning.* Eq. 2.5 expands `V̇_{a;b}` via the Leibniz rule on `V̇_a = V^c V_{a;c}` and the Ricci identity; the
term `V^c_{;b} V_{a;c}` is then evaluated by substituting the zero-vorticity decomposition `V_{a;b} = θ_ab −
V̇_a V_b` (Eq. 2.1) for both factors. Expanding the product gives four contractions, of which the two
`V`-longitudinal ones vanish by the orthogonalities `∑_c θ^c_b V_c = 0` (the expansion is purely spatial,
`θ_ab V^b = 0`) and `∑_c V̇^c V_c = 0` (the acceleration is orthogonal to the velocity, `V̇·V = 0`). What
survives is `θ^c_b θ_ac − θ_ac V̇^c V_b` — the first two terms of Eq. 2.5 (the remaining `V^c V_{a;bc} +
R_{acbd}V^c V^d` come from the Leibniz/Ricci step, taken here as the differential-geometric input). -/
lemma contraction_eq_2_5 {ι : Type*} [Fintype ι]
    (θb θa Vdotup Vlow : ι → ℝ) (Vb Vdota : ℝ)
    (hθV : ∑ c, θb c * Vlow c = 0) (hVdotV : ∑ c, Vdotup c * Vlow c = 0) :
    ∑ c, (θb c - Vdotup c * Vb) * (θa c - Vdota * Vlow c)
      = (∑ c, θb c * θa c) - Vb * ∑ c, θa c * Vdotup c := by
  have key : ∀ c, (θb c - Vdotup c * Vb) * (θa c - Vdota * Vlow c)
      = θb c * θa c - Vdota * (θb c * Vlow c) - Vb * (θa c * Vdotup c)
        + Vb * Vdota * (Vdotup c * Vlow c) := fun c => by ring
  rw [Finset.sum_congr rfl (fun c _ => key c)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hθV, hVdotV]
  ring

/-!

The abstract antisymmetry hypotheses of §A–§C are proved by the genuine algebraic symmetries of
`Curvature.RiemannCurvatureTensor.IsRiemannCurvature` (`antisymm_right`): Piazza's tidal tensor `S_{ab} = R_{acbd}V^c V^d`
(Eq. 2.7) is, for *any* real Riemann tensor, orthogonal to the velocity `V` — so it lives on the screen's
tangent space, exactly as Piazza needs to project the extrinsic curvature `K̃_ab`. -/

/-- **Piazza's tidal tensor** `S_{ab} = R_{acbd} V^c V^d` (Eq. 2.7), built from a genuine Riemann tensor
`Rm : RiemannTensor ι`. -/
noncomputable def piazzaS {ι : Type*} [Fintype ι] (Rm : RiemannTensor ι) (V : ι → ℝ) (a b : ι) : ℝ :=
  ∑ c, ∑ d, Rm a c b d * (V c * V d)

/-- **[`S_ab` is orthogonal to `V`, from the genuine Riemann antisymmetry]** `∑_b S_{ab} V^b = 0` — for any
`Rm` satisfying the curvature symmetries (`IsRiemannCurvature`), the antisymmetry in the last index pair
(`antisymm_right`, `R_{acbd} = −R_{acdb}`) makes the tidal tensor orthogonal to the screen velocity. This
proves the abstract hypothesis of `riemann_S_orthogonal_V` with the repository's real Riemann tensor,
linking Piazza's calculation (Eq. 2.7) to `Curvature.RiemannCurvatureTensor`. -/
lemma piazzaS_orthogonal_V {ι : Type*} [Fintype ι] {Rm : RiemannTensor ι}
    (h : IsRiemannCurvature Rm) (V : ι → ℝ) (a : ι) :
    ∑ b, piazzaS Rm V a b * V b = 0 := by
  unfold piazzaS
  have e1 : ∀ b, (∑ c, ∑ d, Rm a c b d * (V c * V d)) * V b
      = ∑ c, V c * ∑ d, Rm a c b d * (V b * V d) := by
    intro b
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_comm]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← Finset.mul_sum,
    symm_antisymm_contraction_zero (fun b d => Rm a c b d) (fun b d => V b * V d)
      (fun i j => by have := h.antisymm_right a c i j; linarith) (fun _ _ => by ring)]
  ring

end Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenTensorCalculus

end

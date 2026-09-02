/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

/-!
# Curved spacetimes from quantum mechanics (Szabados 2502.07668)

Szabados' *Curved spacetimes from quantum mechanics* (arXiv:2502.07668) extends *Minkowski space from quantum
mechanics* (arXiv:2309.06150, already formalized in `ComptonClock.PoincareCasimirMassShell`) from the flat to
the *curved* case: the local metric of a `C²` Lorentzian 4-manifold is recovered, in the classical limit, from
the empirical-distance observables of Poincaré-invariant quantum mechanics. The differential-geometric core is
that the **curvature at a point is determined by lengths of spacelike geodesics** — the length of a geodesic
"triangle" reads off the sectional curvature.

This module formalizes that core, on the flat tangent space `T_qM` with `η` the Minkowski metric there and `Rm`
the curvature tensor at `q`.

* **§A — the Riemann normal coordinate metric** (Eq. 2.1) `g_ab = η_ab − (t²/3)R_acdb X^cX^d`: the curved
  metric as a curvature perturbation of the flat tangent-space metric. `riemannNormalMetric_zero` (`t = 0 ⇒
  g = η`, flat at `q`) and `riemannNormalMetric_flat` (`Rm = 0 ⇒ g = η`, flat spacetime).
* **§B — the sectional curvature** `K = R_abcd X^aY^bX^cY^d`, a contraction of the library `RiemannTensor`.
* **§C — curvature from geodesic length** (Lemma 2.2.1, Eq. 2.7 to leading order) `L = tw(1 − (t²/6)K)`, and the
  inversion `curvature_from_geodesic_length` `K = 6(tw − L)/(t³w)` — the curvature *recovered from distances*,
  the paper's thesis. The flat limit `K = 0 ⇒ L = tw` recovers the Euclidean/Minkowski case of
  `PoincareCasimirMassShell`.
* **§D — the connection in RNC** (Eq. 2.2) `Γ^a_{bc} = (t/3)(R^a_{bcd}+R^a_{cbd})X^d`, torsion-free
  (`rncChristoffel_symm`) and vanishing at the base point (`rncChristoffel_zero`).
* **§E — parallel transport** (Eqs. 2.4/2.5) `parallelTransport` `P = 1 + (t²/6)R^a_{cdb}X^cX^d` and its inverse,
  the identity at `q` (`parallelTransport_zero`) and inverse to leading order (`parallelTransport_add_inv`).
* **§F — position-vector antisymmetry breaking** (Eq. 2.6) `translationDefect`
  `x̃^a + ξ^a = (1/6)R^a_{bcd}(x^b−ξ^b)ξ^cξ^d`, vanishing in flat space (`translationDefect_flat`).
* **§G — the tangent space at `q` is flat Minkowski** `base_point_flat`: at `t = 0`, `g = η`, `Γ = 0`, `P = 1`.
* **§H — distances as Lorentzian norms** (§3.2, Eqs. 3.5, 3.7). `distance_qr_eq_affineParameter`
  (`(D_{q,r})² = t²` for a unit spacelike `X`), `curvedSquaredDistance` `(D_{r₁,r₂})² = t²w²(1 − (t²/3)K)`,
  `squaredDistance_eq_length_sq` (`L² = D² + t⁶w²K²/36`, consistency with §C) and
  `sectionalCurvature_from_squaredDistance` (`K = 3(t²w² − D²)/(t⁴w²)`, curvature from the squared distance)
  and `curvedSquaredDistance_eq_zero_iff` (vanishing distance ⇔ point coincidence).
* **§I — spacetime points as pairs of timelike geodesics** (§3.1.2). `Meet` (`D(g,h) = 0`), `GeodesicPoint`
  (a point *is* a pair of intersecting geodesics), `Coincide` (Cor. 3.1.2 criterion), with `coincide_refl`
  and `coincide_symm` — the operational, quantum-implementable definition of spacetime points.
* **§J — curvature from purely spatial 2-surfaces** (Appendix A). `bilinearForm`, `sectionalArea` `A(X,Y)`,
  `normalizedSectionalCurvature` `K = R_{abcd}X^aY^bX^cY^d / A` (Eq. A.1) with
  `normalizedSectionalCurvature_orthonormal` (`A = 1` for a unit spacelike orthogonal pair),
  `sectionalCurvature_add_left`, `sectionalCurvaturePolar_symm` (via pair-exchange symmetry) and
  `sectionalCurvature_polarization` — Eq. A.3, recovering the mixed component `R_{abcd}X^aY^bZ^cY^d` as half the
  second difference of sectional-curvature numerators, i.e. spacelike sectional curvatures determine *every*
  curvature component.
* **§L — Theorem 4.2.1** (classical limit). `theorem_4_2_1_curvature_recovery` assembles the paper's headline
  result from §H: the radial squared distance is the affine parameter `t²` and the `r₁→r₂` squared distance
  recovers the sectional curvature `K` — the geometry the six Poincaré-invariant quantum subsystems converge to.

**Honest layering.** All exact algebra. The metric expansion (Eq. 2.1), the sectional-curvature contraction and
the geodesic-length inversion are the leading-order content of the paper's Lemma 2.2.1; the `O(t³)`/`O(w)` tails,
the full convex-normal-neighbourhood construction, and the quantum-mechanical classical-limit realization
(Theorem 4.2.1) are not carried out. At `Rm = 0` this reduces to the flat empirical-distance geometry of the
prequel (`PoincareCasimirMassShell`).
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.SzabadosCurvedSpacetime

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Matrix

variable {ι : Type*} [Fintype ι]


/-- **The curvature quadratic** `(R_acdb X^cX^d)_{ab}` — the leading curvature correction to the flat metric in
Riemann normal coordinates. -/
noncomputable def curvatureQuadratic (Rm : RiemannTensor ι) (X : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun a b => ∑ c, ∑ d, Rm a c d b * X c * X d

/-- **The Riemann normal coordinate metric** (Szabados Eq. 2.1) `g_ab(tX) = η_ab − (t²/3)R_acdb X^cX^d`: the
curved metric as a quadratic curvature perturbation of the flat tangent-space metric `η`, along the geodesic
`t ↦ exp_q(tX)`. -/
noncomputable def riemannNormalMetric (η : Matrix ι ι ℝ) (Rm : RiemannTensor ι) (t : ℝ) (X : ι → ℝ) :
    Matrix ι ι ℝ :=
  η - (t ^ 2 / 3) • curvatureQuadratic Rm X

/-- **[Flat at the base point] `g|_{t=0} = η`** — at `q` the metric is exactly the Minkowski tangent-space
metric. -/
lemma riemannNormalMetric_zero (η : Matrix ι ι ℝ) (Rm : RiemannTensor ι) (X : ι → ℝ) :
    riemannNormalMetric η Rm 0 X = η := by
  simp [riemannNormalMetric]

/-- **[Flat spacetime] `Rm = 0 ⇒ g = η`** — with vanishing curvature the metric is Minkowski everywhere; the
flat limit that recovers `PoincareCasimirMassShell`. -/
lemma riemannNormalMetric_flat (η : Matrix ι ι ℝ) (t : ℝ) (X : ι → ℝ) :
    riemannNormalMetric η (0 : RiemannTensor ι) t X = η := by
  ext a b
  simp [riemannNormalMetric, curvatureQuadratic, Matrix.sub_apply, Matrix.of_apply]


/-- **The sectional curvature** `K = R_abcd X^aY^bX^cY^d` of the 2-plane spanned by `X, Y` — the contraction of
the library `RiemannTensor` that Szabados' geodesic length reads off. -/
noncomputable def sectionalCurvature (Rm : RiemannTensor ι) (X Y : ι → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Rm a b c d * X a * Y b * X c * Y d

/-- **[Flat spacetime has zero sectional curvature] `Rm = 0 ⇒ K = 0`.** -/
lemma sectionalCurvature_flat (X Y : ι → ℝ) :
    sectionalCurvature (0 : RiemannTensor ι) X Y = 0 := by
  simp [sectionalCurvature]


/-- **The geodesic-triangle length** (Szabados Lemma 2.2.1, Eq. 2.7 to leading order)
`L = tw(1 − (t²/6)K)`, `K` the sectional curvature: the length of the spacelike geodesic `χ` closing the
triangle of two radial geodesics of parameter `t` separated by angle `w`. -/
noncomputable def sectionalGeodesicLength (t w K : ℝ) : ℝ := t * w * (1 - t ^ 2 * K / 6)

/-- **[Flat limit] `K = 0 ⇒ L = tw`** — for zero curvature the triangle length is the Euclidean/Minkowski
value, the flat empirical-distance geometry of `PoincareCasimirMassShell`. -/
lemma sectionalGeodesicLength_flat (t w : ℝ) : sectionalGeodesicLength t w 0 = t * w := by
  simp [sectionalGeodesicLength]

/-- **[Curvature from distances] `K = 6(tw − L)/(t³w)`** — inverting the geodesic-length formula recovers the
sectional curvature from the triangle length `L`. This is Szabados' thesis: the local curvature (hence, up to
third order, the metric) of a curved spacetime is *recovered from geodesic lengths* — the distance
observables of the quantum-mechanical system in the classical limit. -/
lemma curvature_from_geodesic_length (t w K : ℝ) (ht : t ≠ 0) (hw : w ≠ 0) :
    6 * (t * w - sectionalGeodesicLength t w K) / (t ^ 3 * w) = K := by
  unfold sectionalGeodesicLength
  field_simp
  ring

/-- **[The flat limit] `Rm = 0`: Minkowski metric and Euclidean triangle length** — with no curvature the
Riemann normal coordinate metric is the flat `η` and the geodesic-triangle length is `tw`, recovering the flat
empirical-distance geometry of the prequel `PoincareCasimirMassShell` (Minkowski from quantum mechanics). -/
lemma flat_limit (η : Matrix ι ι ℝ) (t w : ℝ) (X Y : ι → ℝ) :
    riemannNormalMetric η (0 : RiemannTensor ι) t X = η
      ∧ sectionalGeodesicLength t w (sectionalCurvature (0 : RiemannTensor ι) X Y) = t * w :=
  ⟨riemannNormalMetric_flat η t X,
    by rw [sectionalCurvature_flat]; exact sectionalGeodesicLength_flat t w⟩


/-- **The Christoffel symbols in Riemann normal coordinates** (Szabados Eq. 2.2)
`Γ^a_{bc}(tX) = (t/3)(R^a_{bcd} + R^a_{cbd})X^d` — linear in `t`, so they **vanish at the base point** `q`. -/
noncomputable def rncChristoffel (Rm : RiemannTensor ι) (t : ℝ) (X : ι → ℝ) (a b c : ι) : ℝ :=
  (t / 3) * ∑ d, (Rm a b c d + Rm a c b d) * X d

/-- **[The connection vanishes at the base point] `Γ|_{t=0} = 0`** — the defining property of Riemann normal
(geodesic) coordinates: the tangent space at `q` is flat Minkowski, curvature is an `O(t)` correction. -/
lemma rncChristoffel_zero (Rm : RiemannTensor ι) (X : ι → ℝ) (a b c : ι) :
    rncChristoffel Rm 0 X a b c = 0 := by
  simp [rncChristoffel]

/-- **[The connection is symmetric (torsion-free)] `Γ^a_{bc} = Γ^a_{cb}`.** -/
lemma rncChristoffel_symm (Rm : RiemannTensor ι) (t : ℝ) (X : ι → ℝ) (a b c : ι) :
    rncChristoffel Rm t X a b c = rncChristoffel Rm t X a c b := by
  unfold rncChristoffel
  congr 1
  exact Finset.sum_congr rfl fun d _ => by ring


variable [DecidableEq ι]

/-- **The parallel-transport operator** (Szabados Eq. 2.4) `P^a_b(tX) = δ^a_b + (t²/6)R^a_{cdb}X^cX^d` —
transports a vector from `q` to `exp_q(tX)` along the radial geodesic; the identity at the base point. -/
noncomputable def parallelTransport (Rm : RiemannTensor ι) (t : ℝ) (X : ι → ℝ) : Matrix ι ι ℝ :=
  1 + (t ^ 2 / 6) • curvatureQuadratic Rm X

/-- **The inverse parallel-transport operator** (Szabados Eq. 2.5) `δ^a_b − (t²/6)R^a_{cdb}X^cX^d`. -/
noncomputable def parallelTransportInv (Rm : RiemannTensor ι) (t : ℝ) (X : ι → ℝ) : Matrix ι ι ℝ :=
  1 - (t ^ 2 / 6) • curvatureQuadratic Rm X

/-- **[Parallel transport is the identity at the base point] `P|_{t=0} = 1`.** -/
lemma parallelTransport_zero (Rm : RiemannTensor ι) (X : ι → ℝ) :
    parallelTransport Rm 0 X = 1 := by
  simp [parallelTransport]

/-- **[`P` and `P⁻¹` are inverse to leading order] `P + P⁻¹ = 2·1`** — the `O(t²)` curvature corrections of the
transport operator and its inverse are exactly opposite. -/
lemma parallelTransport_add_inv (Rm : RiemannTensor ι) (t : ℝ) (X : ι → ℝ) :
    parallelTransport Rm t X + parallelTransportInv Rm t X = (1 : Matrix ι ι ℝ) + 1 := by
  simp only [parallelTransport, parallelTransportInv]
  abel


/-- **The translation defect** (Szabados Eq. 2.6) `x̃^a + ξ^a = (1/6)R^a_{bcd}(x^b − ξ^b)ξ^cξ^d` — in flat space
the position vector of `r` relative to `q̃` is minus that of `q̃` relative to `r`, but curvature destroys this
antisymmetry; this is the leading-order defect. -/
noncomputable def translationDefect (Rm : RiemannTensor ι) (ξ x : ι → ℝ) (a : ι) : ℝ :=
  (1 / 6) * ∑ b, ∑ c, ∑ d, Rm a b c d * (x b - ξ b) * ξ c * ξ d

omit [DecidableEq ι] in
/-- **[Flat space restores the antisymmetry] `Rm = 0 ⇒ defect = 0`** — the position vector is exactly
antisymmetric (`x̃ = −ξ`) only when curvature vanishes. -/
lemma translationDefect_flat (ξ x : ι → ℝ) (a : ι) :
    translationDefect (0 : RiemannTensor ι) ξ x a = 0 := by
  simp [translationDefect]


/-- **[The base point is flat] at `t = 0`: `g = η`, `Γ = 0`, `P = 1`** — all curvature corrections vanish at
`q`, so the tangent space `T_qM` is exactly flat Minkowski and the curvature emerges only as the `O(t)`/`O(t²)`
extra structure of `NewtonianLimitCurvatureAPI`-style perturbations. -/
lemma base_point_flat (η : Matrix ι ι ℝ) (Rm : RiemannTensor ι) (X : ι → ℝ) (a b c : ι) :
    riemannNormalMetric η Rm 0 X = η
      ∧ rncChristoffel Rm 0 X a b c = 0
      ∧ parallelTransport Rm 0 X = 1 :=
  ⟨riemannNormalMetric_zero η Rm X, rncChristoffel_zero Rm X a b c, parallelTransport_zero Rm X⟩


omit [DecidableEq ι] in
/-- **The Lorentzian norm** `η_ab X^aX^b` of a tangent vector — negative (`= −1`) for a unit *spacelike* `X`
in the `(+,−,−,−)` signature. -/
noncomputable def lorentzianNormSq (η : Matrix ι ι ℝ) (X : ι → ℝ) : ℝ :=
  ∑ a, ∑ b, η a b * X a * X b

omit [DecidableEq ι] in
/-- **[Distance to a radial point is the affine parameter] `(D_{q,r})² = t²`** (Szabados Eq. 3.5): the squared
distance from `q` to `r = exp_q(tX)` is minus `t²` times the Lorentzian norm of `X`; for a unit spacelike `X`
(`η_abX^aX^b = −1`) it is exactly `t²`, so the distance is the affine parameter `t`. -/
lemma distance_qr_eq_affineParameter (η : Matrix ι ι ℝ) (X : ι → ℝ) (t : ℝ)
    (hX : lorentzianNormSq η X = -1) : -(t ^ 2) * lorentzianNormSq η X = t ^ 2 := by
  rw [hX]; ring

/-- **The curved squared distance** between the two spatially separated points (Szabados Eq. 3.7)
`(D_{r₁,r₂})² = t²w²(1 − (t²/3)K)`, `K = R_abcd X^aY^bX^cY^d` the sectional curvature — the square of the
geodesic-triangle length of §C, and the Lorentzian-norm form that carries over into quantum theory. -/
noncomputable def curvedSquaredDistance (t w K : ℝ) : ℝ := t ^ 2 * w ^ 2 * (1 - t ^ 2 * K / 3)

/-- **[Flat limit] `K = 0 ⇒ (D_{r₁,r₂})² = t²w²`** — the Euclidean/Minkowski squared distance. -/
lemma curvedSquaredDistance_flat (t w : ℝ) : curvedSquaredDistance t w 0 = t ^ 2 * w ^ 2 := by
  simp [curvedSquaredDistance]

/-- **[Consistency of Eq. 3.7 with Eq. 2.7] `L² = D² + t⁶w²K²/36`** — the squared geodesic-triangle length
equals the curved squared distance up to an explicit `O(t⁶)` term, so `(D_{r₁,r₂})²` is `L[χ]²` to leading
order. -/
lemma squaredDistance_eq_length_sq (t w K : ℝ) :
    sectionalGeodesicLength t w K ^ 2 = curvedSquaredDistance t w K + t ^ 6 * w ^ 2 * K ^ 2 / 36 := by
  unfold sectionalGeodesicLength curvedSquaredDistance
  ring

/-- **[Curvature from the squared distance] `K = 3(t²w² − D²)/(t⁴w²)`** — inverting Eq. 3.7 recovers the
sectional curvature from the curved squared distance, the `(+,−,−,−)` Lorentzian-norm form of Szabados' thesis
(curvature, hence the metric, recovered from the distance observables). -/
lemma sectionalCurvature_from_squaredDistance (t w K : ℝ) (ht : t ≠ 0) (hw : w ≠ 0) :
    3 * (t ^ 2 * w ^ 2 - curvedSquaredDistance t w K) / (t ^ 4 * w ^ 2) = K := by
  unfold curvedSquaredDistance
  field_simp
  ring

/-- **[Vanishing distance] `(D_{r₁,r₂})² = 0 ⟺ t = 0 ∨ w = 0 ∨ t²K = 3`** — the two points coincide (`t = 0`
at `q`, or `w = 0` same radial geodesic) exactly when the curved squared distance vanishes; the extra root
`t²K = 3` is outside the small-neighbourhood regime. -/
lemma curvedSquaredDistance_eq_zero_iff (t w K : ℝ) :
    curvedSquaredDistance t w K = 0 ↔ t = 0 ∨ w = 0 ∨ 1 - t ^ 2 * K / 3 = 0 := by
  unfold curvedSquaredDistance
  rw [mul_eq_zero, mul_eq_zero, pow_eq_zero_iff (by norm_num), pow_eq_zero_iff (by norm_num)]
  tauto


section Points

variable {Geo : Type*} (d : Geo → Geo → ℝ)

/-- **Two timelike geodesics meet** (zero empirical distance) `D(g,h) = 0` — the criterion for their world
lines to intersect (Szabados §3.1.2). -/
def Meet (g h : Geo) : Prop := d g h = 0

/-- **A spacetime point** represented operationally as a pair of intersecting timelike geodesics (Szabados
§3.1.2): the event is the meeting of two freely-moving massive particles, `D₁₂ = 0`. Points are thereby
*derived* from geodesics and the empirical distance, implementable in quantum theory. -/
structure GeodesicPoint where
  /-- first timelike geodesic through the point. -/
  fst : Geo
  /-- second timelike geodesic through the point. -/
  snd : Geo
  /-- the two geodesics meet (vanishing empirical distance). -/
  meet : d fst snd = 0

/-- **The coincidence criterion** (Szabados Cor. 3.1.2): two geodesic-pair points are the *same* point iff all
four cross empirical distances vanish — an operational definition of point equality via the distance `d` and
the 4-momenta. -/
def Coincide (p q : GeodesicPoint d) : Prop :=
  d p.fst q.fst = 0 ∧ d p.fst q.snd = 0 ∧ d p.snd q.fst = 0 ∧ d p.snd q.snd = 0

/-- **[Coincidence is reflexive]** a point coincides with itself (self-distance zero, symmetric distance). -/
lemma coincide_refl (hself : ∀ g, d g g = 0) (hsymm : ∀ g h, d g h = d h g) (p : GeodesicPoint d) :
    Coincide d p p :=
  ⟨hself p.fst, p.meet, (hsymm p.snd p.fst).trans p.meet, hself p.snd⟩

/-- **[Coincidence is symmetric]** point coincidence is symmetric, from the symmetry of the empirical
distance. -/
lemma coincide_symm (hsymm : ∀ g h, d g h = d h g) {p q : GeodesicPoint d} (h : Coincide d p q) :
    Coincide d q p :=
  ⟨(hsymm q.fst p.fst).trans h.1, (hsymm q.fst p.snd).trans h.2.2.1,
    (hsymm q.snd p.fst).trans h.2.1, (hsymm q.snd p.snd).trans h.2.2.2⟩

end Points


/-- **The metric bilinear form** `⟨X,Y⟩ = g_{ab}X^aY^b`. -/
noncomputable def bilinearForm (g : Matrix ι ι ℝ) (X Y : ι → ℝ) : ℝ := ∑ a, ∑ b, g a b * X a * Y b

/-- **The 2-plane area** (Szabados Eq. A.1 denominator) `A(X,Y) = ⟨X,X⟩⟨Y,Y⟩ − ⟨X,Y⟩²` — nonzero iff the
2-plane spanned by `X, Y` is non-degenerate. -/
noncomputable def sectionalArea (g : Matrix ι ι ℝ) (X Y : ι → ℝ) : ℝ :=
  bilinearForm g X X * bilinearForm g Y Y - bilinearForm g X Y ^ 2

/-- **The normalized sectional curvature** (Szabados Eq. A.1) `K(X,Y) = R_{abcd}X^aY^bX^cY^d / A(X,Y)` of the
2-plane spanned by `X, Y` — depends only on the plane, not the spanning vectors. -/
noncomputable def normalizedSectionalCurvature (Rm : RiemannTensor ι) (g : Matrix ι ι ℝ) (X Y : ι → ℝ) : ℝ :=
  sectionalCurvature Rm X Y / sectionalArea g X Y

omit [DecidableEq ι] in
/-- **[Orthonormal spacelike 2-plane] `A = 1`, so `K(X,Y) = R_{abcd}X^aY^bX^cY^d`** — for unit spacelike vectors
`X, Y` orthogonal in the `(+,−,−,−)` metric (`⟨X,X⟩ = ⟨Y,Y⟩ = −1`, `⟨X,Y⟩ = 0`) the normalized sectional
curvature is just its numerator, so the geodesic-length contraction `R_{abcd}X^aY^bX^cY^d` *is* the sectional
curvature. -/
lemma normalizedSectionalCurvature_orthonormal (Rm : RiemannTensor ι) (g : Matrix ι ι ℝ) (X Y : ι → ℝ)
    (hXX : bilinearForm g X X = -1) (hYY : bilinearForm g Y Y = -1) (hXY : bilinearForm g X Y = 0) :
    normalizedSectionalCurvature Rm g X Y = sectionalCurvature Rm X Y := by
  unfold normalizedSectionalCurvature sectionalArea
  rw [hXX, hYY, hXY]
  norm_num

/-- **The polarized sectional curvature** `R_{abcd}X^aY^bZ^cY^d`. -/
noncomputable def sectionalCurvaturePolar (Rm : RiemannTensor ι) (X Z Y : ι → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Rm a b c d * X a * Y b * Z c * Y d

omit [DecidableEq ι] in
/-- **[Polarization of the sectional curvature] (Szabados Eq. A.3)**
`R_{abcd}(X+Z)^aY^b(X+Z)^cY^d = R_{abcd}X^aY^bX^cY^d + R_{abcd}Z^aY^bZ^cY^d + R_{abcd}X^aY^bZ^cY^d +
R_{abcd}Z^aY^bX^cY^d` — the curvature numerator is quadratic in its first argument, so its polarization
recovers the mixed component `R_{abcd}X^aY^bZ^cY^d`; the Appendix's route to *all* curvature components from the
purely spacelike sectional curvatures. -/
lemma sectionalCurvature_add_left (Rm : RiemannTensor ι) (X Z Y : ι → ℝ) :
    sectionalCurvature Rm (X + Z) Y = sectionalCurvature Rm X Y + sectionalCurvature Rm Z Y
      + sectionalCurvaturePolar Rm X Z Y + sectionalCurvaturePolar Rm Z X Y := by
  simp only [sectionalCurvature, sectionalCurvaturePolar, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

omit [DecidableEq ι] in
/-- **[The polarization, solved for the mixed pair] (Szabados Eq. A.3 form)**
`R_{abcd}(X+Z)^aY^b(X+Z)^cY^d − R_{abcd}X^aY^bX^cY^d − R_{abcd}Z^aY^bZ^cY^d = R_{abcd}X^aY^bZ^cY^d +
R_{abcd}Z^aY^bX^cY^d` — the sectional-curvature "second difference" is the symmetrized mixed component, the
route to all curvature components from the purely spacelike sectional curvatures. -/
lemma sectionalCurvature_second_difference (Rm : RiemannTensor ι) (X Z Y : ι → ℝ) :
    sectionalCurvature Rm (X + Z) Y - sectionalCurvature Rm X Y - sectionalCurvature Rm Z Y
      = sectionalCurvaturePolar Rm X Z Y + sectionalCurvaturePolar Rm Z X Y := by
  rw [sectionalCurvature_add_left]
  ring

omit [DecidableEq ι] in
/-- **[Pair-swap reindexing of a 4-fold sum]** `∑_{abcd} g(a,b,c,d) = ∑_{abcd} g(c,d,a,b)` — the sum is
invariant under swapping the two index pairs (a bijective reindexing over `ι×ι`). -/
lemma sum4_pair_swap {M : Type*} [AddCommMonoid M] (g : ι → ι → ι → ι → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, g a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, g c d a b := by
  have e1 : (∑ a, ∑ b, ∑ c, ∑ d, g a b c d)
      = ∑ p : ι × ι, ∑ q : ι × ι, g p.1 p.2 q.1 q.2 := by
    simp only [Fintype.sum_prod_type]
  have e2 : (∑ a, ∑ b, ∑ c, ∑ d, g c d a b)
      = ∑ q : ι × ι, ∑ p : ι × ι, g p.1 p.2 q.1 q.2 := by
    simp only [Fintype.sum_prod_type]
  rw [e1, e2, Finset.sum_comm]

omit [DecidableEq ι] in
/-- **[The polarized sectional curvature is symmetric in `X, Z`] `R_{abcd}X^aY^bZ^cY^d = R_{abcd}Z^aY^bX^cY^d`**
— by the pair-exchange symmetry `R_{abcd} = R_{cdab}` of a genuine Riemann tensor. -/
lemma sectionalCurvaturePolar_symm (Rm : RiemannTensor ι) (h : IsRiemannCurvature Rm)
    (X Z Y : ι → ℝ) : sectionalCurvaturePolar Rm X Z Y = sectionalCurvaturePolar Rm Z X Y := by
  simp only [sectionalCurvaturePolar]
  rw [sum4_pair_swap (fun a b c d => Rm a b c d * X a * Y b * Z c * Y d)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [h.pair_symm c d a b]
  ring

omit [DecidableEq ι] in
/-- **[Curvature from sectional curvatures] (Szabados Eq. A.3)**
`R_{abcd}X^aY^bZ^cY^d = ½(R_{abcd}(X+Z)^aY^b(X+Z)^cY^d − R_{abcd}X^aY^bX^cY^d − R_{abcd}Z^aY^bZ^cY^d)` — the
mixed curvature component is recovered as half the second difference of the sectional-curvature numerators. With
`normalizedSectionalCurvature` this is the Appendix's statement that the purely spacelike sectional curvatures
determine *every* component of the Riemann tensor. -/
lemma sectionalCurvature_polarization (Rm : RiemannTensor ι) (h : IsRiemannCurvature Rm)
    (X Z Y : ι → ℝ) :
    sectionalCurvaturePolar Rm X Z Y
      = (sectionalCurvature Rm (X + Z) Y - sectionalCurvature Rm X Y - sectionalCurvature Rm Z Y) / 2 := by
  rw [sectionalCurvature_second_difference, sectionalCurvaturePolar_symm Rm h Z X Y]
  ring


omit [DecidableEq ι] in
/-- **[Szabados Theorem 4.2.1, classical limit] the three-point configuration recovers the curvature.**
Given `q`, `r₁ = exp_q(tX)`, `r₂ = exp_q(tX(w))` with `X` a unit spacelike vector (`⟨X,X⟩ = −1`), the radial
squared distance from `q` to a radial point is the affine parameter `t²` (Eqs. 4.11–4.12), and the `r₁→r₂`
squared distance `curvedSquaredDistance t w K` recovers the sectional curvature `K = 3(t²w² − D²)/(t⁴w²)`
(Eq. 4.13). This is the geometric skeleton of the paper's headline theorem: the local metric of a curved
Lorentzian spacetime is *defined* by the empirical distances of six Poincaré-invariant quantum systems. The
quantum implementation — the six subsystems' empirical-distance operators `d²_ij` built from the centre-of-mass
operators `C^a = J^{ab}p_b − (3/2)iℏp^a` (Eqs. 4.2–4.4) — needs Hilbert-space machinery and is not formalized;
the geometry it converges to is exactly this pair of identities. -/
lemma theorem_4_2_1_curvature_recovery (η : Matrix ι ι ℝ) (X : ι → ℝ) (t w K : ℝ)
    (ht : t ≠ 0) (hw : w ≠ 0) (hX : lorentzianNormSq η X = -1) :
    -(t ^ 2) * lorentzianNormSq η X = t ^ 2
      ∧ 3 * (t ^ 2 * w ^ 2 - curvedSquaredDistance t w K) / (t ^ 4 * w ^ 2) = K :=
  ⟨distance_qr_eq_affineParameter η X t hX, sectionalCurvature_from_squaredDistance t w K ht hw⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.SzabadosCurvedSpacetime

end

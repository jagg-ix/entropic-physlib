/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Intrinsic Levi-Civita connections for pseudo-Riemannian metrics

This file supplies the coordinate-free uniqueness layer needed to glue chartwise
Levi-Civita constructions. Metric compatibility is stated using the manifold
derivative of the scalar pairing, and torsion-freeness uses Mathlib's bundled
torsion tensor.

The main results are:

* `PseudoRiemannianMetric.IsCompatibleConnection`, intrinsic metric compatibility;
* `PseudoRiemannianMetric.IsLeviCivitaConnection`, the global Levi-Civita predicate;
* `PseudoRiemannianMetric.leviCivita_pairing_mfderiv_eq_zero_of_parallel`,
  preservation of the metric pairing of parallel fields;
* `PseudoRiemannianMetric.koszul`, the coordinate-free Koszul identity;
* `PseudoRiemannianMetric.leviCivita_unique_on_smooth`, uniqueness on smooth fields;
* `PseudoRiemannianMetric.leviCivitaAtlas_overlap`, agreement of chart representatives.

The uniqueness theorem is intentionally stated on differentiable vector fields.
Mathlib's `CovariantDerivative` axioms constrain connection actions on smooth
sections, so equality on arbitrary nonsmooth sections would be stronger than the
bundled interface warrants.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle Set FiberBundle
open scoped Manifold ContDiff

namespace PseudoRiemannianMetric

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

/-! ## A. Intrinsic metric compatibility -/

/-- A bundled connection preserves a pseudo-Riemannian metric on differentiable
vector fields. The explicit `fromTangentSpace` map identifies the tangent space
of the scalar target with `ℝ`. -/
def IsCompatibleConnection (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ (X Y Z : ∀ x : M, TangentSpace I x) (x : M),
    MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      NormedSpace.fromTangentSpace
          (g.val x (Y x) (Z x))
          (mfderiv I 𝓘(ℝ) (fun y => g.val y (Y y) (Z y)) x (X x)) =
        g.val x (cov Y x (X x)) (Z x) +
          g.val x (Y x) (cov Z x (X x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Metric compatibility makes the directional derivative of the pairing of
two parallel vector fields vanish. This is the local conservation law behind
preservation of momentum norms and momentum--velocity pairings under transport. -/
lemma pairing_mfderiv_eq_zero_of_parallel
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : IsCompatibleConnection I g cov)
    (X Y Z : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x)
    (hparallelY : cov Y x (X x) = 0)
    (hparallelZ : cov Z x (X x) = 0) :
    NormedSpace.fromTangentSpace
        (g.val x (Y x) (Z x))
        (mfderiv I 𝓘(ℝ) (fun y => g.val y (Y y) (Z y)) x (X x)) = 0 := by
  rw [hcov X Y Z x hX hY hZ, hparallelY, hparallelZ]
  simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- In particular, the metric self-pairing of a parallel vector field has
zero directional derivative. For four-momentum this is local mass-shell
preservation by a metric-compatible connection. -/
lemma selfPairing_mfderiv_eq_zero_of_parallel
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : IsCompatibleConnection I g cov)
    (X Y : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hparallel : cov Y x (X x) = 0) :
    NormedSpace.fromTangentSpace
        (g.val x (Y x) (Y x))
        (mfderiv I 𝓘(ℝ) (fun y => g.val y (Y y) (Y y)) x (X x)) = 0 :=
  pairing_mfderiv_eq_zero_of_parallel I g cov hcov X Y Y x
    hX hY hY hparallel hparallel

/-- A global Levi-Civita connection is torsion-free and metric-compatible. -/
def IsLeviCivitaConnection (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  cov.torsion = 0 ∧ IsCompatibleConnection I g cov

/-- Levi--Civita-parallel vector fields preserve their metric pairing in every
differentiable direction. Applied to momentum and four-velocity, this gives
the local covariant conservation of their phase-rate pairing. -/
lemma leviCivita_pairing_mfderiv_eq_zero_of_parallel
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : IsLeviCivitaConnection I g cov)
    (X Y Z : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x)
    (hparallelY : cov Y x (X x) = 0)
    (hparallelZ : cov Z x (X x) = 0) :
    NormedSpace.fromTangentSpace
        (g.val x (Y x) (Z x))
        (mfderiv I 𝓘(ℝ) (fun y => g.val y (Y y) (Z y)) x (X x)) = 0 :=
  pairing_mfderiv_eq_zero_of_parallel I g cov hcov.2 X Y Z x
    hX hY hZ hparallelY hparallelZ

/-! ## B. Koszul identity -/

/-- A global torsion-free metric connection obeys the coordinate-free Koszul
formula. This determines its action from the metric and Lie brackets alone. -/
lemma koszul (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : IsLeviCivitaConnection I g cov)
    (X Y Z : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    2 * g.val x (cov Y x (X x)) (Z x) =
      NormedSpace.fromTangentSpace (g.val x (Y x) (Z x))
        (mfderiv I 𝓘(ℝ) (fun y => g.val y (Y y) (Z y)) x (X x)) +
      NormedSpace.fromTangentSpace (g.val x (Z x) (X x))
        (mfderiv I 𝓘(ℝ) (fun y => g.val y (Z y) (X y)) x (Y x)) -
      NormedSpace.fromTangentSpace (g.val x (X x) (Y x))
        (mfderiv I 𝓘(ℝ) (fun y => g.val y (X y) (Y y)) x (Z x)) +
      g.val x (VectorField.mlieBracket I X Y x) (Z x) -
      g.val x (VectorField.mlieBracket I X Z x) (Y x) -
      g.val x (VectorField.mlieBracket I Y Z x) (X x) := by
  have hcX := hcov.2 X Y Z x hX hY hZ
  have hcY := hcov.2 Y Z X x hY hZ hX
  have hcZ := hcov.2 Z X Y x hZ hX hY
  have htXY := (CovariantDerivative.torsion_eq_zero_iff cov).mp hcov.1 hX hY
  have htXZ := (CovariantDerivative.torsion_eq_zero_iff cov).mp hcov.1 hX hZ
  have htYZ := (CovariantDerivative.torsion_eq_zero_iff cov).mp hcov.1 hY hZ
  have htXYg := congrArg (fun v => g.val x v (Z x)) htXY
  have htXZg := congrArg (fun v => g.val x v (Y x)) htXZ
  have htYZg := congrArg (fun v => g.val x v (X x)) htYZ
  simp only [map_sub, sub_apply] at htXYg htXZg htYZg
  rw [g.symm x (Y x) (cov Z x (X x))] at hcX
  rw [g.symm x (Z x) (cov X x (Y x))] at hcY
  rw [g.symm x (X x) (cov Y x (Z x))] at hcZ
  linarith

/-! ## C. Levi-Civita uniqueness -/

/-- The difference of two Levi-Civita connections is symmetric in its two
vector-field inputs. -/
lemma leviCivita_difference_symm (g : PseudoRiemannianMetric E H M n I)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : IsLeviCivitaConnection I g cov)
    (hcov' : IsLeviCivitaConnection I g cov')
    (X Y : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov' Y x (X x) =
      cov X x (Y x) - cov' X x (Y x) := by
  have htor := (CovariantDerivative.torsion_eq_zero_iff cov).mp hcov.1 hX hY
  have htor' := (CovariantDerivative.torsion_eq_zero_iff cov').mp hcov'.1 hX hY
  calc
    cov Y x (X x) - cov' Y x (X x) =
        (cov Y x (X x) - cov X x (Y x)) -
          (cov' Y x (X x) - cov' X x (Y x)) +
          (cov X x (Y x) - cov' X x (Y x)) := by abel
    _ = cov X x (Y x) - cov' X x (Y x) := by rw [htor, htor']; simp

/-- Metric compatibility makes the difference of two Levi-Civita connections
skew-adjoint in its final two slots. -/
lemma leviCivita_difference_metric_skew
    (g : PseudoRiemannianMetric E H M n I)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : IsLeviCivitaConnection I g cov)
    (hcov' : IsLeviCivitaConnection I g cov')
    (X Y Z : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.val x (cov Y x (X x) - cov' Y x (X x)) (Z x) =
      -g.val x (cov Z x (X x) - cov' Z x (X x)) (Y x) := by
  have h := hcov.2 X Y Z x hX hY hZ
  have h' := hcov'.2 X Y Z x hX hY hZ
  have hsub :
      g.val x (cov Y x (X x)) (Z x) -
          g.val x (cov' Y x (X x)) (Z x) =
        -(g.val x (Y x) (cov Z x (X x)) -
          g.val x (Y x) (cov' Z x (X x))) := by
    have hsums := h.symm.trans h'
    calc
      _ = (g.val x (cov Y x (X x)) (Z x) +
            g.val x (Y x) (cov Z x (X x))) -
          (g.val x (cov' Y x (X x)) (Z x) +
            g.val x (Y x) (cov' Z x (X x))) -
          (g.val x (Y x) (cov Z x (X x)) -
            g.val x (Y x) (cov' Z x (X x))) := by ring
      _ = -(g.val x (Y x) (cov Z x (X x)) -
            g.val x (Y x) (cov' Z x (X x))) := by rw [hsums]; ring
  rw [g.symm x (Y x) (cov Z x (X x)),
    g.symm x (Y x) (cov' Z x (X x))] at hsub
  simpa only [map_sub, sub_apply] using hsub

/-- Levi-Civita uniqueness on differentiable vector fields. Nondegeneracy of
the pseudo-Riemannian metric converts equality of all scalar pairings into
equality of the connection actions. -/
theorem leviCivita_unique_on_smooth
    (g : PseudoRiemannianMetric E H M n I)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : IsLeviCivitaConnection I g cov)
    (hcov' : IsLeviCivitaConnection I g cov')
    (X Y : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = cov' Y x (X x) := by
  let A : TangentSpace I x := cov Y x (X x) - cov' Y x (X x)
  apply sub_eq_zero.mp
  apply g.nondegenerate x A
  intro z
  let Z := extend E z
  have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend I E z
  have h1 := leviCivita_difference_metric_skew I g cov cov' hcov hcov'
    X Y Z x hX hY hZ
  have h2 := leviCivita_difference_symm I g cov cov' hcov hcov' X Y x hX hY
  have h4 := leviCivita_difference_symm I g cov cov' hcov hcov' X Z x hX hZ
  have h5 := leviCivita_difference_metric_skew I g cov cov' hcov hcov'
    Z X Y x hZ hX hY
  have h6 := leviCivita_difference_symm I g cov cov' hcov hcov' Z Y x hZ hY
  have h7 := leviCivita_difference_metric_skew I g cov cov' hcov hcov'
    Y Z X x hY hZ hX
  have hz : Z x = z := by simp [Z]
  dsimp [A]
  rw [← hz]
  have hneg :
      g.val x (cov Y x (X x) - cov' Y x (X x)) (Z x) =
        -g.val x (cov Y x (X x) - cov' Y x (X x)) (Z x) := by
    calc
      _ = -g.val x (cov Z x (X x) - cov' Z x (X x)) (Y x) := h1
      _ = -g.val x (cov X x (Z x) - cov' X x (Z x)) (Y x) := by rw [h4]
      _ = g.val x (cov Y x (Z x) - cov' Y x (Z x)) (X x) := by rw [h5]; simp
      _ = g.val x (cov Z x (Y x) - cov' Z x (Y x)) (X x) := by rw [h6]
      _ = -g.val x (cov X x (Y x) - cov' X x (Y x)) (Z x) := h7
      _ = -g.val x (cov Y x (X x) - cov' Y x (X x)) (Z x) := by rw [h2]
  linarith

/-! ## D. Atlas compatibility and coordinate independence -/

/-- An atlas-indexed family whose representatives are all global
Levi-Civita connections for the same pseudo-Riemannian metric. -/
def IsLeviCivitaAtlas {α : Type*} (g : PseudoRiemannianMetric E H M n I)
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ a, IsLeviCivitaConnection I g (cov a)

/-- Two Levi-Civita representatives from an atlas agree on every overlap point
where the vector fields are differentiable. This is the intrinsic chart-
independence theorem for the connection action. -/
theorem leviCivitaAtlas_overlap (g : PseudoRiemannianMetric E H M n I)
    {α : Type*}
    (cov : α → CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g cov) (a b : α)
    (X Y : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov a Y x (X x) = cov b Y x (X x) :=
  leviCivita_unique_on_smooth I g (cov a) (cov b)
    (hatlas a) (hatlas b) X Y x hX hY

/-! ## E. Globalization from a compatible open cover -/

/-- Metric compatibility for a raw connection operator on a subset of the
manifold. -/
def IsCompatibleConnectionOn (g : PseudoRiemannianMetric E H M n I)
    (raw : (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (s : Set M) : Prop :=
  ∀ (X Y Z : ∀ x : M, TangentSpace I x) (x : M), x ∈ s →
    MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      NormedSpace.fromTangentSpace
          (g.val x (Y x) (Z x))
          (mfderiv I 𝓘(ℝ) (fun y => g.val y (Y y) (Z y)) x (X x)) =
        g.val x (raw Y x (X x)) (Z x) +
          g.val x (Y x) (raw Z x (X x))

/-- Torsion-freeness for a raw connection operator on a subset, expressed on
differentiable vector fields. -/
def IsTorsionFreeConnectionOn
    (raw : (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (s : Set M) : Prop :=
  ∀ (X Y : ∀ x : M, TangentSpace I x) (x : M), x ∈ s →
    MDiffAt (T% X) x → MDiffAt (T% Y) x →
      raw Y x (X x) - raw X x (Y x) = VectorField.mlieBracket I X Y x

/-- Assemble a global connection from one raw operator verified to be a
connection on every member of an open cover. The overlap agreement is encoded
by using the same raw operator on all cover members. -/
noncomputable def leviCivitaOfOpenCover {α : Type*} {s : α → Set M}
    {raw : (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hraw : ∀ a, IsCovariantDerivativeOn E raw (s a))
    (hcover : ⋃ a, s a = Set.univ) :
    CovariantDerivative I E (TangentSpace I : M → Type _) :=
  CovariantDerivative.of_isCovariantDerivativeOn_of_open_cover hraw hcover

/-- Compatible torsion-free local data for one overlap-consistent raw operator
globalize to a genuine bundled Levi-Civita connection. -/
theorem leviCivitaOfOpenCover_isLeviCivita
    (g : PseudoRiemannianMetric E H M n I)
    {α : Type*} {s : α → Set M}
    {raw : (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hraw : ∀ a, IsCovariantDerivativeOn E raw (s a))
    (hcover : ⋃ a, s a = Set.univ)
    (htor : ∀ a, IsTorsionFreeConnectionOn I raw (s a))
    (hmetric : ∀ a, IsCompatibleConnectionOn I g raw (s a)) :
    IsLeviCivitaConnection I g
      (leviCivitaOfOpenCover I hraw hcover) := by
  constructor
  · rw [CovariantDerivative.torsion_eq_zero_iff]
    intro X Y x hX hY
    have hx : x ∈ ⋃ a, s a := by rw [hcover]; trivial
    simp only [Set.mem_iUnion] at hx
    obtain ⟨a, ha⟩ := hx
    exact htor a X Y x ha hX hY
  · intro X Y Z x hX hY hZ
    have hx : x ∈ ⋃ a, s a := by rw [hcover]; trivial
    simp only [Set.mem_iUnion] at hx
    obtain ⟨a, ha⟩ := hx
    exact hmetric a X Y Z x ha hX hY hZ

/-! ## F. Globalization of genuinely chart-local data -/

/-- The local Levi-Civita conditions for a raw connection operator on a subset.
Unlike `IsLeviCivitaConnection`, this predicate does not require the operator to
be bundled globally. -/
def IsLeviCivitaConnectionOn (g : PseudoRiemannianMetric E H M n I)
    (raw : (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (s : Set M) : Prop :=
  IsCovariantDerivativeOn E raw s ∧
    IsTorsionFreeConnectionOn I raw s ∧ IsCompatibleConnectionOn I g raw s

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- On an overlap, the difference of two local Levi-Civita operators is
symmetric in its two vector-field inputs. -/
lemma localLeviCivita_difference_symm
    (g : PseudoRiemannianMetric E H M n I)
    {raw raw' : (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    {s t : Set M} (hraw : IsLeviCivitaConnectionOn I g raw s)
    (hraw' : IsLeviCivitaConnectionOn I g raw' t)
    (X Y : ∀ x : M, TangentSpace I x) (x : M) (hxs : x ∈ s) (hxt : x ∈ t)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    raw Y x (X x) - raw' Y x (X x) = raw X x (Y x) - raw' X x (Y x) := by
  have htor := hraw.2.1 X Y x hxs hX hY
  have htor' := hraw'.2.1 X Y x hxt hX hY
  calc
    raw Y x (X x) - raw' Y x (X x) =
        (raw Y x (X x) - raw X x (Y x)) -
          (raw' Y x (X x) - raw' X x (Y x)) +
          (raw X x (Y x) - raw' X x (Y x)) := by abel
    _ = raw X x (Y x) - raw' X x (Y x) := by rw [htor, htor']; simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- On an overlap, metric compatibility makes the difference of two local
Levi-Civita operators skew-adjoint in its final two slots. -/
lemma localLeviCivita_difference_metric_skew
    (g : PseudoRiemannianMetric E H M n I)
    {raw raw' : (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    {s t : Set M} (hraw : IsLeviCivitaConnectionOn I g raw s)
    (hraw' : IsLeviCivitaConnectionOn I g raw' t)
    (X Y Z : ∀ x : M, TangentSpace I x) (x : M) (hxs : x ∈ s) (hxt : x ∈ t)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.val x (raw Y x (X x) - raw' Y x (X x)) (Z x) =
      -g.val x (raw Z x (X x) - raw' Z x (X x)) (Y x) := by
  have h := hraw.2.2 X Y Z x hxs hX hY hZ
  have h' := hraw'.2.2 X Y Z x hxt hX hY hZ
  have hsub :
      g.val x (raw Y x (X x)) (Z x) - g.val x (raw' Y x (X x)) (Z x) =
        -(g.val x (Y x) (raw Z x (X x)) -
          g.val x (Y x) (raw' Z x (X x))) := by
    have hsums := h.symm.trans h'
    calc
      _ = (g.val x (raw Y x (X x)) (Z x) + g.val x (Y x) (raw Z x (X x))) -
          (g.val x (raw' Y x (X x)) (Z x) + g.val x (Y x) (raw' Z x (X x))) -
          (g.val x (Y x) (raw Z x (X x)) -
            g.val x (Y x) (raw' Z x (X x))) := by ring
      _ = -(g.val x (Y x) (raw Z x (X x)) -
            g.val x (Y x) (raw' Z x (X x))) := by rw [hsums]; ring
  rw [g.symm x (Y x) (raw Z x (X x)),
    g.symm x (Y x) (raw' Z x (X x))] at hsub
  simpa only [map_sub, sub_apply] using hsub

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Two local Levi-Civita operators agree at every point of their overlap on
differentiable vector fields. This is the local form of Levi-Civita uniqueness
needed to glue independently constructed chart connections. -/
lemma localLeviCivita_uniqueAt
    (g : PseudoRiemannianMetric E H M n I)
    {raw raw' : (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    {s t : Set M} (hraw : IsLeviCivitaConnectionOn I g raw s)
    (hraw' : IsLeviCivitaConnectionOn I g raw' t)
    (X Y : ∀ x : M, TangentSpace I x) (x : M) (hxs : x ∈ s) (hxt : x ∈ t)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    raw Y x (X x) = raw' Y x (X x) := by
  let A : TangentSpace I x := raw Y x (X x) - raw' Y x (X x)
  apply sub_eq_zero.mp
  apply g.nondegenerate x A
  intro z
  let Z := extend E z
  have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend I E z
  have h1 := localLeviCivita_difference_metric_skew I g hraw hraw'
    X Y Z x hxs hxt hX hY hZ
  have h2 := localLeviCivita_difference_symm I g hraw hraw'
    X Y x hxs hxt hX hY
  have h4 := localLeviCivita_difference_symm I g hraw hraw'
    X Z x hxs hxt hX hZ
  have h5 := localLeviCivita_difference_metric_skew I g hraw hraw'
    Z X Y x hxs hxt hZ hX hY
  have h6 := localLeviCivita_difference_symm I g hraw hraw'
    Z Y x hxs hxt hZ hY
  have h7 := localLeviCivita_difference_metric_skew I g hraw hraw'
    Y Z X x hxs hxt hY hZ hX
  have hz : Z x = z := by simp [Z]
  dsimp [A]
  rw [← hz]
  have hneg :
      g.val x (raw Y x (X x) - raw' Y x (X x)) (Z x) =
        -g.val x (raw Y x (X x) - raw' Y x (X x)) (Z x) := by
    calc
      _ = -g.val x (raw Z x (X x) - raw' Z x (X x)) (Y x) := h1
      _ = -g.val x (raw X x (Z x) - raw' X x (Z x)) (Y x) := by rw [h4]
      _ = g.val x (raw Y x (Z x) - raw' Y x (Z x)) (X x) := by rw [h5]; simp
      _ = g.val x (raw Z x (Y x) - raw' Z x (Y x)) (X x) := by rw [h6]
      _ = -g.val x (raw X x (Y x) - raw' X x (Y x)) (Z x) := h7
      _ = -g.val x (raw Y x (X x) - raw' Y x (X x)) (Z x) := by rw [h2]
  linarith

/-- Chart-local Levi-Civita data for a pseudo-Riemannian metric. Each chart
supplies its own raw connection operator; no overlap equality is assumed,
because local Levi-Civita uniqueness derives it. -/
structure LocalLeviCivitaAtlasData (g : PseudoRiemannianMetric E H M n I)
    (α : Type*) where
  /-- The source of each chart-local connection. -/
  source : α → Set M
  /-- The raw connection operator constructed in each chart. -/
  raw : α → (∀ x : M, TangentSpace I x) →
    ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x
  /-- The chart sources cover the manifold. -/
  cover : ⋃ a, source a = Set.univ
  /-- Every chart operator satisfies the local Levi-Civita conditions. -/
  isLeviCivitaOn : ∀ a, IsLeviCivitaConnectionOn I g (raw a) (source a)

namespace LocalLeviCivitaAtlasData

variable {α : Type*} {g : PseudoRiemannianMetric E H M n I}

/-- Choose a chart containing a point of a local Levi-Civita atlas. -/
noncomputable def chartAt (D : LocalLeviCivitaAtlasData I g α) (x : M) : α :=
  Classical.choose (show ∃ a, x ∈ D.source a by
    have hx : x ∈ ⋃ a, D.source a := by rw [D.cover]; trivial
    simpa only [Set.mem_iUnion] using hx)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The selected chart contains the point at which it was selected. -/
lemma chartAt_mem (D : LocalLeviCivitaAtlasData I g α) (x : M) :
    x ∈ D.source (D.chartAt (I := I) x) :=
  Classical.choose_spec (show ∃ a, x ∈ D.source a by
    have hx : x ∈ ⋃ a, D.source a := by rw [D.cover]; trivial
    simpa only [Set.mem_iUnion] using hx)

/-- Select the chart-local connection at each point. Overlap uniqueness will
show that its action on smooth fields is independent of this choice. -/
noncomputable def selectedRaw (D : LocalLeviCivitaAtlasData I g α) :
    (∀ x : M, TangentSpace I x) →
      ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
  fun Y x ↦ D.raw (D.chartAt (I := I) x) Y x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The pointwise-selected local operator satisfies the global covariant-
derivative laws. -/
lemma selectedRaw_isCovariantDerivativeOn
    (D : LocalLeviCivitaAtlasData I g α) :
    IsCovariantDerivativeOn E (D.selectedRaw (I := I)) Set.univ := by
  constructor
  · intro σ σ' x hσ hσ' _
    exact (D.isLeviCivitaOn (D.chartAt (I := I) x)).1.add hσ hσ'
      (D.chartAt_mem (I := I) x)
  · intro σ f x hσ hf _
    exact (D.isLeviCivitaOn (D.chartAt (I := I) x)).1.leibniz hσ hf
      (D.chartAt_mem (I := I) x)

/-- The global covariant derivative selected from chart-local Levi-Civita
data. -/
noncomputable def covariantDerivative (D : LocalLeviCivitaAtlasData I g α) :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := D.selectedRaw (I := I)
  isCovariantDerivativeOnUniv := D.selectedRaw_isCovariantDerivativeOn (I := I)

/-- Globalize the overlap-compatible pointwise selection through Mathlib's
open-cover constructor. Each cover member inherits the covariant-derivative
laws from `selectedRaw_isCovariantDerivativeOn`; `D.cover` supplies the actual
covering equality. -/
noncomputable def covariantDerivativeOfOpenCover
    (D : LocalLeviCivitaAtlasData I g α) :
    CovariantDerivative I E (TangentSpace I : M → Type _) :=
  leviCivitaOfOpenCover I
    (fun _ => (D.selectedRaw_isCovariantDerivativeOn (I := I)).mono
      (Set.subset_univ _)) D.cover

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The open-cover globalization is the same bundled connection as the direct
global bundling of the selected raw operator. In particular, feeding the
overlap-compatible atlas into Mathlib's constructor introduces no new chart
choice. -/
lemma covariantDerivativeOfOpenCover_eq_covariantDerivative
    (D : LocalLeviCivitaAtlasData I g α) :
    D.covariantDerivativeOfOpenCover (I := I) =
      D.covariantDerivative (I := I) := by
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The selected global connection agrees with every chart representative at
points in that chart, on differentiable vector fields. -/
lemma covariantDerivative_eq_chartAt
    (D : LocalLeviCivitaAtlasData I g α) (a : α)
    (X Y : ∀ x : M, TangentSpace I x) (x : M) (hx : x ∈ D.source a)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    D.covariantDerivative (I := I) Y x (X x) = D.raw a Y x (X x) :=
  localLeviCivita_uniqueAt I g (D.isLeviCivitaOn (D.chartAt (I := I) x))
    (D.isLeviCivitaOn a) X Y x (D.chartAt_mem (I := I) x) hx hX hY

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Independently constructed chart Levi-Civita operators agree on chart
overlaps. -/
lemma overlap
    (D : LocalLeviCivitaAtlasData I g α) (a b : α)
    (X Y : ∀ x : M, TangentSpace I x) (x : M)
    (ha : x ∈ D.source a) (hb : x ∈ D.source b)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    D.raw a Y x (X x) = D.raw b Y x (X x) :=
  localLeviCivita_uniqueAt I g (D.isLeviCivitaOn a)
    (D.isLeviCivitaOn b) X Y x ha hb hX hY

/-- A chart-local Levi-Civita atlas determines a genuine global
Levi-Civita connection. -/
theorem covariantDerivative_isLeviCivita
    (D : LocalLeviCivitaAtlasData I g α) :
    IsLeviCivitaConnection I g (D.covariantDerivative (I := I)) := by
  constructor
  · rw [CovariantDerivative.torsion_eq_zero_iff]
    intro X Y x hX hY
    exact (D.isLeviCivitaOn (D.chartAt (I := I) x)).2.1 X Y x
      (D.chartAt_mem (I := I) x) hX hY
  · intro X Y Z x hX hY hZ
    exact (D.isLeviCivitaOn (D.chartAt (I := I) x)).2.2 X Y Z x
      (D.chartAt_mem (I := I) x) hX hY hZ

/-- The connection obtained with Mathlib's open-cover constructor is globally
torsion-free and metric-compatible. -/
theorem covariantDerivativeOfOpenCover_isLeviCivita
    (D : LocalLeviCivitaAtlasData I g α) :
    IsLeviCivitaConnection I g
      (D.covariantDerivativeOfOpenCover (I := I)) := by
  rw [D.covariantDerivativeOfOpenCover_eq_covariantDerivative (I := I)]
  exact D.covariantDerivative_isLeviCivita (I := I)

/-- Global connections selected from any two local Levi-Civita atlases for the
same metric agree on differentiable vector fields. Thus the globalization is
independent of both the chart cover and the pointwise chart choices. -/
theorem covariantDerivative_independent {β : Type*}
    (D : LocalLeviCivitaAtlasData I g α)
    (D' : LocalLeviCivitaAtlasData I g β)
    (X Y : ∀ x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    D.covariantDerivative (I := I) Y x (X x) =
      D'.covariantDerivative (I := I) Y x (X x) :=
  leviCivita_unique_on_smooth I g
    (D.covariantDerivative (I := I)) (D'.covariantDerivative (I := I))
    (D.covariantDerivative_isLeviCivita (I := I))
    (D'.covariantDerivative_isLeviCivita (I := I)) X Y x hX hY

end LocalLeviCivitaAtlasData

end PseudoRiemannianMetric

end

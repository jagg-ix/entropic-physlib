/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Periodization measure bookkeeping on the unit torus

Ports the verified measure-theoretic core of `NavierStokesClean/Sobolev/TorusBridge.lean`
(reference tree, branch `helper-a/isolated-dev-20260409`, own authorship), *generalized* from
`Fin 3`/`Fin n` to an arbitrary finite index type: the standard periodization correspondence
between the unit torus `T^ι = ι → ℝ/ℤ` with product Haar measure and its fundamental domain
`(0,1]^ι` with product Lebesgue measure.

* `torusEquivIoc`, `measurePreserving_torusEquivIoc` — the componentwise fundamental-domain
  equivalence `T^ι ≃ᵐ (ι → Ioc 0 1)` is measure-preserving (product Haar ↔ product Lebesgue);
* `torus_lintegral_fundamentalDomain`, `torus_integral_fundamentalDomain` — the resulting
  change-of-variables bridges for lower and Bochner integrals;
* `measurePreserving_periodization` — the quotient map `ℝ^ι → T^ι` restricted to the
  fundamental domain is measure-preserving: Haar on the torus *is* Lebesgue on `(0,1]^ι`.

This is the exact bookkeeping that transfers spatial integrals of periodic fields (lattice
Navier–Stokes vorticity, Fourier trajectory functionals of
`NSFieldFourierSobolevHierarchy`) between the torus and Euclidean fundamental-domain
pictures.

**Honest layering.**  Pure Mathlib measure theory, sorry-free.  The source file's remaining
content is deliberately *not* ported: its `Space`-carrier hop rides the reference tree's
PhysLean-specific `Space.equivPi`, and its headline vorticity bridge discharges only the
zero-enstrophy case by a zero witness while importing a sorry-carrying Fourier layer.

## References

* Source: `NavierStokesClean/Sobolev/TorusBridge.lean` §§1–3 (reference tree, own
  authorship), re-authored on Mathlib carriers with the index type generalized.
-/

set_option autoImplicit false

open MeasureTheory

@[expose] public section

namespace Physlib.Mathematics.TorusPeriodizationMeasure

private noncomputable instance factPeriodOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

/-- **The componentwise fundamental-domain equivalence** `T^ι ≃ᵐ (ι → Ioc 0 1)`: apply
`AddCircle.measurableEquivIoc 1 0` in every component. -/
noncomputable def torusEquivIoc (ι : Type*) :
    UnitAddTorus ι ≃ᵐ (ι → Set.Ioc (0 : ℝ) (0 + 1)) :=
  MeasurableEquiv.piCongrRight (fun _ => AddCircle.measurableEquivIoc 1 0)

/-- The product of the comap-Lebesgue measures on the fundamental-domain components. -/
noncomputable def piIocMeasure (ι : Type*) [Fintype ι] :
    Measure (ι → Set.Ioc (0 : ℝ) (0 + 1)) :=
  Measure.pi fun _ => Measure.comap Subtype.val (volume : Measure ℝ)

/-- **The fundamental-domain equivalence is measure-preserving**: product Haar on the unit
torus corresponds to product Lebesgue on `(0,1]^ι`. -/
theorem measurePreserving_torusEquivIoc (ι : Type*) [Fintype ι] :
    MeasurePreserving (torusEquivIoc ι)
      (volume : Measure (UnitAddTorus ι)) (piIocMeasure ι) := by
  haveI hFin : IsFiniteMeasure (Measure.comap Subtype.val (volume : Measure ℝ) :
      Measure (Set.Ioc (0 : ℝ) (0 + 1))) := by
    refine ⟨?_⟩
    have hle : (Measure.comap Subtype.val (volume : Measure ℝ))
          (Set.univ : Set (Set.Ioc (0 : ℝ) (0 + 1))) ≤
        (volume : Measure ℝ) (Subtype.val '' (Set.univ : Set (Set.Ioc (0 : ℝ) (0 + 1)))) :=
      Measure.comap_apply_le Subtype.val (volume : Measure ℝ)
        MeasurableSet.univ.nullMeasurableSet
    have hrange : Subtype.val '' (Set.univ : Set (Set.Ioc (0 : ℝ) (0 + 1)))
        = Set.Ioc 0 (0 + 1) := by
      ext x
      simp [Set.mem_Ioc]
    calc (Measure.comap Subtype.val (volume : Measure ℝ)) Set.univ
        ≤ (volume : Measure ℝ) (Subtype.val '' Set.univ) := hle
      _ = volume (Set.Ioc (0 : ℝ) (0 + 1)) := by rw [hrange]
      _ = ENNReal.ofReal (0 + 1 - 0) := Real.volume_Ioc
      _ < ⊤ := by norm_num
  haveI hSF : ∀ _ : ι, SigmaFinite (Measure.comap Subtype.val (volume : Measure ℝ) :
      Measure (Set.Ioc (0 : ℝ) (0 + 1))) := fun _ => hFin.toSigmaFinite
  show MeasurePreserving
      (fun (a : ι → AddCircle (1 : ℝ)) i => (AddCircle.equivIoc (1 : ℝ) 0) (a i))
      (Measure.pi (fun _ => (volume : Measure (AddCircle (1 : ℝ)))))
      (Measure.pi (fun _ => Measure.comap Subtype.val (volume : Measure ℝ)))
  exact measurePreserving_pi
      (fun _ => (volume : Measure (AddCircle (1 : ℝ))))
      (fun _ => Measure.comap Subtype.val (volume : Measure ℝ))
      (fun _ => AddCircle.measurePreserving_equivIoc 1)

section IntegralBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The lower-integral fundamental-domain bridge**:
`∫⁻ t : T^ι, f t = ∫⁻ x : (ι → Ioc 0 1), f (equiv⁻¹ x)`. -/
theorem torus_lintegral_fundamentalDomain {ι : Type*} [Fintype ι]
    (f : UnitAddTorus ι → ENNReal) :
    ∫⁻ t : UnitAddTorus ι, f t =
    ∫⁻ x : ι → Set.Ioc (0 : ℝ) (0 + 1),
      f ((torusEquivIoc ι).symm x) ∂(piIocMeasure ι) := by
  have hmp_sym := MeasurePreserving.symm (torusEquivIoc ι)
      (measurePreserving_torusEquivIoc ι)
  exact (hmp_sym.lintegral_comp_emb (torusEquivIoc ι).symm.measurableEmbedding f).symm

/-- **The Bochner-integral fundamental-domain bridge**:
`∫ t : T^ι, f t = ∫ x : (ι → Ioc 0 1), f (equiv⁻¹ x)`. -/
theorem torus_integral_fundamentalDomain {ι : Type*} [Fintype ι]
    (f : UnitAddTorus ι → E) :
    ∫ t : UnitAddTorus ι, f t =
    ∫ x : ι → Set.Ioc (0 : ℝ) (0 + 1),
      f ((torusEquivIoc ι).symm x) ∂(piIocMeasure ι) := by
  have hmp_sym := MeasurePreserving.symm (torusEquivIoc ι)
      (measurePreserving_torusEquivIoc ι)
  exact (hmp_sym.integral_comp (torusEquivIoc ι).symm.measurableEmbedding f).symm

end IntegralBridge

/-- **Periodization is measure-preserving**: the quotient map `ℝ^ι → T^ι`, restricted to the
fundamental domain `(0,1]^ι`, carries Lebesgue measure to the product Haar measure of the
unit torus — Haar on `T^ι` *is* Lebesgue on the fundamental domain. -/
theorem measurePreserving_periodization (ι : Type*) [Fintype ι] :
    MeasurePreserving
      (fun (x : ι → ℝ) (i : ι) => (x i : AddCircle (1 : ℝ)))
      ((volume : Measure (ι → ℝ)).restrict
        (Set.pi Set.univ (fun _ => Set.Ioc (0 : ℝ) 1)))
      (volume : Measure (UnitAddTorus ι)) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  apply measurePreserving_pi _ _ fun _ => ?_
  have h := AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0
  simp only [zero_add] at h
  exact h

end Physlib.Mathematics.TorusPeriodizationMeasure

end

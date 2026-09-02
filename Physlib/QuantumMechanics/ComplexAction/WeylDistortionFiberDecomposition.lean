/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge
public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

/-!
# The Weyl distortion as a dual-sphere fiber decomposition

Inspecting the Weyl distortion `Δ_abc = −⅛ g_ab Q_c` (`WeylCartanDilatonicCharge.weylDistortion`,
Babourova–Frolov Eq. A.5) through the **dual-sphere fiber decomposition**
(`Hopf.DualSphereFiberDecomposition`) — the "`3D` = `2D` leaves + holonomy defect" structure that maps
a flow to a base/fiber pair and measures the misalignment by a vanishing-minors defect.

The correspondence is exact at the algebraic level:

* the dual-sphere **2D collapse** is characterized by the **2×2 minors vanishing**
  (`crossSphereDefect_eq_zero_iff`: `ξ_i η_j = ξ_j η_i`), i.e. the base and fiber directions are
  collinear / rank-one;
* the Weyl distortion is the **rank-one outer product** `Δ = −⅛ (g ⊗ Q)` — a *base* factor `g_ab`
  (the metric) times a *fiber* factor `Q_c` (the Weyl one-form / dilaton direction). Its `2×2` minors
  vanish identically (`weylDistortion_minors_vanish`), so it is *always* in the collapsed, structure-
  preserving state.

So the Weyl (pure-trace) constraint on the nonmetricity is precisely the **fiber-collapse**: the
traceless "shear" part — the analogue of the cross-sphere defect `|ξ × η|²` — is zero
(`weyl_tracelessNonmetricity_zero`), while a general (non-Weyl) nonmetricity would carry a nonzero
defect. The base is the metric `g`; the fiber is the dilaton one-form `Q`, recovered as the trace
(`WeylCartanDilatonicCharge.weylOneForm_eq_nonmetricityTrace`) — the structure-preserving projection
`Δ ↦ (g, Q)` across the metric ↦ connection dimensions.

**Category-theory framing (interpretive).** In the structure-preserving-map framework of
`Hopf.DualSphereFiberYoneda` (Yoneda over `ModuleCat ℂ`: an object is determined by its probes), the
Weyl structure is the fiber datum `Q`, and the **dilatonic charge is the probe** that detects it —
Corollary 3 (`WeylCartanDilatonicCharge.weylForce_zero_of_no_dilatonicCharge`): matter with no
dilatonic charge cannot distinguish the Weyl structure, exactly as a Yoneda object is invisible to a
trivial probe.

**Honest layering.** Proven: the Weyl distortion is rank-one (minors vanish), its traceless defect is
zero, and — the sharpened statement — its block-rows are literal dual-sphere directions whose
`crossSphereDefect` vanishes (`distortionRows_crossSphereDefect_zero`, §C), so the Weyl collapse *is*
the dual-sphere `2D`-collapse, reusing `crossSphereDefect_eq_zero_iff` on the actual `Fin 3` vectors.
Interpretive: the Yoneda probe reading of the dilatonic charge (Corollary 3), and the reading of `Q`
as the "information" fiber `η`, remain the structural framing.

## References

* Babourova–Frolov Eq. A.5 [`Babourova:1998ah`]; the dual-sphere fiber decomposition
  (`Hopf.DualSphereFiberDecomposition.crossSphereDefect_eq_zero_iff`) and its Yoneda category-theory
  layer (`Hopf.DualSphereFiberYoneda`). Reuses `WeylCartanDilatonicCharge` (`weylDistortion`,
  `IsWeylNonmetricity`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WeylDistortionFiberDecomposition

open Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge
open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

variable {ι : Type*}


/-- **The Weyl distortion's `2×2` minors vanish** (rank-one, the fiber-collapse): `Δ_abc Δ_a'b'c' =
Δ_abc' Δ_a'b'c`. The distortion is the outer product `−⅛ (g ⊗ Q)` of a base factor `g_ab` and a fiber
factor `Q_c` — the exact analogue of the dual-sphere `2D`-collapse condition
(`Hopf.DualSphereFiberDecomposition.crossSphereDefect_eq_zero_iff`, the vanishing `2×2` minors of a
collinear base/fiber pair). -/
lemma weylDistortion_minors_vanish (g : ι → ι → ℝ) (weyl : ι → ℝ) (a b c a' b' c' : ι) :
    weylDistortion g weyl a b c * weylDistortion g weyl a' b' c'
      = weylDistortion g weyl a b c' * weylDistortion g weyl a' b' c := by
  unfold weylDistortion; ring

/-- **The base/fiber factorization**: at fixed metric block `(a,b)`, the distortion depends on the
form index `c` only through the fiber `Q_c` — `Δ_abc / Δ_abc'` is the fiber ratio `Q_c / Q_c'`,
independent of `(a,b)`. Precisely: `Δ_abc Q_c' = Δ_abc' Q_c`. -/
lemma weylDistortion_fiber_factor (g : ι → ι → ℝ) (weyl : ι → ℝ) (a b c c' : ι) :
    weylDistortion g weyl a b c * weyl c' = weylDistortion g weyl a b c' * weyl c := by
  unfold weylDistortion; ring


/-- **The traceless "shear" part of a nonmetricity** `Q_abc − ¼ g_ab Q_c` — the analogue of the
dual-sphere cross-sphere defect `|ξ × η|²`: the part of the nonmetricity that is *not* collinear with
the metric. -/
noncomputable def tracelessNonmetricity (Q : ι → ι → ι → ℝ) (g : ι → ι → ℝ) (weyl : ι → ℝ)
    (a b c : ι) : ℝ := Q a b c - (1 / 4) * g a b * weyl c

/-- **The Weyl constraint is the fiber-collapse**: the traceless "shear" defect of a Weyl
nonmetricity is zero — the base (metric `g`) and fiber (dilaton `Q`) are aligned, exactly the
`2D`-collapse of the dual-sphere fiber decomposition. A general (non-Weyl) nonmetricity would carry a
nonzero defect. -/
lemma weyl_tracelessNonmetricity_zero (Q : ι → ι → ι → ℝ) (g : ι → ι → ℝ) (weyl : ι → ℝ)
    (h : IsWeylNonmetricity Q g weyl) (a b c : ι) :
    tracelessNonmetricity Q g weyl a b c = 0 := by
  unfold tracelessNonmetricity; rw [h a b c]; ring


/-- A **block-row of the Weyl distortion** as a dual-sphere direction: `c ↦ Δ_abc = −⅛ g_ab Q_c`, the
metric-block `(a,b)` slice — a `Fin 3 → ℝ` vector proportional to the fiber `Q`. -/
noncomputable def distortionRow (g : Fin 3 → Fin 3 → ℝ) (weyl : Fin 3 → ℝ) (a b : Fin 3) :
    Fin 3 → ℝ := fun c => weylDistortion g weyl a b c

/-- **The Weyl-distortion collapse *is* the dual-sphere cross-sphere defect vanishing** — a theorem,
not an analogy. Any two block-rows of the Weyl distortion are collinear dual-sphere directions: their
cross-sphere defect `|ξ × η|²` (`Hopf.DualSphereFiberDecomposition.crossSphereDefect`) is zero, because
both rows are proportional to the fiber `Q`. So the Weyl (pure-trace) constraint is literally the
`2D`-collapse `crossSphereDefect_eq_zero_iff` of the dual-sphere fiber decomposition, applied to the
distortion's base/fiber rows. -/
lemma distortionRows_crossSphereDefect_zero (g : Fin 3 → Fin 3 → ℝ) (weyl : Fin 3 → ℝ)
    (a b a' b' : Fin 3) :
    crossSphereDefect (distortionRow g weyl a b) (distortionRow g weyl a' b') = 0 := by
  rw [crossSphereDefect_eq_zero_iff]
  refine ⟨?_, ?_, ?_⟩ <;> · simp only [distortionRow, weylDistortion]; ring

end Physlib.QuantumMechanics.ComplexAction.WeylDistortionFiberDecomposition

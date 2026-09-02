/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality

/-!
# Local causality conditions for piecewise-flat manifolds (Asante–Dittrich §III)

Asante–Dittrich–Padua-Argüelles §III proposes a class of **local causality conditions** for
`4`-dimensional piecewise-flat manifolds (generalizing the causal-dynamical-triangulation slicing).
All are of one form: a local light-cone structure that must have **exactly two light cones** (two
disconnected components). This formalizes those conditions and ties them to the causal regularity and
amplitude suppression/enhancement of `ComplexReggeActionCausality`.

* **§A — the three conditions.** `IsLocallyCausal count := count = 2`; `IsHingeCausal` (triangle/hinge:
  two light cones at a space-like triangle), `IsEdgeCausal` (two light cones / disks at the
  orthogonal-cut bulk vertex), `IsVertexCausal` (two disconnected `3`-balls at a vertex star) — all
  the same "exactly two" condition.
* **§B — the causal trichotomy** (§III). A space-like hinge is exactly one of causal
  (`IsHingeCausal`, two cones), **trouser-violating** (`IsTrouserViolation`, `> 2` cones), or
  **yarmulke-violating** (`IsYarmulkeViolation`, `< 2` cones) — `hinge_trichotomy`.
* **§C — equivalence with causal regularity.** The light-ray-crossing count is `N_c = 2 × cones`
  (`crossingsFromCones`); hinge causality (two cones) is **exactly** the causal regularity
  `N_c = 4`/real deficit angle of §II.D (`hingeCausal_iff_causallyRegular`).
* **§D — amplitude consequences.** A trouser hinge violation (`> 2` cones) is **suppressed**
  (`trouserViolation_suppressed`) and a yarmulke violation (`< 2` cones) is **enhanced**
  (`yarmulkeViolation_enhanced`) — the same `complexActionWeight` asymmetry, now keyed to the
  light-cone count.

**Honest layering.** Proven: the trichotomy, the equivalence of hinge causality with causal
regularity via `N_c = 2·cones`, and the suppression/enhancement of the two violation types.
Interpretive: the geometric content (light cones from projecting hinges, disconnected disks/`3`-balls,
`null`-geodesic construction) is the physical meaning of the light-cone count `count`, taken as the
datum here — the conditions are stated as its cardinality being two.

## References

* S. K. Asante, B. Dittrich, J. Padua-Argüelles, "Complex actions and causality violations",
  arXiv:2112.15387 [`Asante:2021zzh`], §III (triangle/hinge, edge, vertex causality). Reuses
  `ComplexReggeActionCausality` (`lorentzianDeficitImaginary`, `causallyRegular_iff`,
  `deficitAmplitude`, `trousers_amplitude_suppressed`, `yarmulke_amplitude_enhanced`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LocalCausalityConditions

open Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality


/-- **A local causality condition holds** iff its light-cone structure has exactly two components
(Asante–Dittrich §III): two light cones, or two disconnected disks/balls. -/
def IsLocallyCausal (count : ℕ) : Prop := count = 2

/-- **Triangle/hinge causality**: a space-like triangle has exactly two light cones in the sum of
wedges from its attached `4`-simplices. -/
abbrev IsHingeCausal (numLightCones : ℕ) : Prop := IsLocallyCausal numLightCones

/-- **Edge causality**: the orthogonal cut of a `4`-simplex through a space-like edge has exactly two
light cones (two disconnected disks) at its bulk vertex. -/
abbrev IsEdgeCausal (numLightCones : ℕ) : Prop := IsLocallyCausal numLightCones

/-- **Vertex causality**: the intersection of the light cones of a vertex star with its boundary is
two disconnected `3`-balls. -/
abbrev IsVertexCausal (numComponents : ℕ) : Prop := IsLocallyCausal numComponents


/-- **A trouser-like hinge violation**: more than two light cones (Asante–Dittrich §III / Fig. 1's
four-light-cone crotch). -/
def IsTrouserViolation (numLightCones : ℕ) : Prop := 2 < numLightCones

/-- **A yarmulke-like hinge violation**: fewer than two light cones. -/
def IsYarmulkeViolation (numLightCones : ℕ) : Prop := numLightCones < 2

/-- **The causal trichotomy**: every space-like hinge is exactly one of causal, trouser-violating, or
yarmulke-violating. -/
lemma hinge_trichotomy (n : ℕ) :
    IsHingeCausal n ∨ IsTrouserViolation n ∨ IsYarmulkeViolation n := by
  unfold IsHingeCausal IsLocallyCausal IsTrouserViolation IsYarmulkeViolation; omega


/-- **The light-ray-crossing count** `N_c = 2 × (number of light cones)` — each light cone is crossed
twice going around the hinge. -/
def crossingsFromCones (numLightCones : ℕ) : ℕ := 2 * numLightCones

/-- **Hinge causality is causal regularity**: a space-like hinge has two light cones iff its Lorentzian
deficit angle is real (`N_c = 4`), the §II.D causal-regularity condition. -/
lemma hingeCausal_iff_causallyRegular (n : ℕ) :
    IsHingeCausal n ↔ lorentzianDeficitImaginary (crossingsFromCones n) = 0 := by
  rw [causallyRegular_iff]; unfold IsHingeCausal IsLocallyCausal crossingsFromCones; omega


/-- **A trouser hinge violation is exponentially suppressed** (§III + §II.E): more than two light cones
gives `N_c > 4`, a positive imaginary deficit, and an amplitude `< 1`. -/
lemma trouserViolation_suppressed (area : ℝ) (harea : 0 < area) (n : ℕ) (h : IsTrouserViolation n) :
    deficitAmplitude area (crossingsFromCones n) < 1 := by
  apply trousers_amplitude_suppressed area harea
  unfold IsTrouserViolation at h; unfold crossingsFromCones; omega

/-- **A yarmulke hinge violation is exponentially enhanced** (§III + §II.E): fewer than two light cones
gives `N_c < 4`, a negative imaginary deficit, and an amplitude `> 1`. -/
lemma yarmulkeViolation_enhanced (area : ℝ) (harea : 0 < area) (n : ℕ) (h : IsYarmulkeViolation n) :
    1 < deficitAmplitude area (crossingsFromCones n) := by
  apply yarmulke_amplitude_enhanced area harea
  unfold IsYarmulkeViolation at h; unfold crossingsFromCones; omega

end Physlib.QuantumMechanics.ComplexAction.LocalCausalityConditions

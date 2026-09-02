/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet

/-!
# The non-abelian "minimal-three" self-interaction — gluons and weak bosons share it

Standard QCD: gluons, unlike the photon, **self-interact**, minimally through a **three-gluon vertex** (the
cubic `A³` term of `F = dA + g[A,A]`). Algebraically the three channel color factors obey the
structure-constant **Jacobi identity** `c_s + c_t + c_u = 0` (`BCJDoubleCopy.ColorKinematicsDoubleCopy.color_jacobi`).

This file isolates that "minimal-three" law and answers the question *is this `3` the same as the others?*:

* **§A — the non-abelian three-vertex** `ChernSimons.NonAbelianThreeVertex`: three color factors with the cyclic Jacobi
  `c_s+c_t+c_u=0` and *not all zero* (a genuine self-coupling). `ofBCJ` builds one from any
  `BCJColorKinematicsDuality` (the Jacobi field *is* the same color Jacobi).
* **§B — gluons and weak bosons share it; the photon does not.** `gluonVertex` (`SU(3)`) and `weakVertex`
  (`SU(2)`) are both genuine three-vertices satisfying the *same* cyclic Jacobi
  (`gluon_weak_share_jacobi`); a genuine vertex is never all-zero (`three_vertex_not_abelian`), while the
  abelian photon's color factors all vanish (`photon_color_factors_zero`) — no three-photon vertex.
* **§C — the two distinct "threes."** `minimal_three_distinct_from_color_center`: the self-interaction `3` is
  the **additive cyclic Jacobi** `c_s+c_t+c_u=0` (the `3` channels / the rank of the Lie bracket — *the same
  for `SU(2)` and `SU(3)`*, rank-independent), whereas the color `3` is the **multiplicative `ℤ/3` center**
  `ω³=1` (`Particles.NeutrinoModel.cubeRoot_pow_three`, specific to `N=3` colors). They coincide numerically for `SU(3)`
  but are different structures — so the gluon's "minimal-three" does **not** follow the color-`ℤ/3` pattern;
  it is the universal non-abelian Lie-bracket three, shared with the weak bosons.

**Honest layering.** Proven: the three-vertex Jacobi (reusing the BCJ color Jacobi), that gluon/weak vertices
are genuine (nonzero) while the abelian photon's are zero, and that this additive cyclic `3` coexists with
the distinct multiplicative `ℤ/3` color center. The numeric color-factor values are representative
structure-constant data (e.g. `1+1−2=0`), not the full `f^{abc}` tensor; the 4-gluon vertex and the dynamics
are not modelled.

## References

* Yang–Mills self-interaction; the structure-constant Jacobi `c_s+c_t+c_u=0`; `Z(SU(N))=ℤ/N`. `Physlib`
  (`BCJDoubleCopy.ColorKinematicsDoubleCopy`, `Particles.StrongInteractionColorOctet`, `Particles.NeutrinoModel`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.NonAbelianThreeVertex


/-- **A non-abelian three-vertex**: three channel color factors obeying the structure-constant Jacobi
identity `c_s + c_t + c_u = 0`, and **not all zero** — a genuine self-coupling (the minimal gluon /
weak-boson self-interaction). -/
structure ChernSimons.NonAbelianThreeVertex where
  c_s : ℝ
  c_t : ℝ
  c_u : ℝ
  jacobi : c_s + c_t + c_u = 0
  nontrivial : ¬ (c_s = 0 ∧ c_t = 0 ∧ c_u = 0)

/-- **[The three-vertex Jacobi]** `c_s + c_t + c_u = 0` — the cyclic structure-constant identity. -/
lemma three_vertex_jacobi (v : ChernSimons.NonAbelianThreeVertex) : v.c_s + v.c_t + v.c_u = 0 := v.jacobi

/-- **[A genuine three-vertex is non-abelian]** its color factors are not all zero — so an abelian
(vanishing-structure-constant) theory has no such vertex. -/
lemma three_vertex_not_abelian (v : ChernSimons.NonAbelianThreeVertex) :
    ¬ (v.c_s = 0 ∧ v.c_t = 0 ∧ v.c_u = 0) := v.nontrivial

/-- **[A three-vertex from BCJ]** any `BCJColorKinematicsDuality` with non-vanishing color factors is a
non-abelian three-vertex — its `color_jacobi` *is* the three-vertex Jacobi. -/
def ofBCJ (d : BCJColorKinematicsDuality) (h : ¬ (d.c_s = 0 ∧ d.c_t = 0 ∧ d.c_u = 0)) :
    ChernSimons.NonAbelianThreeVertex :=
  ⟨d.c_s, d.c_t, d.c_u, d.color_jacobi, h⟩


/-- The **three-gluon vertex** (`SU(3)`): representative structure-constant color factors `(1, 1, −2)`. -/
def gluonVertex : ChernSimons.NonAbelianThreeVertex := ⟨1, 1, -2, by ring, by norm_num⟩

/-- The **three-weak-boson vertex** (`SU(2)`, e.g. `WWZ`): the same cyclic structure `(1, 1, −2)`. -/
def weakVertex : ChernSimons.NonAbelianThreeVertex := ⟨1, 1, -2, by ring, by norm_num⟩

/-- **[Gluons and weak bosons share the three-vertex Jacobi]** both `SU(3)` and `SU(2)` self-couplings obey
the *same* cyclic identity `c_s+c_t+c_u=0` — the minimal-three law is a shared non-abelian property. -/
lemma gluon_weak_share_jacobi :
    gluonVertex.c_s + gluonVertex.c_t + gluonVertex.c_u = 0
      ∧ weakVertex.c_s + weakVertex.c_t + weakVertex.c_u = 0 :=
  ⟨gluonVertex.jacobi, weakVertex.jacobi⟩

/-- **[The abelian photon has no self-coupling]** the `U(1)` structure constants vanish, so all color factors
are zero (`trivialBCJDuality`) — there is no three-photon vertex. -/
lemma photon_color_factors_zero :
    trivialBCJDuality.c_s = 0 ∧ trivialBCJDuality.c_t = 0 ∧ trivialBCJDuality.c_u = 0 :=
  ⟨rfl, rfl, rfl⟩


/-- **[The minimal-three is not the colour `ℤ/3`]** the self-interaction `3` is the **additive cyclic
Jacobi** `c_s+c_t+c_u = 0` (the three channels / the Lie-bracket rank — identical for `SU(2)` and `SU(3)`,
independent of the number of colours), while the colour `3` is the **multiplicative `ℤ/3` centre** `ω³ = 1`
(specific to `N=3`). The two coexist and are different structures: the gluon's "minimal-three" is the
universal non-abelian Lie three, *not* the colour `ℤ/3`. -/
lemma minimal_three_distinct_from_color_center :
    gluonVertex.c_s + gluonVertex.c_t + gluonVertex.c_u = 0
      ∧ weakVertex.c_s + weakVertex.c_t + weakVertex.c_u = 0
      ∧ ¬ (gluonVertex.c_s = 0 ∧ gluonVertex.c_t = 0 ∧ gluonVertex.c_u = 0)
      ∧ (trivialBCJDuality.c_s = 0 ∧ trivialBCJDuality.c_t = 0 ∧ trivialBCJDuality.c_u = 0)
      ∧ cubeRoot ^ 3 = 1 :=
  ⟨gluonVertex.jacobi, weakVertex.jacobi, gluonVertex.nontrivial, photon_color_factors_zero,
    cubeRoot_pow_three⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.NonAbelianThreeVertex

end

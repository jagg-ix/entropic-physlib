/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation

/-!
# The Noether conservation double copy: gauge `∂J = 0` ↔ gravity `∇G = 0`

`JacobiBianchiDoubleCopyFamily` places the color Jacobi, the kinematic Jacobi (`dF = 0`, gauge first Bianchi),
the gravity first Bianchi `R_{a[bcd]} = 0` and the frame Lie–Jacobi as four faces of one `cyclicSum` — the
double copy at the level of the *algebraic identities*. This module records the double copy one level down, at
the level of the *Noether conservation laws*: the same arbitrariness kernel `forall_inner_eq_zero_iff`
(`Curvature.DiffeomorphismMetricVariation`) yields both sides.

* Gravity — diffeomorphism invariance (arbitrary `ε^μ`) forces `∇^μ G_{μν} = 0` (the contracted second Bianchi,
  `einsteinTensor_noether_conserved`).
* Gauge (the BCJ dual) — gauge invariance (arbitrary `λ`) forces `∂_μ J^μ = 0` (`gauge_current_conservation`).

Both are `forall_inner_eq_zero_iff` applied to the respective divergence covector; only the symmetry parameter
(`λ` vs `ε`) and the Bianchi sector (first vs second) differ. This is the conservation-level companion of
`DualBianchiContracts` (gauge first Bianchi ↔ gravity second Bianchi).

* `gauge_current_conservation` — gauge invariance ⇒ `∂_μ J^μ = 0`, the BCJ dual of `einsteinTensor_noether_conserved`.
* `noether_conservation_double_copy` — both conservation laws from the one arbitrariness lemma.
* `noether_double_copy_matter_conservation` — the full chain: gauge Noether ⇒ `∂J = 0`; gravity Noether ⇒
  `∇G = 0` ⇒ (Einstein equation) `∇T = 0` (`contracted_bianchi_conservation`).
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy

open Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation

/-- **[Gauge-side Noether: gauge invariance ⇒ current conservation] `∂_μ J^μ = 0`** — the BCJ dual of
`einsteinTensor_noether_conserved`. The gauge invariance `δA_μ = ∂_μ λ` of the Yang–Mills/Maxwell action is,
after integration by parts, the linear functional `λ ↦ ∑_i (∂·J)_i λ^i`; its vanishing for *every* gauge
parameter `λ` forces the current divergence `divJ = ∂_μ J^μ` to vanish — the same `forall_inner_eq_zero_iff`
arbitrariness that gives `∇G = 0` on the gravity side. -/
lemma gauge_current_conservation {ι : Type*} [Fintype ι] [DecidableEq ι] (divJ : ι → ℝ)
    (hgauge : ∀ lam : ι → ℝ, ∑ i, divJ i * lam i = 0) : divJ = 0 :=
  (forall_inner_eq_zero_iff divJ).mp hgauge

/-- **[The Noether conservation double copy]** the gauge current conservation `∂_μ J^μ = 0` (first-Bianchi /
gauge sector) and the gravity Einstein conservation `∇^μ G_{μν} = 0` (second-Bianchi / gravity sector) both
follow from the *same* Noether arbitrariness — of the gauge parameter `λ` and of the diffeomorphism `ε`
respectively. The conservation-level face of the color–kinematics double copy. -/
lemma noether_conservation_double_copy {ι : Type*} [Fintype ι] [DecidableEq ι] (divJ divG : ι → ℝ)
    (hgauge : ∀ lam : ι → ℝ, ∑ i, divJ i * lam i = 0)
    (hdiffeo : ∀ eps : ι → ℝ, ∑ i, divG i * eps i = 0) :
    divJ = 0 ∧ divG = 0 :=
  ⟨(forall_inner_eq_zero_iff divJ).mp hgauge, (forall_inner_eq_zero_iff divG).mp hdiffeo⟩

/-- **[The full double-copy conservation chain]** gauge invariance gives current conservation `∂_μ J^μ = 0`,
and diffeomorphism invariance gives `∇^μ G_{μν} = 0` which, through the Einstein equation `∇G = κ ∇T`
(`κ ≠ 0`), gives matter conservation `∇^μ T_{μν} = 0` (`contracted_bianchi_conservation`). The gauge current
and the gravitational stress-energy are conserved by the two sides of one Noether double copy. -/
lemma noether_double_copy_matter_conservation (divJ divG divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hEin : divG = κ • divT)
    (hgauge : ∀ lam : Fin 4 → ℝ, ∑ i, divJ i * lam i = 0)
    (hdiffeo : ∀ eps : Fin 4 → ℝ, ∑ i, divG i * eps i = 0) :
    divJ = 0 ∧ divT = 0 := by
  refine ⟨(forall_inner_eq_zero_iff divJ).mp hgauge, ?_⟩
  exact contracted_bianchi_conservation κ hκ divG divT hEin ((forall_inner_eq_zero_iff divG).mp hdiffeo)

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy

end

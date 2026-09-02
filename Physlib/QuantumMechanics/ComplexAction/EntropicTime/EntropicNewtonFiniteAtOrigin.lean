/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential
public import Physlib.Thermodynamics.VerlindeNewtonGravity
meta import Zil

/-!
# The entropic/shell gravitational potential: Newtonian at large r, finite at the origin

Plastino–Rocca, *Entropic Forces and Newton's Gravitation* (Entropy 2020, 22, 273): the
first-quantized Verlinde gravitational potential equals Newton's `−GmM/r` at large distances (their
eq. 6, `V₃ = −GmM/r·H(r−r₁)`) but is **finite at the origin** — it has no `1/r` divergence — so the
associated Schrödinger problem has no UV trouble.

The repo carries this qualitative behaviour exactly through Newton's shell mean-value theorem
(`NewtonShellPotential.newtonShellPotential3`): the shell-averaged Newton potential is `−GmM/r`
outside the shell and the **finite constant** `−GmM/R` inside it.  This module packages that as the
Plastino–Rocca finiteness statement.

* `entropicShellPotential_exterior_eq_newton` — for `r > R` the potential is exactly Newton's
  `−GmM/r` (paper eq. 6 with `H = 1`).
* `entropicShellPotential_interior_finite` — for `r < R` the potential is the finite constant
  `−GmM/R` (no origin singularity).
* `entropicShellPotential_bounded_below` — the potential never diverges: `−GmM/R ≤ V` everywhere.
* the exterior force is the Verlinde entropic force (`newtonPotential_deriv_eq_verlinde_entropicForce`).

Honest scope: the finiteness mechanism is Newton's shell mean value (finite value `−GmM/R`), not
Plastino–Rocca's smooth Fourier-regularized boson-boson potential; the qualitative claim
(Newtonian large-r, finite origin) is faithful, the specific `V(0)` value is not the paper's.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin

open scoped Space
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux

/-- **The entropic/shell gravitational potential** — the shell mean of the point-mass Newton kernel
`−GmM/‖·‖` over a screen of radius `R`. -/
def entropicShellPotential (G m M R : ℝ) (center source : Space 3) : ℝ :=
  -(G * m * M) * sphereSurfaceIntegral3 R (fun n => (‖source - (center + R • n.1)‖)⁻¹)
    / (4 * Real.pi * R ^ 2)

/-- The entropic/shell potential is `−GmM / max(r, R)` (Newton's shell theorem). -/
theorem entropicShellPotential_eq (G m M R : ℝ) (center source : Space 3) (hR : 0 < R)
    (hb : ‖source - center‖ ≠ R) :
    entropicShellPotential G m M R center source = -(G * m * M) / max ‖source - center‖ R := by
  unfold entropicShellPotential
  rw [newtonShellPotential3 R center source hR hb]
  have hne : (4 * Real.pi * R ^ 2) ≠ 0 := by positivity
  field_simp

/-- **[Large `r` — Newton's potential, paper eq. 6]** outside the screen (`r > R`) the entropic
potential is exactly Newton's `−GmM/r`. -/
@[zil_level bridge_theorem]
theorem entropicShellPotential_exterior_eq_newton (G m M R : ℝ) (center source : Space 3)
    (hR : 0 < R) (hgt : R < ‖source - center‖) :
    entropicShellPotential G m M R center source = -(G * m * M) / ‖source - center‖ := by
  rw [entropicShellPotential_eq G m M R center source hR (ne_of_gt hgt), max_eq_left hgt.le]

/-- **[Finite at the origin]** inside the screen (`r < R`) the entropic potential is the *finite
constant* `−GmM/R` — no `1/r` divergence. -/
@[zil_level bridge_theorem]
theorem entropicShellPotential_interior_finite (G m M R : ℝ) (center source : Space 3)
    (hR : 0 < R) (hlt : ‖source - center‖ < R) :
    entropicShellPotential G m M R center source = -(G * m * M) / R := by
  rw [entropicShellPotential_eq G m M R center source hR (ne_of_lt hlt), max_eq_right hlt.le]

/-- **The entropic potential never diverges** — it is bounded below by the finite `−GmM/R`
everywhere (`G, m, M ≥ 0`), in contrast to Newton's `−GmM/r → −∞`. -/
@[zil_level physical_theorem]
theorem entropicShellPotential_bounded_below (G m M R : ℝ) (center source : Space 3) (hR : 0 < R)
    (hb : ‖source - center‖ ≠ R) (hG : 0 ≤ G) (hm : 0 ≤ m) (hM : 0 ≤ M) :
    -(G * m * M) / R ≤ entropicShellPotential G m M R center source := by
  rw [entropicShellPotential_eq G m M R center source hR hb, neg_div, neg_div, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (by positivity) hR (le_max_right _ _)

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin

zil attach entropicShellPotential_exterior_eq_newton where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_eq",
  formalizes @ "claim:outside-the-screen-the-entropic-shell-gravitational-potential-is-exactly-newtons-minus-g-m-m-over-r-recovering-newtons-potential-at-large-distances"

zil attach entropicShellPotential_interior_finite where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_eq",
  formalizes @ "claim:inside-the-screen-the-entropic-shell-gravitational-potential-is-the-finite-constant-minus-g-m-m-over-r-with-no-one-over-r-divergence-so-the-potential-is-finite-at-the-origin"

zil attach entropicShellPotential_bounded_below where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_eq",
  formalizes @ "claim:the-entropic-shell-gravitational-potential-never-diverges-it-is-bounded-below-by-the-finite-minus-g-m-m-over-r-everywhere-unlike-newtons-one-over-r-singularity"

zil_file_contract physlib.entropicNewtonFiniteAtOrigin where
  promises "The entropic shell gravitational potential of the Plastino-Rocca first-quantized Verlinde gravity, Newtonian at large r and finite at the origin, formalized through Newton's shell mean-value theorem. The shell-averaged Newton potential is exactly minus G m M over r outside the screen, recovering Newton's potential at large distances, and the finite constant minus G m M over R inside the screen, with no one over r divergence, so the potential is finite at the origin. The potential never diverges, being bounded below by the finite minus G m M over R everywhere, in contrast to Newton's one over r singularity. The finiteness mechanism is the shell mean value, not the paper's smooth Fourier-regularized boson-boson potential; the qualitative Newtonian-large-r finite-origin behaviour is faithful, the specific origin value is not the paper's."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonShellPotential.newtonShellPotential3"
  ]
  forbids_substitutes [
    "reading the shell mean-value finiteness as the paper's smooth Fourier-regularized boson-boson potential rather than a faithful carrier of the qualitative Newtonian-large-r finite-origin behaviour"
  ]
  witnessed_by [
    entropicShellPotential_exterior_eq_newton,
    entropicShellPotential_interior_finite,
    entropicShellPotential_bounded_below
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.entropicNewtonFiniteAtOrigin

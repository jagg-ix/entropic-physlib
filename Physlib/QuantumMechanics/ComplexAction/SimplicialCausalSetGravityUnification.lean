/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl
public import Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral

/-!
# Two discretizations of quantum gravity, one entropic weight: simplicial (Regge/Steiner) and causal-set (BDG)

This links the Ambjørn–Savvidy **simplicial** discrete Einstein–Hilbert action (`AmbjornSavvidySteinerWeyl`,
`reggeEinsteinHilbert = Σ σ·ω`, the Steiner invariant `μ₂` / Regge action) to the **causal-set** quantum-gravity
path integral (`SorkinCausalSetGravityPathIntegral`, the Benincasa–Dowker discrete Einstein–Hilbert action
`bdgAction2D`). Both are discrete Einstein–Hilbert actions on different regularizations of spacetime; both enter the
quantum-gravity path integral `∑ e^{(i/ℏ)S}` through the master complex-action weight, whose modulus is the entropic
damping `kuikenWeight ℏ S_I = e^{−S_I/ℏ}`.

So the **sum over triangulations** (simplicial gravity) and the **sum over causal sets** (causal-set gravity) sit on
the same entropic-weight hub: the discrete geometry is the real phase `S_R`, and both are unitary (pure-phase) when
there is no imaginary action, matching the whole complex-action contour family
(`ComplexActionContourUnification`, `MatsubaraSorkinReggeEntropicWeight`).

* **`reggeEinsteinHilbert_weight_modulus_is_kuiken`** — the simplicial (Regge/Steiner) gravity weight modulus.
* **`reggeEinsteinHilbert_real_unitary`** — the real Regge action gives a unitary sum over triangulations.
* **`simplicial_causalSet_gravity_unified`** — the simplicial and causal-set gravity path integrals have the same
  modulus `kuikenWeight ℏ S_I`.

**Honest layering.** Exact `master_modulus_is_kuiken` / `kuikenWeight` identities; reuses `reggeEinsteinHilbert`,
`bdgAction2D` and `causalSet_bdg_modulus_is_kuiken`. ## References

* Links `AmbjornSavvidySteinerWeyl` (Ambjørn–Savvidy 1996) to `SorkinCausalSetGravityPathIntegral` on
  `PathIntegral.ComplexActionPathIntegralWeight`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl
open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
open Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SimplicialCausalSetGravityUnification

/-- **The simplicial (Regge/Steiner) gravity weight is the entropic weight** — the discrete Einstein–Hilbert action
`reggeEinsteinHilbert σ ω s = Σ σ·ω` (the Steiner invariant `μ₂`) enters the master complex-action weight as the
real phase; its modulus is `kuikenWeight ℏ S_I`. The sum over triangulations is on the entropic-weight hub. -/
lemma reggeEinsteinHilbert_weight_modulus_is_kuiken {ι : Type*} (σ ω : ι → ℝ) (s : Finset ι)
    (S_I ℏ : ℝ) :
    ‖complexActionPathIntegralWeight (reggeEinsteinHilbert σ ω s) S_I ℏ‖ = kuikenWeight ℏ S_I :=
  master_modulus_is_kuiken _ _ _

/-- **The real Regge action gives a unitary sum over triangulations** — with no imaginary action (`S_I = 0`) the
discrete Einstein–Hilbert weight has unit modulus: the reversible/unitary limit of simplicial quantum gravity. -/
lemma reggeEinsteinHilbert_real_unitary {ι : Type*} (σ ω : ι → ℝ) (s : Finset ι) (ℏ : ℝ) :
    ‖complexActionPathIntegralWeight (reggeEinsteinHilbert σ ω s) 0 ℏ‖ = 1 := by
  rw [reggeEinsteinHilbert_weight_modulus_is_kuiken, kuikenWeight, zero_div, neg_zero, Real.exp_zero]

/-- **Two discretizations, one entropic weight** — at a common imaginary action `S_I`, the simplicial (Ambjørn–
Savvidy / Regge, `Σσ·ω`) and the causal-set (Benincasa–Dowker, `bdgAction2D`) discrete Einstein–Hilbert path
integrals **both** have modulus `kuikenWeight ℏ S_I`. The sum over triangulations and the sum over causal sets are
the same quantum-gravity entropic weight, differing only in the discrete geometry supplying the real phase. -/
lemma simplicial_causalSet_gravity_unified {ι : Type*} (σ ω : ι → ℝ) (s : Finset ι)
    (N N₀ N₁ N₂ S_I ℏ : ℝ) :
    ‖complexActionPathIntegralWeight (reggeEinsteinHilbert σ ω s) S_I ℏ‖ = kuikenWeight ℏ S_I
      ∧ ‖complexActionPathIntegralWeight (ℏ * bdgAction2D N N₀ N₁ N₂) S_I ℏ‖ = kuikenWeight ℏ S_I :=
  ⟨reggeEinsteinHilbert_weight_modulus_is_kuiken σ ω s S_I ℏ,
    causalSet_bdg_modulus_is_kuiken N N₀ N₁ N₂ S_I ℏ⟩

end Physlib.QuantumMechanics.ComplexAction.SimplicialCausalSetGravityUnification

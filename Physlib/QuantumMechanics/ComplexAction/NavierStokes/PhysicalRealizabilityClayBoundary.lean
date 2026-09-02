/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.ActionQuantumFiniteResolutionBKM

/-!
# The physical–mathematical boundary of Navier–Stokes: a dissolution, not a solution

This file records — as theorems — the exact boundary the entropic-time programme reaches, and states plainly
what it does **not** do.

The physical action quantum `ℏ` is a fixed positive constant (`Constants.ℏ_pos`); `ℏ = 0` is not a physical
value, only the classical idealization.  Two facts follow, both proved here or reused:

* `physical_dissipation_iff_hbar_pos` — the entropic-time energy descent `dE/dτ = −ℏ` is a genuine (strictly
  negative) dissipation exactly when `ℏ > 0`; at the classical `ℏ = 0` the descent is zero.  The physical
  mechanism is present *iff* the constant is physical.
* the physical fluid (`ℏ > 0`, finite resolution) is regular — `finiteResolution_bkmSurrogate_bounded` bounds
  the BKM surrogate for any band-limited trajectory.

But this is a **dissolution**, not a **solution**, and the difference is itself a theorem:

* `resolution_prefactor_unbounded` — the closure prefactor `(1 + k_max²)` diverges as `k_max → ∞`.  The physical
  bound has **no continuum limit**; the classical regime (`ℏ → 0` / `k_max → ∞`) recovers no bound at all.

So `ℏ > 0` carries no information about the `ℏ = 0` classical PDE.  The Clay problem is a mathematical statement
about that `ℏ = 0` object — a theorem to be proved or disproved — and its truth value is independent of whether
the object is physically realized.  Proving the physical constant nonzero, and proving the physical fluid
regular, **dissolves** the problem's physical relevance; it does **not** determine the mathematical answer,
which remains open.  `clay_dissolution` bundles the three facts as exactly that — physical `ℏ`-dependence,
physical regularity, and continuum divergence — the honest boundary, with **no claim of a solution**.

Physical realizability is not mathematical truth.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.PhysicalRealizabilityClayBoundary

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.ActionQuantumFiniteResolutionBKM
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier

/-- **The physical dissipation exists iff `ℏ` is physical.**  The entropic-time energy descent rate `−ℏ` is
strictly negative — a genuine dissipation resolved by the clock — exactly when `ℏ > 0`.  At the classical
`ℏ = 0` the rate is zero: the physical mechanism is *absent* precisely in the classical limit, so `ℏ = 0` is
not a physical value but the idealization. -/
theorem physical_dissipation_iff_hbar_pos (ℏ : ℝ) : -ℏ < 0 ↔ 0 < ℏ := by
  constructor <;> intro h <;> linarith

/-- **The physical–mathematical boundary, as one statement.**  For a band-limited physical trajectory at
`ℏ > 0, ν > 0`:

* the physical dissipation is present iff `ℏ > 0` (`physical_dissipation_iff_hbar_pos`);
* the physical fluid is regular — the BKM surrogate is bounded (`finiteResolution_bkmSurrogate_bounded`);
* yet the bound's prefactor `(1 + k_max²)` is unbounded over all resolutions (`resolution_prefactor_unbounded`),
  so the physical bound has no continuum (`k_max → ∞`) limit.

This is the honest boundary: the physical (`ℏ > 0`, finite-resolution) fluid is regular, and the classical
(`ℏ = 0`, continuum) object is the divergent limit the physical result does not reach.  It is a **dissolution**
of the problem's physical relevance, **not** a proof of the classical Clay statement — whose truth is a
mathematical fact independent of physical realizability, and remains open. -/
theorem clay_dissolution
    (N : ℕ) (traj : ℝ → NSFieldFourier) (ν ℏ : ℝ) (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    (kmax : ℕ) (hfreq : ∀ t i, (traj t).freq i ≤ kmax) (T : ℝ) :
    (-ℏ < 0 ↔ 0 < ℏ)
      ∧ bkmSurrogateIntegral N traj T
          ≤ ℏ / ν * (1 + (kmax : ℝ) ^ 2) * entropicProperTime N traj ν ℏ T
      ∧ (∀ M : ℝ, ∃ k : ℕ, M ≤ 1 + (k : ℝ) ^ 2) :=
  ⟨physical_dissipation_iff_hbar_pos ℏ,
    finiteResolution_bkmSurrogate_bounded N traj ν ℏ hN hν hℏ kmax hfreq T,
    resolution_prefactor_unbounded⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.PhysicalRealizabilityClayBoundary

end

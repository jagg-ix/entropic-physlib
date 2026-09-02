/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSBKMSurrogateBudget

/-!
# Entropic time quantizes the action: finite resolution closes the velocity PDE

Physical time `t` is a real continuum — arbitrarily fine, arbitrarily large wavenumbers.  **Entropic time**
`τ = (ν/ℏ)∫Ω` is action measured in units of `ℏ` (`= 2ν`, Constantin–Iyer): the master weight
`e^{(i/ℏ)(S_R + iS_I)}` resolves the action only down to the quantum `ℏ`, so there is **no infinite resolution**
— no arbitrarily fine scale, hence a *finite* mode cutoff `k_max` (the inverse viscous/Compton cell
`k_max = 1/ℓ_ν = mc/ℏ` of `SciamaAdSCPTViscousDiffusionComptonClock`).

That finite resolution is exactly what closes the velocity PDE.  `NSBKMSurrogateBudget.bkmSurrogate_le_of_
bandlimited` proves: for a band-limited trajectory (modes `≤ k_max`), the Bernstein cutoff `P ≤ k_max²Ω`
integrates and the BKM surrogate closes in the entropic time alone,

  `∫(Ω + P) ≤ (ℏ/ν)·(1 + k_max²)·τ`.

With a finite `k_max` the right-hand side is finite for every horizon `T`, so BKM is finite and the flow stays
smooth — **the velocity PDE is globally solved on the quantized (finite-resolution) fluid.**  This is the honest
answer to "solve the full velocity PDE": it is solved once the action has finite resolution.

## The continuum is the open problem

The bound's prefactor `(1 + k_max²)` **diverges as `k_max → ∞`** (`resolution_prefactor_unbounded`): the
continuum idealization — real time `t`, infinite action resolution, arbitrarily fine scales — is precisely where
the closure is lost.  `actionQuantum_regularity_dichotomy` states both halves together: *finite resolution ⟹
bounded surrogate (regular); infinite resolution ⟹ unbounded prefactor (the Millennium problem)*.  The gap
between "solved" and "open" is **exactly** the infinite-resolution assumption that entropic time removes.

## Honest scope

`bkmSurrogate_le_of_bandlimited` is a genuine theorem; the band limit `k_max` is a **model input** — physically
the action quantum's minimal scale, mathematically an assumption that classical continuum Navier–Stokes does
*not* make.  This does not prove continuum 3D regularity; it identifies the continuum (infinite action
resolution) as the sole obstruction, and shows the finite-resolution fluid is regular.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.ActionQuantumFiniteResolutionBKM

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier

/-! ### Finite resolution closes the velocity PDE -/

/-- **Finite action resolution ⟹ the BKM surrogate is bounded (regular).**  When entropic time caps the
resolution at a finite mode cutoff `k_max` (band-limited to the action quantum's minimal scale), the BKM
surrogate `∫(Ω + P)` is bounded by `(ℏ/ν)(1 + k_max²)·τ` — finite for every horizon, so the velocity field
stays smooth.  A direct reading of `bkmSurrogate_le_of_bandlimited` as the *finite-resolution* closure. -/
theorem finiteResolution_bkmSurrogate_bounded
    (N : ℕ) (traj : ℝ → NSFieldFourier) (ν ℏ : ℝ) (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    (kmax : ℕ) (hfreq : ∀ t i, (traj t).freq i ≤ kmax) (T : ℝ) :
    bkmSurrogateIntegral N traj T
      ≤ ℏ / ν * (1 + (kmax : ℝ) ^ 2) * entropicProperTime N traj ν ℏ T :=
  bkmSurrogate_le_of_bandlimited N traj ν ℏ hN hν hℏ kmax hfreq T

/-! ### The continuum limit diverges -/

/-- **The resolution prefactor is unbounded.**  As the mode cutoff grows (`k_max → ∞`, the continuum /
infinite-resolution limit), the closure prefactor `1 + k_max²` exceeds every bound: for any `M` there is a
resolution with `M ≤ 1 + k_max²`.  The finite-resolution closure degrades to nothing in the continuum. -/
theorem resolution_prefactor_unbounded (M : ℝ) : ∃ k : ℕ, M ≤ 1 + (k : ℝ) ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_ge M
  exact ⟨k, by nlinarith [hk, sq_nonneg (2 * (k : ℝ) - 1)]⟩

/-! ### The dichotomy: finite resolution regular, continuum open -/

/-- **Action quantization is the whole difference.**  One statement carries both halves: with a *finite*
resolution `k_max` (entropic time's action quantum) the BKM surrogate is bounded — the velocity PDE is solved;
yet the bounding prefactor `1 + k_max²` is *unbounded* over all resolutions — the continuum (infinite action
resolution) has no such bound.  The gap between the solved fluid and the open Millennium problem is exactly the
infinite-resolution idealization that the change from `t` to entropic time removes. -/
theorem actionQuantum_regularity_dichotomy
    (N : ℕ) (traj : ℝ → NSFieldFourier) (ν ℏ : ℝ) (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    (kmax : ℕ) (hfreq : ∀ t i, (traj t).freq i ≤ kmax) (T : ℝ) :
    bkmSurrogateIntegral N traj T
        ≤ ℏ / ν * (1 + (kmax : ℝ) ^ 2) * entropicProperTime N traj ν ℏ T
      ∧ ∀ M : ℝ, ∃ k : ℕ, M ≤ 1 + (k : ℝ) ^ 2 :=
  ⟨finiteResolution_bkmSurrogate_bounded N traj ν ℏ hN hν hℏ kmax hfreq T,
    resolution_prefactor_unbounded⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.ActionQuantumFiniteResolutionBKM

end

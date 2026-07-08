/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution
public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution

/-!
# The AdS/CFT conformal Casimir is the Regge/hydrogen and Gegenbauer eigenvalue

Connects the standard GKP–Witten dictionary (`AdSCFT.GKPWittenAdSCFTDictionary`) to the complex-action
hydrogen / Bethe–Salpeter / Gegenbauer arc of the repo. The boundary operator's conformal Casimir
`Δ(Δ − d) = m²R²` is the **same quadratic Casimir** that already runs through the repo:

* the **Regge / hydrogen `O(4)` Casimir** `reggeCasimir N = N(N+1)`
  (`BetheSalpeter.SwiftLeeComplexAngularMomentum`), the Cutkosky–Bethe–Salpeter bound-state eigenvalue
  `cutkoskyEigenvalue N = N(N+1)` (`BetheSalpeter.CutkoskyBetheSalpeterSolution`);
* the **Gegenbauer / AdS-harmonic eigenvalue** `n(n+2α)` (`OperatorAlgebra.GegenbauerODESolution`), the `S^{2α}`/`O` Laplacian.

So the GKP–Witten dictionary **inverts** them: a bulk scalar at the Regge mass `m²R² = N(N+1)` is dual to a
boundary operator of integer-spaced dimension `Δ = N+1`, and the bulk AdS harmonic with eigenvalue `n(n+2α)`
is dual to `Δ = n + 2α`. The conformal dimension is the Casimir level, tying the holographic dictionary to
the bound-state spectra already formalized.

* **§A — the conformal Casimir is the Gegenbauer/AdS-harmonic eigenvalue** (`conformalCasimir_eq_gegenbauer`,
  `conformalDimension_gegenbauer`). `Δ(Δ−2α) = n(n+2α)` at `Δ = n+2α`; the dictionary returns `Δ = n+2α`.
* **§B — the conformal Casimir is the Regge/hydrogen Casimir** (`reggeCasimir_real`,
  `conformalDimension_reggeCasimir`, `conformalDimension_cutkosky`, `regge_satisfies_massDimension`). The
  bulk mass `m²R² = N(N+1)` (Regge / Cutkosky bound state) is dual to `Δ = N+1`.

## References

* The mass–dimension relation `Δ(Δ−d) = m²R²` of `AdSCFT.GKPWittenAdSCFTDictionary`; the conformal-group quadratic
  Casimir.
* Repo dependencies: `BetheSalpeter.SwiftLeeComplexAngularMomentum` (`reggeCasimir`); `BetheSalpeter.CutkoskyBetheSalpeterSolution`
  (`cutkoskyEigenvalue`); `OperatorAlgebra.GegenbauerODESolution` (`gegenbauerEigenvalue`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenCasimir

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution

/-! ## §A — the conformal Casimir is the Gegenbauer / AdS-harmonic eigenvalue -/

/-- **[Link] The boundary conformal Casimir is the Gegenbauer/AdS-harmonic eigenvalue.** At `d = 2α` and
`Δ = n + 2α`, the conformal Casimir `Δ(Δ − d)` equals the Gegenbauer (ultraspherical / `S^{2α}` Laplacian)
eigenvalue `n(n+2α)` (`OperatorAlgebra.GegenbauerODESolution.gegenbauerEigenvalue`) — the AdS scalar harmonic dual. -/
theorem conformalCasimir_eq_gegenbauer (α : ℝ) (n : ℕ) :
    ((n : ℝ) + 2 * α) * (((n : ℝ) + 2 * α) - 2 * α) = gegenbauerEigenvalue α n := by
  unfold gegenbauerEigenvalue; ring

/-- **[Dictionary ⟹ AdS harmonics] The `n`-th Gegenbauer/AdS harmonic is dual to dimension `Δ = n + 2α`.**
The GKP–Witten dictionary maps the bulk eigenvalue `n(n+2α)` to the boundary operator dimension `n + 2α`. -/
theorem conformalDimension_gegenbauer (α : ℝ) (n : ℕ) (h : 0 ≤ (n : ℝ) + α) :
    conformalDimension (2 * α) (gegenbauerEigenvalue α n) = (n : ℝ) + 2 * α := by
  unfold conformalDimension gegenbauerEigenvalue
  rw [show (2 * α / 2) ^ 2 + (n : ℝ) * ((n : ℝ) + 2 * α) = ((n : ℝ) + α) ^ 2 by ring, Real.sqrt_sq h]
  ring

/-! ## §B — the conformal Casimir is the Regge / hydrogen Casimir -/

/-- **The Regge/hydrogen Casimir as a real bulk mass** `reggeCasimir N = N(N+1)`
(`BetheSalpeter.SwiftLeeComplexAngularMomentum`). -/
theorem reggeCasimir_real (N : ℝ) : reggeCasimir (N : ℂ) = ((N * (N + 1) : ℝ) : ℂ) := by
  unfold reggeCasimir; push_cast; ring

/-- **[Dictionary ⟹ hydrogen] A bulk scalar at the Regge mass `m²R² = N(N+1)` is dual to `Δ = N+1`.** The
GKP–Witten dictionary returns the integer-spaced hydrogen/Regge dimension `Δ = N+1` for the Regge-Casimir
bulk mass. -/
theorem conformalDimension_reggeCasimir (N : ℝ) (hN : 0 ≤ N) :
    conformalDimension 1 (N * (N + 1)) = N + 1 := by
  unfold conformalDimension
  rw [show ((1 : ℝ) / 2) ^ 2 + N * (N + 1) = (N + 1 / 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  ring

/-- **[Dictionary ⟹ Cutkosky bound state] The `N`-th Cutkosky–Bethe–Salpeter bound state is dual to
`Δ = N+1`.** The bound-state eigenvalue `cutkoskyEigenvalue N = N(N+1)`
(`BetheSalpeter.CutkoskyBetheSalpeterSolution`) is the bulk mass dual to dimension `N+1`. -/
theorem conformalDimension_cutkosky (N : ℕ) :
    conformalDimension 1 (cutkoskyEigenvalue N) = (N : ℝ) + 1 := by
  unfold cutkoskyEigenvalue
  exact conformalDimension_reggeCasimir (N : ℝ) (by positivity)

/-- **The Regge mass satisfies the mass–dimension relation** — `Δ(Δ−1) = N(N+1)` (consuming
`massDimension_relation`). -/
theorem regge_satisfies_massDimension (N : ℝ) (hN : -(1 / 2 : ℝ) ≤ N) :
    conformalDimension 1 (N * (N + 1)) * (conformalDimension 1 (N * (N + 1)) - 1) = N * (N + 1) :=
  massDimension_relation 1 (N * (N + 1)) (by nlinarith)

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenCasimir

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBulkCorrespondence
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Holographic description of the surface operator `M_σ`: bubbling geometry and large-N (Gomis 2507.12467, §4.1)

Gomis §4.1: the bulk dual of the charge-conjugation monodromy surface defect `M_σ` is fixed by the large-`N`
scaling of its correlators.  The one-loop dimension jump `dim 𝔤 − dim 𝔤_σ` across the defect (Eqs. 4.10, 4.24)
is `O(N²)` for `𝔰𝔲(N)` (so `M_σ ↔` a new *geometry*, Eq. 4.12) and `O(N)` for `𝔰𝔬(2N)` (so `M_σ ↔` a probe
*D-brane*, Eq. 4.11), and the spherical surface conformal anomaly (Eqs. 4.16–4.18) fixes `⟨M_σ⟩_{S²}`.

All identities are exact rational functions of `N, p` (dimensions `dim 𝔰𝔲(N) = N²−1`, `dim 𝔰𝔬(m) = m(m−1)/2`,
`dim 𝔰𝔭(N/2) = N(N+1)/2`):

* **Eq. 4.24** the two involutive outer automorphisms of `𝔰𝔲(N)`:
  `bubblingDimDiffSO_eq` (`𝔤_σ = 𝔰𝔬(N)`: `(N²+N−2)/2`), `bubblingDimDiffSP_eq` (`𝔤_σ = 𝔰𝔭(N/2)`:
  `(N²−N−2)/2`) — both `O(N²)`, the "heavy" geometric dual.
* **Observation 2** `bubblingDimDiff_N_to_negN` — the two `M_σ` are exchanged by `N ↦ −N`
  (`dimDiffSO(−N) = dimDiffSP(N)`), the `𝔰𝔬 ↔ 𝔰𝔭` large-`N` relation of the unoriented dual.
* **Eqs. 4.16–4.17** `so2NConformalAnomaly_eq` — the spherical anomaly `b = 3[dim 𝔰𝔬(2N) − dim 𝔰𝔬(p) −
  dim 𝔰𝔬(2N−p)] = 3p(2N−p)`; **Eq. 4.18** `so2NConformalAnomaly_leading` — `b − 6Np = −3p²`, so `b ≃ 6Np`.
* `so2NConformalAnomaly_matches_expectation` — `⟨M_σ⟩_{S²} = (a/a₀)^{2pN}` (Eq. 4.23): the planar anomaly
  `6Np = 3·(2pN)` reproduces the on-shell action exponent `2pN`.

Conceptual link: the `𝔰𝔲(N)` correlators of `M_σ` have a `1/N` (not `1/N²`) expansion over **unoriented**
Riemann surfaces (leading `ℝP²`), so the dual string background must carry **worldsheet parity** `Ω` — exactly
the `Ω` factor of `bulkC = Ω(−1)^{F_L}R_{456789}` (`SciamaAdSCPTBulkCorrespondence`, Eq. 1.2).  The two signs
of the crosscap state are the two `M_σ` exchanged by `N ↦ −N` above.

Honest scope: the exact `dim 𝔤 − dim 𝔤_σ` and conformal-anomaly polynomial identities and the `N ↦ −N` map
(the paper's §4.1 quantitative predictions).  The D-brane/orientifold and bubbling-geometry constructions are
the paper's content, contextualized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBubblingSurface

/-- `dim 𝔰𝔲(N) = N² − 1` (type `A_{N−1}`). -/
def dimSU (N : ℝ) : ℝ := N ^ 2 - 1

/-- `dim 𝔰𝔬(m) = m(m−1)/2` (types `B`/`D`). -/
def dimSO (m : ℝ) : ℝ := m * (m - 1) / 2

/-- `dim 𝔰𝔭(N/2) = (N/2)(N+1) = N(N+1)/2` (type `C`, rank `N/2`). -/
def dimSP (N : ℝ) : ℝ := N * (N + 1) / 2

/-- The dimension jump `dim 𝔰𝔲(N) − dim 𝔤_σ` for `𝔤_σ = 𝔰𝔬(N)` (Eq. 4.24, first line). -/
def bubblingDimDiffSO (N : ℝ) : ℝ := dimSU N - dimSO N

/-- The dimension jump `dim 𝔰𝔲(N) − dim 𝔤_σ` for `𝔤_σ = 𝔰𝔭(N/2)` (Eq. 4.24, second line). -/
def bubblingDimDiffSP (N : ℝ) : ℝ := dimSU N - dimSP N

/-- **[Eq. 4.24, `𝔤_σ = 𝔰𝔬(N)`] `dim 𝔰𝔲(N) − dim 𝔰𝔬(N) = (N²+N−2)/2`.**  `O(N²)` — the heavy geometric dual. -/
theorem bubblingDimDiffSO_eq (N : ℝ) : bubblingDimDiffSO N = (N ^ 2 + N - 2) / 2 := by
  unfold bubblingDimDiffSO dimSU dimSO
  ring

/-- **[Eq. 4.24, `𝔤_σ = 𝔰𝔭(N/2)`] `dim 𝔰𝔲(N) − dim 𝔰𝔭(N/2) = (N²−N−2)/2`.** -/
theorem bubblingDimDiffSP_eq (N : ℝ) : bubblingDimDiffSP N = (N ^ 2 - N - 2) / 2 := by
  unfold bubblingDimDiffSP dimSU dimSP
  ring

/-- **[Observation 2: the two `M_σ` are exchanged by `N ↦ −N`] `dimDiffSO(−N) = dimDiffSP(N)`.**  The two
involutive outer automorphisms of `𝔰𝔲(N)` are mapped into each other by `N ↦ −N` — the `𝔰𝔬(N) ↔ 𝔰𝔭(N/2)`
large-`N` relation realized in the unoriented-string dual (the two crosscap signs). -/
theorem bubblingDimDiff_N_to_negN (N : ℝ) : bubblingDimDiffSO (-N) = bubblingDimDiffSP N := by
  rw [bubblingDimDiffSO_eq, bubblingDimDiffSP_eq]
  ring

/-- The spherical surface conformal anomaly `b = 3[dim 𝔰𝔬(2N) − dim 𝔰𝔬(p) − dim 𝔰𝔬(2N−p)]` of the `𝔰𝔬(2N)`
monodromy defect `M_σ` labelled by `p` (Eqs. 4.16–4.17). -/
def so2NConformalAnomaly (p N : ℝ) : ℝ := 3 * (dimSO (2 * N) - dimSO p - dimSO (2 * N - p))

/-- **[Eqs. 4.16–4.17] `b = 3p(2N − p)`.**  The exact surface conformal anomaly of the `𝔰𝔬(2N)` defect. -/
theorem so2NConformalAnomaly_eq (p N : ℝ) : so2NConformalAnomaly p N = 3 * p * (2 * N - p) := by
  unfold so2NConformalAnomaly dimSO
  ring

/-- **[Eq. 4.18: `b ≃ 6Np` at large `N`] `b − 6Np = −3p²`.**  The leading planar anomaly is `6Np`; the
subleading correction is `−3p²`. -/
theorem so2NConformalAnomaly_leading (p N : ℝ) :
    so2NConformalAnomaly p N - 6 * N * p = -(3 * p ^ 2) := by
  rw [so2NConformalAnomaly_eq]
  ring

/-- **[Eq. 4.23: matches the on-shell exponent] `b_planar = 3·(2pN)`.**  The leading anomaly `6Np` is three
times the `⟨M_σ⟩_{S²} = (a/a₀)^{2pN}` on-shell action exponent `2pN` — field theory reproducing the D-brane
computation. -/
theorem so2NConformalAnomaly_matches_expectation (p N : ℝ) :
    so2NConformalAnomaly p N + 3 * p ^ 2 = 3 * (2 * p * N) := by
  rw [so2NConformalAnomaly_eq]
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBubblingSurface

end

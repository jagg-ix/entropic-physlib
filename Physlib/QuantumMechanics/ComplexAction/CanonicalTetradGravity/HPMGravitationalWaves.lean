/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.YorkCanonicalBasis

/-!
# 3-orthogonal Schwinger gauge, HPM linearization & gravitational waves (Lusanna 2015, §5)

Completes the canonical ADM tetrad-gravity arc (`CanonicalTetradGravity.TetradADMGravity`, `CanonicalTetradGravity.YorkCanonicalBasis`,
`NonHermitianComplexAction.DiracConstraints`) with §5 of L. Lusanna, IJGMMP 12 (2015) 1530001 — the **non-harmonic
3-orthogonal Schwinger time gauges**, the **Hamiltonian Post-Minkowskian (HPM) linearization**, and the
**gravitational waves**.

In the 3-orthogonal Schwinger gauge (Eq 5.1: `φ_(a) ≈ 0`, `α_(a) ≈ 0`, `θ_i ≈ 0`, `³K ≈ F`) the rotation
`V → 1`, so the `3`-metric is **diagonal**:

  `³g_rr = φ̃^{2/3} Q_r²`,   `Q_r = exp(Σ_ā γ_ār R_ā)`   (`diagMetric3`).

The HPM linearization expands around the asymptotic Minkowski background `⁴g → ⁴η`. The exact decomposition

  `log ³g_rr = (2/3) log φ̃ + 2·(Σ_ā γ_ār R_ā)`   (`diagMetric3_log`)

splits the metric eigenvalue into a **conformal (scale)** part `(2/3)log φ̃` and a **tidal (gravitational-wave)**
part `2 Σ_ā γ_ār R_ā` — and the latter is **trace-free**, `Σ_r 2(Σ_ā γ_ār R_ā) = 0` (`gw_traceless`, because
`Σ_r γ_ār = 0`): the GW perturbation is *transverse-traceless*, carrying no `3`-volume, while the conformal
factor carries the trace. The `R_ā` (`ā` ranging over the two polarizations) are the gravitational-wave
amplitudes — the genuine dynamical (tidal Dirac-observable) degrees of freedom (`tidal_recover`).

* **§A — the 3-orthogonal diagonal metric** (`diagMetric3`, `diagMetric3_minkowski`, `diagMetric3_det_three`).
* **§B — the HPM linearization & the traceless GW** (`diagMetric3_log`, `gw_traceless`).

The hyperbolic (retarded) GW evolution PDEs `□ R_ā = source`, the explicit Shanmugadhasan tidal momenta `Π_ā`
and the full HPM/Post-Newtonian Hamilton equations are the dynamical/analytic layer; the gauge-fixed metric and
the conformal/tidal (GW) split are formalized here.

## References

* L. Lusanna, IJGMMP 12 (2015) 1530001, §5 (the 3-orthogonal Schwinger gauges Eq 5.1, the diagonal
  `³g_rr = φ̃^{2/3} Q_r²`, the HPM linearization, the GW tidal variables `R_ā`).
* Repo carrier: `CanonicalTetradGravity.YorkCanonicalBasis` (`tidalFactor`, `tidalLog`, `conformal_det_three`,
  `YorkGammaOrtho`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HPMGravitationalWaves

open Finset
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.YorkCanonicalBasis

variable {m n : ℕ}


/-- **[Eq 5.1, 3-orthogonal gauge] The diagonal `3`-metric eigenvalue** `³g_rr = φ̃^{2/3} Q_r²` — in the
Schwinger gauge the rotation `V → 1`, so the `3`-metric is diagonal with eigenvalues `φ̃^{2/3} Q_r²`,
`Q_r = exp(Σ_ā γ_ār R_ā)`. -/
noncomputable def diagMetric3 (φ : ℝ) (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) (r : Fin n) : ℝ :=
  φ ^ ((2 : ℝ) / 3) * tidalFactor γ R r ^ 2

/-- **[Minkowski background] `³g_rr = 1` at `φ̃ = 1`, `R = 0`** — the asymptotic flat background `⁴g → ⁴η` the
HPM linearization expands around. -/
lemma diagMetric3_minkowski (γ : Fin m → Fin n → ℝ) (r : Fin n) :
    diagMetric3 1 γ 0 r = 1 := by
  unfold diagMetric3 tidalFactor tidalLog; simp

/-- **[`det ³g = φ̃²`] the conformal factor is the `3`-volume** — the product of the diagonal eigenvalues is
`φ̃²` (the tidal part is unimodular, `conformal_det_three`). -/
lemma diagMetric3_det_three (φ : ℝ) (hφ : 0 ≤ φ) (γ : Fin 3 → Fin 3 → ℝ) (R : Fin 3 → ℝ)
    (hγ : YorkGammaOrtho γ) : ∏ r : Fin 3, diagMetric3 φ γ R r = φ ^ (2 : ℝ) := by
  unfold diagMetric3; exact conformal_det_three φ hφ γ R hγ


/-- **[HPM conformal/tidal split] `log ³g_rr = (2/3)log φ̃ + 2 Σ_ā γ_ār R_ā`.** The (exact) logarithm of the
diagonal metric splits into a **conformal (scale)** part `(2/3)log φ̃` and a **tidal (gravitational-wave)**
part `2·tidalLog`; the HPM weak-field perturbation `h_rr ≈ log ³g_rr` is this sum. -/
lemma diagMetric3_log (φ : ℝ) (hφ : 0 < φ) (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) (r : Fin n) :
    Real.log (diagMetric3 φ γ R r) = (2 / 3) * Real.log φ + 2 * tidalLog γ R r := by
  unfold diagMetric3 tidalFactor
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hφ, Real.log_pow, Real.log_exp]
  push_cast; ring

/-- **[Transverse-traceless GW] `Σ_r 2·(Σ_ā γ_ār R_ā) = 0`.** The tidal (gravitational-wave) part of the metric
perturbation is **trace-free** — because `Σ_r γ_ār = 0`, the GW carries no `3`-volume (the conformal factor
carries the trace). The `R_ā` are the two transverse-traceless GW polarizations. -/
lemma gw_traceless (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) (hγ : YorkGammaOrtho γ) :
    ∑ r : Fin n, 2 * tidalLog γ R r = 0 := by
  rw [← Finset.mul_sum]
  have h : ∑ r : Fin n, tidalLog γ R r = 0 := by
    unfold tidalLog
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _; rw [← Finset.sum_mul, hγ.sum_zero i, zero_mul]
  rw [h, mul_zero]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HPMGravitationalWaves

end

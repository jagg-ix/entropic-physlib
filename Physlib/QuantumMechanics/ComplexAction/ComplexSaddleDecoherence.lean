/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence

/-!
# Quantum decoherence from complex saddle points (Nishimura–Watanabe 2408.16627)

Nishimura & Watanabe show that quantum decoherence in the Caldeira–Leggett model is captured by **complex saddle
points** of the real-time Feynman path integral — the complex-action analogue of instantons (real saddles of the
Euclidean action) for quantum tunneling. Evaluating the Gaussian path integral, the reduced density matrix is
`ρ_S ∝ exp(−A)` (Eq. 21) with `A` the effective action at the complex saddle `X̄ = M⁻¹C` (Eq. 18). This module
formalizes the exact-algebra core of that result — the diagonal/off-diagonal decoherence structure — and links it
to the Caldeira–Leggett entropic-damping picture of `CaldeiraLeggettDecoherence`.

The real part of the effective action is a `2×2` quadratic form in the final positions `(x_F, y_F)` that
**diagonalizes** in the average/coherence basis (Eqs. 22–23):

`Re A = ½(x_F, y_F)·[[J,−K],[−K,J]]·(x_F, y_F)ᵀ = ¼[(J−K)(x_F+y_F)² + (J+K)(x_F−y_F)²]`,

so `|ρ_S| ≃ exp[−½Γ_diag·((x_F+y_F)/2)² − ½Γ_offdiag·((x_F−y_F)/2)²]` (Eq. 26) with the **decoherence widths**
`Γ_diag = 2(J−K)`, `Γ_offdiag = 2(J+K)` (Eqs. 27–28). The off-diagonal width suppresses the **coherence**
`x_F − y_F` — decoherence — and the master equation predicts it grows **linearly** `Γ_offdiag = (8γ/β)t` (Eq. 29),
a rate `∝ γ/β = γT`, exactly the dissipation × temperature scaling of the Caldeira–Leggett damping
(`CaldeiraLeggettDecoherence.caldeiraLeggett_fluctuation_dissipation`).

* **§A — the effective-action diagonalization (Eqs. 22–23).** `reAMatrix`, `reADiag`; **`reA_diagonalized`**.
* **§B — the decoherence widths (Eqs. 26–28).** `gammaDiag = 2(J−K)`, `gammaOffdiag = 2(J+K)`;
 **`reADiag_eq_widths`** (`Re A = ½Γ_diag·avg² + ½Γ_offdiag·coh²`).
* **§C — the Gaussian off-diagonal suppression.** `rhoMagnitude = exp(−Re A)`;
 **`rhoMagnitude_coherence_le_one`** (a coherence element is suppressed when `Γ_offdiag ≥ 0`).
* **§D — linear decoherence growth (Eqs. 29–30).** `gammaOffdiagLinear = (8γ/β)t`; **`rescaledGamma_eq_t`**
 (the rescaled width `(β/8γ)(Γ_offdiag(t) − Γ_offdiag(0)) = t`) — the `∝ γT` rate matching Caldeira–Leggett.

Exact `ring`/`Real.exp` identities for the decoherence quadratic form, widths, Gaussian
suppression and the linear-growth rescaling. The complex saddle `X̄ = M⁻¹C`, the determinant prefactor `1/√det M`
and the Monte-Carlo / Lefschetz-thimble machinery are the paper's analysis, recorded not re-derived; the closed-form
decoherence structure they produce is formalized here.

## References

* J. Nishimura, H. Watanabe, arXiv:2408.16627, Eqs. 6, 18–30. Extends `CaldeiraLeggettDecoherence` (the same
 Caldeira–Leggett off-diagonal / entropic damping) via the complex-saddle real-time picture.

No new axioms.
-/

set_option autoImplicit false

open scoped Real
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexSaddleDecoherence

/-! ## §A — the effective-action diagonalization (Eqs. 22–23) -/

/-- The **real part of the effective action** as the `2×2` quadratic form `Re A = ½(x, y)·[[J,−K],[−K,J]]·(x, y)ᵀ`
(Eq. 22) — `J, K` are the real parts of the coupling contracted with the inverse saddle matrix (Eqs. 24–25). -/
noncomputable def reAMatrix (J K x y : ℝ) : ℝ := (1 / 2) * (J * x ^ 2 - K * x * y - K * y * x + J * y ^ 2)

/-- The **diagonalized form** `Re A = ¼[(J−K)(x+y)² + (J+K)(x−y)²]` (Eq. 23) — in the average `x+y` and coherence
`x−y` basis. -/
noncomputable def reADiag (J K x y : ℝ) : ℝ :=
  (1 / 4) * ((J - K) * (x + y) ^ 2 + (J + K) * (x - y) ^ 2)

/-- **The effective-action quadratic form diagonalizes (Eqs. 22 = 23)** — the `2×2` matrix `[[J,−K],[−K,J]]` is
diagonal in the `45°`-rotated average/coherence basis, decoupling the diagonal (`x+y`) and off-diagonal (`x−y`)
directions of the reduced density matrix. -/
theorem reA_diagonalized (J K x y : ℝ) : reAMatrix J K x y = reADiag J K x y := by
  unfold reAMatrix reADiag; ring

/-! ## §B — the decoherence widths (Eqs. 26–28) -/

/-- The **diagonal decoherence width** `Γ_diag = 2(J−K)` (Eq. 27) — the fall-off in the diagonal (`x+y`) direction. -/
noncomputable def gammaDiag (J K : ℝ) : ℝ := 2 * (J - K)

/-- The **off-diagonal decoherence width** `Γ_offdiag = 2(J+K)` (Eq. 28) — the fall-off of the *coherence*
(`x−y`); its growth **is** quantum decoherence. -/
noncomputable def gammaOffdiag (J K : ℝ) : ℝ := 2 * (J + K)

/-- **The effective action in terms of the widths (Eq. 26)** `Re A = ½Γ_diag·((x+y)/2)² + ½Γ_offdiag·((x−y)/2)²`
— so `|ρ_S| = exp(−Re A)` is Gaussian in the average and coherence with widths `Γ_diag, Γ_offdiag`. -/
theorem reADiag_eq_widths (J K x y : ℝ) :
    reADiag J K x y
      = (1 / 2) * gammaDiag J K * ((x + y) / 2) ^ 2
        + (1 / 2) * gammaOffdiag J K * ((x - y) / 2) ^ 2 := by
  unfold reADiag gammaDiag gammaOffdiag; ring

/-! ## §C — the Gaussian off-diagonal suppression -/

/-- The **magnitude of the reduced density matrix** `|ρ_S| = exp(−Re A)` (Eqs. 21, 26). -/
noncomputable def rhoMagnitude (J K x y : ℝ) : ℝ := Real.exp (-reADiag J K x y)

/-- **A coherence element is suppressed** — for a pure off-diagonal element `y = −x` (average `= 0`, coherence
`= 2x`), `|ρ_S| = exp(−(J+K)x²) ≤ 1` when the off-diagonal width `Γ_offdiag = 2(J+K) ≥ 0`: decoherence damps the
off-diagonal coherence of the reduced density matrix. -/
theorem rhoMagnitude_coherence_le_one (J K x : ℝ) (h : 0 ≤ gammaOffdiag J K) :
    rhoMagnitude J K x (-x) ≤ 1 := by
  rw [rhoMagnitude, Real.exp_le_one_iff, reADiag]
  have hJK : 0 ≤ J + K := by unfold gammaOffdiag at h; linarith
  nlinarith [sq_nonneg (x - -x), hJK]

/-! ## §D — linear decoherence growth (Eqs. 29–30) -/

/-- The **master-equation off-diagonal width** `Γ_offdiag(t) = (8γ/β)t` (Eq. 29) — at small coupling and high
temperature (`β = 1/T` small), decoherence grows **linearly** in time at a rate `∝ γ/β = γT`. -/
noncomputable def gammaOffdiagLinear (γ β t : ℝ) : ℝ := 8 * γ / β * t

/-- **The rescaled decoherence width is the time (Eq. 30)** `(β/8γ)(Γ_offdiag(t) − Γ_offdiag(0)) = t` — the
scaling collapse of the linear growth, exhibiting `Γ_offdiag ∝ (γ/β)t = γTt`. The rate `γ/β = γT` is the same
dissipation × temperature scaling as the Caldeira–Leggett damping coefficient `2MγkT`
(`CaldeiraLeggettDecoherence.caldeiraLeggett_fluctuation_dissipation`). -/
theorem rescaledGamma_eq_t (γ β t : ℝ) (hγ : γ ≠ 0) (hβ : β ≠ 0) :
    β / (8 * γ) * (gammaOffdiagLinear γ β t - gammaOffdiagLinear γ β 0) = t := by
  unfold gammaOffdiagLinear
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.ComplexSaddleDecoherence

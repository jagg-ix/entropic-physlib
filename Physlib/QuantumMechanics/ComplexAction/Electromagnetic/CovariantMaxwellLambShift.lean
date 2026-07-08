/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-!
# The covariant Maxwell equations and the Lamb shift

Formalizes the **covariant Maxwell equations** on top of the repo's `F = dA` field strength
(`PTSymmetricQFT.MaxwellFaraday.faraday`), and the **Lamb shift** — the QED splitting of the `2S₁⁄₂`–`2P₁⁄₂`
hydrogen levels that the Dirac equation leaves degenerate. The two are physically linked: the Lamb shift is
the radiative energy shift produced by the electron's coupling to the quantized covariant Maxwell (radiation)
field, whose on-shell photon is *massless* — exactly the Lorenz-gauge wave equation of §A — and whose vacuum
fluctuations Bethe summed to the logarithmic shift of §B.

* **§A — the covariant Maxwell equations** (`maxwellCurrent`, `maxwell_current_conserved`,
  `maxwell_lorenz_wave`). The inhomogeneous equation `∂_β F^{αβ} = J^α` defines the four-current; current
  conservation `∂_α J^α = 0` follows from the antisymmetry of `F` (a symmetric `k_α k_β` contracted with the
  antisymmetric `F`); in Lorenz gauge `∂·A = 0` the equation reduces to the massless wave operator
  `∂_β F^{αβ} = −(k·k) A^α` (via `maxwellOp_faraday`). The homogeneous equation `dF = 0` is
  `PTSymmetricQFT.MaxwellFaraday.faraday_bianchi` — the first Bianchi identity, the BCJ kinematic Jacobi.
* **§B — the Bethe Lamb shift** (`betheLambShift`, `betheLambShift_pos`). The leading non-relativistic shift
  `ΔE = (4/3)(α⁵/πn³)·L`, with `L` the Bethe logarithm (positive for an `S` state) — the `α⁵/n³` scaling.
* **§C — lifting the Dirac degeneracy** (`diracFineStructure`, `dirac_2S_2P_degenerate`, `observedEnergy`,
  `lamb_lifts_degeneracy`, `lamb_2S_above_2P`). The Dirac fine-structure energy depends only on `(n, j)`, not
  on `l`, so `2S₁⁄₂` and `2P₁⁄₂` are degenerate; the Lamb shift acts only on the `l = 0` (`S`) state, so the
  observed `2S₁⁄₂ − 2P₁⁄₂` splitting *is* the Lamb shift, placing `2S₁⁄₂` above `2P₁⁄₂`.

## References

* H. A. Bethe, *The Electromagnetic Shift of Energy Levels*, Phys. Rev. 72 (1947) 339 (the `α⁵ ln` shift).
* W. E. Lamb, R. C. Retherford, Phys. Rev. 72 (1947) 241 (the `2S₁⁄₂`–`2P₁⁄₂` splitting).
* Repo dependencies: `PTSymmetricQFT.MaxwellFaraday` (`faraday`, `maxwellOp`, `maxwellOp_faraday`,
  `faraday_bianchi`, `faraday_antisymm`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics

/-! ## §A — the covariant Maxwell equations -/

/-- **[Inhomogeneous Maxwell] The four-current** `J^α = ∂_β F^{αβ}` — in momentum space the divergence
`F^{αβ} k_β` of the field strength (`PTSymmetricQFT.PTTensorDynamics.maxwellOp`). -/
noncomputable def maxwellCurrent (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : Fin 4 → ℝ :=
  maxwellOp F k

/-- **[Current conservation] `∂_α J^α = 0`.** The four-current of any antisymmetric field strength is
conserved: `k_α F^{αβ} k_β = 0` is a symmetric `k_α k_β` contracted with the antisymmetric `F`. (For
`F = dA` the antisymmetry is `faraday_antisymm`.) -/
theorem maxwell_current_conserved (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ)
    (hF : ∀ μ ν, F μ ν = - F ν μ) : ∑ α, k α * maxwellCurrent F k α = 0 := by
  have e : (∑ α, k α * maxwellCurrent F k α) = ∑ α, ∑ β, k α * F α β * k β := by
    apply Finset.sum_congr rfl; intro α _
    simp only [maxwellCurrent, maxwellOp, Finset.mul_sum, mul_assoc]
  rw [e]
  have hswap : (∑ α, ∑ β, k α * F α β * k β) = ∑ α, ∑ β, k β * F β α * k α := Finset.sum_comm
  have hzero : (∑ α, ∑ β, k α * F α β * k β) + (∑ α, ∑ β, k β * F β α * k α) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro α _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro β _
    rw [hF β α]; ring
  rw [← hswap] at hzero
  linarith

/-- **[Lorenz-gauge wave equation] `∂_β F^{αβ} = −(k·k) A^α`.** In Lorenz gauge `∂·A = A·k = 0`, the
inhomogeneous Maxwell equation for `F = dA` becomes the **massless** vector wave operator `−□A = J` (via
`maxwellOp_faraday`). This massless photon is the radiation field whose vacuum fluctuations produce the Lamb
shift of §B. -/
theorem maxwell_lorenz_wave (k A : Fin 4 → ℝ) (hL : ∑ β, A β * k β = 0) :
    maxwellCurrent (faraday k A) k = fun α => -(∑ β, k β * k β) * A α := by
  rw [maxwellCurrent, maxwellOp_faraday]; funext α; rw [hL]; ring

/-! ## §B — the Bethe Lamb shift -/

/-- **[Bethe 1947] The leading Lamb shift** `ΔE = (4/3)(α⁵ / πn³)·L`, with `L` the Bethe logarithm. The
characteristic `α⁵/n³` scaling of the electron self-energy. -/
noncomputable def betheLambShift (α L : ℝ) (n : ℕ) : ℝ := (4 / 3) * α ^ 5 / (Real.pi * n ^ 3) * L

/-- **The Lamb shift is positive** for a real coupling and a positive Bethe log. -/
theorem betheLambShift_pos (α L : ℝ) (n : ℕ) (hα : 0 < α) (hL : 0 < L) (hn : 0 < n) :
    0 < betheLambShift α L n := by unfold betheLambShift; positivity

/-! ## §C — the Lamb shift lifts the Dirac degeneracy -/

/-- **The Dirac fine-structure energy** `E_{n,j} = [1 + (Zα)²/(n − (j+½) + √((j+½)² − (Zα)²))²]^{−1/2}`
(in units `mc² = 1`). It depends only on the principal number `n` and the total angular momentum `j` — *not*
on the orbital `l`. -/
noncomputable def diracFineStructure (Zα : ℝ) (n : ℕ) (j : ℝ) : ℝ :=
  1 / Real.sqrt (1 + Zα ^ 2 / (n - (j + 1 / 2) + Real.sqrt ((j + 1 / 2) ^ 2 - Zα ^ 2)) ^ 2)

/-- **The Dirac energy of a hydrogen state** `(n, l, j)` — depends only on `(n, j)` (the orbital `l` is
intentionally absent: that `l`-independence is the degeneracy). -/
noncomputable def diracStateEnergy (Zα : ℝ) (n _l : ℕ) (j : ℝ) : ℝ := diracFineStructure Zα n j

/-- **[Dirac degeneracy] `2S₁⁄₂` and `2P₁⁄₂` are degenerate.** Both states have `(n, j) = (2, ½)` (differing
only in `l = 0` vs `l = 1`), so the Dirac equation assigns them the *same* energy — the degeneracy the Lamb
shift breaks. -/
theorem dirac_2S_2P_degenerate (Zα : ℝ) :
    diracStateEnergy Zα 2 0 (1 / 2) = diracStateEnergy Zα 2 1 (1 / 2) := rfl

/-- The radiative (Lamb) contribution: nonzero only for the `l = 0` (`S`) state, where the electron's
wavefunction overlaps the nucleus and the self-energy is largest. -/
noncomputable def lambTerm (α L : ℝ) (n l : ℕ) : ℝ := if l = 0 then betheLambShift α L n else 0

/-- **The observed (QED) energy** = Dirac fine structure + the radiative Lamb contribution. -/
noncomputable def observedEnergy (Zα α L : ℝ) (n l : ℕ) (j : ℝ) : ℝ :=
  diracStateEnergy Zα n l j + lambTerm α L n l

/-- **[Lamb 1947] The `2S₁⁄₂ − 2P₁⁄₂` splitting is the Lamb shift.** The Dirac fine-structure energies cancel
(degeneracy), so the observed splitting equals the radiative shift on the `S` state alone — the Lamb shift. -/
theorem lamb_lifts_degeneracy (Zα α L : ℝ) :
    observedEnergy Zα α L 2 0 (1 / 2) - observedEnergy Zα α L 2 1 (1 / 2) = betheLambShift α L 2 := by
  simp [observedEnergy, diracStateEnergy, lambTerm]

/-- **`2S₁⁄₂` lies above `2P₁⁄₂`.** The Lamb shift is positive, so it raises the `S` level above the
(degenerate-in-Dirac) `P` level — the measured sign of the Lamb shift. -/
theorem lamb_2S_above_2P (Zα α L : ℝ) (hα : 0 < α) (hL : 0 < L) :
    observedEnergy Zα α L 2 1 (1 / 2) < observedEnergy Zα α L 2 0 (1 / 2) := by
  have h := lamb_lifts_degeneracy Zα α L
  have hp := betheLambShift_pos α L 2 hα hL (by norm_num)
  linarith

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift

end

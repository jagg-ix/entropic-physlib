/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Current ∥ drift from velocity reflection (Markov et al. 1992, Lemma 3 / Eq. 2.39)

Formalizes **Lemma 3** of *Markov, Rudykh, Sidorov, Sinitsyn, Tolstonogov, Acta Appl. Math. 28 (1992)*: if a
distribution is symmetric under reflection of velocity about the drift `d`,

  `f(V + d) = f(−V + d)`   (equivalently `f ∘ (V ↦ 2d − V) = f`),

then the current is *parallel to the drift*, `j = d·p` (Eq. 2.39), where `j = ∫Vf` and `p = ∫f`. The reflection
`V ↦ 2d − V` is exactly the **velocity time reversal** `V ↦ −V` of `Vlasov.DiamondTimeReversal` in the
drift frame (the peculiar velocity `ξ = V − d` obeys `ξ ↦ −ξ`). The proof is the symmetrization
`j = ∫(2d − V)f = 2d·p − j`, hence `j = d·p`.

* **§A — the drift reflection** (`driftReflect`, `driftReflect_apply`, `driftReflect_involution`,
  `driftReflect_sub_drift`, `driftReflect_zero`, `vlasovEnergy_driftReflect_zero`). `R_d(V) = 2d − V` is an
  involution; the peculiar velocity flips `R_d(V) − d = −(V − d)`; at zero drift it is the bare time reversal
  `V ↦ −V`, under which the Vlasov energy is invariant (`Vlasov.DiamondTimeReversal`).
* **§B — Lemma 3 (Eq. 2.39)** (`charge`, `current`, `current_eq_drift_smul_charge`). For a reflection-paired
  velocity sampling (`σ` the pairing, `V(σk) = 2d − V k`, `f(σk) = f k`), the current is `jᵢ = dᵢ·p`.
* **§C — the time-reversal corollary** (`timeReversal_symmetric_no_current`). A `V ↦ −V`–symmetric
  distribution records *no* current (`j = 0`) — no current without drift.

## References

* Y. Markov et al., Acta Appl. Math. 28 (1992), Lemma 3 / Eqs. 2.38–2.39.
* Repo dependencies: `Vlasov.DiamondTimeReversal` (`vlasovEnergy`, `vlasovEnergy_timeReversal`, the velocity
  time reversal `V ↦ −V`); `Vlasov.MaxwellSteadyState` (the steady distributions whose current this is).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Vlasov.CurrentChargeReflection

open Finset
open Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal

/-! ## §A — the drift reflection `R_d(V) = 2d − V` -/

/-- **The velocity reflection about the drift** `R_d(V) = 2d − V`. -/
def driftReflect (d V : Fin 3 → ℝ) : Fin 3 → ℝ := (2 : ℝ) • d - V

/-- **Componentwise** `R_d(V)ᵢ = 2dᵢ − Vᵢ`. -/
theorem driftReflect_apply (d V : Fin 3 → ℝ) (i : Fin 3) : driftReflect d V i = 2 * d i - V i := by
  simp [driftReflect]

/-- **The drift reflection is an involution** `R_d(R_d V) = V`. -/
theorem driftReflect_involution (d V : Fin 3 → ℝ) : driftReflect d (driftReflect d V) = V := by
  funext i; rw [driftReflect_apply, driftReflect_apply]; ring

/-- **The peculiar velocity flips sign** `R_d(V) − d = −(V − d)` — in the drift frame `ξ = V − d` the
reflection is the velocity time reversal `ξ ↦ −ξ` of `Vlasov.DiamondTimeReversal`. -/
theorem driftReflect_sub_drift (d V : Fin 3 → ℝ) : driftReflect d V - d = -(V - d) := by
  funext i; simp only [Pi.sub_apply, Pi.neg_apply, driftReflect_apply]; ring

/-- **At zero drift the reflection is the bare time reversal** `R_0(V) = −V`. -/
theorem driftReflect_zero (V : Fin 3 → ℝ) : driftReflect 0 V = -V := by
  simp [driftReflect]

/-- **The Vlasov energy is invariant under the zero-drift reflection** — `R = −α|V|² + φ` is `T`-even, the
`d = 0` case of `Vlasov.DiamondTimeReversal.vlasovEnergy_timeReversal`. -/
theorem vlasovEnergy_driftReflect_zero (α φ : ℝ) (V : Fin 3 → ℝ) :
    vlasovEnergy α φ (driftReflect 0 V) = vlasovEnergy α φ V := by
  rw [driftReflect_zero]; exact vlasovEnergy_timeReversal α φ V

/-! ## §B — Lemma 3: the current–charge relation (Eq. 2.39) -/

/-- **The charge density** `p = ∑ₖ fₖ` of a velocity sampling. -/
noncomputable def charge {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ := ∑ k, f k

/-- **The current density** `jᵢ = ∑ₖ Vₖᵢ fₖ`. -/
noncomputable def current {ι : Type*} [Fintype ι] (V : ι → Fin 3 → ℝ) (f : ι → ℝ) (i : Fin 3) : ℝ :=
  ∑ k, V k i * f k

/-- **[Lemma 3, Eq. 2.39] The current is parallel to the drift** `jᵢ = dᵢ·p`. For a reflection-paired
velocity sampling — `σ` pairing each sample with its mirror `V(σk) = 2d − Vk` (Eq. 2.38) and `f(σk) = fk` —
the symmetrization `j = ∫(2d − V)f = 2d·p − j` forces `j = d·p`. -/
theorem current_eq_drift_smul_charge {ι : Type*} [Fintype ι] (d : Fin 3 → ℝ)
    (V : ι → Fin 3 → ℝ) (f : ι → ℝ) (σ : Equiv.Perm ι)
    (hrefl : ∀ k, V (σ k) = driftReflect d (V k)) (hinv : ∀ k, f (σ k) = f k) (i : Fin 3) :
    current V f i = d i * charge f := by
  have key : current V f i + current V f i = 2 * d i * charge f := by
    unfold current charge
    have e : (∑ k, V k i * f k) = ∑ k, V (σ k) i * f (σ k) :=
      (Equiv.sum_comp σ (fun k => V k i * f k)).symm
    nth_rewrite 2 [e]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hinv k, hrefl k, driftReflect_apply]
    ring
  linarith

/-! ## §C — the time-reversal corollary -/

/-- **[No current without drift] A velocity-time-reversal-symmetric distribution has no current.** If the
sampling is symmetric under the bare `V ↦ −V` reversal (`Vlasov.DiamondTimeReversal`), i.e. zero drift,
then `j = 0` — current requires a net drift. -/
theorem timeReversal_symmetric_no_current {ι : Type*} [Fintype ι] (V : ι → Fin 3 → ℝ) (f : ι → ℝ)
    (σ : Equiv.Perm ι) (hrefl : ∀ k, V (σ k) = -V k) (hinv : ∀ k, f (σ k) = f k) (i : Fin 3) :
    current V f i = 0 := by
  have h := current_eq_drift_smul_charge (0 : Fin 3 → ℝ) V f σ
    (fun k => by rw [hrefl k]; simp [driftReflect]) hinv i
  simpa using h

end Physlib.QuantumMechanics.ComplexAction.Vlasov.CurrentChargeReflection

end

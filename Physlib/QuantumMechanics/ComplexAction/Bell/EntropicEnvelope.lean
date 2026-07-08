/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

/-!
# The CHSH entropic envelope: concurrence, dephasing, and the Tsirelson bound

Formalizes the complex-action/entropic-time **CHSH entropic envelope** of the complex-action document (§"re-evaluate the
Bell inequalities", the universal upper-envelope): the maximal CHSH value of a two-qubit state is
controlled by its **concurrence** `C`,

  `S_CHSH ≤ 2√(1 + C²)`   (`chshEnvelope`),

bounded below by the classical / local bound `2` (at `C = 0`, separable) and above by the **Tsirelson**
bound `2√2` (at `C = 1`, maximally entangled). Under the communicative ("entropic") sector the
concurrence **decays** as `C(t) = C₀·e^{−Φ_ent(t)}` with `Φ_ent = ∫Γ_ent`,
`Γ_ent = (2/ħ)⟨−H_I^eff⟩` — the same `H_I` / imaginary-action engine of the Hyperbolic Unification
(`MuonAnomaly.SchmidtRapidityHyperbolicUnification`) — so the violation decays monotonically from Tsirelson toward
the classical bound (`chsh_dephasing_monotone`), always respecting `S_CHSH ≤ 2√2`
(`chsh_dephasing_le_tsirelson`). This is the time-dependent, dissipative face of the static CHSH bounds
of `Bell.DeterministicBounds`, and of `AlgebraicQFT.SummersVacuumBellCHSH`.

* **§A — the envelope** (`chshEnvelope`, `chshEnvelope_ge_classical`, `chshEnvelope_le_tsirelson`,
  `chshEnvelope_separable`, `chshEnvelope_maximal`).
* **§B — the entropic decay** (`chsh_dephasing_le_tsirelson`, `chsh_dephasing_monotone`).
* **§C — the envelope, assembled** (`chsh_entropic_envelope`).

The **Horodecki** spectral form `S_CHSH^max = 2√(λ₁+λ₂)` (largest eigenvalues of `TᵀTᵀ`,
`T_kl = Tr[ρ σ_k⊗σ_l]`) is the operator-level source of `chshEnvelope`; here it is captured at the
concurrence level.

## References

* complex-action/entropic-time complex-action document (CHSH entropic envelope, `S_CHSH ≤ 2√(1+C²)`, `C(t) = C₀e^{−Φ_ent}`);
  R. Horodecki, P. Horodecki, M. Horodecki, Phys. Lett. A 200 (1995) 340 (the `2√(λ₁+λ₂)` criterion);
  B. Tsirelson, Lett. Math. Phys. 4 (1980) 93. Repo dependencies: `Bell.DeterministicBounds`
  (`tsirelsonWitness`), `MuonAnomaly.SchmidtRapidityHyperbolicUnification` (the `H_I` / entropic engine).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope

open Real
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds

/-! ## §A — the CHSH entropic envelope -/

/-- **The CHSH entropic envelope** `S_CHSH ≤ 2√(1 + C²)` — the maximal CHSH value of a two-qubit state
as a function of its concurrence `C` (the convex entanglement monotone). -/
noncomputable def chshEnvelope (C : ℝ) : ℝ := 2 * Real.sqrt (1 + C ^ 2)

/-- **[The envelope is above the classical bound] `2 ≤ 2√(1+C²)`.** The CHSH envelope is always at least
the local / classical bound `2` (`1 + C² ≥ 1`), with equality iff `C = 0`. -/
theorem chshEnvelope_ge_classical (C : ℝ) : 2 ≤ chshEnvelope C := by
  unfold chshEnvelope
  have h1 : (1 : ℝ) ≤ 1 + C ^ 2 := by nlinarith [sq_nonneg C]
  have h2 : Real.sqrt 1 ≤ Real.sqrt (1 + C ^ 2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_one] at h2
  linarith

/-- **[The envelope is below Tsirelson] `2√(1+C²) ≤ 2√2`** for `|C| ≤ 1` (`C² ≤ 1`). The CHSH violation
never exceeds the Tsirelson bound `2√2` (`= Bell.DeterministicBounds.tsirelsonWitness`). -/
theorem chshEnvelope_le_tsirelson (C : ℝ) (hC : C ^ 2 ≤ 1) : chshEnvelope C ≤ tsirelsonWitness := by
  unfold chshEnvelope tsirelsonWitness
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt; linarith

/-- **[Separable saturates the classical bound] `C = 0 ⟹ S_CHSH = 2`.** A separable state (zero
concurrence) gives the classical CHSH value `2` — no Bell violation. -/
theorem chshEnvelope_separable : chshEnvelope 0 = 2 := by
  unfold chshEnvelope; norm_num

/-- **[Maximally entangled saturates Tsirelson] `C = 1 ⟹ S_CHSH = 2√2`.** A maximally entangled state
(unit concurrence) reaches the Tsirelson bound `2√2` — maximal Bell violation. -/
theorem chshEnvelope_maximal : chshEnvelope 1 = tsirelsonWitness := by
  unfold chshEnvelope tsirelsonWitness; norm_num

/-! ## §B — the entropic decay of the violation -/

/-- **[Dephased CHSH stays below Tsirelson] `S_CHSH(t) ≤ 2√2`.** Under entropic dephasing the
concurrence decays to `C₀·e^{−Φ}` (`Φ = Φ_ent ≥ 0`); since `|C₀e^{−Φ}| ≤ |C₀| ≤ 1`, the dephased CHSH
envelope still respects the Tsirelson bound. -/
theorem chsh_dephasing_le_tsirelson (C₀ Φ : ℝ) (hC₀ : C₀ ^ 2 ≤ 1) (hΦ : 0 ≤ Φ) :
    chshEnvelope (C₀ * Real.exp (-Φ)) ≤ tsirelsonWitness := by
  apply chshEnvelope_le_tsirelson
  rw [mul_pow]
  have he : Real.exp (-Φ) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]; exact Real.exp_le_exp.mpr (by linarith)
  have hep : 0 < Real.exp (-Φ) := Real.exp_pos _
  have he2 : Real.exp (-Φ) ^ 2 ≤ 1 := by nlinarith [he, hep]
  nlinarith [mul_nonneg (sq_nonneg C₀) (by linarith [he2] : (0 : ℝ) ≤ 1 - Real.exp (-Φ) ^ 2), hC₀]

/-- **[The violation decays with entropic time] monotone in `Φ_ent`.** As the entropic phase
`Φ_ent = ∫Γ_ent` grows (more communicative dissipation), the concurrence `C₀·e^{−Φ}` shrinks and the
CHSH envelope **decreases** — the Bell violation decays monotonically from Tsirelson toward the
classical bound (for `C₀ ≥ 0`). -/
theorem chsh_dephasing_monotone (C₀ Φ₁ Φ₂ : ℝ) (hC₀ : 0 ≤ C₀) (hΦ : Φ₁ ≤ Φ₂) :
    chshEnvelope (C₀ * Real.exp (-Φ₂)) ≤ chshEnvelope (C₀ * Real.exp (-Φ₁)) := by
  unfold chshEnvelope
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt
  have he : Real.exp (-Φ₂) ≤ Real.exp (-Φ₁) := Real.exp_le_exp.mpr (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left he hC₀, Real.exp_pos (-Φ₂), Real.exp_pos (-Φ₁),
    mul_nonneg hC₀ (Real.exp_pos (-Φ₂)).le]

/-! ## §C — the envelope, assembled -/

/-- **[The CHSH entropic envelope, assembled].** The maximal CHSH value is bounded between the classical
`2` (`chshEnvelope_ge_classical`) and the Tsirelson `2√2` (`chshEnvelope_le_tsirelson`), saturated at
separable `C = 0` (`chshEnvelope_separable`) and maximally entangled `C = 1` (`chshEnvelope_maximal`);
under entropic dephasing it decays monotonically toward the classical bound
(`chsh_dephasing_monotone`) while always respecting Tsirelson (`chsh_dephasing_le_tsirelson`). The Bell
violation is the concurrence read through the `√(1+C²)` envelope, with its decay driven by the same
`H_I` / imaginary-action engine as the Hyperbolic Unification. -/
theorem chsh_entropic_envelope (C₀ Φ : ℝ) (hC₀nn : 0 ≤ C₀) (hC₀ : C₀ ^ 2 ≤ 1) (hΦ : 0 ≤ Φ) :
    2 ≤ chshEnvelope C₀
      ∧ chshEnvelope C₀ ≤ tsirelsonWitness
      ∧ chshEnvelope 0 = 2
      ∧ chshEnvelope 1 = tsirelsonWitness
      ∧ chshEnvelope (C₀ * Real.exp (-Φ)) ≤ tsirelsonWitness :=
  ⟨chshEnvelope_ge_classical C₀, chshEnvelope_le_tsirelson C₀ hC₀,
    chshEnvelope_separable, chshEnvelope_maximal, chsh_dephasing_le_tsirelson C₀ Φ hC₀ hΦ⟩

end Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope

end

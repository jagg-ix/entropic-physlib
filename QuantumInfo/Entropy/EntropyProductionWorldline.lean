/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.GCongr

/-!
# Entropic proper time as a consequence of second-law entropy production

The imaginary action `S_I : ℝ → ℝ` accumulated along a worldline is
the primary, load-bearing quantity. The **entropic proper time**

  `τ_ent(t) := S_I(t) / ℏ`

is *defined from* it; its monotonicity along the worldline is *derived
from* the second law (`S_I` monotone non-decreasing). The arrow of
time `dτ_ent ≥ 0` is therefore a **side effect** of accumulated
entropy production, not an independent input.

This module makes that asymmetry explicit at the structural level:
the second-law hypothesis lives as a single monotonicity field of
`EntropyProductionWorldline`, and every fact about `τ_ent` —
monotonicity, the time-order ↔ entropy-order equivalence, the
sign — is derived from it.

The pointwise non-negativity inputs that the second law builds on
already live on physlib:

* `Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger`
  provides `entropyRate_nonneg` for the non-Hermitian Schrödinger
  structure: `entropyRate ψ = (2/ℏ)·⟨ψ|H_I|ψ⟩ ≥ 0` whenever the
  irreversible generator `H_I` is positive semidefinite.
* `Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate` provides
  `gklsEntropicRate_nonneg` for the GKLS rate
  `λ_GKLS(L, ρ) = ∑_j (Tr(L_j^† L_j ρ)).re ≥ 0`.
* `Physlib.SpaceAndTime.EntropicProperTime` provides
  `relativeEntropyTime_nonneg` for the static state-pair gap
  `(ℏ/(k_B T_∞)) · D(ρ‖σ) ≥ 0`.

This file lifts those pointwise rates to a **worldline-level**
statement: given any time profile of accumulated imaginary action
that respects the second law (`S_I` monotone), the resulting
entropic time `τ_ent := S_I/ℏ` is monotone *as a theorem*, not as a
postulate.

## Key results

- `EntropyProductionWorldline` — the structure, with `S_I` monotone
  (the second law) as the only non-trivial structural hypothesis.
- `EntropyProductionWorldline.entropicProperTime` — definition
  `τ_ent(t) := S_I(t) / ℏ`.
- `EntropyProductionWorldline.entropicProperTime_monotone` —
  monotonicity of `τ_ent` is a derived consequence of the second
  law and `ℏ > 0`.
- `EntropyProductionWorldline.entropicProperTime_le_iff` — time
  order is *exactly* entropy order:
  `τ_ent(t₁) ≤ τ_ent(t₂) ⟺ S_I(t₁) ≤ S_I(t₂)`. The entropic time
  has no ordering information beyond accumulated entropy.
- `EntropyProductionWorldline.entropicProperTime_nonneg_of_S_I_nonneg`
  — sign preservation.

## References

- **Clausius 1865** — *Über verschiedene für die Anwendung bequeme
  Formen der Hauptgleichungen der mechanischen Wärmetheorie*,
  Annalen der Physik 201(7), 353–400, doi:10.1002/andp.18652010702 —
  the original second-law statement `dS ≥ dQ/T` (his §6 Eq. 8) and
  the introduction of the term "entropy" (his §14, p. 390).
- **Spohn 1978** — *Entropy production for quantum dynamical
  semigroups*, J. Math. Phys. 19(5), 1227–1230,
  doi:10.1063/1.523789, Theorem 3 — non-negativity of the entropy
  production rate for a quantum dynamical semigroup. The
  pointwise input for the second-law hypothesis stated here.
- **Sergi & Giaquinta 2016** — *Linear Quantum Entropy and
  Non-Hermitian Hamiltonians*, Entropy 18(12), 451,
  doi:10.3390/e18120451, §II Eq. (3), pp. 2–3 — the
  imaginary-action / decay-rate identification driving
  `dS_I/dt = (2/ℏ)·⟨Γ̂⟩ ≥ 0`.
- **Lieb & Yngvason 1999** — *The physics and mathematics of the
  second law of thermodynamics*, Physics Reports 310(1), 1–96,
  doi:10.1016/S0370-1573(98)00082-9 — axiomatic treatment of the
  second law via comparability and entropy as a monotone state
  function, the abstract setting that the worldline-level
  monotonicity here instantiates.
-/

@[expose] public section

noncomputable section

namespace QuantumInfo.Finite

/-- A worldline along which the imaginary action `S_I` is monotone
non-decreasing (the second law) and the entropic proper time is
defined as `τ_ent := S_I/ℏ`. The single non-trivial structural
hypothesis is `S_I_monotone`; the monotonicity of `τ_ent` and the
time-order ↔ entropy-order equivalence are theorems of physlib
about this structure. -/
structure EntropyProductionWorldline where
  /-- Imaginary action `S_I : ℝ → ℝ` accumulated along the worldline. -/
  S_I : ℝ → ℝ
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- `ℏ > 0`. -/
  hbar_pos : 0 < hbar
  /-- **The second law.** The imaginary action is monotone
  non-decreasing along the worldline. -/
  S_I_monotone : Monotone S_I

namespace EntropyProductionWorldline

variable (W : EntropyProductionWorldline)

/-- The **entropic proper time** along the worldline:
`τ_ent(t) := S_I(t) / ℏ`. Defined *from* the imaginary action, not
postulated independently. -/
def entropicProperTime (t : ℝ) : ℝ := W.S_I t / W.hbar

/-- **Entropic proper time is monotone non-decreasing — a derived
consequence of the second law.** The arrow of time `dτ_ent ≥ 0` is
a side effect of accumulated entropy production `dS_I ≥ 0`, not an
independent input.

**Source.** Lieb & Yngvason 1999,
doi:10.1016/S0370-1573(98)00082-9, §II — entropy as a monotone
state function. Spohn 1978, doi:10.1063/1.523789, Theorem 3 — the
quantum-dynamical-semigroup pointwise rate `≥ 0` that feeds this
worldline-level statement. -/
theorem entropicProperTime_monotone : Monotone W.entropicProperTime := by
  intro t₁ t₂ hle
  unfold entropicProperTime
  have hpos : 0 ≤ W.hbar := W.hbar_pos.le
  have hS := W.S_I_monotone hle
  exact div_le_div_of_nonneg_right hS hpos

/-- **Time order is exactly entropy order.** `τ_ent` has no
ordering information beyond accumulated entropy — it is a strictly
monotone readout of `S_I`. Note this uses only `ℏ > 0`, *not* the
second-law hypothesis: the equivalence is structural, the
monotonicity claim is the one that needs the second law. -/
theorem entropicProperTime_le_iff (t₁ t₂ : ℝ) :
    W.entropicProperTime t₁ ≤ W.entropicProperTime t₂ ↔
      W.S_I t₁ ≤ W.S_I t₂ := by
  unfold entropicProperTime
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h W.hbar_pos.le
    rwa [div_mul_cancel₀ _ W.hbar_pos.ne',
         div_mul_cancel₀ _ W.hbar_pos.ne'] at hmul
  · intro h
    exact div_le_div_of_nonneg_right h W.hbar_pos.le

/-- Sign of entropic time tracks sign of accumulated imaginary
action: `0 ≤ S_I(t) ⟹ 0 ≤ τ_ent(t)`. Uses only `ℏ > 0`. -/
theorem entropicProperTime_nonneg_of_S_I_nonneg
    (t : ℝ) (h : 0 ≤ W.S_I t) :
    0 ≤ W.entropicProperTime t := by
  unfold entropicProperTime
  exact div_nonneg h W.hbar_pos.le

/-- If the imaginary action vanishes at some reference instant
`t₀`, then by the second law (`S_I` monotone non-decreasing)
the entropic proper time is non-negative at every later instant
`t ≥ t₀`. The arrow of time emerges from the second law applied
to a reference origin. -/
theorem entropicProperTime_nonneg_of_S_I_zero_at_origin
    (t₀ t : ℝ) (h₀ : W.S_I t₀ = 0) (hle : t₀ ≤ t) :
    0 ≤ W.entropicProperTime t := by
  have h1 : 0 ≤ W.S_I t := by rw [← h₀]; exact W.S_I_monotone hle
  exact W.entropicProperTime_nonneg_of_S_I_nonneg t h1

end EntropyProductionWorldline

end QuantumInfo.Finite

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.ZenoSpectralTimeUnification
public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.RelationalTime.EntropicThermalComplementarity

/-!
# Three clocks by the sign of the spectral rate: unitary/modular (reversible) vs entropic (irreversible)

The reversibility axis of the three time concepts in quantum theory, made exact through the spectral law
`‖exp(λt)‖ = exp(Re λ · t)` of `ZenoSpectralTimeUnification`:

| clock | generator | reversible? | spectral signature |
|---|---|---|---|
| unitary parameter time | `H_R` (Stone; not an observable, Pauli) | yes | `Re λ = 0` |
| modular / thermal time | `K = −ln ρ` (Connes–Rovelli, KMS) | yes (isospectral) | `Re λ = 0` |
| **entropic time** | `H_I = Σ L_j† L_j` (GKLS) | **no** (entropy-producing) | **`Re λ < 0`** |

The complex spectral rate `λ` splits **orthogonally**: `Re λ` fixes the magnitude (decay — the entropic axis) and
`Im λ` the phase (oscillation — the unitary/modular axis), by `spectral_norm`. Reversibility is exactly
`Re λ = 0`; the entropic clock is the distinct, irreversible one, on the negative-real axis conjugate to the
imaginary (modular/unitary) axis.

* **§A — the reversibility criterion.** **`flow_unitary_iff_re_zero`** (`‖exp λ‖ = 1 ↔ Re λ = 0`, reversible) and
 `flow_contracts_iff_re_neg` (`‖exp λ‖ < 1 ↔ Re λ < 0`, irreversible; `= spectral_decays_iff`).
* **§B — the reversible clocks (unitary `H_R`, modular `K = −ln ρ`).** **`reversible_generator_flow_unitary`** —
 a real generator eigenvalue `κ` gives a purely imaginary spectral rate `−iκ`, so `‖exp(−iκt)‖ = 1`: the unitary
 and modular (Hermitian `K`, real spectrum) flows preserve the norm.
* **§C — the entropic clock (`Σ L†L`) is irreversible.** **`entropic_generator_flow_contracts`** (`Re λ < 0 ⟹
 ‖exp(λt)‖ < 1` for `t > 0`: the dissipative flow strictly contracts) and **`entropic_rate_nonneg`** (the GKLS
 entropy-production rate `Σ_j Tr(L_j†L_j ρ) ≥ 0`, `= gklsEntropicRate_nonneg`) — the arrow of the entropic clock.
* **§D — the orthogonal split.** **`flow_norm_from_re`** (`‖exp(λt)‖ = exp(Re λ · t)`, `= spectral_norm`): the
 magnitude depends only on `Re λ` (entropic), the phase only on `Im λ` (unitary/modular) — the two flows are
 complementary.

§A, §B, §D are exact `Complex.norm_exp`/`Real.exp` identities (reusing `ZenoSpectralTimeUnification`); §C's contraction is exact and its rate-non-negativity is `gklsEntropicRate_nonneg`.
The *classification* into three clocks and the identification of `Re λ = 0 ⟺ reversible` with the physical
unitary/modular generators is the interpretive framing; the theorems are the exact spectral criterion on which it
rests (no claim that a specific model's `Re λ` is entropic is proved here).

## References

* Connes–Rovelli, Class. Quantum Grav. **11** (1994) 2899 (modular/thermal time); Lindblad 1976 (GKLS). Built on
 `Lindblad.ZenoSpectralTimeUnification` and `Lindblad.GKLSEntropicRate` (`gklsImaginaryHamiltonian = (ℏ/2)ΣL†L`).

No new axioms.
-/

set_option autoImplicit false

open Complex
open scoped MState Matrix
open Physlib.QuantumMechanics.Lindblad.ZenoSpectralTimeUnification

@[expose] public section

namespace Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum

/-! ## §A — the reversibility criterion -/

/-- **A flow is norm-preserving (reversible) iff the spectral rate is on the imaginary axis** `‖exp λ‖ = 1 ↔
Re λ = 0` — the unitary/modular clocks (`Re λ = 0`) preserve the norm; any `Re λ ≠ 0` breaks reversibility. -/
theorem flow_unitary_iff_re_zero (l : ℂ) : ‖Complex.exp l‖ = 1 ↔ l.re = 0 := by
  rw [Complex.norm_exp, Real.exp_eq_one_iff]

/-- **A flow strictly contracts (irreversible) iff the spectral rate has negative real part** `‖exp λ‖ < 1 ↔
Re λ < 0` — the entropic-clock signature (`= spectral_decays_iff`). -/
theorem flow_contracts_iff_re_neg (l : ℂ) : ‖Complex.exp l‖ < 1 ↔ l.re < 0 :=
  spectral_decays_iff l

/-! ## §B — the reversible clocks (unitary `H_R`, modular `K = −ln ρ`) -/

/-- **A real generator gives a reversible (unitary) flow** `‖exp(−iκt)‖ = 1` for `κ, t ∈ ℝ` — the unitary
parameter time (`H_R`) and the modular/thermal time (`K = −ln ρ`, Hermitian, real spectrum) both have real
eigenvalues, hence a purely imaginary spectral rate `−iκ` (`Re = 0`) and a norm-preserving flow. -/
theorem reversible_generator_flow_unitary (κ t : ℝ) :
    ‖Complex.exp (-Complex.I * (κ : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-! ## §C — the entropic clock (`Σ L†L`) is irreversible -/

/-- **A dissipative generator gives an irreversible (contracting) flow** `‖exp(λt)‖ < 1` for `Re λ < 0`, `t > 0` —
the entropic clock (`H_I = Σ L†L` entering the non-Hermitian effective generator) has `Re λ < 0`, so the flow
strictly loses norm: the arrow of time of the entropic clock. -/
theorem entropic_generator_flow_contracts (l : ℂ) (t : ℝ) (hl : l.re < 0) (ht : 0 < t) :
    ‖Complex.exp (l * t)‖ < 1 := by
  rw [spectral_norm, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hl ht)

/-- **The entropic clock's rate is non-negative** `Σ_j Tr(L_j† L_j ρ) ≥ 0` — the GKLS entropy-production rate
(`gklsEntropicRate_nonneg`), the second-law arrow that makes the entropic clock intrinsically irreversible,
with the entropic generator `H_I = (ℏ/2)Σ_j L_j†L_j` (`gklsImaginaryHamiltonian`). -/
theorem entropic_rate_nonneg {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
    (L : ι → Matrix d d ℂ) (ρ : MState d) :
    0 ≤ Physlib.QuantumMechanics.Lindblad.gklsEntropicRate L ρ :=
  Physlib.QuantumMechanics.Lindblad.gklsEntropicRate_nonneg L ρ

/-! ## §D — the orthogonal split -/

/-- **The flow magnitude depends only on the real (entropic) part** `‖exp(λt)‖ = exp(Re λ · t)` (`= spectral_norm`)
— `Re λ` (entropic decay) sets the magnitude, `Im λ` (unitary/modular oscillation) sets only the phase: the two
clocks are complementary, acting on orthogonal components of the spectral rate. -/
theorem flow_norm_from_re (l : ℂ) (t : ℝ) : ‖Complex.exp (l * t)‖ = Real.exp (l.re * t) :=
  spectral_norm l t

/-! ## §E — the concrete realization (modular entropy-preservation, entropic ⊥ modular) -/

open Physlib.QuantumMechanics.RelationalTime.Complementarity

/-- **The modular clock's reversibility is entropy preservation (`dS/ds = 0`)** `Sᵥₙ(U ◃ ρ) = Sᵥₙ ρ` — the
concrete form of §B (`reversible_generator_flow_unitary`, `Re λ = 0`): the modular flow `U = e^{−iKs}`
(`K = −ln ρ`, Hermitian, real spectrum) is isospectral, so von Neumann entropy is invariant. Reuses
`EntropicThermalComplementarity.Sᵥₙ_U_conj`; the meeting point of the two clocks is the static bridge
`⟨K⟩ = S_vN` (`modularHamiltonianMat_eq_entropicTimeOperator_add_offset`). -/
theorem modular_flow_entropy_preserving {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U : 𝐔[d]) : Sᵥₙ (U ◃ ρ) = Sᵥₙ ρ :=
  Physlib.QuantumMechanics.RelationalTime.Complementarity.Sᵥₙ_U_conj ρ U

/-- **The entropic direction is HS-orthogonal to the modular one (the basis-free 90°)**
`⟪adK X, D⟫ = trace((KX − XK)ᴴ D) = 0` for `D` in the commutant of `K` — the concrete form of §D
(`flow_norm_from_re`, the `Re ⊥ Im` split): the entropy-producing/dissipative direction `D` (a function of the
steady state `ρ_ss`, so `[K, D] = 0`) is orthogonal to the modular-flow direction `adK X = KX − XK`. Reuses
`EntropicThermalComplementarity.modular_direction_orthogonal_to_commutant`. -/
theorem entropic_direction_orthogonal_modular {n : Type*} [Fintype n]
    (K X D : Matrix n n ℂ) (hK : Kᴴ = K) (hKD : K * D = D * K) :
    Matrix.trace ((K * X - X * K)ᴴ * D) = 0 :=
  modular_direction_orthogonal_to_commutant K X D hK hKD

end Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum

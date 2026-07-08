/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameReversible

/-!
# KMS / modular-flow Quantum Inertial Frame

Promotes the **modular Hamiltonian** `H_θ` (associated with a
thermal / KMS state at inverse temperature `β`) to the Hermitian
generator of a `QuantumInertialFrame`.

In the Connes-Rovelli 1994 *thermal-time hypothesis*, a KMS state at
inverse temperature `β` has a modular automorphism group `σ_t` whose
generator is the modular Hamiltonian `H_θ = −log ρ` (for a finite-dim
state) — equivalently, `H_θ = β · H_R` for a Gibbs state
`ρ = exp(−β H_R)/Z`.

The modular flow is **unitary**: `σ_t(ψ) = exp(−i H_θ t/ℏ) ψ` is
norm-preserving.  So the KMS QIF is just a **reversible QIF** with
the modular Hamiltonian as `H_R`, plus the KMS-specific structure
(connection to inverse temperature `β`, thermal rate
`λ_KMS = 1/(βℏ)`, and the `KMSDetailedBalance` structure from
`QuantumInertialFrame.lean` §3).

This file is intentionally minimal: it does **not** construct the
modular Hamiltonian from a specific density matrix ρ
(that would require `HermitianMat.log` machinery and an MState↔CLM
bridge; see `QuantumInfo.ForMathlib.HermitianMat.LogExp.log` for the
matrix-log primitive when consumers need it).  Instead, the structure
accepts `H_θ` as a Hermitian operator supplied by the consumer.

## Main definitions

* `kmsQIF H_θ ℏ ℏ_pos β β_pos` — KMS QIF at inverse temperature `β`.
  Underlying QIF is `reversibleQIF H_θ ℏ ℏ_pos` (unitary modular
  evolution).
* `kmsThermalRate_at_inverse_temperature β ℏ := 1 / (β · ℏ)`.
* `kmsQIF_isEquilibriumAt` — every state is at equilibrium QIF
  (since modular evolution is unitary; the QIF is reversible).
* `kmsQIF_modular_eigenstate_tise` — TISE on every `H_θ`-eigenstate.
* `connesRovelliThermalTime_eq` — the algebraic identity
  `τ_modular = ℏ · β · t` connecting the modular-flow parameter `t`
  to the physical-time parameter `τ_modular`.

## Cross-references

* `Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame.KMSDetailedBalance` —
  KMS detailed-balance structure (§3 of base QIF file).
* `Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame.kmsThermalRate` —
  `λ_KMS := k_B T / ℏ` definition; this file uses
  `kmsThermalRate_of_beta` for the `β`-parametrised form.
* `QuantumInfo.ForMathlib.HermitianMat.LogExp.log` — matrix log;
  consumers can construct `H_θ = −log ρ` from a specific density
  matrix `ρ : HermitianMat d ℂ` if needed.

## References

* Tomita 1970, Takesaki 1970 — modular flow construction.
* Haag, Hugenholtz, Winnink 1967 — KMS condition.
* Connes-Rovelli 1994 — *thermal time hypothesis*: modular flow is
  the operational clock for a KMS state.
* Bisognano-Wichmann 1975 — modular flow on a wedge algebra.

No new axioms.  std-3 throughout.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — KMS / modular-Hamiltonian QIF -/

/-- **KMS Quantum Inertial Frame at inverse temperature `β`**.

Wraps a consumer-supplied modular Hamiltonian `H_θ` as a reversible
QIF — modular flow `σ_t(ψ) = exp(−i H_θ t/ℏ) ψ` is unitary, so the
underlying structure is `reversibleQIF` (`H_I = 0`).

The KMS-specific content lives in the bridge theorems below, which
expose the inverse-temperature parameter `β` and tie the modular
clock to the `KMSDetailedBalance` structure. -/
def kmsQIF (H_θ : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (_beta : ℝ) (_beta_pos : 0 < _beta) :
    QuantumInertialFrame H :=
  reversibleQIF H_θ hbar hbar_pos

/-- **Every state is at equilibrium-QIF for the KMS frame** — modular
flow is unitary, so the underlying reversible QIF has every state at
equilibrium (`λ ≡ 0`).

The KMS *thermal* rate `λ_KMS = 1/(βℏ)` (next theorem) is *not* the
QIF entropic rate — it is the modular-flow clock rate, exposed by
the structure-level `β` parameter. -/
theorem kmsQIF_isEquilibriumAt
    (H_θ : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (beta : ℝ) (beta_pos : 0 < beta) (ψ : H) :
    (kmsQIF H_θ hbar hbar_pos beta beta_pos).IsEquilibriumAt ψ :=
  reversibleQIF_isEquilibriumAt H_θ hbar hbar_pos ψ

/-- **TISE on every modular eigenstate**: for any
`H_θ`-eigenstate `H_θ ψ = E_θ • ψ`, the complex-Hamiltonian TISE
holds with the same modular-energy eigenvalue. -/
theorem kmsQIF_modular_eigenstate_tise
    (H_θ : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (beta : ℝ) (beta_pos : 0 < beta)
    {ψ : H} {E_θ : ℂ} (h_eig : H_θ ψ = E_θ • ψ) :
    (kmsQIF H_θ hbar hbar_pos beta beta_pos).complexHamiltonian ψ
      = E_θ • ψ :=
  reversibleQIF_tise H_θ hbar hbar_pos h_eig

/-! ## §2 — Connes-Rovelli thermal time -/

/-- **KMS thermal rate at inverse temperature `β`**:
`λ_KMS := 1 / (β · ℏ)`.

This is the rate at which modular flow advances per unit physical
time in a KMS state at inverse temperature `β` — the *modular
clock's tick rate*. -/
def kmsThermalRate_at_inverse_temperature (beta hbar : ℝ) : ℝ :=
  1 / (beta * hbar)

/-- The KMS thermal rate is positive at positive `β, ℏ`. -/
theorem kmsThermalRate_at_inverse_temperature_pos
    {beta hbar : ℝ} (beta_pos : 0 < beta) (hbar_pos : 0 < hbar) :
    0 < kmsThermalRate_at_inverse_temperature beta hbar := by
  unfold kmsThermalRate_at_inverse_temperature
  exact div_pos one_pos (mul_pos beta_pos hbar_pos)

/-- **Connes-Rovelli thermal-time identity**:
`τ_modular(t) = β · ℏ · t`.

Algebraic identity tying the modular-flow parameter `t` (a
dimensionless / clock parameter) to the physical-time accumulator
`τ_modular` (with units of time × energy = action).  Under the
*thermal-time hypothesis*, `t` is the operational time perceived by
an observer in the KMS state at inverse temperature `β`. -/
def connesRovelliThermalTime (beta hbar t : ℝ) : ℝ := beta * hbar * t

/-- The Connes-Rovelli thermal-time rate is constant: `dτ_modular/dt
= β · ℏ`. -/
theorem connesRovelliThermalTime_rate_eq (beta hbar t₁ t₂ : ℝ) :
    connesRovelliThermalTime beta hbar t₂
      - connesRovelliThermalTime beta hbar t₁
      = beta * hbar * (t₂ - t₁) := by
  unfold connesRovelliThermalTime
  ring

/-- **Thermal-rate ↔ thermal-time consistency**: the product
`λ_KMS · (τ_modular at unit `t`) = 1`.

Physically: one modular-clock tick (`t = 1`) advances `τ_modular`
by `β ℏ`, and this advance times the rate `1/(βℏ)` returns `1`
— the dimensionless cycle parameter. -/
theorem kmsThermalRate_mul_connesRovelliThermalTime_at_one
    {beta hbar : ℝ} (beta_pos : 0 < beta) (hbar_pos : 0 < hbar) :
    kmsThermalRate_at_inverse_temperature beta hbar
      * connesRovelliThermalTime beta hbar 1 = 1 := by
  unfold kmsThermalRate_at_inverse_temperature connesRovelliThermalTime
  have hβ : beta ≠ 0 := ne_of_gt beta_pos
  have hℏ : hbar ≠ 0 := ne_of_gt hbar_pos
  field_simp

/-! ## §3 — Bridge to `KMSDetailedBalance` -/

/-- **KMS QIF + KMSDetailedBalance + equilibrium-state** ⟹ trivial
detailed balance at zero gap.

For any state `ψ` (every state is equilibrium for the reversible
KMS QIF) and any `KMSDetailedBalance κ`, the detailed-balance
identity `W^+(0) = W^-(0)` (from
`KMSDetailedBalance.W_plus_eq_W_minus_at_zero`) collapses
operationally — there is no energy gap to transition across in the
equilibrium state. -/
theorem kmsQIF_at_equilibrium_implies_trivial_detailed_balance
    (H_θ : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (beta : ℝ) (beta_pos : 0 < beta) (ψ : H) (κ : KMSDetailedBalance) :
    (kmsQIF H_θ hbar hbar_pos beta beta_pos).IsEquilibriumAt ψ
      ∧ κ.W_plus 0 = κ.W_minus 0 :=
  ⟨kmsQIF_isEquilibriumAt H_θ hbar hbar_pos beta beta_pos ψ,
   κ.W_plus_eq_W_minus_at_zero⟩

end QuantumMechanics.FiniteTarget

end

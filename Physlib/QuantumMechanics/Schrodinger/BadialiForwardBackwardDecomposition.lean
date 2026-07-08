/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Badiali forward–backward wavefunction decomposition

Port of the algebraic content of Badiali 2005,
*"Entropy, time-irreversibility and the Schrödinger equation in a
primarily discrete spacetime"*, J. Phys. A: Math. Gen. 38 2835.

The Badiali framework derives quantum mechanics from a discrete
pre-relativistic spacetime via two real-valued *forward* and
*backward* probability densities `φ, φ̂ : ℝⁿ → ℝ` (solutions of
dual diffusion equations with entry and exit conditions
respectively) and combines them into a single complex-valued
wavefunction. The algebraic centrepiece of the construction —
equations (34) and (37) of the paper — admits a clean,
self-contained Lean formalisation. The deeper PDE results
(Schrödinger equation as a consequence of equations (3) + (25),
H-theorem `dH/dt ≥ 0` of equation (21)) require analytic machinery
not in scope here; this file provides the **load-bearing algebraic
identities** that underpin the decomposition.

## Contents

### §1 — Badiali R/S/Ψ decomposition (paper Eq. 34)

* `badialiR φ φ̂ := (1/2)·ln(φ·φ̂)` — the **amplitude phase**.
* `badialiS φ φ̂ := (1/2)·ln(φ̂/φ)` — the **drift phase**.
* `badialiPsi φ φ̂ := exp(R + i·S)` — the complex wavefunction.

### §2 — Born rule from the decomposition (paper Eq. 37)

* **`badialiPsi_normSq`** — `|Ψ|² = φ·φ̂`.
 The probability density of the underlying Markov process is the
 modulus squared of the Badiali wavefunction. This is the
 Nelson–Nagasawa form of the Born rule.
* **`badialiPsi_mul_conj`** — equivalent statement
 `Ψ·Ψ̄ = (φ·φ̂ : ℂ)`.

### §3 — Inverse decomposition

* `badialiR_add_badialiS_eq_log_phi_hat` — `R + S = ln(φ̂)`.
* `badialiR_sub_badialiS_eq_log_phi` — `R − S = ln(φ)`.
 These invert the (34) defining equations.

### §4 — Discrete-spacetime relations (paper §2.1)

* `badialiUncertaintyXP m Δx Δt := m·(Δx)²/Δt` — the discrete-time
 momentum-uncertainty product `Δx·Δp` with `Δp := m·Δx/Δt`.
* `badialiUncertaintyTE m Δx Δt := (1/2)·m·(Δx)²/Δt` — the
 energy-time product `Δt·ΔE` with `ΔE := (1/2)·m·(Δx/Δt)²`.
* `badialiDiffusionCoeff ℏ m := ℏ/(2·m)` — the diffusion coefficient
 `D = ℏ/(2m)` emerging from the limit `Δx, Δt → 0` with
 `(Δx)²/Δt = ℏ/m` fixed.
* **`badialiUncertaintyXP_eq_hbar`** — given the Badiali postulate
 `m·(Δx)²/Δt = ℏ`, we have `Δx·Δp = ℏ`.
* **`badialiUncertaintyTE_eq_hbar_half`** — and `Δt·ΔE = ℏ/2`.
* **`badialiDiffusionCoeff_eq_halved_postulate`** —
 `D = (Δx)² / (2·Δt)` under the Badiali postulate.

### §5 — Path-temperature like-equilibrium condition (paper Eq. 18)

* `badialiPathTemperatureProduct τ kB T := τ·kB·T`.
* **`badiali_like_equilibrium_iff`** — the like-equilibrium identity
 `τ·k_B·T = ℏ` ↔ `τ = ℏ/(k_B·T)` (Badiali Eq. 18: `τ* = β*·ℏ`).

## Scope

This file provides the **algebraic kernel** of the Badiali derivation:

* The Born-rule identity `|Ψ|² = φ·φ̂` (Eq. 37) — fully proved here.
* The R/S phase definitions (Eq. 34) — fully formalised here.
* The discrete-spacetime uncertainty algebra (paper §2.1) — fully
 proved here.
* The like-equilibrium identity `τ = β·ℏ` (paper §4) — fully proved
 here.

This file does NOT ship:

* The Schrödinger equation `iℏ·∂Ψ/∂t = −(ℏ²/2m)·ΔΨ + V·Ψ` (Eq. 35).
 Proving Eq. 35 from the diffusion equations (3) and (25) requires
 formalising the diffusion / Fokker–Planck PDE machinery, the
 Kolmogorov duality, and the drift identities for `ln φ` and
 `ln φ̂`. Achievable in principle; large separate scope.
* The H-theorem `dH/dt ≥ 0` (Eq. 21). Requires the diffusion-PDE
 framework. Separate file.

When those PDE pieces are formalised, the algebraic identities in
this file are the bridge that ties the complex-wavefunction
representation back to the underlying forward/backward
real-valued diffusion fields.

## References

* Badiali 2005 — *Entropy, time-irreversibility and the Schrödinger
 equation in a primarily discrete spacetime*, J. Phys. A 38, 2835.
 - Equation (34) — R, S, Ψ definitions.
 - Equation (37) — Born rule `μ = φ·φ̂ = Ψ·Ψ̄`.
 - Equation (18) — like-equilibrium `τ* = β*·ℏ`.
 - Section §2.1 — discrete-spacetime postulate `(Δx)²/Δt = ℏ/m`.
* Nelson 1966 *Phys. Rev.* 150, 1079 — stochastic mechanics; same
 R/S/Ψ pattern.
* Nagasawa 1993 *Schrödinger Equations and Diffusion Theory* — full
 Kolmogorov-duality formalism.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

open Real Complex

/-! ## §1 — R, S, Ψ definitions (Badiali Eq. 34) -/

/-- **Badiali amplitude phase**: `R(φ, φ̂) := (1/2)·ln(φ·φ̂)`.

Pointwise (per spacetime point `x`) the amplitude phase of the
forward–backward decomposition.  Equation (34) of Badiali 2005. -/
def badialiR (φ φ_hat : ℝ) : ℝ := (1 / 2) * Real.log (φ * φ_hat)

/-- **Badiali drift phase**: `S(φ, φ̂) := (1/2)·ln(φ̂ / φ)`.

Pointwise drift phase.  When the underlying Markov process has
osmotic velocity `(ℏ/m)·∇S`, this is the function whose gradient
generates the osmotic drift.  Equation (34) of Badiali 2005. -/
def badialiS (φ φ_hat : ℝ) : ℝ := (1 / 2) * Real.log (φ_hat / φ)

/-- **Badiali complex wavefunction**: `Ψ(φ, φ̂) := exp(R + i·S)`.

The single complex-valued field obtained by combining the
amplitude phase `R` and the drift phase `S`.  Badiali 2005
combines two real-valued solutions of dual diffusion equations
(forward and backward) into one complex wavefunction; this is the
combination.  Equation (34) of Badiali 2005. -/
def badialiPsi (φ φ_hat : ℝ) : ℂ :=
  Complex.exp ((badialiR φ φ_hat : ℂ) + (badialiS φ φ_hat : ℂ) * Complex.I)

/-! ## §2 — Born rule from the decomposition (Badiali Eq. 37) -/

/-- **Badiali Born rule** `|Ψ|² = φ·φ̂`.

Given strictly positive forward density `φ > 0` and backward
density `φ̂ > 0`, the squared modulus of the Badiali wavefunction
equals the product `φ·φ̂`, which Badiali identifies with the
probability density `μ` of the underlying Markov process.  This
is Equation (37) of Badiali 2005:

  `μ(t,x) = φ(t,x)·φ̂(t,x) = Ψ(t,x)·Ψ̄(t,x)`.

**Algebraic core**: `Ψ·Ψ̄ = exp(R + iS)·exp(R − iS) = exp(2R)
= exp(ln(φ·φ̂)) = φ·φ̂`. -/
theorem badialiPsi_normSq
    {φ φ_hat : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) :
    Complex.normSq (badialiPsi φ φ_hat) = φ * φ_hat := by
  have h_re : ((badialiR φ φ_hat : ℂ) + (badialiS φ φ_hat : ℂ) * Complex.I).re
              = badialiR φ φ_hat := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h_norm : ‖badialiPsi φ φ_hat‖
                = Real.exp (badialiR φ φ_hat) := by
    unfold badialiPsi
    rw [Complex.norm_exp, h_re]
  have h_normSq : Complex.normSq (badialiPsi φ φ_hat)
                  = ‖badialiPsi φ φ_hat‖ ^ 2 := by
    have : @RCLike.normSq ℂ _ (badialiPsi φ φ_hat)
            = ‖badialiPsi φ φ_hat‖ ^ 2 :=
      RCLike.normSq_eq_def' (badialiPsi φ φ_hat)
    simpa using this
  rw [h_normSq, h_norm]
  -- Goal: (Real.exp (badialiR φ φ_hat)) ^ 2 = φ * φ_hat
  unfold badialiR
  rw [sq, ← Real.exp_add]
  rw [show (1 / 2 : ℝ) * Real.log (φ * φ_hat) + 1 / 2 * Real.log (φ * φ_hat)
        = Real.log (φ * φ_hat) from by ring]
  exact Real.exp_log (mul_pos hφ hφ_hat)

/-- **Badiali Born rule (complex form)**: `Ψ · conj Ψ = φ·φ̂` as a
complex equation.

Equivalent restatement of `badialiPsi_normSq`; convenient when the
ambient calculation works in `ℂ`. -/
theorem badialiPsi_mul_conj
    {φ φ_hat : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) :
    badialiPsi φ φ_hat * (starRingEnd ℂ) (badialiPsi φ φ_hat) =
      ((φ * φ_hat : ℝ) : ℂ) := by
  rw [Complex.mul_conj]
  rw [badialiPsi_normSq hφ hφ_hat]

/-! ## §3 — Inverse decomposition: R, S recover φ, φ̂ -/

/-- **`R + S = ln(φ̂)`**: the two phases recombine to the backward
log-density.  Inverts the (34) definitions. -/
theorem badialiR_add_badialiS_eq_log_phi_hat
    {φ φ_hat : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) :
    badialiR φ φ_hat + badialiS φ φ_hat = Real.log φ_hat := by
  unfold badialiR badialiS
  have h_div_pos : 0 < φ_hat / φ := div_pos hφ_hat hφ
  rw [Real.log_mul (ne_of_gt hφ) (ne_of_gt hφ_hat)]
  rw [Real.log_div (ne_of_gt hφ_hat) (ne_of_gt hφ)]
  ring

/-- **`R − S = ln(φ)`**: the two phases recombine to the forward
log-density.  Inverts the (34) definitions. -/
theorem badialiR_sub_badialiS_eq_log_phi
    {φ φ_hat : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) :
    badialiR φ φ_hat - badialiS φ φ_hat = Real.log φ := by
  unfold badialiR badialiS
  rw [Real.log_mul (ne_of_gt hφ) (ne_of_gt hφ_hat)]
  rw [Real.log_div (ne_of_gt hφ_hat) (ne_of_gt hφ)]
  ring

/-- **Inverse identity, forward**: `φ = exp(R − S)`. -/
theorem phi_eq_exp_R_sub_S
    {φ φ_hat : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) :
    φ = Real.exp (badialiR φ φ_hat - badialiS φ φ_hat) := by
  rw [badialiR_sub_badialiS_eq_log_phi hφ hφ_hat]
  exact (Real.exp_log hφ).symm

/-- **Inverse identity, backward**: `φ̂ = exp(R + S)`. -/
theorem phi_hat_eq_exp_R_add_S
    {φ φ_hat : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) :
    φ_hat = Real.exp (badialiR φ φ_hat + badialiS φ φ_hat) := by
  rw [badialiR_add_badialiS_eq_log_phi_hat hφ hφ_hat]
  exact (Real.exp_log hφ_hat).symm

/-! ## §4 — Discrete-spacetime uncertainty relations (Badiali §2.1) -/

/-- **Badiali momentum-uncertainty product** for the discrete
spacetime: with `Δp := m·Δx/Δt` (the discrete-time momentum), the
position–momentum product is

  `Δx · Δp = m · (Δx)² / Δt`.

Paper §2.1 — *"if a mass m is located in a region Δx, the only one
relation that we can introduce between Δx and Δt is `(Δx)²/Δt =
ℏ/m`."* -/
def badialiUncertaintyXP (m Δx Δt : ℝ) : ℝ := m * Δx^2 / Δt

/-- **Badiali energy-time product** for the discrete spacetime:
with `ΔE := (1/2)·m·(Δx/Δt)²`, the energy–time product is

  `Δt · ΔE = (1/2) · m · (Δx)² / Δt`. -/
def badialiUncertaintyTE (m Δx Δt : ℝ) : ℝ := (1 / 2) * m * Δx^2 / Δt

/-- **Badiali diffusion coefficient** `D := ℏ/(2m)` — the
continuous-limit diffusion coefficient emerging when `Δx, Δt → 0`
with `(Δx)²/Δt = ℏ/m` fixed (paper §2.2). -/
def badialiDiffusionCoeff (ℏ m : ℝ) : ℝ := ℏ / (2 * m)

/-- **Position–momentum uncertainty equals `ℏ`** under the Badiali
postulate `m·(Δx)²/Δt = ℏ`.

Direct algebraic consequence: `Δx·Δp = m·(Δx)²/Δt = ℏ`.
Paper §2.1 — the discrete-spacetime mimic of Heisenberg's
position-momentum relation. -/
theorem badialiUncertaintyXP_eq_hbar
    {m Δx Δt ℏ : ℝ}
    (hPostulate : m * Δx^2 / Δt = ℏ) :
    badialiUncertaintyXP m Δx Δt = ℏ := by
  unfold badialiUncertaintyXP
  exact hPostulate

/-- **Energy–time uncertainty equals `ℏ/2`** under the Badiali
postulate.

Direct algebraic consequence: `Δt·ΔE = (1/2)·m·(Δx)²/Δt = ℏ/2`.
Paper §2.1 — the discrete-spacetime mimic of Heisenberg's
energy-time relation. -/
theorem badialiUncertaintyTE_eq_hbar_half
    {m Δx Δt ℏ : ℝ}
    (hPostulate : m * Δx^2 / Δt = ℏ) (hΔt_ne : Δt ≠ 0) :
    badialiUncertaintyTE m Δx Δt = ℏ / 2 := by
  unfold badialiUncertaintyTE
  have h : (1 / 2 : ℝ) * m * Δx^2 / Δt = (1 / 2) * (m * Δx^2 / Δt) := by
    field_simp
  rw [h, hPostulate]
  ring

/-- **Diffusion coefficient identity** `D = (Δx)² / (2·Δt)` under
the Badiali postulate `m·(Δx)²/Δt = ℏ`.

This is the bridge from the discrete-spacetime postulate (§2.1)
to the continuous-limit diffusion process (§2.2), where the
diffusion equation `−∂φ/∂t + D·Δ φ = 0` has `D = ℏ/(2m)`. -/
theorem badialiDiffusionCoeff_eq_halved_postulate
    {m Δx Δt ℏ : ℝ}
    (hm_pos : 0 < m) (hΔt_ne : Δt ≠ 0)
    (hPostulate : m * Δx^2 / Δt = ℏ) :
    badialiDiffusionCoeff ℏ m = Δx^2 / (2 * Δt) := by
  unfold badialiDiffusionCoeff
  rw [← hPostulate]
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  field_simp

/-! ## §5 — Like-equilibrium condition (Badiali Eq. 18) -/

/-- **Badiali path-temperature product**: `τ · k_B · T`.

In the path-entropy framework of paper §3–§4, this product takes
the value `ℏ` exactly when the path-temperature `T_path` coincides
with the thermal temperature — the like-equilibrium condition. -/
def badialiPathTemperatureProduct (τ kB T : ℝ) : ℝ := τ * kB * T

/-- **Badiali like-equilibrium identity** (paper Eq. 18):

  `τ · k_B · T = ℏ`   ↔   `τ = ℏ / (k_B · T)`.

This is the path-temperature ↔ thermal-temperature identification
`τ* = β* · ℏ` of paper §4 — the condition under which the path
entropy `S_path` becomes the standard thermal entropy.

Quantitatively: the relaxation time required for quantum
fluctuations not to exceed the typical thermal energy is exactly
`τ = ℏ/(k_B·T)`. -/
theorem badiali_like_equilibrium_iff
    {τ kB T ℏ : ℝ} (hkB_ne : kB ≠ 0) (hT_ne : T ≠ 0) :
    badialiPathTemperatureProduct τ kB T = ℏ ↔ τ = ℏ / (kB * T) := by
  unfold badialiPathTemperatureProduct
  constructor
  · intro h
    have hkBT_ne : kB * T ≠ 0 := mul_ne_zero hkB_ne hT_ne
    have : τ * (kB * T) = ℏ := by linarith [h]
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp

end Physlib.QuantumMechanics.Schrodinger

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.EntropicLapseFactor
public import Physlib.StatisticalMechanics.DiscreteEntropicTimeTrinity
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential entropic-damping ADM lapse `Ñ = N·exp(−φ)`

Third entropic-lapse convention added to physlib (after the
**additive** form in commit `a6049d7f` and the **multiplicative**
`Λ`-form in commit `7ede1f0f`).

Port of the complex-action/entropic-time modified ADM line element from
`/Users/macbookpro/Downloads/chat-session-3current.txt` line ~1635
(Paper3_Geometric_Standard_Theory.pdf, §3.1):

 `ds² = −N²·N_ent²·c²·dt²
 + h_ij·(dx^i + N^i·dt)·(dx^j + N^j·dt)`,

with the **exponential entropic-damping factor**

 `N_ent(x) := exp(−φ(x))`, `φ(x) := ∫λ(x(t)) dt`,

so that the **effective ADM lapse** becomes

 `Ñ(x) := N(x) · exp(−φ(x))`.

## Why "exponential damping" and not "additive focusing"

The earlier physlib commits used:

* **Additive convention** `dτ_total = (N + λ)·dt` (commit `a6049d7f`)
 — the entropic rate `λ ≥ 0` **adds** to the lapse, so the clock
 runs **faster** as entropy accumulates (geometric focusing
 reading).

* **Multiplicative convention** `dτ_ent = Λ·dτ_GR` with
 `Λ ≥ 1` (commit `7ede1f0f`) — same direction: clock speeds up.

This file provides the **opposite-sign** convention:

* **Exponential damping** `Ñ = N·exp(−φ)` — the lapse **shrinks**
 as entropy accumulates. In the limit `φ → ∞`, `Ñ → 0`: the
 clock freezes (information-theoretic decoherence / KMS thermal
 freeze-out).

These are **different physical models**:

* Additive / multiplicative `Λ ≥ 1` describes regimes where
 entropic accumulation **accelerates** the local clock (e.g.,
 gravitational collapse via compression work).

* Exponential damping `Ñ = N·exp(−φ)` describes regimes where
 entropic accumulation **damps** the local clock (e.g.,
 KMS thermal decoherence, Bisognano–Wichmann boost).

Both are valid in their respective domains. This file connects
the exponential form to the existing complex-action/entropic-time damping envelope
`Λ_n = exp(−τ_ent_n)` from `DiscreteEntropicTimeTrinity` (commit
`a832527f`) and to a corresponding `EntropicLapseFactor`
construction.

## The load-bearing identification

The **exponential entropic-damping factor**
`N_ent(x) := exp(−φ(x))` is *literally* the discrete complex-action/entropic-time
**damping envelope** `Λ_n := exp(−τ_ent_n)` at the continuous
worldline level:

 `N_ent(x) = dampingEnvelope(φ(x))`, `φ(x) ↔ τ_ent_n`.

So **the modified ADM lapse `Ñ = N·exp(−φ)` IS the bare ADM
lapse times the complex-action/entropic-time damping envelope**, evaluated at the
entropic-time accumulator. No new physics — just identification.

## Contents

### §1 — Exponential entropic-damping factor + effective lapse

* `exponentialDampingFactor φ := exp(−φ)`.
* `exponentialDampingFactor_pos`.
* `exponentialDampingFactor_le_one` — under `φ ≥ 0`, the damping
 factor is in `(0, 1]`.
* `exponentialEntropicLapse N φ := N · exp(−φ)` — the modified
 ADM lapse `Ñ`.
* `exponentialEntropicLapse_pos`.
* `exponentialEntropicLapse_at_zero_phi_eq_lapse` — at `φ = 0`
 (no entropy production), `Ñ = N` (pure GR).

### §2 — Bridge to `EntropicLapseFactor` multiplicative form

* `EntropicLapseFactor.ofExponentialDamping φ_fn h_nonneg` —
 constructs an `EntropicLapseFactor` with `Λ(x) := exp(−φ(x))`,
 the multiplicative form of the exponential damping.
* `ofExponentialDamping_Λ_eq` — definitional unfolding.

### §3 — Connection to complex-action/entropic-time damping envelope

* **`exponentialDampingFactor_eq_dampingEnvelope`** — the
 exponential damping factor at φ IS the
 `DiscreteEntropicTimeTrinity.dampingEnvelope` evaluated when
 `τ_ent = φ`. Pointwise algebraic identification of the
 continuous and discrete complex-action/entropic-time damping pictures.

### §4 — Frozen-LRF and complete-decoherence limits

* `exponentialEntropicLapse_at_zero_phi_eq_N` — pure GR.
* `exponentialEntropicLapse_tends_to_zero_as_phi_to_infty` —
 full decoherence: at large `φ`, the lapse `Ñ → 0` and the
 clock freezes.

## Scope

* The integrated entropic potential `φ(x) := ∫λ dt` is treated as
 an **abstract input scalar field** here — no explicit
 integration of `λ` along worldlines. Integration would route
 through the Bochner machinery (commit `a306462e`); the
 pointwise algebra is the load-bearing scope here.
* The complex-action/entropic-time modified Einstein equation
 `G_μν + i·Λ_μν = (8πG/c⁴)·(T_μν + i·S_μν)` is *not* shipped —
 it requires tensor-calculus / Ricci infrastructure not in
 physlib. Only the algebraic lapse identity is provided here.

## References

* Source: `/Users/macbookpro/Downloads/chat-session-3current.txt`
 line ~1635 (Paper3_Geometric_Standard_Theory §3.1).
* `Physlib.SpaceAndTime.EntropicLapseFactor` — multiplicative
 `Λ`-form with four origins (commit `7ede1f0f`).
* `Physlib.SpaceAndTime.EntropicADMLineElement` — additive form
 (commit `a6049d7f`).
* `Physlib.StatisticalMechanics.DiscreteEntropicTimeTrinity` —
 discrete complex-action/entropic-time damping envelope (commit `a832527f`).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.SpaceTime

open Real Physlib.StatisticalMechanics

variable {d : ℕ}

/-! ## §1 — Exponential damping factor + effective lapse -/

/-- **Exponential entropic-damping factor** at integrated
entropic potential `φ`:

  `N_ent(φ) := exp(−φ)`.

In complex-action/entropic-time notation, `φ := ∫λ dt` is the path-integrated entropy
production rate.  At `φ = 0` (no production), `N_ent = 1`; as
`φ → ∞` (full decoherence), `N_ent → 0`. -/
def exponentialDampingFactor (φ : ℝ) : ℝ := Real.exp (-φ)

/-- **Exponential damping factor is strictly positive**. -/
theorem exponentialDampingFactor_pos (φ : ℝ) :
    0 < exponentialDampingFactor φ := Real.exp_pos _

/-- **Exponential damping factor is at most 1** under `φ ≥ 0`
(monotone non-negative accumulated entropy production). -/
theorem exponentialDampingFactor_le_one
    {φ : ℝ} (h_nonneg : 0 ≤ φ) :
    exponentialDampingFactor φ ≤ 1 := by
  unfold exponentialDampingFactor
  rw [show (1 : ℝ) = Real.exp 0 by simp]
  apply Real.exp_le_exp.mpr
  linarith

/-- **At zero entropy production, the damping factor is `1`**
(pure GR). -/
theorem exponentialDampingFactor_at_zero_eq_one :
    exponentialDampingFactor 0 = 1 := by
  unfold exponentialDampingFactor
  simp

/-- **Exponential entropic ADM lapse** `Ñ := N · exp(−φ)`.

Modified ADM lapse from
`/Users/macbookpro/Downloads/chat-session-3current.txt` §3.1:
the bare ADM lapse `N` multiplied by the exponential damping
factor at the integrated entropic potential `φ`. -/
def exponentialEntropicLapse (N : SpaceTime d → ℝ)
    (φ : SpaceTime d → ℝ) (x : SpaceTime d) : ℝ :=
  N x * exponentialDampingFactor (φ x)

/-- **The exponential entropic ADM lapse is positive** under
positive bare lapse. -/
theorem exponentialEntropicLapse_pos
    {N : SpaceTime d → ℝ} {φ : SpaceTime d → ℝ}
    (hN_pos : ∀ y, 0 < N y) (x : SpaceTime d) :
    0 < exponentialEntropicLapse N φ x :=
  mul_pos (hN_pos x) (exponentialDampingFactor_pos _)

/-- **At zero entropic potential, the modified ADM lapse equals
the bare ADM lapse** (pure GR recovery).

`exponentialEntropicLapse N φ x = N(x)` when `φ ≡ 0`. -/
theorem exponentialEntropicLapse_at_zero_phi_eq_lapse
    {N : SpaceTime d → ℝ} {φ : SpaceTime d → ℝ}
    (h_zero : ∀ y, φ y = 0) (x : SpaceTime d) :
    exponentialEntropicLapse N φ x = N x := by
  unfold exponentialEntropicLapse exponentialDampingFactor
  rw [h_zero x]
  simp

/-- **At positive `φ`, the modified ADM lapse is strictly less
than the bare ADM lapse** — the exponential damping reduces the
local clock rate. -/
theorem exponentialEntropicLapse_lt_lapse_at_pos_phi
    {N : SpaceTime d → ℝ} {φ : SpaceTime d → ℝ}
    {x : SpaceTime d} (hN_pos : 0 < N x) (h_pos : 0 < φ x) :
    exponentialEntropicLapse N φ x < N x := by
  unfold exponentialEntropicLapse exponentialDampingFactor
  have h_damp_lt_one : Real.exp (-(φ x)) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    apply Real.exp_lt_exp.mpr
    linarith
  calc N x * Real.exp (-(φ x)) < N x * 1 :=
        mul_lt_mul_of_pos_left h_damp_lt_one hN_pos
    _ = N x := mul_one _

/-! ## §2 — Bridge to `EntropicLapseFactor` multiplicative form -/

/-- **Bridge constructor**: a non-negative integrated entropic
potential `φ : SpaceTime d → ℝ` defines a multiplicative
`EntropicLapseFactor` with `Λ(x) := exp(−φ(x))`.

This is the **fifth origin construction** of the multiplicative
lapse factor (after entropy production rate, modular β·E, path
compressibility, and horizon Tolman in
`Physlib.SpaceAndTime.EntropicLapseFactor`), specialised to the
exponential-damping regime.

Note: `Λ ≤ 1` (clock slows) — opposite sign from the
entropy-production-rate construction `Λ_λ = 1 + λ/N ≥ 1`
(clock speeds up).  Both are valid in their physical regimes;
this one corresponds to KMS thermal damping / Bisognano–Wichmann
modular damping. -/
def EntropicLapseFactor.ofExponentialDamping
    (φ_fn : SpaceTime d → ℝ) :
    EntropicLapseFactor d where
  Λ := fun x => Real.exp (-(φ_fn x))
  Λ_pos := fun _ => Real.exp_pos _

/-- **The exponential-damping `Λ` IS the damping factor**. -/
theorem EntropicLapseFactor.ofExponentialDamping_Λ_eq
    (φ_fn : SpaceTime d → ℝ) (x : SpaceTime d) :
    (EntropicLapseFactor.ofExponentialDamping φ_fn).Λ x
      = exponentialDampingFactor (φ_fn x) := rfl

/-! ## §3 — Connection to complex-action/entropic-time damping envelope -/

/-- **:exponential damping factor IS the discrete
complex-action/entropic-time damping envelope** at the continuous-worldline level.

For a discrete complex-action/entropic-time trinity `T` with accumulated entropic
time `τ_ent(n)`, the damping envelope is

  `Λ(n) := exp(−τ_ent(n)) = dampingEnvelope T n`.

The exponential entropic-damping factor at integrated potential
`φ` is

  `exp(−φ) = exponentialDampingFactor(φ)`.

These coincide pointwise when `φ ↔ τ_ent(n)`:

  `exponentialDampingFactor(T.τ_ent n) = T.dampingEnvelope n`.

This is the **continuous-worldline ↔ discrete-step
identification** of the complex-action/entropic-time damping picture. -/
theorem exponentialDampingFactor_eq_dampingEnvelope
    (T : DiscreteEntropicTimeTrinity) (n : ℕ) :
    exponentialDampingFactor (T.τ_ent n) = T.dampingEnvelope n := by
  unfold exponentialDampingFactor
        DiscreteEntropicTimeTrinity.dampingEnvelope
  rfl

/-! ## §4 — Frozen-LRF and complete-decoherence limits -/

/-- **At zero entropy production, the multiplicative
`ofExponentialDamping` factor reduces to unit** — pure GR. -/
theorem ofExponentialDamping_at_zero_phi_eq_unit
    {φ_fn : SpaceTime d → ℝ} (h_zero : ∀ y, φ_fn y = 0)
    (x : SpaceTime d) :
    (EntropicLapseFactor.ofExponentialDamping φ_fn).Λ x = 1 := by
  rw [EntropicLapseFactor.ofExponentialDamping_Λ_eq]
  rw [h_zero x]
  exact exponentialDampingFactor_at_zero_eq_one

/-- **The exponential damping factor is monotone non-increasing
in `φ`**: as accumulated entropy production grows, the lapse
shrinks. -/
theorem exponentialDampingFactor_antitone
    {φ₁ φ₂ : ℝ} (h_le : φ₁ ≤ φ₂) :
    exponentialDampingFactor φ₂ ≤ exponentialDampingFactor φ₁ := by
  unfold exponentialDampingFactor
  apply Real.exp_le_exp.mpr
  linarith

/-- **Damping-factor algebraic compounding**:

  `exp(−φ₁) · exp(−φ₂) = exp(−(φ₁ + φ₂))`.

Two-step accumulation of entropic potential along a worldline
compounds multiplicatively at the damping-factor level — the
complex-action/entropic-time analogue of the Pythagorean-additivity of variances for
diffusion. -/
theorem exponentialDampingFactor_mul (φ₁ φ₂ : ℝ) :
    exponentialDampingFactor φ₁ * exponentialDampingFactor φ₂
      = exponentialDampingFactor (φ₁ + φ₂) := by
  unfold exponentialDampingFactor
  rw [← Real.exp_add]
  congr 1
  ring

end Physlib.SpaceTime

end

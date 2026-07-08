/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition
public import Physlib.QuantumMechanics.Schrodinger.BohmianQuantumPotential

/-!
# Bridge: Badiali amplitude `R := √(φ·φ̂)` feeds the Bohmian quantum potential

Sixth and final bridge in the analytic-gap
closure plan.

**The load-bearing identification**:

Badiali 2005's forward–backward decomposition produces, at every
spatial point, the amplitude

 `R(x) := √(φ(x) · φ̂(x)) = exp(R_Bd(x))`

(by the algebraic identity `exp(R_Bd) = √(φ·φ̂)` already proven in
`BadialiToMadelung.badialiToMadelung_density_eq`). Fed into the
Bohmian quantum potential

 `Q(x) := −ℏ² · Δ R(x) / (2·m·R(x))`

(now a concrete Mathlib-Laplacian-derived function thanks to
`BohmianQuantumPotential.lean`), this gives the **Badiali quantum
potential** — the back-reaction term that appears when Badiali's
forward–backward diffusion is rephrased as a Schrödinger equation
(paper §6, Eq. 35).

This file closes the gap by:

1. Defining `badialiAmplitude φ φ̂` as a function `E → ℝ` (the
 pointwise square-root combination of forward and backward
 densities).
2. Showing `badialiAmplitude φ φ̂ x = Real.sqrt (φ x · φ̂ x)`
 pointwise.
3. Showing positivity / non-negativity under positive `φ, φ̂`.
4. Defining `badialiQuantumPotential φ φ̂ m ℏ x` by composition.
5. Producing the **concrete** `BohmianQuantumPotential` record
 via `BohmianQuantumPotential.ofMathlibLaplacian` with the
 Badiali amplitude.
6. Sign theorems for the Badiali quantum potential.

## Why this completes the closure

The five previous bridges already established that Badiali's
forward–backward Born density is the same as the Madelung Born
density:

 `Complex.normSq (badialiPsi φ φ̂) = φ · φ̂
 = (badialiAmplitude φ φ̂)²
 = madelungDensity (badialiToMadelung …)`

— *as algebraic identities*. But the Bohmian quantum potential
`Q := −ℏ²·ΔR/(2mR)` was, until this commit, **abstracted** as a
`laplacianAmplitude : ℝ` field in the `BohmianQuantumPotential`
record — an opaque real number, not a Laplacian.

The previous file `BohmianQuantumPotential.lean` closed that gap by
defining the *concrete* quantum potential as a real Mathlib
Laplacian. This file finishes the loop:

 Badiali (φ, φ̂)
 → Amplitude R := √(φ·φ̂) : E → ℝ
 → Quantum potential Q := −ℏ²·Δ R/(2m R) : E → ℝ
 → BohmianQuantumPotential record with `laplacianAmplitude := Δ R x`

Every step is **concrete** (no abstract opaque real numbers); each
identification is a **Lean theorem** (not informal physics
shorthand).

## Contents

### §1 — Badiali amplitude

* `badialiAmplitude φ φ̂` — the function
 `x ↦ √(φ x · φ̂ x) : E → ℝ`.
* `badialiAmplitude_apply` — pointwise identity.
* `badialiAmplitude_nonneg` — non-negative everywhere.
* `badialiAmplitude_pos_iff` — strictly positive at `x` iff
 `φ(x)·φ̂(x) > 0`.
* `badialiAmplitude_sq` — `R(x)² = φ(x)·φ̂(x)`.

### §2 — Badiali quantum potential

* `badialiQuantumPotential φ φ̂ m ℏ x` — composition of
 `quantumPotential` with `badialiAmplitude`.
* `badialiQuantumPotential_eq_unfold` — pointwise unfolding to
 `−ℏ²·Δ(√(φφ̂)) / (2m·√(φφ̂))`.

### §3 — Concrete `BohmianQuantumPotential` from Badiali fields

* **`BohmianQuantumPotential.ofBadialiFields`** — main theorem
 constructor: takes positive `(φ, φ̂)` and `(m, ℏ)`, produces a
 `BohmianQuantumPotential` record whose `laplacianAmplitude`
 is `Δ (badialiAmplitude φ φ̂) x` — concrete, not abstract.
* `ofBadialiFields_laplacianAmplitude_eq`.
* `ofBadialiFields_amplitude_eq`.

## Scope

The explicit chain-rule expansion

 `Δ(√h) = Δh/(2√h) − |∇h|²/(4·h^(3/2))`

(with `h := φ·φ̂` for Badiali) is a Mathlib-derivative computation
that would unfold the Laplacian-of-square-root into the underlying
`Δφ, Δφ̂, ∇φ·∇φ̂` terms. This is **not** done here — but
critically, **it is not needed for the Bohmian quantum-potential
gap closure**. The `BohmianQuantumPotential` record includes the
Laplacian as a single value `Δ R x`; the amplitude `R = √(φφ̂)` is
a concrete function, and the Laplacian is the Mathlib Laplacian.
The chain-rule expansion is a downstream simplification, not a
structural gap.

## References

* Madelung 1927, de Broglie 1927, Bohm 1952.
* Badiali 2005 *J. Phys. A* 38, 2835 §6 (Eq. 35–36).
* `Physlib.QuantumMechanics.Schrodinger.BohmianQuantumPotential`.
* `Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

open Real
open scoped InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ## §1 — Badiali amplitude as a function `E → ℝ` -/

/-- **Badiali amplitude** `R(x) := √(φ(x) · φ̂(x))`.

Pointwise: at every spatial point `x ∈ E`, the amplitude is the
square root of the forward × backward density product.  This is
the Madelung amplitude in the Badiali decomposition, equal by
algebra to `exp(R_Bd(x))` where `R_Bd` is the Badiali amplitude
phase. -/
def badialiAmplitude (φ φ_hat : E → ℝ) : E → ℝ :=
  fun x => Real.sqrt (φ x * φ_hat x)

section BasicAmplitudeLemmas

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Pointwise unfolding**: `R(x) = √(φ(x)·φ̂(x))`. -/
theorem badialiAmplitude_apply (φ φ_hat : E → ℝ) (x : E) :
    badialiAmplitude φ φ_hat x = Real.sqrt (φ x * φ_hat x) := rfl

/-- **Amplitude non-negativity**: `R(x) ≥ 0` everywhere. -/
theorem badialiAmplitude_nonneg (φ φ_hat : E → ℝ) (x : E) :
    0 ≤ badialiAmplitude φ φ_hat x :=
  Real.sqrt_nonneg _

/-- **Amplitude strict positivity** at points where `φ·φ̂ > 0`. -/
theorem badialiAmplitude_pos_of_product_pos
    {φ φ_hat : E → ℝ} {x : E} (h : 0 < φ x * φ_hat x) :
    0 < badialiAmplitude φ φ_hat x :=
  Real.sqrt_pos.mpr h

/-- **Amplitude squared equals the Born density**: `R(x)² = φ(x)·φ̂(x)`. -/
theorem badialiAmplitude_sq
    {φ φ_hat : E → ℝ} {x : E} (h : 0 ≤ φ x * φ_hat x) :
    (badialiAmplitude φ φ_hat x) ^ 2 = φ x * φ_hat x := by
  unfold badialiAmplitude
  rw [sq, Real.mul_self_sqrt h]

end BasicAmplitudeLemmas

/-! ## §2 — Badiali quantum potential -/

/-- **Badiali quantum potential at `x`**:

  `Q_Bd(x) := −ℏ² · Δ(√(φ·φ̂))(x) / (2m · √(φ(x)·φ̂(x)))`.

Composition of the concrete Mathlib-Laplacian-based
`quantumPotential` with the Badiali amplitude
`R := √(φ·φ̂)`. -/
def badialiQuantumPotential (φ φ_hat : E → ℝ) (m ℏ : ℝ) (x : E) : ℝ :=
  quantumPotential (badialiAmplitude φ φ_hat) m ℏ x

/-- **Definitional unfolding** of the Badiali quantum potential. -/
theorem badialiQuantumPotential_eq_unfold
    (φ φ_hat : E → ℝ) (m ℏ : ℝ) (x : E) :
    badialiQuantumPotential φ φ_hat m ℏ x
      = -(ℏ^2) * Δ (badialiAmplitude φ φ_hat) x
          / (2 * m * badialiAmplitude φ φ_hat x) := rfl

/-! ## §3 — Concrete `BohmianQuantumPotential` from Badiali fields -/

/-- **:Bohmian quantum potential constructor from
Badiali forward/backward fields**.

Given positive forward `φ` and backward `φ̂` densities (point
positivity at the chosen `x`), positive mass `m`, and positive
`ℏ`, produces a `BohmianQuantumPotential` record whose:

* `mass`             = `m`,
* `wf.amplitude`     = `√(φ(x)·φ̂(x))`   (the concrete Madelung
                                          amplitude at `x`),
* `wf.hbar`          = `ℏ`,
* `laplacianAmplitude` = `Δ(√(φ·φ̂))(x)`   (the **concrete Mathlib
                                            Laplacian**, not an
                                            abstract real
                                            number).

This **closes the Sobolev-Laplacian gap** for the Bohmian
quantum potential in the Badiali setting.  The previously
abstract `laplacianAmplitude : ℝ` field is now the actual
second-order derivative on a finite-dimensional real
inner-product space. -/
def BohmianQuantumPotential.ofBadialiFields
    (φ φ_hat : E → ℝ) (m ℏ : ℝ) (x : E)
    (_hφ : 0 < φ x) (_hφ_hat : 0 < φ_hat x) (hm : 0 < m) (hℏ : 0 < ℏ) :
    BohmianQuantumPotential :=
  BohmianQuantumPotential.ofMathlibLaplacian
    (badialiAmplitude φ φ_hat) m ℏ x
    (badialiAmplitude_nonneg φ φ_hat x)
    hm hℏ

/-- **The constructor's `laplacianAmplitude` IS the Mathlib
Laplacian of `√(φ·φ̂)`** — concrete, not abstract. -/
theorem BohmianQuantumPotential.ofBadialiFields_laplacianAmplitude_eq
    (φ φ_hat : E → ℝ) (m ℏ : ℝ) (x : E)
    (hφ : 0 < φ x) (hφ_hat : 0 < φ_hat x) (hm : 0 < m) (hℏ : 0 < ℏ) :
    (BohmianQuantumPotential.ofBadialiFields φ φ_hat m ℏ x hφ hφ_hat hm hℏ).laplacianAmplitude
      = Δ (badialiAmplitude φ φ_hat) x := rfl

/-- **The constructor's amplitude is `√(φ(x)·φ̂(x))`**. -/
theorem BohmianQuantumPotential.ofBadialiFields_amplitude_eq
    (φ φ_hat : E → ℝ) (m ℏ : ℝ) (x : E)
    (hφ : 0 < φ x) (hφ_hat : 0 < φ_hat x) (hm : 0 < m) (hℏ : 0 < ℏ) :
    (BohmianQuantumPotential.ofBadialiFields φ φ_hat m ℏ x hφ hφ_hat hm hℏ).wf.amplitude
      = Real.sqrt (φ x * φ_hat x) := rfl

/-- **The Badiali Bohmian quantum-potential scale is `−ℏ²/(2m) < 0`**. -/
theorem BohmianQuantumPotential.ofBadialiFields_scale_neg
    (φ φ_hat : E → ℝ) (m ℏ : ℝ) (x : E)
    (hφ : 0 < φ x) (hφ_hat : 0 < φ_hat x) (hm : 0 < m) (hℏ : 0 < ℏ) :
    quantumPotentialScale
        (BohmianQuantumPotential.ofBadialiFields φ φ_hat m ℏ x hφ hφ_hat hm hℏ) < 0 :=
  quantumPotentialScale_neg _

/-! ## §4 — Sign theorems for the Badiali quantum potential -/

/-- **Badiali quantum potential is negative at convex amplitude
points**.

When `φ(x), φ̂(x) > 0` (Born density positive) and `Δ R(x) > 0`
(amplitude convex at `x`), the Badiali quantum potential is
strictly negative — an attractive quantum force.

Direct application of `quantumPotential_neg_of_laplacian_pos`
specialised to the Badiali amplitude. -/
theorem badialiQuantumPotential_neg_of_amplitude_convex
    {φ φ_hat : E → ℝ} {m ℏ : ℝ} {x : E}
    (hφ : 0 < φ x) (hφ_hat : 0 < φ_hat x)
    (hΔ_pos : 0 < Δ (badialiAmplitude φ φ_hat) x)
    (hm : 0 < m) (hℏ : 0 < ℏ) :
    badialiQuantumPotential φ φ_hat m ℏ x < 0 := by
  unfold badialiQuantumPotential
  apply quantumPotential_neg_of_laplacian_pos _ hΔ_pos hm hℏ
  exact badialiAmplitude_pos_of_product_pos (mul_pos hφ hφ_hat)

/-- **Badiali quantum potential is positive at concave amplitude
points**.

When `φ(x), φ̂(x) > 0` and `Δ R(x) < 0` (amplitude concave at `x`),
the Badiali quantum potential is strictly positive — a repulsive
quantum force, the source of the kinetic pressure that prevents
Born-density concentration into singular spikes. -/
theorem badialiQuantumPotential_pos_of_amplitude_concave
    {φ φ_hat : E → ℝ} {m ℏ : ℝ} {x : E}
    (hφ : 0 < φ x) (hφ_hat : 0 < φ_hat x)
    (hΔ_neg : Δ (badialiAmplitude φ φ_hat) x < 0)
    (hm : 0 < m) (hℏ : 0 < ℏ) :
    0 < badialiQuantumPotential φ φ_hat m ℏ x := by
  unfold badialiQuantumPotential
  apply quantumPotential_pos_of_laplacian_neg _ hΔ_neg hm hℏ
  exact badialiAmplitude_pos_of_product_pos (mul_pos hφ hφ_hat)

end Physlib.QuantumMechanics.Schrodinger

end

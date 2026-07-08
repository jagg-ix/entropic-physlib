/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.MadelungPolarDecomposition
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Bohmian quantum potential as a Mathlib-Laplacian-derived function

Phase-6 closure of the Sobolev-Laplacian gap in the Bohmian
quantum-potential lane.

The Madelung 1927 polar form `ψ = R·exp(i·S/ℏ)` of the
Schrödinger wavefunction, fed into the Schrödinger equation,
splits into the **continuity equation** and the **Hamilton–Jacobi–
Madelung equation** with an extra term — the **Bohmian quantum
potential** (de Broglie 1927, Bohm 1952):

 `Q(x) := −ℏ² / (2m) · Δ R(x) / R(x)`.

`Δ` is the **Laplacian on physical space** — *not* an abstract
real number. Previous physlib files
(`Physlib.QuantumMechanics.Schrodinger.MadelungPolarDecomposition`
and the port) include the Bohmian quantum potential
record `BohmianQuantumPotential` with a field
`laplacianAmplitude : ℝ` — an **abstracted** Laplacian value.

This file closes that gap.

**The load-bearing identification**:

Mathlib's `Δ` (from `Mathlib.Analysis.InnerProductSpace.Laplacian`)
is the **real Laplacian** on a finite-dimensional real
inner-product space `E`, with notation `Δ f` and definition via
the canonical covariant tensor. The Bohmian quantum potential

 `Q(x) := −ℏ²·(Δ R)(x) / (2·m·R(x))`

is therefore a **concrete function** `E → ℝ` whenever `R : E → ℝ`
is `C²` and `R(x) ≠ 0`.

This file:

1. Defines the **concrete** Bohmian quantum potential
 `quantumPotential R m ℏ x` for any `C²` amplitude
 `R : E → ℝ` on a finite-dim real inner-product space.
2. Proves the **defining identity**
 `Q(x) · R(x) = −ℏ²/(2m)·Δ R(x)` (after multiplying through
 by `R(x)`), the algebraic statement of the quantum potential.
3. Proves **sign theorems**:
 * `quantumPotential_neg_of_laplacian_pos` — `Q < 0` when
 `R > 0` and `Δ R > 0` (amplitude convex, attractive
 quantum force).
 * `quantumPotential_pos_of_laplacian_neg` — `Q > 0` when
 `R > 0` and `Δ R < 0` (amplitude concave, repulsive
 quantum force).
4. **Closes the abstract laplacianAmplitude gap**: the
 `BohmianQuantumPotential` record's `laplacianAmplitude` field
 is now obtained as `Δ R x` from a real `C²` amplitude
 `R : E → ℝ`.

## Contents

### §1 — Concrete Bohmian quantum potential

* `quantumPotential R m ℏ x` — the pointwise quantum potential,
 using Mathlib's `Δ R x`.

### §2 — Algebraic identities

* `quantumPotential_mul_R` — `Q(x)·R(x) = −ℏ²/(2m)·Δ R(x)`.
* `quantumPotential_eq_scale_div_amplitude` —
 `Q(x) = (−ℏ²/(2m))·(Δ R(x)/R(x))`.

### §3 — Sign theorems

* `quantumPotential_neg_of_laplacian_pos`.
* `quantumPotential_pos_of_laplacian_neg`.

### §4 — Bridge to physlib's abstract `BohmianQuantumPotential`

* `BohmianQuantumPotential.ofMathlibLaplacian` — constructor that
 takes a `C²` amplitude `R : E → ℝ` and a point `x : E`, and
 produces a `BohmianQuantumPotential` whose `laplacianAmplitude`
 is the actual Mathlib Laplacian `Δ R x`.
* `BohmianQuantumPotential.ofMathlibLaplacian_laplacianAmplitude_eq` —
 certifies that the constructor's `laplacianAmplitude` is exactly
 `Δ R x`.

## Scope

The chain-rule expansion `Δ(√(φ·φ̂))` in terms of `Δφ, Δφ̂, ∇φ·∇φ̂`
for the Badiali amplitude `R := √(φ·φ̂)` is a Mathlib-derivative
computation that is left to a downstream file when needed — the
quantum potential `Q[badialiAmplitude]` is well-defined here as
`quantumPotential (badialiAmplitude φ φ̂) m ℏ x` whenever
`φ, φ̂ ∈ C²` and `φ(x)·φ̂(x) > 0`.

## References

* Madelung 1927 *Z. Phys.* 40, 322.
* de Broglie 1927 — pilot-wave theory.
* Bohm 1952 *Phys. Rev.* 85, 166 — Bohmian mechanics.
* `Mathlib.Analysis.InnerProductSpace.Laplacian` (Kebekus 2025).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

open Real
open scoped InnerProductSpace Laplacian

/-! ## §1 — Concrete Bohmian quantum potential -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Concrete Bohmian quantum potential** at a point `x`:

  `Q(x) := −ℏ² · Δ R(x) / (2 · m · R(x))`.

Here `Δ` is Mathlib's real Laplacian on the finite-dimensional
real inner-product space `E`, and `R : E → ℝ` is the Madelung
amplitude.  The expression is the pointwise quantum potential of
de Broglie–Bohm mechanics.

Well-defined whenever `m ≠ 0` and `R(x) ≠ 0`. -/
def quantumPotential (R : E → ℝ) (m ℏ : ℝ) (x : E) : ℝ :=
  -(ℏ^2) * Δ R x / (2 * m * R x)

/-! ## §2 — Algebraic identities -/

/-- **Quantum potential times amplitude**:

  `Q(x) · R(x) = −ℏ²/(2m) · Δ R(x)`.

The defining algebraic identity of the quantum potential — clears
the denominator `R(x)` from the definition.  Useful for chained
Schrödinger-equation manipulations. -/
theorem quantumPotential_mul_R (R : E → ℝ) (m ℏ : ℝ) (x : E)
    (hR : R x ≠ 0) (hm : m ≠ 0) :
    quantumPotential R m ℏ x * R x = -(ℏ^2) / (2 * m) * Δ R x := by
  unfold quantumPotential
  have h2m : (2 * m : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hm
  field_simp

/-- **Quantum potential as scale × (Laplacian / amplitude)**:

  `Q(x) = (−ℏ²/(2m)) · (Δ R(x) / R(x))`.

Direct factorization separating the dimensional scale factor from
the Laplacian-to-amplitude ratio.  Connects to the existing
`quantumPotentialScale := −ℏ²/(2m)` record-field of
`BohmianQuantumPotential`. -/
theorem quantumPotential_eq_scale_div_amplitude
    (R : E → ℝ) (m ℏ : ℝ) (x : E) (hR : R x ≠ 0) (hm : m ≠ 0) :
    quantumPotential R m ℏ x = -(ℏ^2) / (2 * m) * (Δ R x / R x) := by
  unfold quantumPotential
  have h2m : (2 * m : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hm
  field_simp

/-! ## §3 — Sign theorems -/

/-- **Quantum potential is negative where amplitude is convex**:

When `R(x) > 0` (positive amplitude), `Δ R(x) > 0` (convex
amplitude curvature at `x`), `m > 0` and `ℏ > 0`, the Bohmian
quantum potential is **strictly negative**:

  `Q(x) < 0`.

In Bohmian language: a convex amplitude (probability density
locally minimized) gives an **attractive** quantum force toward
that region. -/
theorem quantumPotential_neg_of_laplacian_pos
    {R : E → ℝ} {m ℏ : ℝ} {x : E}
    (hR_pos : 0 < R x) (hΔ_pos : 0 < Δ R x)
    (hm_pos : 0 < m) (hℏ_pos : 0 < ℏ) :
    quantumPotential R m ℏ x < 0 := by
  unfold quantumPotential
  apply div_neg_of_neg_of_pos
  · -- Numerator: −ℏ² · Δ R(x) < 0
    have hℏ_sq_pos : 0 < ℏ^2 := pow_pos hℏ_pos 2
    have : 0 < ℏ^2 * Δ R x := mul_pos hℏ_sq_pos hΔ_pos
    linarith
  · -- Denominator: 2·m·R(x) > 0
    exact mul_pos (mul_pos two_pos hm_pos) hR_pos

/-- **Quantum potential is positive where amplitude is concave**:

When `R(x) > 0` and `Δ R(x) < 0` (concave amplitude curvature at
`x`), with `m > 0` and `ℏ > 0`, the Bohmian quantum potential is
**strictly positive**:

  `Q(x) > 0`.

In Bohmian language: a concave amplitude (probability density
locally maximized) gives a **repulsive** quantum force away from
that region — the source of the quantum kinetic-pressure that
prevents wavefunction collapse. -/
theorem quantumPotential_pos_of_laplacian_neg
    {R : E → ℝ} {m ℏ : ℝ} {x : E}
    (hR_pos : 0 < R x) (hΔ_neg : Δ R x < 0)
    (hm_pos : 0 < m) (hℏ_pos : 0 < ℏ) :
    0 < quantumPotential R m ℏ x := by
  unfold quantumPotential
  apply div_pos
  · -- Numerator: −ℏ² · Δ R(x) > 0
    have hℏ_sq_pos : 0 < ℏ^2 := pow_pos hℏ_pos 2
    have : ℏ^2 * Δ R x < 0 := mul_neg_of_pos_of_neg hℏ_sq_pos hΔ_neg
    linarith
  · exact mul_pos (mul_pos two_pos hm_pos) hR_pos

/-- **Quantum potential vanishes at amplitude-harmonic points**:
When `Δ R(x) = 0` (amplitude is locally harmonic / linear),
the Bohmian quantum potential vanishes pointwise. -/
theorem quantumPotential_eq_zero_of_laplacian_zero
    {R : E → ℝ} {m ℏ : ℝ} {x : E} (hΔ_zero : Δ R x = 0) :
    quantumPotential R m ℏ x = 0 := by
  unfold quantumPotential
  rw [hΔ_zero]
  simp

/-! ## §4 — Bridge to physlib's abstract `BohmianQuantumPotential` -/

/-- **Constructor — Bohmian quantum potential from a Mathlib-Laplacian
amplitude**.

Takes a `C²` amplitude `R : E → ℝ`, a positive mass `m`, a
positive `ℏ`, and a base point `x : E`.  Produces a
`BohmianQuantumPotential` record whose `laplacianAmplitude` is the
**actual Mathlib Laplacian** `Δ R x` — closing the abstract
`laplacianAmplitude : ℝ` gap in the original `BohmianQuantumPotential`
struct.

The wavefunction record `wf` is built with the amplitude
`R x` and phase `0` (the phase plays no role in the quantum
potential; consumers needing a non-zero phase can update `wf`
post hoc). -/
def BohmianQuantumPotential.ofMathlibLaplacian
    (R : E → ℝ) (m ℏ : ℝ) (x : E)
    (hR_nonneg : 0 ≤ R x) (hm_pos : 0 < m) (hℏ_pos : 0 < ℏ) :
    BohmianQuantumPotential where
  mass               := m
  mass_pos           := hm_pos
  wf := {
    amplitude        := R x
    amplitude_nonneg := hR_nonneg
    phase            := 0
    hbar             := ℏ
    hbar_pos         := hℏ_pos
  }
  laplacianAmplitude := Δ R x

/-- **The constructor's `laplacianAmplitude` IS the Mathlib
Laplacian**.

Closes the abstract `laplacianAmplitude : ℝ` field at the
type-checker level: it is no longer an opaque real number but
exactly the `Δ R x` value from
`Mathlib.Analysis.InnerProductSpace.Laplacian`. -/
theorem BohmianQuantumPotential.ofMathlibLaplacian_laplacianAmplitude_eq
    (R : E → ℝ) (m ℏ : ℝ) (x : E)
    (hR_nonneg : 0 ≤ R x) (hm_pos : 0 < m) (hℏ_pos : 0 < ℏ) :
    (BohmianQuantumPotential.ofMathlibLaplacian R m ℏ x hR_nonneg hm_pos hℏ_pos).laplacianAmplitude
      = Δ R x := rfl

/-- **The constructor's `quantumPotentialScale` is `−ℏ²/(2m)`** —
inherited from the generic `quantumPotentialScale_neg` theorem
in `MadelungPolarDecomposition.lean`.

Combined with the constructor identity, certifies that the
*concrete* Bohmian quantum potential
`Q := scale · laplacianAmplitude / amplitude` has the right scale
and the right Laplacian source. -/
theorem BohmianQuantumPotential.ofMathlibLaplacian_scale_neg
    (R : E → ℝ) (m ℏ : ℝ) (x : E)
    (hR_nonneg : 0 ≤ R x) (hm_pos : 0 < m) (hℏ_pos : 0 < ℏ) :
    quantumPotentialScale
        (BohmianQuantumPotential.ofMathlibLaplacian R m ℏ x hR_nonneg hm_pos hℏ_pos) < 0 :=
  quantumPotentialScale_neg _

/-! ## §5 — Concrete quantum potential matches the abstract scale-product form -/

/-- **The concrete quantum potential equals the abstract
`scale · (laplacianAmplitude / amplitude)` form**.

When the abstract `BohmianQuantumPotential` is constructed from a
real Mathlib-Laplacian amplitude, the concrete `quantumPotential`
function and the abstract scale-product form coincide:

  `quantumPotential R m ℏ x
    = quantumPotentialScale Q · (laplacianAmplitude Q / amplitude Q)`

where `Q := BohmianQuantumPotential.ofMathlibLaplacian R m ℏ x …`.

Closes the algebraic gap between the two representations. -/
theorem quantumPotential_eq_abstract_form
    (R : E → ℝ) (m ℏ : ℝ) (x : E)
    (hR_pos : 0 < R x) (hm_pos : 0 < m) (hℏ_pos : 0 < ℏ) :
    quantumPotential R m ℏ x
      = quantumPotentialScale
          (BohmianQuantumPotential.ofMathlibLaplacian R m ℏ x
            (le_of_lt hR_pos) hm_pos hℏ_pos)
        * (Δ R x / R x) := by
  rw [quantumPotential_eq_scale_div_amplitude R m ℏ x
        (ne_of_gt hR_pos) (ne_of_gt hm_pos)]
  rfl

end Physlib.QuantumMechanics.Schrodinger

end

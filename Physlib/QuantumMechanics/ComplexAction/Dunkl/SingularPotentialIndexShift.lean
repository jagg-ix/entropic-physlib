/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

/-!
# Absorbing the singular potential `g/x²` into a Bessel index shift (Junker §6 outlook)

Junker closes *On the Path Integral Formulation of Wigner–Dunkl Quantum Mechanics* (arXiv:2312.12895,
§6) by noting that "the singular potential `g/x²` may be absorbed via a change of index in the Bessel
processes." The mechanism is the Radon–Nikodym relation between two Bessel indices (Appendix A, Eq. A.6):
a Bessel path integral of index `α` with potential `V` equals one of index `β` with potential
`V + (α² − β²)/(2 z²)` (up to the `(xy)^{β−α}` speed-density prefactor). Read in reverse, a `1/z²`
(centrifugal) potential of strength `g` added to a Bessel-`β` process is *absorbed* into a shifted index
`α = √(β² + 2g)`, since then `(α² − β²)/2 = g`.

This module formalizes the algebraic core of that reduction and connects it back to the Dunkl arc:

* `besselCentrifugalCoeff α β = (α² − β²)/2` — the coefficient of the `1/z²` potential in Eq. A.6 that
  distinguishes index-`α` from index-`β` dynamics.
* `absorbedIndex β g = √(β² + 2g)` — the index that absorbs a `g/z²` potential (`absorbedIndex_sq`,
  `absorbedIndex_nonneg`, `absorbedIndex_mono`).
* `besselCentrifugalCoeff_absorbedIndex` — the reduction itself: the centrifugal coefficient of the
  shift `β → √(β² + 2g)` is exactly `g`, so the `g/x²` potential is gone from the index-`α` process.
* `absorbedIndex_zero` — consistency: no potential (`g = 0`) means no index shift.
* `dunkl_sectors_centrifugal` — the connection to the Dunkl reflection potential: the ½-shift between the
  Wigner–Dunkl *reflecting* (`ν − ½`) and *absorbing* (`ν + ½`) Bessel sectors (`EuclideanProcess`,
  Junker Eq. 77) carries centrifugal coefficient exactly `ν`. That is precisely the `ν/x²` by which the
  odd Dunkl generator exceeds the even one, `L₋^{(ν)} = L₊^{(ν)} − ν/x²` (Eq. 75) — the Dunkl reflection
  term `−(ν/x²)(1 − R)` of the Hamiltonian (Eq. 8) resolved into the even/odd split.
* `dunklAbsorbedParameter`, `besselAbsorbingIndex_dunklAbsorbedParameter` — adding a `g/x²` potential to
  the Dunkl absorbing sector renormalizes the deformation parameter `ν ↦ √((ν+½)² + 2g) − ½`.

## Honest scope

Formalized: the index-shift *algebra* — the exact quadratic relation `(α² − β²)/2 = g ⟺ α = √(β²+2g)`
that underlies the absorption, and its identification with the Dunkl reflecting/absorbing split. The
Bessel path-integral measures of Eq. A.6 themselves, and the `(xy)^{β−α}` Radon–Nikodym prefactor, are
carried symbolically by the existing `Dunkl.EuclideanProcess`/`Dunkl.HeatKernelBesselDensity` arc; the
functional-integral identity A.6 is cited, not re-derived.

## References

* G. Junker, *On the Path Integral Formulation of Wigner–Dunkl Quantum Mechanics*, arXiv:2312.12895,
  §6 (outlook: `g/x²` via change of index) and Appendix A (Eqs. A.1, A.6, A.7).
* `Dunkl.EuclideanProcess` — `besselReflectingIndex = ν − ½`, `besselAbsorbingIndex = ν + ½`,
  `besselGenEigenvalue`, `bessel_index_diff` (the Radon–Nikodym `+1` shift, Eq. A.6/A.7).
-/

set_option autoImplicit false

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.SingularPotentialIndexShift

/-- **[Junker Eq. A.6] The Bessel centrifugal coefficient** `(α² − β²)/2`: the strength of the `1/z²`
potential that distinguishes a Bessel process of index `α` from one of index `β`. In A.6,
`∫dB^{(α)} e^{−∫V} = (xy)^{β−α} ∫dB^{(β)} e^{−∫[V + (α²−β²)/(2z²)]}`. -/
noncomputable def besselCentrifugalCoeff (α β : ℝ) : ℝ := (α ^ 2 - β ^ 2) / 2

/-- **The index that absorbs a `g/z²` potential** `α = √(β² + 2g)`: the shifted Bessel index for which
the added centrifugal strength `g` on a Bessel-`β` process is reabsorbed (Junker §6). -/
noncomputable def absorbedIndex (β g : ℝ) : ℝ := Real.sqrt (β ^ 2 + 2 * g)

/-- The absorbed index is non-negative — a Bessel index `α ≥ 0` (`α > −1` in general). -/
theorem absorbedIndex_nonneg (β g : ℝ) : 0 ≤ absorbedIndex β g := Real.sqrt_nonneg _

/-- **The absorbed index squares back** `(√(β²+2g))² = β² + 2g`, whenever `β² + 2g ≥ 0` (the Bessel
index is real). -/
theorem absorbedIndex_sq (β g : ℝ) (h : 0 ≤ β ^ 2 + 2 * g) :
    (absorbedIndex β g) ^ 2 = β ^ 2 + 2 * g := by
  unfold absorbedIndex; exact Real.sq_sqrt h

/-- **The `g/x²` absorption (Junker §6).** The Bessel centrifugal coefficient of the shift
`β → √(β² + 2g)` is exactly `g`: `besselCentrifugalCoeff (absorbedIndex β g) β = g`. Hence a `g/z²`
potential added to a Bessel-`β` process is fully accounted for by moving to the index `√(β² + 2g)`, with
no singular potential left (Eq. A.6 read in reverse). -/
theorem besselCentrifugalCoeff_absorbedIndex (β g : ℝ) (h : 0 ≤ β ^ 2 + 2 * g) :
    besselCentrifugalCoeff (absorbedIndex β g) β = g := by
  unfold besselCentrifugalCoeff; rw [absorbedIndex_sq β g h]; ring

/-- **No potential, no shift**: `g = 0` leaves the index unchanged, `absorbedIndex β 0 = β` (for
`β ≥ 0`). The absorption is the identity exactly when there is nothing to absorb. -/
theorem absorbedIndex_zero (β : ℝ) (hβ : 0 ≤ β) : absorbedIndex β 0 = β := by
  unfold absorbedIndex; rw [mul_zero, add_zero]; exact Real.sqrt_sq hβ

/-- **A stronger singular potential needs a larger index**: `absorbedIndex` is monotone in the
centrifugal strength `g`. -/
theorem absorbedIndex_mono (β : ℝ) {g₁ g₂ : ℝ} (h : g₁ ≤ g₂) :
    absorbedIndex β g₁ ≤ absorbedIndex β g₂ := by
  unfold absorbedIndex; exact Real.sqrt_le_sqrt (by linarith)

/-- **The Dunkl reflection potential is the centrifugal coefficient of the ½-index-shift.** The Wigner–
Dunkl process splits into a *reflecting* Bessel process of index `ν − ½` and an *absorbing* one of index
`ν + ½` (`EuclideanProcess`, Junker Eq. 77). The centrifugal coefficient relating these two sectors is
`besselCentrifugalCoeff (ν + ½) (ν − ½) = ν` — precisely the `ν/x²` by which the odd Dunkl generator
exceeds the even one, `L₋^{(ν)} = L₊^{(ν)} − ν/x²` (Eq. 75), i.e. the Dunkl reflection term
`−(ν/x²)(1 − R)` of the Hamiltonian (Eq. 8). The Dunkl deformation is itself a `1/x²` index shift. -/
theorem dunkl_sectors_centrifugal (ν : ℝ) :
    besselCentrifugalCoeff (besselAbsorbingIndex ν) (besselReflectingIndex ν) = ν := by
  unfold besselCentrifugalCoeff besselAbsorbingIndex besselReflectingIndex; ring

/-- **The Dunkl parameter renormalized by a `g/x²` potential** `ν ↦ √((ν+½)² + 2g) − ½`: the effective
deformation parameter whose absorbing Bessel index equals that of the original absorbing sector with the
`g/x²` potential absorbed (`besselAbsorbingIndex_dunklAbsorbedParameter`). -/
noncomputable def dunklAbsorbedParameter (ν g : ℝ) : ℝ :=
  absorbedIndex (besselAbsorbingIndex ν) g - 1 / 2

/-- **A `g/x²` potential renormalizes the Dunkl parameter.** The absorbing Bessel index of the
renormalized parameter `dunklAbsorbedParameter ν g` equals the absorbed index of the original absorbing
sector: `besselAbsorbingIndex (dunklAbsorbedParameter ν g) = absorbedIndex (besselAbsorbingIndex ν) g`.
So adding `g/x²` to the Wigner–Dunkl absorbing sector is equivalent to running the bare process with the
shifted deformation `ν ↦ √((ν+½)² + 2g) − ½`. -/
theorem besselAbsorbingIndex_dunklAbsorbedParameter (ν g : ℝ) :
    besselAbsorbingIndex (dunklAbsorbedParameter ν g) = absorbedIndex (besselAbsorbingIndex ν) g := by
  simp only [besselAbsorbingIndex, dunklAbsorbedParameter]; ring

end Physlib.QuantumMechanics.ComplexAction.Dunkl.SingularPotentialIndexShift

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction

/-!
# Bridging the geometric edge `∂Σ` to the abstract area `A`, `V`, `V_ζ`

`CausalDiamond.Construction` built the causal diamond and its edge `∂Σ` (the bifurcation surface, at
`q = iR`, i.e. `t = 0`, `r = R`). `CausalDiamondThermodynamics` proved the Smarr formula and first law
for an *abstract* area function `A(V, Λ)`. This file **closes the loop**: it gives `A`, `V`, `V_ζ`, and
the extrinsic-curvature trace `k` their concrete geometric values on the constructed diamond and shows
they satisfy the abstract relations.

For a flat (Minkowski) diamond whose edge `∂Σ` is a `(d−2)`-sphere of area radius `R` (`Ω = ` area of
the unit `(d−2)`-sphere):

* **area of the edge** `A = Ω R^{d-2}` (`diamondArea`),
* **proper volume of the ball `Σ`** `V = Ω R^{d-1}/(d-1)` (`diamondVolume`),
* **extrinsic-curvature trace of `∂Σ`** `k = (d-2)/R` (`extrinsicK`), `= ∂A/∂V`,
* **thermodynamic volume** `V_ζ = κ Ω R^d/((d-1)(d+1))` (`thermoVolume`, the flat `R/L → 0` limit of
  Jacobson–Visser Eq. 3.14).

The area radius is read off the constructed edge: `R = Im(iR) = edgeRadius (iR)`
(`canonical_edgeRadius`), so these are values *on the constructed diamond*.

## The abstract relations hold concretely (flat, `Λ = 0`)

* `concrete_smarr` / `constructed_diamond_smarr` — the Smarr formula `(d-2)κA = (d-1)κk V + 2V_ζ·Λ`
  with `Λ = 0`, i.e. `(d-2)κA = (d-1)κk V` (the `(d-1)` and one power of `R` cancel exactly).
* `volume_hasDerivAt` — `dV/dR = A` (the rate of volume change is the area),
* `area_hasDerivAt` — `dA/dR = k·A`,
* `concrete_firstLaw` — hence the first law `dA = k dV` (`δA = k δV` at fixed `Λ`), matching
  `CausalDiamondThermodynamics.causalDiamond_firstLaw` with `V_ζ δΛ = 0`.

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, §3, §5.2. This development: `CausalDiamond.Construction`,
  `CausalDiamondThermodynamics`.

No new axioms.
-/

set_option autoImplicit false

open Complex Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Area

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction

/-! ## §A — the area radius read off the constructed edge `∂Σ` -/

/-- **The area radius** of a point on the edge `∂Σ` is its spatial coordinate `Im q` (`= r`). -/
def edgeRadius (q : ℂ) : ℝ := q.im

/-- **The canonical edge point `q = iR` has area radius `R`** — the `(d−2)`-sphere `∂Σ` of the
constructed diamond `D(−R, R)` has radius `R`. -/
@[simp] theorem canonical_edgeRadius (R : ℝ) : edgeRadius (Complex.I * (R : ℂ)) = R := by
  simp [edgeRadius, Complex.mul_im]

/-! ## §B — concrete geometric quantities of the flat diamond -/

/-- **Area of the edge `∂Σ`** `A = Ω R^{d-2}` (`Ω = ` unit `(d−2)`-sphere area). -/
def diamondArea (Ω d R : ℝ) : ℝ := Ω * R ^ (d - 2)

/-- **Proper volume of the ball `Σ`** `V = Ω R^{d-1}/(d-1)`. -/
def diamondVolume (Ω d R : ℝ) : ℝ := Ω * R ^ (d - 1) / (d - 1)

/-- **Extrinsic-curvature trace of `∂Σ`** `k = (d-2)/R` (each of the `d−2` principal curvatures of a
sphere of radius `R` is `1/R`); equals `∂A/∂V`. -/
def extrinsicK (d R : ℝ) : ℝ := (d - 2) / R

/-- **Thermodynamic volume** `V_ζ = κ Ω R^d/((d-1)(d+1))` — the flat `R/L → 0` limit of Jacobson–Visser
Eq. 3.14, `V_ζ^flat = κ R V^flat/(d+1)`. -/
def thermoVolume (κ Ω d R : ℝ) : ℝ := κ * Ω * R ^ d / ((d - 1) * (d + 1))

/-! ## §C — the Smarr formula holds with the concrete values -/

/-- **The Smarr formula for the flat diamond** `(d-2)κA = (d-1)κk V`: the `(d-1)` and one power of `R`
cancel exactly (`R^{d-1}/R = R^{d-2}`). -/
theorem concrete_smarr (κ Ω d R : ℝ) (hR : 0 < R) (hd1 : d - 1 ≠ 0) :
    (d - 2) * κ * diamondArea Ω d R
      = (d - 1) * κ * extrinsicK d R * diamondVolume Ω d R := by
  unfold diamondArea extrinsicK diamondVolume
  have hkey : R ^ (d - 1) = R ^ (d - 2) * R := by
    have h := Real.rpow_add hR (d - 2) 1
    rw [Real.rpow_one] at h
    rw [show d - 1 = (d - 2) + 1 by ring]; exact h
  rw [hkey]
  field_simp

/-- **The Smarr formula in the abstract `CausalDiamondThermodynamics` shape** (flat ⟹ `Λ = 0`):
`(d-2)κA = (d-1)κk V + 2 V_ζ Λ`. The thermodynamic-volume term drops because `Λ = 0`. -/
theorem concrete_smarr_flat (κ Ω d R : ℝ) (hR : 0 < R) (hd1 : d - 1 ≠ 0) :
    (d - 2) * κ * diamondArea Ω d R
      = (d - 1) * κ * extrinsicK d R * diamondVolume Ω d R + 2 * thermoVolume κ Ω d R * (0 : ℝ) := by
  rw [mul_zero, add_zero]
  exact concrete_smarr κ Ω d R hR hd1

/-- **Smarr on the constructed diamond**: the same relation, with every geometric quantity evaluated at
the area radius `R = edgeRadius (iR)` read off the constructed edge `∂Σ`. -/
theorem constructed_diamond_smarr (κ Ω d R : ℝ) (hR : 0 < R) (hd1 : d - 1 ≠ 0) :
    (d - 2) * κ * diamondArea Ω d (edgeRadius (Complex.I * (R : ℂ)))
      = (d - 1) * κ * extrinsicK d (edgeRadius (Complex.I * (R : ℂ)))
          * diamondVolume Ω d (edgeRadius (Complex.I * (R : ℂ))) := by
  rw [canonical_edgeRadius]
  exact concrete_smarr κ Ω d R hR hd1

/-! ## §D — the first law `dA = k dV` holds with the concrete values -/

/-- **`dV/dR = A`** — the rate of change of the ball volume with radius is the area of its edge. -/
theorem volume_hasDerivAt (Ω d R : ℝ) (hR : 0 < R) (hd1 : d - 1 ≠ 0) :
    HasDerivAt (fun r => diamondVolume Ω d r) (diamondArea Ω d R) R := by
  have hval : diamondArea Ω d R = Ω * ((d - 1) * R ^ (d - 1 - 1)) / (d - 1) := by
    unfold diamondArea
    rw [show d - 1 - 1 = d - 2 by ring]
    field_simp
  rw [hval]
  exact ((Real.hasDerivAt_rpow_const (x := R) (p := d - 1)
    (Or.inl hR.ne')).const_mul Ω).div_const (d - 1)

/-- **`dA/dR = k·A`** — the area changes at the rate `k` (extrinsic curvature) times itself. -/
theorem area_hasDerivAt (Ω d R : ℝ) (hR : 0 < R) :
    HasDerivAt (fun r => diamondArea Ω d r) (extrinsicK d R * diamondArea Ω d R) R := by
  have hval : extrinsicK d R * diamondArea Ω d R = Ω * ((d - 2) * R ^ (d - 2 - 1)) := by
    unfold extrinsicK diamondArea
    rw [Real.rpow_sub hR (d - 2) 1, Real.rpow_one]
    field_simp
  rw [hval]
  exact (Real.hasDerivAt_rpow_const (x := R) (p := d - 2) (Or.inl hR.ne')).const_mul Ω

/-- **The first law of the constructed diamond** `dA = k dV` (Jacobson–Visser Eq. 3.22 at fixed `Λ`):
the area variation equals the extrinsic-curvature trace times the volume variation, exactly. This is
`causalDiamond_firstLaw` with the concrete geometric `A`, `V`, `k`, and `V_ζ δΛ = 0`. -/
theorem concrete_firstLaw (Ω d R : ℝ) (hR : 0 < R) (hd1 : d - 1 ≠ 0) :
    deriv (fun r => diamondArea Ω d r) R
      = extrinsicK d R * deriv (fun r => diamondVolume Ω d r) R := by
  rw [(area_hasDerivAt Ω d R hR).deriv, (volume_hasDerivAt Ω d R hR hd1).deriv]

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Area

end

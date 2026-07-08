/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Area

/-!
# The (A)dS Smarr formula: the full `V_ζ` with curvature radius `L`

`CausalDiamond.Area` gave the flat (`Λ = 0`) Smarr formula `(d-2)κA = (d-1)κk V`. This file
completes it to a **nonzero cosmological constant** `Λ ≠ 0`, where the thermodynamic-volume term
participates. For a causal diamond of area radius `R` in a maximally symmetric space of curvature
radius `L` (de Sitter for `Λ > 0`, anti-de Sitter for `Λ < 0`):

* **extrinsic-curvature trace** `k = (d-2)/R · √(1 − (R/L)²)` (Jacobson–Visser Eq. 2.12);
* **thermodynamic volume** `V_ζ = (κL²/R)(V_R^flat − √(1−(R/L)²) · V_R)` (Eq. 3.14), where
  `V_R^flat = Ω R^{d-1}/(d-1)` is the flat sphere volume (`diamondVolume`) and `V_R` is the *curved*
  proper volume of the ball `Σ` (a free parameter here);
* **cosmological constant** `Λ = (d-1)(d-2)/(2L²)` for dS, `−(d-1)(d-2)/(2L²)` for AdS.

## The exact cancellation

The Smarr formula `(d-2)κA = (d-1)κk V_R + 2 V_ζ Λ` holds, and the proper volume `V_R` and the
`√(1−(R/L)²)` factor **cancel exactly**: the `k V_R` term and the `−√… V_R` piece of `V_ζ` annihilate,
leaving only the flat sphere volume `V_R^flat`, so

  `(d-2)κA = (d-1)(d-2)κ/R · V_R^flat = (d-2)κ Ω R^{d-2}`.

`adsSmarr_general` proves this with `V_R` and `√(1−(R/L)²)` as *free* reals (the cancellation is
structural), and with the cosmological-constant scale `M` (`= ±L²`) appearing as `κM/R` in `V_ζ` and
`…/(2M)` in `Λ`, so `M` cancels too — hence the *same* identity covers dS (`M = L²`) and
AdS (`M = −L²`). The flat case (`CausalDiamond.Area.concrete_smarr`) is `s = 1`; the de Sitter
static patch is `R = L`, where `√(1−(R/L)²) = 0`, so `k = 0` (`adsExtrinsicK_staticPatch`).

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, Eqs. 2.12, 3.14, 3.16. This development:
  `CausalDiamond.Area`, `CausalDiamond.Construction`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdS

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Area

/-! ## §A — the (A)dS geometric quantities -/

/-- **The relativistic factor** `√(1 − (R/L)²)` appearing in `k` and `V_ζ` (Jacobson–Visser Eqs.
2.10–2.12, 3.14). It vanishes at the de Sitter horizon `R = L` and tends to `1` in the flat limit
`L → ∞`. -/
def sqrtFactor (L R : ℝ) : ℝ := Real.sqrt (1 - (R / L) ^ 2)

/-- **Extrinsic-curvature trace in (A)dS** `k = (d-2) s / R` with `s = √(1−(R/L)²)` (Eq. 2.12). For
`s = 1` (flat limit) this is the flat `extrinsicK d R = (d-2)/R`. -/
def adsExtrinsicK (d R s : ℝ) : ℝ := (d - 2) * s / R

/-- **Thermodynamic volume in (A)dS** `V_ζ = (κM/R)(V_R^flat − s·V_R)` (Eq. 3.14), `M = ±L²`,
`V_R^flat = diamondVolume`, `V_R = ` the curved proper volume (free). -/
def thermoVolumeAdS (κ Ω d R M s Vproper : ℝ) : ℝ :=
  (κ * M / R) * (diamondVolume Ω d R - s * Vproper)

/-- **Cosmological constant** `Λ = (d-1)(d-2)/(2M)`, `M = L²` (dS, `Λ > 0`) or `M = −L²` (AdS,
`Λ < 0`). -/
def cosmoConstant (d M : ℝ) : ℝ := (d - 1) * (d - 2) / (2 * M)

/-! ## §B — the (A)dS Smarr formula and its structural cancellation -/

/-- **The (A)dS Smarr formula, structural form** `(d-2)κA = (d-1)κk V_R + 2 V_ζ Λ`, proved with the
proper volume `V` and the factor `s` as *free* reals and the cosmological scale `M ≠ 0`: the
`(d-1)κ·((d-2)s/R)·V` term and the `−s·V` piece of `V_ζ` cancel, and `M` cancels between `V_ζ` and `Λ`,
leaving `(d-2)κ·Ω R^{d-2}`. This is the explicit check of Eq. 3.16 announced in the paper. -/
theorem adsSmarr_general (κ Ω d R M s V : ℝ) (hR : 0 < R) (hM : M ≠ 0) (hd1 : d - 1 ≠ 0) :
    (d - 2) * κ * (Ω * R ^ (d - 2))
      = (d - 1) * κ * ((d - 2) * s / R) * V
        + 2 * ((κ * M / R) * (Ω * R ^ (d - 1) / (d - 1) - s * V)) * ((d - 1) * (d - 2) / (2 * M)) := by
  have hkey : R ^ (d - 1) = R ^ (d - 2) * R := by
    have h := Real.rpow_add hR (d - 2) 1
    rw [Real.rpow_one] at h
    rw [show d - 1 = (d - 2) + 1 by ring]; exact h
  rw [hkey]
  field_simp
  ring

/-- **The de Sitter Smarr formula** with the named geometric quantities `A`, `k`, `V_ζ`, `Λ`
(`M = L²`, `s = √(1−(R/L)²)`). -/
theorem adsSmarr (κ Ω d R L Vproper : ℝ) (hR : 0 < R) (hL : L ≠ 0) (hd1 : d - 1 ≠ 0) :
    (d - 2) * κ * diamondArea Ω d R
      = (d - 1) * κ * adsExtrinsicK d R (sqrtFactor L R) * Vproper
        + 2 * thermoVolumeAdS κ Ω d R (L ^ 2) (sqrtFactor L R) Vproper * cosmoConstant d (L ^ 2) := by
  unfold diamondArea adsExtrinsicK thermoVolumeAdS cosmoConstant diamondVolume
  exact adsSmarr_general κ Ω d R (L ^ 2) (sqrtFactor L R) Vproper hR (pow_ne_zero 2 hL) hd1

/-- **The anti-de Sitter Smarr formula** (`M = −L²`, `Λ < 0`): the same identity, with the
cosmological scale of the opposite sign. -/
theorem adsSmarr_AdS (κ Ω d R L Vproper : ℝ) (hR : 0 < R) (hL : L ≠ 0) (hd1 : d - 1 ≠ 0) :
    (d - 2) * κ * diamondArea Ω d R
      = (d - 1) * κ * adsExtrinsicK d R (sqrtFactor L R) * Vproper
        + 2 * thermoVolumeAdS κ Ω d R (-(L ^ 2)) (sqrtFactor L R) Vproper *
            cosmoConstant d (-(L ^ 2)) := by
  unfold diamondArea adsExtrinsicK thermoVolumeAdS cosmoConstant diamondVolume
  exact adsSmarr_general κ Ω d R (-(L ^ 2)) (sqrtFactor L R) Vproper hR
    (neg_ne_zero.mpr (pow_ne_zero 2 hL)) hd1

/-! ## §C — limiting cases: static patch (`R = L`) and flat (`s = 1`) -/

/-- **The relativistic factor vanishes at the de Sitter horizon** `R = L`: `√(1 − (L/L)²) = 0`. -/
@[simp] theorem sqrtFactor_staticPatch (L : ℝ) (hL : L ≠ 0) : sqrtFactor L L = 0 := by
  unfold sqrtFactor
  rw [div_self hL]
  norm_num

/-- **The extrinsic curvature vanishes on the de Sitter static patch** `R = L` (Jacobson–Visser Sec.
5.1): `k = 0`, so the Smarr formula reduces to `(d-2)κA = 2 V_ζ Λ` — the static patch is a true
Killing horizon. Recovers `CausalDiamondThermodynamics.deSitter_smarr`. -/
theorem adsExtrinsicK_staticPatch (d L : ℝ) (hL : L ≠ 0) :
    adsExtrinsicK d L (sqrtFactor L L) = 0 := by
  unfold adsExtrinsicK
  rw [sqrtFactor_staticPatch L hL]
  ring

/-- **Flat-limit consistency** `s = 1`: the (A)dS extrinsic curvature reduces to the flat
`CausalDiamond.Area.extrinsicK d R = (d-2)/R`. -/
theorem adsExtrinsicK_flat (d R : ℝ) : adsExtrinsicK d R 1 = extrinsicK d R := by
  unfold adsExtrinsicK extrinsicK
  ring

/-! ## §D — Smarr on the constructed diamond's edge `∂Σ` -/

/-- **(A)dS Smarr on the constructed diamond**: the de Sitter Smarr formula, with every quantity
evaluated at the area radius `R = edgeRadius (iR)` read off the constructed edge `∂Σ`
(`CausalDiamond.Construction`). -/
theorem constructed_adsSmarr (κ Ω d R L Vproper : ℝ) (hR : 0 < R) (hL : L ≠ 0) (hd1 : d - 1 ≠ 0) :
    (d - 2) * κ * diamondArea Ω d (edgeRadius (Complex.I * (R : ℂ)))
      = (d - 1) * κ * adsExtrinsicK d (edgeRadius (Complex.I * (R : ℂ))) (sqrtFactor L R) * Vproper
        + 2 * thermoVolumeAdS κ Ω d (edgeRadius (Complex.I * (R : ℂ))) (L ^ 2) (sqrtFactor L R) Vproper
            * cosmoConstant d (L ^ 2) := by
  rw [canonical_edgeRadius]
  exact adsSmarr κ Ω d R L Vproper hR hL hd1

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdS

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Physlib.Relativity.SemiClassical.HawkingTemperature
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits

/-!
# Thermodynamics of causal diamonds in (A)dS (Jacobson–Visser)

Formalizes the thermodynamic skeleton of Jacobson & Visser, *Gravitational Thermodynamics of Causal
Diamonds in (A)dS* (arXiv:1812.01596). A causal diamond in a maximally symmetric space behaves as a
thermodynamic equilibrium state under gravitational perturbations. Its area `A` is a function of the
spatial volume `V` and the cosmological constant `Λ` alone, with the anisotropic scaling

  `A(λ^{d-1} V, λ^{-2} Λ) = λ^{d-2} A(V, Λ)`

(area scales as length`^{d-2}`, volume as length`^{d-1}`, `Λ` as length`^{-2}`).

## §A — Smarr formula and first law from Euler's theorem

The paper derives the **first law** (Eq 3.22) by comparing the **Smarr formula** (Eq 3.16, from Wald's
Noether-charge method) with **Euler's homogeneous-function theorem** applied to the scaling above
(Eq 3.20). We formalize that calculus core: `aniso_euler` is the anisotropic Euler theorem (the
`t`-derivative of the dilation orbit at `t = 1`), and it yields directly

  `(d-2) A = (d-1) V (∂A/∂V) − 2 Λ (∂A/∂Λ)`   (Euler, `causalDiamond_euler`),
  `(d-2) κ A = (d-1) κ k V + 2 V_ζ Λ`          (Smarr, `causalDiamond_smarr`),
  `κ δA = κ k δV − V_ζ δΛ`                       (first law, `causalDiamond_firstLaw`),

with the identifications `k = ∂A/∂V` (extrinsic-curvature trace of `∂Σ`) and `V_ζ = −κ ∂A/∂Λ`
(thermodynamic volume), Eq 3.21.

## §B — Negative temperature (Eq 4.1–4.3)

The first law reads `δH_ζ = −(κ/8πG) δA`. Identifying the right side with `T δS_BH` for the
Bekenstein–Hawking entropy `S_BH = A/4ℏG` forces a **negative temperature** `T = −T_H = −ℏκ/2π`,
because increasing the conformal Killing energy *decreases* the horizon area. We build this on the
existing `hawkingTemperature` and `bekensteinTauEnt` (= `A/4ℓ_P²`, the entropy in nats): `T = −T_H`
(`diamondTemperature`), it is negative for positive surface gravity (`diamondTemperature_neg`), and the
first law `δH_ζ = T δS_BH` holds exactly (`firstLaw_negTemp`). This is the gravitational face of the
entropic-time / complex-action thermal arc, in its inverted-temperature regime.

## §C — de Sitter static patch (Sec 5.1)

At the cosmological horizon of de Sitter space the extrinsic-curvature trace `k = ∂A/∂V` vanishes, so
the Smarr formula and first law reduce to `(d-2) κ A = 2 V_ζ Λ` and `κ δA = −V_ζ δΛ`.

## References

* T. Jacobson, M. Visser, arXiv:1812.01596. This development: `HawkingTemperature`,
  `BekensteinJacobsonEntropicBits` (Bekenstein 1973, Jacobson 1995).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Set Filter Topology
open Physlib.Thermodynamics

namespace Physlib.Relativity.SemiClassical.CausalDiamondThermodynamics

/-! ## §A — the anisotropic Euler theorem and the first law -/

/-- **The anisotropic Euler theorem.** If `A : ℝ² → ℝ` is differentiable at `(V, Λ)` and homogeneous of
weights `(a, b)` and degree `c` near `t = 1`, i.e. `A(tᵃ V, t^b Λ) = t^c A(V,Λ)` for `t` near `1`, then
its partial derivatives `A_V = L(1,0)` and `A_Λ = L(0,1)` satisfy `a V A_V + b Λ A_Λ = c A(V,Λ)`. This
is the `t`-derivative of the dilation orbit at `t = 1` (chain rule = homogeneity). -/
theorem aniso_euler {A : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {V lam a b c A0 : ℝ}
    (hA : HasFDerivAt A L (V, lam)) (hA0 : A (V, lam) = A0)
    (hhom : (fun t : ℝ => A (t ^ a * V, t ^ b * lam)) =ᶠ[𝓝 1] fun t : ℝ => t ^ c * A0) :
    a * V * L (1, 0) + b * lam * L (0, 1) = c * A0 := by
  -- the dilation path `q t = (tᵃ V, t^b Λ)` and its derivative at `t = 1`
  have hq1 : HasDerivAt (fun t : ℝ => t ^ a * V) (a * V) 1 := by
    have h := (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := a) (Or.inl one_ne_zero)).mul_const V
    simpa [Real.one_rpow] using h
  have hq2 : HasDerivAt (fun t : ℝ => t ^ b * lam) (b * lam) 1 := by
    have h := (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := b) (Or.inl one_ne_zero)).mul_const lam
    simpa [Real.one_rpow] using h
  have hq : HasDerivAt (fun t : ℝ => (t ^ a * V, t ^ b * lam)) ((a * V, b * lam) : ℝ × ℝ) 1 :=
    hq1.prodMk hq2
  -- `A` is differentiable at `q 1 = (V, Λ)`
  have hAq : HasFDerivAt A L ((1 : ℝ) ^ a * V, (1 : ℝ) ^ b * lam) := by
    rw [Real.one_rpow, Real.one_rpow, one_mul, one_mul]; exact hA
  have hcomp : HasDerivAt (fun t : ℝ => A (t ^ a * V, t ^ b * lam)) (L (a * V, b * lam)) 1 :=
    hAq.comp_hasDerivAt 1 hq
  -- the homogeneous side `t^c A₀` and uniqueness of the derivative
  have hrhs : HasDerivAt (fun t : ℝ => t ^ c * A0) (c * A0) 1 := by
    have h := (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := c) (Or.inl one_ne_zero)).mul_const A0
    simpa [Real.one_rpow] using h
  have huniq : c * A0 = L (a * V, b * lam) :=
    hrhs.unique (hcomp.congr_of_eventuallyEq hhom.symm)
  -- expand `L` by linearity
  have hsplit : ((a * V, b * lam) : ℝ × ℝ)
      = (a * V) • ((1 : ℝ), (0 : ℝ)) + (b * lam) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at huniq
  linarith [huniq]

/-- **Euler relation for causal diamonds** (Eq 3.20): `(d−2) A = (d−1) V A_V − 2 Λ A_Λ`, from the
`(d-1, −2, d-2)` scaling `A(t^{d-1} V, t^{-2} Λ) = t^{d-2} A(V,Λ)`. -/
theorem causalDiamond_euler {A : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {V lam A0 : ℝ} (d : ℝ)
    (hA : HasFDerivAt A L (V, lam)) (hA0 : A (V, lam) = A0)
    (hhom : ∀ t : ℝ, 0 < t → A (t ^ (d - 1) * V, t ^ (-2 : ℝ) * lam) = t ^ (d - 2) * A0) :
    (d - 1) * V * L (1, 0) - 2 * lam * L (0, 1) = (d - 2) * A0 := by
  have hmem : Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ) := isOpen_Ioi.mem_nhds (by norm_num)
  have hev : (fun t : ℝ => A (t ^ (d - 1) * V, t ^ (-2 : ℝ) * lam))
      =ᶠ[𝓝 1] fun t : ℝ => t ^ (d - 2) * A0 :=
    eventually_of_mem hmem (fun t ht => hhom t ht)
  have h := aniso_euler (a := d - 1) (b := -2) (c := d - 2) hA hA0 hev
  linarith [h]

/-- **The first law of causal diamonds** (Eq 3.22): `κ δA = κ k δV − V_ζ δΛ`, where the area variation
is `δA = A_V δV + A_Λ δΛ`, `k = A_V`, and `V_ζ = −κ A_Λ`. Pure linearity of the differential — no
homogeneity needed. -/
theorem causalDiamond_firstLaw {A : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {V lam : ℝ}
    (_hA : HasFDerivAt A L (V, lam)) (κ δV δΛ : ℝ) :
    κ * L (δV, δΛ) = κ * L (1, 0) * δV - (-κ * L (0, 1)) * δΛ := by
  have hsplit : ((δV, δΛ) : ℝ × ℝ)
      = δV • ((1 : ℝ), (0 : ℝ)) + δΛ • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The Smarr formula for causal diamonds** (Eq 3.16): `(d−2) κ A = (d−1) κ k V + 2 V_ζ Λ`, with
`k = A_V` and `V_ζ = −κ A_Λ`. Obtained from the Euler relation by multiplying by `κ`. -/
theorem causalDiamond_smarr {A : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {V lam A0 : ℝ} (d κ : ℝ)
    (hA : HasFDerivAt A L (V, lam)) (hA0 : A (V, lam) = A0)
    (hhom : ∀ t : ℝ, 0 < t → A (t ^ (d - 1) * V, t ^ (-2 : ℝ) * lam) = t ^ (d - 2) * A0) :
    (d - 2) * κ * A0 = (d - 1) * κ * L (1, 0) * V + 2 * (-κ * L (0, 1)) * lam := by
  have h := causalDiamond_euler d hA hA0 hhom
  -- `(d-2) A = (d-1) V A_V - 2 Λ A_Λ`; multiply by `κ`
  have : κ * ((d - 1) * V * L (1, 0) - 2 * lam * L (0, 1)) = κ * ((d - 2) * A0) := by rw [h]
  nlinarith [this]

/-! ## §B — negative temperature (using `hawkingTemperature` and `bekensteinTauEnt`) -/

/-- **The (negative) temperature of a causal diamond** `T = −T_H = −ℏκ/2π` (Eq 4.2). Built on the
existing `hawkingTemperature`. -/
def diamondTemperature (ℏ κ c kB : ℝ) : ℝ := -hawkingTemperature ℏ κ c kB

@[simp] theorem diamondTemperature_def (ℏ κ c kB : ℝ) :
    diamondTemperature ℏ κ c kB = -(ℏ * κ / (2 * Real.pi * c * kB)) := by
  rw [diamondTemperature, hawkingTemperature_def]

/-- **The diamond temperature is minus the Hawking temperature** (Eq 4.2): `T + T_H = 0`. -/
theorem diamondTemperature_add_hawking (ℏ κ c kB : ℝ) :
    diamondTemperature ℏ κ c kB + hawkingTemperature ℏ κ c kB = 0 := by
  rw [diamondTemperature]; ring

/-- **The diamond temperature is negative** for positive surface gravity — the hallmark of the causal
diamond (vs the positive Hawking temperature). -/
theorem diamondTemperature_neg
    (ℏ κ c kB : ℝ) (hℏ : 0 < ℏ) (hκ : 0 < κ) (hc : 0 < c) (hkB : 0 < kB) :
    diamondTemperature ℏ κ c kB < 0 := by
  rw [diamondTemperature]
  exact neg_neg_iff_pos.mpr (hawkingTemperature_pos ℏ κ c kB hℏ hκ hc hkB)

/-- **The Bekenstein–Hawking entropy in `ℏ, G` form** `S_BH = A/(4ℏG)`, recovered from the existing
`bekensteinTauEnt A ℓ_P = A/(4ℓ_P²)` via the Planck length `ℓ_P² = ℏG`. -/
theorem bekensteinTauEnt_eq_over_hbarG (A ℏ G ℓP : ℝ) (hℓ : ℓP ^ 2 = ℏ * G) :
    bekensteinTauEnt A ℓP = A / (4 * ℏ * G) := by
  rw [bekensteinTauEnt, hℓ]; ring

/-- **The first law of causal diamonds as a negative-temperature relation** (Eq 4.3):
`δH_ζ = −(κ/8πG) δA = T δS_BH`, with `T = −ℏκ/2π` the diamond temperature and `δS_BH = δA/(4ℏG)` the
Bekenstein–Hawking entropy variation (`= bekensteinTauEnt δA ℓ_P` at `ℓ_P² = ℏG`). The `ℏ` cancels,
recovering the geometric Hamiltonian variation with the correct (negative) sign. -/
theorem firstLaw_negTemp (ℏ κ G δA ℓP : ℝ) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hℓ : ℓP ^ 2 = ℏ * G) :
    -(κ * δA) / (8 * Real.pi * G) = diamondTemperature ℏ κ 1 1 * bekensteinTauEnt δA ℓP := by
  rw [diamondTemperature_def, bekensteinTauEnt_eq_over_hbarG δA ℏ G ℓP hℓ]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## §C — de Sitter static patch (`k = 0`) -/

/-- **Smarr formula at the de Sitter cosmological horizon** (Sec 5.1): with `k = A_V = 0` the area–`Λ`
relation `(d−2) κ A = 2 V_ζ Λ` holds. -/
theorem deSitter_smarr {A : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {V lam A0 : ℝ} (d κ : ℝ)
    (hA : HasFDerivAt A L (V, lam)) (hA0 : A (V, lam) = A0)
    (hhom : ∀ t : ℝ, 0 < t → A (t ^ (d - 1) * V, t ^ (-2 : ℝ) * lam) = t ^ (d - 2) * A0)
    (hk : L (1, 0) = 0) :
    (d - 2) * κ * A0 = 2 * (-κ * L (0, 1)) * lam := by
  have h := causalDiamond_smarr d κ hA hA0 hhom
  rw [hk] at h
  simpa using h

/-- **First law at the de Sitter cosmological horizon** (Sec 5.1): with `k = A_V = 0` the first law
reduces to `κ δA = −V_ζ δΛ` — the variation of area is purely the cosmological-constant term. -/
theorem deSitter_firstLaw {A : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {V lam : ℝ}
    (hA : HasFDerivAt A L (V, lam)) (κ δV δΛ : ℝ) (hk : L (1, 0) = 0) :
    κ * L (δV, δΛ) = -(-κ * L (0, 1)) * δΛ := by
  have h := causalDiamond_firstLaw hA κ δV δΛ
  rw [hk] at h
  simpa using h

end Physlib.Relativity.SemiClassical.CausalDiamondThermodynamics

end

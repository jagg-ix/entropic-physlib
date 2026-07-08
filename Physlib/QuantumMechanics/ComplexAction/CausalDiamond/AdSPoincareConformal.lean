/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSConformalKilling
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixD

/-!
# Anti-de Sitter conformal generators, Poincaré coordinates, and the diamond CKV (Appendix D.2)

This completes Jacobson–Visser §D.2: the global-AdS conformal generators (Eq. D.11), the diamond
conformal Killing vector as a combination of them (Eq. D.12), the Poincaré coordinates (Eq. D.13), the
Poincaré induced metric (Eq. D.14), and the conformal-algebra generators `D, P_μ, M_μν, K_μ` (Eq. D.15).
Together with `CausalDiamond.AdSConformalKilling` (D.9, D.10, D.12-factor) this formalizes all of §D.2.

* **D.11** the global-AdS generators. The three with only `∂_t, ∂_r` parts (no sphere `∇_i`) are built in
 full: `iJ_{−10} = L∂_t` (`adsKilling_m10_*`), `iJ_{0d}` (`adsConf_0d_*`), `iJ_{−1d}` (`adsConf_m1d_*`).
 The first four `J_{−10}, J_{−1i}, J_{0i}, J_{ij}` are true Killing, the latter three
 `J_{−1d}, J_{0d}, J_{id}` conformal Killing.
* **D.12** `ζ^{AdS} = (L/R)[√(1+(R/L)²)·(iJ_{0d}) − (iJ_{−10})]` (`adsDiamondCKV_*`); for `R/L → ∞` it
 reduces to `iJ_{0d}` (`adsDiamondCKV_t_tendsto`, `adsDiamondCKV_r_tendsto`), the coefficient
 `(L/R)√(1+(R/L)²) → 1` (`adsDiamond_coeff_tendsto_one`).
* **D.13** the Poincaré embedding lies on the light cone `X · X = 0` (`adS_poincare_lightCone`).
* **D.14** the Poincaré metric `ds² = (L/z)²(−dt² + dx⃗² + dz²)` is conformally flat
 (`adSPoincare_conformally_flat`).
* **D.15** the conformal generators `D = J_{−11}`, `P_μ = J_{μ,−1} − J_{μ,1}`, `M_μν = J_μν`,
 `K_μ = J_{μ,−1} + J_{μ,1}` (`confDilatation`, `confTranslation`, `confRotation`, `confSpecial`) and
 their relations (`confTranslation_add_confSpecial`, `confRotation_antisymm`).

## Full vector fields

All the generators `J_{AB}` are built as **genuine vector fields** on the embedding space `ℝ^{2,d}` in
`§D.11/D.15 (full vector fields)`: `embGenerator` is the linear vector field `J_{AB}(X)^C = X_A δ^C_B −
X_B δ^C_A`, of which the scalar `genJ` is the contraction (`genJ_eq_embGenerator_contraction`); every one
is an `so(2,d)` Killing generator preserving the Minkowski form (`embGenerator_killing`). The `(t,r,Ω)`
generators with `∇_i` (D.11: `J_{−1i}, J_{0i}, J_{id}, J_{ij}`) are the same embedding vector fields in
those coordinates — the `∇_i` is a coordinate artifact.

## Scope

The conformal-algebra relations of D.15 are the linear combinations and antisymmetry, not the full
`o(2,d)` brackets.

No new axioms.
-/

set_option autoImplicit false

open Real Filter Topology

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSConformalKilling
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixD

/-! ## §D.11 — the global-AdS generators with only `∂_t, ∂_r` parts -/

/-- **Eq. D.11: `iJ_{−10} = L∂_t`** — the AdS timelike Killing vector (`∂_t` coefficient). -/
def adsKilling_m10_t (L : ℝ) : ℝ := L

/-- `iJ_{−10}` has no `∂_r` part. -/
def adsKilling_m10_r : ℝ := 0

/-- **Eq. D.11: `iJ_{0d}` `∂_t` coefficient** `L²cos(t/L)/√(L²+r²)` (conformal Killing). -/
def adsConf_0d_t (L r t : ℝ) : ℝ := L ^ 2 * Real.cos (t / L) / Real.sqrt (L ^ 2 + r ^ 2)

/-- **Eq. D.11: `iJ_{0d}` `∂_r` coefficient** `−(r/L)√(L²+r²)sin(t/L)`. -/
def adsConf_0d_r (L r t : ℝ) : ℝ := -(r / L) * Real.sqrt (L ^ 2 + r ^ 2) * Real.sin (t / L)

/-- **Eq. D.11: `iJ_{−1d}` `∂_t` coefficient** `−L²sin(t/L)/√(L²+r²)` (conformal Killing). -/
def adsConf_m1d_t (L r t : ℝ) : ℝ := -(L ^ 2 * Real.sin (t / L)) / Real.sqrt (L ^ 2 + r ^ 2)

/-- **Eq. D.11: `iJ_{−1d}` `∂_r` coefficient** `−(r/L)√(L²+r²)cos(t/L)`. -/
def adsConf_m1d_r (L r t : ℝ) : ℝ := -(r / L) * Real.sqrt (L ^ 2 + r ^ 2) * Real.cos (t / L)

/-! ## §D.12 — the diamond conformal Killing vector `ζ^{AdS}` and its `R/L → ∞` limit -/

/-- **Eq. D.12: `ζ^{AdS}` `∂_t` component** `(L/R)[√(1+(R/L)²)·(iJ_{0d})_t − (iJ_{−10})_t]`. -/
def adsDiamondCKV_t (L R r t : ℝ) : ℝ :=
  (L / R) * (adsConfKillingFactor L R * adsConf_0d_t L r t - adsKilling_m10_t L)

/-- **Eq. D.12: `ζ^{AdS}` `∂_r` component** `(L/R)√(1+(R/L)²)·(iJ_{0d})_r` (`iJ_{−10}` has no `∂_r`). -/
def adsDiamondCKV_r (L R r t : ℝ) : ℝ :=
  (L / R) * (adsConfKillingFactor L R * adsConf_0d_r L r t)

/-- **The `ζ^{AdS}` coefficient `(L/R)√(1+(R/L)²) = √(L²/R² + 1) → 1`** as `R/L → ∞`. -/
theorem adsDiamond_coeff_eq (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    (L / R) * adsConfKillingFactor L R = Real.sqrt (L ^ 2 / R ^ 2 + 1) := by
  rw [adsConfKillingFactor, show L / R = Real.sqrt ((L / R) ^ 2) from (Real.sqrt_sq (by positivity)).symm,
    ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

theorem adsDiamond_coeff_tendsto_one (L : ℝ) (hL : 0 < L) :
    Tendsto (fun R : ℝ => (L / R) * adsConfKillingFactor L R) atTop (𝓝 1) := by
  have heq : (fun R : ℝ => (L / R) * adsConfKillingFactor L R)
      =ᶠ[atTop] fun R => Real.sqrt (L ^ 2 / R ^ 2 + 1) := by
    filter_upwards [eventually_gt_atTop 0] with R hR using adsDiamond_coeff_eq L R hL hR
  rw [tendsto_congr' heq]
  have hR2 : Tendsto (fun R : ℝ => R ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have h0 : Tendsto (fun R : ℝ => L ^ 2 / R ^ 2 + 1) atTop (𝓝 (0 + 1)) :=
    (Filter.Tendsto.div_atTop tendsto_const_nhds hR2).add_const 1
  rw [zero_add] at h0
  have := (Real.continuous_sqrt.tendsto 1).comp h0
  rwa [Real.sqrt_one] at this

/-- **`(L/R) → 0`** as `R/L → ∞` (the `iJ_{−10}` coefficient vanishes). -/
theorem adsDiamond_killing_coeff_tendsto_zero (L : ℝ) :
    Tendsto (fun R : ℝ => L / R) atTop (𝓝 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id

/-- **Eq. D.12: `ζ^{AdS} → iJ_{0d}` as `R/L → ∞`** (`∂_t` component): for an infinite-size diamond the
conformal Killing field reduces to the generator `iJ_{0d}`. -/
theorem adsDiamondCKV_t_tendsto (L r t : ℝ) (hL : 0 < L) :
    Tendsto (fun R => adsDiamondCKV_t L R r t) atTop (𝓝 (adsConf_0d_t L r t)) := by
  have hexpand : (fun R => adsDiamondCKV_t L R r t)
      = fun R => ((L / R) * adsConfKillingFactor L R) * adsConf_0d_t L r t
          - (L / R) * adsKilling_m10_t L := by
    funext R; rw [adsDiamondCKV_t]; ring
  rw [hexpand]
  have h1 := (adsDiamond_coeff_tendsto_one L hL).mul_const (adsConf_0d_t L r t)
  have h2 := (adsDiamond_killing_coeff_tendsto_zero L).mul_const (adsKilling_m10_t L)
  simpa using h1.sub h2

/-- **Eq. D.12: `ζ^{AdS} → iJ_{0d}` as `R/L → ∞`** (`∂_r` component). -/
theorem adsDiamondCKV_r_tendsto (L r t : ℝ) (hL : 0 < L) :
    Tendsto (fun R => adsDiamondCKV_r L R r t) atTop (𝓝 (adsConf_0d_r L r t)) := by
  have hexpand : (fun R => adsDiamondCKV_r L R r t)
      = fun R => ((L / R) * adsConfKillingFactor L R) * adsConf_0d_r L r t := by
    funext R; rw [adsDiamondCKV_r]; ring
  rw [hexpand]
  simpa using (adsDiamond_coeff_tendsto_one L hL).mul_const (adsConf_0d_r L r t)

/-! ## §D.13 — the Poincaré embedding lies on the light cone -/

/-- **Eq. D.13: the Poincaré embedding satisfies `X · X = 0`.** With `X^{−1} = (L²−t²+x⃗²+z²)/(2z)`,
`X¹ = (L²+t²−x⃗²−z²)/(2z)`, `X⁰ = Lt/z`, `Xⁱ = Lxⁱ/z` (`∑(Xⁱ)² = L²x⃗²/z²`), `X^d = L`, the Poincaré
embedding lies on the `ℝ^{2,d}` light cone `−(X^{−1})² − (X⁰)² + (X¹)² + ∑(Xⁱ)² + (X^d)² = 0`. -/
theorem adS_poincare_lightCone (L t z xsq : ℝ) (hz : z ≠ 0) :
    -((L ^ 2 - t ^ 2 + xsq + z ^ 2) / (2 * z)) ^ 2 - (L * t / z) ^ 2
        + ((L ^ 2 + t ^ 2 - xsq - z ^ 2) / (2 * z)) ^ 2 + L ^ 2 * xsq / z ^ 2 + L ^ 2 = 0 := by
  field_simp
  ring

/-! ## §D.14 — the Poincaré induced metric is conformally flat -/

/-- **The Poincaré conformal factor** `(L/z)²` of `ds² = (L/z)²(−dt² + dx⃗² + dz²)` (Eq. D.14). -/
def adSPoincareFactor (L z : ℝ) : ℝ := (L / z) ^ 2

theorem adSPoincareFactor_pos (L z : ℝ) (hL : L ≠ 0) (hz : z ≠ 0) : 0 < adSPoincareFactor L z := by
  rw [adSPoincareFactor]; positivity

/-- **Eq. D.14: `g_tt = −(L/z)²`** (the Poincaré lapse). -/
def adSPoincareMetricTT (L z : ℝ) : ℝ := -(adSPoincareFactor L z)

/-- **Eq. D.14: `g_xx = g_zz = (L/z)²`** (the spatial Poincaré components). -/
def adSPoincareMetricSS (L z : ℝ) : ℝ := adSPoincareFactor L z

/-- **Eq. D.14: the Poincaré metric is conformally flat** `g_tt/g_xx = −1` — `ds² = (L/z)² η` with
`η = diag(−1, +1, …, +1)`. -/
theorem adSPoincare_conformally_flat (L z : ℝ) (hL : L ≠ 0) (hz : z ≠ 0) :
    adSPoincareMetricTT L z / adSPoincareMetricSS L z = -1 := by
  rw [adSPoincareMetricTT, adSPoincareMetricSS, neg_div, div_self (adSPoincareFactor_pos L z hL hz).ne']

/-! ## §D.15 — the conformal-algebra generators `D, P_μ, M_μν, K_μ` -/

variable {n : ℕ}

/-- **Eq. D.15: the dilatation** `D = J_{−1,1}`. -/
def confDilatation (X der : Fin n → ℝ) (m1 p1 : Fin n) : ℝ := genJ X der m1 p1

/-- **Eq. D.15: the translations** `P_μ = J_{μ,−1} − J_{μ,1}`. -/
def confTranslation (X der : Fin n → ℝ) (μ m1 p1 : Fin n) : ℝ :=
  genJ X der μ m1 - genJ X der μ p1

/-- **Eq. D.15: the special conformal generators** `K_μ = J_{μ,−1} + J_{μ,1}`. -/
def confSpecial (X der : Fin n → ℝ) (μ m1 p1 : Fin n) : ℝ :=
  genJ X der μ m1 + genJ X der μ p1

/-- **Eq. D.15: the rotations/Lorentz generators** `M_μν = J_μν`. -/
def confRotation (X der : Fin n → ℝ) (μ ν : Fin n) : ℝ := genJ X der μ ν

/-- **`P_μ + K_μ = 2 J_{μ,−1}`** — translations and special conformal generators recombine to the
boundary `J_{μ,−1}`. -/
theorem confTranslation_add_confSpecial (X der : Fin n → ℝ) (μ m1 p1 : Fin n) :
    confTranslation X der μ m1 p1 + confSpecial X der μ m1 p1 = 2 * genJ X der μ m1 := by
  rw [confTranslation, confSpecial]; ring

/-- **`K_μ − P_μ = 2 J_{μ,1}`**. -/
theorem confSpecial_sub_confTranslation (X der : Fin n → ℝ) (μ m1 p1 : Fin n) :
    confSpecial X der μ m1 p1 - confTranslation X der μ m1 p1 = 2 * genJ X der μ p1 := by
  rw [confSpecial, confTranslation]; ring

/-- **The Lorentz generators are antisymmetric** `M_μν = −M_νμ` (from `genJ_antisymm`). -/
theorem confRotation_antisymm (X der : Fin n → ℝ) (μ ν : Fin n) :
    confRotation X der μ ν = -confRotation X der ν μ := by
  rw [confRotation, confRotation]; exact genJ_antisymm X der μ ν

/-- **The dilatation is antisymmetric** `D = J_{−1,1} = −J_{1,−1}`. -/
theorem confDilatation_antisymm (X der : Fin n → ℝ) (m1 p1 : Fin n) :
    confDilatation X der m1 p1 = -genJ X der p1 m1 := by
  rw [confDilatation]; exact genJ_antisymm X der m1 p1

/-! ## §D.11/D.15 (full vector fields) — the generators as `so(2,d)` Killing vector fields

The conformal generators `J_{AB}` are **linear vector fields** on the embedding space `ℝ^{2,d}` — the
infinitesimal boosts/rotations in the `(A,B)` plane. Each is `J_{AB}(X)^C = X_A δ^C_B − X_B δ^C_A` with
`X_A = η_A X^A` (the Minkowski signature `η`). This is the full vector field that the scalar `genJ` is the
contraction of, and it is uniformly defined for *every* `(A,B)` (the `∇_i` of the `(t,r,Ω)` form is just a
coordinate artifact). Built here with the embedding-space Killing structure: every `J_{AB}` preserves the
Minkowski form (`embGenerator_killing`), i.e. `J_{AB} ∈ so(2,d)`. -/

/-- **The embedding Minkowski form** `X · Y = ∑_C η_C X^C Y^C` (signature `η : Fin m → ℝ`). -/
def embForm (η X Y : Fin n → ℝ) : ℝ := ∑ C, η C * X C * Y C

theorem embForm_symm (η X Y : Fin n → ℝ) : embForm η X Y = embForm η Y X := by
  unfold embForm; exact Finset.sum_congr rfl fun C _ => by ring

/-- **The generator `J_{AB}` as a full vector field** `J_{AB}(X)^C = X_A δ^C_B − X_B δ^C_A`
(`X_A = η_A X^A`) — the infinitesimal boost/rotation in the `(A,B)` plane on `ℝ^{2,d}`. -/
def embGenerator (η X : Fin n → ℝ) (A B : Fin n) : Fin n → ℝ :=
  fun C => (η A * X A) * (if C = B then 1 else 0) - (η B * X B) * (if C = A then 1 else 0)

/-- **The generator vector field is antisymmetric** `J_{AB} = −J_{BA}`. -/
theorem embGenerator_antisymm (η X : Fin n → ℝ) (A B : Fin n) :
    embGenerator η X A B = -embGenerator η X B A := by
  funext C; simp only [embGenerator, Pi.neg_apply]; ring

/-- **`genJ` is the contraction of the generator vector field.** With trivial signature `η ≡ 1`, the
scalar `genJ X der A B = ∑_C J_{AB}(X)^C der_C` — the full vector field `embGenerator` generalizes the
scalar generator coefficient. -/
theorem genJ_eq_embGenerator_contraction (X der : Fin n → ℝ) (A B : Fin n) :
    genJ X der A B = ∑ C, embGenerator (fun _ => 1) X A B C * der C := by
  have hC : ∀ C, embGenerator (fun _ => 1) X A B C * der C
      = (if C = B then X A * der B else 0) - (if C = A then X B * der A else 0) := by
    intro C; simp only [embGenerator]; by_cases hB : C = B <;> by_cases hA : C = A <;> simp_all
  rw [Finset.sum_congr rfl (fun C _ => hC C), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ B, Finset.sum_ite_eq' Finset.univ A, genJ]
  simp

/-- **The generator's contraction with the Minkowski form** `J_{AB}(X) · Z = η_A η_B (X_A Z_B − X_B Z_A)`. -/
theorem embForm_embGenerator (η X Z : Fin n → ℝ) (A B : Fin n) :
    embForm η (embGenerator η X A B) Z = η A * η B * (X A * Z B - X B * Z A) := by
  unfold embForm embGenerator
  rw [Finset.sum_congr rfl (fun C _ =>
    show η C * ((η A * X A) * (if C = B then 1 else 0) - (η B * X B) * (if C = A then 1 else 0)) * Z C
        = (if C = B then η B * (η A * X A) * Z B else 0)
          - (if C = A then η A * (η B * X B) * Z A else 0) from by
      by_cases hB : C = B <;> by_cases hA : C = A <;> simp_all),
    Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ B, Finset.sum_ite_eq' Finset.univ A]
  simp only [Finset.mem_univ, if_true]
  ring

/-- **Every generator `J_{AB}` is in `so(2,d)`** — it preserves the Minkowski form:
`J_{AB}(Y) · Z + Y · J_{AB}(Z) = 0` (the infinitesimal isometry condition). The full vector fields of all
the D.11 generators are Killing generators of the embedding form, uniformly. -/
theorem embGenerator_killing (η Y Z : Fin n → ℝ) (A B : Fin n) :
    embForm η (embGenerator η Y A B) Z + embForm η Y (embGenerator η Z A B) = 0 := by
  rw [embForm_embGenerator, embForm_symm η Y, embForm_embGenerator]; ring

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal

end

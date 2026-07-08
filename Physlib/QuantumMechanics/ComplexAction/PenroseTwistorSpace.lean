/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere

/-!
# Penrose twistor space

Penrose twistor theory built on the Weyl-spinor / Riemann-sphere picture of
`AdSCFT.WeylSpinorPoincareSphere`. A **twistor** `Z = (ω, π) ∈ ℂ⁴ = ℂ² ⊕ ℂ²` pairs a Weyl spinor
`ω^A` with a dual Weyl spinor `π_{A'}`. Its `π`-spinor determines a point of the Riemann sphere
`CP¹ = OnePoint ℂ` — the null direction the twistor points along — via `weylRatio π = π₀/π₁`.

* **§A — twistor space and its Riemann-sphere direction.** `Twistor = (Fin 2 → ℂ) × (Fin 2 → ℂ)`;
 `twistorDirection Z = weylRatio π` (a point of `CP¹`), invariant under rescaling `Z ↦ cZ`
 (`twistorDirection_smul`) — the map from projective twistor space `ℙ𝕋` to the sphere.
* **§B — the (2,2) Hermitian norm and null twistors.** `twistorNorm Z = 2 Re⟨ω, π⟩` (the pseudo-
 Hermitian form of signature `(2,2)`); it scales as `‖c‖²` (`twistorNorm_smul`), so **nullity is
 projective** (`isNullTwistor_smul`). `IsNullTwistor Z` (`Σ(Z) = 0`) is Penrose's null twistor — a
 light ray.
* **§C — the incidence relation.** `Incident Z x` is `ω = i·x·π` for a Hermitian `x` (a Minkowski
 point as a `2×2` Hermitian matrix). The key theorem: a twistor incident to a real spacetime point is
 **null** (`incident_isNull`, `Σ = 0`) — because `π† x π` is real for Hermitian `x`, so `Σ = 2 Re(i·real) = 0`.
* **§D — the Lorentz `SL(2,ℂ)` action is the boundary Möbius action.** The `SL(2,ℂ)` transformation of
 the `π`-spinor sends the twistor direction by the boundary Möbius map (`sl2c_twistorDirection`,
 reusing `WeylSpinorPoincareSphere.sl2c_weylRatio`).

Proven: the direction and its projective invariance, the `‖c‖²` scaling of the
Hermitian norm and projective nullity, incidence ⟹ null, and the `SL(2,ℂ)` = Möbius law on the
direction. Interpretive: identifying `(ω,π)` with a Penrose twistor, `twistorNorm` with the standard
`Σ_{αβ̄}Z^α Z̄^β` of signature `(2,2)`, and `Incident` with the incidence relation `ω^A = i x^{AA'}π_{A'}`
is the standard twistor dictionary (the conformal `SU(2,2)` action is not formalized; only its `SL(2,ℂ)`
Lorentz subgroup, via the boundary action).

## References

* R. Penrose, "Twistor algebra", J. Math. Phys. 8 (1967) 345; R. Penrose, W. Rindler, *Spinors and
 Space-Time* Vol. 2. Reuses `AdSCFT.WeylSpinorPoincareSphere` (`weylRatio`, `sl2c_weylRatio`).

No new axioms.
-/

set_option autoImplicit false

open ComplexConjugate
open scoped MatrixGroups
open scoped Matrix
open OnePoint
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PenroseTwistorSpace

/-! ## §A — twistor space and its Riemann-sphere direction -/

/-- **Twistor space** `𝕋 = ℂ⁴ = ℂ² ⊕ ℂ²`: a twistor `Z = (ω, π)` is a Weyl spinor `ω` and a dual Weyl
spinor `π`. -/
abbrev Twistor : Type := (Fin 2 → ℂ) × (Fin 2 → ℂ)

/-- **The twistor's point on the Riemann sphere** `Z ↦ weylRatio π ∈ CP¹`: the null direction the
twistor points along, from its `π`-spinor. -/
noncomputable def twistorDirection (Z : Twistor) : OnePoint ℂ := weylRatio Z.2

/-- **The direction is projective** `twistorDirection (c·Z) = twistorDirection Z` for `c ≠ 0`: it
depends only on the projective class `[Z] ∈ ℙ𝕋`, giving the map `ℙ𝕋 → CP¹`. -/
theorem twistorDirection_smul {c : ℂ} (hc : c ≠ 0) (Z : Twistor) :
    twistorDirection (c • Z) = twistorDirection Z := by
  unfold twistorDirection
  exact weylRatio_smul c hc Z.2

/-! ## §B — the (2,2) Hermitian norm and null twistors -/

/-- **The twistor pairing** `⟨ω, π⟩ = Σ_A ω^A π̄_A ∈ ℂ`. -/
noncomputable def twistorPairing (Z : Twistor) : ℂ := ∑ i, Z.1 i * conj (Z.2 i)

/-- **The twistor norm** `Σ(Z) = ω^A π̄_A + π_{A'} ω̄^{A'} = 2 Re⟨ω, π⟩ ∈ ℝ`: the pseudo-Hermitian form
of signature `(2,2)` on twistor space. -/
noncomputable def twistorNorm (Z : Twistor) : ℝ := 2 * (twistorPairing Z).re

/-- **The pairing scales by `c·c̄`** `⟨cω, cπ⟩ = ‖c‖²⟨ω, π⟩`. -/
theorem twistorPairing_smul (c : ℂ) (Z : Twistor) :
    twistorPairing (c • Z) = (Complex.normSq c : ℂ) * twistorPairing Z := by
  unfold twistorPairing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← Complex.mul_conj c]
  ring

/-- **The norm scales as `‖c‖²`** `Σ(c·Z) = ‖c‖² Σ(Z)`: the Hermitian form is quadratic. -/
theorem twistorNorm_smul (c : ℂ) (Z : Twistor) :
    twistorNorm (c • Z) = Complex.normSq c * twistorNorm Z := by
  unfold twistorNorm
  rw [twistorPairing_smul, Complex.re_ofReal_mul]
  ring

/-- **A null twistor** `Σ(Z) = 0` — Penrose's null twistor, corresponding to a light ray. -/
def IsNullTwistor (Z : Twistor) : Prop := twistorNorm Z = 0

/-- **Nullity is projective** `Σ(c·Z) = 0 ↔ Σ(Z) = 0` for `c ≠ 0`: being a null twistor is a property of
the projective class `[Z]`. -/
theorem isNullTwistor_smul {c : ℂ} (hc : c ≠ 0) (Z : Twistor) :
    IsNullTwistor (c • Z) ↔ IsNullTwistor Z := by
  unfold IsNullTwistor
  rw [twistorNorm_smul, mul_eq_zero, or_iff_right (Complex.normSq_pos.mpr hc).ne']

/-! ## §C — the incidence relation -/

/-- **A twistor is incident to a spacetime point** `ω = i·x·π`, with `x` a `2×2` Hermitian matrix (a
point of Minkowski space in spinor form `x^{AA'}`). -/
def Incident (Z : Twistor) (x : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Z.1 = Complex.I • (x *ᵥ Z.2)

/-- **The Hermitian quadratic form is real** `π† x π ∈ ℝ` for `x` Hermitian: `conj Σᵢⱼ x_{ij} πⱼ π̄ᵢ =
Σᵢⱼ x_{ij} πⱼ π̄ᵢ`. -/
theorem hermitian_form_selfConj (x : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ)
    (hx : ∀ i j, x i j = conj (x j i)) :
    conj (∑ i, ∑ j, x i j * v j * conj (v i)) = ∑ i, ∑ j, x i j * v j * conj (v i) := by
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hx i j]
  ring

/-- **A twistor incident to a real spacetime point is null** `Incident Z x → Σ(Z) = 0` (for `x`
Hermitian): the twistor of a point lies on the null cone. Because `ω = i x π` gives
`Σ = 2 Re(i · π† x π)` and `π† x π` is real, so `Σ = 0`. -/
theorem incident_isNull (Z : Twistor) (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : ∀ i j, x i j = conj (x j i)) (hZ : Incident Z x) : IsNullTwistor Z := by
  unfold Incident at hZ
  have hS := hermitian_form_selfConj x Z.2 hx
  have hSim : (∑ i, ∑ j, x i j * Z.2 j * conj (Z.2 i)).im = 0 :=
    Complex.conj_eq_iff_im.mp hS
  unfold IsNullTwistor twistorNorm twistorPairing
  have hpair : (∑ i, Z.1 i * conj (Z.2 i))
      = Complex.I * ∑ i, ∑ j, x i j * Z.2 j * conj (Z.2 i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hZ]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hpair, Complex.mul_re, Complex.I_re, Complex.I_im, hSim]
  ring

/-! ## §D — the Lorentz `SL(2,ℂ)` action is the boundary Möbius action -/

/-- **The Lorentz `SL(2,ℂ)` law is the boundary Möbius action on the twistor direction**
`M • twistorDirection Z = (M₀₀π₀+M₀₁π₁)/(M₁₀π₀+M₁₁π₁)`: transforming the `π`-spinor by `M ∈ SL(2,ℂ)`
moves the twistor's Riemann-sphere point by the boundary Möbius map (`sl2c_weylRatio`). -/
theorem sl2c_twistorDirection (M : SL(2, ℂ)) (Z : Twistor) (hb : Z.2 1 ≠ 0)
    (hden : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * Z.2 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * Z.2 1 ≠ 0) :
    M.toGL • twistorDirection Z
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * Z.2 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * Z.2 1)
          / ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * Z.2 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * Z.2 1)
          : ℂ) : OnePoint ℂ) := by
  unfold twistorDirection weylRatio
  rw [if_neg hb]
  exact sl2c_weylRatio M (Z.2 0) (Z.2 1) hb hden

end Physlib.QuantumMechanics.ComplexAction.PenroseTwistorSpace

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

/-!
# The diffeomorphism variation of the metric and the Lorentz–Levi-Civita thesis

Loinger, *Proof of a Lorentz and Levi-Civita thesis* (arXiv:1109.5268), argues that the left-hand side of the
Einstein equations, `G^{jk} = R^{jk} − ½g^{jk}R`, is the genuine energy–momentum–stress tensor of the
gravitational field — because it is a *symmetric* tensor that is *covariantly conserved* as a Noether identity
of coordinate (diffeomorphism) invariance, independently of the field equations.

The rigorously algebraic kernel is §2's transformation law (Eq. 7): under the infinitesimal coordinate change
`x'^j = x^j + ε^j`, the metric varies by (minus) its **Lie derivative**,
 `δ*g_{mn} = −(L_ε g)_{mn} = −(ε^s ∂_s g_{mn} + g_{sn} ∂_m ε^s + g_{ms} ∂_n ε^s)`.
This module formalizes that law, its symmetry (which forces the conjugate variational derivative to be
symmetric), and the Killing characterization `δ*g = 0`. The variational/integral steps (Eqs. 8–13, boundary
terms) are not performed; the paper's conclusion — that `G^{jk}` is symmetric and conserved — is assembled
from the existing `einsteinTensor_symm` and `bianchi_implies_conservation`.

* `metricLieDerivative` — Eq. 7, `(L_ε g)_{mn}` from the metric `g`, its derivatives `dg` and `∂ε` (`dε`).
* `metricLieDerivative_symm`, `metricDiffeoVariation`, `metricDiffeoVariation_symm` — the diffeomorphism
 variation `δ*g = −L_ε g` and its symmetry.
* `IsKillingVector`, `metricDiffeoVariation_zero_iff_isKilling` — `δ*g = 0` iff `ε` is Killing.
* `einsteinTensor_is_thesis_tensor` — Loinger's thesis: `G^{jk}` is symmetric *and* covariantly conserved.
* `noether_conservation` — Eq. 9: `(∀ ε, ∑ᵢ (Div P)ᵢ εⁱ = 0) ⇒ Div P = 0`, the Noether identity for the
 variational derivative of *any* scalar density (arbitrariness of `ε`).
* `einsteinTensor_noether_conserved` — Eq. 13: `G^{jk}_{;k} = 0` derived from diffeomorphism invariance.
* `loinger_thesis_from_invariance` — the full thesis from invariance alone: `G` symmetric, conserved, and `T`
 conserved, with the contracted Bianchi identity *derived* rather than assumed.
* `noether_invariance_iff_secondBianchi` — the two routes to Eq. 13 agree: Noether diffeomorphism invariance
 `∀ ε, ∑ᵢ (∇G)ᵢ εⁱ = 0` **iff** the contracted second (differential) Bianchi identity `∇^μR_{μν} = ½∇_νR`
 (`LeviCivita.BianchiValidation`), both being exactly `∇G = 0` — Loinger's remark that Eq. 13 holds by
 invariance *and* "by virtue of the Bianchi relations."

The Lie-derivative law, its symmetry, and the Noether arbitrariness step (`noether_conservation`)
are exact. The remaining physical input is `hinv` — the diffeomorphism invariance of the action, already in the
post-`IBP` form `∑ᵢ (Div P)ᵢ εⁱ` of Eq. 8; producing that form from `⟨P, δ*g⟩` is the paper's variational
computation (`∫ … d⁴x`, Stokes), which is not performed.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

variable {ι : Type*} [Fintype ι]

/-- **The Lie derivative of the metric** (Loinger Eq. 7) `(L_ε g)_{mn} = ε^s ∂_s g_{mn} + g_{sn} ∂_m ε^s +
g_{ms} ∂_n ε^s`, from the metric `g`, its partial derivatives `dg` (`dg s = ∂_s g`) and the gradient of the
vector field, `dε m s = ∂_m ε^s`. -/
noncomputable def metricLieDerivative (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (ε : ι → ℝ) (dε : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun m n =>
    (∑ s, ε s * dg s m n) + (∑ s, g m s * dε n s) + (∑ s, g n s * dε m s)

/-- **[The Lie derivative of a symmetric metric is symmetric] `(L_ε g)_{mn} = (L_ε g)_{nm}`** — from the
symmetry of the metric derivatives `∂_s g_{mn} = ∂_s g_{nm}`. This is why the conjugate variational derivative
`P^{jk}` (contracted against `δ*g`) is a *symmetric* tensor. -/
theorem metricLieDerivative_symm (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ε : ι → ℝ)
    (dε : Matrix ι ι ℝ) (hdg : ∀ s, (dg s)ᵀ = dg s) :
    (metricLieDerivative g dg ε dε)ᵀ = metricLieDerivative g dg ε dε := by
  ext m n
  simp only [Matrix.transpose_apply, metricLieDerivative, Matrix.of_apply]
  rw [show (∑ s, ε s * dg s n m) = ∑ s, ε s * dg s m n from
    Finset.sum_congr rfl fun s _ => by
      rw [show dg s n m = dg s m n from by
        simpa [Matrix.transpose_apply] using (congrFun (congrFun (hdg s) m) n)]]
  ring

/-- **The diffeomorphism variation of the metric** (Loinger Eq. 7) `δ*g = −L_ε g` — the change of the metric
under the infinitesimal coordinate transformation `x'^j = x^j + ε^j`. -/
noncomputable def metricDiffeoVariation (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (ε : ι → ℝ) (dε : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  - metricLieDerivative g dg ε dε

/-- **[The diffeomorphism variation is symmetric] `δ*g_{mn} = δ*g_{nm}`.** -/
theorem metricDiffeoVariation_symm (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ε : ι → ℝ)
    (dε : Matrix ι ι ℝ) (hdg : ∀ s, (dg s)ᵀ = dg s) :
    (metricDiffeoVariation g dg ε dε)ᵀ = metricDiffeoVariation g dg ε dε := by
  rw [metricDiffeoVariation, transpose_neg, metricLieDerivative_symm g dg ε dε hdg]

/-- **A Killing vector** `L_ε g = 0` — the metric is unchanged under the flow of `ε`. -/
def IsKillingVector (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ε : ι → ℝ) (dε : Matrix ι ι ℝ) : Prop :=
  metricLieDerivative g dg ε dε = 0

/-- **[The metric is diffeomorphism-invariant iff `ε` is Killing] `δ*g = 0 ↔ IsKillingVector`.** -/
theorem metricDiffeoVariation_zero_iff_isKilling (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ε : ι → ℝ)
    (dε : Matrix ι ι ℝ) :
    metricDiffeoVariation g dg ε dε = 0 ↔ IsKillingVector g dg ε dε := by
  rw [metricDiffeoVariation, neg_eq_zero, IsKillingVector]

omit [Fintype ι] in
/-- **[The Lorentz–Levi-Civita thesis] `G^{jk}` is symmetric and covariantly conserved.** Loinger's
conclusion: the Einstein tensor `G^{jk} = R^{jk} − ½g^{jk}R` — the variational derivative `P^{jk}` of the
Einstein–Hilbert action, conjugate to the symmetric metric variation `δ*g` above — is a symmetric tensor
(`einsteinTensor_symm`) that is covariantly conserved (`bianchi_implies_conservation`), the two defining
properties of a true energy–momentum–stress tensor. Assembled from existing infrastructure; the Noether
derivation of the divergence-free identity `hBianchi` is the paper's §2–3 variational argument. -/
theorem einsteinTensor_is_thesis_tensor
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)) (Ric g T : Matrix ι ι ℝ) (scalarR κ : ℝ)
    (hRic : Ricᵀ = Ric) (hg : gᵀ = g)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ)
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0) (hκ : κ ≠ 0) :
    (einsteinTensor Ric scalarR g)ᵀ = einsteinTensor Ric scalarR g ∧ Div T = 0 :=
  ⟨einsteinTensor_symm Ric scalarR g hRic hg,
    bianchi_implies_conservation Div Ric scalarR g T κ hEFE hBianchi hκ⟩

/-! ## §B — the Noether conservation of the variational derivative (Eqs. 9, 13) -/

/-- **[Noether: arbitrary variation ⇒ conservation] `(∀ ε, ∑ᵢ (Div P)ᵢ εⁱ = 0) ⇒ Div P = 0`** (Loinger Eq. 9).
The diffeomorphism invariance `δ*_g 𝒥 = 0` of a scalar-density action, after the integration by parts of Eq. 8,
is the linear functional `ε ↦ ∑ⱼ (P^m_{j;m}) εʲ`; its vanishing for *every* vector field `ε` forces the
covariant divergence `Div P = P^m_{;m}` to vanish. This is the Noether identity for the variational derivative
`P` of *any* scalar density, independent of the field equations. -/
theorem noether_conservation [DecidableEq ι] (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)) (P : Matrix ι ι ℝ)
    (hinv : ∀ ε : ι → ℝ, ∑ i, Div P i * ε i = 0) : Div P = 0 := by
  funext j
  have h := hinv (Pi.single j 1)
  simpa [Pi.single_apply, Finset.sum_ite_eq'] using h

/-- **[Loinger Eq. 13] the Einstein tensor is covariantly conserved** `G^{jk}_{;k} = 0` as a Noether identity.
For `S = R` the variational derivative of the Einstein–Hilbert action `∫ R √(-g)` is `P^{jk} = G^{jk} =
R^{jk} − ½g^{jk}R` (Hilbert, Eq. 11); the diffeomorphism invariance of the action (`hinv`) therefore forces
`Div G = 0` by `noether_conservation` — the contracted Bianchi identity *derived from coordinate invariance*,
not assumed. -/
theorem einsteinTensor_noether_conserved [DecidableEq ι] (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric g : Matrix ι ι ℝ) (scalarR : ℝ)
    (hinv : ∀ ε : ι → ℝ, ∑ i, Div (einsteinTensor Ric scalarR g) i * ε i = 0) :
    Div (einsteinTensor Ric scalarR g) = 0 :=
  noether_conservation Div (einsteinTensor Ric scalarR g) hinv

/-- **[The Lorentz–Levi-Civita thesis, from invariance alone]** given only the diffeomorphism invariance of the
Einstein–Hilbert action (`hinv`) and the field equation `G = κT`, the Einstein tensor is symmetric, covariantly
conserved (`G^{jk}_{;k} = 0`, Eq. 13, *derived* via `noether_conservation`), and the matter stress-energy is
conserved. This is Loinger's full conclusion: `G^{jk}` has both defining properties of the true
energy–momentum–stress tensor of the gravitational field, obtained without invoking the field equations to get
the Bianchi identity. -/
theorem loinger_thesis_from_invariance [DecidableEq ι] (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric g T : Matrix ι ι ℝ) (scalarR κ : ℝ) (hRic : Ricᵀ = Ric) (hg : gᵀ = g)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ) (hκ : κ ≠ 0)
    (hinv : ∀ ε : ι → ℝ, ∑ i, Div (einsteinTensor Ric scalarR g) i * ε i = 0) :
    (einsteinTensor Ric scalarR g)ᵀ = einsteinTensor Ric scalarR g
      ∧ Div (einsteinTensor Ric scalarR g) = 0 ∧ Div T = 0 := by
  have hcons := einsteinTensor_noether_conserved Div Ric g scalarR hinv
  exact ⟨einsteinTensor_symm Ric scalarR g hRic hg, hcons,
    bianchi_implies_conservation Div Ric scalarR g T κ hEFE hcons hκ⟩

/-! ## §C — the second (differential) Bianchi route to Eq. 13 -/

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

/-- **[Arbitrary test field ⇒ vanishing] `(∀ ε, ∑ᵢ vᵢ εⁱ = 0) ↔ v = 0`** — the linear-algebra core of the
Noether step (`noether_conservation` is its `v = Div P` instance), stated for a divergence covector `v`. -/
theorem forall_inner_eq_zero_iff [DecidableEq ι] (v : ι → ℝ) :
    (∀ ε : ι → ℝ, ∑ i, v i * ε i = 0) ↔ v = 0 := by
  constructor
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using hj
  · rintro rfl ε
    simp

/-- **[Loinger Eq. 13, both routes agree] Noether invariance ⟺ contracted second Bianchi.** The diffeomorphism
invariance of the Einstein–Hilbert action — `∀ ε, ∑ᵢ (∇G)ᵢ εⁱ = 0`, the Noether/§B route — holds *iff* the
contracted second (differential) Bianchi identity `∇^μ R_{μν} = ½∇_ν R` holds (`contractedSecondBianchi`,
`LeviCivita.BianchiValidation`, the differential-geometry route). Both are exactly `∇G = 0`
(`einsteinDivergence = 0`). This is Loinger's remark that Eq. 13 follows from coordinate invariance *and* is
"identically satisfied by virtue of the Bianchi relations." -/
theorem noether_invariance_iff_secondBianchi [DecidableEq ι] (divRicci gradScalar : ι → ℝ) :
    (∀ ε : ι → ℝ, ∑ i, einsteinDivergence divRicci gradScalar i * ε i = 0)
      ↔ contractedSecondBianchi divRicci gradScalar := by
  rw [forall_inner_eq_zero_iff, einsteinDivergence_eq_zero_iff]

/-- **[Loinger Eq. 13 via the second Bianchi] `∇G = 0`** from the contracted second Bianchi identity — the
differential-geometry route to the conservation of the Einstein tensor (the Bianchi companion of the
Noether-route `einsteinTensor_noether_conserved`). -/
theorem einsteinDivergence_zero_of_secondBianchi (divRicci gradScalar : ι → ℝ)
    (hB : contractedSecondBianchi divRicci gradScalar) :
    einsteinDivergence divRicci gradScalar = 0 :=
  (einsteinDivergence_eq_zero_iff divRicci gradScalar).mpr hB

end Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation

end

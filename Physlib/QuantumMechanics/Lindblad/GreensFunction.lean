/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.SecondLaw

/-!
# Lindblad dissipator positivity and the proper-time Green's function

Structural origin of the entropic-time arrow and of Green's-function decay: a
Lindblad jump operator `L` produces the dissipator `H_I = L† L`, which is a
positive operator **automatically** (`isPositive_adjoint_comp_self`) — no
positivity hypothesis is assumed. This:

* establishes the `H_I.IsPositive` premise of
  `Physlib.Thermodynamics.SecondLaw.ofPositiveGeneratorArrow`, so the
  second-law monotonicity of the entropic-time arrow holds with **no hypothesis**
  beyond the existence of a jump operator (`ofLindbladJump`);
* makes the dissipative rate `Γ = ⟨ψ, L†L ψ⟩ = ‖L ψ‖² ≥ 0` manifestly
  non-negative (`lindbladRate_nonneg`, `lindbladRate_eq_normSq`);
* turns the non-negative damping `K_I` of the proper-time (Schwinger)
  Green's-function kernel — a *field assumption* in the proper-time
  resolvent layer (`ProperTimeLorentzianOperator.K_I_nonneg`)
  — into a **theorem**: the kernel `G(σ) = exp(i E_R σ − Γ σ)` decays and is
  contractive for `σ ≥ 0` (`lindblad_greenKernel_contraction`).

The single positive quantity `Γ = ‖L ψ‖²` is at once the entropy-production rate
`(2/ℏ)Γ` of the arrow (`lindblad_greenKernel_rate_eq_entropyRate`) and the decay
rate of the Green's function: dissipation, the arrow of time, and propagator decay
share one structural source — `L†L ⪰ 0`.


## References

- **Lindblad 1976** — *On the generators of quantum dynamical semigroups*
- **Gorini, Kossakowski, Sudarshan 1976** — *Completely positive dynamical semigroups of N-level systems*
- **Spohn 1978** — *Entropy production for quantum dynamical semigroups*
- **Breuer & Petruccione 2002** — *The Theory of Open Quantum Systems (textbook)*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.Thermodynamics.SecondLaw
open Physlib.QFT.Wick.Consistency
namespace Physlib.QuantumMechanics.Lindblad.GreensFunction

open QuantumInfo.Finite QuantumMechanics.FiniteTarget ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — A Lindblad jump operator gives a structurally positive dissipator -/

/-- The **Lindblad dissipator** `H_I = L† L` built from a jump operator `L`. -/
def lindbladDissipator (L : H →L[ℂ] H) : H →L[ℂ] H := adjoint L ∘L L

/-- **Structural positivity**: `L† L ⪰ 0` holds automatically — no hypothesis. -/
theorem lindbladDissipator_isPositive (L : H →L[ℂ] H) :
    (lindbladDissipator L).IsPositive :=
  isPositive_adjoint_comp_self L

/-- The **dissipative rate** `Γ = ⟨ψ, L†L ψ⟩` of a jump operator at `ψ`. -/
def lindbladRate (L : H →L[ℂ] H) (ψ : H) : ℝ := (lindbladDissipator L).reApplyInnerSelf ψ

/-- **The dissipative rate is non-negative** — structurally, from `L†L ⪰ 0`. -/
theorem lindbladRate_nonneg (L : H →L[ℂ] H) (ψ : H) : 0 ≤ lindbladRate L ψ :=
  (lindbladDissipator_isPositive L).2 ψ

/-- The dissipative rate is the squared jump amplitude `‖L ψ‖²` — manifestly
non-negative. -/
theorem lindbladRate_eq_normSq (L : H →L[ℂ] H) (ψ : H) :
    lindbladRate L ψ = ‖L ψ‖ ^ 2 := by
  unfold lindbladRate lindbladDissipator
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq]

/-! ## §2 — Entropic-time arrow from a Lindblad jump (no monotonicity hypothesis) -/

/-- **Entropic-time arrow from a Lindblad jump operator.** The dissipator `L†L` is
positive automatically, so this arrow exists with no positivity/monotonicity
hypothesis at all — the arrow of time arises from the mere existence of a
dissipative channel `L`. -/
def ofLindbladJump (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    EntropyArrowWorldline :=
  ofPositiveGeneratorArrow H_R (lindbladDissipator L) hbar hbar_pos
    (lindbladDissipator_isPositive L) ψ

/-- **The second-law monotonicity for a Lindblad-jump arrow is unconditional.** -/
theorem ofLindbladJump_S_I_monotone (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (ψ : H) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (ofLindbladJump H_R L hbar hbar_pos ψ).S_I_along t₁ ≤
      (ofLindbladJump H_R L hbar hbar_pos ψ).S_I_along t₂ :=
  (ofLindbladJump H_R L hbar hbar_pos ψ).S_I_monotone h

/-! ## §3 — Proper-time (Schwinger) Green's-function kernel and its decay

Proper-time resolvent layer. In other formalisations the
non-negative damping `K_I` is a *structure field*
(`ProperTimeLorentzianOperator.K_I_nonneg`); here it is `Γ = ‖L ψ‖²`, whose
non-negativity is a theorem from `L†L` positivity. -/

/-- Proper-time (Schwinger) Green's-function kernel `G(σ) = exp(i E_R σ − Γ σ)`
in **natural units `ℏ = 1`**: the proper-time representation of the dissipative
propagator with energy `E_R` and dissipative rate `Γ` (both in reciprocal-proper-
time units). It is the complex action weight, hence factors through the
Wick expansion. The `ℏ`-explicit form is `properTimeGreenKernelHbar`. -/
def properTimeGreenKernel (E_R Γ σ : ℝ) : ℂ := complexActionWeight (E_R * σ) (Γ * σ) 1

/-- **Dimensionful** proper-time Green's-function kernel
`G(σ) = exp(i E_R σ/ℏ − Γ σ)`, with energy `E_R` and dissipative rate `Γ`
(units of inverse time). Built from `complexActionWeight` with `S_R = E_R σ`,
`S_I = ℏ Γ σ`, so the phase records `1/ℏ` and the damping is the dimensionless
`Γ σ`. -/
def properTimeGreenKernelHbar (E_R Γ hbar σ : ℝ) : ℂ :=
  complexActionWeight (E_R * σ) (hbar * Γ * σ) hbar

/-- The Green's kernel is the complex action weight (grounding). -/
theorem properTimeGreenKernel_eq_complexActionWeight (E_R Γ σ : ℝ) :
    properTimeGreenKernel E_R Γ σ = complexActionWeight (E_R * σ) (Γ * σ) 1 := rfl

/-- The natural-units kernel is the `ℏ = 1` case of the dimensionful one. -/
theorem properTimeGreenKernel_eq_hbar_one (E_R Γ σ : ℝ) :
    properTimeGreenKernel E_R Γ σ = properTimeGreenKernelHbar E_R Γ 1 σ := by
  unfold properTimeGreenKernelHbar
  rw [properTimeGreenKernel_eq_complexActionWeight, one_mul]

/-- The dimensionful kernel's modulus is the dimensionless damping `exp(−Γσ)`,
independent of `ℏ` — the phase `E_R σ/ℏ` is unitary. -/
theorem norm_properTimeGreenKernelHbar (E_R Γ hbar σ : ℝ) (hbar0 : hbar ≠ 0) :
    ‖properTimeGreenKernelHbar E_R Γ hbar σ‖ = Real.exp (-(Γ * σ)) := by
  unfold properTimeGreenKernelHbar
  rw [norm_complexActionWeight, mul_assoc, mul_div_cancel_left₀ _ hbar0]

/-- **The Green's-function modulus is the proper-time damping** `exp(−Γσ)`. -/
theorem norm_properTimeGreenKernel (E_R Γ σ : ℝ) :
    ‖properTimeGreenKernel E_R Γ σ‖ = Real.exp (-(Γ * σ)) := by
  unfold properTimeGreenKernel
  rw [norm_complexActionWeight, div_one]

/-- **Green's-function decay from `L†L` positivity.** For a kernel whose damping is
the Lindblad rate `Γ = ‖L ψ‖²`, the proper-time Green's function is contractive
for `σ ≥ 0`: `‖G(σ)‖ = exp(−Γσ) ≤ 1`. This is the
`proper_time_lorentzian_contraction` result, but with `K_I_nonneg` now *derived* from the
positive dissipator rather than assumed. -/
theorem lindblad_greenKernel_contraction (L : H →L[ℂ] H) (ψ : H) (E_R σ : ℝ)
    (hσ : 0 ≤ σ) :
    ‖properTimeGreenKernel E_R (lindbladRate L ψ) σ‖ ≤ 1 := by
  rw [norm_properTimeGreenKernel, Real.exp_le_one_iff]
  have : 0 ≤ lindbladRate L ψ * σ := mul_nonneg (lindbladRate_nonneg L ψ) hσ
  linarith

/-! ## §4 — One source: the Green's-function rate is the entropy-production rate -/

/-- **The Green's-function decay rate is the arrow's entropy-production rate.** The
single quantity `Γ = ‖L ψ‖²` that damps the proper-time Green's function is, up to
`2/ℏ`, the entropy-production rate driving the entropic-time arrow built from the
same jump operator. Dissipation, propagator decay, and the time arrow share one
positive source. -/
theorem lindblad_greenKernel_rate_eq_entropyRate
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (positiveGeneratorSystem H_R (lindbladDissipator L) hbar hbar_pos
        (lindbladDissipator_isPositive L)).entropyRate ψ
      = (2 / hbar) * lindbladRate L ψ :=
  rfl

/-! ## §5 — Integrated theorem -/

/-- **The open-system chain, packaged.** From a Lindblad jump operator `L` the
entire derivation closes with no positivity/monotonicity hypothesis:

* (i) the dissipator `H_I = L† L` is positive;
* (ii) the dissipative rate is `Γ = ‖L ψ‖²`;
* (iii) the entropy-production rate is `(2/ℏ) Γ`;
* (iv) the entropic-time arrow's `S_I` is monotone;
* (v) the proper-time Green's kernel `G(σ) = exp(i E_R σ − Γσ)` is contractive for
  `σ ≥ 0`.

`L† L ⪰ 0` is the single structural source of the entropy arrow and of
Green's-function decay. -/
theorem lindblad_open_system_recovers_entropic_green_contraction
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) (E_R : ℝ) :
    (lindbladDissipator L).IsPositive
    ∧ lindbladRate L ψ = ‖L ψ‖ ^ 2
    ∧ (positiveGeneratorSystem H_R (lindbladDissipator L) hbar hbar_pos
        (lindbladDissipator_isPositive L)).entropyRate ψ = (2 / hbar) * lindbladRate L ψ
    ∧ (∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
        (ofLindbladJump H_R L hbar hbar_pos ψ).S_I_along t₁ ≤
          (ofLindbladJump H_R L hbar hbar_pos ψ).S_I_along t₂)
    ∧ (∀ σ : ℝ, 0 ≤ σ → ‖properTimeGreenKernel E_R (lindbladRate L ψ) σ‖ ≤ 1) :=
  ⟨lindbladDissipator_isPositive L,
   lindbladRate_eq_normSq L ψ,
   lindblad_greenKernel_rate_eq_entropyRate H_R L hbar hbar_pos ψ,
   fun {_ _} h => (ofLindbladJump H_R L hbar hbar_pos ψ).S_I_monotone h,
   fun σ hσ => lindblad_greenKernel_contraction L ψ E_R σ hσ⟩

/-! ## §4 — Bridge: Sergi-style `EntropyControlledSchrodingerSystem` from a Lindblad jump

For any Lindblad jump operator `L : H →L[ℂ] H` and `ℏ > 0`, the Sergi
non-Hermitian generator with `H_I := (ℏ/2)·L†L` reproduces the **no-jump**
(deterministic) part of the Lindblad master equation:

  `iℏ ∂_t |ψ⟩ = H_eff |ψ⟩`,    `H_eff = H_R − i·H_I = H_R − (iℏ/2)·L†L`.

This is the standard quantum-trajectory effective Hamiltonian
[Dalibard, Castin, Mølmer 1992; Knight 1998]. Under this identification:
  * `H_I` is automatically positive (`L†L ⪰ 0`, `ℏ/2 > 0`)
  * `expectation_HI = (ℏ/2)·⟨ψ, L†L ψ⟩ = (ℏ/2)·‖L ψ‖²`
  * `entropyRate = (2/ℏ)·expectation_HI = ‖L ψ‖² =` `lindbladRate L ψ`

The Lindblad rate-positivity (`lindbladRate_nonneg`) gives the Sergi
`expectation_nonneg` field for free. -/

/-- **Sergi-Lindblad bridge constructor.** Build an
`EntropyControlledSchrodingerSystem` from a Lindblad jump operator
`L : H →L[ℂ] H` by setting `H_I := (ℏ/2)·L†L`.

This realises Sergi's H_I as the canonical Lindblad dissipator, with the
wavefunction-level entropy rate equal to `‖L ψ‖²` — physlib's
`lindbladRate L ψ` from §1 of this file.

This is the operator-level instance of `L_k† L_k = 2·H_I/ℏ` — the standard
identification between Sergi's anti-Hermitian generator and the deterministic
part of a Lindblad master equation. -/
noncomputable def
    QuantumMechanics.FiniteTarget.EntropyControlledSchrodingerSystem.ofLindbladJump
    (H_R L : H →L[ℂ] H) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    QuantumMechanics.FiniteTarget.EntropyControlledSchrodingerSystem (H := H) where
  H_R := H_R
  H_I := (ℏ / 2 : ℝ) • lindbladDissipator L
  hbar := ℏ
  hbar_pos := hℏ
  expectation_HI := fun ψ => (ℏ / 2) * lindbladRate L ψ
  entropyRate := fun ψ => lindbladRate L ψ
  entropyRate_eq_expectation := by
    intro ψ
    show lindbladRate L ψ = (2 / ℏ) * ((ℏ / 2) * lindbladRate L ψ)
    field_simp
  expectation_nonneg := by
    intro ψ
    exact mul_nonneg (by linarith) (lindbladRate_nonneg L ψ)
  zero_HI_zero_expectation := by
    intro h_HI ψ
    have hℏ2 : (ℏ / 2 : ℝ) ≠ 0 := by linarith
    have h_LL : lindbladDissipator L = 0 :=
      (smul_eq_zero.mp h_HI).resolve_left hℏ2
    show (ℏ / 2) * lindbladRate L ψ = 0
    rw [lindbladRate_eq_normSq]
    have h_rate_zero : lindbladRate L ψ = 0 := by
      unfold lindbladRate
      rw [h_LL]
      simp [ContinuousLinearMap.reApplyInnerSelf]
    have h_normSq_zero : ‖L ψ‖ ^ 2 = 0 := by
      rw [← lindbladRate_eq_normSq L ψ]; exact h_rate_zero
    have hL_norm : ‖L ψ‖ = 0 := by nlinarith [norm_nonneg (L ψ)]
    have : L ψ = 0 := norm_eq_zero.mp hL_norm
    rw [this]; simp

/-- **Sergi entropyRate = Lindblad rate** (in the bridge instance):
the wavefunction-level entropy production via the Sergi/Lindblad
identification equals `‖L ψ‖²`. -/
theorem
    QuantumMechanics.FiniteTarget.EntropyControlledSchrodingerSystem.ofLindbladJump_entropyRate
    (H_R L : H →L[ℂ] H) (ℏ : ℝ) (hℏ : 0 < ℏ) (ψ : H) :
    (QuantumMechanics.FiniteTarget.EntropyControlledSchrodingerSystem.ofLindbladJump
        H_R L ℏ hℏ).entropyRate ψ
      = lindbladRate L ψ := rfl

/-- **Sergi `H_I = (ℏ/2)·L†L`** in the bridge instance. -/
theorem
    QuantumMechanics.FiniteTarget.EntropyControlledSchrodingerSystem.ofLindbladJump_H_I
    (H_R L : H →L[ℂ] H) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    (QuantumMechanics.FiniteTarget.EntropyControlledSchrodingerSystem.ofLindbladJump
        H_R L ℏ hℏ).H_I
      = (ℏ / 2 : ℝ) • lindbladDissipator L := rfl

end Physlib.QuantumMechanics.Lindblad.GreensFunction

end

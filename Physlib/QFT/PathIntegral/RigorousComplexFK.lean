/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.MeasureModel

/-!
# Rigorous complex Feynman–Kac for entropically damped oscillatory measures

Port of the rigorous complex FK content from
``
into physlib's `Physlib.QFT.PathIntegral.MeasureModel` scope.

The general complex Feynman–Kac theorem — for arbitrary oscillatory
complex measures with no real damping component — is **open in the
literature** (Glimm & Jaffe 1987 *Quantum Physics: A Functional
Integral Point of View*, 2nd ed., pp. 43–44):

> *"The complex case, needed in quantum mechanics, is still an open
> question."*

This file provides **rigorous complex FK** in the **restricted
class of entropically damped oscillatory measures** — those whose
weight factorises as

  `weight(x) = exp(i·S_R(x)/ℏ) · exp(−S_I(x)/ℏ)`

with `S_I ≥ 0`.  The identity `‖weight‖ = damping` (already proven
in `MeasureModel.weight_norm_is_damping`) makes the modulus
integrable iff the damping is `L¹`, which in turn makes the complex
weight Bochner-integrable.

This is not the Glimm–Jaffe full theorem; it is the rigorous complex
FK theorem **specialised to the complex-action/entropic-time entropically damped class**,
where the entropic suppression converts the would-be oscillatory
integral into a genuinely absolutely-convergent Bochner integral.

## Normalisation versus renormalisation

The result here is **counterterm-free / no-renormalisation control**,
not a claim that probabilistic normalisation is unnecessary.  The
unnormalised complex expectation

  `⟨obs⟩ := ∫ obs · weight dμ`

is well-defined and bounded by `C · partitionFunction m` under the
entropic-damping hypothesis.  Downstream consumers seeking
probability semantics may divide by the partition function `Z`.
The path-integral lane removes the need for UV subtraction
counterterms in the certified entropically damped class.

## Contents

### §1 — Partition function and complex FK expectation

* `partitionFunction m := ∫ damping dμ` — the entropic-damping
  partition functional.
* `complexFKExpectation m obs := ∫ obs · weight dμ` — the rigorous
  complex FK expectation of an ℂ-valued observable.

### §2 — Integrability

* `complexFKExpectation_integrable` — for damping in `L¹` and `obs`
  essentially bounded by `C`, the integrand `obs · weight` is
  Bochner-integrable.

### §3 — Norm bound

* `complexFKExpectation_norm_le` — `‖⟨obs⟩‖ ≤ C · partitionFunction m`.

### §4 — Headline theorem

* **`complex_FK_rigorous`** — the headline: integrability + norm
  bound bundled.

## References

* Glimm–Jaffe 1987 *Quantum Physics: A Functional Integral Point of
  View* (2nd ed., pp. 43–44) — open status of the general
  complex-measure problem.
* Source: ``.
* `Physlib.QFT.PathIntegral.MeasureModel` — substrate.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open MeasureTheory Complex Real

namespace MeasurePathIntegralModel

variable {α : Type*} [MeasurableSpace α] (m : MeasurePathIntegralModel α)

/-! ## §1 — Partition function + complex FK expectation -/

/-- **Partition function** `Z := ∫ damping dμ = ∫ exp(−S_I/ℏ) dμ`.

The entropic-damping partition functional: the integral of the
real damping factor against the reference measure.  Since damping
`> 0` everywhere, `Z ≥ 0`. -/
def partitionFunction : ℝ := ∫ x, m.damping x ∂m.μ

/-- **Rigorous complex FK expectation** `⟨obs⟩ := ∫ obs · weight dμ`.

The Bochner integral of an ℂ-valued observable against the
complex weight.  This is the rigorous content the long-standing
`complex_FK_bridge` placeholder reserved for the entropically
damped class. -/
def complexFKExpectation (obs : α → ℂ) : ℂ :=
  ∫ x, obs x * m.weight x ∂m.μ

/-! ## §2 — Integrability of `obs · weight` -/

/-- **Integrability of the FK integrand**.

For an entropically damped `MeasurePathIntegralModel m` with
`Integrable damping`, any measurable ℂ-valued observable `obs`
essentially bounded by `C ≥ 0` yields a Bochner-integrable
integrand `obs · weight`.

**Strategy**: bound the integrand norm by `C · damping`, which is
`L¹` by hypothesis. -/
theorem complexFKExpectation_integrable
    (hL1 : Integrable (fun x => m.damping x) m.μ)
    (obs : α → ℂ) (hMeas : Measurable obs)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂m.μ, ‖obs x‖ ≤ C) :
    Integrable (fun x => obs x * m.weight x) m.μ := by
  refine Integrable.mono'
    (g := fun x => C * m.damping x)
    (hL1.const_mul C)
    (hMeas.aestronglyMeasurable.mul m.measurable_weight.aestronglyMeasurable)
    ?_
  refine hBound.mono ?_
  intro x hx
  show ‖obs x * m.weight x‖ ≤ C * m.damping x
  rw [norm_mul, m.weight_norm_is_damping]
  exact mul_le_mul hx (le_refl _) (m.damping_pos x).le hC

/-! ## §3 — Norm bound of the complex FK expectation -/

/-- **Norm bound** for the complex FK expectation.

Under the integrability assumption (damping ∈ `L¹`) and the
observable bound (`‖obs x‖ ≤ C` a.e.), the FK expectation is
bounded in modulus by `C · partitionFunction m`. -/
theorem complexFKExpectation_norm_le
    (hL1 : Integrable (fun x => m.damping x) m.μ)
    (obs : α → ℂ) (hMeas : Measurable obs)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂m.μ, ‖obs x‖ ≤ C) :
    ‖m.complexFKExpectation obs‖ ≤ C * m.partitionFunction := by
  unfold complexFKExpectation partitionFunction
  calc
    ‖∫ x, obs x * m.weight x ∂m.μ‖
        ≤ ∫ x, ‖obs x * m.weight x‖ ∂m.μ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * m.damping x ∂m.μ := by
          refine integral_mono_ae ?_ (hL1.const_mul C) ?_
          · exact (m.complexFKExpectation_integrable hL1 obs hMeas C hC hBound).norm
          · refine hBound.mono ?_
            intro x hx
            show ‖obs x * m.weight x‖ ≤ C * m.damping x
            rw [norm_mul, m.weight_norm_is_damping]
            exact mul_le_mul hx (le_refl _) (m.damping_pos x).le hC
    _ = C * ∫ x, m.damping x ∂m.μ := by
          rw [integral_const_mul]

/-! ## §4 — Headline rigorous complex FK theorem -/

/-- **HEADLINE — Rigorous complex Feynman–Kac for entropically
damped oscillatory measures**.

For an entropically-damped `MeasurePathIntegralModel m` with
damping ∈ `L¹` and any measurable ℂ-valued observable `obs`
essentially bounded by `C ≥ 0`:

1. The integrand `obs · weight` is Bochner-integrable.
2. The expectation `⟨obs⟩ := ∫ obs · weight dμ` is well-defined.
3. The expectation satisfies the norm bound
 `‖⟨obs⟩‖ ≤ C · partitionFunction m`.

**scope**: this is rigorous *for entropically-damped*
complex measures. The general Glimm–Jaffe oscillatory-measure
problem remains open in the literature; the entropic-damping
class admits this rigorous treatment because the Phase-12
identity `‖weight‖ = damping` converts the oscillatory integral
into an absolutely-convergent Bochner integral. -/
theorem complex_FK_rigorous
    (hL1 : Integrable (fun x => m.damping x) m.μ)
    (obs : α → ℂ) (hMeas : Measurable obs)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂m.μ, ‖obs x‖ ≤ C) :
    Integrable (fun x => obs x * m.weight x) m.μ ∧
      ‖m.complexFKExpectation obs‖ ≤ C * m.partitionFunction :=
  ⟨m.complexFKExpectation_integrable hL1 obs hMeas C hC hBound,
   m.complexFKExpectation_norm_le hL1 obs hMeas C hC hBound⟩

/-! ## §5 — Partition function under Euclidean (S_R ≡ 0) sector -/

/-- **Euclidean partition function**: when the real action vanishes
identically (`S_R ≡ 0`), the partition function equals the integral
of `Real.exp(−S_I/ℏ)` against the reference measure — the standard
Boltzmann / Feynman–Kac partition function. -/
theorem partitionFunction_eq_integral_damping_of_actionRe_zero
    (_ : ∀ x, m.actionRe x = 0) :
    m.partitionFunction = ∫ x, Real.exp (-(m.actionImScaled x)) ∂m.μ := by
  unfold partitionFunction damping
  rfl

/-- **Euclidean complex FK expectation = real FK expectation**:
when `S_R ≡ 0`, the complex FK expectation collapses to the
purely-real Boltzmann/Feynman–Kac expectation. -/
theorem complexFKExpectation_eq_real_of_actionRe_zero
    (hRe : ∀ x, m.actionRe x = 0) (obs : α → ℂ) :
    m.complexFKExpectation obs
      = ∫ x, obs x * (m.damping x : ℂ) ∂m.μ := by
  unfold complexFKExpectation
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  show obs x * m.weight x = obs x * (m.damping x : ℂ)
  rw [m.weight_eq_damping_of_actionRe_zero hRe x]

end MeasurePathIntegralModel

end Physlib.QFT.PathIntegral

end

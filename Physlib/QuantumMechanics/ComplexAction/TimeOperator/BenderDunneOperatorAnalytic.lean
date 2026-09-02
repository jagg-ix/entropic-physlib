/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneMomentLadder
public import Mathlib.Data.Real.Sign
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The Bender–Dunne `T_{−1,1}` integral operator: the analytic expansion (Eq. 8, 10)

The *analytic* content of the free time-of-arrival operator `T_{−1,1}` of Bunao & Galapon (arXiv:1509.00340).
Where `BenderDunneTimeOperatorDomain` records the domain as an abstract pair of moment conditions, this module
formalizes the **integral operator itself** and the expansion (Eq. 10) that *produces* those conditions.

The operator (Eq. 8) is the singular-kernel integral

`(T_{−1,1}φ)(q) = ∫_ℝ (q + q') sgn(q − q') φ(q') dq'`.

The pointwise identity `sgn(q − q') = 𝟙_{q'<q} − 𝟙_{q'>q}` splits the real line at `q`, giving the antiderivative
form (Eq. 10)

`(T_{−1,1}φ)(q) = ∫_{q'<q}(q+q')φ − ∫_{q'>q}(q+q')φ = q·(∫_{q'<q}φ − ∫_{q'>q}φ) + (∫_{q'<q}q'φ − ∫_{q'>q}q'φ)`.

This is the analytic heart of the paper's domain result: as `q → +∞` the two cumulative integrals tend to the full
integrals `∫φ` and `∫q'φ`, and the leading term `q·∫φ` grows linearly unless `∫φ = 0`; the next term forces
`∫q'φ = 0`. Those are exactly the two moment conditions (Eq. 11) formalized abstractly in
`BenderDunneTimeOperatorDomain.benderDunneDomain`.

* **§A — the singular kernel splits the line.** `arrivalKernel q q' = (q+q') sgn(q−q')`; **`sign_sub_eq_indicator`**
  (`sgn(q−q') = 𝟙_{Iio q} − 𝟙_{Ioi q}`).
* **§B — the operator expansion (Eq. 10).** `arrivalOperator φ q = ∫ (q+q') sgn(q−q') φ`; **`arrivalOperator_split`**
  (`= ∫_{Iio q}(q+q')φ − ∫_{Ioi q}(q+q')φ`, over an integrability hypothesis).
* **§C — the moment form (Eq. 10, expanded).** **`arrivalOperator_eq_moments`**
  (`= q·(∫_{Iio}φ − ∫_{Ioi}φ) + (∫_{Iio}q'φ − ∫_{Ioi}q'φ)`) — the leading `q·∫φ` term whose growth the zeroth-moment
  condition kills, and the constant `∫q'φ` term the first-moment condition kills.

**Honest layering.** These are exact `MeasureTheory` integral identities (given the natural integrability
hypotheses that hold on the paper's Schwartz-type domain). The paper's main **density** theorem
(`D(T_{−1,1})` dense in `L²(ℝ)`) is now proven in `TimeOperator.BenderDunneDensity.benderDunneDomain_dense`: the
two-moment domain is dense because each moment functional is unbounded (`discontinuous_ker_dense` iterated), with
the `HermiteL2Basis` orthonormal basis behind the unboundedness of the moments. What remains is the
asymptotic-limit step turning `arrivalOperator_eq_moments` into the *necessity* of Eqs. 11 (the `q → ∞` limits of
the cumulative integrals) — recorded here as the residual analytic content.

## References

* Bunao & Galapon, arXiv:1509.00340 (2015), Eqs. 8, 10, 11. Supplies the integral-operator analytics behind the
  abstract `BenderDunneTimeOperatorDomain`.


-/

set_option autoImplicit false

open MeasureTheory Set

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneOperatorAnalytic


/-- The **Bender–Dunne `T_{−1,1}` kernel** `⟨q|T_{−1,1}|q'⟩ = (q + q') sgn(q − q')` (Eq. 8): symmetric in `q + q'`,
antisymmetric through `sgn(q − q')`. -/
noncomputable def arrivalKernel (q q' : ℝ) : ℝ := (q + q') * Real.sign (q - q')

/-- **The sign kernel splits the line at `q`** `sgn(q − q') = 𝟙_{q' < q} − 𝟙_{q' > q}` — the Heaviside
decomposition that turns the singular integral operator into a pair of one-sided (cumulative) integrals. -/
lemma sign_sub_eq_indicator (q q' : ℝ) :
    Real.sign (q - q')
      = (Set.Iio q).indicator (fun _ => (1 : ℝ)) q' - (Set.Ioi q).indicator (fun _ => (1 : ℝ)) q' := by
  rcases lt_trichotomy q' q with h | h | h
  · rw [Real.sign_of_pos (by linarith), Set.indicator_of_mem (Set.mem_Iio.mpr h),
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; linarith)]
    ring
  · subst h
    rw [sub_self, Real.sign_zero, Set.indicator_of_notMem (by simp),
      Set.indicator_of_notMem (by simp)]
    ring
  · rw [Real.sign_of_neg (by linarith), Set.indicator_of_notMem (by simp only [Set.mem_Iio]; linarith),
      Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
    ring


/-- The **free time-of-arrival operator** `(T_{−1,1}φ)(q) = ∫_ℝ (q + q') sgn(q − q') φ(q') dq'` (Eq. 8). -/
noncomputable def arrivalOperator (φ : ℝ → ℝ) (q : ℝ) : ℝ := ∫ q', arrivalKernel q q' * φ q'

/-- **The operator splits into one-sided integrals (Eq. 10)** `(T_{−1,1}φ)(q) = ∫_{q'<q}(q+q')φ − ∫_{q'>q}(q+q')φ`
— the singular kernel `(q+q')sgn(q−q')` integrates to the difference of the cumulative integrals below and above
`q`. Requires only that `(q + ·)φ` be integrable (true on the paper's domain). -/
lemma arrivalOperator_split (φ : ℝ → ℝ) (q : ℝ)
    (hf : Integrable (fun q' => (q + q') * φ q')) :
    arrivalOperator φ q
      = (∫ q' in Set.Iio q, (q + q') * φ q') - (∫ q' in Set.Ioi q, (q + q') * φ q') := by
  unfold arrivalOperator arrivalKernel
  have key : (fun q' => (q + q') * Real.sign (q - q') * φ q')
      = fun q' => (Set.Iio q).indicator (fun q'' => (q + q'') * φ q'') q'
        - (Set.Ioi q).indicator (fun q'' => (q + q'') * φ q'') q' := by
    funext q'
    rw [sign_sub_eq_indicator]
    by_cases h1 : q' ∈ Set.Iio q <;> by_cases h2 : q' ∈ Set.Ioi q <;>
      simp only [Set.indicator_apply, h1, h2, if_true, if_false] <;> ring
  rw [key, integral_sub (hf.indicator measurableSet_Iio) (hf.indicator measurableSet_Ioi),
    integral_indicator measurableSet_Iio, integral_indicator measurableSet_Ioi]


/-- **The expansion exposing the two moments (Eq. 10)**
`(T_{−1,1}φ)(q) = q·(∫_{q'<q}φ − ∫_{q'>q}φ) + (∫_{q'<q}q'φ − ∫_{q'>q}q'φ)`.

As `q → +∞` the cumulative integrals tend to `∫φ` and `∫q'φ`: the leading `q·∫φ` term grows linearly (breaking
square-integrability) unless the **zeroth moment** `∫φ = 0`, and the residual then forces the **first moment**
`∫q'φ = 0`. This is precisely the pair of conditions `BenderDunneTimeOperatorDomain.benderDunneDomain` encodes. -/
lemma arrivalOperator_eq_moments (φ : ℝ → ℝ) (q : ℝ)
    (hφ : Integrable φ) (hqφ : Integrable (fun q' => q' * φ q')) :
    arrivalOperator φ q
      = q * ((∫ q' in Set.Iio q, φ q') - (∫ q' in Set.Ioi q, φ q'))
        + ((∫ q' in Set.Iio q, q' * φ q') - (∫ q' in Set.Ioi q, q' * φ q')) := by
  have hf : Integrable (fun q' => (q + q') * φ q') := by
    have e : (fun q' => (q + q') * φ q') = (fun q' => q * φ q' + q' * φ q') := by funext q'; ring
    rw [e]; exact (hφ.const_mul q).add hqφ
  have hsplit : ∀ s : Set ℝ, (∫ q' in s, (q + q') * φ q')
      = q * (∫ q' in s, φ q') + ∫ q' in s, q' * φ q' := by
    intro s
    have e : (fun q' => (q + q') * φ q') = (fun q' => q * φ q' + q' * φ q') := by funext q'; ring
    rw [e, integral_add ((hφ.const_mul q).integrableOn) (hqφ.integrableOn), integral_const_mul]
  rw [arrivalOperator_split φ q hf, hsplit (Set.Iio q), hsplit (Set.Ioi q)]
  ring

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneOperatorAnalytic

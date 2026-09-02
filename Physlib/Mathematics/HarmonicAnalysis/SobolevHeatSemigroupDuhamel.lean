/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
meta import Zil

/-!
# The Duhamel identity and exponent conditions of the Ozawa–Takeuchi proof

Completes the algebraic scaffolding of the Ozawa–Takeuchi heat-semigroup proof of the
Gagliardo–Nirenberg and Sobolev inequalities (Proc. Amer. Math. Soc. Ser. B 11 (2024) 371–377),
beyond the balancing kernel of `GagliardoNirenbergHeatSemigroup`.

* `duhamel_telescoping` — the **telescoping / Duhamel identity** that opens both proofs:
  `f = e^{tΔ}f − ∫₀ᵗ Δe^{τΔ}f dτ`. Abstractly, for a path `u` with `u 0 = f` and derivative `u'`,
  the fundamental theorem of calculus gives `f = u t − ∫₀ᵗ u'`. Combined with the `Lᵖ`-`Lq` heat
  estimate on `u t = e^{tΔ}f` and `u'τ = Δe^{τΔ}f`, this produces the two-term time bound.
* `heat_gradient_exponent_pos_iff` — the **integrability threshold** `np/(n+p) < r`: exactly the
  condition that the gradient exponent `1/2 − (n/2)(1/r−1/p)` is positive (so the `τ`-integral of the
  gradient term converges and the balancing time `t → 0` is admissible).
* `gnSigma_pos` / `gnSigma_lt_one` — under `q < p` and the threshold, the interpolation index
  `σ ∈ (0,1)`, so `σ` is a genuine interpolation weight.
* `sobolev_holder_exponent_balance` — the **three-factor Hölder balance** of the Sobolev proof:
  with `η = 2/n`, `θ = n/(2n−2)` (`n ≥ 3`), the exponents satisfy
  `θ(n−1)/n + η/2 + (1−η)/2 = 1`, licensing the Hölder split `G_t|Δf| = F₀^θ F₁^η F₂^{1−η}`.
-/

set_option autoImplicit false

open MeasureTheory
open Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup

@[expose] public section

namespace Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel

/-- **[The telescoping / Duhamel identity]** `f = u t − ∫₀ᵗ u'(τ) dτ` for a path `u` with `u 0 = f`.
This is the opening identity of both Ozawa–Takeuchi proofs, `f = e^{tΔ}f − ∫₀ᵗ Δe^{τΔ}f dτ` (with
`u τ = e^{τΔ}f`, `u' τ = ∂_τ e^{τΔ}f = Δe^{τΔ}f`), which produces the two-term time bound after the
`Lᵖ`-`Lq` heat estimate. Pure fundamental theorem of calculus. -/
theorem duhamel_telescoping {u u' : ℝ → ℝ} {f t : ℝ} (h0 : u 0 = f)
    (hderiv : ∀ x ∈ Set.uIcc 0 t, HasDerivAt u (u' x) x)
    (hint : IntervalIntegrable u' volume 0 t) :
    f = u t - ∫ τ in (0 : ℝ)..t, u' τ := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, h0]
  ring

/-- **[The integrability threshold] `np/(n+p) < r ↔ 0 < 1/2 − (n/2)(1/r − 1/p)`.** The
Gagliardo–Nirenberg hypothesis `np/(n+p) < r` is exactly the positivity of the gradient exponent
`1/2 − (n/2)(1/r − 1/p)`: the condition `−(n/2)(1/r − 1/p) − 1/2 > −1` under which the `τ`-integral
`∫₀ᵗ τ^{−(n/2)(1/r−1/p)−1/2} dτ` of the gradient term converges. -/
theorem heat_gradient_exponent_pos_iff {n p r : ℝ} (hn : 0 < n) (hp : 0 < p) (hr : 0 < r) :
    n * p / (n + p) < r ↔ 0 < 1 / 2 - (n / 2) * (1 / r - 1 / p) := by
  have hnp : (0 : ℝ) < n + p := by positivity
  rw [div_lt_iff₀ hnp,
    show (1 : ℝ) / 2 - (n / 2) * (1 / r - 1 / p) = (r * (n + p) - n * p) / (2 * r * p) by
      field_simp; ring,
    lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * r * p)]
  constructor <;> intro h <;> nlinarith

/-- Under `q < p`, the Gagliardo–Nirenberg index `σ = n(1/q − 1/p)/(1 + n(1/q − 1/r))` is positive:
the numerator `n(1/q − 1/p)` is positive and the denominator (`2·gnScale`) is positive. -/
theorem gnSigma_pos {n p q : ℝ} (r : ℝ) (hn : 0 < n) (hq : 0 < q) (hqp : q < p)
    (hscale : 0 < gnScale n q r) : 0 < gnSigma n p q r := by
  have hden : 0 < 1 + n * (1 / q - 1 / r) := by rw [← two_mul_gnScale]; linarith
  have hd : 0 < 1 / q - 1 / p := by
    have := one_div_lt_one_div_of_lt hq hqp; linarith
  unfold gnSigma
  exact div_pos (mul_pos hn hd) hden

/-- Under `q < p` and the integrability threshold `np/(n+p) < r`, the Gagliardo–Nirenberg index
`σ < 1`: equivalently `n(1/r − 1/p) < 1`, the same threshold that makes the gradient exponent
positive. Together with `gnSigma_pos` this gives `σ ∈ (0,1)`, a genuine interpolation weight. -/
theorem gnSigma_lt_one {n p q r : ℝ} (hn : 0 < n) (hp : 0 < p) (hr : 0 < r)
    (hscale : 0 < gnScale n q r) (hthresh : n * p / (n + p) < r) :
    gnSigma n p q r < 1 := by
  have hden : 0 < 1 + n * (1 / q - 1 / r) := by rw [← two_mul_gnScale]; positivity
  have hpos : 0 < 1 / 2 - (n / 2) * (1 / r - 1 / p) :=
    (heat_gradient_exponent_pos_iff hn hp hr).mp hthresh
  have hkey : n * (1 / r - 1 / p) < 1 := by
    have heq : (n / 2) * (1 / r - 1 / p) = n * (1 / r - 1 / p) / 2 := by ring
    rw [heq] at hpos; linarith
  unfold gnSigma
  rw [div_lt_one hden]
  have hexp : n * (1 / q - 1 / p) = n * (1 / q - 1 / r) + n * (1 / r - 1 / p) := by ring
  rw [hexp]; linarith

/-- **[The three-factor Hölder exponent balance of the Sobolev proof]** With `η = 2/n` and
`θ = n/(2n−2)` (`n > 1`, in the paper `n ≥ 3`), the three Hölder exponents balance:
`θ(n−1)/n + η/2 + (1−η)/2 = 1`. This is the identity licensing the split
`G_t|f(x−y)−f(x)| = F₀^θ F₁^η F₂^{1−η}` with Hölder exponents `n/(n−1)`, `2`, `2`, the key algebraic
step of the Sobolev-inequality proof. -/
theorem sobolev_holder_exponent_balance {n : ℝ} (hn : 1 < n) :
    (n / (2 * n - 2)) * ((n - 1) / n) + (2 / n) / 2 + (1 - 2 / n) / 2 = 1 := by
  have h1 : n ≠ 0 := ne_of_gt (by linarith)
  have h3 : n - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [show 2 * n - 2 = 2 * (n - 1) by ring]
  field_simp
  ring

end Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel

end

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.duhamel_telescoping where
  formalizes @ "claim:the-telescoping-duhamel-identity-f-equals-the-smoothed-value-minus-the-integral-of-the-time-derivative-opens-the-heat-semigroup-proof",
  supported_by @ "paper:ozawa-takeuchi-heat-semigroup-gagliardo-nirenberg-sobolev"

zil attach Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.heat_gradient_exponent_pos_iff where
  formalizes @ "claim:the-gagliardo-nirenberg-hypothesis-np-over-n-plus-p-less-than-r-is-exactly-the-positivity-of-the-gradient-heat-exponent-the-integral-convergence-threshold",
  supported_by @ "paper:ozawa-takeuchi-heat-semigroup-gagliardo-nirenberg-sobolev"

zil attach Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.gnSigma_lt_one where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.heat_gradient_exponent_pos_iff",
  formalizes @ "claim:under-q-less-than-p-and-the-integrability-threshold-the-gagliardo-nirenberg-index-is-less-than-one",
  requires @ "claim:the-gagliardo-nirenberg-hypothesis-np-over-n-plus-p-less-than-r-is-exactly-the-positivity-of-the-gradient-heat-exponent-the-integral-convergence-threshold"

zil attach Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.sobolev_holder_exponent_balance where
  formalizes @ "claim:the-three-factor-holder-exponents-of-the-sobolev-proof-balance-to-one-with-eta-two-over-n-and-theta-n-over-two-n-minus-two",
  supported_by @ "paper:ozawa-takeuchi-heat-semigroup-gagliardo-nirenberg-sobolev"

zil_file_contract physlib.sobolevHeatSemigroupDuhamel where
  promises "The Duhamel scaffolding of the Ozawa-Takeuchi proof: the telescoping identity f = u(t) - integral of u' (the FTC opening f = e^{t Delta}f - integral Delta e^{tau Delta}f) that produces the two-term time bound; the integrability threshold np/(n+p) < r as exactly the positivity of the gradient heat exponent 1/2 - (n/2)(1/r-1/p); the resulting sigma in (0,1) as a genuine interpolation weight; and the three-factor Holder exponent balance theta(n-1)/n + eta/2 + (1-eta)/2 = 1 of the Sobolev proof."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gnSigma",
    "lean:Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gnScale"]
  forbids_substitutes ["the Lp realization of e^{t Delta}f and the heat-kernel derivative estimates, which are the cited hypotheses of the two-term bound",
    "the Gaussian moment scaling and the Hardy inequality of the Sobolev proof, only the exponent balance is carried"]
  witnessed_by [Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.duhamel_telescoping,
    Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.heat_gradient_exponent_pos_iff,
    Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.gnSigma_pos,
    Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.gnSigma_lt_one,
    Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel.sobolev_holder_exponent_balance]

/- ZIL-END -/

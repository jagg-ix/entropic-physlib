/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.HamiltonianRenormalisation.FreeScalarCovarianceFlow

/-!
# Hamiltonian formulation from the measure: the free-field reconstruction
(Hamiltonian renormalisation II, §2.4)

Section 2.4 of Lang–Liegener–Thiemann, *Hamiltonian renormalisation II*
(arXiv:1711.06727v2): starting from the Gaussian history measure with covariance
`C = ℏκ(−∂₀² + ω²)⁻¹` — whose position-space kernel is `e^{−ω|s−t|}/(2ω)` (Eq. 2.27; the
momentum-space form `1/(k₀² + ω²)` is the library's
`QFT.PathIntegral.EuclideanPropagator.euclidean_propagator`) — one reconstructs the Hilbert
space, vacuum, and contraction semigroup.  The exact mechanisms, per frequency mode:

* `reflectedKernel_factorizes`, `reflectedPairing_factorizes` — **Eq. 2.31**: across the time
  reflection the kernel loses its modulus, `e^{−ω|(−s)−t|} = e^{−ωs}·e^{−ωt}` for positive
  times, so the reflected history pairing of two sharp-time families **factorizes** into
  exponentially damped time-zero data — the single mechanism behind the whole
  reconstruction.
* `reflectedPairing_eq_timeZero` — **Eq. 2.32**: consequently a positive-time family pairs
  with any reflected family exactly as its damped **time-zero projection**
  `Ĝ = δ(t,0)·Σ_l e^{−ωs_l}G_l` does.
* `weylForm_timeZero_reduction` — **Eqs. 2.33–2.34**: at the level of the Gaussian
  generating functional `μ(W[F]) = e^{−½⟨F,CF⟩}` (the Weyl expectation of a Gaussian
  measure, the shape of `gaussianWeyl`), matching cross pairings force
  `⟨e^{iΦ[F]}, e^{iΦ[G]}⟩ = z·⟨e^{iΦ[F]}, e^{iΦ[Ĝ]}⟩` with
  `z = e^{−½(⟨G,CG⟩−⟨Ĝ,CĜ⟩)}` — the vector `e^{iΦ[G]} − z e^{iΦ[Ĝ]}` is null, and the OS
  Hilbert space is spanned by time-zero data.
* `dampedForm_eq`, `shift_exponent_identity`, `transferRatio_eq_ladderShift` —
  **Eqs. 2.40–2.41**: the reconstructed contraction acts on coherent vectors by
  `e^{−βH/ℏ}e^{iφ[f]}Ω = e^{−(ℏκ/4)[⟨f,ω⁻¹f⟩−⟨f̂,ω⁻¹f̂⟩]}·e^{iφ[f̂]}Ω` with the damped
  smearing `f̂ = e^{−βcω}f`.  Per mode, the Gaussian ratio's exponent
  `(1 − e^{−2x})·f²/ω` equals the ladder-conjugation shift `2e^{−x}·sinh x·f²/ω` of the
  Fock verification Eq. 2.41 — the paper's "indeed" is the hyperbolic identity
  `2e^{−x}sinh x = 1 − e^{−2x}`.
* `transferRatio_cocycle` — the Gaussian ratios compose along the damping semigroup,
  `z(β₁, f̂_{β₂})·z(β₂, f) = z(β₁+β₂, f)` — the consistency making Eq. 2.40 a one-parameter
  contraction semigroup on the coherent span.

**Honest layering.**  Exact exponential/hyperbolic and finite-sum algebra per frequency
mode.  The Minkowski/Gaussian measure itself, its `S'(ℝ^{D+1})` support, the residue
computation of Eq. 2.27, the ε-density of sharp-time vectors (Eq. 2.37 — whose approximant
is a fixed-step Riemann sum in the sense of `Mathematics.LeftRiemannSum`), and the operator
BCH steps of Eqs. 2.17–2.20 are recorded, not re-derived; the abstract Weyl/annihilator
layer that the conjugation Eq. 2.41 rides is `WeylAnnihilatorSystem`, and the Euclidean
weight `e^{−½⟨F,CF⟩}` is the damping sector of `QFT.PathIntegral.MeasureModel`.

## References

* T. Lang, K. Liegener, T. Thiemann, *Hamiltonian renormalisation II: renormalisation flow
  of 1+1 dimensional free scalar fields*, arXiv:1711.06727v2, §§2.3–2.4 (Eqs. 2.24–2.41).
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Physlib.QFT.HamiltonianRenormalisation

/-! ## §A — the reflected kernel factorizes (Eqs. 2.24, 2.31) -/

/-- **The reflected kernel loses its modulus** (the mechanism of Eq. 2.31): for positive
times on opposite sides of the reflection, `e^{−ω|(−s)−t|} = e^{−ωs}·e^{−ωt}`. -/
theorem reflectedKernel_factorizes (ω s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.exp (-(ω * |(-s) - t|)) = Real.exp (-(ω*s)) * Real.exp (-(ω*t)) := by
  have habs : |(-s) - t| = s + t := by
    rw [show (-s) - t = -(s + t) by ring, abs_neg, abs_of_nonneg (by linarith)]
  rw [habs, ← Real.exp_add]
  ring_nf

/-- **The history pairing of a sharp-time family**, per frequency mode: two families of
times and amplitudes pair through the kernel `e^{−ω|t−s|}` (the `ℏκ/(2ω)` dressing of the
covariance Eq. 2.27 is a global constant, kept outside). -/
noncomputable def historyPairing (ω : ℝ) {n m : ℕ} (t : Fin n → ℝ) (F : Fin n → ℝ)
    (s : Fin m → ℝ) (G : Fin m → ℝ) : ℝ :=
  ∑ k, ∑ l, Real.exp (-(ω * |t k - s l|)) * (F k * G l)

/-- **Eq. 2.31**: the reflected history pairing factorizes into damped time-zero data —
the double sum splits as a product of two exponentially damped amplitude sums. -/
theorem reflectedPairing_factorizes (ω : ℝ) {n m : ℕ} (t : Fin n → ℝ) (F : Fin n → ℝ)
    (s : Fin m → ℝ) (G : Fin m → ℝ) (ht : ∀ k, 0 ≤ t k) (hs : ∀ l, 0 ≤ s l) :
    historyPairing ω (fun k => -(t k)) F s G
      = (∑ k, Real.exp (-(ω * t k)) * F k) * (∑ l, Real.exp (-(ω * s l)) * G l) := by
  unfold historyPairing
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [reflectedKernel_factorizes ω (t k) (s l) (ht k) (hs l)]
  ring

/-- **Eq. 2.32**: a positive-time family pairs with any reflected family exactly as its
damped time-zero projection does — the single sharp time `0` with amplitude
`Σ_l e^{−ωs_l}G_l`. -/
theorem reflectedPairing_eq_timeZero (ω : ℝ) {n m : ℕ} (t : Fin n → ℝ) (F : Fin n → ℝ)
    (s : Fin m → ℝ) (G : Fin m → ℝ) (ht : ∀ k, 0 ≤ t k) (hs : ∀ l, 0 ≤ s l) :
    historyPairing ω (fun k => -(t k)) F s G
      = historyPairing ω (fun k => -(t k)) F (fun _ : Fin 1 => 0)
          (fun _ => ∑ l, Real.exp (-(ω * s l)) * G l) := by
  rw [reflectedPairing_factorizes ω t F s G ht hs,
    reflectedPairing_factorizes ω t F (fun _ : Fin 1 => 0)
      (fun _ => ∑ l, Real.exp (-(ω * s l)) * G l) ht (fun _ => le_refl 0)]
  simp

/-! ## §B — the null-vector reduction of the Weyl form (Eqs. 2.30, 2.33–2.34) -/

/-- **Eqs. 2.33–2.34**: for a Gaussian generating functional the reflection-positive Weyl
form is `⟨e^{iΦ[F]}, e^{iΦ[G]}⟩ = e^{−½q_G}·e^{−½q_F}·e^{c}` with `c = ⟨θF, CG⟩`; whenever
the cross pairing agrees with that of the time-zero projection (Eq. 2.32), the form
reduces with the explicit factor `z = e^{−½(q_G − q_{Ĝ})}` — the statement that
`e^{iΦ[G]} − z·e^{iΦ[Ĝ]}` is a null vector. -/
theorem weylForm_timeZero_reduction (qF qG qĜ c : ℝ) :
    Real.exp (-(1/2)*qG) * Real.exp (-(1/2)*qF) * Real.exp c
      = Real.exp (-(1/2)*(qG - qĜ))
        * (Real.exp (-(1/2)*qĜ) * Real.exp (-(1/2)*qF) * Real.exp c) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  ring_nf

/-! ## §C — the contraction on coherent vectors (Eqs. 2.39–2.41) -/

/-- The damped quadratic form: per mode, `⟨e^{−x}f, ω⁻¹ e^{−x}f⟩ = e^{−2x}·f²/ω`. -/
theorem dampedForm_eq (ω f x : ℝ) :
    (Real.exp (-x) * f)^2 / ω = Real.exp (-(2*x)) * (f^2 / ω) := by
  rw [mul_pow, mul_div_assoc, sq, ← Real.exp_add]
  ring_nf

/-- **The hyperbolic identity behind Eq. 2.41's verification**:
`2e^{−x}·sinh x = 1 − e^{−2x}`. -/
theorem shift_exponent_identity (x : ℝ) :
    2 * Real.exp (-x) * Real.sinh x = 1 - Real.exp (-(2*x)) := by
  have h1 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (-x) * Real.exp (-x) = Real.exp (-(2*x)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [Real.sinh_eq]
  linear_combination h1 - h2

/-- **Eq. 2.40 ⟺ Eq. 2.41**: the exponent of the Gaussian transfer ratio,
`(ℏκ/4)[⟨f,ω⁻¹f⟩ − ⟨f̂,ω⁻¹f̂⟩]` with `f̂ = e^{−x}f`, equals the ladder-conjugation shift
`(ℏκ/2)·e^{−x}·sinh x·⟨f,ω⁻¹f⟩` produced by the Fock computation — the paper's
verification that the reconstructed contraction is the original one. -/
theorem transferRatio_eq_ladderShift (a ω f x : ℝ) :
    a/4 * (f^2/ω - (Real.exp (-x) * f)^2/ω)
      = a/2 * (Real.exp (-x) * Real.sinh x) * (f^2/ω) := by
  rw [dampedForm_eq ω f x]
  have h := shift_exponent_identity x
  linear_combination (-(a/4 * (f^2/ω))) * h

/-- **The Gaussian transfer ratios form a cocycle** (the semigroup consistency of
Eq. 2.40): along any damping semigroup `damp` on the smearing data, the ratios compose,
`z(β₁, f̂_{β₂})·z(β₂, f) = z(β₁+β₂, f)` — so the coherent transfer law defines a
one-parameter semigroup on the coherent span. -/
theorem transferRatio_cocycle {E : Type*} (q : E → ℝ) (damp : ℝ → E → E)
    (hdamp : ∀ β₁ β₂ f, damp β₁ (damp β₂ f) = damp (β₁+β₂) f)
    (a β₁ β₂ : ℝ) (f : E) :
    Real.exp (-(a/4) * (q (damp β₂ f) - q (damp β₁ (damp β₂ f))))
      * Real.exp (-(a/4) * (q f - q (damp β₂ f)))
      = Real.exp (-(a/4) * (q f - q (damp (β₁+β₂) f))) := by
  rw [hdamp, ← Real.exp_add]
  ring_nf

end Physlib.QFT.HamiltonianRenormalisation

end

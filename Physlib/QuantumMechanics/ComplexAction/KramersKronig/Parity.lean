/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.KramersKronig.EntropyHamiltonian

/-!
# Kramers–Kronig parity: dispersion is even, absorption is odd

This file improves `KramersKronig.EntropyHamiltonian` (which had only the abstract involution
`Hilb² = −id`) with the **parity structure** of the Kramers–Kronig relations from **M. Kozak,
V. Zhikharev, P. Puga, V. Loya, *The Kramers–Kronig Relations: Validation via Calculation
Technique*, IJISET 4(12) (2017)**.

For a causal linear response `χ(ω) = ξ(ω) + i η(ω)`, the real part (dispersion / susceptibility
`ξ`) is **even** and the imaginary part (absorption `η`) is **odd**:

  `ξ(−ω) = ξ(ω)`,   `η(−ω) = −η(ω)`,

and the Hilbert transform **changes parity** (even ↔ odd) — which is what makes the two
equivalent KK integral forms (Kozak Eqs. 2, 3) interconvert. We formalize the **algebraic /
parity** content (not the principal-value integral, which is out of scope here, as in
`KramersKronig.EntropyHamiltonian`).

## Main results

* `FnEven`, `FnOdd` — even/odd functions of frequency.
* `ParityHilbertTransform` — the Hilbert transform with `Hilb² = −id` *and* the parity-changing
  axioms (`even → odd`, `odd → even`).
* `kk_dispersion_even_absorption_odd` — **`ξ` even ⟹ `η = Hilb ξ` is odd**: the absorption is odd
  when the dispersion is even (the physical KK parity).
* `hilb_parity_consistent` — applying the Hilbert transform twice preserves parity, consistent
  with `Hilb² = −id` (even → odd → even).
* `absorption_zero_at_zero_freq` — **`η(0) = 0`**: the absorption (entropy production) vanishes at
  zero frequency, because an odd function vanishes at the origin. For the arc: the entropy
  production has no static (`ω = 0`) component.

## References

* M. Kozak et al., IJISET 4(12) (2017) (KK parity, dielectric susceptibility);
  `KramersKronig.EntropyHamiltonian` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity

/-! ## §A — even/odd functions and the parity-Hilbert transform -/

/-- **An even function of frequency** `f(−ω) = f(ω)` (the dispersion / real susceptibility). -/
def FnEven (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = f x

/-- **An odd function of frequency** `f(−ω) = −f(ω)` (the absorption / imaginary part). -/
def FnOdd (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = -f x

/-- **The Kramers–Kronig (parity) Hilbert transform** on functions of frequency: `Hilb² = −id`
together with the parity-changing property (even ↔ odd). -/
structure ParityHilbertTransform where
  /-- The Hilbert transform. -/
  hilb : (ℝ → ℝ) → (ℝ → ℝ)
  /-- `Hilb² = −id` (the Kramers–Kronig involution). -/
  hilb_hilb : ∀ f, hilb (hilb f) = -f
  /-- The Hilbert transform maps **even** functions to **odd** ones. -/
  hilb_even_to_odd : ∀ f, FnEven f → FnOdd (hilb f)
  /-- The Hilbert transform maps **odd** functions to **even** ones. -/
  hilb_odd_to_even : ∀ f, FnOdd f → FnEven (hilb f)

/-! ## §B — the KK parity relations -/

/-- **Even dispersion ⟹ odd absorption**: if the dispersion `ξ` is even and the absorption is
its Hilbert transform (`η = Hilb ξ`), then `η` is odd — the parity structure of the
Kramers–Kronig relations. -/
theorem kk_dispersion_even_absorption_odd (H : ParityHilbertTransform) {ξ η : ℝ → ℝ}
    (hξ : FnEven ξ) (h : η = H.hilb ξ) : FnOdd η := by
  rw [h]; exact H.hilb_even_to_odd ξ hξ

/-- **Odd absorption ⟹ even dispersion** (the reciprocal KK relation `ξ = −Hilb η`): if `η` is
odd then `Hilb η` is even. -/
theorem kk_absorption_odd_dispersion_even (H : ParityHilbertTransform) {η : ℝ → ℝ}
    (hη : FnOdd η) : FnEven (H.hilb η) :=
  H.hilb_odd_to_even η hη

/-- **`−f` keeps the parity of `f`** (even stays even). -/
theorem fnEven_neg {f : ℝ → ℝ} (hf : FnEven f) : FnEven (-f) := by
  intro x
  show -(f (-x)) = -(f x)
  rw [hf x]

/-- **Parity is consistent with `Hilb² = −id`**: applying the Hilbert transform twice to an even
function returns an even function (`even → odd → even`), matching `−f` (which is even). -/
theorem hilb_parity_consistent (H : ParityHilbertTransform) {ξ : ℝ → ℝ} (hξ : FnEven ξ) :
    FnEven (H.hilb (H.hilb ξ)) := by
  rw [H.hilb_hilb]
  exact fnEven_neg hξ

/-! ## §C — consequence: the absorption vanishes at zero frequency -/

/-- **An odd function vanishes at the origin** `f(0) = 0`. -/
theorem fnOdd_zero_at_zero {f : ℝ → ℝ} (hf : FnOdd f) : f 0 = 0 := by
  have h := hf 0
  rw [neg_zero] at h
  linarith

/-- **The absorption (entropy production) vanishes at zero frequency** `η(0) = 0`: being odd (KK
parity), the imaginary part of the causal response has no static `ω = 0` component. For the arc:
the entropy production has no zero-frequency (DC) part. -/
theorem absorption_zero_at_zero_freq (H : ParityHilbertTransform) {ξ η : ℝ → ℝ}
    (hξ : FnEven ξ) (h : η = H.hilb ξ) : η 0 = 0 :=
  fnOdd_zero_at_zero (kk_dispersion_even_absorption_odd H hξ h)

end Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity

end

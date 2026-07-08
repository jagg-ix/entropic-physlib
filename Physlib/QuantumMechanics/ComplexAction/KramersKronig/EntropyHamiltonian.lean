/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BogoljubovPoincareActionConsistency

/-!
# Kramers–Kronig: Hamiltonian ↔ entropy production are mutually Hilbert transforms

This file completes `Bogoliubov.BogoljubovPoincareActionConsistency` — where the complex action's real part
`S_R` (the order-parameter / Poincaré phase) was used with the imaginary part `S_I` set to `0` —
by formalizing the result of **M. Parker, C. Jeynes, *Relating a System's Hamiltonian to Its
Entropy Production Using a Complex Time Approach*, Entropy 25 (2023) 629**: the real and
imaginary parts of the complex dispersion (the Hamiltonian `H_R` and the entropy production
`S_I`) are **not independent** — they are **mutually Hilbert transforms of each other**
(Kramers–Kronig), with `S` the Wick-rotated complex conjugate of `H`.

## Scope note

We formalize the **algebraic core** of the Hilbert/Kramers–Kronig relation — the defining
involution property `Hilb² = −id` and the conjugate-pair consequence — *not* the analytic
singular-integral realisation `Hilb f(ω) = (1/π) p.v. ∫ f(ω')/(ω−ω') dω'` (which needs
operator-analytic infrastructure not on this branch; cf. the Carleson Hilbert transform, which
is the `Lᵖ` operator, not the KK relation). The `Hilb² = −id` property is exactly the property
of the Hilbert transform that the paper uses to relate real and imaginary parts.

## Main results

* `HilbertTransform` — a Hilbert transform on `V`, abstracted by `Hilb² = −id`.
* `kk_pair_symm` — **the Kramers–Kronig pair is symmetric**: `f_I = Hilb f_R ⟹ f_R = −Hilb f_I`;
 the real and imaginary parts are mutually Hilbert transforms.
* `entropy_hamiltonian_mutual_hilbert` — Parker–Jeynes: with `S_I = Hilb H_R`, also
 `H_R = −Hilb S_I` — Hamiltonian and entropy production are mutually Hilbert transforms.
* `reversible_iff_hilb_zero` — **reversible ⟺ `Hilb H_R = 0`**: zero entropy production (the
 alpha particle) iff the Hilbert transform of the Hamiltonian vanishes; non-zero is the
 irreversible (black-hole) case.
* `reversible_complexActionWeight_unimodular` / `irreversible_complexActionWeight_damped` — the
 reversible fiber (`S_I = 0`) is the pure phase `e^{iS_R/ℏ}` of `Bogoliubov.BogoljubovPoincareActionConsistency`;
 the irreversible case (`S_I = Hilb H_R > 0`) adds the entropic damping `e^{−S_I/ℏ} < 1`.

## References

* M. Parker, C. Jeynes, Entropy 25 (2023) 629 (Hamiltonian ↔ entropy production via complex
 time, Hilbert/Kramers–Kronig); J. S. Toll (1956). `QFT.Wick.Consistency`,
 `Bogoliubov.BogoljubovPoincareActionConsistency` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Physlib.QFT.Wick.Consistency

namespace Physlib.QuantumMechanics.ComplexAction.KramersKronig.EntropyHamiltonian

/-! ## §A — the Hilbert transform and the Kramers–Kronig pair -/

/-- **A Hilbert transform** on `V`, abstracted by its defining algebraic property `Hilb² = −id`
(the property used in the Kramers–Kronig relations to interrelate real and imaginary parts). -/
structure HilbertTransform (V : Type*) [AddCommGroup V] where
  /-- The Hilbert transform map. -/
  hilb : V → V
  /-- **`Hilb² = −id`** — the defining involution of the Hilbert transform. -/
  hilb_hilb : ∀ f, hilb (hilb f) = -f

variable {V : Type*} [AddCommGroup V]

/-- **The Kramers–Kronig pair is symmetric**: if the imaginary part is the Hilbert transform of
the real part (`f_I = Hilb f_R`), then the real part is *minus* the Hilbert transform of the
imaginary part (`f_R = −Hilb f_I`). Real and imaginary parts are mutually Hilbert transforms. -/
theorem kk_pair_symm (H : HilbertTransform V) {fR fI : V} (h : fI = H.hilb fR) :
    fR = -H.hilb fI := by
  rw [h, H.hilb_hilb, neg_neg]

/-! ## §B — Hamiltonian ↔ entropy production (Parker–Jeynes) -/

/-- **The Hamiltonian and entropy production are mutually Hilbert transforms** (Parker–Jeynes):
if the entropy production is the Hilbert transform of the Hamiltonian (`S_I = Hilb H_R`), then
the Hamiltonian is minus the Hilbert transform of the entropy production (`H_R = −Hilb S_I`).
`S` is the Wick-rotated complex conjugate of `H`. -/
theorem entropy_hamiltonian_mutual_hilbert (H : HilbertTransform V) {hamiltonian entropyProd : V}
    (hkk : entropyProd = H.hilb hamiltonian) : hamiltonian = -H.hilb entropyProd :=
  kk_pair_symm H hkk

/-- **Reversible ⟺ `Hilb H_R = 0`**: zero entropy production (the absolutely stable alpha
particle, trivially reversible) iff the Hilbert transform of the Hamiltonian vanishes. Non-zero
`Hilb H_R` is the irreversible (black-hole) case. -/
theorem reversible_iff_hilb_zero (H : HilbertTransform V) {hamiltonian entropyProd : V}
    (hkk : entropyProd = H.hilb hamiltonian) :
    entropyProd = 0 ↔ H.hilb hamiltonian = 0 := by
  rw [hkk]

/-! ## §C — the complex action weight: reversible phase vs irreversible damping -/

/-- **Reversible fiber** (`S_I = 0`, alpha particle, `Hilb H_R = 0`): the complex action weight is
the pure phase `e^{iS_R/ℏ}` (`‖·‖ = 1`) of `Bogoliubov.BogoljubovPoincareActionConsistency`. -/
theorem reversible_complexActionWeight_unimodular (S_R ℏ : ℝ) :
    ‖complexActionWeight S_R 0 ℏ‖ = 1 :=
  norm_complexActionWeight_zero_imag S_R ℏ

/-- **Irreversible case** (`S_I = Hilb H_R > 0`, black hole): the complex action weight acquires
the entropic damping `e^{−S_I/ℏ} < 1` — irreversibility, determined from the Hamiltonian by the
Kramers–Kronig (Hilbert) relation. -/
theorem irreversible_complexActionWeight_damped (S_R S_I ℏ : ℝ) (hS_I : 0 < S_I) (hℏ : 0 < ℏ) :
    ‖complexActionWeight S_R S_I ℏ‖ < 1 := by
  rw [norm_complexActionWeight]
  have hneg : -(S_I / ℏ) < 0 := by
    have : 0 < S_I / ℏ := div_pos hS_I hℏ
    linarith
  calc Real.exp (-(S_I / ℏ)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    _ = 1 := Real.exp_zero

end Physlib.QuantumMechanics.ComplexAction.KramersKronig.EntropyHamiltonian

end

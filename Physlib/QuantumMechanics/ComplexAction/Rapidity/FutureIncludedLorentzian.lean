/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-!
# The future-included theory and the Minkowski double cone (Nagao–Nielsen)

The Nagao–Nielsen **future-included** complex action theory (FIT) includes both a past
boundary `|A(T_A)⟩` at `T_A = −∞` and a future boundary `|B(T_B)⟩` at `T_B = +∞`, with the
present `t` between them; the **future-not-included** theory (FNI) keeps only the past
boundary. The momentum relation `p = m q̇` (`PathIntegral.MomentumPathIntegral.momentum_relation`) is
valid in FIT but breaks to `p = m_eff q̇` in FNI (arXiv:1304.4017).

This file extends the Minkowski/causality `lorentzianForm` `L(q) = (Re q)² − (Im q)²` of
`ComplexDelta.Convergence` with the **two-boundary / double-cone structure** that mirrors
FIT, and records its links to the earlier time-operator and dissipation formalism.

* `timelikeFuture`, `timelikePast` — the two sheets of the timelike cone `L > 0`, split by
  the sign of `Re q` (the "time" coordinate). `timelike_re_ne_zero`: a timelike `q` has
  `Re q ≠ 0`, so `timelike_future_or_past` is an **exclusive** alternative.
* `timelikeFuture_neg_iff` — **time reversal** `q ↦ −q` swaps the future and past sheets:
  this is the `A ↔ B` (past ↔ future boundary) symmetry of FIT. `lorentzianForm_neg`,
  `lorentzianForm_conj`: `L` is invariant under reflection and conjugation.
* `timelike_mul_I_iff_spacelike` — **Wick rotation** `q ↦ i q` exchanges the timelike
  (causal) and spacelike (forbidden) regions (`lorentzianForm_mul_I`): the rotation to
  imaginary/Euclidean time underlying the Feynman–Kac form of the path integral.

## The links this makes precise

* **FIT ↔ double cone.** The full timelike cone `L > 0 = timelikeFuture ∪ timelikePast`
  uses *both* sheets; FNI uses one. The `A ↔ B` time-reflection of FIT is the
  `q ↦ −q` exchange of the two sheets (`timelikeFuture_neg_iff`). The convergence cone of
  the complex-action delta (Eq. 2.10, `gaussian_lt_one_iff`) is exactly this causal structure, so the
  momentum/delta machinery and FIT live on the same Minkowski domain.
* **Herglotz (dissipation).** The imaginary action `S_I` is the dissipative part of the
  complex-action action; its rate `dS_I/dt = Γ/2` is the Bender decay width
  (`ComplexAction.BenderIdentity.widthFromRate`). The Wick exchange `i` here is what turns
  the reversible (timelike, `L > 0`) part into the damping (spacelike, `L < 0`) part — the
  Herglotz action-dependent / dissipative term. Positivity of the imaginary mass
  (`PathIntegral.MomentumPathIntegral.momentum_integral_converges_iff`, `Im m > 0`) is the same
  damping-sign condition.
* **Misra (time operator / arrow).** FNI keeps a single temporal boundary — a definite
  arrow of time, like the irreversible `Λ`-dynamics of Misra–Prigogine–Courbage; FIT
  restores past↔future symmetry. `Re q` is the "time" axis whose sign label
  (`timelikeFuture`/`Past`) is the orientation the conjugate time operator
  (`RelationalTime.LiouvillianAgeOperator`, `i[L,T] = I`) measures.

Reference: K. Nagao, H. B. Nielsen, arXiv:1304.4017 (future-not-included) and Prog. Theor.
Phys. **126**(6) (2011) 1021–1049 §2.5 (the delta and its cone).
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian

open ComplexDelta.Convergence

/-- The **timelike** (causal) condition `L(q) > 0`. -/
def timelike (q : ℂ) : Prop := 0 < lorentzianForm q

/-- The **spacelike** (forbidden) condition `L(q) < 0`. -/
def spacelike (q : ℂ) : Prop := lorentzianForm q < 0

/-- **Future-pointing timelike**: causal with positive "time" coordinate `Re q > 0` — the
future boundary sheet of FIT. -/
def timelikeFuture (q : ℂ) : Prop := timelike q ∧ 0 < q.re

/-- **Past-pointing timelike**: causal with negative "time" coordinate `Re q < 0` — the
past boundary sheet of FIT. -/
def timelikePast (q : ℂ) : Prop := timelike q ∧ q.re < 0

/-- `L` is invariant under reflection `q ↦ −q`. -/
@[simp] theorem lorentzianForm_neg (q : ℂ) : lorentzianForm (-q) = lorentzianForm q := by
  simp [lorentzianForm]

/-- `L` is invariant under complex conjugation (it depends only on `(Re q)²` and `(Im q)²`). -/
@[simp] theorem lorentzianForm_conj (q : ℂ) :
    lorentzianForm (starRingEnd ℂ q) = lorentzianForm q := by
  simp [lorentzianForm, Complex.conj_re, Complex.conj_im]

/-- **A timelike `q` has `Re q ≠ 0`**: `L(q) > 0` forces `(Re q)² > (Im q)² ≥ 0`. So the
"time" coordinate never vanishes on the causal cone. -/
theorem timelike_re_ne_zero {q : ℂ} (h : timelike q) : q.re ≠ 0 := by
  intro h0
  rw [timelike, lorentzianForm, h0] at h
  nlinarith [sq_nonneg q.im]

/-- **The causal cone is the disjoint union of the future and past sheets** (exclusive,
since `Re q ≠ 0`): every timelike `q` is future-pointing or past-pointing. This is the
two-boundary structure FIT integrates over. -/
theorem timelike_future_or_past {q : ℂ} (h : timelike q) :
    timelikeFuture q ∨ timelikePast q := by
  rcases lt_or_gt_of_ne (timelike_re_ne_zero h) with hlt | hgt
  · exact Or.inr ⟨h, hlt⟩
  · exact Or.inl ⟨h, hgt⟩

/-- **Time reversal `q ↦ −q` swaps the future and past sheets** — the `A ↔ B` (past ↔
future boundary) reflection of the future-included theory. -/
theorem timelikeFuture_neg_iff (q : ℂ) : timelikeFuture (-q) ↔ timelikePast q := by
  simp only [timelikeFuture, timelikePast, timelike, lorentzianForm_neg, Complex.neg_re,
    neg_pos]

/-- **Wick rotation `q ↦ i q` exchanges causal and forbidden regions**: `i q` is spacelike
iff `q` is timelike (`L(iq) = −L(q)`). This is the rotation to imaginary/Euclidean time
that turns the oscillatory weight into the Feynman–Kac (damping) weight. -/
theorem timelike_mul_I_iff_spacelike (q : ℂ) : spacelike (Complex.I * q) ↔ timelike q := by
  rw [spacelike, timelike, lorentzianForm_mul_I, neg_lt_zero]

end Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian

end

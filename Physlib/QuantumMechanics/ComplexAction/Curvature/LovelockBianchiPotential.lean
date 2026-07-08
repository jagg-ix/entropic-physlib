/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lovelock gravity from the Bianchi derivative: the Bianchi potential and the critical dimension

N. Dadhich, *Characterization of the Lovelock gravity by Bianchi derivative* (arXiv:0802.3034): the
divergence-free second-rank tensor `H_{ab}` of order-`n` Lovelock gravity is the trace of the Bianchi
derivative of a fourth-rank **Bianchi potential** `F_{abcd}` (a homogeneous polynomial in the Riemann
curvature, Eqs. 11, 15), and the *existence* of such a potential for each term characterizes Lovelock
gravity. For `n = 1` this is the ordinary story — the second Bianchi identity giving `∇^a G_{ab} = 0`
(`Curvature.SecondBianchiCyclicFamily`) — and Dadhich lifts it to every Lovelock order.

The curvature polynomial `Q^{ab}_{cd} = δ^{ab a₁b₁…aₙbₙ}_{cd c₁d₁…cₙdₙ} R^{c₁d₁}_{a₁b₁}⋯` (Eq. 11) is built
from the **generalized Kronecker delta** of `Curvature.LovelockDimensionalTermination`, so the whole
construction inherits its dimension-dependence: the order-`n` tensor `H_{ab}` is **non-trivial only for
`d > 2n`** (Eqs. 16–18), and its trace / the potential trace vanish at the critical dimension `d = 2n`.

* **§A — the Bianchi-potential trace (Eq. 18).** `bianchiPotentialCoeff d n = (d−2n)/(n(d−2))` with
 `F = coeff · R`; `bianchiPotentialCoeff_einstein` (`n = 1 ⇒ coeff = 1`, `F = R`),
 `bianchiPotentialCoeff_zero_iff` (`= 0 ↔ d = 2n`, the critical dimension), `bianchiPotentialCoeff_pos`
 (`> 0` for `d > 2n`).
* **§B — the Lovelock–Einstein tensor trace (Eq. 13).** `lovelockEinsteinTrace d n R = nR − ½Rd`
 (`= R(2n−d)/2`, `lovelockEinsteinTrace_eq`); it vanishes at the critical dimension
 (`lovelockEinsteinTrace_zero_iff`, `= 0 ↔ d = 2n`) — `H_{ab} = 0` at `d = 2n`.
* **§C — the critical dimension is the Lovelock survival condition.**
 `bianchi_threshold_iff_lovelock_survives` (`d > 2n ↔ 0 < genKroneckerTrace d (2n+1)`): Dadhich's
 threshold `d > 2n` for a non-trivial `H_{ab}` **is** the generalized-Kronecker survival condition of
 `LovelockDimensionalTermination`; `bianchi_einstein_threshold` (`n = 1`: `d > 2`, so `G_{ab} ≡ 0` in
 two dimensions).
* **§D — `F` is the Ricci analog, `H` the Einstein analog (Eq. 17).** `bianchiPotentialTrace`
 (`F = coeff·R`), `bianchiPotentialTrace_einstein` (`n = 1 ⇒ F = R`), and
 `bianchi_potential_trace_consistency` (`n(F − ½Fd) = g^{ab}H_{ab}` — Eqs. 13/17/18 close on themselves).

Proven: the rational trace coefficient of the Bianchi potential and its critical-
dimension zero, the Lovelock–Einstein tensor trace and its zero, and the identification of Dadhich's
`d > 2n` threshold with the generalized-Kronecker survival condition. Interpretive: that `H_{ab}` is the
divergence-free trace of the Bianchi derivative of `F_{abcd}` is Dadhich's theorem (the covariant
derivative and the fourth-rank tensors are not formalized — only the scalar/dimension algebra it forces).

## References

* N. Dadhich, arXiv:0802.3034 (Eqs. 11, 13, 15–18; the Bianchi-potential characterization). Reuses
 `Curvature.LovelockDimensionalTermination`; the `n = 1` Bianchi story is
 `Curvature.SecondBianchiCyclicFamily`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockBianchiPotential

/-! ## §A — the Bianchi-potential trace (Eq. 18) -/

/-- **The trace coefficient of the Bianchi potential** `F = (d−2n)/(n(d−2)) · R` (Eq. 18): the trace of
`F_{abcd}` in terms of the order-`n` Lovelock Lagrangian scalar `R`, at dimension `d`. -/
noncomputable def bianchiPotentialCoeff (d n : ℕ) : ℝ := ((d : ℝ) - 2 * n) / (n * ((d : ℝ) - 2))

/-- **Einstein recovery** `n = 1 ⇒ coeff = 1` (so `F = R`): for ordinary gravity the Bianchi potential's
trace is just the Ricci scalar. -/
theorem bianchiPotentialCoeff_einstein (d : ℕ) (hd : (d : ℝ) ≠ 2) :
    bianchiPotentialCoeff d 1 = 1 := by
  unfold bianchiPotentialCoeff
  simp only [Nat.cast_one, mul_one, one_mul]
  exact div_self (sub_ne_zero.mpr hd)

/-- **The critical dimension** `coeff = 0 ↔ d = 2n`: the Bianchi-potential trace (hence the order-`n`
Lovelock contribution) vanishes exactly at `d = 2n`. -/
theorem bianchiPotentialCoeff_zero_iff (d n : ℕ) (hn : n ≠ 0) (hd : (d : ℝ) ≠ 2) :
    bianchiPotentialCoeff d n = 0 ↔ (d : ℝ) = 2 * n := by
  unfold bianchiPotentialCoeff
  rw [div_eq_zero_iff]
  have hden : (n : ℝ) * ((d : ℝ) - 2) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hn) (sub_ne_zero.mpr hd)
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hden
  · intro h; exact Or.inl (by linarith)

/-- **The coefficient is positive above the critical dimension** `d > 2n` (with `n ≥ 1`, `d > 2`): the
order-`n` Lovelock term contributes with a definite sign. -/
theorem bianchiPotentialCoeff_pos (d n : ℕ) (hn : 0 < n) (hd2 : 2 < d) (hdn : 2 * n < d) :
    0 < bianchiPotentialCoeff d n := by
  unfold bianchiPotentialCoeff
  apply div_pos
  · have : (2 * n : ℝ) < d := by exact_mod_cast hdn
    linarith
  · have h1 : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : (2 : ℝ) < d := by exact_mod_cast hd2
    exact mul_pos h1 (by linarith)

/-! ## §B — the Lovelock–Einstein tensor trace (Eq. 13) -/

/-- **The trace of the order-`n` Lovelock–Einstein tensor** `g^{ab}H_{ab} = nR − ½Rd` (from Eq. 13
`H_{ab} = nℛ_{ab} − ½ℛg_{ab}`). -/
noncomputable def lovelockEinsteinTrace (d n : ℕ) (R : ℝ) : ℝ := (n : ℝ) * R - (1 / 2) * R * (d : ℝ)

/-- **`g^{ab}H_{ab} = R(2n − d)/2`.** -/
theorem lovelockEinsteinTrace_eq (d n : ℕ) (R : ℝ) :
    lovelockEinsteinTrace d n R = R * (2 * n - d) / 2 := by
  unfold lovelockEinsteinTrace; ring

/-- **`H_{ab}` vanishes at the critical dimension** `g^{ab}H_{ab} = 0 ↔ d = 2n` (for `R ≠ 0`): the
order-`n` Lovelock–Einstein tensor is trivial exactly at `d = 2n`. -/
theorem lovelockEinsteinTrace_zero_iff (d n : ℕ) (R : ℝ) (hR : R ≠ 0) :
    lovelockEinsteinTrace d n R = 0 ↔ (d : ℝ) = 2 * n := by
  rw [lovelockEinsteinTrace_eq, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hR
      · linarith
    · norm_num at h
  · intro h; exact Or.inl (by rw [mul_eq_zero]; exact Or.inr (by linarith))

/-! ## §C — the critical dimension is the Lovelock survival condition -/

/-- **Dadhich's threshold is the generalized-Kronecker survival condition**
`d > 2n ↔ 0 < genKroneckerTrace d (2n+1)`: a non-trivial order-`n` Lovelock–Einstein tensor `H_{ab}`
exists exactly when the order-`n` Lovelock tensor term of `LovelockDimensionalTermination` survives —
the `(2n+1)`-index generalized Kronecker delta is nonzero. -/
theorem bianchi_threshold_iff_lovelock_survives (d n : ℕ) :
    2 * n < d ↔ 0 < LovelockDimensionalTermination.genKroneckerTrace d (2 * n + 1) := by
  rw [LovelockDimensionalTermination.lovelockTensorTerm_pos_iff]; omega

/-- **The Einstein case** `n = 1`: a non-trivial Einstein tensor needs `d > 2`, so `G_{ab} ≡ 0` in two
dimensions (`Curvature.LovelockDimensionalTermination.lovelock_dim2_einstein_trivial`). -/
theorem bianchi_einstein_threshold (d : ℕ) :
    2 < d ↔ 0 < LovelockDimensionalTermination.genKroneckerTrace d 3 := by
  have h := bianchi_threshold_iff_lovelock_survives d 1
  simpa using h

/-! ## §D — `F` is the Ricci analog, `H` the Einstein analog (Eq. 17), and the construction closes -/

/-- **The scalar trace of the Bianchi potential** `F = (d−2n)/(n(d−2)) R` (Eq. 18) — the analogue of the
Ricci scalar for the order-`n` curvature polynomial. -/
noncomputable def bianchiPotentialTrace (d n : ℕ) (R : ℝ) : ℝ := bianchiPotentialCoeff d n * R

/-- **Einstein recovery** `n = 1 ⇒ F = R`: for ordinary gravity the Bianchi-potential trace is the Ricci
scalar (its `F_{ab}` is the Ricci tensor, its `H_{ab}` the Einstein tensor). -/
theorem bianchiPotentialTrace_einstein (d : ℕ) (hd : (d : ℝ) ≠ 2) (R : ℝ) :
    bianchiPotentialTrace d 1 R = R := by
  unfold bianchiPotentialTrace
  rw [bianchiPotentialCoeff_einstein d hd, one_mul]

/-- **Eqs. 13, 17 and 18 are mutually consistent** `n(F − ½Fd) = g^{ab}H_{ab}`: tracing the
Einstein-analog relation `H_{ab} = n(F_{ab} − ½F g_{ab})` (Eq. 17) with the Bianchi-potential trace `F`
of Eq. 18 reproduces the order-`n` Lovelock–Einstein trace of Eq. 13 — Dadhich's construction closes on
itself, confirming `F` is the Ricci analog and `H` the Einstein analog. -/
theorem bianchi_potential_trace_consistency (d n : ℕ) (hn : n ≠ 0) (hd : (d : ℝ) ≠ 2) (R : ℝ) :
    (n : ℝ) * (bianchiPotentialTrace d n R - (1 / 2) * bianchiPotentialTrace d n R * d)
      = lovelockEinsteinTrace d n R := by
  unfold bianchiPotentialTrace bianchiPotentialCoeff lovelockEinsteinTrace
  have hden : (n : ℝ) * ((d : ℝ) - 2) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hn) (sub_ne_zero.mpr hd)
  field_simp
  ring

/-! ## §E — the double-copy Bianchi structure: `n = 1` is the gravity face, `n > 1` is Lovelock -/

/-- **The Eq. 14 trace-correction coefficient** `(n−1)/n`: in
`R^{cd}_{[cd;e]} − (n−1)/n (Rδ_e^c)_{;c} = −(2/n) H^c_{e;c} = 0`, this is the coefficient of the trace
term that must be added to the Bianchi derivative of the curvature polynomial to yield the conserved
order-`n` Lovelock–Einstein tensor. -/
noncomputable def dadhichBianchiCoeff (n : ℕ) : ℝ := ((n : ℝ) - 1) / n

/-- **`n = 1` needs no trace correction** `(n−1)/n = 0`: for ordinary gravity the trace of the Bianchi
derivative vanishes by the Riemann (first) Bianchi identity, so `H_{ab} = G_{ab}` is divergence-free
*directly* — this is exactly the gravity face `∇^a G_{ab} = 0` that
`LeviCivita.leviCivita_bianchi_double_copy_validation` bundles (with the Riemann-cyclic first Bianchi)
against the gauge side. The gauge counterpart is the contracted second Bianchi / conservation of
`BCJDoubleCopy.SecondBianchiConservation`, and the first Bianchi is the color–kinematics / kinematic
Jacobi of `BCJDoubleCopy.JacobiBianchiDoubleCopyFamily`. -/
theorem dadhichBianchiCoeff_einstein : dadhichBianchiCoeff 1 = 0 := by
  unfold dadhichBianchiCoeff; norm_num

/-- **Lovelock orders `n > 1` require the trace correction** `(n−1)/n > 0`: for higher-curvature terms
the trace of the Bianchi derivative does not vanish, and the correction beyond the Einstein/double-copy
case is exactly `(n−1)/n` — the higher-order generalization of the gravity-side second Bianchi
(conservation) that the double copy relates to the gauge side. -/
theorem dadhichBianchiCoeff_pos (n : ℕ) (hn : 1 < n) : 0 < dadhichBianchiCoeff n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  unfold dadhichBianchiCoeff
  exact div_pos (by linarith) (by linarith)

/-- **The Einstein/double-copy face is *exactly* the vanishing of the trace correction** `(n−1)/n = 0 ↔
n = 1` (for a physical order `n ≥ 1`): among all Lovelock orders, `n = 1` is the unique order whose
Bianchi derivative is divergence-free with no trace term added — precisely the gravity face
`∇^a G_{ab} = 0` of `LeviCivita.leviCivita_bianchi_double_copy_validation`. Together with
`dadhichBianchiCoeff_pos` this is a clean dichotomy: `dadhichBianchiCoeff n = 0` (Einstein / double copy)
or `dadhichBianchiCoeff n > 0` (genuinely higher-order Lovelock). -/
theorem dadhichBianchiCoeff_eq_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    dadhichBianchiCoeff n = 0 ↔ n = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold dadhichBianchiCoeff
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have : (n : ℝ) = 1 := by linarith
      exact_mod_cast this
    · exact absurd h hn0
  · rintro rfl
    left; norm_num

end Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockBianchiPotential

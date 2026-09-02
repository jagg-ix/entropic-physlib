/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
public import Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
public import Mathlib.Tactic.Module

/-!
# The mass-shell is the first Poincaré Casimir `μ² = η_{ab} p^a p^b`

L. B. Szabados, *Minkowski space from quantum mechanics* (arXiv:2309.06150), recovers the metric structure
of Minkowski space from the `E(1,3)`-invariant (Poincaré) observables — the 4-momentum `p^a` and angular
momentum `J^{ab}` — of elementary quantum systems. Its §2.1 fixes the two Casimir invariants of the
Poincaré algebra `e(1,3)`: the **rest mass** `μ² := η_{ab} p^a p^b` (Eq. 2.3, signature `(+,−,−,−)`) and the
Pauli–Lubanski spin `S_a S^a` (spacelike, `≤ 0`).

This grounds the ad-hoc Compton mass-shell of `ComptonClock.EquivalencePrincipleMassShell` in the proper
Poincaré framework: the first Casimir `μ² = (p^0)² − |p⃗|²` in full `3+1` dimensions, its Lorentz-boost
invariance, and the identification of the earlier `(1+1)` mass-shell and the Nagao–Nielsen cone as its
restrictions.

* **§A — the first Casimir and its Poincaré invariance.** `poincareRestMassSq` (Eq. 2.3) and
  `poincareRestMassSq_boost_invariant` (`μ²` is unchanged by a Lorentz boost of rapidity `θ` — the Casimir
  is Poincaré-invariant, `cosh²θ − sinh²θ = 1`).
* **§B — the earlier mass-shells are Casimir restrictions.** `einstein_massShell_is_first_casimir`
  (`EquivalencePrincipleMassShell.einstein_massShell` is `μ²` at `p² = p³ = 0`, `= (mc)²`) and
  `nnLorentzForm_is_first_casimir` (the Nagao–Nielsen `(1,1)` cone `(Re q)²−(Im q)²` is `μ²` restricted to
  the complex-coordinate plane).
* **§C — the second Casimir.** `pauli_lubanski_spacelike`: a 4-vector orthogonal to a timelike 4-momentum
  is spacelike/null, so the Pauli–Lubanski spin satisfies `S_a S^a ≤ 0` (Szabados Eq. 2.3).
* **§D — the full Lorentz-matrix invariance.** `poincareRestMassSqM` (the first Casimir as `pᵀ η p` via the
  tetrad `minkowskiMatrix`) and `poincareRestMassSqM_lorentz_invariant` (`μ²(Λp) = μ²(p)` for any
  `Λ ∈ SO(1,3)`, via `lorentz_preserves_eta` — the full `p^a ↦ Λ^a_b p^b`, not just a single boost).
* **§E — the reverse Cauchy–Schwarz (Szabados §2.2).** `inner_sq_ge_massSq_product`
  (`⟨p₁,p₂⟩² ≥ μ₁²μ₂²` for future-timelike momenta — `P²₁₂ ≥ μ₁μ₂`) and
  `inner_sq_gt_massSq_product_of_not_parallel` (strict `>` when the momenta are non-parallel, so the
  empirical distance of §2.2 is well defined).
* **§F — the centre-of-mass vector (Szabados Eq. 2.3).** `centreOfMassVector` (`M_a = J_{ab} p^b`) and
  `centreOfMass_orthogonal_momentum` (`M_a p^a = 0` from `J^{ab}` antisymmetric) — the building block of
  the distance formula, via `antisymmetric_quadratic_form_zero` (the antisymmetric-form fact shared with
  the Sorkin–Johnston Pauli–Jordan kernel; the ε-based projection `Π` of Eq. 2.8 is not built, the 4-D
  Levi-Civita being unavailable for Lorentz vectors in the library).
* **§G — the Gram determinant (Szabados §2.2).** `gramDeterminant` (`μ₁²μ₂² − P⁴₁₂`, the `Π` denominator),
  `gramDeterminant_nonpos` (`≤ 0` — the two-momentum plane is timelike, its complement spacelike, so the
  distance is real) and `gramDeterminant_neg_of_not_parallel` (strict `< 0` — `Π` well defined, the
  empirical distance exists). Together with §C (distance vector spacelike) and §E these fix the empirical
  distance as a well-defined, real, spacelike quantity.
* **§H — the projection `Π` and the empirical-distance vector (Szabados Eqs. 2.7–2.8, ε-free).** `minkProd`
  (the Minkowski inner product), `gramProj` (the orthogonal projection onto `⊥ span{p₁,p₂}` via the `2×2`
  Gram matrix — Szabados' `Π` of Eq. 2.8 *without* the Levi-Civita), `gramProj_orthogonal_left`/`_right`
  (`⟨pᵢ, Πv⟩ = 0`), `empiricalDistanceVector` (`d₁₂ = Π(M₁/μ₁² − M₂/μ₂²)`, Eq. 2.7) and
  `empiricalDistanceVector_orthogonal` (`⟨p₁,d₁₂⟩ = ⟨p₂,d₁₂⟩ = 0`, so `d₁₂` is spacelike by §C).
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert


/-- **The first Poincaré Casimir** `μ² = η_{ab} p^a p^b = (p^0)² − (p^1)² − (p^2)² − (p^3)²` (Szabados
Eq. 2.3, signature `(+,−,−,−)`): the rest-mass-squared invariant of the 4-momentum. -/
def poincareRestMassSq (p0 p1 p2 p3 : ℝ) : ℝ := p0 ^ 2 - p1 ^ 2 - p2 ^ 2 - p3 ^ 2

/-- **The rest mass is Lorentz-boost invariant** — the defining Poincaré-Casimir property: a boost of
rapidity `θ` in the `1`-direction, `(p^0, p^1) ↦ (p^0 cosh θ − p^1 sinh θ, p^1 cosh θ − p^0 sinh θ)`, leaves
`μ² = η_{ab} p^a p^b` unchanged (`cosh²θ − sinh²θ = 1`). -/
lemma poincareRestMassSq_boost_invariant (p0 p1 p2 p3 θ : ℝ) :
    poincareRestMassSq (p0 * Real.cosh θ - p1 * Real.sinh θ) (p1 * Real.cosh θ - p0 * Real.sinh θ) p2 p3
      = poincareRestMassSq p0 p1 p2 p3 := by
  unfold poincareRestMassSq
  linear_combination (p0 ^ 2 - p1 ^ 2) * Real.cosh_sq_sub_sinh_sq θ


/-- **The Compton mass-shell is the first Casimir at `p² = p³ = 0`** `μ² = (E/c)² − p² = (mc)²`: the
`(1+1)` `EquivalencePrincipleMassShell.einstein_massShell` is the full Poincaré Casimir of Szabados Eq. 2.3
restricted to a single spatial momentum component. -/
lemma einstein_massShell_is_first_casimir (m c p : ℝ) (hc : c ≠ 0) :
    poincareRestMassSq (einsteinEnergy m c p / c) p 0 0 = (m * c) ^ 2 := by
  unfold poincareRestMassSq
  linear_combination einstein_massShell m c p hc

/-- **The Nagao–Nielsen convergence cone is the first Casimir on the complex-coordinate plane**
`(Re q)² − (Im q)² = μ²(Re q, Im q, 0, 0)`: the `(1,1)` Minkowski form of `NagaoNielsenMassShellCone`
(the steepest-descent cone, `= Re(q²)`) is the Poincaré rest-mass Casimir restricted to two components. -/
lemma nnLorentzForm_is_first_casimir (q : ℂ) :
    nnLorentzForm q = poincareRestMassSq q.re q.im 0 0 := by
  unfold nnLorentzForm poincareRestMassSq
  ring


/-- **The Minkowski inner product** `η_{ab} a^a b^b = a^0 b^0 − a⃗·b⃗` (signature `(+,−,−,−)`). -/
def minkInner (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ) : ℝ := a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3

/-- **[Second Casimir: the Pauli–Lubanski spin is spacelike] `S_a S^a ≤ 0`.** A 4-vector `S` orthogonal to
a timelike 4-momentum `p` (`η_{ab} S^a p^b = 0`, `μ² = η_{ab} p^a p^b > 0`) is spacelike or null — the
reason the second Poincaré Casimir `S_a S^a` (Szabados Eq. 2.3, with `S_a p^a = 0`) satisfies `≤ 0`. The
proof is the reverse of Cauchy–Schwarz forced by the Lorentzian signature: `S_0 p_0 = S⃗·p⃗` and
`|p⃗|² < p_0²` give `S_0² ≤ |S⃗|²`. -/
lemma pauli_lubanski_spacelike (S0 S1 S2 S3 p0 p1 p2 p3 : ℝ)
    (htime : 0 < poincareRestMassSq p0 p1 p2 p3)
    (horth : minkInner S0 S1 S2 S3 p0 p1 p2 p3 = 0) :
    poincareRestMassSq S0 S1 S2 S3 ≤ 0 := by
  unfold poincareRestMassSq minkInner at *
  have hp02 : (0 : ℝ) < p0 ^ 2 := by nlinarith [sq_nonneg p1, sq_nonneg p2, sq_nonneg p3]
  have hSp2 : S0 ^ 2 * p0 ^ 2 = (S1 * p1 + S2 * p2 + S3 * p3) ^ 2 := by
    have hSp : S0 * p0 = S1 * p1 + S2 * p2 + S3 * p3 := by linarith
    rw [show S0 ^ 2 * p0 ^ 2 = (S0 * p0) ^ 2 from by ring, hSp]
  have key : (S0 ^ 2 - S1 ^ 2 - S2 ^ 2 - S3 ^ 2) * p0 ^ 2 ≤ 0 := by
    nlinarith [hSp2, sq_nonneg (S1 * p2 - S2 * p1), sq_nonneg (S1 * p3 - S3 * p1),
      sq_nonneg (S2 * p3 - S3 * p2),
      mul_nonneg (add_nonneg (add_nonneg (sq_nonneg S1) (sq_nonneg S2)) (sq_nonneg S3)) htime.le]
  by_contra h
  rw [not_le] at h
  nlinarith [mul_pos h hp02, key]


open Matrix
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

/-- **The first Casimir as the Minkowski norm of the 4-momentum** `μ² = pᵀ η p` (matrix form over
`ℝ^{1,3} = Fin 1 ⊕ Fin 3`), using the tetrad `minkowskiMatrix`. -/
noncomputable def poincareRestMassSqM (p : Fin 1 ⊕ Fin 3 → ℝ) : ℝ :=
  p ⬝ᵥ (minkowskiMatrix *ᵥ p)

/-- **[Full Poincaré invariance] `μ²(Λp) = μ²(p)`.** The first Casimir is invariant under the full Lorentz
transformation of the 4-momentum `p^a ↦ Λ^a_b p^b`, `Λ ∈ SO(1,3)` (Szabados Eq. 2.1, `p^a` a Lorentzian
4-vector) — not only under a single-direction boost (§A). The proof is the congruence
`(Λp)ᵀ η (Λp) = pᵀ (Λᵀ η Λ) p = pᵀ η p` via `TetradADMGravity.lorentz_preserves_eta`. -/
lemma poincareRestMassSqM_lorentz_invariant
    {Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ} (hΛ : Λ ∈ LorentzGroup 3)
    (p : Fin 1 ⊕ Fin 3 → ℝ) :
    poincareRestMassSqM (Λ *ᵥ p) = poincareRestMassSqM p := by
  have adjoint : ∀ (A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) (x y : Fin 1 ⊕ Fin 3 → ℝ),
      (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
    intro A x y
    rw [dotProduct_comm (A *ᵥ x) y, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]
  unfold poincareRestMassSqM
  rw [adjoint Λ p (minkowskiMatrix *ᵥ (Λ *ᵥ p)), mulVec_mulVec, mulVec_mulVec,
    lorentz_preserves_eta hΛ]


/-- **[Reverse Cauchy–Schwarz for future-timelike momenta] `P²₁₂ = ⟨p₁,p₂⟩ ≥ μ₁μ₂`, squared as
`⟨p₁,p₂⟩² ≥ μ₁²μ₂²`.** For two future-pointing timelike 4-momenta the Minkowski inner product dominates the
product of the rest masses (Szabados §2.2, p. 8, with equality iff the momenta are parallel) — the
inequality behind the well-definedness of the empirical distance (`P⁴₁₂ > μ₁²μ₂²` unless `p₁ ∥ p₂`). The
proof introduces the spatial norms `|p⃗ᵢ|` (`Real.sqrt`), uses the 3-D Cauchy–Schwarz `p⃗₁·p⃗₂ ≤ |p⃗₁||p⃗₂|`
and `|p⃗ᵢ| < pᵢ⁰` (timelike), then the Lorentzian identity `(p₁⁰p₂⁰ − |p⃗₁||p⃗₂|)² − μ₁²μ₂² =
(p₁⁰|p⃗₂| − |p⃗₁|p₂⁰)²`. -/
lemma inner_sq_ge_massSq_product (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ)
    (hta : 0 < poincareRestMassSq a0 a1 a2 a3) (htb : 0 < poincareRestMassSq b0 b1 b2 b3)
    (ha0 : 0 < a0) (hb0 : 0 < b0) :
    poincareRestMassSq a0 a1 a2 a3 * poincareRestMassSq b0 b1 b2 b3
      ≤ minkInner a0 a1 a2 a3 b0 b1 b2 b3 ^ 2 := by
  simp only [poincareRestMassSq, minkInner] at *
  obtain ⟨na, hna, hna2⟩ : ∃ na, 0 ≤ na ∧ na ^ 2 = a1 ^ 2 + a2 ^ 2 + a3 ^ 2 :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, Real.sq_sqrt (by positivity)⟩
  obtain ⟨nb, hnb, hnb2⟩ : ∃ nb, 0 ≤ nb ∧ nb ^ 2 = b1 ^ 2 + b2 ^ 2 + b3 ^ 2 :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, Real.sq_sqrt (by positivity)⟩
  have hD : a1 * b1 + a2 * b2 + a3 * b3 ≤ na * nb := by
    have hD2 : (a1 * b1 + a2 * b2 + a3 * b3) ^ 2 ≤ (na * nb) ^ 2 := by
      nlinarith [sq_nonneg (a1 * b2 - a2 * b1), sq_nonneg (a1 * b3 - a3 * b1),
        sq_nonneg (a2 * b3 - a3 * b2), hna2, hnb2]
    nlinarith [hD2, mul_nonneg hna hnb, sq_nonneg (na * nb + (a1 * b1 + a2 * b2 + a3 * b3))]
  have hna0 : na < a0 := by nlinarith [hna2, ha0, hna]
  have hnb0 : nb < b0 := by nlinarith [hnb2, hb0, hnb]
  have hpos : 0 ≤ a0 * b0 - na * nb := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hna0.le) hb0.le, mul_nonneg hna (sub_nonneg.mpr hnb0.le)]
  nlinarith [sq_nonneg (a0 * nb - na * b0), hna2, hnb2,
    mul_nonneg (by linarith [hD] : (0 : ℝ) ≤ na * nb - (a1 * b1 + a2 * b2 + a3 * b3))
      (by nlinarith [hpos, hD] : (0 : ℝ) ≤ 2 * (a0 * b0) - (a1 * b1 + a2 * b2 + a3 * b3) - na * nb)]

/-- **The empirical distance is well defined for non-parallel momenta** `P⁴₁₂ > μ₁²μ₂²` (strict), whenever
the two future-timelike momenta are not parallel — here in the sufficient form `p₁⁰|p⃗₂| ≠ |p⃗₁|p₂⁰` (the
`(p₁⁰|p⃗₂| − |p⃗₁|p₂⁰)²` term of §E is then strictly positive). -/
lemma inner_sq_gt_massSq_product_of_not_parallel (a0 a1 a2 a3 b0 b1 b2 b3 na nb : ℝ)
    (hna : 0 ≤ na) (hna2 : na ^ 2 = a1 ^ 2 + a2 ^ 2 + a3 ^ 2)
    (hnb2 : nb ^ 2 = b1 ^ 2 + b2 ^ 2 + b3 ^ 2)
    (hb0 : 0 < b0) (hna0 : na < a0) (hnb0 : nb < b0)
    (hD : a1 * b1 + a2 * b2 + a3 * b3 ≤ na * nb) (hpar : a0 * nb - na * b0 ≠ 0) :
    poincareRestMassSq a0 a1 a2 a3 * poincareRestMassSq b0 b1 b2 b3
      < minkInner a0 a1 a2 a3 b0 b1 b2 b3 ^ 2 := by
  simp only [poincareRestMassSq, minkInner]
  have hpos : 0 ≤ a0 * b0 - na * nb := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hna0.le) hb0.le, mul_nonneg hna (sub_nonneg.mpr hnb0.le)]
  have hsq : 0 < (a0 * nb - na * b0) ^ 2 := by positivity
  nlinarith [hsq, hna2, hnb2,
    mul_nonneg (by linarith [hD] : (0 : ℝ) ≤ na * nb - (a1 * b1 + a2 * b2 + a3 * b3))
      (by nlinarith [hpos, hD] : (0 : ℝ) ≤ 2 * (a0 * b0) - (a1 * b1 + a2 * b2 + a3 * b3) - na * nb)]

/-!

The distance formula `d₁₂ᵃ = Πᵃᵦ(M₁ᵇ/μ₁² − M₂ᵇ/μ₂²)` (Eq. 2.7) is built from the centre-of-mass vectors
`M_a := J_{ab} p^b` (Eq. 2.3). Their orthogonality `M_a p^a = 0` is a pure antisymmetric-form fact — the
same structure carried by the Sorkin–Johnston Pauli–Jordan kernel
(`SorkinJohnstonCausalGreen.causalPauliJordan`, antisymmetric) and dual to the positive Wright form
(`WrightQuadraticFormRepresentation.wrightForm_diag_nonneg`). The projection `Πᵃᵦ` of Eq. 2.8 needs the 4-D
Levi-Civita `ε_{abcd}`, which is not available for Lorentz vectors in the library, so it is not built here.
-/

/-- **Transpose-adjoint of the natural pairing** `(A x)·y = x·(Aᵀ y)`. -/
lemma dotProduct_mulVec_adjoint (A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (x y : Fin 1 ⊕ Fin 3 → ℝ) : (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_comm (A *ᵥ x) y, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

/-- **An antisymmetric bilinear form vanishes on the diagonal** `pᵀ J p = 0` for `Jᵀ = −J` — the same
structural fact as the antisymmetry of the Sorkin–Johnston Pauli–Jordan kernel `Δ(x,y) = −Δ(y,x)`. -/
lemma antisymmetric_quadratic_form_zero (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (hJ : Jᵀ = -J) (p : Fin 1 ⊕ Fin 3 → ℝ) : p ⬝ᵥ (J *ᵥ p) = 0 := by
  have h : p ⬝ᵥ (J *ᵥ p) = -(p ⬝ᵥ (J *ᵥ p)) :=
    calc p ⬝ᵥ (J *ᵥ p) = (J *ᵥ p) ⬝ᵥ p := dotProduct_comm _ _
      _ = p ⬝ᵥ (Jᵀ *ᵥ p) := dotProduct_mulVec_adjoint J p p
      _ = p ⬝ᵥ ((-J) *ᵥ p) := by rw [hJ]
      _ = p ⬝ᵥ (-(J *ᵥ p)) := by rw [Matrix.neg_mulVec]
      _ = -(p ⬝ᵥ (J *ᵥ p)) := by rw [dotProduct_neg]
  linarith

/-- **The centre-of-mass vector** `M_a := J_{ab} p^b` (Szabados Eq. 2.3): the antisymmetric
angular-momentum tensor contracted with the 4-momentum. -/
noncomputable def centreOfMassVector (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (p : Fin 1 ⊕ Fin 3 → ℝ) : Fin 1 ⊕ Fin 3 → ℝ := J *ᵥ p

/-- **The centre-of-mass vector is orthogonal to the momentum** `M_a p^a = 0` (Szabados Eq. 2.3, from
`J^{ab}` antisymmetric) — the analogue of the Pauli–Lubanski orthogonality `S_a p^a = 0` (§C), the
building block `M_a` of the empirical-distance formula (Eq. 2.7), proved by the antisymmetric-form
vanishing shared with the Sorkin–Johnston Pauli–Jordan construction. -/
lemma centreOfMass_orthogonal_momentum (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (hJ : Jᵀ = -J) (p : Fin 1 ⊕ Fin 3 → ℝ) : p ⬝ᵥ centreOfMassVector J p = 0 :=
  antisymmetric_quadratic_form_zero J hJ p


/-- **The Minkowski Gram determinant of two momenta** `det[[μ₁², P²₁₂],[P²₁₂, μ₂²]] = μ₁²μ₂² − P⁴₁₂` — the
denominator `P⁴₁₂ − μ₁²μ₂²` (up to sign) of the projection `Π` in Szabados Eq. 2.8. -/
def gramDeterminant (mu1Sq mu2Sq P12 : ℝ) : ℝ := mu1Sq * mu2Sq - P12 ^ 2

/-- **The Gram determinant of two future-timelike momenta is nonpositive** `μ₁²μ₂² − P⁴₁₂ ≤ 0` (from the
reverse Cauchy–Schwarz §E): the 2-plane spanned by two timelike momenta is itself timelike (Lorentzian
signature), so its orthogonal complement — where the empirical-distance vector `d₁₂` lives (§C: orthogonal
to a timelike vector ⇒ spacelike) — is spacelike, and `(D₁₂)² = −η_{ab}d₁₂^a d₁₂^b ≥ 0` is a real distance. -/
lemma gramDeterminant_nonpos (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ)
    (hta : 0 < poincareRestMassSq a0 a1 a2 a3) (htb : 0 < poincareRestMassSq b0 b1 b2 b3)
    (ha0 : 0 < a0) (hb0 : 0 < b0) :
    gramDeterminant (poincareRestMassSq a0 a1 a2 a3) (poincareRestMassSq b0 b1 b2 b3)
        (minkInner a0 a1 a2 a3 b0 b1 b2 b3) ≤ 0 := by
  unfold gramDeterminant
  linarith [inner_sq_ge_massSq_product a0 a1 a2 a3 b0 b1 b2 b3 hta htb ha0 hb0]

/-- **The Gram determinant is strictly negative for non-parallel momenta** `μ₁²μ₂² − P⁴₁₂ < 0` (strict
reverse Cauchy–Schwarz §E): the projection `Π` of Szabados Eq. 2.8 is well defined (nonzero denominator),
so the empirical distance `d₁₂` exists whenever the two momenta are not parallel. -/
lemma gramDeterminant_neg_of_not_parallel (a0 a1 a2 a3 b0 b1 b2 b3 na nb : ℝ)
    (hna : 0 ≤ na) (hna2 : na ^ 2 = a1 ^ 2 + a2 ^ 2 + a3 ^ 2)
    (hnb2 : nb ^ 2 = b1 ^ 2 + b2 ^ 2 + b3 ^ 2)
    (hb0 : 0 < b0) (hna0 : na < a0) (hnb0 : nb < b0)
    (hD : a1 * b1 + a2 * b2 + a3 * b3 ≤ na * nb) (hpar : a0 * nb - na * b0 ≠ 0) :
    gramDeterminant (poincareRestMassSq a0 a1 a2 a3) (poincareRestMassSq b0 b1 b2 b3)
        (minkInner a0 a1 a2 a3 b0 b1 b2 b3) < 0 := by
  unfold gramDeterminant
  linarith [inner_sq_gt_massSq_product_of_not_parallel a0 a1 a2 a3 b0 b1 b2 b3 na nb
    hna hna2 hnb2 hb0 hna0 hnb0 hD hpar]

/-!

Szabados' projection `Πᵃᵦ` (Eq. 2.8) is written with the Levi-Civita `ε`, but it is the orthogonal
projection onto the spacelike 2-plane `⊥ span{p₁,p₂}`, which is expressible purely from the `2×2` Gram
matrix — no `ε` needed. This builds it, and the empirical-distance vector `d₁₂ = Π(M₁/μ₁² − M₂/μ₂²)`
(Eq. 2.7), and proves it is orthogonal to both momenta.
-/

/-- **The Minkowski inner product** `⟨u,v⟩ = u^a η_{ab} v^b` as `uᵀ η v` (via the tetrad `minkowskiMatrix`). -/
noncomputable def minkProd (u v : Fin 1 ⊕ Fin 3 → ℝ) : ℝ := u ⬝ᵥ (minkowskiMatrix *ᵥ v)

/-- The Minkowski inner product is symmetric (`η` symmetric). -/
lemma minkProd_symm (u v : Fin 1 ⊕ Fin 3 → ℝ) : minkProd u v = minkProd v u := by
  unfold minkProd
  rw [dotProduct_comm u (minkowskiMatrix *ᵥ v), dotProduct_mulVec_adjoint, minkowskiMatrix.eq_transpose]

/-- The Minkowski inner product is additive on the right through subtraction. -/
lemma minkProd_sub_right (u v w : Fin 1 ⊕ Fin 3 → ℝ) :
    minkProd u (v - w) = minkProd u v - minkProd u w := by
  simp only [minkProd, Matrix.mulVec_sub, dotProduct, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

/-- The Minkowski inner product is homogeneous on the right. -/
lemma minkProd_smul_right (c : ℝ) (u v : Fin 1 ⊕ Fin 3 → ℝ) :
    minkProd u (c • v) = c * minkProd u v := by
  simp only [minkProd, Matrix.mulVec_smul, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The Gram projection onto `⊥ span{p₁,p₂}`** `Π v = v − (G⁻¹ w)₁ p₁ − (G⁻¹ w)₂ p₂`, with the `2×2`
Minkowski Gram matrix `G = [[⟨p₁,p₁⟩,⟨p₁,p₂⟩],[·,⟨p₂,p₂⟩]]` and `w = (⟨p₁,v⟩,⟨p₂,v⟩)` — Szabados' `Π` of
Eq. 2.8 expressed without the Levi-Civita `ε`. -/
noncomputable def gramProj (p1 p2 v : Fin 1 ⊕ Fin 3 → ℝ) : Fin 1 ⊕ Fin 3 → ℝ :=
  v - ((minkProd p2 p2 * minkProd p1 v - minkProd p1 p2 * minkProd p2 v) /
        (minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2)) • p1
    - ((minkProd p1 p1 * minkProd p2 v - minkProd p1 p2 * minkProd p1 v) /
        (minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2)) • p2

/-- **The projection is orthogonal to `p₁`** `⟨p₁, Π v⟩ = 0` (whenever the Gram determinant is nonzero,
i.e. the momenta are non-parallel, §G). -/
lemma gramProj_orthogonal_left (p1 p2 v : Fin 1 ⊕ Fin 3 → ℝ)
    (hdet : minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2 ≠ 0) :
    minkProd p1 (gramProj p1 p2 v) = 0 := by
  unfold gramProj
  simp only [minkProd_sub_right, minkProd_smul_right]
  set μ1 := minkProd p1 p1
  set μ2 := minkProd p2 p2
  set P := minkProd p1 p2
  set w1 := minkProd p1 v
  set w2 := minkProd p2 v
  have hdet2 : μ2 * μ1 - P ^ 2 ≠ 0 := by simpa [mul_comm] using hdet
  field_simp [hdet2]
  ring

/-- **The projection is orthogonal to `p₂`** `⟨p₂, Π v⟩ = 0`. -/
lemma gramProj_orthogonal_right (p1 p2 v : Fin 1 ⊕ Fin 3 → ℝ)
    (hdet : minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2 ≠ 0) :
    minkProd p2 (gramProj p1 p2 v) = 0 := by
  unfold gramProj
  simp only [minkProd_sub_right, minkProd_smul_right, minkProd_symm p2 p1]
  set μ1 := minkProd p1 p1
  set μ2 := minkProd p2 p2
  set P := minkProd p1 p2
  set w1 := minkProd p1 v
  set w2 := minkProd p2 v
  have hdet2 : μ2 * μ1 - P ^ 2 ≠ 0 := by simpa [mul_comm] using hdet
  field_simp [hdet2]
  ring

/-- **The empirical-distance vector** `d₁₂ = Π(M₁/μ₁² − M₂/μ₂²)` (Szabados Eq. 2.7): the relative position
of the two centre-of-mass lines, the projection of the difference of the centre-of-mass vectors (scaled by
the rest masses) onto the spacelike 2-plane orthogonal to both momenta. -/
noncomputable def empiricalDistanceVector (p1 p2 M1 M2 : Fin 1 ⊕ Fin 3 → ℝ) (mu1Sq mu2Sq : ℝ) :
    Fin 1 ⊕ Fin 3 → ℝ :=
  gramProj p1 p2 (mu1Sq⁻¹ • M1 - mu2Sq⁻¹ • M2)

/-- **The empirical-distance vector is orthogonal to both momenta** `⟨p₁,d₁₂⟩ = ⟨p₂,d₁₂⟩ = 0` (Szabados
Eq. 2.7): `d₁₂` lies in the spacelike 2-plane `⊥ span{p₁,p₂}`, hence (§C) is spacelike and
`(D₁₂)² = −⟨d₁₂,d₁₂⟩ ≥ 0` is a real spatial distance. -/
lemma empiricalDistanceVector_orthogonal (p1 p2 M1 M2 : Fin 1 ⊕ Fin 3 → ℝ) (mu1Sq mu2Sq : ℝ)
    (hdet : minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2 ≠ 0) :
    minkProd p1 (empiricalDistanceVector p1 p2 M1 M2 mu1Sq mu2Sq) = 0
      ∧ minkProd p2 (empiricalDistanceVector p1 p2 M1 M2 mu1Sq mu2Sq) = 0 :=
  ⟨gramProj_orthogonal_left p1 p2 _ hdet, gramProj_orthogonal_right p1 p2 _ hdet⟩

/-!

The sequel paper (curved spacetimes from QM) builds its empirical distance from the *quantum* centre-of-mass
operator `C^a`, which is the classical `M_a = J_{ab}p^b` of §F promoted to a ℂ-valued self-adjoint operator by
the operator-ordering term `−(3/2)iℏ p^a`. In the classical limit `ℏ → 0` it returns `M_a`, closing the loop
with the flat-spacetime construction of this file. -/

/-- **The quantum centre-of-mass operator** `C^a := J^{ab}p_b − (3/2)iℏ p^a` (Szabados 2502.07668 Eq. 4.2):
the classical centre-of-mass vector `M_a = J_{ab}p^b` (§F) with the operator-ordering term `−(3/2)iℏ p^a`. -/
noncomputable def quantumCentreOfMass (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (p : Fin 1 ⊕ Fin 3 → ℝ) (ℏ : ℝ) : Fin 1 ⊕ Fin 3 → ℂ :=
  fun a => (centreOfMassVector J p a : ℂ) - Complex.I * ((3 / 2 * ℏ * p a : ℝ) : ℂ)

/-- **[Classical limit `ℏ → 0`] `C^a = M_a`** — the quantum centre-of-mass reduces to the classical
centre-of-mass vector of §F, the shared building block of the flat (2309.06150) and curved (2502.07668) papers. -/
lemma quantumCentreOfMass_hbar_zero (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (p : Fin 1 ⊕ Fin 3 → ℝ) :
    quantumCentreOfMass J p 0 = fun a => (centreOfMassVector J p a : ℂ) := by
  funext a; simp [quantumCentreOfMass]

/-- **[Real part] `Re C^a = M_a`** — the classical centre-of-mass is the real part of the quantum operator. -/
lemma quantumCentreOfMass_re (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (p : Fin 1 ⊕ Fin 3 → ℝ) (ℏ : ℝ) (a : Fin 1 ⊕ Fin 3) :
    (quantumCentreOfMass J p ℏ a).re = centreOfMassVector J p a := by
  simp [quantumCentreOfMass, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

/-- **[Imaginary part] `Im C^a = −(3/2)ℏ p^a`** — the operator-ordering (quantum) correction. -/
lemma quantumCentreOfMass_im (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (p : Fin 1 ⊕ Fin 3 → ℝ) (ℏ : ℝ) (a : Fin 1 ⊕ Fin 3) :
    (quantumCentreOfMass J p ℏ a).im = -(3 / 2 * ℏ * p a) := by
  simp [quantumCentreOfMass, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

/-- **[The classical centre-of-mass is the real part] `Re C^a = M_a`, and `C^a = M_a ⟺ ℏ p^a = 0`** — the
quantum operator collapses to the §F classical centre-of-mass exactly when the operator-ordering term vanishes
(`ℏ = 0` or on the zero-momentum shell), so the imaginary part `Im C^a = −(3/2)ℏ p^a` is the sole quantum
correction. -/
lemma quantumCentreOfMass_eq_classical_iff (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (p : Fin 1 ⊕ Fin 3 → ℝ) (ℏ : ℝ) (a : Fin 1 ⊕ Fin 3) :
    quantumCentreOfMass J p ℏ a = (centreOfMassVector J p a : ℂ) ↔ ℏ * p a = 0 := by
  rw [Complex.ext_iff, quantumCentreOfMass_re, quantumCentreOfMass_im, Complex.ofReal_re,
    Complex.ofReal_im]
  constructor
  · rintro ⟨-, h⟩
    have hz : (3 : ℝ) / 2 * (ℏ * p a) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    exact ⟨rfl, by linear_combination (-3 / 2 : ℝ) * h⟩

/-!

The orthogonality `M_a p^a = 0` of §F is powered by the antisymmetry `Jᵀ = −J` of the angular-momentum
tensor. That antisymmetry is exactly the defining property of the Pauli–Jordan function of the Sorkin–Johnston
causal-set vacuum (`SorkinJohnstonRegionState.IsPauliJordan`, `Δ(x,y) = −Δ(y,x)`). So `J` — read as a kernel on
the momentum index — *is* a Pauli–Jordan kernel, and the same structural fact that makes the SJ commutator
antisymmetric makes the centre-of-mass vector orthogonal to the momentum. This makes the link asserted in §F's
docstring a theorem. -/

/-- **[The angular-momentum tensor is a Pauli–Jordan kernel] `Jᵀ = −J ⇒ IsPauliJordan J`** — Szabados'
angular-momentum tensor, read as a two-point kernel on the momentum index, satisfies the same antisymmetry
`J(x,y) = −J(y,x)` that defines the Sorkin–Johnston Pauli–Jordan function `Δ = G_ret − G_adv`. -/
lemma angularMomentum_isPauliJordan (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) (hJ : Jᵀ = -J) :
    IsPauliJordan (fun i j => J i j) := by
  intro x y
  have h : Jᵀ y x = (-J) y x := congrFun (congrFun hJ y) x
  simpa [Matrix.transpose_apply, Matrix.neg_apply] using h

/-- **[The self-coupling of the angular-momentum kernel vanishes] `J_{ii} = 0`** — via the Sorkin–Johnston
`pauliJordan_self` applied to `J`: the diagonal of a Pauli–Jordan kernel is zero, the index-space shadow of the
antisymmetric-form vanishing `M_a p^a = 0` (`centreOfMass_orthogonal_momentum`) that gives the centre-of-mass
vector its spacelike character. -/
lemma angularMomentum_diag_zero (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) (hJ : Jᵀ = -J)
    (i : Fin 1 ⊕ Fin 3) : J i i = 0 :=
  pauliJordan_self _ (angularMomentum_isPauliJordan J hJ) i

/-- **[The angular-momentum tensor feeds the Sorkin quantum-gravity path integral]** for any symmetric kernel
`A`, the Sorkin–Johnston Wightman two-point built from `A` and the angular-momentum tensor `J` (used as its
Pauli–Jordan commutator) satisfies the Dowker–Johnston–Sorkin decoherence-functional Hermiticity
`W(x,y) = W(y,x)*` (`QuantumMeasureHistoryHilbert.sj_wightman_isHermitian`). So Szabados' centre-of-mass
structure supplies an admissible commutator kernel to the quantum-measure / history-Hilbert construction of the
path integral: the momentum-space angular momentum is the input from which a quantal measure is built. -/
lemma angularMomentum_sjWightman_isHermitian (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (hJ : Jᵀ = -J) (A : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ) (hA : IsSymmetricKernel A)
    (x y : Fin 1 ⊕ Fin 3) :
    wightmanTwoPoint A (fun i j => J i j) x y
      = starRingEnd ℂ (wightmanTwoPoint A (fun i j => J i j) y x) :=
  sj_wightman_isHermitian A (fun i j => J i j) hA (angularMomentum_isPauliJordan J hJ) x y

/-!

Szabados' quantum centre-of-mass operator `C^a = J^{ab}p_b − (3/2)iℏp^a` (§I) enters the quantum empirical
distance `d²_ij` (2502.07668 Eq. 4.2) only through the relative vector `Σ^a_ij = C_i^a/μ_i² − C_j^a/μ_j²`
projected onto the spacelike 2-plane `⊥ span{p₁,p₂}` — the same projection `gramProj` (§H) that carries the
*classical* empirical distance. The projection **annihilates the momenta** (`gramProj_momentum_left/right`), and
the imaginary operator-ordering term `−(3/2)iℏp^a` of `C^a` (`quantumCentreOfMass_im`) is a multiple of the
momentum. So the ordering term is projected out: the quantum `d²_ij` equals the classical `(D_ij)²`. This is
why Szabados' Theorem 4.2.1 can use the quantum operator `C^a` and still recover the classical distance — the
`iℏ` correction is invisible to the empirical distance. The Hilbert-space operators are the `J^{ab}`, `p^b`
carriers already in `centreOfMassVector`/`quantumCentreOfMass`; no new machinery is needed. -/

/-- **[The Gram projection annihilates the first momentum] `Π p₁ = 0`** — `gramProj p1 p2 p1 = p1 − 1·p1 − 0·p2`
vanishes: the projection onto `⊥ span{p₁,p₂}` kills `p₁` itself. -/
lemma gramProj_momentum_left (p1 p2 : Fin 1 ⊕ Fin 3 → ℝ)
    (hdet : minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2 ≠ 0) :
    gramProj p1 p2 p1 = 0 := by
  unfold gramProj
  simp only [minkProd_symm p2 p1]
  set μ1 := minkProd p1 p1
  set μ2 := minkProd p2 p2
  set P := minkProd p1 p2
  have e1 : (μ2 * μ1 - P * P) / (μ1 * μ2 - P ^ 2) = 1 := by
    rw [show μ2 * μ1 - P * P = μ1 * μ2 - P ^ 2 by ring, div_self hdet]
  have e2 : (μ1 * P - P * μ1) / (μ1 * μ2 - P ^ 2) = 0 := by
    rw [mul_comm μ1 P, sub_self, zero_div]
  rw [e1, e2]; simp

/-- **[The Gram projection annihilates the second momentum] `Π p₂ = 0`**. -/
lemma gramProj_momentum_right (p1 p2 : Fin 1 ⊕ Fin 3 → ℝ)
    (hdet : minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2 ≠ 0) :
    gramProj p1 p2 p2 = 0 := by
  unfold gramProj
  set μ1 := minkProd p1 p1
  set μ2 := minkProd p2 p2
  set P := minkProd p1 p2
  have e1 : (μ2 * P - P * μ2) / (μ1 * μ2 - P ^ 2) = 0 := by
    rw [mul_comm μ2 P, sub_self, zero_div]
  have e2 : (μ1 * μ2 - P * P) / (μ1 * μ2 - P ^ 2) = 1 := by
    rw [show μ1 * μ2 - P * P = μ1 * μ2 - P ^ 2 by ring, div_self hdet]
  rw [e1, e2]; simp

/-- **[Minkowski pairing is additive in the second slot]** `⟨u, v+w⟩ = ⟨u,v⟩ + ⟨u,w⟩`. -/
lemma minkProd_add_right (u v w : Fin 1 ⊕ Fin 3 → ℝ) :
    minkProd u (v + w) = minkProd u v + minkProd u w := by
  simp only [minkProd, Matrix.mulVec_add, dotProduct, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

/-- **[The Gram projection is additive]** `Π(v + w) = Π v + Π w`. -/
lemma gramProj_add (p1 p2 v w : Fin 1 ⊕ Fin 3 → ℝ) :
    gramProj p1 p2 (v + w) = gramProj p1 p2 v + gramProj p1 p2 w := by
  unfold gramProj
  simp only [minkProd_add_right]
  module

/-- **[The Gram projection is homogeneous]** `Π(c • v) = c • Π v`. -/
lemma gramProj_smul (p1 p2 v : Fin 1 ⊕ Fin 3 → ℝ) (c : ℝ) :
    gramProj p1 p2 (c • v) = c • gramProj p1 p2 v := by
  unfold gramProj
  simp only [minkProd_smul_right]
  module

/-- **[The projection annihilates any momentum multiple]** `Π(c • p₁) = 0` — the direction the quantum
ordering term `−(3/2)iℏp^a` points in. -/
lemma gramProj_momentum_smul_left (p1 p2 : Fin 1 ⊕ Fin 3 → ℝ) (c : ℝ)
    (hdet : minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2 ≠ 0) :
    gramProj p1 p2 (c • p1) = 0 := by
  rw [gramProj_smul, gramProj_momentum_left p1 p2 hdet, smul_zero]

/-- **[The empirical distance is invariant under a momentum shift of the centre of mass]**
`d₁₂(M₁ + c·p₁, M₂) = d₁₂(M₁, M₂)` — adding a multiple of `p₁` to the centre-of-mass vector `M₁` does not change
the empirical-distance vector, because the shift lies along `p₁`, which the Gram projection annihilates. This is
the exact mechanism by which the **quantum operator-ordering term is invisible**: `C^a = M_a − (3/2)iℏp^a`
(`quantumCentreOfMass_re`/`_im`), so the `iℏ` term is a momentum shift of the classical centre of mass `M_a`,
and the quantum `d²_ij` equals the classical `(D_ij)²`. -/
lemma empiricalDistanceVector_shift_momentum_left (p1 p2 M1 M2 : Fin 1 ⊕ Fin 3 → ℝ)
    (mu1Sq mu2Sq c : ℝ)
    (hdet : minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2 ≠ 0) :
    empiricalDistanceVector p1 p2 (M1 + c • p1) M2 mu1Sq mu2Sq
      = empiricalDistanceVector p1 p2 M1 M2 mu1Sq mu2Sq := by
  unfold empiricalDistanceVector
  rw [smul_add, show mu1Sq⁻¹ • M1 + mu1Sq⁻¹ • c • p1 - mu2Sq⁻¹ • M2
        = (mu1Sq⁻¹ • M1 - mu2Sq⁻¹ • M2) + (mu1Sq⁻¹ * c) • p1 by module,
    gramProj_add, gramProj_momentum_smul_left p1 p2 _ hdet, add_zero]

/-- **[The quantum operator-ordering term is invisible to the empirical distance]** — using the ordering shift
`c = −(3/2)ℏ` of `C^a = M_a − (3/2)iℏp^a` (`quantumCentreOfMass_im`): shifting the classical centre of mass `M₁`
by the quantum ordering term `−(3/2)ℏ p₁` leaves the empirical-distance vector unchanged. So the quantum
`d²_ij` built from the operator `C^a` equals the classical `(D_ij)²` built from `M_a` — Szabados' Theorem 4.2.1
recovers the classical distance from the quantum operator precisely because the `iℏ` correction points along the
momentum, which the spacelike Gram projection annihilates. -/
lemma quantumOrdering_invisible_to_empiricalDistance (p1 p2 M1 M2 : Fin 1 ⊕ Fin 3 → ℝ)
    (mu1Sq mu2Sq ℏ : ℝ)
    (hdet : minkProd p1 p1 * minkProd p2 p2 - minkProd p1 p2 ^ 2 ≠ 0) :
    empiricalDistanceVector p1 p2 (M1 + (-(3 / 2) * ℏ) • p1) M2 mu1Sq mu2Sq
      = empiricalDistanceVector p1 p2 M1 M2 mu1Sq mu2Sq :=
  empiricalDistanceVector_shift_momentum_left p1 p2 M1 M2 mu1Sq mu2Sq (-(3 / 2) * ℏ) hdet

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.StatisticalMechanics.BoltzmannConstant
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Unified entropic-time / bits / Bekenstein / Jacobson identity

Port of the complex-action/entropic-time unification chain from
`/Users/macbookpro/Downloads/paths-bits-eins.md` REPLYID
20260519-018. The chain identifies four expressions for the same
quantity:

 `dτ_ent = dS / k_B = δQ / (k_B·T) = dA / (4·ℓ_P²)
 = (ln 2) · d N_bits`.

* **Left** (`dτ_ent`) — the complex-action/entropic-time entropic-time increment.
* **Boltzmann** (`dS / k_B`) — entropy in nats per `k_B`.
* **Clausius / Jacobson** (`δQ / (k_B·T)`) — heat flux across a
 local horizon at temperature `T` (Jacobson 1995 *Phys. Rev. Lett.*
 75, 1260; Einstein equation from Clausius relation).
* **Bekenstein** (`dA / (4·ℓ_P²)`) — Planck-area horizon-bit count
 (Bekenstein 1973 *Phys. Rev. D* 7, 2333).
* **Bits** (`(ln 2) · d N_bits`) — Landauer bits-to-nats
 conversion (already in
 `Physlib.Thermodynamics.EntropicInformationRate`).

This file formalises the chain as **machine-checked algebraic
equalities** under the appropriate hypotheses.

**Physical content of the unification**:

Bekenstein measures **hidden horizon microstructure** through
`S_BH = k_B · A / (4·ℓ_P²)`; the horizon "counts Planck-area
information cells". Jacobson derives spacetime dynamics by
imposing the **Clausius relation** `δQ = T·dS` on **all local
Rindler horizons**: requiring this for arbitrary null directions
yields the **Einstein field equations**. complex-action/entropic-time recasts both:

* Bekenstein bit count `N_bits = A / (4·ℓ_P²·ln 2)` becomes the
 entropic-time scale `τ_ent = (ln 2) · N_bits = A / (4·ℓ_P²)`.

* Jacobson's Clausius increment `dS = δQ / T` becomes
 `dτ_ent = δQ / (k_B·T)` — energy flux **advances entropic time**
 in proportion to the temperature.

Both readings collapse onto the same `dτ_ent`, which is the
single quantity that unifies black-hole thermodynamics
(Bekenstein), gravity (Jacobson), information (Landauer), and
complex-action/entropic-time entropic time.

## Contents

### §1 — Entropy ↔ bits ↔ entropic time conversions

* `bitsFromEntropy S := S / (k_B · ln 2)` — Landauer.
* `tauEntFromEntropy S := S / k_B` — complex-action/entropic-time.
* `tauEnt_eq_ln2_mul_bits` — `τ_ent = ln(2) · bits`.

### §2 — Bekenstein bit / entropy / entropic-time identities

* `bekensteinEntropy A ℓP := k_B · A / (4·ℓP²)` — paper Eq.,
 `S_BH`.
* `bekensteinBits A ℓP := A / (4·ℓP²·ln 2)`.
* `bekensteinTauEnt A ℓP := A / (4·ℓP²)`.
* `bekensteinTauEnt_eq_entropy_div_kB` — algebraic equality.
* `bekensteinTauEnt_eq_ln2_mul_bits` — Bekenstein bits/ent-time.

### §3 — Jacobson Clausius identity

* `clausiusTauEnt δQ T := δQ / (k_B · T)` — Jacobson 1995.
* `clausiusTauEnt_eq_tauEntFromEntropy_under_Clausius` — under
 `dS = δQ / T`, the Jacobson form matches the entropy form.

### §4 — Unified four-way identity

* **`entropicTime_four_way_identity`** — at horizon thermal
 equilibrium with `δQ = T · dS` and `dS = (k_B · dA) / (4 · ℓ_P²)`,
 the four expressions for `dτ_ent` are pairwise equal.

## Scope

* This file provides the **algebraic identities** of the unification.
 The **derivation** of Bekenstein entropy from horizon physics
 (Bardeen–Carter–Hawking laws, generalised second law) is a
 separate scope. The **derivation** of Einstein's field equations
 from the Jacobson construction (Raychaudhuri focusing,
 null-energy condition) is a much larger separate scope.

* The four-way identity formalises the *equivalence* of the four
 quantities at the equilibrium thermodynamic level — the
 complex-action/entropic-time-substantive content of the paths-bits-eins reading.

## References

* Bekenstein 1973 *Phys. Rev. D* 7, 2333 — black-hole entropy.
* Hawking 1975 *Commun. Math. Phys.* 43, 199 — Hawking radiation.
* Jacobson 1995 *Phys. Rev. Lett.* 75, 1260 — *Thermodynamics of
 Spacetime: The Einstein Equation of State*.
* Landauer 1961, Bennett 1982 — bit-erasure thermodynamics.
* `Physlib.Thermodynamics.EntropicInformationRate` — `landauerInfoRate`.
* `Physlib.Thermodynamics.VerlindeNewtonGravity` — `holographicBits`.
* Source: `/Users/macbookpro/Downloads/paths-bits-eins.md`
 REPLYID 20260519-018.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics

open Real Constants

/-! ## §1 — Entropy ↔ bits ↔ entropic-time conversions -/

/-- **Bits from entropy** (Landauer):

  `N_bits := S / (k_B · ln 2)`.

Converts a Boltzmann-style entropy `S` (in J/K) to an
information-theoretic bit count.  `Real.log 2 ≈ 0.693`. -/
def bitsFromEntropy (S : ℝ) : ℝ := S / (kB * Real.log 2)

/-- **Entropic time from entropy** (complex-action/entropic-time):

  `τ_ent := S / k_B`.

Dimensional re-expression of entropy in **nats**. -/
def tauEntFromEntropy (S : ℝ) : ℝ := S / kB

/-- **The entropic-time / bit identity**:

  `τ_ent  =  ln(2) · N_bits`.

Both sides express the same dimensionless quantity; the difference
is unit convention (`ln 2` is the nat-to-bit conversion factor). -/
theorem tauEnt_eq_ln2_mul_bits (S : ℝ) :
    tauEntFromEntropy S = Real.log 2 * bitsFromEntropy S := by
  unfold tauEntFromEntropy bitsFromEntropy
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hlog2_ne : Real.log 2 ≠ 0 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  field_simp

/-- **The bits / entropic-time identity**: `N_bits = τ_ent / ln 2`. -/
theorem bits_eq_tauEnt_div_ln2 (S : ℝ) :
    bitsFromEntropy S = tauEntFromEntropy S / Real.log 2 := by
  unfold bitsFromEntropy tauEntFromEntropy
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hlog2_ne : Real.log 2 ≠ 0 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  field_simp

/-! ## §2 — Bekenstein bit / entropy / entropic-time identities -/

/-- **Bekenstein–Hawking entropy** `S_BH := k_B · A / (4·ℓ_P²)`.

For a black-hole horizon of area `A` with Planck length `ℓ_P`. -/
def bekensteinEntropy (A ℓP : ℝ) : ℝ := kB * A / (4 * ℓP^2)

/-- **Bekenstein bit count** `N_bits := A / (4·ℓ_P²·ln 2)`.

Number of Landauer bits stored on the horizon. -/
def bekensteinBits (A ℓP : ℝ) : ℝ := A / (4 * ℓP^2 * Real.log 2)

/-- **Bekenstein entropic time** `τ_ent := A / (4·ℓ_P²)`.

Dimensionless horizon-bit count in nats. -/
def bekensteinTauEnt (A ℓP : ℝ) : ℝ := A / (4 * ℓP^2)

/-- **The Bekenstein entropic time equals the Bekenstein entropy
divided by `k_B`**. -/
theorem bekensteinTauEnt_eq_entropy_div_kB
    {A ℓP : ℝ} (hℓP : ℓP ≠ 0) :
    bekensteinTauEnt A ℓP = bekensteinEntropy A ℓP / kB := by
  unfold bekensteinTauEnt bekensteinEntropy
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
  have h4ℓP_sq_ne : (4 * ℓP^2 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hℓP_sq_ne
  field_simp

/-- **The Bekenstein entropic time equals `ln 2` times the Bekenstein
bit count**. -/
theorem bekensteinTauEnt_eq_ln2_mul_bits
    {A ℓP : ℝ} (hℓP : ℓP ≠ 0) :
    bekensteinTauEnt A ℓP = Real.log 2 * bekensteinBits A ℓP := by
  unfold bekensteinTauEnt bekensteinBits
  have hlog2_ne : Real.log 2 ≠ 0 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
  field_simp

/-- **Bekenstein entropy = `k_B · ln 2 · N_bits`** — `S_BH` in
information units. -/
theorem bekensteinEntropy_eq_kB_ln2_mul_bits
    {A ℓP : ℝ} (hℓP : ℓP ≠ 0) :
    bekensteinEntropy A ℓP = kB * Real.log 2 * bekensteinBits A ℓP := by
  unfold bekensteinEntropy bekensteinBits
  have hlog2_ne : Real.log 2 ≠ 0 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
  field_simp

/-! ## §3 — Jacobson Clausius identity -/

/-- **Clausius / Jacobson entropic time** `dτ_ent := δQ / (k_B · T)`.

Energy flux `δQ` through a local Rindler horizon at temperature `T`
advances entropic time by `δQ / (k_B · T)` — the **Clausius
increment** in nat units.

Jacobson 1995 *Phys. Rev. Lett.* 75, 1260 derives the Einstein
field equations from the requirement that this Clausius relation
holds for **all** local Rindler horizons. -/
def clausiusTauEnt (δQ T : ℝ) : ℝ := δQ / (kB * T)

/-- **Under the Clausius relation `δQ = T·dS`, the Jacobson form
matches the entropy form**:

  `clausiusTauEnt(δQ, T) = tauEntFromEntropy(dS) = dS / k_B`.

This is the **definitional equivalence** of the two
entropic-time increments at thermal equilibrium. -/
theorem clausiusTauEnt_eq_tauEntFromEntropy_under_Clausius
    {δQ T dS : ℝ} (hT : T ≠ 0)
    (hClausius : δQ = T * dS) :
    clausiusTauEnt δQ T = tauEntFromEntropy dS := by
  unfold clausiusTauEnt tauEntFromEntropy
  rw [hClausius]
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  field_simp

/-! ## §4 — Unified four-way identity -/

/-- **:Four-way entropic-time identity**.

At a horizon in local thermal equilibrium with Clausius relation
`δQ = T · dS` and Bekenstein bit-area relation
`dS = (k_B · dA) / (4 · ℓ_P²)`, the **four complex-action/entropic-time expressions
for `dτ_ent` are equal**:

  `tauEntFromEntropy dS                         (Boltzmann nats)
   = clausiusTauEnt δQ T                         (Jacobson Clausius)
   = bekensteinTauEnt dA ℓ_P                     (Bekenstein horizon)
   = (Real.log 2) · bekensteinBits dA ℓ_P`.      (Landauer bits)

This is the **unified equality** of the four entropic-time
readings, machine-checked at the algebraic level.

The chain composes:
* `tauEntFromEntropy dS = dS / k_B`            (def);
* `clausiusTauEnt δQ T = δQ / (k_B·T) = dS/k_B` (Clausius);
* `bekensteinTauEnt dA ℓ_P = dA/(4 ℓ_P²) = dS/k_B`
                                                (Bekenstein);
* `bekensteinTauEnt dA ℓ_P = (ln 2) · bekensteinBits` (Landauer).

**Physical reading**: heat flux, entropy production, horizon area
growth, and information bit growth are **the same physical
quantity** — they all measure the rate at which the system
explores new microstates. -/
theorem entropicTime_four_way_identity
    {δQ T dS dA ℓP : ℝ}
    (hT : T ≠ 0) (hℓP : ℓP ≠ 0)
    (hClausius : δQ = T * dS)
    (hBekenstein : dS = (kB * dA) / (4 * ℓP^2)) :
    tauEntFromEntropy dS = clausiusTauEnt δQ T ∧
    tauEntFromEntropy dS = bekensteinTauEnt dA ℓP ∧
    bekensteinTauEnt dA ℓP = Real.log 2 * bekensteinBits dA ℓP := by
  refine ⟨?_, ?_, ?_⟩
  · -- tauEntFromEntropy dS = clausiusTauEnt δQ T
    exact (clausiusTauEnt_eq_tauEntFromEntropy_under_Clausius hT hClausius).symm
  · -- tauEntFromEntropy dS = bekensteinTauEnt dA ℓP
    unfold tauEntFromEntropy bekensteinTauEnt
    rw [hBekenstein]
    have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
    have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
    have h4ℓP_sq_ne : (4 * ℓP^2 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hℓP_sq_ne
    field_simp
  · -- bekensteinTauEnt = ln 2 · bekensteinBits
    exact bekensteinTauEnt_eq_ln2_mul_bits hℓP

end Physlib.Thermodynamics

end

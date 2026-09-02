/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.StatisticalMechanics.BoltzmannConstant
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv

meta import Zil

/-!
# Unified entropic-time / bits / Bekenstein / Jacobson identity

Port of the complex-action/entropic-time unification chain from
`paths-bits-eins.md` REPLYID
20260519-018.  The chain identifies four expressions for the same
quantity:

  `dτ_ent  =  dS / k_B  =  δQ / (k_B·T)  =  dA / (4·ℓ_P²)
           =  (ln 2) · d N_bits`.

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
information cells".  Jacobson derives spacetime dynamics by
imposing the **Clausius relation** `δQ = T·dS` on **all local
Rindler horizons**: requiring this for arbitrary null directions
yields the **Einstein field equations**.  complex-action/entropic-time recasts both:

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


* `bitsFromEntropy S := S / (k_B · ln 2)` — Landauer.
* `tauEntFromEntropy S := S / k_B` — complex-action/entropic-time.
* `tauEnt_eq_ln2_mul_bits` — `τ_ent = ln(2) · bits`.


* `bekensteinEntropy A ℓP := k_B · A / (4·ℓP²)` — paper Eq.,
  `S_BH`.
* `bekensteinBits A ℓP := A / (4·ℓP²·ln 2)`.
* `bekensteinTauEnt A ℓP := A / (4·ℓP²)`.
* `bekensteinTauEnt_eq_entropy_div_kB` — algebraic equality.
* `bekensteinTauEnt_eq_ln2_mul_bits` — Bekenstein bits/ent-time.


* `clausiusTauEnt δQ T := δQ / (k_B · T)` — Jacobson 1995.
* `clausiusTauEnt_eq_tauEntFromEntropy_under_Clausius` — under
  `dS = δQ / T`, the Jacobson form matches the entropy form.


* **`entropicTime_four_way_identity`** — at horizon thermal
  equilibrium with `δQ = T · dS` and `dS = (k_B · dA) / (4 · ℓ_P²)`,
  the four expressions for `dτ_ent` are pairwise equal.
* **`FutureRegularNullRaychaudhuri.expansion_nonneg`** — the null
  Raychaudhuri focusing argument: a globally regular future generator
  cannot have negative expansion under nonnegative shear and null Ricci
  contraction.
* **`FutureRegularHorizonAreaEvolution.area_monotone`** — Hawking
  horizon-area monotonicity on that future-regular carrier.
* **`FutureRegularHorizonAreaEvolution.generalizedEntropy_monotone`** —
  the generalized second law when the exterior entropy-loss rate is
  bounded by the derived horizon-entropy gain.

## Honest scope

* The original sections provide the **algebraic identities** of the
  unification. The new null section proves the scalar four-dimensional
  Raychaudhuri focusing comparison and global area monotonicity on an
  explicit future-regular horizon carrier. Global differentiability on
  the whole affine line is the no-caustic/future-regularity premise; the
  shear square and null Ricci contraction are explicitly nonnegative.
  Deriving those scalar data from a spacetime metric, proving event-horizon
  achronality/future completeness, and deriving the null energy condition
  from matter are separate differential-geometric inputs.

* The generalized second law does not follow from the classical area
  theorem alone. Its theorem therefore exposes the quantum exterior
  entropy-loss bound `-S_out' ≤ S_BH'`; it proves global monotonicity from
  that local production inequality rather than assuming the final
  two-time GSL conclusion.

* The four-way identity formalises the *equivalence* of the four
  quantities at the equilibrium thermodynamic level — the
  complex-action/entropic-time-substantive content of the paths-bits-eins reading.

## References

* Bekenstein 1973 *Phys. Rev. D* 7, 2333 — black-hole entropy.
* Hawking 1975 *Commun. Math. Phys.* 43, 199 — Hawking radiation.
* Hawking 1971 *Phys. Rev. Lett.* 26, 1344 — event-horizon area theorem.
* Jacobson 1995 *Phys. Rev. Lett.* 75, 1260 — *Thermodynamics of
  Spacetime: The Einstein Equation of State*.
* Landauer 1961, Bennett 1982 — bit-erasure thermodynamics.
* `Physlib.Thermodynamics.EntropicInformationRate` — `landauerInfoRate`.
* `Physlib.Thermodynamics.VerlindeNewtonGravity` — `holographicBits`.
* Source: `paths-bits-eins.md`
  REPLYID 20260519-018.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics

open Real Constants


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
lemma tauEnt_eq_ln2_mul_bits (S : ℝ) :
    tauEntFromEntropy S = Real.log 2 * bitsFromEntropy S := by
  unfold tauEntFromEntropy bitsFromEntropy
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hlog2_ne : Real.log 2 ≠ 0 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt hlog2_pos
  field_simp

/-- **The bits / entropic-time identity**: `N_bits = τ_ent / ln 2`. -/
lemma bits_eq_tauEnt_div_ln2 (S : ℝ) :
    bitsFromEntropy S = tauEntFromEntropy S / Real.log 2 := by
  unfold bitsFromEntropy tauEntFromEntropy
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hlog2_ne : Real.log 2 ≠ 0 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt hlog2_pos
  field_simp


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
lemma bekensteinTauEnt_eq_entropy_div_kB
    {A ℓP : ℝ} (hℓP : ℓP ≠ 0) :
    bekensteinTauEnt A ℓP = bekensteinEntropy A ℓP / kB := by
  unfold bekensteinTauEnt bekensteinEntropy
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
  have h4ℓP_sq_ne : (4 * ℓP^2 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hℓP_sq_ne
  field_simp

/-- **The Bekenstein entropic time equals `ln 2` times the Bekenstein
bit count**. -/
lemma bekensteinTauEnt_eq_ln2_mul_bits
    {A ℓP : ℝ} (hℓP : ℓP ≠ 0) :
    bekensteinTauEnt A ℓP = Real.log 2 * bekensteinBits A ℓP := by
  unfold bekensteinTauEnt bekensteinBits
  have hlog2_ne : Real.log 2 ≠ 0 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt hlog2_pos
  have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
  field_simp

/-- **Bekenstein entropy = `k_B · ln 2 · N_bits`** — `S_BH` in
information units. -/
lemma bekensteinEntropy_eq_kB_ln2_mul_bits
    {A ℓP : ℝ} (hℓP : ℓP ≠ 0) :
    bekensteinEntropy A ℓP = kB * Real.log 2 * bekensteinBits A ℓP := by
  unfold bekensteinEntropy bekensteinBits
  have hlog2_ne : Real.log 2 ≠ 0 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt hlog2_pos
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
  field_simp


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
lemma clausiusTauEnt_eq_tauEntFromEntropy_under_Clausius
    {δQ T dS : ℝ} (hT : T ≠ 0)
    (hClausius : δQ = T * dS) :
    clausiusTauEnt δQ T = tauEntFromEntropy dS := by
  unfold clausiusTauEnt tauEntFromEntropy
  rw [hClausius]
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  field_simp


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
lemma entropicTime_four_way_identity
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


/-! ## Null Raychaudhuri focusing and Hawking area monotonicity -/

/-- A future-regular four-dimensional null-congruence carrier.

The expansion is differentiable on the entire affine line and obeys the null
Raychaudhuri equation
`θ' = -θ²/2 - σ² - R_ab k^a k^b`. Nonnegative `shearSq` is geometric;
nonnegative `ricciNull` is the null convergence condition (equivalent to the
null energy condition under Einstein's equation).

Having a finite differentiable expansion for every future affine parameter is
the strong no-caustic/future-regularity input appropriate to an event-horizon
generator. The structure does not derive that global causal fact. -/
structure FutureRegularNullRaychaudhuri where
  /-- Null expansion scalar `θ(λ)`. -/
  expansion : ℝ → ℝ
  /-- Squared shear `σ_ab σ^ab`. -/
  shearSq : ℝ → ℝ
  /-- Null Ricci contraction `R_ab k^a k^b`. -/
  ricciNull : ℝ → ℝ
  /-- The four-dimensional null Raychaudhuri equation. -/
  expansion_hasDerivAt : ∀ s,
    HasDerivAt expansion
      (-(expansion s) ^ 2 / 2 - shearSq s - ricciNull s) s
  /-- The shear square is nonnegative. -/
  shearSq_nonneg : ∀ s, 0 ≤ shearSq s
  /-- Null convergence/energy condition. -/
  ricciNull_nonneg : ∀ s, 0 ≤ ricciNull s

namespace FutureRegularNullRaychaudhuri

/-- Derivative of `1/θ` obtained from Raychaudhuri wherever `θ ≠ 0`. -/
noncomputable def reciprocalRate
    (R : FutureRegularNullRaychaudhuri) (s : ℝ) : ℝ :=
  ((R.expansion s) ^ 2 / 2 + R.shearSq s + R.ricciNull s) /
    (R.expansion s) ^ 2

/-- Raychaudhuri plus nonnegative shear/null Ricci contraction makes the
expansion nonincreasing along each generator. -/
lemma expansion_deriv_nonpos (R : FutureRegularNullRaychaudhuri) (s : ℝ) :
    deriv R.expansion s ≤ 0 := by
  rw [(R.expansion_hasDerivAt s).deriv]
  nlinarith [R.shearSq_nonneg s, R.ricciNull_nonneg s,
    sq_nonneg (R.expansion s)]

/-- The expansion is globally antitone along the affine parameter. -/
lemma expansion_antitone (R : FutureRegularNullRaychaudhuri) :
    Antitone R.expansion := by
  apply antitone_of_deriv_nonpos
  · exact fun s => (R.expansion_hasDerivAt s).differentiableAt
  · exact R.expansion_deriv_nonpos

/-- The reciprocal expansion has the exact derivative supplied by
Raychaudhuri. -/
lemma reciprocal_hasDerivAt (R : FutureRegularNullRaychaudhuri) (s : ℝ)
    (hθ : R.expansion s ≠ 0) :
    HasDerivAt (fun u => 1 / R.expansion u) (R.reciprocalRate s) s := by
  have h := (R.expansion_hasDerivAt s).inv hθ
  have h' : HasDerivAt (fun u => 1 / R.expansion u)
      (-(-R.expansion s ^ 2 / 2 - R.shearSq s - R.ricciNull s) /
        R.expansion s ^ 2) s :=
    h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => by simp only [Pi.inv_apply, one_div])
  apply h'.congr_deriv
  unfold reciprocalRate
  field_simp
  ring

/-- Under the null convergence condition, `(1/θ)' ≥ 1/2` wherever
`θ ≠ 0`. This is the quantitative core of the four-dimensional focusing
estimate. -/
lemma one_half_le_reciprocalRate
    (R : FutureRegularNullRaychaudhuri) (s : ℝ)
    (hθ : R.expansion s ≠ 0) :
    (1 / 2 : ℝ) ≤ R.reciprocalRate s := by
  unfold reciprocalRate
  have hsq : 0 < R.expansion s ^ 2 := sq_pos_of_ne_zero hθ
  rw [le_div_iff₀ hsq]
  nlinarith [R.shearSq_nonneg s, R.ricciNull_nonneg s]

/-- **[Null focusing contradiction].**
If `θ(s) < 0` and remains finite and negative through
`T = s - 2/θ(s)`, then integrating `(1/θ)' ≥ 1/2` makes
`1/θ(T) ≥ 0`, contradicting `θ(T) < 0`. Thus a negative expansion
must form a focal point within affine length at most `-2/θ(s)`. -/
theorem focusing_contradiction
    (R : FutureRegularNullRaychaudhuri) (s T : ℝ)
    (hs : R.expansion s < 0)
    (hT : T = s - 2 / R.expansion s)
    (hneg : ∀ u ∈ Set.Icc s T, R.expansion u < 0) : False := by
  have hsT : s < T := by
    rw [hT]
    have hdiv : 2 / R.expansion s < 0 :=
      div_neg_of_pos_of_neg (by norm_num) hs
    have : 0 < -(2 / R.expansion s) := neg_pos.mpr hdiv
    linarith
  let f : ℝ → ℝ := fun u => 1 / R.expansion u
  have hf : ContinuousOn f (Set.Icc s T) := by
    intro u hu
    exact (R.reciprocal_hasDerivAt u
      (ne_of_lt (hneg u hu))).continuousAt.continuousWithinAt
  have hfdiff : DifferentiableOn ℝ f (interior (Set.Icc s T)) := by
    intro u hu
    have hu' : u ∈ Set.Icc s T := interior_subset hu
    exact (R.reciprocal_hasDerivAt u
      (ne_of_lt (hneg u hu'))).differentiableAt.differentiableWithinAt
  have hfderiv :
      ∀ u ∈ interior (Set.Icc s T), (1 / 2 : ℝ) ≤ deriv f u := by
    intro u hu
    have hu' : u ∈ Set.Icc s T := interior_subset hu
    rw [(R.reciprocal_hasDerivAt u (ne_of_lt (hneg u hu'))).deriv]
    exact R.one_half_le_reciprocalRate u (ne_of_lt (hneg u hu'))
  have hbound := (convex_Icc s T).mul_sub_le_image_sub_of_le_deriv
    hf hfdiff hfderiv s ⟨le_rfl, hsT.le⟩ T ⟨hsT.le, le_rfl⟩ hsT.le
  change (1 / 2 : ℝ) * (T - s) ≤
    1 / R.expansion T - 1 / R.expansion s at hbound
  have hleft :
      (1 / 2 : ℝ) * (T - s) = -(1 / R.expansion s) := by
    rw [hT]
    field_simp
    ring
  rw [hleft] at hbound
  have hinvT : 1 / R.expansion T < 0 :=
    one_div_neg.mpr (hneg T ⟨hsT.le, le_rfl⟩)
  linarith

/-- **[Future-regular event-horizon generators have nonnegative expansion].**
A negative value would stay negative because expansion is antitone, but the
focusing estimate says that no globally differentiable finite expansion can
remain negative through the corresponding finite affine time. -/
theorem expansion_nonneg
    (R : FutureRegularNullRaychaudhuri) (s : ℝ) :
    0 ≤ R.expansion s := by
  by_contra h
  have hs : R.expansion s < 0 := lt_of_not_ge h
  let T := s - 2 / R.expansion s
  have hneg : ∀ u ∈ Set.Icc s T, R.expansion u < 0 := by
    intro u hu
    exact lt_of_le_of_lt (R.expansion_antitone hu.1) hs
  exact R.focusing_contradiction s T hs rfl hneg

end FutureRegularNullRaychaudhuri


/-! ## Horizon area and generalized entropy transport -/

/-- A future-regular null Raychaudhuri congruence with a positive horizon
cross-section area satisfying the geometric transport equation
`A' = θA`. -/
structure FutureRegularHorizonAreaEvolution extends
    FutureRegularNullRaychaudhuri where
  /-- Horizon cross-section area. -/
  area : ℝ → ℝ
  /-- Cross-section area is strictly positive. -/
  area_pos : ∀ s, 0 < area s
  /-- Expansion transports area by `A' = θA`. -/
  area_hasDerivAt : ∀ s,
    HasDerivAt area (expansion s * area s) s

namespace FutureRegularHorizonAreaEvolution

/-- Nonnegative null expansion gives a nonnegative area derivative. -/
lemma area_deriv_nonneg
    (H : FutureRegularHorizonAreaEvolution) (s : ℝ) :
    0 ≤ deriv H.area s := by
  rw [(H.area_hasDerivAt s).deriv]
  exact mul_nonneg
    (H.toFutureRegularNullRaychaudhuri.expansion_nonneg s)
    (H.area_pos s).le

/-- **[Hawking area theorem on the future-regular scalar carrier].**
Every horizon cross-section area is monotone along the affine parameter. -/
theorem area_monotone (H : FutureRegularHorizonAreaEvolution) :
    Monotone H.area := by
  apply monotone_of_deriv_nonneg
  · exact fun s => (H.area_hasDerivAt s).differentiableAt
  · exact H.area_deriv_nonneg

/-- Bekenstein–Hawking entropy-production rate obtained from
`S_BH = k_B A/(4ℓ_P²)` and `A' = θA`. -/
noncomputable def horizonEntropyRate
    (H : FutureRegularHorizonAreaEvolution) (ℓP s : ℝ) : ℝ :=
  Constants.kB * (H.expansion s * H.area s) / (4 * ℓP ^ 2)

/-- The horizon entropy-production rate is the actual derivative of the
repository's existing `bekensteinEntropy`. -/
lemma horizonEntropy_hasDerivAt
    (H : FutureRegularHorizonAreaEvolution) (ℓP s : ℝ) :
    HasDerivAt (fun u => bekensteinEntropy (H.area u) ℓP)
      (H.horizonEntropyRate ℓP s) s := by
  have h :=
    ((H.area_hasDerivAt s).const_mul Constants.kB).div_const (4 * ℓP ^ 2)
  simpa [bekensteinEntropy, horizonEntropyRate] using h

/-- Bekenstein–Hawking entropy is globally monotone whenever the Planck
length is nonzero. -/
theorem horizonEntropy_monotone
    (H : FutureRegularHorizonAreaEvolution) (ℓP : ℝ) (hℓP : ℓP ≠ 0) :
    Monotone (fun s => bekensteinEntropy (H.area s) ℓP) := by
  intro s t hst
  have harea := H.area_monotone hst
  unfold bekensteinEntropy
  have hsquare : 0 < ℓP ^ 2 := sq_pos_of_ne_zero hℓP
  have hcoef : 0 < Constants.kB / (4 * ℓP ^ 2) :=
    div_pos Constants.kB_pos (mul_pos (by norm_num) hsquare)
  calc
    Constants.kB * H.area s / (4 * ℓP ^ 2)
        = (Constants.kB / (4 * ℓP ^ 2)) * H.area s := by ring
    _ ≤ (Constants.kB / (4 * ℓP ^ 2)) * H.area t :=
      mul_le_mul_of_nonneg_left harea hcoef.le
    _ = Constants.kB * H.area t / (4 * ℓP ^ 2) := by ring

/-- Generalized entropy `S_gen = S_BH + S_out`. -/
noncomputable def generalizedEntropy
    (H : FutureRegularHorizonAreaEvolution) (ℓP : ℝ)
    (exteriorEntropy : ℝ → ℝ) (s : ℝ) : ℝ :=
  bekensteinEntropy (H.area s) ℓP + exteriorEntropy s

/-- **[Generalized second law from a local exterior-loss bound].**
If the exterior entropy has rate `S_out'` and its loss never exceeds the
derived Bekenstein–Hawking entropy gain,
`-S_out' ≤ S_BH'`, then `S_BH + S_out` is globally monotone.
The theorem proves the two-time GSL from the local production inequality;
it does not derive that quantum exterior inequality from classical geometry. -/
theorem generalizedEntropy_monotone
    (H : FutureRegularHorizonAreaEvolution) (ℓP : ℝ)
    (exteriorEntropy exteriorRate : ℝ → ℝ)
    (hexterior : ∀ s, HasDerivAt exteriorEntropy (exteriorRate s) s)
    (hloss : ∀ s, -exteriorRate s ≤ H.horizonEntropyRate ℓP s) :
    Monotone (H.generalizedEntropy ℓP exteriorEntropy) := by
  have hderiv : ∀ s,
      HasDerivAt (H.generalizedEntropy ℓP exteriorEntropy)
        (H.horizonEntropyRate ℓP s + exteriorRate s) s := by
    intro s
    exact (H.horizonEntropy_hasDerivAt ℓP s).add (hexterior s)
  apply monotone_of_deriv_nonneg
  · exact fun s => (hderiv s).differentiableAt
  · intro s
    rw [(hderiv s).deriv]
    linarith [hloss s]

end FutureRegularHorizonAreaEvolution

end Physlib.Thermodynamics

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.expansion_deriv_nonpos where
  formalizes @ "claim:null-raychaudhuri-with-nec-makes-null-expansion-nonincreasing",
  supported_by @ "paper:hawking-1971-area-theorem",
  supported_by @ "paper:jacobson-1995-thermodynamics-of-spacetime",
  epistemic_status @ "conditional-model",
  caveat @ "claim:raychaudhuri-equation-nonnegative-shear-and-null-ricci-contraction-are-explicit-carrier-data"

zil attach Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.focusing_contradiction where
  formalizes @ "claim:negative-null-expansion-focuses-within-affine-length-minus-two-over-theta",
  supported_by @ "paper:hawking-1971-area-theorem",
  epistemic_status @ "conditional-model",
  caveat @ "claim:four-dimensional-scalar-focusing-comparison-not-a-construction-of-null-geodesics-from-a-metric"

zil attach Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.expansion_nonneg where
  formalizes @ "claim:future-regular-horizon-generator-has-nonnegative-expansion",
  supported_by @ "paper:hawking-1971-area-theorem",
  requires @ "claim:negative-null-expansion-focuses-within-affine-length-minus-two-over-theta",
  epistemic_status @ "conditional-model",
  caveat @ "claim:global-differentiability-on-the-affine-line-encodes-future-regularity-and-absence-of-a-focal-endpoint"

zil attach Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.area_monotone where
  formalizes @ "claim:hawking-horizon-area-is-monotone-on-future-regular-null-generators",
  supported_by @ "paper:hawking-1971-area-theorem",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:future-regular-horizon-generator-has-nonnegative-expansion",
  epistemic_status @ "conditional-model",
  caveat @ "claim:area-transport-A-prime-equals-theta-times-A-and-positive-cross-section-area-are-explicit-geometric-data"

zil attach Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.horizonEntropy_hasDerivAt where
  formalizes @ "claim:bekenstein-hawking-entropy-rate-is-kb-theta-A-over-four-planck-area",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:hawking-horizon-area-is-monotone-on-future-regular-null-generators",
  epistemic_status @ "conditional-model",
  caveat @ "claim:uses-the-bekenstein-hawking-area-entropy-identification"

zil attach Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.horizonEntropy_monotone where
  formalizes @ "claim:bekenstein-hawking-horizon-entropy-is-globally-monotone",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:hawking-horizon-area-is-monotone-on-future-regular-null-generators",
  epistemic_status @ "conditional-model",
  caveat @ "claim:classical-horizon-entropy-monotonicity-not-the-quantum-generalized-second-law-by-itself"

zil attach Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.generalizedEntropy_monotone where
  formalizes @ "claim:generalized-black-hole-entropy-is-monotone-from-local-exterior-loss-bound",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:bekenstein-hawking-entropy-rate-is-kb-theta-A-over-four-planck-area",
  epistemic_status @ "conditional-model",
  caveat @ "claim:the-local-quantum-bound-minus-Sout-prime-le-SBH-prime-is-explicit-and-is-not-derived-from-classical-raychaudhuri"

zil_file_contract physlib.bekensteinJacobsonEntropicBits where
  promises "The entropy/nats/Clausius/horizon-area/bit dictionary; the four-dimensional scalar null-Raychaudhuri focusing comparison under nonnegative shear and null Ricci contraction; nonnegative expansion on a globally future-regular generator; monotone positive horizon area; the actual Bekenstein-Hawking entropy derivative and its monotonicity; and global generalized-entropy monotonicity from an explicit local exterior entropy-loss bound."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Constants.kB", "lean:Real.log",
    "lean:HasDerivAt", "lean:Convex.mul_sub_le_image_sub_of_le_deriv"]
  forbids_substitutes ["deriving future completeness or event-horizon achronality from a spacetime metric",
    "deriving the null energy condition from a quantum matter theory",
    "claiming the quantum exterior entropy-loss bound follows from the classical area theorem",
    "deriving the Einstein equation from Clausius data in this file"]
  witnessed_by [
    Physlib.Thermodynamics.entropicTime_four_way_identity,
    Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.focusing_contradiction,
    Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.expansion_nonneg,
    Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.area_monotone,
    Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.horizonEntropy_hasDerivAt,
    Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.horizonEntropy_monotone,
    Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.generalizedEntropy_monotone]

/- ZIL-END -/

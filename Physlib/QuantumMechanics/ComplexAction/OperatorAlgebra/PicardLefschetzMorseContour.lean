/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QFTPathIntegralComplexAction
public import Physlib.QFT.PathIntegral.FeynmanKac

/-!
# Picard-Lefschetz / Morse steepest-descent contours for the complex-action path integral

This file adds the contour-selection layer that sits between the existing
Nagao--Nielsen/Feynman complex-action kernel and the analytic contour machinery.

The analytic statement in Picard-Lefschetz theory is that admissible contours are
assembled from steepest-descent thimbles of the Morse function

`h = Re (i S / hbar) = - S_I / hbar`.

Along such a thimble the real phase `S_R` is constant, while the imaginary action
`S_I` is nondecreasing away from the saddle.  Therefore the Nagao--Nielsen
weight

`exp(i S_R / hbar - S_I / hbar)`

has no phase drift and its modulus is bounded by the saddle modulus.  This is
exactly the Feynman--Kac damping factor already used in the repo.

The file formalizes that consequence in a finite/discrete structure.  It does not
claim a global infinite-dimensional thimble-existence theorem; instead, it gives
the checked theorem that any Morse/Picard-Lefschetz flow certificate supplies a
valid steepest-descent contour for the existing path-integral kernel.
-/

set_option autoImplicit false

universe u

@[expose] public section

noncomputable section

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open MeasureTheory

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour

/-! ## Li: attractor Morse-Lyapunov certificates and Morse inequalities -/

/-- A checkable representative for Li's Theorems 3.1 and 3.5: a Lyapunov function on an attraction basin with a
nonnegative decay rate.  The field `radiallyUnbounded` records the topological properness/radial
unboundedness assertion; the algebraic consequences use the Dini-derivative inequality. -/
structure AttractorLyapunovCertificate (State : Type*) where
  basin : Set State
  attractor : Set State
  V : State -> ℝ
  diniDerivative : State -> ℝ
  decayRate : State -> ℝ
  radiallyUnbounded : Prop
  zero_on_attractor : forall {x : State}, x ∈ attractor -> V x = 0
  nonnegative : forall x : State, x ∈ basin -> 0 ≤ V x
  decay_le_neg : forall x : State, x ∈ basin -> diniDerivative x ≤ -decayRate x
  decayRate_nonneg : forall x : State, x ∈ basin -> 0 ≤ decayRate x
  decayRate_pos_off_attractor :
    forall x : State, x ∈ basin -> x ∉ attractor -> 0 < decayRate x

namespace AttractorLyapunovCertificate

variable {State : Type*} (C : AttractorLyapunovCertificate State)

/-- **[Li, Theorem 3.1/3.5 consequence]** The Dini derivative of a certified attractor Lyapunov function is
nonpositive on the basin. -/
theorem diniDerivative_nonpos {x : State} (hx : x ∈ C.basin) :
    C.diniDerivative x ≤ 0 := by
  exact le_trans (C.decay_le_neg x hx) (neg_nonpos.mpr (C.decayRate_nonneg x hx))

/-- **[Li, Theorem 3.1/3.5 consequence]** The Lyapunov function strictly decreases off the attractor when
the supplied decay rate is positive there. -/
theorem diniDerivative_neg_off_attractor {x : State} (hx : x ∈ C.basin) (hnot : x ∉ C.attractor) :
    C.diniDerivative x < 0 := by
  exact lt_of_le_of_lt (C.decay_le_neg x hx)
    (neg_lt_zero.mpr (C.decayRate_pos_off_attractor x hx hnot))

end AttractorLyapunovCertificate

/-- A global strict Morse-Lyapunov function for an ordered Morse decomposition, corresponding to Li's
Definition 4.1 and Theorem 4.3.  `morseUnion` is the paper's `R = ⋃ₖ Mₖ`. -/
structure StrictMorseLyapunovCertificate (State Index : Type*) [LT Index] where
  morseSet : Index -> Set State
  morseUnion : Set State
  V : State -> ℝ
  criticalValue : Index -> ℝ
  diniDerivative : State -> ℝ
  decayRate : State -> ℝ
  constant_on_morse :
    forall (i : Index) {x : State}, x ∈ morseSet i -> V x = criticalValue i
  values_strict : forall {i j : Index}, i < j -> criticalValue i < criticalValue j
  decay_le_neg : forall x : State, diniDerivative x ≤ -decayRate x
  decayRate_nonneg : forall x : State, 0 ≤ decayRate x
  decayRate_zero_on_morseUnion : forall {x : State}, x ∈ morseUnion -> decayRate x = 0
  decayRate_pos_off_morseUnion : forall {x : State}, x ∉ morseUnion -> 0 < decayRate x

namespace StrictMorseLyapunovCertificate

variable {State Index : Type*} [LT Index] (C : StrictMorseLyapunovCertificate State Index)

/-- **[Generalized critical values are ordered]** A strict Morse-Lyapunov certificate gives
`V(Mᵢ) < V(Mⱼ)` whenever the Morse sets are ordered by `i < j`. -/
theorem criticalValue_strict {i j : Index} (hij : i < j) :
    C.criticalValue i < C.criticalValue j :=
  C.values_strict hij

/-- **[Li, Eq. 4.1/4.2 consequence]** The Dini derivative is nonpositive everywhere covered by the
certificate. -/
theorem diniDerivative_nonpos (x : State) :
    C.diniDerivative x ≤ 0 := by
  exact le_trans (C.decay_le_neg x) (neg_nonpos.mpr (C.decayRate_nonneg x))

/-- **[Strict Morse-Lyapunov decrease]** Off the union of Morse sets, `D⁺V < 0`. -/
theorem diniDerivative_neg_off_morseUnion {x : State} (hx : x ∉ C.morseUnion) :
    C.diniDerivative x < 0 := by
  exact lt_of_le_of_lt (C.decay_le_neg x)
    (neg_lt_zero.mpr (C.decayRate_pos_off_morseUnion hx))

/-- On the Morse union, the certified decay rate vanishes, matching Li's `v ≡ 0` on `R`. -/
theorem decayRate_eq_zero_on_morseUnion {x : State} (hx : x ∈ C.morseUnion) :
    C.decayRate x = 0 :=
  C.decayRate_zero_on_morseUnion hx

end StrictMorseLyapunovCertificate

/-- The critical value assigned by Li's construction (Eq. 4.8) to the `k`-th Morse set in a finite
filtration, using zero-based `Fin` indices.  Paper notation gives `V(Mₖ)=k-1`; in Lean this is `k.val`. -/
def finiteMorseCriticalValue {l : ℕ} (k : Fin l) : ℝ := k.val

/-- The constructed finite-filtration critical values are strictly ordered. -/
theorem finiteMorseCriticalValue_strict {l : ℕ} {i j : Fin l} (hij : i < j) :
    finiteMorseCriticalValue i < finiteMorseCriticalValue j := by
  change (i.val : ℝ) < (j.val : ℝ)
  exact_mod_cast (Fin.lt_def.mp hij)

/-- Adjacent finite-filtration values differ by one when the successor index exists. -/
theorem finiteMorseCriticalValue_succ {l : ℕ} (k : Fin l) (hk : k.val + 1 < l) :
    finiteMorseCriticalValue ⟨k.val + 1, hk⟩ = finiteMorseCriticalValue k + 1 := by
  simp [finiteMorseCriticalValue]

/-- Ranks of critical groups `C_q(M_k)`.  This abstracts Li's Definition 6.1 without choosing a concrete
singular homology implementation in this file. -/
structure CriticalGroupRanks (Index : Type*) where
  rank : Index -> ℕ -> ℕ

/-- The `q`-th Morse type number `m_q = Σ_k rank C_q(M_k)` from Li Eq. (6.8). -/
def morseTypeNumber {Index : Type*} [Fintype Index] (C : CriticalGroupRanks Index) (q : ℕ) : ℕ :=
  ∑ i, C.rank i q

/-- A local version of Li's Theorem 6.5: if a neighborhood-pair computation is supplied, then the critical
group ranks can be read from that pair. -/
structure CriticalGroupNeighborhoodPair where
  criticalRank : ℕ -> ℕ
  neighborhoodPairRank : ℕ -> ℕ
  rank_eq_pair_rank : forall q : ℕ, criticalRank q = neighborhoodPairRank q

/-- **[Li, Theorem 6.5 rank form]** Critical groups may be computed from positively invariant
neighborhood pairs once the pair certificate is supplied. -/
theorem criticalRank_eq_neighborhoodPairRank (P : CriticalGroupNeighborhoodPair) (q : ℕ) :
    P.criticalRank q = P.neighborhoodPairRank q :=
  P.rank_eq_pair_rank q

/-- Alternating partial sum `a_q - a_{q-1} + ... + (-1)^q a_0`. -/
def alternatingPartial (a : ℕ -> ℤ) : ℕ -> ℤ
  | 0 => a 0
  | q + 1 => a (q + 1) - alternatingPartial a q

@[simp] theorem alternatingPartial_zero (a : ℕ -> ℤ) :
    alternatingPartial a 0 = a 0 :=
  rfl

@[simp] theorem alternatingPartial_succ (a : ℕ -> ℤ) (q : ℕ) :
    alternatingPartial a (q + 1) = a (q + 1) - alternatingPartial a q :=
  rfl

/-- Alternating partial sums distribute over subtraction. -/
theorem alternatingPartial_sub (a b : ℕ -> ℤ) (q : ℕ) :
    alternatingPartial (fun n => a n - b n) q = alternatingPartial a q - alternatingPartial b q := by
  induction q with
  | zero => simp
  | succ q ih =>
      simp [alternatingPartial_succ, ih]
      ring

/-- **[Morse equation algebra]** If `m_n - β_n` is the coefficient of `(1+t)Q(t)`, i.e.
`m₀-β₀ = r₀` and `m_{n+1}-β_{n+1}=r_{n+1}+r_n`, then the alternating excess through degree `q` is exactly
`r_q`. -/
theorem alternatingPartial_morseEquation (delta remainder : ℕ -> ℤ)
    (h0 : delta 0 = remainder 0)
    (hsucc : forall q : ℕ, delta (q + 1) = remainder (q + 1) + remainder q) :
    forall q : ℕ, alternatingPartial delta q = remainder q := by
  intro q
  induction q with
  | zero => simpa using h0
  | succ q ih =>
      rw [alternatingPartial_succ, hsucc q, ih]
      ring

/-- **[Li, Theorem 6.6 algebraic core]** The Morse equation with nonnegative remainder coefficients implies
the alternating Morse inequalities
`β_q - β_{q-1}+... ≤ m_q - m_{q-1}+...`. -/
theorem morseEquation_implies_alternatingInequality (m beta remainder : ℕ -> ℤ)
    (h0 : m 0 - beta 0 = remainder 0)
    (hsucc : forall q : ℕ,
      m (q + 1) - beta (q + 1) = remainder (q + 1) + remainder q)
    (hremainder : forall q : ℕ, 0 ≤ remainder q) :
    forall q : ℕ, alternatingPartial beta q ≤ alternatingPartial m q := by
  intro q
  have hdelta : alternatingPartial (fun n => m n - beta n) q = remainder q :=
    alternatingPartial_morseEquation (fun n => m n - beta n) remainder h0 hsucc q
  rw [alternatingPartial_sub] at hdelta
  have hnonneg : 0 ≤ alternatingPartial m q - alternatingPartial beta q := by
    linarith [hremainder q]
  linarith

/-- A discrete Picard-Lefschetz/Morse steepest-descent flow certificate.

`point 0` is the saddle point.  The two fields are the exact algebraic
consequences of downward Morse flow for `h = -S_I / hbar`: the real phase
`S_R` is constant along the thimble, and the imaginary action `S_I`
is nondecreasing away from the saddle. -/
structure PicardLefschetzMorseFlow (α : Type*) where
  /-- Real part of the complex action. -/
  actionRe : α → ℝ
  /-- Imaginary part of the complex action, controlling damping. -/
  actionIm : α → ℝ
  /-- A discrete parametrization of the thimble. -/
  point : ℕ → α
  /-- Steepest descent has constant real phase. -/
  phase_step : ∀ n : ℕ, actionRe (point (n + 1)) = actionRe (point n)
  /-- Moving away from the saddle cannot decrease the damping action. -/
  imaginary_step : ∀ n : ℕ, actionIm (point n) ≤ actionIm (point (n + 1))

/-! ## Witten §2.3: Stokes phenomena -/

/-- A critical point representative for the finite-dimensional Picard-Lefschetz shadow of
Witten's analytic continuation.  Section 2.3 only needs the value of the complex
exponent `I`: the Stokes condition compares its imaginary part. -/
structure StokesCriticalPoint where
  /-- The complex exponent `I` whose real part supplies the Morse height. -/
  exponent : ℂ

/-- A critical point with exponent `I`. -/
def stokesCriticalPoint (I : ℂ) : StokesCriticalPoint :=
  { exponent := I }

/-- Witten's Stokes condition from §2.3: the conserved quantity `Im I`
agrees for the two critical points.  A steepest-descent flow between critical
points can occur only on this locus. -/
def StokesAligned (p q : StokesCriticalPoint) : Prop :=
  p.exponent.im = q.exponent.im

/-- Stokes alignment is reflexive. -/
theorem stokesAligned_refl (p : StokesCriticalPoint) : StokesAligned p p := rfl

/-- Stokes alignment is symmetric. -/
theorem stokesAligned_symm {p q : StokesCriticalPoint}
    (h : StokesAligned p q) : StokesAligned q p :=
  h.symm

/-- A Stokes connection records the integer count/orientation of flow lines
between two aligned critical points. -/
structure StokesConnection where
  source : StokesCriticalPoint
  target : StokesCriticalPoint
  /-- Signed count of the connecting steepest-descent flow lines. -/
  multiplicity : ℤ
  /-- Witten §2.3's necessary condition for such a connection. -/
  aligned : StokesAligned source target

/-- The existence of a recorded Stokes connection gives equality of the conserved
quantity `Im I`. -/
theorem stokesConnection_imaginary_eq (S : StokesConnection) :
    S.source.exponent.im = S.target.exponent.im :=
  S.aligned

/-- Affine interpolation of complex exponents.  This is the finite-dimensional
normal form of a Stokes connecting trajectory: it joins the two critical
exponents and preserves the Stokes conserved quantity when their imaginary
parts agree. -/
noncomputable def affineStokesExponent (I₀ I₁ : ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * I₀ + (t : ℂ) * I₁

@[simp] theorem affineStokesExponent_zero (I₀ I₁ : ℂ) :
    affineStokesExponent I₀ I₁ 0 = I₀ := by
  simp [affineStokesExponent]

@[simp] theorem affineStokesExponent_one (I₀ I₁ : ℂ) :
    affineStokesExponent I₀ I₁ 1 = I₁ := by
  simp [affineStokesExponent]

@[simp] theorem affineStokesExponent_re (I₀ I₁ : ℂ) (t : ℝ) :
    (affineStokesExponent I₀ I₁ t).re = (1 - t) * I₀.re + t * I₁.re := by
  simp [affineStokesExponent]

theorem affineStokesExponent_im_of_aligned {I₀ I₁ : ℂ}
    (h : I₀.im = I₁.im) (t : ℝ) :
    (affineStokesExponent I₀ I₁ t).im = I₀.im := by
  simp [affineStokesExponent, h]
  ring

/-- The affine Stokes path between two critical points. -/
noncomputable def affineStokesPath (p q : StokesCriticalPoint) (t : ℝ) :
    StokesCriticalPoint :=
  stokesCriticalPoint (affineStokesExponent p.exponent q.exponent t)

/-- A Chern-Simons Stokes flow line realizing a recorded Stokes connection in
the analytic-continuation structure.  It records the endpoint equations and the
conserved quantity `Im I` from Witten §2.3. -/
structure ChernSimonsStokesFlowLine (S : StokesConnection) where
  /-- Parametrized flow line in the critical-exponent structure. -/
  path : ℝ → StokesCriticalPoint
  /-- The line starts at the source critical point. -/
  source_at_zero : path 0 = S.source
  /-- The line ends at the target critical point. -/
  target_at_one : path 1 = S.target
  /-- Witten's conserved Stokes quantity along the line. -/
  conserved_im : ∀ t, (path t).exponent.im = S.source.exponent.im

/-- A Stokes connection is height-ordered when its target is no higher than its
source for the Morse height `Re I`.  This is the finite underlying space of the
downward-gradient orientation. -/
def StokesConnection.HeightOrdered (S : StokesConnection) : Prop :=
  S.target.exponent.re ≤ S.source.exponent.re

/-- A downward Chern-Simons gradient-flow line: a Stokes flow line whose Morse
height is nonincreasing on the unit interval. -/
structure ChernSimonsGradientFlowLine (S : StokesConnection) extends
    ChernSimonsStokesFlowLine S where
  /-- On `0 ≤ s ≤ t ≤ 1`, the Morse height `Re I` does not increase. -/
  height_antitone_on_unit :
    ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ 1 →
      (path t).exponent.re ≤ (path s).exponent.re

/-- Every recorded Stokes connection has an explicit affine Stokes flow line
preserving Witten's conserved `Im I`. -/
noncomputable def affineChernSimonsStokesFlowLine
    (S : StokesConnection) : ChernSimonsStokesFlowLine S where
  path := affineStokesPath S.source S.target
  source_at_zero := by
    cases S.source
    simp [affineStokesPath, stokesCriticalPoint]
  target_at_one := by
    cases S.target
    simp [affineStokesPath, stokesCriticalPoint]
  conserved_im := by
    intro t
    exact affineStokesExponent_im_of_aligned S.aligned t

/-- Existence form: every Stokes connection recorded by the analytic
continuation layer has a Stokes flow line. -/
theorem chernSimonsStokesFlowLine_exists (S : StokesConnection) :
    Nonempty (ChernSimonsStokesFlowLine S) :=
  ⟨affineChernSimonsStokesFlowLine S⟩

/-- Along the affine Stokes path, height is antitone whenever the target
critical point is no higher than the source. -/
theorem affineStokesPath_re_antitone_of_heightOrdered
    (S : StokesConnection) (hheight : S.HeightOrdered) {s t : ℝ}
    (hst : s ≤ t) :
    (affineStokesPath S.source S.target t).exponent.re ≤
      (affineStokesPath S.source S.target s).exponent.re := by
  have hd : S.target.exponent.re - S.source.exponent.re ≤ 0 := sub_nonpos.mpr hheight
  have hmul : t * (S.target.exponent.re - S.source.exponent.re) ≤
      s * (S.target.exponent.re - S.source.exponent.re) :=
    mul_le_mul_of_nonpos_right hst hd
  simp only [affineStokesPath, stokesCriticalPoint, affineStokesExponent_re]
  nlinarith [hmul]

/-- Every height-ordered Stokes connection has a downward affine Chern-Simons
gradient-flow line. -/
noncomputable def affineChernSimonsGradientFlowLine
    (S : StokesConnection) (hheight : S.HeightOrdered) :
    ChernSimonsGradientFlowLine S where
  toChernSimonsStokesFlowLine := affineChernSimonsStokesFlowLine S
  height_antitone_on_unit := by
    intro s t _ hst _
    exact affineStokesPath_re_antitone_of_heightOrdered S hheight hst

/-- Existence form: the analytic hypotheses only need to supply the usual
height-ordering/orientation; then Lean constructs the corresponding downward
Chern-Simons gradient-flow line. -/
theorem chernSimonsGradientFlowLine_exists_of_heightOrdered
    (S : StokesConnection) (hheight : S.HeightOrdered) :
    Nonempty (ChernSimonsGradientFlowLine S) :=
  ⟨affineChernSimonsGradientFlowLine S hheight⟩

/-- A thimble cycle is the integer coefficient function in Witten's expansion
`C = Σ n_sigma J_sigma`. -/
abbrev ThimbleCycle (ι : Type u) :=
  ι → ℤ

/-- The coefficient jump in Witten §2.3: crossing a Stokes wall adds `m`
copies of the target thimble to the integer cycle expansion. -/
def stokesCoefficientJump {ι : Type u} [DecidableEq ι]
    (C : ThimbleCycle ι) (target : ι) (m : ℤ) : ThimbleCycle ι :=
  fun i => C i + if i = target then m else 0

/-- The target coefficient changes by exactly the Stokes multiplicity. -/
theorem stokesCoefficientJump_target {ι : Type u} [DecidableEq ι]
    (C : ThimbleCycle ι) (target : ι) (m : ℤ) :
    stokesCoefficientJump C target m target = C target + m := by
  simp [stokesCoefficientJump]

/-- Coefficients away from the crossed thimble are unchanged. -/
theorem stokesCoefficientJump_other {ι : Type u} [DecidableEq ι]
    (C : ThimbleCycle ι) {i target : ι} (m : ℤ) (hit : i ≠ target) :
    stokesCoefficientJump C target m i = C i := by
  simp [stokesCoefficientJump, hit]

/-- A zero-multiplicity Stokes crossing leaves the cycle coefficients unchanged. -/
theorem stokesCoefficientJump_zero {ι : Type u} [DecidableEq ι]
    (C : ThimbleCycle ι) (target : ι) :
    stokesCoefficientJump C target 0 = C := by
  funext i
  by_cases h : i = target <;> simp [stokesCoefficientJump, h]

/-- If the thimble `J_sigma` itself jumps by `m • J_tau`, the compensating
coefficient of `J_tau` is `n_tau - m*n_sigma`. -/
def stokesCompensatingCoefficient (n_sigma n_tau m : ℤ) : ℤ :=
  n_tau - m * n_sigma

/-- The scalar arithmetic behind local constancy of the homology class:
the added `m*n_sigma` copies of `J_tau` are exactly cancelled by the
compensating coefficient jump. -/
theorem stokesCompensatingCoefficient_cancels (n_sigma n_tau m : ℤ) :
    n_sigma * m + stokesCompensatingCoefficient n_sigma n_tau m = n_tau := by
  unfold stokesCompensatingCoefficient
  ring

/-- **Witten §2.3 local-constancy law.**  In a two-thimble crossing, if
`J_sigma` jumps to `J_sigma + m J_tau` and the coefficient of `J_tau` jumps
to `n_tau - m*n_sigma`, the target-thimble multiplicity is unchanged after
combining the basis jump and coefficient jump. -/
theorem twoCritical_stokesCompensation_keeps_targetMultiplicity
    (n_sigma n_tau m : ℤ) :
    n_sigma * m + stokesCompensatingCoefficient n_sigma n_tau m = n_tau :=
  stokesCompensatingCoefficient_cancels n_sigma n_tau m

/-- The exponent of the existing complex-action weight,
`I = i S_R / hbar - S_I / hbar`.  Its imaginary part is the conserved
oscillatory phase `S_R / hbar`. -/
noncomputable def complexActionStokesExponent (S_R S_I hbar : ℝ) : ℂ :=
  ((S_R / hbar : ℝ) : ℂ) * Complex.I - ((S_I / hbar : ℝ) : ℂ)

/-- The critical-point structure associated to a complex-action saddle. -/
noncomputable def complexActionCriticalPoint (S_R S_I hbar : ℝ) : StokesCriticalPoint :=
  stokesCriticalPoint (complexActionStokesExponent S_R S_I hbar)

@[simp] theorem complexActionStokesExponent_im (S_R S_I hbar : ℝ) :
    (complexActionStokesExponent S_R S_I hbar).im = S_R / hbar := by
  simp [complexActionStokesExponent]

/-- For the repo's complex-action kernel, Witten's Stokes condition `Im I_sigma =
Im I_tau` is exactly equality of real action phases. -/
theorem stokesAligned_complexAction_iff {hbar : ℝ} (hhbar : hbar ≠ 0)
    (S_R S_I T_R T_I : ℝ) :
    StokesAligned
        (complexActionCriticalPoint S_R S_I hbar)
        (complexActionCriticalPoint T_R T_I hbar)
      ↔ S_R = T_R := by
  unfold StokesAligned complexActionCriticalPoint stokesCriticalPoint
  simp only [complexActionStokesExponent_im]
  constructor
  · intro h
    have hmul := congrArg (fun x : ℝ => x * hbar) h
    field_simp [hhbar] at hmul
    exact hmul
  · intro h
    rw [h]

namespace PicardLefschetzMorseFlow

variable {α : Type*} (F : PicardLefschetzMorseFlow α)

/-- The saddle selected by the Morse/Picard-Lefschetz flow. -/
def saddle : α := F.point 0

/-- The Morse height for the oscillatory integral:
`h = Re(iS) = -S_I`, omitting the positive scale `hbar`. -/
def morseHeight (x : α) : ℝ := -F.actionIm x

/-- The complex-action path-integral weight at the `n`-th point of the thimble. -/
noncomputable def weightAt (hbar : ℝ) (n : ℕ) : ℂ :=
  complexActionPathIntegralWeight (F.actionRe (F.point n)) (F.actionIm (F.point n)) hbar

/-- Extra imaginary action accumulated from the saddle to the `n`-th point. -/
def excessImaginaryAction (n : ℕ) : ℝ :=
  F.actionIm (F.point n) - F.actionIm F.saddle

/-- The real phase is constant along a Picard-Lefschetz thimble. -/
theorem actionRe_eq_saddle (n : ℕ) :
    F.actionRe (F.point n) = F.actionRe F.saddle := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        F.actionRe (F.point (Nat.succ n)) = F.actionRe (F.point n) := F.phase_step n
        _ = F.actionRe F.saddle := ih

/-- The imaginary action is bounded below by its saddle value along the thimble. -/
theorem saddle_le_actionIm (n : ℕ) :
    F.actionIm F.saddle ≤ F.actionIm (F.point n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact le_trans ih (F.imaginary_step n)

/-- The Morse height `-S_I` decreases along each discrete steepest-descent step. -/
theorem morseHeight_step_antitone (n : ℕ) :
    F.morseHeight (F.point (n + 1)) ≤ F.morseHeight (F.point n) := by
  unfold morseHeight
  linarith [F.imaginary_step n]

/-- The Morse height is never above the saddle height along the thimble. -/
theorem morseHeight_le_saddle (n : ℕ) :
    F.morseHeight (F.point n) ≤ F.morseHeight F.saddle := by
  unfold morseHeight
  linarith [F.saddle_le_actionIm n]

/-- The excess imaginary action is nonnegative on a steepest-descent thimble. -/
theorem excessImaginaryAction_nonneg (n : ℕ) :
    0 ≤ F.excessImaginaryAction n := by
  unfold excessImaginaryAction
  linarith [F.saddle_le_actionIm n]

/-- The thimble weight is the existing Lorentzian complex-action kernel. -/
theorem weightAt_eq_lorentzianKernel (hbar : ℝ) (n : ℕ) :
    F.weightAt hbar n =
      lorentzianKernel (F.actionRe (F.point n)) (F.actionIm (F.point n)) hbar :=
  complexActionPathIntegralWeight_eq_lorentzianKernel
    (F.actionRe (F.point n)) (F.actionIm (F.point n)) hbar

/-- The thimble weight is also the Nagao--Nielsen complex-action weight
`exp((i/hbar)(S_R + i S_I))`. -/
theorem weightAt_eq_nagaoNielsen {hbar : ℝ} (hhbar : hbar ≠ 0) (n : ℕ) :
    F.weightAt hbar n =
      nagaoNielsenComplexActionWeight
        (F.actionRe (F.point n)) (F.actionIm (F.point n)) hbar := by
  unfold weightAt
  exact (nagaoNielsen_eq_master
    (F.actionRe (F.point n)) (F.actionIm (F.point n)) hbar hhbar).symm

/-- The norm of the thimble weight is the existing entropy-production damping. -/
theorem weightAt_norm (hbar : ℝ) (n : ℕ) :
    ‖F.weightAt hbar n‖ = Real.exp (-(F.actionIm (F.point n) / hbar)) := by
  unfold weightAt
  rw [master_modulus_is_kuiken]
  rfl

/-- **Steepest-descent bound.**  Along a Picard-Lefschetz/Morse thimble,
the Nagao--Nielsen/Feynman path-integral weight is bounded by its saddle
weight. -/
theorem weightAt_norm_le_saddle {hbar : ℝ} (hhbar : 0 < hbar) (n : ℕ) :
    ‖F.weightAt hbar n‖ ≤ ‖F.weightAt hbar 0‖ := by
  rw [F.weightAt_norm hbar n, F.weightAt_norm hbar 0]
  apply Real.exp_le_exp.mpr
  have hdiv :
      F.actionIm F.saddle / hbar ≤ F.actionIm (F.point n) / hbar :=
    div_le_div_of_nonneg_right (F.saddle_le_actionIm n) hhbar.le
  unfold saddle at hdiv
  linarith

/-- The excess damping along a thimble is exactly a constant-potential
Feynman--Kac weight. -/
theorem excess_damping_eq_feynmanKac (hbar : ℝ) (n : ℕ) :
    Real.exp (-(F.excessImaginaryAction n / hbar)) =
      feynman_kac_weight (fun _ : Unit => F.excessImaginaryAction n / hbar) 1 () := by
  unfold feynman_kac_weight
  ring_nf

/-- The Feynman--Kac excess damping is bounded by `1` because the Morse flow
only increases `S_I` away from the saddle. -/
theorem excess_feynmanKac_le_one {hbar : ℝ} (hhbar : 0 < hbar) (n : ℕ) :
    feynman_kac_weight (fun _ : Unit => F.excessImaginaryAction n / hbar) 1 () ≤ 1 := by
  rw [← F.excess_damping_eq_feynmanKac hbar n, Real.exp_le_one_iff]
  have hnonneg : 0 ≤ F.excessImaginaryAction n / hbar :=
    div_nonneg (F.excessImaginaryAction_nonneg n) hhbar.le
  linarith

/-- **Factorization through Feynman--Kac.**  The weight at any point of a
Picard-Lefschetz thimble is the saddle weight multiplied by the FK damping
of the excess imaginary action. -/
theorem weightAt_norm_factorizes_through_feynmanKac
    {hbar : ℝ} (hhbar : hbar ≠ 0) (n : ℕ) :
    ‖F.weightAt hbar n‖ =
      ‖F.weightAt hbar 0‖ *
        feynman_kac_weight (fun _ : Unit => F.excessImaginaryAction n / hbar) 1 () := by
  rw [F.weightAt_norm hbar n, F.weightAt_norm hbar 0]
  unfold feynman_kac_weight excessImaginaryAction saddle
  rw [← Real.exp_add]
  congr 1
  field_simp [hhbar]
  ring

/-- Compact checked statement: a Morse/Picard-Lefschetz flow certificate gives
a valid steepest-descent contour for the existing Nagao--Nielsen/Feynman kernel. -/
theorem checked_steepestDescent_summary {hbar : ℝ} (hhbar : 0 < hbar) (n : ℕ) :
    F.actionRe (F.point n) = F.actionRe F.saddle
      ∧ F.actionIm F.saddle ≤ F.actionIm (F.point n)
      ∧ ‖F.weightAt hbar n‖ ≤ ‖F.weightAt hbar 0‖
      ∧ ‖F.weightAt hbar n‖ =
        ‖F.weightAt hbar 0‖ *
          feynman_kac_weight (fun _ : Unit => F.excessImaginaryAction n / hbar) 1 () :=
  ⟨F.actionRe_eq_saddle n,
    F.saddle_le_actionIm n,
    F.weightAt_norm_le_saddle hhbar n,
    F.weightAt_norm_factorizes_through_feynmanKac hhbar.ne' n⟩

/-- Points on the same Picard-Lefschetz thimble are Stokes-aligned for the
complex-action exponent: the conserved `Im I` is exactly the constant real
action phase already proved by `actionRe_eq_saddle`. -/
theorem stokesAligned_points_on_same_thimble {hbar : ℝ} (hhbar : hbar ≠ 0)
    (m n : ℕ) :
    StokesAligned
        (complexActionCriticalPoint
          (F.actionRe (F.point m)) (F.actionIm (F.point m)) hbar)
        (complexActionCriticalPoint
          (F.actionRe (F.point n)) (F.actionIm (F.point n)) hbar) := by
  rw [stokesAligned_complexAction_iff hhbar]
  rw [F.actionRe_eq_saddle m, F.actionRe_eq_saddle n]

end PicardLefschetzMorseFlow

/-! ## Li Morse-Lyapunov reading of Picard-Lefschetz descent -/

/-- Picard-Lefschetz steepest descent supplies the Morse-Lyapunov monotonicity used for contour deformation:
the Morse height decreases along each thimble step. -/
theorem picardLefschetz_morseHeight_step_is_lyapunov
    {α : Type*} (F : PicardLefschetzMorseFlow α) (n : ℕ) :
    F.morseHeight (F.point (n + 1)) ≤ F.morseHeight (F.point n) :=
  F.morseHeight_step_antitone n

/-! ## Concrete quadratic Morse saddle -/

/-- The local quadratic Morse model for the imaginary action near a nondegenerate
saddle: `S_I(x) = κ x²`. -/
def quadraticMorseImaginaryAction (κ x : ℝ) : ℝ :=
  κ * x ^ 2

/-- The quadratic Morse imaginary action is nonnegative when `κ ≥ 0`. -/
theorem quadraticMorseImaginaryAction_nonneg {κ x : ℝ} (hκ : 0 ≤ κ) :
    0 ≤ quadraticMorseImaginaryAction κ x := by
  unfold quadraticMorseImaginaryAction
  exact mul_nonneg hκ (sq_nonneg x)

/-- In the quadratic Morse model, the saddle value is `S_I(0)=0`. -/
@[simp] theorem quadraticMorseImaginaryAction_zero (κ : ℝ) :
    quadraticMorseImaginaryAction κ 0 = 0 := by
  simp [quadraticMorseImaginaryAction]

/-- **Quadratic steepest-descent bound.**  The local Morse normal form
`S_I = κx²` gives a concrete Picard-Lefschetz damping contour: every point
has weight bounded by the saddle weight. -/
theorem quadratic_morse_weight_norm_le_saddle
    {κ hbar : ℝ} (hκ : 0 ≤ κ) (hhbar : 0 < hbar) (S_R x : ℝ) :
    ‖complexActionPathIntegralWeight S_R (quadraticMorseImaginaryAction κ x) hbar‖
      ≤ ‖complexActionPathIntegralWeight S_R 0 hbar‖ := by
  rw [master_modulus_is_kuiken, master_modulus_is_kuiken]
  unfold kuikenWeight
  apply Real.exp_le_exp.mpr
  have hdiv : 0 ≤ quadraticMorseImaginaryAction κ x / hbar :=
    div_nonneg (quadraticMorseImaginaryAction_nonneg hκ) hhbar.le
  simpa using (neg_nonpos.mpr hdiv)

/-- The same quadratic Morse damping is exactly a Feynman--Kac factor
relative to the saddle. -/
theorem quadratic_morse_weight_norm_factorizes_feynmanKac
    {κ hbar : ℝ} (hhbar : hbar ≠ 0) (S_R x : ℝ) :
    ‖complexActionPathIntegralWeight S_R (quadraticMorseImaginaryAction κ x) hbar‖
      = ‖complexActionPathIntegralWeight S_R 0 hbar‖ *
        feynman_kac_weight
          (fun _ : Unit => quadraticMorseImaginaryAction κ x / hbar) 1 () := by
  rw [master_modulus_is_kuiken, master_modulus_is_kuiken]
  unfold kuikenWeight feynman_kac_weight
  rw [← Real.exp_add]
  congr 1
  field_simp [hhbar]
  ring

/-! ## Links to the existing contour, lapse, and saddle-point structures -/

/-- The quadratic Morse normal form is the same Gaussian class whose permitted-ray
contour integral is independent of the contour angle in `ComplexDelta.ContourGaussian`.
This is the analytic contour-independence representative for the local Picard-Lefschetz
normal form. -/
theorem gaussianContourIntegral_indep_from_quadratic_morse
    {c θ₀ θ₁ : ℝ} (hc : 0 < c)
    (h0 : |θ₀| < Real.pi / 4) (h1 : |θ₁| < Real.pi / 4) :
    ∫ s : ℝ, ComplexDelta.ContourShift.contourIntegrand
        (ComplexDelta.ContourGaussian.gaussH c) θ₀ s
      = ∫ s : ℝ, ComplexDelta.ContourShift.contourIntegrand
        (ComplexDelta.ContourGaussian.gaussH c) θ₁ s :=
  ComplexDelta.ContourGaussian.gaussianContourIntegral_indep hc h0 h1

/-- The gravitational lapse contour's damping is a concrete Picard-Lefschetz
steepest-descent bound: switching on a nonnegative imaginary lapse action can only
decrease the modulus relative to the real lapse contour. -/
theorem lapseWeight_picardLefschetz_bound
    {ε Ham : ℝ} (hεH : 0 ≤ ε * Ham) (N : ℝ) :
    ‖GravLapse.ContourMaster.lapseWeight N ε Ham‖
      ≤ ‖GravLapse.ContourMaster.lapseWeight N 0 Ham‖ := by
  rw [GravLapse.ContourMaster.lapseWeight_modulus,
    GravLapse.ContourMaster.lapseWeight_modulus]
  unfold kuikenWeight
  apply Real.exp_le_exp.mpr
  simpa using (neg_nonpos.mpr hεH)

/-- Off the real lapse axis, the Banihashemi-Jacobson lapse contour is strictly
Picard-Lefschetz damped when the regulator and Hamiltonian constraint are positive. -/
theorem lapseContour_offAxis_is_picardLefschetz_damping
    (N ε Ham : ℝ) (hε : 0 < ε) (hH : 0 < Ham) :
    ‖GravLapse.ContourMaster.lapseWeight N ε Ham‖ < 1 :=
  GravLapse.ContourEntropicTime.lapse_irreversible_off_axis N ε Ham hε hH

/-- The Nagao-Nielsen momentum Gaussian convergence criterion is the same
Picard-Lefschetz condition: the Gaussian coefficient has positive real part exactly
when the imaginary mass gives Feynman-Kac damping. -/
theorem momentumGaussianCoeff_positive_iff_picardLefschetz_damping
    (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    0 < (PathIntegral.MomentumPathIntegral.momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  PathIntegral.MomentumPathIntegral.momentum_integral_converges_iff m hℏ hdt hm

/-- The momentum saddle used before the lapse integral is the saddle selected by
the Picard-Lefschetz/Morse contour layer: at `p = m qdot`, phase space collapses
to the configuration-space action. -/
theorem momentum_saddle_selected_by_picardLefschetz
    (m qdot V : ℂ) (hm : m ≠ 0) :
    PathIntegral.MomentumPathIntegral.phaseLagrangian m (m * qdot) qdot V
      = PathIntegral.MomentumPathIntegral.configLagrangian m qdot V :=
  PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle m qdot V hm

/-- The reversible/no-information sector of the QFT bridge is the zero-height
Picard-Lefschetz sector: when the eigenvalue has no imaginary part, both the Green
kernel and Lorentzian path-integral kernel are unimodular. -/
theorem greenKernel_unitary_is_zeroHeight_picardLefschetz_sector
    {ℏ t : ℝ} (hℏ : ℏ ≠ 0) (ht : t ≠ 0) {lam : ℂ} (hI : lam.im = 0) (S_R : ℝ) :
    ‖PeriodicQHermitian.Basic.greenKernel lam ℏ t‖ = 1
      ∧ ‖lorentzianKernel S_R 0 ℏ‖ = 1 :=
  PathIntegral.QFTPathIntegralComplexAction.greenKernel_unitary_eq_lorentzian_no_information
    hℏ ht hI S_R

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour

end

end

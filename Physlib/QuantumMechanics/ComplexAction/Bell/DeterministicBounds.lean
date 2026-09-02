/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH

/-!
# CHSH: the local-hidden-variable bound and the Tsirelson correlation bound

Ports the self-contained CHSH formalizations from the reference tree repo
(`BellCHSHBohmCoreAbstractions`, `NoFTLBellBridge §4–5`) into physlib, giving the **correlation-level**
CHSH bounds that complement the operator-algebra CHSH of `AlgebraicQFT.SummersVacuumBellCHSH` (Summers §4) and fill
the Tsirelson gap left open in `Physlib.QuantumMechanics.Bell.HyperbolicRegime`.

Two faces of the CHSH inequality `S = ⟨ab⟩ + ⟨ab'⟩ + ⟨a'b⟩ − ⟨a'b'⟩`:

* **Local hidden variables / classical** (deterministic `±1` outcomes): `|S| ≤ 2`
  (`classicalCHSH_bound`, `chsh_lhv_bound`) — Bell's theorem, proved by exhausting the `2⁴` sign
  assignments; the bound is **tight** (`classicalCHSH_tight`).
* **Quantum / Tsirelson** (correlations in `[−1,1]`): `S² ≤ 8`, hence `|S| ≤ 2√2`
  (`tsirelson_sq_bound`, `tsirelson_correlation_bound`) — proved by **Cauchy–Schwarz**:
  `S = a(b+b') + a'(b−b')`, so `S² ≤ (a²+a'²)·((b+b')²+(b−b')²) = (a²+a'²)·2(b²+b'²) ≤ 2·2·2 = 8`.

Since `2 < 2√2` (`classical_lt_tsirelson`), the quantum bound strictly exceeds the classical one — Bell
violation. This `[−1,1]`-correlation Cauchy–Schwarz proof of Tsirelson's `|S| ≤ 2√2` is exactly the one
`Bell.HyperbolicRegime` declared out of scope; it is the elementary face of the operator-algebra
`AlgebraicQFT.SummersVacuumBellCHSH.chsh_tsirelson_bound`.

* **§A — the local-hidden-variable bound** (`CHSHAssignment`, `classicalCHSHValue`,
  `classicalCHSH_bound`, `chsh_lhv_bound`, `classicalCHSH_tight`).
* **§B — the Tsirelson correlation bound** (`tsirelson_sq_bound`, `tsirelson_correlation_bound`).
* **§C — the violation gap** (`tsirelsonWitness`, `classical_lt_tsirelson`, `chsh_correlation_gap`).

## References

* J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt, Phys. Rev. Lett. 23 (1969) 880; B. Tsirelson,
  Lett. Math. Phys. 4 (1980) 93. Ported from reference tree `BellCHSHBohmCoreAbstractions` /
  `NoFTLBellBridge`. Operator-algebra companion: `AlgebraicQFT.SummersVacuumBellCHSH`; regime carrier:
  `Physlib.QuantumMechanics.Bell.HyperbolicRegime`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds

open scoped BigOperators


/-- **A deterministic CHSH assignment** — four dichotomic `±1` hidden-variable outcomes `a, a', b, b'`
(the local-hidden-variable model of a CHSH experiment). -/
structure CHSHAssignment where
  /-- outcome of measurement `a` -/
  a : ℤ
  /-- outcome of measurement `a'` -/
  aPrime : ℤ
  /-- outcome of measurement `b` -/
  b : ℤ
  /-- outcome of measurement `b'` -/
  bPrime : ℤ
  /-- `a = ±1` -/
  ha : a = 1 ∨ a = -1
  /-- `a' = ±1` -/
  haPrime : aPrime = 1 ∨ aPrime = -1
  /-- `b = ±1` -/
  hb : b = 1 ∨ b = -1
  /-- `b' = ±1` -/
  hbPrime : bPrime = 1 ∨ bPrime = -1

/-- **The classical CHSH polynomial** `S = ab + ab' + a'b − a'b'` of a deterministic assignment. -/
def classicalCHSHValue (x : CHSHAssignment) : ℤ :=
  x.a * x.b + x.a * x.bPrime + x.aPrime * x.b - x.aPrime * x.bPrime

/-- **[Local hidden variables — raw form] `|S| ≤ 2`.** For dichotomic `±1` outcomes, the CHSH
combination `ab + ab' + a'b − a'b'` is bounded by `2` — Bell's theorem (the local/classical bound),
proved by exhausting all `2⁴` sign assignments. -/
lemma chsh_lhv_bound (a a' b b' : ℤ)
    (ha : a = 1 ∨ a = -1) (ha' : a' = 1 ∨ a' = -1)
    (hb : b = 1 ∨ b = -1) (hb' : b' = 1 ∨ b' = -1) :
    |a * b + a * b' + a' * b - a' * b'| ≤ 2 := by
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;>
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;> norm_num

/-- **[Local hidden variables] `|S| ≤ 2`** for a `CHSHAssignment`. -/
lemma classicalCHSH_bound (x : CHSHAssignment) : |classicalCHSHValue x| ≤ 2 :=
  chsh_lhv_bound x.a x.aPrime x.b x.bPrime x.ha x.haPrime x.hb x.hbPrime

/-- **[The classical bound is tight] `|S| = 2` is achieved** (e.g. `a=a'=b=1, b'=−1`). -/
lemma classicalCHSH_tight :
    ∃ a a' b b' : ℤ, (a = 1 ∨ a = -1) ∧ (a' = 1 ∨ a' = -1) ∧
      (b = 1 ∨ b = -1) ∧ (b' = 1 ∨ b' = -1) ∧
      |a * b + a * b' + a' * b - a' * b'| = 2 :=
  ⟨1, 1, 1, -1, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inr rfl, by norm_num⟩


/-- The predicted CHSH value of a **probabilistic** local hidden-variable model: a finite family of
deterministic assignments `x l` weighted by a distribution `ρ`, `⟨S⟩ = ∑_l ρ l · S(x l)`. -/
def lhvMixtureValue {ι : Type*} (s : Finset ι) (ρ : ι → ℝ) (x : ι → CHSHAssignment) : ℝ :=
  ∑ l ∈ s, ρ l * (classicalCHSHValue (x l) : ℝ)

/-- **[Bell's inequality, averaged form] `|⟨S⟩| ≤ 2`.** The empirically-testable bound: *any* probabilistic
local hidden-variable model — a distribution `ρ` (`ρ ≥ 0`, `∑ ρ = 1`) over deterministic `±1` assignments —
has averaged CHSH value bounded by `2`, by convexity over the per-assignment bound `classicalCHSH_bound`
(`|∑ ρ S| ≤ ∑ ρ |S| ≤ ∑ ρ · 2 = 2`). Real Bell experiments measure this average, not a single assignment; a
model whose worlds interact nonlocally in configuration space (Bohm / Many-Interacting-Worlds) is not of this
factorized local form and may exceed it — the content behind `classical_lt_tsirelson`. -/
lemma lhvMixture_bound {ι : Type*} (s : Finset ι) (ρ : ι → ℝ) (x : ι → CHSHAssignment)
    (hρ : ∀ l ∈ s, 0 ≤ ρ l) (hsum : ∑ l ∈ s, ρ l = 1) :
    |lhvMixtureValue s ρ x| ≤ 2 := by
  unfold lhvMixtureValue
  calc |∑ l ∈ s, ρ l * (classicalCHSHValue (x l) : ℝ)|
      ≤ ∑ l ∈ s, |ρ l * (classicalCHSHValue (x l) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ s, ρ l * 2 := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        rw [abs_mul, abs_of_nonneg (hρ l hl)]
        refine mul_le_mul_of_nonneg_left ?_ (hρ l hl)
        have hb := classicalCHSH_bound (x l)
        exact_mod_cast hb
    _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]


/-- **[Tsirelson, squared form] `S² ≤ 8`** for correlations `a, a', b, b' ∈ [−1,1]`. Writing
`S = a(b+b') + a'(b−b')`, Cauchy–Schwarz gives `S² ≤ (a²+a'²)·((b+b')²+(b−b')²) = (a²+a'²)·2(b²+b'²)
≤ 2·2·2 = 8` — the quantum-correlation Tsirelson bound. -/
lemma tsirelson_sq_bound (a a' b b' : ℝ)
    (ha : |a| ≤ 1) (ha' : |a'| ≤ 1) (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) :
    (a * b + a * b' + a' * b - a' * b') ^ 2 ≤ 8 := by
  have hC : a * b + a * b' + a' * b - a' * b' = a * (b + b') + a' * (b - b') := by ring
  have hCS : (a * (b + b') + a' * (b - b')) ^ 2
      ≤ (a ^ 2 + a' ^ 2) * ((b + b') ^ 2 + (b - b') ^ 2) := by
    nlinarith [sq_nonneg (a * (b - b') - a' * (b + b'))]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [abs_nonneg a, sq_abs a]
  have ha'2 : a' ^ 2 ≤ 1 := by nlinarith [abs_nonneg a', sq_abs a']
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [abs_nonneg b, sq_abs b]
  have hb'2 : b' ^ 2 ≤ 1 := by nlinarith [abs_nonneg b', sq_abs b']
  rw [hC]; nlinarith [hCS]

/-- **[Tsirelson bound] `|S| ≤ 2√2`** for correlations in `[−1,1]` — from `S² ≤ 8` and `√8 = 2√2`. This
is the elementary (`[−1,1]`-correlation) face of the operator-algebra Tsirelson bound
`AlgebraicQFT.SummersVacuumBellCHSH.chsh_tsirelson_bound`, and the bound `Bell.HyperbolicRegime` left out of scope. -/
lemma tsirelson_correlation_bound (a a' b b' : ℝ)
    (ha : |a| ≤ 1) (ha' : |a'| ≤ 1) (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) :
    |a * b + a * b' + a' * b - a' * b'| ≤ 2 * Real.sqrt 2 := by
  have h8 := tsirelson_sq_bound a a' b b' ha ha' hb hb'
  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← hsqrt8, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h8


/-- **The Tsirelson witness** `2√2` — the quantum maximum of the CHSH correlation. -/
noncomputable def tsirelsonWitness : ℝ := 2 * Real.sqrt 2

/-- **[Quantum exceeds classical] `2 < 2√2`.** The Tsirelson witness strictly exceeds the classical
CHSH bound `2`, so Bell's inequality can be violated. -/
lemma classical_lt_tsirelson : (2 : ℝ) < tsirelsonWitness := by
  unfold tsirelsonWitness
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [h, hpos]

/-- **[Tsirelson value, squared] `(2√2)² = 8`** — the squared CHSH witness (reference tree
`proved_tsirelson_value`). -/
lemma tsirelsonWitness_sq : tsirelsonWitness ^ 2 = 8 := by
  unfold tsirelsonWitness
  rw [mul_pow]; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- **[Bell violation, squared form] `(2√2)² > 4`** — the quantum CHSH value squared exceeds the
classical `2² = 4` (reference tree `proved_bell_violation`). -/
lemma tsirelsonWitness_sq_gt_four : tsirelsonWitness ^ 2 > 4 := by
  rw [tsirelsonWitness_sq]; norm_num

/-- **[CHSH violation gap] classical `≤ 2 < 2√2 ≥` quantum.** The local-hidden-variable bound `2`
(`classicalCHSH_bound`) is strictly below the Tsirelson correlation maximum `2√2`
(`classical_lt_tsirelson`); any correlation exceeding `2` is non-classical (Bell-violating /
entangled), saturating at `2√2`. -/
lemma chsh_correlation_gap (x : CHSHAssignment) :
    |classicalCHSHValue x| ≤ 2 ∧ (2 : ℝ) < tsirelsonWitness :=
  ⟨classicalCHSH_bound x, classical_lt_tsirelson⟩

end Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PerturbationTheory.WickAlgebra.TimeOrder
public import Physlib.QFT.PerturbationTheory.WickAlgebra.WicksTheorem
public import Physlib.SpaceAndTime.EntropicProperTime
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Self-consistency of entropic time with Wick's-theorem infrastructure

Physlib's Wick's theorem lives in the `ℂ`-algebra `WickAlgebra 𝓕`, with the
`ℂ`-linear time-ordering map `timeOrder`. The complex action supplies a
**scalar in that very ring**:

 `w(S_R, S_I, ℏ) := exp(i S_R/ℏ − S_I/ℏ) ∈ ℂ`.

The bridge to entropic time is the **modulus**:

 `‖w‖ = exp(−S_I/ℏ)`,

so the entropic time `τ_ent = S_I/ℏ` is exactly `−log‖w‖`. With `S_I = ℏ·D(ρ‖σ)`
this is `exp(−D(ρ‖σ))`, equal to `1` on the diagonal `ρ = σ`.

The complex action weight `w` is a scalar of the algebra over which
Wick's theorem is stated. Because `timeOrder` is `ℂ`-linear and `w`
is a never-zero complex exponential, three identities follow
mechanically from physlib's existing `wicks_theorem`:

* **Module/scalar level** (§C): the complex action weight commutes through
 time-ordering, `timeOrder (w • A) = w • timeOrder A`, because `timeOrder` is
 `ℂ`-linear.
* **Combinatorial level** (§D): the entropic weight **distributes over the Wick
 expansion**, `w • 𝓣(ofFieldOpList φs) = ∑_{φsΛ} w • φsΛ.wickTerm`, so the
 entropic damping `exp(−D(ρ‖σ))` factors uniformly across every contraction
 term.
* **Subsumption / recovery** (§D, `entropic_weight_recovers_wicks_theorem`): because the
 entropic weight is a complex exponential it is **never zero**; dividing it out
 of the entropic identity returns the standard Wick expansion
 `𝓣(ofFieldOpList φs) = ∑_{φsΛ} φsΛ.wickTerm` *as a theorem of the entropic
 calculus*. Wick's theorem is thus the `w = 1` (zero-relative-entropy) fiber of
 the entropic contraction calculus: the entropic-time framework **embeds and
 recovers it as the entropy-free member** of a strictly more general weighted
 expansion, using HepLean's `wicks_theorem` as input. It does *not* derive the
 combinatorial contraction enumeration.

scope note: the combinatorial *enumeration* of contractions is HepLean's
`wicks_theorem`, used here as input; this layer does not re-derive that enumeration
from scratch. What is contributed here is the embedding of Wick's theorem into
the entropic-weighted family and the identification of standard Wick combinatorics
as its entropy-free fiber.

## References

- **Mazur & Ulam 1932** — *Sur les transformations isométriques d'espaces vectoriels normés* [bib: `MazurUlam1932`]
- **Wick 1954** — *Properties of Bethe-Salpeter Wave Functions* [bib key needed: `Wick1954`]
-/

@[expose] public section

noncomputable section


namespace Physlib.QFT.Wick.Consistency

open QuantumInfo.Finite FieldSpecification

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## A. The complex action weight and its entropic modulus -/

/-- The complex action weight `exp(iS/ℏ) = exp((S_R/ℏ)·i − S_I/ℏ) ∈ ℂ` — a scalar
in the ring over which `WickAlgebra` is a module. -/
def complexActionWeight (S_R S_I hbar : ℝ) : ℂ :=
  Complex.exp (((S_R / hbar : ℝ) : ℂ) * Complex.I - ((S_I / hbar : ℝ) : ℂ))

/-- **The modulus of the complex action weight is the entropic damping**:
`‖w‖ = exp(−S_I/ℏ)`. Equivalently, the entropic time `S_I/ℏ = −log‖w‖`. -/
theorem norm_complexActionWeight (S_R S_I hbar : ℝ) :
    ‖complexActionWeight S_R S_I hbar‖ = Real.exp (-(S_I / hbar)) := by
  unfold complexActionWeight
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

/-- At zero imaginary action the weight is a **pure phase** (modulus `1`). -/
theorem norm_complexActionWeight_zero_imag (S_R hbar : ℝ) :
    ‖complexActionWeight S_R 0 hbar‖ = 1 := by
  rw [norm_complexActionWeight]; simp

/-- The complex action weight is **never zero** — it is a complex exponential. -/
theorem complexActionWeight_ne_zero (S_R S_I hbar : ℝ) :
    complexActionWeight S_R S_I hbar ≠ 0 :=
  Complex.exp_ne_zero _

/-- Restatement: the entropic damping `exp(−S_I/ℏ)` is the modulus of the
complex action weight. -/
theorem entropyDamping_eq_norm_complexActionWeight (S_R S_I hbar : ℝ) :
    Real.exp (-(S_I / hbar)) = ‖complexActionWeight S_R S_I hbar‖ :=
  (norm_complexActionWeight S_R S_I hbar).symm

/-! ## B. Link to entropic proper time -/

/-- The **entropic complex weight** of a state pair: the complex action weight
whose imaginary action is `ℏ · D(ρ‖σ)` (so its entropic time is the relative
entropy gap). -/
def entropicComplexWeight (S_R hbar : ℝ) (ρ σ : MState d) : ℂ :=
  complexActionWeight S_R (hbar * (entropicProperTime ρ σ).toReal) hbar

/-- The entropic complex weight is **never zero**. -/
theorem entropicComplexWeight_ne_zero (S_R hbar : ℝ) (ρ σ : MState d) :
    entropicComplexWeight S_R hbar ρ σ ≠ 0 :=
  complexActionWeight_ne_zero _ _ _

/-- Its modulus is `exp(−D(ρ‖σ))` — the entropic time enters as the damping. -/
theorem norm_entropicComplexWeight
    (S_R hbar : ℝ) (hbar0 : hbar ≠ 0) (ρ σ : MState d) :
    ‖entropicComplexWeight S_R hbar ρ σ‖ =
      Real.exp (-(entropicProperTime ρ σ).toReal) := by
  unfold entropicComplexWeight
  rw [norm_complexActionWeight, mul_div_cancel_left₀ _ hbar0]

/-- **Frozen diagonal**: on `ρ = σ` the entropic complex weight is a pure phase
(modulus `1`) — no damping, unitary sector. -/
theorem norm_entropicComplexWeight_self
    (S_R hbar : ℝ) (hbar0 : hbar ≠ 0) (ρ : MState d) :
    ‖entropicComplexWeight S_R hbar ρ ρ‖ = 1 := by
  rw [norm_entropicComplexWeight S_R hbar hbar0 ρ ρ, entropicProperTime_self]
  simp

/-! ## C. Self-consistency with Wick's theorem -/

/-- **Wick-theorem self-consistency**: the complex action weight — which records
the entropic damping in its modulus — commutes through Wick's-theorem
time-ordering, since `timeOrder` is `ℂ`-linear. The entropic (modulus) sector
factors out of the Wick combinatorics and leaves the time-ordered expansion
structurally unchanged. -/
theorem timeOrder_complexActionWeight_smul
    {𝓕 : FieldSpecification} (S_R S_I hbar : ℝ) (A : 𝓕.WickAlgebra) :
    WickAlgebra.timeOrder (complexActionWeight S_R S_I hbar • A) =
      complexActionWeight S_R S_I hbar • WickAlgebra.timeOrder A :=
  map_smul WickAlgebra.timeOrder (complexActionWeight S_R S_I hbar) A

/-- The entropic complex weight likewise commutes through Wick time-ordering. -/
theorem timeOrder_entropicComplexWeight_smul
    {𝓕 : FieldSpecification} (S_R hbar : ℝ) (ρ σ : MState d) (A : 𝓕.WickAlgebra) :
    WickAlgebra.timeOrder (entropicComplexWeight S_R hbar ρ σ • A) =
      entropicComplexWeight S_R hbar ρ σ • WickAlgebra.timeOrder A :=
  map_smul WickAlgebra.timeOrder (entropicComplexWeight S_R hbar ρ σ) A

/-! ## D. Distribution over the combinatorial Wick expansion

The statements above commute the weight past the *operator* `timeOrder`. Here we
go one step further and push the weight through the **combinatorial expansion**
delivered by HepLean's `wicks_theorem`: the time-ordered product of field
operators is a sum over Wick contractions, and the entropic weight distributes
across that sum termwise. This is the precise sense in which the entropic sector
is compatible with — and does not perturb — the Wick combinatorics. -/

/-- **Entropic-weighted Wick's theorem (scalar form).** Multiplying the
time-ordered product of field operators by the complex action weight `w`
distributes over the Wick-contraction sum: `w • 𝓣(ofFieldOpList φs)` equals the
sum of the weighted contraction terms `w • φsΛ.wickTerm`. The combinatorial
identity is HepLean's `wicks_theorem`; we only encode `w` through it. -/
theorem complexActionWeight_smul_wicks_theorem
    {𝓕 : FieldSpecification} (S_R S_I hbar : ℝ) (φs : List 𝓕.FieldOp) :
    complexActionWeight S_R S_I hbar •
        WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length,
        complexActionWeight S_R S_I hbar • φsΛ.wickTerm := by
  rw [wicks_theorem φs, Finset.smul_sum]

/-- The entropic complex weight likewise distributes over the Wick-contraction
expansion: `w(ρ,σ) • 𝓣(ofFieldOpList φs) = ∑ φsΛ, w(ρ,σ) • φsΛ.wickTerm`. The
entropic damping `exp(−D(ρ‖σ))` (the modulus of `w(ρ,σ)`) therefore multiplies
every contraction term uniformly. -/
theorem entropicComplexWeight_smul_wicks_theorem
    {𝓕 : FieldSpecification} (S_R hbar : ℝ) (ρ σ : MState d) (φs : List 𝓕.FieldOp) :
    entropicComplexWeight S_R hbar ρ σ •
        WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length,
        entropicComplexWeight S_R hbar ρ σ • φsΛ.wickTerm := by
  rw [wicks_theorem φs, Finset.smul_sum]

/-- **Entropic recovery of Wick's theorem as its entropy-free fiber.** The entropic
weight `w(ρ,σ)` is a complex exponential, hence never zero; dividing it out of
the entropic-weighted identity `w • 𝓣 = ∑ φsΛ, w • φsΛ.wickTerm` returns the
standard Wick expansion `𝓣(ofFieldOpList φs) = ∑ φsΛ, φsΛ.wickTerm`. This is the
precise sense in which the entropic contraction calculus **embeds and recovers**
Wick's theorem: the latter is the `w = 1` member of the entropic family. The
contraction *enumeration* itself is HepLean's `wicks_theorem`, used as input —
this layer does not derive it. -/
theorem entropic_weight_recovers_wicks_theorem
    {𝓕 : FieldSpecification} (S_R hbar : ℝ) (ρ σ : MState d) (φs : List 𝓕.FieldOp) :
    WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length, φsΛ.wickTerm := by
  have hw : entropicComplexWeight S_R hbar ρ σ ≠ 0 :=
    entropicComplexWeight_ne_zero S_R hbar ρ σ
  have h := entropicComplexWeight_smul_wicks_theorem S_R hbar ρ σ φs
  rw [← Finset.smul_sum] at h
  have h2 := congrArg (fun x => (entropicComplexWeight S_R hbar ρ σ)⁻¹ • x) h
  simpa only [inv_smul_smul₀ hw] using h2

end Physlib.QFT.Wick.Consistency

end

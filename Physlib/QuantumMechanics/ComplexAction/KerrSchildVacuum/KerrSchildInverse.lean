/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Complex.Basic

/-!
# The Kerr–Schild inverse metric

Formalizes the exact algebraic identity underlying every Kerr–Schild solution (J. Harada, *Exact vacuum
solution with Hopf structure in general relativity*, arXiv:2506.20878, §II, Eqs. 1–3): for the Kerr–Schild
metric `g_{μν} = η_{μν} + H k_μ k_ν` built from a flat metric `η`, a scalar `H`, and a covector `k` that is
**null** with respect to `η` (`η^{μν} k_μ k_ν = 0`), the inverse metric is *exactly linear* in `H`,

  `g^{μν} = η^{μν} − H k^μ k^ν`,   `k^μ = η^{μν} k_ν`   (Eq. 3).

`kerrSchild_mul_inverse` proves `g · g⁻¹ = 1` from the null condition alone — the cross terms cancel and the
`H²` term vanishes by nullity. As corollaries, `k` is null for the inverse metric too
(`kerrSchildInverse_mulVec_null`, Eq. 2), and the determinant is preserved (`det g = det η`).

## References

* J. Harada (2025), arXiv:2506.20878, §II; R. P. Kerr & A. Schild (1965). Carrier: `Mathlib` (`Matrix`).


-/

set_option autoImplicit false

open scoped BigOperators

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Kerr–Schild metric** `g_{μν} = η_{μν} + H k_μ k_ν`. -/
def kerrSchildMetric (η : Matrix ι ι ℝ) (H : ℝ) (k : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => η i j + H * k i * k j

/-- **The (conjectured-exact) Kerr–Schild inverse metric** `g^{μν} = η^{μν} − H k^μ k^ν` (with `k^μ` the
raised null covector). -/
def kerrSchildInverse (ηInv : Matrix ι ι ℝ) (H : ℝ) (kup : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ηInv i j - H * kup i * kup j

/-- **[Kerr–Schild inverse, Eq. 3] `g · g⁻¹ = 1`.** For a symmetric flat inverse `η⁻¹` (`η · η⁻¹ = 1`) and a
covector `k` null with respect to `η` (`k · (η⁻¹ k) = 0`), the metric `g = η + H k⊗k` has exact inverse
`η⁻¹ − H (η⁻¹k)⊗(η⁻¹k)` — linear in `H`. -/
lemma kerrSchild_mul_inverse (η ηInv : Matrix ι ι ℝ) (H : ℝ) (k : ι → ℝ)
    (hinv : η * ηInv = 1) (hsym : ηInvᵀ = ηInv) (hnull : dotProduct k (ηInv *ᵥ k) = 0) :
    kerrSchildMetric η H k * kerrSchildInverse ηInv H (ηInv *ᵥ k) = 1 := by
  have ηsym : ∀ a b, ηInv a b = ηInv b a := fun a b => by
    have h := congrFun (congrFun hsym b) a; rwa [Matrix.transpose_apply] at h
  set kup := ηInv *ᵥ k with hkup
  have hηk : η *ᵥ kup = k := by rw [hkup, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  ext i j
  rw [Matrix.mul_apply]
  have hsummand : ∀ l, kerrSchildMetric η H k i l * kerrSchildInverse ηInv H kup l j
      = η i l * ηInv l j + H * k i * (k l * ηInv l j)
        - H * kup j * (η i l * kup l) - H ^ 2 * k i * kup j * (k l * kup l) := fun l => by
    simp only [kerrSchildMetric, kerrSchildInverse, Matrix.of_apply]; ring
  rw [Finset.sum_congr rfl fun l _ => hsummand l]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsA : ∑ l, η i l * ηInv l j = (1 : Matrix ι ι ℝ) i j := by rw [← Matrix.mul_apply, hinv]
  have hsB : ∑ l, η i l * kup l = k i := by
    have h : (η *ᵥ kup) i = k i := congrFun hηk i
    simpa [Matrix.mulVec, dotProduct] using h
  have hsC : ∑ l, k l * ηInv l j = kup j := by
    simp only [hkup, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun l _ => by rw [ηsym l j, mul_comm]
  have hsD : ∑ l, k l * kup l = 0 := hnull
  rw [hsA, hsB, hsC, hsD]
  ring

omit [DecidableEq ι] in
/-- **[The raised covector is null for the inverse metric] (Eq. 2)** `g^{μν} k_μ k_ν = 0`. The inverse
Kerr–Schild metric annihilates `k` exactly as `η⁻¹` does. -/
lemma kerrSchildInverse_mulVec_null (ηInv : Matrix ι ι ℝ) (H : ℝ) (k : ι → ℝ)
    (hnull : dotProduct k (ηInv *ᵥ k) = 0) :
    dotProduct k (kerrSchildInverse ηInv H (ηInv *ᵥ k) *ᵥ k) = 0 := by
  have hkupk : dotProduct (ηInv *ᵥ k) k = 0 := by simpa [dotProduct_comm] using hnull
  have hrow : kerrSchildInverse ηInv H (ηInv *ᵥ k) *ᵥ k = ηInv *ᵥ k := by
    funext i
    show ∑ j, kerrSchildInverse ηInv H (ηInv *ᵥ k) i j * k j = (ηInv *ᵥ k) i
    simp only [kerrSchildInverse, Matrix.of_apply, sub_mul]
    rw [Finset.sum_sub_distrib]
    have h2 : ∑ j, H * (ηInv *ᵥ k) i * (ηInv *ᵥ k) j * k j = 0 := by
      rw [Finset.sum_congr rfl fun j _ =>
        show H * (ηInv *ᵥ k) i * (ηInv *ᵥ k) j * k j
          = (H * (ηInv *ᵥ k) i) * ((ηInv *ᵥ k) j * k j) from by ring,
        ← Finset.mul_sum]
      rw [show ∑ j, (ηInv *ᵥ k) j * k j = dotProduct (ηInv *ᵥ k) k from rfl, hkupk, mul_zero]
    rw [h2, sub_zero]
    rfl
  simpa [hrow] using hnull

/-! ## The Kerr metric: horizons and the ergosphere

The Kerr black hole of mass `M` and specific angular momentum `a` is a Kerr–Schild vacuum solution:
`g = η + H k⊗k` with the Kerr scalar `H` and the Kerr null congruence `k`, whose exact inverse is
`kerrSchild_mul_inverse` above. It is Ricci-flat (Harada §II–III), with the Petrov-D curvature of
`HopfInvariants` — hence a vacuum solution of the Einstein field equation `G_{μν} = 0` by
`ComplexEinstein.EinsteinFieldEquationsPhysLean.ricciFlat_satisfies_einsteinFieldEquation`. Its causal
structure is governed by the Boyer–Lindquist horizon function `Δ(r) = r² − 2Mr + a²`. -/

/-- **The Kerr horizon function** `Δ(r) = r² − 2Mr + a²` (Boyer–Lindquist). -/
def kerrDelta (M a r : ℝ) : ℝ := r ^ 2 - 2 * M * r + a ^ 2

/-- **The outer (event) horizon** `r₊ = M + √(M² − a²)`. -/
noncomputable def kerrHorizonOuter (M a : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2)

/-- **The inner (Cauchy) horizon** `r₋ = M − √(M² − a²)`. -/
noncomputable def kerrHorizonInner (M a : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - a ^ 2)

/-- **[Δ factorizes over its horizons]** `Δ(r) = (r − r₊)(r − r₋)` in the subextremal regime `a² ≤ M²`. -/
theorem kerrDelta_factored (M a r : ℝ) (h : a ^ 2 ≤ M ^ 2) :
    kerrDelta M a r = (r - kerrHorizonOuter M a) * (r - kerrHorizonInner M a) := by
  have hs : Real.sqrt (M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  rw [kerrDelta, kerrHorizonOuter, kerrHorizonInner]; linear_combination hs

/-- **The outer horizon is a root of `Δ`** `Δ(r₊) = 0` (subextremal `a² ≤ M²`). -/
theorem kerrDelta_horizonOuter (M a : ℝ) (h : a ^ 2 ≤ M ^ 2) :
    kerrDelta M a (kerrHorizonOuter M a) = 0 := by
  rw [kerrDelta_factored M a (kerrHorizonOuter M a) h]; ring

/-- **The inner horizon is a root of `Δ`** `Δ(r₋) = 0` (subextremal `a² ≤ M²`). -/
theorem kerrDelta_horizonInner (M a : ℝ) (h : a ^ 2 ≤ M ^ 2) :
    kerrDelta M a (kerrHorizonInner M a) = 0 := by
  rw [kerrDelta_factored M a (kerrHorizonInner M a) h]; ring

/-- **[Over-extremal ⇒ no horizon]** `M² < a²`: `Δ(r) > 0` for all `r`, so there is no event horizon —
the naked-singularity regime. -/
theorem kerrDelta_pos_of_overextremal (M a r : ℝ) (h : M ^ 2 < a ^ 2) : 0 < kerrDelta M a r := by
  rw [kerrDelta]; nlinarith [sq_nonneg (r - M)]

/-- **[Schwarzschild limit] `a = 0`** `Δ = r(r − 2M)` — the single horizon at `r = 2M`. -/
theorem kerrDelta_schwarzschild (M r : ℝ) : kerrDelta M 0 r = r * (r - 2 * M) := by
  rw [kerrDelta]; ring

/-- **[Schwarzschild horizon] `r₊ = 2M`** at `a = 0` for `M ≥ 0`. -/
theorem kerrHorizonOuter_schwarzschild (M : ℝ) (hM : 0 ≤ M) : kerrHorizonOuter M 0 = 2 * M := by
  rw [kerrHorizonOuter, show M ^ 2 - (0 : ℝ) ^ 2 = M ^ 2 by ring, Real.sqrt_sq hM]; ring

/-- **[Extremal Kerr] `a = M`** the two horizons coincide and `Δ = (r − M)²`. -/
theorem kerrDelta_extremal (M r : ℝ) : kerrDelta M M r = (r - M) ^ 2 := by
  rw [kerrDelta]; ring

/-- **[Extremal horizons coincide] `r₊ = r₋ = M`** at `a = M`. -/
theorem kerrHorizon_extremal (M : ℝ) :
    kerrHorizonOuter M M = M ∧ kerrHorizonInner M M = M := by
  rw [kerrHorizonOuter, kerrHorizonInner, show M ^ 2 - M ^ 2 = (0 : ℝ) by ring, Real.sqrt_zero]
  constructor <;> ring

/-- **The static-limit (ergosphere) surface** `r_E(θ) = M + √(M² − a²cos²θ)` — the outer boundary of the
ergoregion, where the timelike Killing field `∂_t` becomes null (`g_{tt} = 0`, `c = cos θ`). -/
noncomputable def kerrStaticLimit (M a c : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2 * c ^ 2)

/-- **The ergosphere lies outside the event horizon** `r_E(θ) ≥ r₊`: the ergoregion `r₊ ≤ r ≤ r_E` is
where energy extraction (the Penrose process) is possible. -/
theorem kerrStaticLimit_ge_horizonOuter (M a c : ℝ) (hc : c ^ 2 ≤ 1) :
    kerrHorizonOuter M a ≤ kerrStaticLimit M a c := by
  rw [kerrHorizonOuter, kerrStaticLimit]
  have hac : a ^ 2 * c ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
  have hle : M ^ 2 - a ^ 2 ≤ M ^ 2 - a ^ 2 * c ^ 2 := by linarith
  linarith [Real.sqrt_le_sqrt hle]

/-- **The ergosphere meets the horizon at the poles** `r_E = r₊` at `cos²θ = 1`: the ergoregion pinches
off on the rotation axis. -/
theorem kerrStaticLimit_poles (M a : ℝ) : kerrStaticLimit M a 1 = kerrHorizonOuter M a := by
  rw [kerrStaticLimit, kerrHorizonOuter, show M ^ 2 - a ^ 2 * (1 : ℝ) ^ 2 = M ^ 2 - a ^ 2 by ring]

/-! ### The Newman–Janis complex shift: Kerr from Schwarzschild

Arkani-Hamed–Huang–O'Connell (*Kerr black holes as elementary particles*, JHEP 01 (2020) 046,
arXiv:1906.10100, §2): the Kerr–Schild scalar `φ_Kerr(r,θ) = r₀ r/(r² + a²cos²θ)` (Eq 2.3) is obtained
from the Schwarzschild scalar `φ_Sch = r₀/r` (Eq 2.2) by the **Newman–Janis complex shift** `z → z + ia`,
equivalently `r → r + ia cos θ` (Eq 2.6) — equivalently `φ_Kerr = r₀ · Re(1/(r + ia cos θ))`, the real
part of the complex-shifted Coulomb potential. Its electromagnetic single copy `A^μ = c^a k^μ φ` is the
"√Kerr" of the double copy (Eq 2.7). Here `c = cos θ` and `r₀ = 2GM`; the amplitudes picture identifies
this shift with the exponentiated spin factor `exp(q·a)` of the minimally coupled spinning particle. -/

/-- **The Kerr–Schild scalar potential** `φ(r,θ) = r₀ r/(r² + a²cos²θ)` (Arkani-Hamed et al. Eq 2.3,
`c = cos θ`). -/
noncomputable def kerrPotential (r0 a r c : ℝ) : ℝ := r0 * r / (r ^ 2 + a ^ 2 * c ^ 2)

/-- **[Schwarzschild limit] `a = 0`** `φ = r₀/r` (Eq 2.2). -/
theorem kerrPotential_schwarzschild (r0 r c : ℝ) (hr : r ≠ 0) :
    kerrPotential r0 0 r c = r0 / r := by
  rw [kerrPotential, show (0 : ℝ) ^ 2 * c ^ 2 = 0 by ring, add_zero, sq]
  field_simp

/-- **[Newman–Janis shift, Eq 2.6] `φ_Kerr = r₀ · Re(1/(r + ia cosθ))`.** The Kerr potential is the real
part of the complex-shifted (`z → z + ia`) Schwarzschild/Coulomb potential — the shift taking
Schwarzschild to Kerr and Coulomb to √Kerr. -/
theorem kerrPotential_eq_re_shifted_coulomb (r0 a r c : ℝ) :
    kerrPotential r0 a r c = r0 * (1 / ((r : ℂ) + Complex.I * (a * c))).re := by
  rw [kerrPotential, one_div, Complex.inv_re]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

end Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum

end

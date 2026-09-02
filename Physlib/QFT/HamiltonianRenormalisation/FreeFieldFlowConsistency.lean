/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.HamiltonianRenormalisation.WeylAnnihilatorSystem
public import Physlib.QFT.HamiltonianRenormalisation.FreeFieldMeasureReconstruction
public import Physlib.QFT.HamiltonianRenormalisation.BargmannCoherentShift
public import Physlib.QFT.HamiltonianRenormalisation.InducedHamiltonianSemigroup
public import Physlib.Mathematics.WeightedSmoothNuclearity

/-!
# Consistency of the free-field flow arc across its layers

Mechanical links between the modules of the Hamiltonian-renormalisation arc — each
statement combines two layers that were developed separately, so their agreement is a
theorem, not a citation:

* `WeylAnnihilatorSystem.ann_coherent_damped` — **Eq. 2.40 meets Eq. 3.115**: the
  contraction of `FreeFieldMeasureReconstruction` maps coherent vectors to coherent vectors
  with damped smearing `f̂ = e^{−βcω}f`; on the abstract system the damped coherent vector is
  again an annihilator eigenvector, with the eigenvalue scaled by the same damping factor.
* `ann_coherentPoly_damped` — the same statement realized on the Bargmann–Fock polynomials
  of `BargmannCoherentShift`: the damped truncated coherent state is an eigenvector with the
  damped eigenvalue, exactly, at every truncation order.
* `transferRatio_cocycle_exp` — the cocycle hypothesis of
  `FreeFieldMeasureReconstruction.transferRatio_cocycle` is *instantiated* by the actual
  free-field damping `f ↦ e^{−cωβ}·f`: the concrete Gaussian transfer ratios of Eq. 2.40
  compose as a one-parameter semigroup.
* `imagePoleTerm_tendsto_zero`, `principalPoleTerm_tendsto_continuum`,
  `continuum_covariance_dictionary` — **Eqs. 3.72–3.75 meet §3.3**: the pole terms whose
  coefficients `imagePole_coefficient` extracts from the fixed-point covariance are the
  functions whose limits `DirectHamiltonianFlow` computes; composing the two, each image
  pole term (`N ≠ 0`) switches off *entirely* in the continuum limit — coefficient and
  denominator together — while the principal term converges to `1/q²`, which under the
  lattice dictionary `q² = (k₀²+p²)ε²` is the continuum covariance `1/(k₀²+p²)`: the flow
  ends at the free continuum theory it started from.

## References

* T. Lang, K. Liegener, T. Thiemann, *Hamiltonian renormalisation II*, arXiv:1711.06727v2,
  §§2.4, 3.1.2, 3.3 (Eqs. 2.40–2.41, 3.72–3.76).
-/

set_option autoImplicit false

open Filter Topology

@[expose] public section

namespace Physlib.QFT.HamiltonianRenormalisation

/-! ## §A — the contraction and the annihilator agree on coherent vectors -/

/-- **Eq. 2.40 meets Eq. 3.115**: the damped coherent vector — the image of `W(f)Ω` under
the free-field contraction, up to its Gaussian ratio — is again an annihilator eigenvector,
with the eigenvalue damped by the same factor `r = e^{−βcω}`. -/
theorem WeylAnnihilatorSystem.ann_coherent_damped {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : WeylAnnihilatorSystem E H) (f g : E) (r : ℝ) :
    S.ann g (S.weyl (r • f) S.vacuum)
      = (Complex.I * (S.scale : ℂ) * ((r * inner ℝ g (S.halfInv f) : ℝ) : ℂ))
          • S.weyl (r • f) S.vacuum := by
  rw [S.ann_coherent (r • f) g, map_smul, real_inner_smul_right]

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.BargmannFockCCR

/-- Real scalings pass through the Bargmann inner product of the directions. -/
theorem bargmannInner_real_smul {n : ℕ} (r : ℝ) (a b : Fin n → ℂ) :
    bargmannInner a (fun i => (r : ℂ) * b i) = (r : ℂ) * bargmannInner a b := by
  unfold bargmannInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- **The damped coherent eigenvector on the Bargmann–Fock polynomials**: the faithful
realization of `ann_coherent_damped` — damping the direction damps the eigenvalue, exactly,
at every truncation order. -/
theorem ann_coherentPoly_damped {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) (N : ℕ) :
    ann a (coherentPoly (N+1) (fun i => (r : ℂ) * b i))
      = ((r : ℂ) * bargmannInner a b) • coherentPoly N (fun i => (r : ℂ) * b i) := by
  rw [ann_coherentPoly a _ N, bargmannInner_real_smul]

/-- **The free-field damping instantiates the cocycle**: with the concrete damping
`f ↦ e^{−cωβ}·f` of Eq. 2.40, the hypothesis of `transferRatio_cocycle` holds and the
Gaussian transfer ratios compose as a one-parameter semigroup. -/
theorem transferRatio_cocycle_exp {E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : E → ℝ) (c ω a β₁ β₂ : ℝ) (f : E) :
    Real.exp (-(a/4) * (q (Real.exp (-(c*ω*β₂)) • f)
        - q (Real.exp (-(c*ω*β₁)) • (Real.exp (-(c*ω*β₂)) • f))))
      * Real.exp (-(a/4) * (q f - q (Real.exp (-(c*ω*β₂)) • f)))
      = Real.exp (-(a/4) * (q f - q (Real.exp (-(c*ω*(β₁+β₂))) • f))) := by
  have hdamp : ∀ β₁ β₂ (g : E), Real.exp (-(c*ω*β₁)) • (Real.exp (-(c*ω*β₂)) • g)
      = Real.exp (-(c*ω*(β₁+β₂))) • g := by
    intro β₁ β₂ g
    rw [smul_smul, ← Real.exp_add]
    ring_nf
  exact transferRatio_cocycle q (fun β g => Real.exp (-(c*ω*β)) • g) hdamp a β₁ β₂ f

/-! ## §B — the pole terms meet the continuum limit -/

/-- **Each image pole term switches off entirely** (Eqs. 3.72–3.75 composed with §3.3): not
merely the coefficient `ĝ_N` but the whole simple-pole term of the fixed-point covariance —
the object `imagePole_coefficient` extracts — tends to zero for `N ≠ 0` in the continuum
limit. -/
theorem imagePoleTerm_tendsto_zero (q : ℝ) (N : ℤ) (hN : N ≠ 0) :
    Tendsto (fun t : ℝ =>
        (2*(1 - Real.cos t)/(t + 2*Real.pi*N)^2) / (q^2 + (t + 2*Real.pi*N)^2))
      (𝓝 (0:ℝ)) (𝓝 0) := by
  have hnum := couplingFunction_tendsto_zero N hN
  have hden : Tendsto (fun t : ℝ => q^2 + (t + 2*Real.pi*N)^2)
      (𝓝 (0:ℝ)) (𝓝 (q^2 + (2*Real.pi*N)^2)) := by
    have hc : Continuous fun t : ℝ => q^2 + (t + 2*Real.pi*N)^2 := by continuity
    simpa using hc.tendsto 0
  have hNr : (2*Real.pi*(N:ℝ)) ≠ 0 := by
    have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hNc : ((N:ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hN
    positivity
  have hden_ne : (q^2 + (2*Real.pi*N)^2 : ℝ) ≠ 0 := by
    have h2 : (0:ℝ) < (2*Real.pi*(N:ℝ))^2 := by positivity
    nlinarith [sq_nonneg q]
  have h := hnum.div hden hden_ne
  rw [zero_div] at h
  exact h.congr fun _ => rfl

/-- **The principal pole term converges to the continuum covariance** `1/q²` (Eq. 3.75 at
`N = 0` composed with §3.3): coefficient and pole together, the surviving species carries
the continuum dispersion. -/
theorem principalPoleTerm_tendsto_continuum (q : ℝ) (hq : q ≠ 0) :
    Tendsto (fun t : ℝ => (2*(1 - Real.cos t)/t^2) / (q^2 + t^2))
      (𝓝[≠] (0:ℝ)) (𝓝 (1/q^2)) := by
  have hnum := couplingFunction_tendsto_one
  have hden : Tendsto (fun t : ℝ => q^2 + t^2) (𝓝[≠] (0:ℝ)) (𝓝 (q^2)) := by
    have hc : Continuous fun t : ℝ => q^2 + t^2 := by continuity
    have h0 := hc.tendsto 0
    norm_num at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hq2 : (q^2 : ℝ) ≠ 0 := pow_ne_zero 2 hq
  exact (hnum.div hden hq2).congr fun _ => rfl

/-- **The lattice dictionary closes the loop**: under `q² = (k₀²+p²)ε²` the continuum limit
`ε²·(1/q²)` of the principal pole term is the free continuum covariance `1/(k₀²+p²)` — the
flow ends at the theory it started from. -/
theorem continuum_covariance_dictionary (ε k₀ p q : ℝ)
    (hq : q^2 = (k₀^2 + p^2) * ε^2) (hε : ε ≠ 0) (hk : k₀^2 + p^2 ≠ 0) :
    ε^2 * (1/q^2) = 1/(k₀^2 + p^2) := by
  rw [hq]
  field_simp

/-! ## §C — the reconstruction kernel weight falls under the nuclearity conditions -/

/-- **The OS kernel weight fulfils (ω.1)**: the exponential kernel `t ↦ e^{−ω|t|}` — the
weight through which `FreeFieldMeasureReconstruction.historyPairing` pairs sharp-time
families — is ball comparable in the sense of the Kruse nuclearity conditions
(`Mathematics.WeightedSmoothNuclearity`), with any constant radius `δ` and constant
`e^{2|ω|δ}`: the free-field reconstruction operates inside a nuclear weight family, the
hypothesis under which its Schwinger functionals extend to kernels on product spaces. -/
theorem osKernelWeight_ballComparable (ω δ : ℝ) (hδ : 0 ≤ δ) :
    Physlib.Mathematics.WeightedSmoothNuclearity.BallComparable
      (fun t : ℝ => Real.exp (-(ω * |t|))) (fun t : ℝ => Real.exp (-(ω * |t|)))
      (fun _ => δ) (Real.exp (2 * |ω| * δ)) := by
  have h := Physlib.Mathematics.WeightedSmoothNuclearity.expNormWeight_ballComparable
    (X := ℝ) (-ω) δ hδ
  simpa [Real.norm_eq_abs, neg_mul, abs_neg] using h

end Physlib.QFT.HamiltonianRenormalisation

end

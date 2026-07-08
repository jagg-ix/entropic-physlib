/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopScalarIntegralsQCD

/-!
# Generalized D-dimensional unitarity: amplitudes as combinations of master integrals

Formalizes the core decomposition of R. K. Ellis, W. T. Giele, Z. Kunszt, K. Melnikov,
*Masses, fermions and generalized D-dimensional unitarity*, Nucl. Phys. B **822** (2009) 270, and
**applies/extends** the scalar one-loop masters of `PathIntegral.OneLoopScalarIntegralsQCD` (the
`ScalarIntegralLaurent` tadpole/bubble/triangle/box of Ellis–Zanderighi).

The central statement (their Eq. 2.1) is that *any* `N`-particle one-loop amplitude is a **linear
combination of master integrals**:

  `A⁽¹⁾_N = Σ dᵢ I₄ᵢ + Σ cᵢ I₃ᵢ + Σ bᵢ I₂ᵢ + Σ aᵢ I₁ᵢ + (D-dim/rational)`,

with coefficients fixed by **generalized unitarity cuts**: the residue of the amplitude on a
multi-particle cut factorizes into a product of on-shell tree amplitudes (their Eq. 12,
`Res A⁽¹⁾ ∼ Σ_states A⁽⁰⁾_L × A⁽⁰⁾_R`).

What is formalized (the masters' `ε`-Laurent expansions are the underlying spaces; the genuine content is the
*linearity* of the decomposition, the pole bookkeeping, and the D-dimensional rational mechanism):

* **§A — the amplitude as a linear combination of masters** (`oneLoopAmplitude`, Eq. 2.1): the
  `1/ε²`, `1/ε`, `ε⁰` coefficients of the amplitude are the coefficient-weighted sums of the masters'.
* **§B — pole structure and finiteness** (`amplitude_uv_finite_of_all_finite`,
  `amplitude_pole_cancellation`): the amplitude's UV/IR poles are the linear combination of the
  masters' poles; the amplitude is finite when they vanish (cancel).
* **§C — the generalized unitarity cut** (`cutResidue`, `cutCoefficient`, Eq. 12): a master's
  coefficient is the cut residue `Σ_states treeₗ · treeᵣ` — the factorization of the one-loop residue
  into tree amplitudes (bilinear in the trees, `cutCoefficient_add_left`).
* **§D — the D-dimensional rational mechanism** (`epsShift`, `rational_from_dDim`): the
  `ε`-suppressed extra-dimensional integrals `ε·Î⁽ᴰ⁺²⁾` convert a master's `1/ε` pole into a **finite
  rational** term — the rational part missed by four-dimensional (cut-constructible) unitarity.
* **§E — the link** (`anomalousMoment_as_amplitude`, `anomalousMoment_no_rational`,
  `tadpole_rational`): the anomalous-moment vertex (`anomalousMomentVertex`) is a single UV-finite
  master contributing no rational term, while a divergent master (`tadpoleLaurent`) contributes the
  rational `m²`.

## References

* R. K. Ellis, W. T. Giele, Z. Kunszt, K. Melnikov, Nucl. Phys. B 822 (2009) 270, arXiv:0906.1445
  (Eq. 2.1 master decomposition, Eq. 12 unitarity cut). Builds on the EGKM method, arXiv:0801.2237.
* Repo structure: `PathIntegral.OneLoopScalarIntegralsQCD` (`ScalarIntegralLaurent`, `IsUVFinite`, `tadpoleLaurent`,
  `anomalousMomentVertex`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GeneralizedDDimensionalUnitarity

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopScalarIntegralsQCD

variable {ι : Type*} {σ : Type*}

/-! ## §A — the amplitude as a linear combination of master integrals (Eq. 2.1) -/

/-- **[Generalized unitarity, Eq. 2.1] the one-loop amplitude as a linear combination of master
integrals** `A⁽¹⁾ = Σᵢ coeffᵢ · masterᵢ`. The amplitude's `1/ε²`, `1/ε`, `ε⁰` coefficients are the
coefficient-weighted sums of the masters' Laurent coefficients. -/
noncomputable def oneLoopAmplitude (s : Finset ι) (coeff : ι → ℂ) (master : ι → ScalarIntegralLaurent) :
    ScalarIntegralLaurent where
  eps2 := ∑ i ∈ s, coeff i * (master i).eps2
  eps1 := ∑ i ∈ s, coeff i * (master i).eps1
  eps0 := ∑ i ∈ s, coeff i * (master i).eps0

@[simp] theorem oneLoopAmplitude_eps2 (s : Finset ι) (coeff : ι → ℂ)
    (master : ι → ScalarIntegralLaurent) :
    (oneLoopAmplitude s coeff master).eps2 = ∑ i ∈ s, coeff i * (master i).eps2 := rfl

@[simp] theorem oneLoopAmplitude_eps1 (s : Finset ι) (coeff : ι → ℂ)
    (master : ι → ScalarIntegralLaurent) :
    (oneLoopAmplitude s coeff master).eps1 = ∑ i ∈ s, coeff i * (master i).eps1 := rfl

@[simp] theorem oneLoopAmplitude_eps0 (s : Finset ι) (coeff : ι → ℂ)
    (master : ι → ScalarIntegralLaurent) :
    (oneLoopAmplitude s coeff master).eps0 = ∑ i ∈ s, coeff i * (master i).eps0 := rfl

/-- **A single master is its own (coefficient-`1`) amplitude.** -/
theorem oneLoopAmplitude_single [DecidableEq ι] (i : ι) (master : ι → ScalarIntegralLaurent) :
    oneLoopAmplitude {i} (fun _ => 1) master = master i := by
  simp [oneLoopAmplitude, Finset.sum_singleton]

/-! ## §B — the pole structure and finiteness of the amplitude -/

/-- **[All masters finite ⟹ amplitude finite] no poles to cancel.** If every contributing master is
UV/IR finite, the amplitude is finite (its pole sums are sums of zeros). -/
theorem amplitude_uv_finite_of_all_finite (s : Finset ι) (coeff : ι → ℂ)
    (master : ι → ScalarIntegralLaurent) (h : ∀ i ∈ s, IsUVFinite (master i)) :
    IsUVFinite (oneLoopAmplitude s coeff master) := by
  constructor
  · simp only [oneLoopAmplitude_eps2]
    exact Finset.sum_eq_zero fun i hi => by rw [(h i hi).1, mul_zero]
  · simp only [oneLoopAmplitude_eps1]
    exact Finset.sum_eq_zero fun i hi => by rw [(h i hi).2, mul_zero]

/-- **[Pole cancellation ⟹ finite amplitude]** the amplitude is UV/IR finite exactly when the
coefficient-weighted master poles cancel — `Σ coeffᵢ·eps2ᵢ = 0` and `Σ coeffᵢ·eps1ᵢ = 0`. This is how a
sum of *individually divergent* QCD master integrals produces a finite physical amplitude. -/
theorem amplitude_pole_cancellation (s : Finset ι) (coeff : ι → ℂ)
    (master : ι → ScalarIntegralLaurent)
    (h2 : ∑ i ∈ s, coeff i * (master i).eps2 = 0)
    (h1 : ∑ i ∈ s, coeff i * (master i).eps1 = 0) :
    IsUVFinite (oneLoopAmplitude s coeff master) :=
  ⟨h2, h1⟩

/-! ## §C — the generalized unitarity cut (Eq. 12) -/

/-- **[Unitarity cut, Eq. 12] the residue factorizes into tree amplitudes** `Res A⁽¹⁾ ∼ A⁽⁰⁾_L·A⁽⁰⁾_R`
— the contribution of a single intermediate state to a generalized cut is the product of the on-shell
tree amplitudes on each side of the cut. -/
def cutResidue (treeL treeR : ℂ) : ℂ := treeL * treeR

/-- **[Master coefficient from the cut] `coeff = Σ_states A⁽⁰⁾_L·A⁽⁰⁾_R`** (Eq. 12) — a master
integral's coefficient is the unitarity-cut residue, summed over the intermediate on-shell states of
the cut lines. -/
noncomputable def cutCoefficient (states : Finset σ) (treeL treeR : σ → ℂ) : ℂ :=
  ∑ st ∈ states, cutResidue (treeL st) (treeR st)

/-- **The cut residue is bilinear in the cut trees** (a tree amplitude on one side adds linearly). -/
theorem cutResidue_add_left (treeL treeL' treeR : ℂ) :
    cutResidue (treeL + treeL') treeR = cutResidue treeL treeR + cutResidue treeL' treeR := by
  simp [cutResidue, add_mul]

/-- **The cut coefficient is additive in the left tree amplitudes** (linearity of the cut over the
intermediate-state sum). -/
theorem cutCoefficient_add_left (states : Finset σ) (treeL treeL' treeR : σ → ℂ) :
    cutCoefficient states (fun st => treeL st + treeL' st) treeR
      = cutCoefficient states treeL treeR + cutCoefficient states treeL' treeR := by
  simp only [cutCoefficient, cutResidue, add_mul]
  exact Finset.sum_add_distrib

/-! ## §D — the D-dimensional rational mechanism -/

/-- **[The `ε`-shift of the extra-dimensional integrals] `ε·I⁽ᴰ⁺²⁾`.** Multiplying a master by the
explicit `ε` that accompanies the `(D+2)`/`(D+4)`-dimensional integrals in Eq. 2.1 shifts its Laurent
expansion down by one: `ε·(c₋₂/ε² + c₋₁/ε + c₀) = c₋₂/ε + c₋₁ + O(ε)`. -/
def epsShift (L : ScalarIntegralLaurent) : ScalarIntegralLaurent where
  eps2 := 0
  eps1 := L.eps2
  eps0 := L.eps1

/-- **[Rational terms from D-dimensional unitarity] the `ε·I⁽ᴰ⁺²⁾` pole becomes a finite rational
term** `(ε·I)₀ = I₋₁`. The `ε`-suppressed extra-dimensional master integrals turn their `1/ε` poles
into finite **rational** contributions to the amplitude — the rational part invisible to purely
four-dimensional (cut-constructible) unitarity. -/
theorem rational_from_dDim (L : ScalarIntegralLaurent) : (epsShift L).eps0 = L.eps1 := rfl

/-! ## §E — the link to the anomalous moment and the QCD masters -/

/-- **[The anomalous-moment vertex is a one-master amplitude]** — a generalized-unitarity amplitude
with a single UV-finite master integral. -/
theorem anomalousMoment_as_amplitude (α : ℝ) :
    oneLoopAmplitude {(0 : Fin 1)} (fun _ => 1) (fun _ => anomalousMomentVertex α)
      = anomalousMomentVertex α :=
  oneLoopAmplitude_single 0 _

/-- **[A finite master contributes no rational term] `(ε·F₂)₀ = 0`.** The UV-finite anomalous-moment
vertex has no `1/ε` pole, so its `ε`-shifted (extra-dimensional) contribution vanishes — the anomalous
moment is purely cut-constructible, no rational piece. -/
theorem anomalousMoment_no_rational (α : ℝ) : (epsShift (anomalousMomentVertex α)).eps0 = 0 := by
  rw [rational_from_dDim]; rfl

/-- **[A divergent master contributes a rational term] `(ε·I₁)₀ = m²`.** The UV-divergent tadpole has
a `1/ε` pole `m²`, so its `ε`-shifted extra-dimensional contribution is the finite rational `m²` — the
genuine D-dimensional rational term that four-dimensional unitarity would miss. -/
theorem tadpole_rational (m2 : ℝ) : (epsShift (tadpoleLaurent m2)).eps0 = (m2 : ℂ) := by
  rw [rational_from_dDim]; rfl

/-- **[Generalized D-dimensional unitarity, assembled] one structure across the cut, the masters, and
the rational part.** The anomalous-moment vertex is a single UV-finite master amplitude
(`anomalousMoment_as_amplitude`) with no rational term (`anomalousMoment_no_rational`); a divergent
master includes the D-dimensional rational `m²` (`tadpole_rational`); and any amplitude built from
finite masters is finite (`amplitude_uv_finite_of_all_finite`). The coefficients are the unitarity-cut
residues `Σ_states treeₗ·treeᵣ` (`cutCoefficient`). -/
theorem generalized_unitarity_assembled (α m2 : ℝ) :
    oneLoopAmplitude {(0 : Fin 1)} (fun _ => 1) (fun _ => anomalousMomentVertex α)
        = anomalousMomentVertex α
      ∧ (epsShift (anomalousMomentVertex α)).eps0 = 0
      ∧ (epsShift (tadpoleLaurent m2)).eps0 = (m2 : ℂ) :=
  ⟨anomalousMoment_as_amplitude α, anomalousMoment_no_rational α, tadpole_rational m2⟩

end Physlib.QuantumMechanics.ComplexAction.GeneralizedDDimensionalUnitarity

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution

/-!
# Open-system (Lindblad) evolution: the dissipative generator preserves probability

The open-system / dissipative regime of the time-evolution architecture (McArdle et al, Rev. Mod. Phys. **92**
(2020) 015003, arXiv:1808.10402): density-matrix dynamics under the **Lindblad (GKSL) generator**

  `𝓛[ρ] = −i[H,ρ] + Σ_k ( L_k ρ L_k† − ½{L_k† L_k, ρ} )`,

the natural home of the CAT/EPT entropic generator `Γ_I` (an *open-system* dissipator, not a closed-system
Hermitian correction). The defining structural property is **trace (probability) preservation**
`Tr 𝓛[ρ] = 0` — the review's Target 3 — which holds for *any* cyclic trace functional `Tr(ab)=Tr(ba)`.

* **§A — the generator.** `coherentPart H ρ = −i[H,ρ]`, `dissipatorTerm L ρ = LρL† − ½{L†L,ρ}`,
  `lindbladGenerator H Ls ρ`.
* **§B — trace preservation.** `coherentPart_trace_zero`, `dissipatorTerm_trace_zero`,
  `dissipatorSum_trace_zero`, and the main result `lindblad_trace_preserving` (`Tr 𝓛[ρ] = 0`).

**Honest layering.** Proven: trace preservation for an abstract `ℂ`-linear cyclic trace `Tr : A →ₗ[ℂ] ℂ`
(`Tr(ab)=Tr(ba)`) — the algebraic core of probability conservation. Complete positivity of the generated
semigroup, the actual exponential `e^{t𝓛}`, and the entropy-monotonicity `dS/dt ≥ 0` are the analytic /
operator-semigroup content, named but not derived here. (Per `QuantumChemistry.TimeEvolution.ChannelSource`,
the dissipator's physical origin — hardware noise vs. thermodynamic bath vs. CAT/EPT information loss — must be
declared separately.)

## References

* G. Lindblad, Commun. Math. Phys. **48** (1976) 119, doi:10.1007/BF01608499; V. Gorini, A. Kossakowski,
  E. C. G. Sudarshan, J. Math. Phys. **17** (1976) 821. S. McArdle et al, Rev. Mod. Phys. **92** (2020)
  015003; arXiv:1808.10402 — open-system `ρ = ∏ᵢ 𝒩ᵢ∘Uᵢ(ρ₀)`, `Ō = Tr[ρ O]`. `Physlib`
  (`QuantumChemistry.TimeEvolution`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OpenSystemLindblad

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A]


/-- The **coherent (von Neumann) part** `−i[H,ρ]` of the generator. -/
def coherentPart (H ρ : A) : A := (-Complex.I) • (H * ρ - ρ * H)

/-- A single **Lindblad dissipator term** `L ρ L† − ½{L†L, ρ} = LρL† − ½(L†Lρ + ρL†L)`. -/
noncomputable def dissipatorTerm (L ρ : A) : A :=
  L * ρ * star L - (2⁻¹ : ℂ) • (star L * L * ρ + ρ * (star L * L))

/-- The **Lindblad (GKSL) generator** `𝓛[ρ] = −i[H,ρ] + Σ_k (L_kρL_k† − ½{L_k†L_k, ρ})`. -/
noncomputable def lindbladGenerator (H : A) (Ls : List A) (ρ : A) : A :=
  coherentPart H ρ + (Ls.map fun L => dissipatorTerm L ρ).sum


variable (tr : A →ₗ[ℂ] ℂ) (htr_cyc : ∀ a b : A, tr (a * b) = tr (b * a))
include htr_cyc

/-- **[The coherent part is traceless]** `Tr(−i[H,ρ]) = 0` — the trace of a commutator vanishes
(cyclicity). -/
lemma coherentPart_trace_zero (H ρ : A) : tr (coherentPart H ρ) = 0 := by
  unfold coherentPart
  rw [map_smul, map_sub, htr_cyc ρ H, sub_self, smul_zero]

/-- **[Each dissipator term is traceless]** `Tr(LρL† − ½{L†L,ρ}) = 0` — by cyclicity
`Tr(LρL†) = Tr(L†Lρ) = Tr(ρL†L)`, so the gain term cancels the `½`-weighted loss terms. -/
lemma dissipatorTerm_trace_zero (L ρ : A) : tr (dissipatorTerm L ρ) = 0 := by
  have ht1 : tr (L * ρ * star L) = tr (star L * L * ρ) := by
    rw [htr_cyc (L * ρ) (star L), mul_assoc]
  have ht3 : tr (ρ * (star L * L)) = tr (star L * L * ρ) := by
    rw [htr_cyc ρ (star L * L)]
  unfold dissipatorTerm
  rw [map_sub, map_smul, map_add, ht1, ht3, smul_eq_mul]
  ring

/-- **[The full dissipator is traceless]** `Tr(Σ_k LₖρLₖ† − ½{Lₖ†Lₖ,ρ}) = 0`. -/
lemma dissipatorSum_trace_zero (Ls : List A) (ρ : A) :
    tr ((Ls.map fun L => dissipatorTerm L ρ).sum) = 0 := by
  induction Ls with
  | nil => simp
  | cons L Ls ih =>
    rw [List.map_cons, List.sum_cons, map_add, dissipatorTerm_trace_zero tr htr_cyc L ρ, zero_add, ih]

/-- **[The Lindblad generator preserves the trace] `Tr 𝓛[ρ] = 0`** — probability is conserved under
open-system (dissipative) evolution: `d/dt Tr ρ = 0`. The defining structural property of a Lindblad
generator, here for any cyclic trace `Tr(ab)=Tr(ba)`. -/
lemma lindblad_trace_preserving (H : A) (Ls : List A) (ρ : A) :
    tr (lindbladGenerator H Ls ρ) = 0 := by
  unfold lindbladGenerator
  rw [map_add, coherentPart_trace_zero tr htr_cyc H ρ, zero_add,
    dissipatorSum_trace_zero tr htr_cyc Ls ρ]

end Physlib.QuantumMechanics.ComplexAction.OpenSystemLindblad

end

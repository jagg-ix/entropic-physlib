/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexSaddleDecoherence
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
public import Physlib.CondensedMatter.TightBindingChain.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.MetricSpace.Contracting
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# Discretizing and varying the Caldeira–Leggett model

The companion to `ComplexSaddleDecoherence` (same paper, arXiv:2408.16627): before the complex-saddle evaluation
of the decoherence structure (Eqs. 18–30), Nishimura & Watanabe set up the discretized Caldeira–Leggett model
(Eqs. 1–8) — a system oscillator `x` coupled to a bath of `N_ℰ` oscillators `q^k` with an **Ohmic** spectral
density. This module formalizes the exact-algebra core of that setup.

**The Ohmic spectrum (Eqs. 2–3).** Reproducing the Ohmic bath requires the mode frequencies
`ω_k = ω_cut (k/N_ℰ)^{1/3}`; equivalently `ω_k² = ω_cut² (k/N_ℰ)^{2/3}` and `1/ω_k² = ω_cut⁻² (N_ℰ/k)^{2/3}`.

**Completing the square (Eq. 4).** The bilinear coupling `L_int = c x Σ q^k` is absorbed per bath mode by shifting
`q^k → q^k − (c/ω_k²)x`, leaving a residual `+ (c²/2ω_k²)x²` that renormalizes the system frequency:

`−½ω_k²(q^k)² + c x q^k = −½ω_k²(q^k − (c/ω_k²)x)² + (c²/2ω_k²)x²`.

**Frequency renormalization (Eqs. 5–7).** Summing the residuals shifts the bare frequency to
`ω_r² = ω_b² − c² Σ_k 1/ω_k²` (Eq. 5). The coupling constant is fixed at finite `N_ℰ` by
`c² = (4γ/π) ω_cut³ / (Σ_k (N_ℰ/k)^{2/3})` (Eq. 7) — chosen **precisely** so that the reciprocal-frequency sum
cancels exactly and the renormalization collapses to the closed form `ω_r² = ω_b² − 4γω_cut/π` (Eq. 6), for
*every* `N_ℰ`. The dissipation coefficient `γ` here is the same `γ` that sets the Caldeira–Leggett decoherence
rate `∝ γ/β = γT` (`ComplexSaddleDecoherence.gammaOffdiagLinear`,
`CaldeiraLeggettDecoherence.caldeiraLeggett_fluctuation_dissipation`).

* **§A — the Ohmic spectrum (Eqs. 2–3).** `ohmicFreq`, `ohmicFreq_sq`, `ohmicFreq_inv_sq`.
* **§B — completing the square (Eq. 4).** `completeSquare_mode`.
* **§C — the reciprocal-frequency sum (bridge to §D).** `ohmicReciprocalSum`, `ohmicShapeSum`,
  **`ohmicReciprocalSum_eq`** (`Σ 1/ω_k² = ω_cut⁻² Σ (N_ℰ/k)^{2/3}`).
* **§D — coupling and frequency renormalization (Eqs. 5–7).** `couplingSq` (Eq. 7); **`coupling_reciprocalSum_cancel`**
  (`c² Σ 1/ω_k² = 4γω_cut/π`, the exact cancellation); `renormFreqSq` (Eq. 5); **`renormFreqSq_eq_closed`** (Eq. 6).
* **§E — Sabio–Sols displaced-oscillator chain.** The counterterm cancels the static square-completion
  residual; `displacedOscillatorRenormalizedHopping = t exp(-B)` is positive and no larger than the bare
  hopping for finite nonnegative dressing; the paper's zero-temperature Eqs. 11–12 and finite-temperature
  scale Eq. 15 are represented with their exact algebraic consequences.

**Honest layering.** Exact `ring` / `field_simp` / `Real.rpow` identities for the Ohmic frequencies, the
completing-the-square shift, and the coupling-constant cancellation. The discretized real-time action (Eq. 8), the
imaginary-time bath action (Eq. 12), the Gaussian path integral over `Dx Dq Dq̃` and the resulting complex saddle
`X̄ = M⁻¹C` with `det M` prefactor (Eqs. 13–21) are the paper's calculation, recorded not re-derived; the
closed-form model-setup identities they rest on are formalized here. The Ohmic condition `(dg/dκ)⁻¹ ∝ g²` (Eq. 2)
selecting `g(κ) ∝ κ^{1/3}` — a differential-equation statement — and the `N_ℰ → ∞` limit are not formalized.

## References

* J. Nishimura, H. Watanabe, arXiv:2408.16627, Eqs. 1–8. Companion to `ComplexSaddleDecoherence` (the
  decoherence structure of the same model).
* J. Sabio, F. Sols, *Variational approach to the Caldeira–Leggett model*, Physica E **42**
  (2010) 378–382, Eqs. 1–15.


-/

set_option autoImplicit false

open scoped Real BigOperators
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization


/-- The **Ohmic bath mode frequency** `ω_k = ω_cut (k/N_ℰ)^{1/3}` (Eq. 3) — the spectrum reproducing the Ohmic
spectral density (`(dg/dκ)⁻¹ ∝ ω² = g²`, Eq. 2, forces `g(κ) ∝ κ^{1/3}`). -/
noncomputable def ohmicFreq (ωcut NE k : ℝ) : ℝ := ωcut * (k / NE) ^ ((1 : ℝ) / 3)

/-- **The squared Ohmic frequency** `ω_k² = ω_cut² (k/N_ℰ)^{2/3}`. -/
lemma ohmicFreq_sq (ωcut NE k : ℝ) (h : 0 ≤ k / NE) :
    ohmicFreq ωcut NE k ^ 2 = ωcut ^ 2 * (k / NE) ^ ((2 : ℝ) / 3) := by
  rw [ohmicFreq, mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((k / NE) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul h]
  norm_num

/-- **The reciprocal squared Ohmic frequency** `1/ω_k² = ω_cut⁻² (N_ℰ/k)^{2/3}` — the summand of the frequency
renormalization (Eq. 5), rewritten with the ratio inverted. -/
lemma ohmicFreq_inv_sq (ωcut NE k : ℝ) (hk : 0 < k) (hNE : 0 < NE) :
    1 / ohmicFreq ωcut NE k ^ 2 = (1 / ωcut ^ 2) * (NE / k) ^ ((2 : ℝ) / 3) := by
  have hkNE : 0 < k / NE := div_pos hk hNE
  rw [ohmicFreq_sq ωcut NE k hkNE.le, one_div, mul_inv]
  congr 1
  · rw [one_div]
  · rw [← Real.inv_rpow hkNE.le, inv_div]


/-- **Completing the square per bath mode (Eq. 4)** — the bilinear coupling `c x q^k` in
`L = −½ω_k²(q^k)² + c x q^k` is absorbed by the shift `q^k → q^k − (c/ω_k²)x`, leaving the residual
`(c²/2ω_k²)x²` that renormalizes the system frequency (Eq. 5). -/
lemma completeSquare_mode (ωk c x q : ℝ) (hωk : ωk ≠ 0) :
    -(1 / 2) * ωk ^ 2 * q ^ 2 + c * x * q
      = -(1 / 2) * ωk ^ 2 * (q - (c / ωk ^ 2) * x) ^ 2 + c ^ 2 * x ^ 2 / (2 * ωk ^ 2) := by
  field_simp
  ring


/-- The **reciprocal-frequency sum** `Σ_{k=1}^{n} 1/ω_k²` appearing in the frequency renormalization (Eq. 5). -/
noncomputable def ohmicReciprocalSum (ωcut NE : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / ohmicFreq ωcut NE (k : ℝ) ^ 2

/-- The **Ohmic shape sum** `Σ_{k=1}^{n} (N_ℰ/k)^{2/3}` — the frequency-independent factor whose inverse fixes the
coupling constant (Eq. 7). -/
noncomputable def ohmicShapeSum (NE : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (NE / (k : ℝ)) ^ ((2 : ℝ) / 3)

/-- **The reciprocal-frequency sum factors** `Σ 1/ω_k² = ω_cut⁻² Σ (N_ℰ/k)^{2/3}` — the `ω_cut` scale pulls out,
leaving the pure shape sum. -/
lemma ohmicReciprocalSum_eq (ωcut NE : ℝ) (n : ℕ) (hNE : 0 < NE) :
    ohmicReciprocalSum ωcut NE n = (1 / ωcut ^ 2) * ohmicShapeSum NE n := by
  rw [ohmicReciprocalSum, ohmicShapeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk1
  exact ohmicFreq_inv_sq ωcut NE (k : ℝ) hkpos hNE


/-- The **coupling constant** `c² = (4γ/π) ω_cut³ / (Σ (N_ℰ/k)^{2/3})` (Eq. 7) — fixed at finite `N_ℰ` so the
frequency renormalization collapses to its `N_ℰ`-independent closed form (Eq. 6). -/
noncomputable def couplingSq (γ ωcut S : ℝ) : ℝ := 4 * γ / π * ωcut ^ 3 * S⁻¹

/-- **The coupling constant is chosen so the reciprocal-frequency sum cancels exactly (Eqs. 5–7)**
`c² Σ 1/ω_k² = 4γω_cut/π` — the finite bath sum `Σ (N_ℰ/k)^{2/3}` divides out completely, for *every* `N_ℰ`.
This is the exact identity behind the `N_ℰ`-independent renormalized frequency (Eq. 6). -/
lemma coupling_reciprocalSum_cancel (γ ωcut NE : ℝ) (n : ℕ)
    (hωcut : ωcut ≠ 0) (hNE : 0 < NE) (hS : ohmicShapeSum NE n ≠ 0) :
    couplingSq γ ωcut (ohmicShapeSum NE n) * ohmicReciprocalSum ωcut NE n = 4 * γ * ωcut / π := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [ohmicReciprocalSum_eq ωcut NE n hNE, couplingSq]
  field_simp

/-- The **renormalized system frequency** `ω_r² = ω_b² − c² Σ 1/ω_k²` (Eq. 5) — the bare frequency `ω_b` shifted by
the environment via the completing-the-square residuals (`completeSquare_mode`). -/
noncomputable def renormFreqSq (ωb γ ωcut NE : ℝ) (n : ℕ) : ℝ :=
  ωb ^ 2 - couplingSq γ ωcut (ohmicShapeSum NE n) * ohmicReciprocalSum ωcut NE n

/-- **The renormalized frequency in closed form (Eq. 6)** `ω_r² = ω_b² − 4γω_cut/π` — independent of `N_ℰ` and of
the bath shape sum, by the exact cancellation `coupling_reciprocalSum_cancel`. The shift `∝ γω_cut` is set by the
dissipation coefficient `γ` (the same `γ` driving Caldeira–Leggett decoherence). -/
lemma renormFreqSq_eq_closed (ωb γ ωcut NE : ℝ) (n : ℕ)
    (hωcut : ωcut ≠ 0) (hNE : 0 < NE) (hS : ohmicShapeSum NE n ≠ 0) :
    renormFreqSq ωb γ ωcut NE n = ωb ^ 2 - 4 * γ * ωcut / π := by
  rw [renormFreqSq, coupling_reciprocalSum_cancel γ ωcut NE n hωcut hNE hS]

/-! ## E. Sabio–Sols displaced-oscillator variational chain -/

/-- **[Counterterm cancellation]** The Caldeira–Leggett counterterm removes exactly the
static quadratic residual generated by displacing one bath mode. This is the scalar algebraic
content behind the homogeneous-dissipation Hamiltonian in Sabio–Sols Eqs. 1–2. -/
lemma completeSquare_mode_with_counterterm (ωk c x q : ℝ) (hωk : ωk ≠ 0) :
    -(1 / 2) * ωk ^ 2 * q ^ 2 + c * x * q - c ^ 2 * x ^ 2 / (2 * ωk ^ 2)
      = -(1 / 2) * ωk ^ 2 * (q - (c / ωk ^ 2) * x) ^ 2 := by
  rw [completeSquare_mode ωk c x q hωk]
  ring

/-- The displaced-oscillator renormalized hopping `t_ren = t exp(-B)` from Sabio–Sols Eq. 9,
where `B` is the nonnegative thermal bath-dressing exponent. -/
noncomputable def displacedOscillatorRenormalizedHopping (t B : ℝ) : ℝ :=
  t * Real.exp (-B)

/-- Finite oscillator dressing preserves strictly positive hopping. -/
lemma displacedOscillatorRenormalizedHopping_pos (t B : ℝ) (ht : 0 < t) :
    0 < displacedOscillatorRenormalizedHopping t B := by
  unfold displacedOscillatorRenormalizedHopping
  exact mul_pos ht (Real.exp_pos _)

/-- A nonnegative bath exponent can only reduce a nonnegative bare hopping:
`0 ≤ t_ren ≤ t`. -/
lemma displacedOscillatorRenormalizedHopping_mem_Icc (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) :
    displacedOscillatorRenormalizedHopping t B ∈ Set.Icc 0 t := by
  constructor
  · exact mul_nonneg ht (Real.exp_pos _).le
  · unfold displacedOscillatorRenormalizedHopping
    exact mul_le_of_le_one_right ht (by simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hB))

/-- For every finite real dressing exponent, `t_ren = 0` iff the bare hopping was already zero. -/
lemma displacedOscillatorRenormalizedHopping_eq_zero_iff (t B : ℝ) :
    displacedOscillatorRenormalizedHopping t B = 0 ↔ t = 0 := by
  simp [displacedOscillatorRenormalizedHopping, Real.exp_ne_zero]

/-- **[Honest coherent/incoherent boundary]** A finite scalar displacement exponent cannot by itself
produce the paper's incoherent `t_ren = 0` phase from nonzero bare hopping. Such a phase requires a
singular/infinite-dressing limit or loss of the nontrivial self-consistent variational branch. -/
lemma finite_displacement_does_not_create_zero_hopping (t B : ℝ) (ht : t ≠ 0) :
    displacedOscillatorRenormalizedHopping t B ≠ 0 := by
  exact (displacedOscillatorRenormalizedHopping_eq_zero_iff t B).not.mpr ht

/-- The Sabio–Sols dressing applied directly to Physlib's existing tight-binding-chain carrier. -/
noncomputable def sabioTightBindingDressedHopping (T : CondensedMatter.TightBindingChain) (B : ℝ) : ℝ :=
  displacedOscillatorRenormalizedHopping T.t B

/-- Positive bare hopping in the repository's tight-binding chain remains positive under finite
displaced-oscillator dressing. -/
lemma sabioTightBindingDressedHopping_pos (T : CondensedMatter.TightBindingChain) (B : ℝ)
    (ht : 0 < T.t) : 0 < sabioTightBindingDressedHopping T B :=
  displacedOscillatorRenormalizedHopping_pos T.t B ht

/-- Sabio–Sols Eq. 11 at zero temperature and unit cutoff:
`t_ren = t (1 + 1/s₀)^{-α} exp(α/(s₀+1))`.

This is a parameter carrier for the paper's self-consistency equation; existence or uniqueness of
a fixed point `s₀(t_ren)` is deliberately not built into the definition. -/
noncomputable def sabioZeroTempRenormalizedHopping (t α s0 : ℝ) : ℝ :=
  t * Real.rpow (1 + 1 / s0) (-α) * Real.exp (α / (s0 + 1))

/-- At zero bath coupling, the zero-temperature variational hopping reduces exactly to the bare hopping. -/
lemma sabioZeroTempRenormalizedHopping_zero_coupling (t s0 : ℝ) :
    sabioZeroTempRenormalizedHopping t 0 s0 = t := by
  simp [sabioZeroTempRenormalizedHopping]

/-- Positive bare hopping and positive `s₀` give a positive nontrivial zero-temperature branch. -/
lemma sabioZeroTempRenormalizedHopping_pos (t α s0 : ℝ) (ht : 0 < t) (hs0 : 0 < s0) :
    0 < sabioZeroTempRenormalizedHopping t α s0 := by
  unfold sabioZeroTempRenormalizedHopping
  have hbase : 0 < 1 + 1 / s0 := by positivity
  exact mul_pos (mul_pos ht (Real.rpow_pos_of_pos hbase _)) (Real.exp_pos _)

/-- Sabio–Sols Eq. 12 at zero temperature and unit cutoff: `g = 2αs₀/(s₀+1)`. -/
noncomputable def sabioZeroTempPotential (α s0 : ℝ) : ℝ := 2 * α * s0 / (s0 + 1)

/-- The bath-induced variational confinement vanishes at zero coupling. -/
lemma sabioZeroTempPotential_zero_coupling (s0 : ℝ) : sabioZeroTempPotential 0 s0 = 0 := by
  simp [sabioZeroTempPotential]

/-- For nonnegative coupling and response scale, the induced quadratic potential is nonnegative. -/
lemma sabioZeroTempPotential_nonneg (α s0 : ℝ) (hα : 0 ≤ α) (hs0 : 0 ≤ s0) :
    0 ≤ sabioZeroTempPotential α s0 := by
  unfold sabioZeroTempPotential
  positivity

/-- For positive coupling and nonnegative finite `s₀`, Eq. 12 gives the strict bound `g < 2α`. -/
lemma sabioZeroTempPotential_lt_two_mul (α s0 : ℝ) (hα : 0 < α) (hs0 : 0 ≤ s0) :
    sabioZeroTempPotential α s0 < 2 * α := by
  unfold sabioZeroTempPotential
  rw [div_lt_iff₀ (by linarith : 0 < s0 + 1)]
  nlinarith

/-- The coordinate of site `m` relative to the midpoint of an `M`-site open chain,
`q_m = m - (M-1)/2`, in lattice-spacing units. Unlike the repository's periodic-chain
Hamiltonian, this scalar carrier records the open-boundary geometry used by Sabio–Sols. -/
noncomputable def sabioCenteredSiteCoordinate (M m : ℕ) : ℝ :=
  (m : ℝ) - ((M : ℝ) - 1) / 2

/-- An odd chain with `M = 2n+1` has a unique lattice site `m=n` at the geometric center. -/
lemma sabioCenteredSiteCoordinate_odd_center (n : ℕ) :
    sabioCenteredSiteCoordinate (2 * n + 1) n = 0 := by
  simp [sabioCenteredSiteCoordinate]

/-- An even chain with `M = 2n`, `n>0`, has its left central site at `q=-1/2`. -/
lemma sabioCenteredSiteCoordinate_even_left (n : ℕ) (hn : 0 < n) :
    sabioCenteredSiteCoordinate (2 * n) (n - 1) = -(1 / 2 : ℝ) := by
  rw [sabioCenteredSiteCoordinate, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
  push_cast
  ring

/-- The right central site of a nonempty even chain lies at `q=+1/2`. -/
lemma sabioCenteredSiteCoordinate_even_right (n : ℕ) (hn : 0 < n) :
    sabioCenteredSiteCoordinate (2 * n) n = (1 / 2 : ℝ) := by
  simp [sabioCenteredSiteCoordinate]
  ring

/-- The induced quadratic potential `g q_m²` on the open-chain coordinate carrier. -/
noncomputable def sabioCenteredQuadraticPotential (g : ℝ) (M m : ℕ) : ℝ :=
  g * sabioCenteredSiteCoordinate M m ^ 2

/-- On an odd chain the central site has zero induced quadratic potential. -/
lemma sabioCenteredQuadraticPotential_odd_center (g : ℝ) (n : ℕ) :
    sabioCenteredQuadraticPotential g (2 * n + 1) n = 0 := by
  simp [sabioCenteredQuadraticPotential, sabioCenteredSiteCoordinate_odd_center]

/-- On an even chain the two central sites are degenerate at potential `g/4`. -/
lemma sabioCenteredQuadraticPotential_even_pair (g : ℝ) (n : ℕ) (hn : 0 < n) :
    sabioCenteredQuadraticPotential g (2 * n) (n - 1) = g / 4 ∧
      sabioCenteredQuadraticPotential g (2 * n) n = g / 4 := by
  rw [sabioCenteredQuadraticPotential, sabioCenteredQuadraticPotential,
    sabioCenteredSiteCoordinate_even_left n hn, sabioCenteredSiteCoordinate_even_right n hn]
  constructor <;> ring

/-! ### The actual finite open-boundary Hamiltonian and its parity symmetry -/

/-- Two sites are adjacent in an open chain exactly when their natural-number labels differ by one.
There is no modular wraparound edge between the first and last sites. -/
def sabioOpenNeighbor {N : ℕ} (i j : Fin N) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

instance sabioOpenNeighborDecidable {N : ℕ} (i j : Fin N) : Decidable (sabioOpenNeighbor i j) :=
  by
    unfold sabioOpenNeighbor
    infer_instance

/-- Open-chain adjacency is symmetric. -/
lemma sabioOpenNeighbor_symm {N : ℕ} (i j : Fin N) :
    sabioOpenNeighbor i j ↔ sabioOpenNeighbor j i := by
  simp only [sabioOpenNeighbor, or_comm]

/-- **[Sabio–Sols finite open-chain Hamiltonian]** The Hermitian matrix with diagonal
`E₀ + g qᵢ²`, nearest-neighbor entry `-t_ren`, and zero otherwise. It reuses the site type and
physical parameters of `CondensedMatter.TightBindingChain` while replacing its periodic edge by
the paper's open-boundary adjacency. -/
noncomputable def sabioOpenChainHamiltonianMatrix (T : CondensedMatter.TightBindingChain)
    (tRen g : ℝ) : Matrix (Fin T.N) (Fin T.N) ℂ := fun i j =>
  if i = j then
    (T.E0 + g * sabioCenteredSiteCoordinate T.N i.val ^ 2 : ℝ)
  else if sabioOpenNeighbor i j then -(tRen : ℂ) else 0

/-- The open-chain Hamiltonian's diagonal is exactly the onsite energy plus induced quadratic
confinement. -/
lemma sabioOpenChainHamiltonianMatrix_diagonal (T : CondensedMatter.TightBindingChain)
    (tRen g : ℝ) (i : Fin T.N) :
    sabioOpenChainHamiltonianMatrix T tRen g i i =
      (T.E0 + g * sabioCenteredSiteCoordinate T.N i.val ^ 2 : ℝ) := by
  simp [sabioOpenChainHamiltonianMatrix]

/-- Every genuine open-chain nearest-neighbor matrix element is `-t_ren`. -/
lemma sabioOpenChainHamiltonianMatrix_neighbor (T : CondensedMatter.TightBindingChain)
    (tRen g : ℝ) (i j : Fin T.N) (hij : i ≠ j) (hn : sabioOpenNeighbor i j) :
    sabioOpenChainHamiltonianMatrix T tRen g i j = -(tRen : ℂ) := by
  simp [sabioOpenChainHamiltonianMatrix, hij, hn]

/-- **[Hermiticity]** The Sabio–Sols open-chain Hamiltonian is Hermitian for all real parameters. -/
lemma sabioOpenChainHamiltonianMatrix_isHermitian (T : CondensedMatter.TightBindingChain)
    (tRen g : ℝ) : (sabioOpenChainHamiltonianMatrix T tRen g).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  by_cases hij : i = j
  · subst j
    simp [sabioOpenChainHamiltonianMatrix]
  · have hji : j ≠ i := Ne.symm hij
    by_cases hn : sabioOpenNeighbor i j
    · have hnj : sabioOpenNeighbor j i := (sabioOpenNeighbor_symm i j).mp hn
      simp [sabioOpenChainHamiltonianMatrix, hij, hji, hn, hnj]
    · have hnj : ¬sabioOpenNeighbor j i :=
        fun h => hn ((sabioOpenNeighbor_symm i j).mpr h)
      simp [sabioOpenChainHamiltonianMatrix, hij, hji, hn, hnj]

/-- Reflection of an open chain about its midpoint, `i ↦ N-1-i`. -/
def sabioOpenChainReflection (T : CondensedMatter.TightBindingChain) (i : Fin T.N) : Fin T.N :=
  ⟨T.N - 1 - i.val, by
    have hN : 0 < T.N := Nat.pos_of_ne_zero (NeZero.ne T.N)
    omega⟩

/-- Open-chain reflection is an involution. -/
lemma sabioOpenChainReflection_involutive (T : CondensedMatter.TightBindingChain) (i : Fin T.N) :
    sabioOpenChainReflection T (sabioOpenChainReflection T i) = i := by
  apply Fin.ext
  simp only [sabioOpenChainReflection, Fin.val_mk]
  have hN : 0 < T.N := Nat.pos_of_ne_zero (NeZero.ne T.N)
  omega

/-- Open-chain reflection is injective. -/
lemma sabioOpenChainReflection_injective (T : CondensedMatter.TightBindingChain) :
    Function.Injective (sabioOpenChainReflection T) := by
  intro i j h
  have h' := congrArg (sabioOpenChainReflection T) h
  simpa only [sabioOpenChainReflection_involutive] using h'

/-- Reflection negates the centered coordinate. -/
lemma sabioOpenChainReflection_coordinate (T : CondensedMatter.TightBindingChain)
    (i : Fin T.N) :
    sabioCenteredSiteCoordinate T.N (sabioOpenChainReflection T i).val =
      -sabioCenteredSiteCoordinate T.N i.val := by
  have hN : 0 < T.N := Nat.pos_of_ne_zero (NeZero.ne T.N)
  have hi : i.val ≤ T.N - 1 := by omega
  have h1 : 1 ≤ T.N := hN
  unfold sabioCenteredSiteCoordinate
  simp only [sabioOpenChainReflection, Fin.val_mk]
  rw [Nat.cast_sub hi, Nat.cast_sub h1]
  ring

/-- Reflection preserves open-chain nearest-neighbor adjacency. -/
lemma sabioOpenChainReflection_neighbor (T : CondensedMatter.TightBindingChain)
    (i j : Fin T.N) :
    sabioOpenNeighbor (sabioOpenChainReflection T i) (sabioOpenChainReflection T j) ↔
      sabioOpenNeighbor i j := by
  have hN : 0 < T.N := Nat.pos_of_ne_zero (NeZero.ne T.N)
  simp only [sabioOpenNeighbor, sabioOpenChainReflection, Fin.val_mk]
  constructor <;> omega

/-- **[Parity symmetry]** The full open-chain Hamiltonian kernel is invariant under simultaneous
reflection of both site indices. This proves the exact parity symmetry whose spontaneous breaking
is discussed for the localized even-chain phase. -/
lemma sabioOpenChainHamiltonianMatrix_reflection (T : CondensedMatter.TightBindingChain)
    (tRen g : ℝ) (i j : Fin T.N) :
    sabioOpenChainHamiltonianMatrix T tRen g (sabioOpenChainReflection T i)
        (sabioOpenChainReflection T j) =
      sabioOpenChainHamiltonianMatrix T tRen g i j := by
  by_cases hij : i = j
  · subst j
    simp only [sabioOpenChainHamiltonianMatrix, ↓reduceIte]
    rw [sabioOpenChainReflection_coordinate]
    ring
  · have hrne : sabioOpenChainReflection T i ≠ sabioOpenChainReflection T j :=
      fun h => hij (sabioOpenChainReflection_injective T h)
    by_cases hn : sabioOpenNeighbor i j
    · have hnr : sabioOpenNeighbor (sabioOpenChainReflection T i)
          (sabioOpenChainReflection T j) :=
        (sabioOpenChainReflection_neighbor T i j).mpr hn
      simp [sabioOpenChainHamiltonianMatrix, hrne, hij, hnr, hn]
    · have hnr : ¬sabioOpenNeighbor (sabioOpenChainReflection T i)
          (sabioOpenChainReflection T j) :=
        fun h => hn ((sabioOpenChainReflection_neighbor T i j).mp h)
      simp [sabioOpenChainHamiltonianMatrix, hrne, hij, hnr, hn]

/-! ### Parity-sector decomposition and Hamiltonian preservation -/

/-- The midpoint reflection packaged as an equivalence of the finite site type. -/
def sabioOpenChainReflectionEquiv (T : CondensedMatter.TightBindingChain) : Fin T.N ≃ Fin T.N where
  toFun := sabioOpenChainReflection T
  invFun := sabioOpenChainReflection T
  left_inv := sabioOpenChainReflection_involutive T
  right_inv := sabioOpenChainReflection_involutive T

/-- Reflection acting on a finite-chain state. -/
def sabioReflectState (T : CondensedMatter.TightBindingChain) (ψ : Fin T.N → ℂ) : Fin T.N → ℂ :=
  fun i => ψ (sabioOpenChainReflection T i)

/-- State reflection is an involution. -/
lemma sabioReflectState_involutive (T : CondensedMatter.TightBindingChain) (ψ : Fin T.N → ℂ) :
    sabioReflectState T (sabioReflectState T ψ) = ψ := by
  funext i
  simp [sabioReflectState, sabioOpenChainReflection_involutive]

/-- The even-parity projection `(ψ + Pψ)/2`. -/
noncomputable def sabioEvenParityPart (T : CondensedMatter.TightBindingChain)
    (ψ : Fin T.N → ℂ) : Fin T.N → ℂ := fun i => (ψ i + sabioReflectState T ψ i) / 2

/-- The odd-parity projection `(ψ - Pψ)/2`. -/
noncomputable def sabioOddParityPart (T : CondensedMatter.TightBindingChain)
    (ψ : Fin T.N → ℂ) : Fin T.N → ℂ := fun i => (ψ i - sabioReflectState T ψ i) / 2

/-- **[Parity decomposition]** Every finite open-chain state is exactly the sum of its even and
odd reflection sectors. -/
lemma sabioParity_decomposition (T : CondensedMatter.TightBindingChain) (ψ : Fin T.N → ℂ) :
    sabioEvenParityPart T ψ + sabioOddParityPart T ψ = ψ := by
  funext i
  simp only [Pi.add_apply, sabioEvenParityPart, sabioOddParityPart]
  ring

/-- The even component is a `+1` eigenstate of reflection. -/
lemma sabioReflectState_evenParityPart (T : CondensedMatter.TightBindingChain)
    (ψ : Fin T.N → ℂ) :
    sabioReflectState T (sabioEvenParityPart T ψ) = sabioEvenParityPart T ψ := by
  funext i
  simp only [sabioReflectState, sabioEvenParityPart]
  rw [sabioOpenChainReflection_involutive]
  ring

/-- The odd component is a `-1` eigenstate of reflection. -/
lemma sabioReflectState_oddParityPart (T : CondensedMatter.TightBindingChain)
    (ψ : Fin T.N → ℂ) :
    sabioReflectState T (sabioOddParityPart T ψ) = -sabioOddParityPart T ψ := by
  funext i
  simp only [sabioReflectState, sabioOddParityPart, Pi.neg_apply]
  rw [sabioOpenChainReflection_involutive]
  ring

/-- **[Hamiltonian commutes with parity]** Acting with the open-chain Hamiltonian after reflecting
a state equals reflecting the Hamiltonian-evolved state. The proof reindexes the finite matrix sum
by the reflection equivalence and uses kernel parity invariance. -/
lemma sabioOpenChainHamiltonianMatrix_reflectState (T : CondensedMatter.TightBindingChain)
    (tRen g : ℝ) (ψ : Fin T.N → ℂ) :
    Matrix.mulVec (sabioOpenChainHamiltonianMatrix T tRen g) (sabioReflectState T ψ) =
      sabioReflectState T (Matrix.mulVec (sabioOpenChainHamiltonianMatrix T tRen g) ψ) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, sabioReflectState]
  rw [← Equiv.sum_comp (sabioOpenChainReflectionEquiv T)
    (fun j => sabioOpenChainHamiltonianMatrix T tRen g (sabioOpenChainReflection T i) j * ψ j)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [sabioOpenChainReflectionEquiv, Equiv.coe_fn_mk]
  rw [sabioOpenChainHamiltonianMatrix_reflection]

/-- The open-chain Hamiltonian preserves the even-parity state sector. -/
lemma sabioOpenChainHamiltonianMatrix_preserves_even (T : CondensedMatter.TightBindingChain)
    (tRen g : ℝ) (ψ : Fin T.N → ℂ) (hψ : sabioReflectState T ψ = ψ) :
    sabioReflectState T (Matrix.mulVec (sabioOpenChainHamiltonianMatrix T tRen g) ψ) =
      Matrix.mulVec (sabioOpenChainHamiltonianMatrix T tRen g) ψ := by
  rw [← sabioOpenChainHamiltonianMatrix_reflectState, hψ]

/-- The open-chain Hamiltonian preserves the odd-parity state sector. -/
lemma sabioOpenChainHamiltonianMatrix_preserves_odd (T : CondensedMatter.TightBindingChain)
    (tRen g : ℝ) (ψ : Fin T.N → ℂ) (hψ : sabioReflectState T ψ = -ψ) :
    sabioReflectState T (Matrix.mulVec (sabioOpenChainHamiltonianMatrix T tRen g) ψ) =
      -Matrix.mulVec (sabioOpenChainHamiltonianMatrix T tRen g) ψ := by
  rw [← sabioOpenChainHamiltonianMatrix_reflectState, hψ]
  rw [Matrix.mulVec_neg]

/-! ### Conditional self-consistent hopping -/

/-- The Sabio displaced-oscillator self-consistency map `t_ren ↦ t exp(-B(t_ren))`.
The bath functional `B` is kept explicit so that concrete spectral-density models can instantiate
the same fixed-point theorem without duplicating its analysis. -/
noncomputable def sabioHoppingSelfConsistencyMap (t : ℝ) (B : ℝ → ℝ) : ℝ → ℝ :=
  fun tRen => displacedOscillatorRenormalizedHopping t (B tRen)

/-- **[Conditional self-consistency]** If the Sabio hopping map is a contraction, it has a unique
renormalized hopping. This isolates the analytical obligation on the bath dressing from the exact
fixed-point conclusion. -/
theorem sabioHoppingSelfConsistency_unique (t : ℝ) (B : ℝ → ℝ) (K : NNReal)
    (hcontract : ContractingWith K (sabioHoppingSelfConsistencyMap t B)) :
    ∃! tRen : ℝ, sabioHoppingSelfConsistencyMap t B tRen = tRen := by
  refine ⟨hcontract.fixedPoint, hcontract.fixedPoint_isFixedPt, fun y hy => ?_⟩
  exact hcontract.fixedPoint_unique hy

/-- Every Picard iteration of a contracting Sabio hopping map converges to its unique
self-consistent renormalized hopping. -/
theorem sabioHoppingSelfConsistency_iterates_tendsto (t : ℝ) (B : ℝ → ℝ) (K : NNReal)
    (hcontract : ContractingWith K (sabioHoppingSelfConsistencyMap t B)) (seed : ℝ) :
    Filter.Tendsto
      (fun n => (sabioHoppingSelfConsistencyMap t B)^[n] seed)
      Filter.atTop
      (nhds hcontract.fixedPoint) :=
  hcontract.tendsto_iterate_fixedPoint seed

/-- Quantitative a-priori error bound for the self-consistency iteration. -/
theorem sabioHoppingSelfConsistency_iterate_dist_le (t : ℝ) (B : ℝ → ℝ) (K : NNReal)
    (hcontract : ContractingWith K (sabioHoppingSelfConsistencyMap t B)) (seed : ℝ) (n : ℕ) :
    dist ((sabioHoppingSelfConsistencyMap t B)^[n] seed) hcontract.fixedPoint ≤
      dist seed (sabioHoppingSelfConsistencyMap t B seed) * (K : ℝ) ^ n / (1 - K) :=
  hcontract.apriori_dist_iterate_fixedPoint_le seed n

/-- The finite-temperature critical scale in Sabio–Sols Eq. 15,
`T* ∼ sqrt(t_ren /(α Σ_m (m-m₀)²))`. The definition records the right-hand scale only;
the paper's asymptotic `∼` is not promoted to an exact phase-transition equality. -/
noncomputable def sabioCriticalTemperatureScale (tRen α centeredSquareSum : ℝ) : ℝ :=
  Real.sqrt (tRen / (α * centeredSquareSum))

/-- The square of the critical-temperature scale recovers the Eq. 15 radicand when it is nonnegative. -/
lemma sabioCriticalTemperatureScale_sq (tRen α centeredSquareSum : ℝ)
    (h : 0 ≤ tRen / (α * centeredSquareSum)) :
    sabioCriticalTemperatureScale tRen α centeredSquareSum ^ 2 =
      tRen / (α * centeredSquareSum) := by
  exact Real.sq_sqrt h

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach completeSquare_mode_with_counterterm where
  formalizes @ "claim:sabio-caldeira-leggett-counterterm-cancels-static-displacement-residual",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:sabio-sols-2010-eqs-1-2",
  caveat @ "claim:single-mode-square-completion-not-the-continuum-bath-unitary-equivalence"

zil attach displacedOscillatorRenormalizedHopping_mem_Icc where
  formalizes @ "claim:sabio-finite-nonnegative-bath-dressing-reduces-nonnegative-tight-binding-hopping",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-eq-9",
  caveat @ "claim:scalar-dressing-bound-does-not-solve-the-self-consistent-bath-integral"

zil attach finite_displacement_does_not_create_zero_hopping where
  formalizes @ "claim:sabio-finite-displacement-cannot-create-zero-renormalized-hopping-from-nonzero-bare-hopping",
  supported_by @ "paper:sabio-sols-2010",
  epistemic_status @ "risky",
  requires @ "claim:sabio-finite-nonnegative-bath-dressing-reduces-nonnegative-tight-binding-hopping",
  caveat @ "claim:incoherent-phase-requires-singular-limit-or-loss-of-nontrivial-self-consistent-branch"

zil attach sabioTightBindingDressedHopping_pos where
  formalizes @ "claim:sabio-displaced-oscillator-dressing-acts-on-existing-physlib-tight-binding-chain",
  supported_by @ "paper:sabio-sols-2010",
  epistemic_status @ "risky",
  caveat @ "claim:existing-periodic-chain-carrier-does-not-supply-the-paper-open-boundary-condition"

zil attach sabioZeroTempRenormalizedHopping_zero_coupling where
  formalizes @ "claim:sabio-zero-temperature-hopping-recovers-bare-hopping-at-zero-bath-coupling",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:sabio-sols-2010-eq-11",
  caveat @ "claim:zero-coupling-limit-does-not-prove-existence-or-uniqueness-of-a-self-consistent-solution"

zil attach sabioZeroTempPotential_nonneg where
  formalizes @ "claim:sabio-zero-temperature-induced-quadratic-potential-is-nonnegative",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-eq-12",
  caveat @ "claim:nonnegativity-does-not-establish-the-even-odd-chain-localization-phase-diagram"

zil attach sabioZeroTempPotential_lt_two_mul where
  formalizes @ "claim:sabio-zero-temperature-induced-potential-is-strictly-bounded-by-two-alpha",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-eq-12",
  caveat @ "claim:finite-parameter-bound-does-not-identify-the-critical-coupling"

zil attach sabioCenteredSiteCoordinate_odd_center where
  formalizes @ "claim:sabio-odd-open-chain-has-one-site-at-the-geometric-center",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-sections-3-4",
  caveat @ "claim:exact-open-chain-coordinate-geometry-not-a-proof-of-the-localization-phase-transition"

zil attach sabioCenteredQuadraticPotential_even_pair where
  formalizes @ "claim:sabio-even-open-chain-central-pair-is-symmetric-and-quadratically-degenerate",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-sections-3-4",
  caveat @ "claim:central-pair-degeneracy-does-not-prove-spontaneous-parity-breaking-or-critical-alpha-equals-one"

zil attach sabioOpenChainHamiltonianMatrix_isHermitian where
  formalizes @ "claim:sabio-finite-open-boundary-tight-binding-plus-quadratic-confinement-hamiltonian-is-hermitian",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-eqs-1-4",
  caveat @ "claim:finite-matrix-construction-not-the-system-plus-infinite-bosonic-bath-hamiltonian"

zil attach sabioOpenChainHamiltonianMatrix_reflection where
  formalizes @ "claim:sabio-open-chain-effective-hamiltonian-has-exact-midpoint-parity-symmetry",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-sections-2-4",
  caveat @ "claim:hamiltonian-parity-symmetry-does-not-by-itself-prove-spontaneous-parity-breaking"

zil attach sabioParity_decomposition where
  formalizes @ "claim:sabio-every-finite-open-chain-state-splits-into-even-and-odd-reflection-sectors",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-sections-3-4",
  caveat @ "claim:algebraic-parity-decomposition-does-not-prove-degeneracy-or-spontaneous-symmetry-breaking"

zil attach sabioOpenChainHamiltonianMatrix_preserves_even where
  formalizes @ "claim:sabio-open-chain-hamiltonian-preserves-the-even-parity-sector",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-sections-3-4",
  caveat @ "claim:sector-invariance-does-not-compute-the-even-sector-spectrum"

zil attach sabioOpenChainHamiltonianMatrix_preserves_odd where
  formalizes @ "claim:sabio-open-chain-hamiltonian-preserves-the-odd-parity-sector",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-sections-3-4",
  caveat @ "claim:sector-invariance-does-not-compute-the-odd-sector-spectrum"

zil attach sabioHoppingSelfConsistency_unique where
  formalizes @ "claim:sabio-contracting-bath-dressing-has-a-unique-self-consistent-renormalized-hopping",
  epistemic_status @ "risky",
  supported_by @ "paper:sabio-sols-2010-eqs-9-12",
  caveat @ "claim:conditional-on-contractivity-and-does-not-assert-that-every-ohmic-bath-functional-contracts"

zil attach sabioHoppingSelfConsistency_iterates_tendsto where
  formalizes @ "claim:sabio-contracting-hopping-iteration-converges-to-the-self-consistent-branch",
  supported_by @ "paper:sabio-sols-2010",
  epistemic_status @ "risky",
  requires @ "claim:sabio-contracting-bath-dressing-has-a-unique-self-consistent-renormalized-hopping",
  caveat @ "claim:convergence-is-conditional-and-does-not-identify-the-paper-critical-coupling"

zil attach sabioCriticalTemperatureScale_sq where
  formalizes @ "claim:sabio-finite-temperature-critical-scale-squares-to-the-eq-15-radicand",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:sabio-sols-2010-eq-15",
  caveat @ "claim:the-paper-asymptotic-scale-is-not-promoted-to-an-exact-critical-temperature-law"

zil_file_contract physlib.caldeiraLeggettSabioVariational where
  promises "Sabio-Sols displaced-oscillator variational structure on existing Physlib carriers: exact counterterm cancellation, finite hopping attenuation and its honest nonzero boundary, zero-temperature hopping and confinement identities, and the finite-temperature Eq. 15 scale, backed by the finite diagonal Bogoliubov-Feynman theorem."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy.finite_bogoliubov_feynman_bound",
    "lean:CondensedMatter.TightBindingChain",
    "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization.completeSquare_mode"
  ]
  forbids_substitutes [
    "claiming the finite diagonal variational bound is the full noncommutative trace inequality",
    "claiming the scalar self-consistency carriers prove the numerical even-odd phase diagram",
    "claiming an infinite Ohmic bath or thermodynamic limit from finite parameters",
    "promoting the Eq. 15 asymptotic scale to an exact transition temperature",
    "claiming the existing periodic tight-binding carrier has the paper's open boundary condition"
  ]
  witnessed_by [
    completeSquare_mode_with_counterterm,
    displacedOscillatorRenormalizedHopping_mem_Icc,
    finite_displacement_does_not_create_zero_hopping,
    sabioTightBindingDressedHopping_pos,
    sabioZeroTempRenormalizedHopping_zero_coupling,
    sabioZeroTempPotential_nonneg,
    sabioZeroTempPotential_lt_two_mul,
    sabioCenteredSiteCoordinate_odd_center,
    sabioCenteredQuadraticPotential_even_pair,
    sabioOpenChainHamiltonianMatrix_isHermitian,
    sabioOpenChainHamiltonianMatrix_reflection,
    sabioParity_decomposition,
    sabioOpenChainHamiltonianMatrix_preserves_even,
    sabioOpenChainHamiltonianMatrix_preserves_odd,
    sabioHoppingSelfConsistency_unique,
    sabioHoppingSelfConsistency_iterates_tendsto,
    sabioCriticalTemperatureScale_sq
  ]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

meta import Zil

/-!
# The Caldeira–Leggett decoherence functional: Gaussian thermal-bath decoherence as entropic damping

The Caldeira–Leggett model (Dowker–Halliwell §IV–V, Phys. Rev. D **46** (1992) 1580): a distinguished harmonic
oscillator coupled to a thermal bath of oscillators. Tracing out the bath in the Fokker–Planck (high-temperature)
limit gives an influence functional `F[x,y] = exp(−φ[x,y])` whose **decoherence exponent** (Eqs. 4.23/4.25) is

`φ[x,y] = 2MγkT ∫₀^τ (x(t) − y(t))² dt`,

the imaginary part of the effective action. In the decoherence functional `D([α],[α']) ∝ exp(iS̄ − φ)`, this `φ`
is the term that **suppresses the off-diagonal** `ξ = x − y ≠ 0` elements — the mechanism of decoherence.

**Directly on entropic time.** `φ` *is* the entropic (imaginary) action: `φ = S_I/ℏ` in the sense of
`PathIntegral.ComplexActionPathIntegralWeight` (`|weight| = exp(−S_I/ℏ) = kuikenWeight`), so the modulus of the
Caldeira–Leggett decoherence functional is the **entropic damping** `|D| = exp(−φ)` — the same imaginary-action /
entropy-production sector that drives the arrow of time in `DecoherenceFunctionalSorkinJohnston` and the
Snoke H-theorem. Decoherence here is entropy production made explicit: `φ ≥ 0`, vanishing exactly on the diagonal
`x = y`, growing with path separation, at a **fluctuation–dissipation** rate `∝ γT` (dissipation × temperature).

For a sustained path separation `ξ = x − y` over time `τ` (a single Gaussian slit), `∫ξ² dt = ξ²τ`, and
`caldeiraLeggettDecoherence` collects the closed-form exponent `2MγkTτ ξ²`.

* **§A — the decoherence/entropic action.** `caldeiraLeggettDecoherence = 2MγkTτ ξ²`;
  **`caldeiraLeggettDecoherence_nonneg`**, **`caldeiraLeggettDecoherence_eq_zero_iff`** (`= 0 ↔ x = y`),
  **`caldeiraLeggett_fluctuation_dissipation`** (`= 2MkT·(γT)·τ ξ²`, decoherence ∝ dissipation × temperature).
* **§B — the Gaussian off-diagonal suppression.** `caldeiraLeggettSuppression = exp(−φ)`;
  **`caldeiraLeggettSuppression_le_one`**, **`caldeiraLeggettSuppression_diagonal`** (`= 1` at `x = y`),
  **`caldeiraLeggettSuppression_antitone`** (larger separation ⇒ stronger suppression).
* **§C — the entropic-damping identification.** **`caldeiraLeggettSuppression_eq_kuiken`**
  (`exp(−φ) = kuikenWeight ℏ (ℏφ)` — the decoherence modulus is the entropic damping `exp(−S_I/ℏ)`).

**Honest layering.** Exact `Real.exp` / `ring` identities for the decoherence exponent and its Gaussian
suppression. The full Gaussian path integral of §V (Eqs. 5.1–5.35, the propagators `A,B,C`, the wave-packet
evaluation) is the paper's calculation, recorded not re-derived; the closed-form decoherence exponent `φ` it
produces — the entropic core — is formalized here.

## References

* H. F. Dowker, J. J. Halliwell, *Phys. Rev. D* **46** (1992) 1580, §IV, Eqs. 4.23–4.25; A. O. Caldeira,
  A. J. Leggett, *Physica A* **121** (1983) 587. Extends `DowkerHalliwellDecoherenceFunctional` into the thermal
  Caldeira–Leggett model; links to `PathIntegral.ComplexActionPathIntegralWeight`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence


/-- The **Caldeira–Leggett decoherence exponent** `φ = 2MγkT τ ξ²` — the imaginary (entropic) action for a path
separation `ξ = x − y` sustained over time `τ` (`∫ξ²dt = ξ²τ`), the Fokker–Planck influence-functional damping of
Eqs. 4.23/4.25. -/
noncomputable def caldeiraLeggettDecoherence (M γ kB T τ ξ : ℝ) : ℝ := 2 * M * γ * kB * T * τ * ξ ^ 2

/-- **The decoherence exponent is non-negative** `φ ≥ 0` — entropy production is non-negative. -/
lemma caldeiraLeggettDecoherence_nonneg (M γ kB T τ ξ : ℝ)
    (hM : 0 ≤ M) (hγ : 0 ≤ γ) (hkB : 0 ≤ kB) (hT : 0 ≤ T) (hτ : 0 ≤ τ) :
    0 ≤ caldeiraLeggettDecoherence M γ kB T τ ξ := by
  unfold caldeiraLeggettDecoherence; positivity

/-- **Decoherence vanishes exactly on the diagonal** `φ = 0 ↔ x = y` (`ξ = 0`) — the diagonal (Born) elements are
not suppressed; only the off-diagonal coherences decay. -/
lemma caldeiraLeggettDecoherence_eq_zero_iff (M γ kB T τ ξ : ℝ)
    (hM : 0 < M) (hγ : 0 < γ) (hkB : 0 < kB) (hT : 0 < T) (hτ : 0 < τ) :
    caldeiraLeggettDecoherence M γ kB T τ ξ = 0 ↔ ξ = 0 := by
  unfold caldeiraLeggettDecoherence
  have hc : 0 < 2 * M * γ * kB * T * τ := by positivity
  rw [mul_eq_zero, or_iff_right (ne_of_gt hc), pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)]

/-- **Fluctuation–dissipation** `φ = 2MkT·(γT)·ξ²τ` — the decoherence rate is proportional to `γT`, dissipation
(`γ`) times temperature (`T`): the fluctuation–dissipation relation for the noise driving decoherence. -/
lemma caldeiraLeggett_fluctuation_dissipation (M γ kB T τ ξ : ℝ) :
    caldeiraLeggettDecoherence M γ kB T τ ξ = 2 * M * kB * (γ * T) * τ * ξ ^ 2 := by
  unfold caldeiraLeggettDecoherence; ring


/-- The **decoherence suppression factor** `|F| = exp(−φ)` — the modulus of the Caldeira–Leggett influence
functional, the Gaussian damping of off-diagonal coherence. -/
noncomputable def caldeiraLeggettSuppression (M γ kB T τ ξ : ℝ) : ℝ :=
  Real.exp (-caldeiraLeggettDecoherence M γ kB T τ ξ)

/-- **The suppression factor is ≤ 1** — coherence can only decay, never grow. -/
lemma caldeiraLeggettSuppression_le_one (M γ kB T τ ξ : ℝ)
    (hM : 0 ≤ M) (hγ : 0 ≤ γ) (hkB : 0 ≤ kB) (hT : 0 ≤ T) (hτ : 0 ≤ τ) :
    caldeiraLeggettSuppression M γ kB T τ ξ ≤ 1 := by
  unfold caldeiraLeggettSuppression
  rw [Real.exp_le_one_iff]
  linarith [caldeiraLeggettDecoherence_nonneg M γ kB T τ ξ hM hγ hkB hT hτ]

/-- **No suppression on the diagonal** `exp(−φ) = 1` at `x = y` — the Born probabilities are preserved. -/
lemma caldeiraLeggettSuppression_diagonal (M γ kB T τ : ℝ) :
    caldeiraLeggettSuppression M γ kB T τ 0 = 1 := by
  simp [caldeiraLeggettSuppression, caldeiraLeggettDecoherence]

/-- **Larger path separation ⇒ stronger suppression** `ξ₁² ≤ ξ₂² → exp(−φ(ξ₂)) ≤ exp(−φ(ξ₁))` — coherence between
more-separated histories decays faster (the Gaussian in `ξ`). -/
lemma caldeiraLeggettSuppression_antitone (M γ kB T τ : ℝ)
    (hc : 0 ≤ 2 * M * γ * kB * T * τ) {ξ₁ ξ₂ : ℝ} (h : ξ₁ ^ 2 ≤ ξ₂ ^ 2) :
    caldeiraLeggettSuppression M γ kB T τ ξ₂ ≤ caldeiraLeggettSuppression M γ kB T τ ξ₁ := by
  unfold caldeiraLeggettSuppression caldeiraLeggettDecoherence
  gcongr


/-- **The decoherence modulus is the entropic damping** `exp(−φ) = kuikenWeight ℏ (ℏφ)` — the Caldeira–Leggett
Gaussian thermal-bath decoherence factor is exactly the entropic-damping modulus `exp(−S_I/ℏ)` of the complex-action
path-integral weight (`PathIntegral.ComplexActionPathIntegralWeight`), with imaginary action `S_I = ℏφ`. Decoherence
is entropy production. -/
lemma caldeiraLeggettSuppression_eq_kuiken (M γ kB T τ ξ ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    caldeiraLeggettSuppression M γ kB T τ ξ
      = kuikenWeight ℏ (ℏ * caldeiraLeggettDecoherence M γ kB T τ ξ) := by
  rw [caldeiraLeggettSuppression, kuikenWeight, mul_div_cancel_left₀ _ hℏ]

end Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettSuppression_eq_kuiken where
  formalizes @ "claim:the-caldeira-leggett-off-diagonal-suppression-factor-exp-minus-phi-is-exactly-the-entropic-damping-modulus-kuiken-weight-exp-minus-s-imaginary-over-hbar-of-the-complex-action-path-integral-weight-so-decoherence-is-literally-entropy-production",
  supported_by @ "paper:dowker-halliwell-phys-rev-d-46-1992-1580-caldeira-leggett-decoherence-functional"

zil attach Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettDecoherence_eq_zero_iff where
  formalizes @ "claim:the-caldeira-leggett-decoherence-exponent-vanishes-if-and-only-if-the-two-histories-coincide-x-equals-y-so-diagonal-born-elements-survive-while-all-off-diagonal-coherences-are-damped"

zil attach Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettSuppression_antitone where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:off-diagonal-coherence-between-more-widely-separated-histories-is-suppressed-more-strongly-a-gaussian-falloff-in-the-path-separation-xi"

zil attach Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettDecoherence_nonneg where
  formalizes @ "claim:the-caldeira-leggett-decoherence-exponent-is-non-negative-entropy-production-in-the-quantum-brownian-bath-is-never-negative"

zil_file_contract physlib.caldeiraLeggettDecoherence where
  promises "The Caldeira-Leggett decoherence functional (Dowker-Halliwell, Phys. Rev. D 46 (1992) 1580, Eqs. 4.23-4.25) as entropic damping. The high-temperature influence-functional decoherence exponent phi = 2 M gamma k T tau xi^2 is non-negative (caldeiraLeggettDecoherence_nonneg) and vanishes exactly on the diagonal x = y (caldeiraLeggettDecoherence_eq_zero_iff); the Gaussian off-diagonal suppression exp(-phi) is antitone in path separation (caldeiraLeggettSuppression_antitone). The suppression factor is exactly the entropic-damping modulus kuikenWeight = exp(-S_I/hbar) of the complex-action path-integral weight (caldeiraLeggettSuppression_eq_kuiken) -- decoherence is entropy production made explicit."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettDecoherence",
    "lean:Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettSuppression",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.kuikenWeight"]
  forbids_substitutes ["the full Gaussian path integral of the paper's Section V (Eqs. 5.1-5.35, the propagators A, B, C, the wave-packet evaluation), which is the cited calculation recorded not re-derived",
    "any claim that the exact non-Markovian influence functional is carried; only the high-temperature Fokker-Planck closed-form decoherence exponent is formalized"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettSuppression_eq_kuiken,
    Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettDecoherence_eq_zero_iff,
    Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettSuppression_antitone,
    Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence.caldeiraLeggettDecoherence_nonneg]

/- ZIL-END -/

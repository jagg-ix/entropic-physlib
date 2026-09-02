/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
meta import Zil

/-!
# The identity `E_I = Γ/2 = Ṡ_I` as a hub: path weight ↔ decay ↔ entropic time

The load-bearing, experimentally-grounded identity of the complex-action programme is

  `Im E = Γ/2 = Ṡ_I`  (imaginary energy = half the decay width = entropy-production rate),

with Gamow lifetime `τ = ℏ/Γ`. Three of its faces are already formalized in separate files but were not
linked:

* `NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight` — the complex-action path-integral weight `e^{iS/ℏ}` with
  `‖nnPathWeight S_R S_I ℏ‖ = e^{−S_I/ℏ}` (`norm_nnPathWeight`).
* `BenderIdentity` — the resonance side: `widthFromRate Ṡ_I = 2 Ṡ_I`, `lifetimeFromRate ℏ Ṡ_I = ℏ/Γ`, and
  the survival fraction `benderDecayFraction t τ = e^{−t/τ}`.
* `PathIntegral.ComplexActionDampingCoercivity.entropicProperTime S_I ℏ = S_I/ℏ` — the entropic clock.

This file makes them one structure, with the entropy-production rate `Ṡ_I` the common source. Under linear
entropy production `S_I(t) = Ṡ_I·t`:

* **Amplitude = entropic-clock weight** (`norm_nnPathWeight_eq_expNeg_entropicProperTime`):
  `‖nnPathWeight‖ = e^{−τ_ent}` — the path-weight modulus is `e^{−entropicProperTime}`.
* **Amplitude decays at half the width** (`norm_nnPathWeight_eq_expNegHalfWidth`):
  `‖nnPathWeight S_R (Ṡ_I t) ℏ‖ = e^{−(Γ t)/(2ℏ)}` with `Γ = widthFromRate Ṡ_I`.
* **Born rule — survival probability is the squared amplitude** (`benderDecayFraction_eq_normSq_nnPathWeight`):
  `benderDecayFraction t (ℏ/Γ) = ‖nnPathWeight S_R (Ṡ_I t) ℏ‖²`. The Gamow survival probability is exactly
  `|amplitude|²`, and (`benderDecayFraction_eq_expNegWidth`) equals `e^{−Γ t/ℏ}`.
* **Reversible limit** (`nnPathWeight_norm_reversible`): `Ṡ_I = 0 ⟹ ‖nnPathWeight‖ = 1` (unitary, no decay),
  matching `widthFromRate 0 = 0`.

So the Nagao–Nielsen path weight, the Bender resonance decay, and the entropic proper time are three readings
of the same `E_I = Γ/2 = Ṡ_I`.

## References

* N. Nagao, H. B. Nielsen, *Complex Action Theory* (path weight `e^{iS/ℏ}`). G. Gamow (decay width). `Physlib`
  (`BenderIdentity`, `NonHermitianComplexAction.EntropicDampingEquivalence`, `PathIntegral.ComplexActionDampingCoercivity`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay

/-- **[Path-weight modulus = entropic-clock weight]** `‖nnPathWeight S_R S_I ℏ‖ = e^{−τ_ent}` with
`τ_ent = entropicProperTime S_I ℏ = S_I/ℏ`: the complex-action weight's modulus is `e^{−entropicProperTime}`,
linking the Nagao–Nielsen weight to the entropic clock. -/
lemma norm_nnPathWeight_eq_expNeg_entropicProperTime (S_R S_I ℏ : ℝ) :
    ‖nnPathWeight S_R S_I ℏ‖ = Real.exp (-(entropicProperTime S_I ℏ)) := by
  rw [norm_nnPathWeight, entropicProperTime]

/-- **[Amplitude decays at half the width]** with linear entropy production `S_I = Ṡ_I·t`, the path-weight
amplitude is `‖nnPathWeight S_R (Ṡ_I t) ℏ‖ = e^{−(Γ t)/(2ℏ)}` where `Γ = widthFromRate Ṡ_I = 2 Ṡ_I` — the
Gamow amplitude decay `e^{−Γ t/2ℏ}`. -/
lemma norm_nnPathWeight_eq_expNegHalfWidth (S_R dSI ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    ‖nnPathWeight S_R (dSI * t) ℏ‖ = Real.exp (-(widthFromRate dSI * t) / (2 * ℏ)) := by
  rw [norm_nnPathWeight]
  congr 1
  unfold widthFromRate
  field_simp

/-- **[Born rule: survival probability is the squared amplitude]** the Gamow survival fraction equals the
squared modulus of the complex-action path weight: `benderDecayFraction t (ℏ/Γ) =
‖nnPathWeight S_R (Ṡ_I t) ℏ‖²`, with `ℏ/Γ = lifetimeFromRate ℏ Ṡ_I`. The probability is `|amplitude|²` — the
entropy-production rate `Ṡ_I` sourcing both. -/
lemma benderDecayFraction_eq_normSq_nnPathWeight (S_R dSI ℏ t : ℝ) :
    benderDecayFraction t (lifetimeFromRate ℏ dSI) = ‖nnPathWeight S_R (dSI * t) ℏ‖ ^ 2 := by
  rw [norm_nnPathWeight, ← Real.exp_nat_mul, benderDecayFraction, lifetimeFromRate]
  congr 1
  rw [div_div_eq_mul_div]
  push_cast
  ring

/-- **[Survival probability decays at the full width]** `benderDecayFraction t (ℏ/Γ) = e^{−Γ t/ℏ}` with
`Γ = widthFromRate Ṡ_I` — the probability decays at `Γ/ℏ`, twice the amplitude rate. -/
lemma benderDecayFraction_eq_expNegWidth (dSI ℏ t : ℝ) :
    benderDecayFraction t (lifetimeFromRate ℏ dSI) = Real.exp (-(widthFromRate dSI * t) / ℏ) := by
  rw [benderDecayFraction, lifetimeFromRate]
  congr 1
  unfold widthFromRate
  rw [div_div_eq_mul_div, neg_div]
  ring

/-- **[Reversible limit]** at zero entropy production the path weight is unitary: `‖nnPathWeight S_R 0 ℏ‖ = 1`
(no decay), matching `widthFromRate 0 = 0`. The boring/reversible model. -/
@[simp] lemma nnPathWeight_norm_reversible (S_R ℏ : ℝ) :
    ‖nnPathWeight S_R 0 ℏ‖ = 1 := by
  rw [norm_nnPathWeight]; simp

/-!

The decay results above are the **communicative** clock — the irreversible `H_I` decoherence, with width
`Γ = widthFromRate Ṡ_I` and survival `e^{−Γt/ℏ}`. The complementary **computational** clock is the *unitary*
`H_R` evolution, bounded by the Mandelstam–Tamm quantum speed limit set by the energy spread `ΔE`: the survival
`Q(t) = cos²(ΔE t/ℏ)`, with short-time quadratic flatness `Q(t) ≥ 1 − (ΔE t/ℏ)²` (the **quantum Zeno**
mechanism — frequent measurement keeps each interval's survival near `1`), reaching orthogonality at
`T_⊥ = πℏ/(2ΔE)`, i.e. the speed limit `ΔE·T_⊥ = πℏ/2`.

The two clocks are **independent**: the total survival factorizes into the unitary oscillation `cos²(ΔE t/ℏ)`
(governed by `ΔE`, an `H_R` property) and the irreversible decay `e^{−Γt/ℏ}` (governed by `Γ`, an `H_I`
property) — `combinedSurvival_eq`. The `ΔE` of `H_R` does not set the `Γ` of `H_I`. (Uses
Mandelstam–Tamm / Margolus–Levitin speed limits and the quantum Zeno effect.) -/

/-- **The Mandelstam–Tamm survival probability** `Q(t) = cos²(ΔE t/ℏ)` — the unitary `H_R` "computational
clock", saturating the quantum speed limit set by the energy spread `ΔE`. -/
noncomputable def mandelstamTammSurvival (ΔE ℏ t : ℝ) : ℝ := Real.cos (ΔE * t / ℏ) ^ 2

@[simp] lemma mandelstamTammSurvival_nonneg (ΔE ℏ t : ℝ) : 0 ≤ mandelstamTammSurvival ΔE ℏ t :=
  sq_nonneg _

lemma mandelstamTammSurvival_le_one (ΔE ℏ t : ℝ) : mandelstamTammSurvival ΔE ℏ t ≤ 1 := by
  unfold mandelstamTammSurvival; exact Real.cos_sq_le_one _

/-- **[Short-time quadratic flatness — the Zeno mechanism]** `Q(t) ≥ 1 − (ΔE t/ℏ)²`. The survival is
quadratically flat at short time, so dividing the evolution into ever-shorter measured intervals keeps each
interval's survival near `1` (quantum Zeno freeze). -/
lemma mandelstamTammSurvival_quadratic_lower (ΔE ℏ t : ℝ) :
    1 - (ΔE * t / ℏ) ^ 2 ≤ mandelstamTammSurvival ΔE ℏ t := by
  unfold mandelstamTammSurvival
  have hpyth := Real.sin_sq_add_cos_sq (ΔE * t / ℏ)
  have hsin : Real.sin (ΔE * t / ℏ) ^ 2 ≤ (ΔE * t / ℏ) ^ 2 := Real.sin_sq_le_sq
  nlinarith [hpyth, hsin]

/-- **[Quantum Zeno freeze]** dividing the evolution into `N` measured intervals of duration `t/N`, each
interval's survival is `≥ 1 − (ΔE t/(Nℏ))² → 1` as `N` grows: frequent measurement freezes the `H_R` clock. -/
lemma zeno_interval_survival (ΔE ℏ t N : ℝ) :
    1 - (ΔE * t / (N * ℏ)) ^ 2 ≤ mandelstamTammSurvival ΔE ℏ (t / N) := by
  have h := mandelstamTammSurvival_quadratic_lower ΔE ℏ (t / N)
  have he : ΔE * (t / N) / ℏ = ΔE * t / (N * ℏ) := by ring
  rwa [he] at h

/-- **[Genuine ideal quantum-Zeno freeze].**  The survival probability for `n` equal monitored
intervals tends to one:

`(mandelstamTammSurvival ΔE ℏ (t/n))ⁿ → 1` as `n → ∞`.

The proof upgrades the per-interval quadratic bound to the actual repeated-survival limit.  It uses
`sin² x ≤ x²` to show
`n · (cos²(a/n) - 1) → 0`, then the general varying-base power limit
`(1 + g n)ⁿ → exp 0 = 1`.  This is the ideal factorized projection model; it does not construct a
measurement channel, prove a product formula for an unbounded Hamiltonian and projection, or model
finite-duration detector backreaction. -/
@[zil_level bridge_theorem]
theorem mandelstamTamm_repeated_survival_tendsto_one (ΔE ℏ t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => mandelstamTammSurvival ΔE ℏ (t / n) ^ n)
      Filter.atTop (nhds 1) := by
  let a : ℝ := ΔE * t / ℏ
  let gseq : ℕ → ℝ := fun n => Real.cos (a / n) ^ 2 - 1
  have hg : Filter.Tendsto (fun n : ℕ => (n : ℝ) * gseq n)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
      have htrig : Real.cos (a / n) ^ 2 - 1 = -(Real.sin (a / n) ^ 2) := by
        nlinarith [Real.sin_sq_add_cos_sq (a / n)]
      change ‖(n : ℝ) * (Real.cos (a / n) ^ 2 - 1)‖ ≤ a ^ 2 / n
      rw [htrig, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n),
        abs_neg, abs_sq]
      calc
        (n : ℝ) * Real.sin (a / n) ^ 2 ≤ (n : ℝ) * (a / n) ^ 2 :=
          mul_le_mul_of_nonneg_left Real.sin_sq_le_sq (Nat.cast_nonneg n)
        _ = a ^ 2 / n := by field_simp
    · exact tendsto_const_div_atTop_nhds_zero_nat (a ^ 2)
  have hpow := Real.tendsto_one_add_pow_exp_of_tendsto hg
  have hpow' : Filter.Tendsto
      (fun n : ℕ => (Real.cos (a / n) ^ 2) ^ n)
      Filter.atTop (nhds 1) := by
    simpa [gseq] using hpow
  apply hpow'.congr'
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  congr 1
  unfold mandelstamTammSurvival a
  congr 2
  field_simp

/-- **The quantum speed-limit (orthogonalization) time** `T_⊥ = πℏ/(2ΔE)` — the earliest time the state
becomes orthogonal under unitary `H_R` evolution. -/
noncomputable def orthogonalizationTime (ΔE ℏ : ℝ) : ℝ := Real.pi * ℏ / (2 * ΔE)

/-- **[Orthogonality at `T_⊥`]** `Q(T_⊥) = 0` — the state is orthogonal to its initial value at the
speed-limit time. -/
lemma mandelstamTammSurvival_orthogonal (ΔE ℏ : ℝ) (hΔE : ΔE ≠ 0) (hℏ : ℏ ≠ 0) :
    mandelstamTammSurvival ΔE ℏ (orthogonalizationTime ΔE ℏ) = 0 := by
  unfold mandelstamTammSurvival orthogonalizationTime
  have hπ2 : ΔE * (Real.pi * ℏ / (2 * ΔE)) / ℏ = Real.pi / 2 := by field_simp
  rw [hπ2, Real.cos_pi_div_two]; norm_num

/-- **[The quantum speed limit]** `ΔE · T_⊥ = πℏ/2` — the Mandelstam–Tamm bound: the energy spread `ΔE` of the
unitary `H_R` clock sets the minimal time to orthogonality. -/
lemma quantumSpeedLimit (ΔE ℏ : ℝ) (hΔE : ΔE ≠ 0) :
    ΔE * orthogonalizationTime ΔE ℏ = Real.pi * ℏ / 2 := by
  unfold orthogonalizationTime; field_simp

/-- **The combined two-clock survival** `Q_R(t)·Q_I(t)` — the unitary Mandelstam–Tamm factor times the
irreversible decay factor. -/
noncomputable def combinedSurvival (ΔE dSI ℏ t : ℝ) : ℝ :=
  mandelstamTammSurvival ΔE ℏ t * benderDecayFraction t (lifetimeFromRate ℏ dSI)

/-- **[Two independent clocks]** the total survival factorizes into the unitary oscillation `cos²(ΔE t/ℏ)`
(the computational `H_R` clock, set by the energy spread `ΔE`) and the irreversible decay `e^{−Γt/ℏ}` (the
communicative `H_I` clock, set by the width `Γ = widthFromRate Ṡ_I`). The two are manifestly independent —
oscillatory vs exponential, `ΔE` vs `Γ` — so the `ΔE` of `H_R` does not set the decoherence rate of `H_I`. -/
lemma combinedSurvival_eq (ΔE dSI ℏ t : ℝ) :
    combinedSurvival ΔE dSI ℏ t
      = Real.cos (ΔE * t / ℏ) ^ 2 * Real.exp (-(widthFromRate dSI * t) / ℏ) := by
  unfold combinedSurvival mandelstamTammSurvival
  rw [benderDecayFraction_eq_expNegWidth]

/-!

The communicative sector's specific physical form (Gambini–Porto fundamental decoherence) is the
double-commutator dissipator `σ[H_R,[H_R,ρ]]`. In the energy basis it makes the coherence between two levels
separated by the energy gap `ΔE = Eₙ − Eₘ` decay as `e^{−σ·ΔE²·t}`. Three consequences: **diagonal populations
are stable** (gap `0` ⟹ no decay), **off-diagonal coherences decay**, and **decoherence is fastest for
macroscopic superpositions** (large energy gap ⟹ fast decay). -/

/-- **The Gambini–Porto coherence factor** `e^{−σ·ΔE²·t}` for the coherence between two energy levels separated
by the gap `ΔE`, from the double-commutator dissipator `σ[H_R,[H_R,ρ]]`. -/
noncomputable def gambiniPortoCoherence (σ Egap t : ℝ) : ℝ := Real.exp (-(σ * Egap ^ 2 * t))

/-- **[Diagonal populations are stable]** zero energy gap ⟹ coherence factor `1` (no decay): populations
(diagonal `ρₙₙ`) are untouched by the fundamental-decoherence dissipator. -/
@[simp] lemma gambiniPorto_diagonal_stable (σ t : ℝ) : gambiniPortoCoherence σ 0 t = 1 := by
  unfold gambiniPortoCoherence; simp

/-- **[Coherences never grow]** `e^{−σΔE²t} ≤ 1` for `σ, t ≥ 0`. -/
lemma gambiniPortoCoherence_le_one (σ Egap t : ℝ) (hσ : 0 ≤ σ) (ht : 0 ≤ t) :
    gambiniPortoCoherence σ Egap t ≤ 1 := by
  unfold gambiniPortoCoherence
  rw [Real.exp_le_one_iff]
  have := mul_nonneg (mul_nonneg hσ (sq_nonneg Egap)) ht
  linarith

/-- **[Off-diagonal coherences decay]** a nonzero energy gap with `σ, t > 0` strictly suppresses the coherence
`e^{−σΔE²t} < 1` — superpositions of distinct energies lose phase relation. -/
lemma gambiniPorto_offdiagonal_decays (σ Egap t : ℝ) (hσ : 0 < σ) (hgap : Egap ≠ 0) (ht : 0 < t) :
    gambiniPortoCoherence σ Egap t < 1 := by
  unfold gambiniPortoCoherence
  rw [Real.exp_lt_one_iff]
  have hsq : 0 < Egap ^ 2 := lt_of_le_of_ne (sq_nonneg Egap) (pow_ne_zero 2 hgap).symm
  nlinarith [mul_pos (mul_pos hσ hsq) ht]

/-- **[Decoherence is fastest for macroscopic superpositions]** a larger energy gap (`ΔE₁² ≤ ΔE₂²`) gives a
smaller coherence factor — the wider the energy separation of the superposition, the faster it decoheres. -/
lemma gambiniPorto_monotone (σ Egap₁ Egap₂ t : ℝ) (hσ : 0 ≤ σ) (ht : 0 ≤ t)
    (h : Egap₁ ^ 2 ≤ Egap₂ ^ 2) :
    gambiniPortoCoherence σ Egap₂ t ≤ gambiniPortoCoherence σ Egap₁ t := by
  unfold gambiniPortoCoherence
  apply Real.exp_le_exp.mpr
  have hle : σ * Egap₁ ^ 2 * t ≤ σ * Egap₂ ^ 2 * t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hσ) ht
  linarith

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.norm_nnPathWeight_eq_expNeg_entropicProperTime where
  formalizes @ "claim:the-complex-action-path-weight-amplitude-equals-exp-minus-entropic-proper-time-linking-the-path-integral-to-the-entropic-clock",
  supported_by @ "object:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity.entropicProperTime"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.benderDecayFraction_eq_normSq_nnPathWeight where
  formalizes @ "claim:the-gamow-survival-fraction-equals-the-squared-modulus-of-the-complex-action-path-weight-the-born-rule-for-the-decaying-state",
  supported_by @ "object:Physlib.QuantumMechanics.ComplexAction.BenderIdentity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.benderDecayFraction_eq_expNegWidth where
  formalizes @ "claim:the-survival-probability-decays-at-the-full-width-gamma-over-hbar-twice-the-amplitude-rate-with-gamma-equal-to-twice-the-entropy-production-rate",
  requires @ "claim:the-gamow-survival-fraction-equals-the-squared-modulus-of-the-complex-action-path-weight-the-born-rule-for-the-decaying-state"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.quantumSpeedLimit where
  formalizes @ "claim:the-mandelstam-tamm-quantum-speed-limit-delta-E-times-the-orthogonalization-time-equals-pi-hbar-over-two"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.mandelstamTamm_repeated_survival_tendsto_one where
  formalizes @ "claim:in-the-ideal-factorized-projection-model-the-n-fold-mandelstam-tamm-survival-at-interval-t-over-n-tends-to-one-the-genuine-quantum-zeno-freeze-limit",
  supported_by @ "lean:Real.tendsto_one_add_pow_exp_of_tendsto",
  supported_by @ "lean:Real.sin_sq_le_sq",
  caveat @ "claim:ideal-repeated-survival-limit-not-an-unbounded-operator-product-formula-or-finite-duration-detector-model"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.combinedSurvival_eq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.benderDecayFraction_eq_expNegWidth",
  formalizes @ "claim:the-total-survival-factorizes-into-a-unitary-mandelstam-tamm-oscillation-set-by-delta-E-and-an-irreversible-decay-set-by-the-width-two-independent-clocks"

zil_file_contract physlib.entropyProductionDecay where
  promises "The load-bearing identity Im E = Gamma/2 = Sdot_I as a hub linking three formalized faces. The complex-action path-integral weight amplitude equals exp(-entropicProperTime) = exp(-S_I/hbar) (norm_nnPathWeight_eq_expNeg_entropicProperTime); the Gamow survival fraction is the squared modulus of that path weight, the Born rule for the decaying state (benderDecayFraction_eq_normSq_nnPathWeight), decaying at the full width Gamma/hbar = 2 Sdot_I/hbar, twice the amplitude rate (benderDecayFraction_eq_expNegWidth). It also carries the Mandelstam-Tamm quantum speed limit Delta_E times the orthogonalization time = pi hbar/2 (quantumSpeedLimit), proves the ideal n-fold repeated-survival quantum-Zeno limit tends to one (mandelstamTamm_repeated_survival_tendsto_one), and shows the total survival factorizes into a unitary oscillation set by Delta_E times an irreversible decay set by the width -- two independent clocks (combinedSurvival_eq)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity.entropicProperTime"]
  forbids_substitutes ["the microscopic derivation of the decay width from resonance theory, only the algebraic identity Im E = Gamma/2 = Sdot_I and its three faces are carried",
    "the Gambini-Porto fundamental-decoherence dynamics, whose specific dissipator form is cited not derived",
    "calling the ideal factorized repeated-survival limit an unbounded-Hamiltonian projection-product theorem or a finite-duration detector model"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.norm_nnPathWeight_eq_expNeg_entropicProperTime,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.benderDecayFraction_eq_normSq_nnPathWeight,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.benderDecayFraction_eq_expNegWidth,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.quantumSpeedLimit,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.mandelstamTamm_repeated_survival_tendsto_one,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.combinedSurvival_eq]

/- ZIL-END -/

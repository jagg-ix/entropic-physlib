/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
public import Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
meta import Zil

/-!
# Entropic time of the Bogoliubov transformation

This file inspects how the **entropic time** `τ_ent = S_I/ℏ` of the arc enters the Bogoliubov
transformation (`Bogoliubov.Transformation`). The answer: it is the **entanglement entropy of the
quasiparticle occupation** `v²` — the Bogoliubov mode-mixing produces entropy.

For the Bogoliubov-transformed (BCS) state, tracing out one partner of each pair leaves a
single-mode state with occupation `v²`; its (binary / von Neumann) entropy

  `τ_ent = binEntropy(v²)`   (`bogoliubovEntropicTime`)

is the entropy production. It is:

* **`≥ 0`** (`bogoliubov_entropicTime_nonneg`) — the arrow of time;
* **`= 0` exactly when there is no mode mixing** (`v² = 0` or `v² = 1`,
  `bogoliubov_entropicTime_eq_zero_iff`) — the reversible normal state. In particular at
  `Δ = 0` (no pairing) the entropic time vanishes (`bogoliubov_entropicTime_normal_zero`): the
  reversible / alpha-particle / `S_I = 0` point of `KramersKronig.EntropyHamiltonian`;
* **maximal at `ξ = 0`** (`v² = ½`, `bogoliubov_entropicTime_at_zero_xi`), the symmetric pairing
  point where the particle–hole entanglement is greatest.

So the Bogoliubov pairing `Δ ≠ 0` (the irreversible / Kramers–Kronig sector) is exactly what
turns on the entropic time, and the normal state `Δ = 0` is the entropy-free / reversible fiber
the rest of the arc lives on.

## References

* N. N. Bogoljubov (1958); BCS entanglement entropy. `Bogoliubov.Transformation`,
  `KramersKronig.EntropyHamiltonian` (this development); `Real.binEntropy` (Mathlib).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime


/-- **The entropic time of the Bogoliubov transformation** `τ_ent = binEntropy(v²)` — the
entanglement entropy of the quasiparticle occupation `v²` (the entropy production `S_I/ℏ`). -/
def bogoliubovEntropicTime (ξ Δ : ℝ) : ℝ := Real.binEntropy (bogoliubovV2 ξ Δ)


/-- `|ξ| ≤ E` (the kinetic energy is bounded by the quasiparticle energy). -/
lemma abs_le_bogoliubovEnergy (ξ Δ : ℝ) : |ξ| ≤ bogoliubovEnergy ξ Δ := by
  unfold bogoliubovEnergy
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg Δ]

/-- **The occupation is a probability** `0 ≤ v² ≤ 1` (for a genuine gap `Δ ≠ 0`, so `E > 0`). -/
lemma bogoliubovV2_mem_unitInterval (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    0 ≤ bogoliubovV2 ξ Δ ∧ bogoliubovV2 ξ Δ ≤ 1 := by
  have hE : 0 < bogoliubovEnergy ξ Δ := by
    unfold bogoliubovEnergy; exact Real.sqrt_pos.mpr (by positivity)
  have habs : |ξ / bogoliubovEnergy ξ Δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hE, div_le_one hE]
    exact abs_le_bogoliubovEnergy ξ Δ
  rw [abs_le] at habs
  unfold bogoliubovV2
  constructor <;> linarith [habs.1, habs.2]


/-- **Entropic time is non-negative** (the arrow of time), for a genuine gap `Δ ≠ 0`. -/
lemma bogoliubov_entropicTime_nonneg (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    0 ≤ bogoliubovEntropicTime ξ Δ :=
  Real.binEntropy_nonneg (bogoliubovV2_mem_unitInterval ξ Δ hΔ).1
    (bogoliubovV2_mem_unitInterval ξ Δ hΔ).2

/-- **Entropic time vanishes iff there is no mode mixing** (`v² = 0` or `v² = 1`): the reversible
normal state has zero entropy production. -/
lemma bogoliubov_entropicTime_eq_zero_iff (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = 0 ↔ bogoliubovV2 ξ Δ = 0 ∨ bogoliubovV2 ξ Δ = 1 :=
  Real.binEntropy_eq_zero

/-- **No pairing ⟹ no entropic time**: at `Δ = 0`, `ξ > 0` the normal state (`v² = 0`) has zero
entropic time — the reversible / alpha-particle / `S_I = 0` fiber. -/
lemma bogoliubov_entropicTime_normal_zero (ξ : ℝ) (hξ : 0 < ξ) :
    bogoliubovEntropicTime ξ 0 = 0 := by
  unfold bogoliubovEntropicTime
  rw [(bogoliubov_normal_state ξ hξ).2, Real.binEntropy_zero]

/-- **At `ξ = 0` the occupation is `½`** (the symmetric pairing point). -/
lemma bogoliubovV2_at_zero_xi (Δ : ℝ) : bogoliubovV2 0 Δ = 1 / 2 := by
  unfold bogoliubovV2; simp

/-- **Entropic time is maximal at `ξ = 0`**: `τ_ent = binEntropy(½)` (the greatest particle–hole
entanglement, the symmetric pairing point). -/
lemma bogoliubov_entropicTime_at_zero_xi (Δ : ℝ) :
    bogoliubovEntropicTime 0 Δ = Real.binEntropy (1 / 2) := by
  unfold bogoliubovEntropicTime
  rw [bogoliubovV2_at_zero_xi]

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime


/-- **The Nagao-Nielsen Lorentzian form on the contour `q = ω + iγ`, as a function of the real
frequency `ω`**: `L(ω + iγ) = ω² - γ²`. -/
def lorentzianDispersion (γ : ℝ) : ℝ → ℝ :=
  fun ω => lorentzianForm ((ω : ℂ) + (γ : ℂ) * Complex.I)

/-- **The Nagao-Nielsen dispersion is Kozak-even** in the frequency `ω`:
`L(-ω + iγ) = L(ω + iγ)`. -/
lemma lorentzianDispersion_fnEven (γ : ℝ) : FnEven (lorentzianDispersion γ) := by
  intro ω
  unfold lorentzianDispersion lorentzianForm
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]


/-- **On the real contour** (`γ = 0`) the Nagao-Nielsen form is timelike `L = ω² ≥ 0`. -/
lemma lorentzianDispersion_real_nonneg (ω : ℝ) : 0 ≤ lorentzianDispersion 0 ω := by
  simp [lorentzianDispersion, lorentzianForm]
  positivity

/-- **The Wick rotation flips the Lorentzian form** `L(iq) = -L(q)`. -/
lemma wick_flips_lorentzian (q : ℂ) : lorentzianForm (Complex.I * q) = -lorentzianForm q :=
  lorentzianForm_mul_I q


/-- **The real contour is reversible.** At `γ = 0`, the Nagao-Nielsen form is nonnegative,
the Kozak dispersion is even, and the Bogoliubov entropic time vanishes. -/
lemma real_contour_reversible (ξ : ℝ) (hξ : 0 < ξ) (ω : ℝ) :
    0 ≤ lorentzianDispersion 0 ω
      ∧ FnEven (lorentzianDispersion 0)
      ∧ bogoliubovEntropicTime ξ 0 = 0 :=
  ⟨lorentzianDispersion_real_nonneg ω, lorentzianDispersion_fnEven 0,
   bogoliubov_entropicTime_normal_zero ξ hξ⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubovV2_mem_unitInterval where
  supported_by @ "lean:HermitianMat.sqrt_pos",
  formalizes @ "claim:the-bogoliubov-quasiparticle-occupation-v-squared-lies-in-the-unit-interval-for-a-genuine-gap-a-valid-probability"

zil attach Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubov_entropicTime_nonneg where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubovV2_mem_unitInterval",
  formalizes @ "claim:the-bogoliubov-entropic-time-the-binary-entanglement-entropy-of-the-quasiparticle-occupation-is-non-negative-the-arrow-of-time",
  requires @ "claim:the-bogoliubov-quasiparticle-occupation-v-squared-lies-in-the-unit-interval-for-a-genuine-gap-a-valid-probability"

zil attach Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubov_entropicTime_eq_zero_iff where
  formalizes @ "claim:the-bogoliubov-entropic-time-vanishes-if-and-only-if-there-is-no-mode-mixing-occupation-zero-or-one-the-reversible-normal-state-has-zero-entropy-production"

zil attach Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubov_entropicTime_at_zero_xi where
  formalizes @ "claim:the-bogoliubov-entropic-time-is-maximal-at-zero-xi-equal-to-the-binary-entropy-of-one-half-the-greatest-particle-hole-entanglement-at-the-symmetric-pairing-point"

zil_file_contract physlib.bogoliubovEntropicTime where
  promises "How the entropic time tau_ent = S_I/hbar of the arc enters the Bogoliubov transformation: it is the binary entanglement entropy of the quasiparticle occupation v^2, so the Bogoliubov mode-mixing produces entropy. The occupation v^2 is a valid probability in the unit interval (bogoliubovV2_mem_unitInterval); the resulting entropic time is non-negative -- the arrow of time (bogoliubov_entropicTime_nonneg) -- and vanishes exactly when there is no mode mixing (v^2 = 0 or 1), the reversible normal state (bogoliubov_entropicTime_eq_zero_iff). It is maximal at zero xi, where the occupation is one half and the particle-hole entanglement is greatest (bogoliubov_entropicTime_at_zero_xi)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubovEntropicTime",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation.bogoliubovV2"]
  forbids_substitutes ["the operational identification of the binary entanglement entropy with a physical clock, which is the entropic-time hypothesis of the arc",
    "any many-body entanglement-entropy computation, only the single-mode binary-entropy identities are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubovV2_mem_unitInterval,
    Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubov_entropicTime_nonneg,
    Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubov_entropicTime_eq_zero_iff,
    Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubov_entropicTime_at_zero_xi]

/- ZIL-END -/

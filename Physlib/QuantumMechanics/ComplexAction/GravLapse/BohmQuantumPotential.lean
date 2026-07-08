/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.HyperbolicInterval
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram

/-!
# de Broglie–Bohm quantum potential & Born rule, ported and linked to the lapse / hyperbolic interval

Ports the Bohmian-mechanics theorems of the `reference tree` integration layer
(`DBBQuantumPotentialBridge`, `BohmianQMBridge`) into `physlib` and links them to the lapse-contour and
hyperbolic-interval formalizations (`GravLapse.ContourMaster`, `GravLapse.HyperbolicInterval`).
`physlib` cannot import `reference tree` (the dependency runs the other way), so the Bohm theorems are
re-proved here as self-contained `physlib` lemmas and then **connected to the actual lapse objects** rather
than to abstract `S_I`.

The Madelung decomposition `ψ = R·e^{iS/ℏ}` gives the de Broglie–Bohm quantum potential
`Q = −(ℏ²/2m)∇²R/R`, which under the complex-action/entropic-time dissipative extension is `Q = S_I·ℏ/(2m)`
(reference tree `DBBQuantumPotentialBridge`, Paper 2 App. C), and the Born weight `‖ψ‖ = e^{−S_I/ℏ}`
(reference tree `BohmianQMBridge`, `path_amplitude_norm`). The lapse arc supplies the concrete
`S_I = εℋ`.

* **§A — ported de Broglie–Bohm quantum potential** (`bohmQuantumPotential`, `…_nonneg`, `…_zero_iff`).
  `Q = S_I·ℏ/(2m)`, non-negative for `S_I ≥ 0`, and `Q = 0 ⟺ S_I = 0` (the classical limit). The `S_I` here
  is *not* a free parameter: it is rederived in **§F** from the Nagao–Nielsen contour (`S_I = E_I·t`, the
  gap × time) and in **§G** from the complex oscillator (`S_I = −V_I·t`, the imaginary potential), with
  `_nonneg`/`_zero_iff` following from NN convergence (`E_I ≥ 0` / `V_I ≤ 0`) and reversibility
  (`E_I = 0` / `V_I = 0`).
* **§B — ported Madelung / Born amplitude** (`madelungAmplitude`, `madelungAmplitude_norm`, `bornWeight`,
  `madelung_born_rule`). `ψ = e^{iS_R/ℏ}·e^{−S_I/ℏ}` with `‖ψ‖ = e^{−S_I/ℏ}` (Born weight) and Born
  probability `‖ψ‖² = e^{−2S_I/ℏ}`.
* **§C — the lapse weight IS a Madelung pilot wave** (`lapseWeight_eq_madelungAmplitude`, `lapse_bornWeight`,
  `lapse_born_rule`). `lapseWeight N ε ℋ = madelungAmplitude (−Nℋ) (εℋ) 1`, so the Banihashemi–Jacobson
  lapse weight is a de Broglie–Bohm pilot-wave amplitude with real action `S_R = −Nℋ` and Born weight
  `e^{−εℋ}`.
* **§D — the lapse quantum potential and its classical limit** (`lapse_quantumPotential`,
  `lapse_classical_limit_iff_reversible`). The lapse imaginary action `S_I = εℋ` is the Bohmian quantum
  potential `Q = εℋ·ℏ/(2m)`, which vanishes **iff** `ε = 0` (for `ℋ ≠ 0`) — the de Broglie–Bohm classical
  limit is exactly the reversible lapse contour of `GravLapse.ContourEntropicTime.lapse_real_contour_reversible`.
* **§E — the Bohmian guidance velocity is the rapidity / diamond velocity** (`lapse_bohm_velocity_eq_tanh`,
  `lapse_bohm_hyperbolic`). On the mass shell (`N = Δcosh θ`, `ε = Δsinh θ`,
  `GravLapse.HyperbolicInterval`), the de Broglie–Bohm guidance velocity `ε/N = tanh θ` is the
  causal-diamond / Bogoliubov velocity. The hyperbolic rapidity `θ` controls both the kinematic velocity
  (`tanh θ`) and the Bohmian quantum potential (`∝ Δsinh θ`); the rest frame `θ = 0` is the classical /
  reversible limit (`Q = 0`, velocity `0`, Born weight `1`).
* **§F — `Q` rederived from the Nagao–Nielsen contour** (`nnContour_bornWeight`,
  `nnContour_quantumPotential_nonneg`, `nnContour_quantumPotential_zero_iff`). The imaginary action is the
  gap × time, `S_I = E_I·t`; the NN eigen-propagator's modulus is the Born weight (`norm_evolutionFactor`);
  `Q ≥ 0` follows from the gap `E_I ≥ 0` (convergence) and `Q = 0 ⟺ E_I = 0` (reversible / unitary).
* **§G — `Q` rederived from the complex oscillator** (`oscillator_quantumPotential_nonneg`,
  `oscillator_quantumPotential_zero_iff`). The imaginary action is `S_I = −V_I·t` with `V_I = ½Im(mω²)q²`
  (`ComplexOscillator.PhaseDiagram.oscillatorPotentialIm`); `Q ≥ 0` follows from oscillator convergence
  `V_I ≤ 0` (`potentialConverges_iff_potentialIm_nonpos`) and `Q = 0 ⟺ V_I = 0` (the real-oscillator
  phase-diagram boundary).
* **§H — the clock, clarified** (`nnEntropicTime`, `nnContour_bornWeight_eq_exp_neg_entropicTime`,
  `nnContour_bornWeight_eq_entropyDamping`). The `t` of §F/§G is the **ordinary Schrödinger evolution
  (coordinate) time** of the propagator `e^{−iE_C t/ℏ}` — the *input* clock, **not** the entropic time. The
  **entropic time** is the *derived* `τ_ent = S_I/ℏ = E_I·t/ℏ`; the Born weight is `e^{−τ_ent}` and the
  quantum potential `Q = τ_ent·ℏ²/(2m)`. `t` enters only through `τ_ent`.
* **§I — the imaginary action is the contour gap × conjugate** (`complexAction`, `complexAction_im`,
  `lapse_imaginaryAction`, `propagator_imaginaryAction`, `contour_interval_and_action`). Formalizes the
  clock-resolving reasoning: `S_I = Im(−(contour point)·(conjugate)) = g·c`, where the contour point
  `complexEnergy a g = a − ig` includes the gap `g` and `c` is the real conjugate. The lapse (`c = ℋ`,
  `g = ε`) and the propagator (`c = t`, `g = E_I`) are the two dual instances; the same gap `g` is the
  contour interval's spacelike leg (`lorentzianForm = a² − g²`).
* **§J — a lapse constructed from the NN complex via the Bohm polar form** (`bohmLapse`,
  `bohmLapseWeight_eq_madelung`, `bohmLapse_recovers_action`). The Bohm polar transform of the
  Nagao–Nielsen weight `e^{(i/ℏ)S_complex}` (`S_complex = S_R + iS_I`) gives amplitude `R = e^{−S_I/ℏ}` and phase
  `S_R`; the lapse realising it is `N_c = −S_complex/ℋ` (real lapse `N = −S_R/ℋ`, gap `ε = S_I/ℋ`). Its lapse
  weight **is** the NN Bohm pilot wave `madelungAmplitude S_R S_I`, its complex action recovers `S_complex`
  (invertible), and its Born weight is the Bohm amplitude `e^{−S_I}`. It is anchored to the rest of the repo
  by `bohmLapse_inverts_lapseAction` (the exact inverse of the lapse → action map,
  `bohmLapse (−Nℋ) (εℋ) ℋ = complexEnergy N ε`), `bohmLapseWeight_eq_nagaoNielsen` (the canonical NN complex-action
  weight), and `bohmLapseWeight_unimodular_iff` (reversible ⟺ `S_I = 0`, the classical fiber).

## References

* reference tree `reference tree/Integration/DBBQuantumPotentialBridge.lean` (Paper 2 App. C, `Q = S_I·ℏ/2m`) and
  `reference tree/Integration/BohmianQMBridge.lean` (`path_amplitude_norm`, Madelung / Born) — the
  ported theorems.
* D. Bohm, *A suggested interpretation of the quantum theory in terms of "hidden" variables I, II*,
  Phys. Rev. 85 (1952) 166, 180. E. Madelung, *Quantentheorie in hydrodynamischer Form*, Z. Phys. 40
  (1927) 322.
* Repo dependencies: `GravLapse.ContourMaster` (`lapseWeight`, `lapseWeight_eq_master`),
  `GravLapse.HyperbolicInterval` (`lapse_velocity_eq_rapidity`), `PathIntegral.ComplexActionPathIntegralWeight`
  (`complexActionPathIntegralWeight`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential

open Physlib.QuantumMechanics.ComplexAction.GravLapse.HyperbolicInterval
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-! ## §A — ported de Broglie–Bohm quantum potential `Q = S_I·ℏ/(2m)` -/

/-- **[Port — reference tree `DBBQuantumPotentialBridge`, Paper 2 App. C] The de Broglie–Bohm quantum
potential** `Q = S_I·ℏ/(2m)`: under the complex-action/entropic-time dissipative extension the Bohmian quantum potential
`−(ℏ²/2m)∇²R/R` is the imaginary-action density times `ℏ/(2m)`. -/
noncomputable def bohmQuantumPotential (S_I ℏ m : ℝ) : ℝ := S_I * ℏ / (2 * m)

/-- **[Port] The quantum potential is non-negative** for `S_I ≥ 0` (the Bohmian non-classical attractor). -/
theorem bohmQuantumPotential_nonneg (S_I ℏ m : ℝ) (hS : 0 ≤ S_I) (hℏ : 0 ≤ ℏ) (hm : 0 < m) :
    0 ≤ bohmQuantumPotential S_I ℏ m := by
  unfold bohmQuantumPotential; apply div_nonneg (mul_nonneg hS hℏ); linarith

/-- **[Port] The classical-limit dichotomy** `Q = 0 ⟺ S_I = 0`: the Bohmian guide turns off precisely when
the imaginary action vanishes. -/
theorem bohmQuantumPotential_zero_iff (S_I ℏ m : ℝ) (hℏ : ℏ ≠ 0) (hm : 0 < m) :
    bohmQuantumPotential S_I ℏ m = 0 ↔ S_I = 0 := by
  unfold bohmQuantumPotential
  rw [div_eq_zero_iff, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact h
    · exact absurd h hℏ
    · have h2 : (0 : ℝ) < 2 * m := by positivity
      exact absurd h h2.ne'
  · intro h; exact Or.inl (Or.inl h)

/-! ## §B — ported Madelung / Born amplitude `ψ = e^{iS_R/ℏ}·e^{−S_I/ℏ}` -/

/-- **[Port — reference tree `BohmianQMBridge`] The Madelung / complex-action pilot-wave amplitude**
`ψ = e^{iS_R/ℏ}·e^{−S_I/ℏ}` (`R = e^{−S_I/ℏ}`, phase `S = S_R`). -/
noncomputable def madelungAmplitude (S_R S_I ℏ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((S_R / ℏ : ℝ) : ℂ)) * ((Real.exp (-S_I / ℏ) : ℝ) : ℂ)

/-- **[Port] The Born weight** `‖ψ‖ = e^{−S_I/ℏ}` — the phase factor is unimodular, leaving the
imaginary-action damping. -/
noncomputable def bornWeight (S_I ℏ : ℝ) : ℝ := Real.exp (-S_I / ℏ)

/-- **[Port — `path_amplitude_norm`] `‖ψ‖ = e^{−S_I/ℏ}`.** -/
theorem madelungAmplitude_norm (S_R S_I ℏ : ℝ) :
    ‖madelungAmplitude S_R S_I ℏ‖ = bornWeight S_I ℏ := by
  unfold madelungAmplitude bornWeight
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  exact Real.norm_of_nonneg (Real.exp_nonneg _)

/-- **[Port] The Born rule** `‖ψ‖² = e^{−2S_I/ℏ}` — the probability density is the squared Born weight. -/
theorem madelung_born_rule (S_R S_I ℏ : ℝ) :
    ‖madelungAmplitude S_R S_I ℏ‖ ^ 2 = Real.exp (-2 * S_I / ℏ) := by
  rw [madelungAmplitude_norm, bornWeight, sq, ← Real.exp_add]
  congr 1; ring

/-! ## §C — the lapse weight IS a Madelung pilot wave -/

/-- The complex-action/entropic-time master weight is the Madelung pilot-wave amplitude. -/
theorem complexActionPathIntegralWeight_eq_madelungAmplitude (S_R S_I ℏ : ℝ) :
    complexActionPathIntegralWeight S_R S_I ℏ = madelungAmplitude S_R S_I ℏ := by
  unfold complexActionPathIntegralWeight madelungAmplitude
  rw [sub_eq_add_neg, Complex.exp_add, Complex.ofReal_exp]
  congr 2
  push_cast; ring

/-- **[Link] The Banihashemi–Jacobson lapse weight is a de Broglie–Bohm pilot-wave amplitude.**
`lapseWeight N ε ℋ = madelungAmplitude (−Nℋ) (εℋ) 1`: real action `S_R = −Nℋ`, imaginary action
`S_I = εℋ`. -/
theorem lapseWeight_eq_madelungAmplitude (N ε Ham : ℝ) :
    lapseWeight N ε Ham = madelungAmplitude (-(N * Ham)) (ε * Ham) 1 := by
  rw [lapseWeight_eq_master, complexActionPathIntegralWeight_eq_madelungAmplitude]

/-- **[Link] The lapse Born weight** `‖lapseWeight N ε ℋ‖ = e^{−εℋ}` — the lapse modulus is the Bohmian
Born weight at imaginary action `S_I = εℋ`. -/
theorem lapse_bornWeight (N ε Ham : ℝ) :
    ‖lapseWeight N ε Ham‖ = bornWeight (ε * Ham) 1 := by
  rw [lapseWeight_eq_madelungAmplitude, madelungAmplitude_norm]

/-- **[Link] The lapse Born rule** `‖lapseWeight N ε ℋ‖² = e^{−2εℋ}` — the de Broglie–Bohm probability
density of the lapse-displaced path integral. -/
theorem lapse_born_rule (N ε Ham : ℝ) :
    ‖lapseWeight N ε Ham‖ ^ 2 = Real.exp (-2 * (ε * Ham) / 1) := by
  rw [lapseWeight_eq_madelungAmplitude, madelung_born_rule]

/-! ## §D — the lapse quantum potential and the classical limit -/

/-- **[Link] The lapse imaginary action is the Bohmian quantum potential** `Q = εℋ·ℏ/(2m)`. -/
theorem lapse_quantumPotential (ε Ham ℏ m : ℝ) :
    bohmQuantumPotential (ε * Ham) ℏ m = (ε * Ham) * ℏ / (2 * m) := rfl

/-- **[Link — the classical limit is the reversible contour] `Q = 0 ⟺ ε = 0`** (for `ℋ ≠ 0`). The de
Broglie–Bohm classical limit of the lapse-displaced path integral is exactly the reversible lapse contour
`ε = 0` (`GravLapse.ContourEntropicTime.lapse_real_contour_reversible`): no `iε` displacement ⟺ no Bohmian
guide ⟺ no entropy production. -/
theorem lapse_classical_limit_iff_reversible (ε Ham ℏ m : ℝ) (hℏ : ℏ ≠ 0) (hm : 0 < m) (hH : Ham ≠ 0) :
    bohmQuantumPotential (ε * Ham) ℏ m = 0 ↔ ε = 0 := by
  rw [bohmQuantumPotential_zero_iff (ε * Ham) ℏ m hℏ hm, mul_eq_zero]
  constructor
  · rintro (h | h); exact h; exact absurd h hH
  · intro h; exact Or.inl h

/-! ## §E — the Bohmian guidance velocity is the rapidity / diamond velocity -/

/-- **[Link to `GravLapse.HyperbolicInterval`] The Bohmian guidance velocity is the rapidity
velocity.** On the mass shell (`N = Δcosh θ`, `ε = Δsinh θ`) the de Broglie–Bohm guidance velocity is the
displacement ratio `ε/N = tanh θ` — the causal-diamond / Bogoliubov velocity (`lapse_velocity_eq_rapidity`). -/
theorem lapse_bohm_velocity_eq_tanh (Δ θ : ℝ) (hΔ : Δ ≠ 0) :
    (Δ * Real.sinh θ) / (Δ * Real.cosh θ) = Real.tanh θ :=
  lapse_velocity_eq_rapidity Δ θ hΔ

/-- **[Main result] The mass-shell lapse mode is a de Broglie–Bohm pilot wave with hyperbolic data.** For the
lapse `N − iε` at `(N, ε) = (Δcosh θ, Δsinh θ)`:

* Born weight `‖lapseWeight‖ = e^{−Δsinh θ·ℋ}` (the gap `Δsinh θ` drives the damping);
* quantum potential `Q = (Δsinh θ·ℋ)·ℏ/(2m)` (the imaginary action is the Bohmian guide);
* guidance velocity `ε/N = tanh θ` (the rapidity / diamond velocity).

At the rest frame `θ = 0` (`sinh 0 = 0`) the gap vanishes: `Q = 0`, velocity `0`, Born weight `1` — the
classical / reversible limit. The single rapidity `θ` controls both the kinematic velocity and the Bohmian
quantum potential. -/
theorem lapse_bohm_hyperbolic (Δ θ Ham ℏ m : ℝ) (hΔ : Δ ≠ 0) :
    ‖lapseWeight (Δ * Real.cosh θ) (Δ * Real.sinh θ) Ham‖ = bornWeight (Δ * Real.sinh θ * Ham) 1
      ∧ bohmQuantumPotential (Δ * Real.sinh θ * Ham) ℏ m = (Δ * Real.sinh θ * Ham) * ℏ / (2 * m)
      ∧ (Δ * Real.sinh θ) / (Δ * Real.cosh θ) = Real.tanh θ :=
  ⟨lapse_bornWeight _ _ _, rfl, lapse_velocity_eq_rapidity Δ θ hΔ⟩

/-! ## §F — the quantum potential rederived from the Nagao–Nielsen contour (the gap) -/

/-- **[Derive] The Nagao–Nielsen imaginary action is the gap × evolution time** `S_I = E_I·t`. **Here `t` is
the ordinary Schrödinger evolution (coordinate) time** — the parameter of the eigen-propagator
`u(t) = e^{−iE_C t/ℏ}` (`WickRotation.evolutionFactor`, `iℏ ∂_t ψ = H_C ψ`), the dual of the ADM lapse `N`
in the lapse formulation. It is **not** the entropic time: `t` is the *input* coordinate clock, and the
imaginary action `S_I = E_I·t` is the gap `E_I = Im(E_C)` accumulated over it. The entropic time is the
*derived* quantity `τ_ent = S_I/ℏ = E_I·t/ℏ` (§H, `nnEntropicTime`), the entropic clock running at rate
`E_I/ℏ` relative to `t`. The non-Hermitian contour energy `E_C = E_R − iE_I` (`complexEnergy`) drives the
propagator whose modulus is `e^{−E_I·t/ℏ}` (`norm_evolutionFactor`). -/
noncomputable def nnImaginaryAction (E_I t : ℝ) : ℝ := E_I * t

/-- **[Derive] The Nagao–Nielsen contour propagator's modulus IS the Bohmian Born weight.**
`‖evolutionFactor E_R E_I ℏ t‖ = bornWeight (E_I·t) ℏ = e^{−E_I·t/ℏ}` (`norm_evolutionFactor`): the NN
non-Hermitian eigen-propagator is a de Broglie–Bohm pilot wave with imaginary action `S_I = E_I·t`. -/
theorem nnContour_bornWeight (E_R E_I ℏ t : ℝ) :
    ‖evolutionFactor E_R E_I ℏ t‖ = bornWeight (nnImaginaryAction E_I t) ℏ := by
  rw [norm_evolutionFactor, bornWeight, nnImaginaryAction]; congr 1; ring

/-- **[Derive `_nonneg` from NN convergence] `Q ≥ 0` because the NN gap is non-negative.** With
`S_I = E_I·t`, the de Broglie–Bohm quantum potential `Q = E_I·t·ℏ/(2m) ≥ 0` is rederived from the
Nagao–Nielsen convergence condition: the gap `E_I ≥ 0` (the contour converges, the propagator decays). -/
theorem nnContour_quantumPotential_nonneg (E_I t ℏ m : ℝ)
    (hE : 0 ≤ E_I) (ht : 0 ≤ t) (hℏ : 0 ≤ ℏ) (hm : 0 < m) :
    0 ≤ bohmQuantumPotential (nnImaginaryAction E_I t) ℏ m :=
  bohmQuantumPotential_nonneg _ ℏ m (mul_nonneg hE ht) hℏ hm

/-- **[Derive `_zero_iff` from NN reversibility] `Q = 0 ⟺ E_I = 0`** (the gap vanishes). With `S_I = E_I·t`
and `t ≠ 0`, the de Broglie–Bohm classical limit `Q = 0` is rederived as the Nagao–Nielsen reversible fiber:
the gap `E_I = 0`, i.e. the energy is real and the evolution unitary (`complexEnergy_at_E_I_zero`). -/
theorem nnContour_quantumPotential_zero_iff (E_I t ℏ m : ℝ)
    (ht : t ≠ 0) (hℏ : ℏ ≠ 0) (hm : 0 < m) :
    bohmQuantumPotential (nnImaginaryAction E_I t) ℏ m = 0 ↔ E_I = 0 := by
  rw [bohmQuantumPotential_zero_iff _ ℏ m hℏ hm, nnImaginaryAction, mul_eq_zero]
  constructor
  · rintro (h | h); exact h; exact absurd h ht
  · intro h; exact Or.inl h

/-! ## §G — the quantum potential rederived from the complex oscillator (the imaginary potential) -/

/-- **[Derive] The complex-oscillator imaginary action is `−V_I·t`.** The Nagao–Nielsen complex oscillator
has imaginary potential `V_I = ½ Im(mω²) q²` (`ComplexOscillator.PhaseDiagram.oscillatorPotentialIm`); the
dissipative imaginary action accumulated over time `t` is `S_I = −V_I·t` (the action `∫(−V_I)dt`). This is
the oscillator's source for the de Broglie–Bohm `S_I`. -/
noncomputable def oscillatorImaginaryAction (m ω : ℂ) (q t : ℝ) : ℝ :=
  -(oscillatorPotentialIm m ω q) * t

/-- **[Derive `_nonneg` from oscillator convergence] `Q ≥ 0` because the oscillator's `V_I ≤ 0`.** With
`S_I = −V_I·t`, the de Broglie–Bohm quantum potential is non-negative, rederived from the complex-oscillator
convergence condition `oscillatorPotentialConverges` (`Im(mω²) ≤ 0 ⟺ V_I ≤ 0`,
`potentialConverges_iff_potentialIm_nonpos`): a convergent (sensible-boson) oscillator gives a non-negative
Bohmian quantum potential. -/
theorem oscillator_quantumPotential_nonneg (m ω : ℂ) (q t ℏ mass : ℝ)
    (hq : q ≠ 0) (hconv : oscillatorPotentialConverges m ω) (ht : 0 ≤ t) (hℏ : 0 ≤ ℏ) (hmass : 0 < mass) :
    0 ≤ bohmQuantumPotential (oscillatorImaginaryAction m ω q t) ℏ mass := by
  have hVI : oscillatorPotentialIm m ω q ≤ 0 :=
    (potentialConverges_iff_potentialIm_nonpos m ω hq).mp hconv
  exact bohmQuantumPotential_nonneg _ ℏ mass (mul_nonneg (by linarith) ht) hℏ hmass

/-- **[Derive `_zero_iff` from oscillator reversibility] `Q = 0 ⟺ V_I = 0`** (the oscillator's imaginary
potential vanishes). With `S_I = −V_I·t` and `t ≠ 0`, the de Broglie–Bohm classical limit is rederived as
the complex-oscillator reversible boundary `V_I = 0` — the phase-diagram regions `φ = 0` / `φ = π` of a
real harmonic oscillator (`ComplexOscillator.PhaseDiagram`, `ThermoFieldDynamics.RealHOWick`). -/
theorem oscillator_quantumPotential_zero_iff (m ω : ℂ) (q t ℏ mass : ℝ)
    (ht : t ≠ 0) (hℏ : ℏ ≠ 0) (hmass : 0 < mass) :
    bohmQuantumPotential (oscillatorImaginaryAction m ω q t) ℏ mass = 0
      ↔ oscillatorPotentialIm m ω q = 0 := by
  rw [bohmQuantumPotential_zero_iff _ ℏ mass hℏ hmass, oscillatorImaginaryAction, mul_eq_zero,
    neg_eq_zero]
  constructor
  · rintro (h | h); exact h; exact absurd h ht
  · intro h; exact Or.inl h

/-! ## §H — clarifying the clock: coordinate time `t` vs the entropic time `τ_ent`

The `t` of §F (and §G) is the **ordinary Schrödinger evolution / coordinate time** — the parameter of the
propagator `u(t) = e^{−iE_C t/ℏ}`. It is the *input* clock, not the entropic time. The **entropic time** is
the *derived* relational quantity `τ_ent := S_I/ℏ`: with `S_I = E_I·t` (the NN gap accumulated over
coordinate time), `τ_ent = E_I·t/ℏ`. Two distinct clocks: `t` ticks externally; `τ_ent` is the
entropy-production readout that the imaginary action defines. The Born weight is `e^{−τ_ent}`, and the
quantum potential is `Q = τ_ent·ℏ²/(2m)`. -/

/-- **[Clarify] The entropic time** `τ_ent = S_I/ℏ` — the *derived* entropic clock, **not** the coordinate
time `t`. By definition `nnEntropicTime E_I t ℏ = (E_I·t)/ℏ = nnImaginaryAction E_I t / ℏ`: the gap `E_I`
times the coordinate time `t`, normalised by `ℏ`. -/
noncomputable def nnEntropicTime (E_I t ℏ : ℝ) : ℝ := nnImaginaryAction E_I t / ℏ

/-- **[Clarify] The propagator's Born weight is `e^{−τ_ent}`** — the *entropic* time, not the coordinate
time, is the damping exponent: `‖evolutionFactor E_R E_I ℏ t‖ = e^{−τ_ent}` with `τ_ent = E_I·t/ℏ`. The
coordinate clock `t` enters only through `τ_ent`. -/
theorem nnContour_bornWeight_eq_exp_neg_entropicTime (E_R E_I ℏ t : ℝ) :
    ‖evolutionFactor E_R E_I ℏ t‖ = Real.exp (-nnEntropicTime E_I t ℏ) := by
  rw [norm_evolutionFactor, nnEntropicTime, nnImaginaryAction]

/-- **[Clarify — canonical model] The propagator's Born weight is the entropic damping.**
`‖evolutionFactor E_R E_I ℏ t‖ = entropyDamping (E_I·t) ℏ` (`WickRotation.entropyDamping = e^{−S_I/ℏ}`): the
Born weight, the Bohmian `R = e^{−S_I/ℏ}`, and the arc's entropic-damping factor coincide, all read off the
entropic time `τ_ent = E_I·t/ℏ`. -/
theorem nnContour_bornWeight_eq_entropyDamping (E_R E_I ℏ t : ℝ) :
    ‖evolutionFactor E_R E_I ℏ t‖ = entropyDamping (nnImaginaryAction E_I t) ℏ := by
  rw [norm_evolutionFactor, entropyDamping, nnImaginaryAction]

/-- **[Clarify] The quantum potential in terms of the entropic time** `Q = τ_ent·ℏ²/(2m)`. The Bohmian
guide is set by the *entropic* time, not the coordinate time directly. -/
theorem nnContour_quantumPotential_eq_entropicTime (E_I t ℏ m : ℝ) :
    bohmQuantumPotential (nnImaginaryAction E_I t) ℏ m = nnEntropicTime E_I t ℏ * ℏ ^ 2 / (2 * m) := by
  unfold bohmQuantumPotential nnEntropicTime nnImaginaryAction
  field_simp

/-! ## §I — the imaginary action is the contour gap × conjugate (lapse / propagator duality)

Formalizes the reasoning that resolved the clock question: the imaginary action `S_I` is the **imaginary
part of the complex action** `S = −(contour point)·(conjugate variable)`, where the **contour point**
`complexEnergy a g = a − ig` (`WickRotation`, the same point whose interval is `lorentzianForm = a² − g²`)
includes the imaginary part `−g` (the gap), and the conjugate variable `c` is real. Then
`S_I = Im(S) = g·c`. The lapse and the propagator are the *two dual instances* of this single contour
structure:

* **lapse** — `contour point = N − iε` (complex lapse / time), `conjugate = ℋ` (real energy), gap `= ε`:
  `S_I = εℋ`;
* **propagator** — `contour point = E_R − iE_I` (complex energy), `conjugate = t` (real coordinate time),
  gap `= E_I`: `S_I = E_I·t = nnImaginaryAction`.

Neither the lapse `N` nor the coordinate time `t` is the entropic time; the entropic time is the derived
`τ_ent = S_I/ℏ` (§H). The gap is what lives on the contour. -/

/-- **[Reasoning] The complex action** `S = −(contour point)·(conjugate variable)`. The contour point
`complexEnergy a g = a − ig` is multiplied by the real conjugate variable `c` (the energy `ℋ` for the lapse,
the coordinate time `t` for the propagator). -/
noncomputable def complexAction (a g c : ℝ) : ℂ := -(complexEnergy a g) * (c : ℂ)

/-- **[Reasoning] The imaginary action is the gap times the conjugate** `S_I = Im(S) = g·c`. This is the
content that resolved the clock question: `S_I` is the imaginary part of the complex action, with the gap
`g` (the contour point's spacelike leg) as the source. -/
theorem complexAction_im (a g c : ℝ) : (complexAction a g c).im = g * c := by
  unfold complexAction complexEnergy
  simp [Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **[Reasoning] The real action is `S_R = −(a·c)`** — the reversible part (real contour component `a`
times the conjugate `c`). -/
theorem complexAction_re (a g c : ℝ) : (complexAction a g c).re = -(a * c) := by
  unfold complexAction complexEnergy
  simp [Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **[Reasoning] The imaginary action is `(−Im of the contour point)·c`.** `S_I = (−(complexEnergy a g).im)·c
= g·c`: the gap `g = −Im(contour point)` (`lapse_im_eq_gap`) is what the contour contributes to the
imaginary action. -/
theorem complexAction_im_eq_neg_contourIm (a g c : ℝ) :
    (complexAction a g c).im = (-(complexEnergy a g).im) * c := by
  rw [complexAction_im, lapse_im_eq_gap]; ring

/-- **[Lapse instance] `S_I = εℋ`.** Contour point `= N − iε` (the complex lapse), conjugate `= ℋ` (the
Hamiltonian constraint), gap `= ε` (the `iε` displacement): the lapse imaginary action. -/
theorem lapse_imaginaryAction (N ε Ham : ℝ) : (complexAction N ε Ham).im = ε * Ham :=
  complexAction_im N ε Ham

/-- **[Propagator instance] `S_I = E_I·t = nnImaginaryAction`.** Contour point `= E_R − iE_I` (the complex
energy), conjugate `= t` (the coordinate time), gap `= E_I` (the non-Hermitian gap): the propagator
imaginary action of §F. The lapse and the propagator are the same `complexAction_im` with the gap moved from
the time leg to the energy leg. -/
theorem propagator_imaginaryAction (E_R E_I t : ℝ) :
    (complexAction E_R E_I t).im = nnImaginaryAction E_I t := by
  rw [complexAction_im, nnImaginaryAction]

/-- **[Reasoning — the contour ties interval and action] The contour interval and the imaginary action share
the gap `g`.** The same contour point `complexEnergy a g` has Minkowski interval `lorentzianForm = a² − g²`
(`GravLapse.ContourEntropicTime.lapse_lorentzianForm_eq`) and complex action with imaginary part `g·c`: the
spacelike leg `g` of the contour is both the interval's imaginary direction and the imaginary-action source.
This is why the gap (lapse `ε`, propagator `E_I`) is the single dissipative/entropic direction. -/
theorem contour_interval_and_action (a g c : ℝ) :
    lorentzianForm (complexEnergy a g) = a ^ 2 - g ^ 2 ∧ (complexAction a g c).im = g * c :=
  ⟨lapse_lorentzianForm_eq a g, complexAction_im a g c⟩

/-! ## §J — constructing a lapse from the Nagao–Nielsen complex via the Bohm polar form

The Bohm polar transform writes a wave amplitude as `ψ = R·e^{iS/ℏ}` with modulus `R` and phase `S`. Applied
to the Nagao–Nielsen complex weight `e^{(i/ℏ)S_complex}` (`S_complex = S_R + iS_I`) it gives `R = e^{−S_I/ℏ}`
(amplitude) and phase `S_R`. **This section constructs the complex lapse that realises that polar form.**
Inverting §I (`S_complex = −(contour point)·ℋ`), the lapse is `N_c = −S_complex/ℋ`: real lapse `N = −S_R/ℋ`,
gap `ε = S_I/ℋ`. Its lapse weight is exactly the Nagao–Nielsen Bohm pilot wave `madelungAmplitude S_R S_I`,
and its complex action recovers `S_complex`. -/

/-- **[Construct] The Bohm-polar lapse from the Nagao–Nielsen complex action.** Given `S_complex = S_R + iS_I`
and a constraint scale `ℋ`, the constructed complex lapse is `N_c = −S_complex/ℋ = (−S_R/ℋ) − i(S_I/ℋ)`
(`complexEnergy (−S_R/ℋ) (S_I/ℋ)`): real lapse `N = −S_R/ℋ`, gap `ε = S_I/ℋ` (the imaginary action /
constraint). -/
noncomputable def bohmLapse (S_R S_I Ham : ℝ) : ℂ := complexEnergy (-S_R / Ham) (S_I / Ham)

/-- The constructed lapse's timelike leg is the (negated) real action over the constraint, `N = −S_R/ℋ`. -/
theorem bohmLapse_re (S_R S_I Ham : ℝ) : (bohmLapse S_R S_I Ham).re = -S_R / Ham :=
  lapse_re_eq _ _

/-- The constructed lapse's spacelike leg (the gap) is the imaginary action over the constraint,
`Im = −(S_I/ℋ)` — `ε = S_I/ℋ` is the Bohm amplitude exponent `R = e^{−S_I/ℏ}` per unit constraint
(`lapse_im_eq_gap`). -/
theorem bohmLapse_im_eq_gap (S_R S_I Ham : ℝ) : (bohmLapse S_R S_I Ham).im = -(S_I / Ham) :=
  lapse_im_eq_gap _ _

/-- **The lapse weight of the Bohm-polar lapse.** -/
noncomputable def bohmLapseWeight (S_R S_I Ham : ℝ) : ℂ := lapseWeight (-S_R / Ham) (S_I / Ham) Ham

/-- **[Construct — the defining property] The Bohm-polar lapse weight IS the Nagao–Nielsen Bohm pilot
wave.** `bohmLapseWeight S_R S_I ℋ = madelungAmplitude S_R S_I 1 = e^{iS_R}·e^{−S_I}`: the lapse built from
the NN complex action via the Bohm polar form reproduces the NN Bohm pilot-wave amplitude (modulus
`R = e^{−S_I}`, phase `S_R`). The constraint `ℋ` cancels. -/
theorem bohmLapseWeight_eq_madelung (S_R S_I Ham : ℝ) (h : Ham ≠ 0) :
    bohmLapseWeight S_R S_I Ham = madelungAmplitude S_R S_I 1 := by
  unfold bohmLapseWeight
  rw [lapseWeight_eq_madelungAmplitude]
  congr 1 <;> field_simp

/-- **[Construct — self-consistency] The complex action of the Bohm-polar lapse recovers `S_complex`.**
`complexAction (−S_R/ℋ) (S_I/ℋ) ℋ = S_R + iS_I`: applying the §I complex-action map `−(contour point)·ℋ` to
the constructed lapse returns the original Nagao–Nielsen complex action. The construction is invertible. -/
theorem bohmLapse_recovers_action (S_R S_I Ham : ℝ) (h : Ham ≠ 0) :
    complexAction (-S_R / Ham) (S_I / Ham) Ham = (S_R : ℂ) + Complex.I * (S_I : ℂ) := by
  have hc : (Ham : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  unfold complexAction complexEnergy
  push_cast
  field_simp
  ring

/-- **[Construct] The Bohm-polar lapse's Born weight is the Bohm amplitude** `‖bohmLapseWeight‖ = e^{−S_I}`
(`R = e^{−S_I/ℏ}` at `ℏ = 1`): the dissipative amplitude of the Nagao–Nielsen pilot wave. -/
theorem bohmLapse_bornWeight (S_R S_I Ham : ℝ) (h : Ham ≠ 0) :
    ‖bohmLapseWeight S_R S_I Ham‖ = bornWeight S_I 1 := by
  rw [bohmLapseWeight_eq_madelung _ _ _ h, madelungAmplitude_norm]

/-- **[Construct — spacetime interval] The Bohm-polar lapse's spacetime interval is the NN action's
interval.** `lorentzianForm(bohmLapse) = (S_R² − S_I²)/ℋ²`: the constructed lapse's Minkowski interval
(`lapse_lorentzianForm_eq`) is the difference of squares of the real and imaginary actions, scaled by the
constraint — timelike when `|S_R| > |S_I|` (reversible-dominated), spacelike when `|S_I| > |S_R|`. -/
theorem bohmLapse_lorentzianForm (S_R S_I Ham : ℝ) :
    lorentzianForm (bohmLapse S_R S_I Ham) = (S_R ^ 2 - S_I ^ 2) / Ham ^ 2 := by
  unfold bohmLapse
  rw [lapse_lorentzianForm_eq]
  ring

/-- **[Un-float — round-trip with the lapse arc] `bohmLapse` is the exact inverse of the lapse → action
map.** Feeding the *actual* lapse's Nagao–Nielsen action `(S_R, S_I) = (−Nℋ, εℋ)`
(`GravLapse.ContourMaster.lapseWeight_eq_master`) back into the construction recovers the original complex
lapse: `bohmLapse (−Nℋ) (εℋ) ℋ = complexEnergy N ε`. So `bohmLapse` is not a free construction — it is the
inverse of the existing lapse machinery. -/
theorem bohmLapse_inverts_lapseAction (N ε Ham : ℝ) (h : Ham ≠ 0) :
    bohmLapse (-(N * Ham)) (ε * Ham) Ham = complexEnergy N ε := by
  unfold bohmLapse
  congr 1 <;> field_simp

/-- **[Un-float — canonical NN weight] The Bohm-polar lapse weight is the Nagao–Nielsen complex-action weight.**
`bohmLapseWeight S_R S_I ℋ = nagaoNielsenComplexActionWeight S_R S_I 1` (`PathIntegral.ComplexActionPathIntegralWeight`): the constructed
lapse's weight is the canonical NN complex-action weight `e^{(i/ℏ)S_complex}`, not a bespoke object. -/
theorem bohmLapseWeight_eq_nagaoNielsen (S_R S_I Ham : ℝ) (h : Ham ≠ 0) :
    bohmLapseWeight S_R S_I Ham = nagaoNielsenComplexActionWeight S_R S_I 1 := by
  rw [bohmLapseWeight_eq_madelung _ _ _ h, ← complexActionPathIntegralWeight_eq_madelungAmplitude,
    ← nagaoNielsen_eq_master _ _ _ one_ne_zero]

/-- **[Un-float — reversible / classical fiber] The Bohm-polar lapse weight is unimodular iff the imaginary
action vanishes.** `‖bohmLapseWeight S_R S_I ℋ‖ = 1 ⟺ S_I = 0`: the constructed lapse is reversible
(pure phase, no Born damping, no Bohmian guide) exactly on the `S_I = 0` fiber — the same reversible fiber
as `GravLapse.ContourEntropicTime.lapse_real_contour_reversible` and the de Broglie–Bohm classical limit. -/
theorem bohmLapseWeight_unimodular_iff (S_R S_I Ham : ℝ) (h : Ham ≠ 0) :
    ‖bohmLapseWeight S_R S_I Ham‖ = 1 ↔ S_I = 0 := by
  rw [bohmLapse_bornWeight _ _ _ h, bornWeight, Real.exp_eq_one_iff]
  constructor
  · intro h2; linarith [h2]
  · intro h2; rw [h2]; norm_num

end Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential

end

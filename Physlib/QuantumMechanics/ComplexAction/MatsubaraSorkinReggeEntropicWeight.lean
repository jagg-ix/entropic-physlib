/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional
public import Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality
public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston

/-!
# One entropic weight, four path integrals: Matsubara, Sorkin, Regge, Caldeira–Leggett

This module **links** three further path-integral / action families to the entropic-weight hub already carrying the
Caldeira–Leggett arc — the canonical `PathIntegral.ComplexActionPathIntegralWeight.kuikenWeight = exp(−S_I)`
(the modulus of the master complex-action weight `exp[(i/ℏ)S_R − (1/ℏ)S_I]`, `master_modulus_is_kuiken`). Each of
the four families is a *different physical incarnation of the same imaginary (entropic) action* `S_I`:

| family | module | entropic action `S_I` |
|---|---|---|
| **Matsubara** (imaginary-time thermal) | `ThermoFieldDynamics.MatsubaraThermalOscillator` | `β E` (thermal, `= 1/kT · E`) |
| **Regge** (Lorentzian deficit gravity) | `ComplexReggeActionCausality` | `A · Im ε_L` (geometric, light-cone crossings) |
| **Sorkin** (consistent-histories) | `DecoherenceFunctionalSorkinJohnston` | `S_ent` (entanglement) |
| **Caldeira–Leggett** (open system) | `CaldeiraLeggettInfluenceFunctional` | `W_R` (decoherence) |

Each family's weight is proved equal to `kuikenWeight 1 (·)` of its own `S_I`, so they coincide whenever their
imaginary actions do — one entropic weight `exp(−S_I)`, four physics readings. The reversible (unitary) limit
`S_I = 0` gives modulus `1` (pure phase) in every case: thermal `βE → 0` (high `T`), Regge `N_c = 4` (causally
regular), Sorkin `S_ent = 0` (no environment), CL `W_R = 0` (diagonal `x = x̃`).

* **§A — each path integral is the entropic weight.** `matsubara_boltzmann_is_kuiken`,
  `regge_amplitude_is_kuiken`, `sorkin_historyWeight_born_is_kuiken`, `caldeiraLeggett_feynmanVernon_is_kuiken`.
* **§B — the unification.** **`four_actions_one_entropic_weight`** — a common `S_I` makes all four weights equal.

**Honest layering.** Exact `Real.exp` / `ring` identities reducing each family's weight to `kuikenWeight`; the
physics of each `S_I` (thermal propagator, Lorentzian deficit angle, Sorkin decoherence functional, influence
functional) is developed in the respective modules and reused, not re-derived.

## References

* Reuses `MatsubaraThermalOscillator`, `ComplexReggeActionCausality`, `DecoherenceFunctionalSorkinJohnston`,
  `CaldeiraLeggettInfluenceFunctional`, all on `PathIntegral.ComplexActionPathIntegralWeight`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatsubaraSorkinReggeEntropicWeight


/-- **Matsubara = entropic weight** — the imaginary-time thermal Boltzmann weight `e^{−βE}` is
`kuikenWeight 1 (βE)`: the entropic damping with thermal imaginary action `S_I = βE`. -/
lemma matsubara_boltzmann_is_kuiken (β E : ℝ) :
    matsubaraBoltzmannWeight β E = kuikenWeight 1 (β * E) := by
  rw [matsubaraBoltzmannWeight, kuikenWeight, div_one]

/-- **Regge = entropic weight** — the Lorentzian-deficit causality amplitude `e^{−A·Im ε_L}` is
`kuikenWeight 1 (A · Im ε_L)`: the entropic damping with geometric imaginary action `S_I = A·Im ε_L`
(the light-cone-crossing deficit). -/
lemma regge_amplitude_is_kuiken (area : ℝ) (Nc : ℕ) :
    deficitAmplitude area Nc = kuikenWeight 1 (area * lorentzianDeficitImaginary Nc) := by
  rw [deficitAmplitude, kuikenWeight, div_one]
  congr 1
  ring

/-- **Sorkin = entropic weight** — the consistent-histories Born weight `|w|² = e^{−S_ent}` of the
Sorkin–Johnston decoherence functional's history weight is `kuikenWeight 1 (S_ent)`: the entropic damping with
entanglement imaginary action `S_I = S_ent`. -/
lemma sorkin_historyWeight_born_is_kuiken (S_R S_ent ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    Complex.normSq (historyWeight S_R S_ent ℏ) = kuikenWeight 1 S_ent := by
  rw [historyWeight_born S_R S_ent ℏ hℏ, kuikenWeight, div_one]

/-- **Caldeira–Leggett = entropic weight** — the Feynman–Vernon influence functional's modulus (at `ℏ = 1`, the
paper's convention) is `kuikenWeight 1 (W_R)`: the entropic damping with decoherence imaginary action
`S_I = W_R = (2Mγ/β) ξ² t`. -/
lemma caldeiraLeggett_feynmanVernon_is_kuiken (S_R M γ β ξ t : ℝ) :
    ‖feynmanVernonWeight S_R (decoherenceExponentIF M γ β ξ t) 1‖
      = kuikenWeight 1 (decoherenceExponentIF M γ β ξ t) :=
  feynmanVernon_modulus_is_decoherence S_R M γ β ξ t 1


/-- **Four path integrals, one entropic weight** — when the thermal (`βE`), geometric (`A·Im ε_L`), entanglement
(`S_ent`) and decoherence (`W_R`) imaginary actions all equal a common `S_I`, the Matsubara thermal weight, the
Regge causality amplitude, the Sorkin Born weight and the Caldeira–Leggett Feynman–Vernon modulus **all coincide**
with `kuikenWeight 1 S_I = exp(−S_I)`. The imaginary-time/thermal, gravitational, consistent-histories and
open-system path integrals are one entropic damping, read four ways. -/
lemma four_actions_one_entropic_weight
    (S_I β E area S_R S_ent M γ βcl ξ t : ℝ) (Nc : ℕ) (hℏ : (1 : ℝ) ≠ 0)
    (hMatsubara : β * E = S_I) (hRegge : area * lorentzianDeficitImaginary Nc = S_I)
    (hSorkin : S_ent = S_I) (hCL : decoherenceExponentIF M γ βcl ξ t = S_I) :
    matsubaraBoltzmannWeight β E = kuikenWeight 1 S_I
      ∧ deficitAmplitude area Nc = kuikenWeight 1 S_I
      ∧ Complex.normSq (historyWeight S_R S_ent 1) = kuikenWeight 1 S_I
      ∧ ‖feynmanVernonWeight S_R (decoherenceExponentIF M γ βcl ξ t) 1‖ = kuikenWeight 1 S_I := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [matsubara_boltzmann_is_kuiken, hMatsubara]
  · rw [regge_amplitude_is_kuiken, hRegge]
  · rw [sorkin_historyWeight_born_is_kuiken S_R S_ent 1 hℏ, hSorkin]
  · rw [caldeiraLeggett_feynmanVernon_is_kuiken, hCL]

end Physlib.QuantumMechanics.ComplexAction.MatsubaraSorkinReggeEntropicWeight

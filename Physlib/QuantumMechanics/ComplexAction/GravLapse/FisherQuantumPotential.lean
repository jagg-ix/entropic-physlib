/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential
public import Physlib.StatisticalMechanics.FisherInformationCoercivity

/-!
# The quantum potential is the Fisher information — no pilot wave assumed

The de Broglie–Bohm quantum potential `Q = S_I·ℏ/(2m)` of `GravLapse.BohmQuantumPotential` was
introduced through the Madelung/pilot-wave amplitude `R = e^{−S_I/ℏ}`. That framing is
interpretation-laden. This file replaces it with the **interpretation-neutral** identification: the
imaginary action `S_I` is the **Fisher information** of the probability density,
`S_I[Φ] = I(p) = ∫|∇log p|²·p` (`Physlib.StatisticalMechanics.FisherInformationCoercivity`), and the
quantum potential is `Q = (ℏ/2m)·I(p)` (de Bruijn / Stam). Its non-negativity is then a *statistical* fact
about any probability density (`fisherInfo_nonneg`), not a feature of a hypothetical pilot wave.

* **§A — the quantum potential is the Fisher information** (`fisherQuantumPotential`,
  `fisherQuantumPotential_eq`, `fisherQuantumPotential_nonneg`). `Q = I(p)·ℏ/(2m)`, with `Q ≥ 0` derived
  from `FisherInformationData.fisherInfo_nonneg` — the Fisher information of a probability density is
  non-negative, so the quantum potential is non-negative without any wavefunction.
* **§B — de Bruijn: the quantum potential is twice the entropy-production rate**
  (`fisherQuantumPotential_eq_two_deBruijn`). Under heat-equation evolution `∂ₜp = DΔp` with `D = ℏ/(2m)`,
  the de Bruijn identity is `dH/dt = (D/2)·I(p)`; hence `Q = (ℏ/2m)·I(p) = 2·(dH/dt)`. The quantum potential
  is twice the rate of differential-entropy production — a purely information-theoretic reading.
* **§C — the Fisher imaginary action is UV-coercive** (`fisherImaginaryAction_coercive`). The Fisher
  imaginary action satisfies `S_I = I(p) ≥ (p_min·k_UV²)·‖Φ‖²_UV` (`fisher_info_coercivity`): coercivity
  comes from a density floor and a Poincaré spectral gap, again with no pilot wave.
* **§D — the lapse imaginary action as Fisher information** (`lapse_quantumPotential_is_fisher`,
  `lapse_quantumPotential_nonneg_from_fisher`). When the lapse imaginary action `εℋ` is identified with the
  Fisher information `I(p)`, the lapse quantum potential is the Fisher quantum potential, and its
  non-negativity is Fisher non-negativity — replacing the pilot-wave assumption for the lapse contour.
* **§E — linking the Fisher quantum potential to the Bohm-Q machinery** (`fisherQuantumPotential_zero_iff`,
  `fisherQuantumPotential_zero_implies_uniform`, `fisherBornWeight`, `nnContour_quantumPotential_is_fisher`,
  `oscillator_quantumPotential_is_fisher`). The Fisher quantum potential is no longer isolated: its classical
  limit is `I(p) = 0` (zero Fisher information = uniform density, the no-information state); its Born weight
  is `e^{−I(p)/ℏ}`; and the §F NN-contour and §G complex-oscillator quantum potentials are the Fisher quantum
  potential whenever their imaginary actions equal `I(p)`.

## References

* B. R. Frieden, *Physics from Fisher Information* (1998); M. J. W. Hall, M. Reginatto,
  *Schrödinger equation from an exact uncertainty principle*, J. Phys. A 35 (2002) 3289 — the quantum
  potential as Fisher information.
* J.-P. Badiali — Schrödinger from entropy / Fisher information (the de Bruijn `dH/dt = (D/2)I(p)`).
* Repo dependencies: `Physlib.StatisticalMechanics.FisherInformationCoercivity`
  (`FisherInformationData`, `fisherInfo_nonneg`, `fisher_info_coercivity`),
  `GravLapse.BohmQuantumPotential` (`bohmQuantumPotential`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.FisherQuantumPotential

open Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential
open Physlib.StatisticalMechanics

variable {Φ : Type}

/-! ## §A — the quantum potential is the Fisher information (no pilot wave) -/

/-- **[Interpretation-neutral] The quantum potential with the Fisher-information imaginary action.** Taking
`S_I = I(p) = ∫|∇log p|²·p` (`FisherInformationData.fisherInfo`), the de Broglie–Bohm quantum potential is
`Q = I(p)·ℏ/(2m)` — the Fisher information of the density times `ℏ/(2m)`, with no pilot-wave amplitude. -/
noncomputable def fisherQuantumPotential (data : FisherInformationData Φ) (φ : Φ) (ℏ m : ℝ) : ℝ :=
  bohmQuantumPotential (data.fisherInfo φ) ℏ m

/-- `Q = I(p)·ℏ/(2m)`. -/
theorem fisherQuantumPotential_eq (data : FisherInformationData Φ) (φ : Φ) (ℏ m : ℝ) :
    fisherQuantumPotential data φ ℏ m = data.fisherInfo φ * ℏ / (2 * m) := rfl

/-- **[No pilot wave] The quantum potential is non-negative from Fisher-information non-negativity.**
`Q ≥ 0` because the Fisher information `I(p) ≥ 0` (`fisherInfo_nonneg`) — a statistical fact about every
probability density. The Bohmian "non-classical attractor" positivity needs no wavefunction: it is the
non-negativity of Fisher information. -/
theorem fisherQuantumPotential_nonneg (data : FisherInformationData Φ) (φ : Φ) (ℏ m : ℝ)
    (hℏ : 0 ≤ ℏ) (hm : 0 < m) : 0 ≤ fisherQuantumPotential data φ ℏ m :=
  bohmQuantumPotential_nonneg _ ℏ m (data.fisherInfo_nonneg φ) hℏ hm

/-! ## §B — de Bruijn: the quantum potential is twice the entropy-production rate -/

/-- **[de Bruijn] The differential-entropy production rate** `dH/dt = (D/2)·I(p)` under heat flow
`∂ₜp = DΔp` (Stam / de Bruijn identity), with diffusion `D`. -/
noncomputable def deBruijnEntropyRate (D fisher : ℝ) : ℝ := D * fisher / 2

/-- **[Interpretation-neutral] The quantum potential is twice the de Bruijn entropy-production rate.**
With diffusion `D = ℏ/(2m)`, `Q = (ℏ/2m)·I(p) = 2·(D/2)·I(p) = 2·(dH/dt)`: the quantum potential is twice
the rate of differential-entropy production of the density — a purely information-theoretic quantity. -/
theorem fisherQuantumPotential_eq_two_deBruijn (data : FisherInformationData Φ) (φ : Φ) (ℏ m : ℝ)
    (hm : m ≠ 0) :
    fisherQuantumPotential data φ ℏ m = 2 * deBruijnEntropyRate (ℏ / (2 * m)) (data.fisherInfo φ) := by
  unfold fisherQuantumPotential bohmQuantumPotential deBruijnEntropyRate
  field_simp

/-! ## §C — the Fisher imaginary action is UV-coercive -/

/-- **[Interpretation-neutral coercivity] The Fisher imaginary action is UV-coercive.**
`S_I = I(p) ≥ (p_min·k_UV²)·‖Φ‖²_UV` (`fisher_info_coercivity`): from a density floor `p ≥ p_min` and a
Poincaré spectral gap, with no pilot wave. This is the coercivity the de Broglie–Bohm quantum potential
needs, supplied by Fisher information. -/
theorem fisherImaginaryAction_coercive (data : FisherInformationData Φ) (φ : Φ) :
    data.p_min * data.k_UV_sq * data.uvNormSq φ ≤ data.fisherInfo φ :=
  data.fisher_info_coercivity φ

/-! ## §D — the lapse imaginary action as Fisher information -/

/-- **[Link — replace the pilot wave for the lapse] When the lapse imaginary action is the Fisher
information, the lapse quantum potential is the Fisher quantum potential.** Given the identification
`εℋ = I(p)` (the lapse gap × constraint equals the density's Fisher information),
`bohmQuantumPotential (εℋ) ℏ m = fisherQuantumPotential data φ ℏ m` — the lapse contour's imaginary action
is read as Fisher information, not a pilot-wave amplitude. -/
theorem lapse_quantumPotential_is_fisher (data : FisherInformationData Φ) (φ : Φ) (ε Ham ℏ m : ℝ)
    (h : ε * Ham = data.fisherInfo φ) :
    bohmQuantumPotential (ε * Ham) ℏ m = fisherQuantumPotential data φ ℏ m := by
  rw [fisherQuantumPotential, h]

/-- **[No pilot wave for the lapse] The lapse quantum potential is non-negative from Fisher
non-negativity.** With `εℋ = I(p)`, `bohmQuantumPotential (εℋ) ℏ m ≥ 0` because `I(p) ≥ 0` — the lapse
contour's quantum potential is non-negative as a statistical fact, no wavefunction required. -/
theorem lapse_quantumPotential_nonneg_from_fisher (data : FisherInformationData Φ) (φ : Φ) (ε Ham ℏ m : ℝ)
    (h : ε * Ham = data.fisherInfo φ) (hℏ : 0 ≤ ℏ) (hm : 0 < m) :
    0 ≤ bohmQuantumPotential (ε * Ham) ℏ m := by
  rw [lapse_quantumPotential_is_fisher data φ ε Ham ℏ m h]
  exact fisherQuantumPotential_nonneg data φ ℏ m hℏ hm

/-! ## §E — linking the Fisher quantum potential to the Bohm-Q machinery -/

/-- **[Link — the classical limit is zero Fisher information] `Q = 0 ⟺ I(p) = 0`.** Routing through the
Bohm-Q dichotomy (`bohmQuantumPotential_zero_iff`), the de Broglie–Bohm classical limit of the Fisher
quantum potential is exactly the vanishing of the Fisher information. -/
theorem fisherQuantumPotential_zero_iff (data : FisherInformationData Φ) (φ : Φ) (ℏ m : ℝ)
    (hℏ : ℏ ≠ 0) (hm : 0 < m) :
    fisherQuantumPotential data φ ℏ m = 0 ↔ data.fisherInfo φ = 0 :=
  bohmQuantumPotential_zero_iff _ ℏ m hℏ hm

/-- **[Link — the classical limit is the no-information state] `Q = 0 ⟹ ∇log p = 0`.** Zero Fisher quantum
potential forces zero log-density gradient (`gradNormSq = 0`): the density is uniform. The classical limit
is *informationless* — `Q = 0` iff there is no Fisher information to extract. Uses the density floor
(`density_bound`) and `gradNormSq_nonneg`. -/
theorem fisherQuantumPotential_zero_implies_uniform (data : FisherInformationData Φ) (φ : Φ) (ℏ m : ℝ)
    (hℏ : ℏ ≠ 0) (hm : 0 < m) (h : fisherQuantumPotential data φ ℏ m = 0) :
    data.gradNormSq φ = 0 := by
  have hf : data.fisherInfo φ = 0 := (fisherQuantumPotential_zero_iff data φ ℏ m hℏ hm).mp h
  have hb := data.density_bound φ
  have hg := data.gradNormSq_nonneg φ
  nlinarith [data.p_min_pos]

/-- **[Link — Bohm Born machinery] The Born weight at the Fisher imaginary action is `e^{−I(p)/ℏ}`.**
`‖madelungAmplitude S_R (I(p)) ℏ‖ = bornWeight (I(p)) ℏ` (`madelungAmplitude_norm`): the de Broglie–Bohm
Born weight of a state is the exponential of (minus) its density's Fisher information — the amplitude
`R = e^{−I(p)/ℏ}` read information-theoretically. -/
theorem fisherBornWeight (data : FisherInformationData Φ) (φ : Φ) (S_R ℏ : ℝ) :
    ‖madelungAmplitude S_R (data.fisherInfo φ) ℏ‖ = bornWeight (data.fisherInfo φ) ℏ :=
  madelungAmplitude_norm S_R (data.fisherInfo φ) ℏ

/-- **[Link §F — the NN contour quantum potential is the Fisher quantum potential].** When the contour's
imaginary action `E_I·t` (gap × coordinate time) is the Fisher information `I(p)`, the §F contour quantum
potential is the Fisher quantum potential: the propagator's Bohm-Q reading is information-theoretic. -/
theorem nnContour_quantumPotential_is_fisher (data : FisherInformationData Φ) (φ : Φ) (E_I t ℏ m : ℝ)
    (h : nnImaginaryAction E_I t = data.fisherInfo φ) :
    bohmQuantumPotential (nnImaginaryAction E_I t) ℏ m = fisherQuantumPotential data φ ℏ m := by
  rw [fisherQuantumPotential, h]

/-- **[Link §G — the complex-oscillator quantum potential is the Fisher quantum potential].** When the
oscillator's imaginary action `−V_I·t` is the Fisher information `I(p)`, the §G oscillator quantum potential
is the Fisher quantum potential: the complex oscillator's Bohm-Q reading is information-theoretic. -/
theorem oscillator_quantumPotential_is_fisher (data : FisherInformationData Φ) (φ : Φ)
    (m ω : ℂ) (q t ℏ mass : ℝ) (h : oscillatorImaginaryAction m ω q t = data.fisherInfo φ) :
    bohmQuantumPotential (oscillatorImaginaryAction m ω q t) ℏ mass
      = fisherQuantumPotential data φ ℏ mass := by
  rw [fisherQuantumPotential, h]

end Physlib.QuantumMechanics.ComplexAction.GravLapse.FisherQuantumPotential

end

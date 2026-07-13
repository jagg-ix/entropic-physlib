/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Kinematic core for the entropic screen: Compton wavelength, Schmidt number, entropic distance

The light, Mathlib-only definitions the Newton-`G` screen derivation is built on:

* `FrequencyTrinity` — the reduced Compton wavelength `λ_C = ħ/(mc)`;
* `SchmidtRapidityHyperbolic` — the Schmidt number `K = coth η`;
* `EntropicProperDistance` — the entropic proper distance `r = λ_C·log K`.

No dependence on the Bell / Bogoliubov / Wick / Helicity machinery. (In the full library these live
in `ComptonClock.FrequencyTrinity`, `MuonAnomaly.SchmidtRapidityHyperbolic` and
`ComptonClock.EntropicProperDistance`, which import this core and add their application faces.)

## References

* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. **126** (2011)
  1021, arXiv:1104.3381 — the complex-action framework these definitions live in.
* A. H. Compton, *A Quantum Theory of the Scattering of X-rays by Light Elements*, Phys. Rev. **21**
  (1923) 483 — the Compton wavelength.
* E. Schmidt, *Zur Theorie der linearen und nichtlinearen Integralgleichungen. I*, Math. Ann. **63**
  (1907) 433 — the Schmidt decomposition / Schmidt number.
* D. Wilkins, D. Williams, *From rapidity to vibracy (logarithmic frequency)*, Am. J. Phys. **69**
  (2001) 158 — the rapidity/logarithm relation behind `r = λ_C·log K`.
* S. J. Summers, *Yet More Ado About Nothing*, arXiv:0802.1854; A. F. Bennett, arXiv:1406.0750 — the
  Reeh–Schlieder exponential decay of vacuum Bell correlations `C(r) = C₀·e^{−r/λ_C}` over the
  Compton wavelength.
* Yu. I. Bogdanov, N. A. Bogdanova, K. A. Valiev, *Entanglement of Quantum States, Thermodynamical
  Statistical Distributions and Physical Nature of Temperature*, arXiv:quant-ph/0605208 (2006) — a
  pure entangled state has a thermal reduced density matrix with geometric Schmidt spectrum
  `P_n = (1−g)·gⁿ`, `g = e^{−βħω}`, so `K = (1+g)/(1−g) = coth(βħω/2)`. S. M. Barnett, S. J. D.
  Phoenix, *Bell's Inequality and the Schmidt Decomposition*, Phys. Lett. A **167** (1992) 233.
* A. Sergi, P. V. Giaquinta, *Linear Quantum Entropy and Non-Hermitian Hamiltonians*, Entropy **18**
  (2016) 451, doi:10.3390/e18120451 — the non-Hermitian convention `H = H_R − i·H_I` and the
  entropic amplitude damping `exp(−S_I/ℏ)`.
* C. M. Bender, D. C. Brody, D. W. Hook, *Quantum effects in classical systems having complex
  energy*, J. Phys. A **41** (2008) 352003, arXiv:0804.4169 — the complex energy `E = E_R − i·E_I`
  whose imaginary part is the entropy-production rate `E_I = dS_I/dt`.

The Schmidt number `K = coth η` is the thermal-spectrum result of Bogdanov et al. (`η = βħω/2`,
`schmidtNumber_eq_thermal_ratio`). The entropic distance `r = λ_C·log K` is the **inverse of the
Reeh–Schlieder vacuum-correlation decay**: solving `C(r) = C₀·e^{−r/λ_C}` for `r` gives
`r = λ_C·log(C₀/C)`, so `K = C₀/C` is the concurrence-decay ratio.

The entropic proper time `τ_ent = r/c` carries the imaginary (entropic) action
`mc²·τ_ent = ħ·log K = S_I` (`restEnergy_mul_entropicProperTime`, Nagao–Nielsen complex action); its
non-Hermitian Schrödinger amplitude `exp(−S_I/ℏ) = 1/K = tanh η` (`entropicAmplitude_eq_tanh`, the
`H = H_R − i·H_I` damping of Sergi–Giaquinta / Bender–Brody–Hook) is the two-mode-squeezed
concurrence. -/

set_option autoImplicit false

@[expose] public section

open Real

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-- **The reduced Compton wavelength** `λ_C = ħ/(mc)` — the natural length scale of a mass `m`. -/
noncomputable def comptonWavelength (m c ħ : ℝ) : ℝ := ħ / (m * c)

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic

/-- **The Schmidt number** `K = coth η_eff = cosh η / sinh η` — the bipartite entanglement measure.
-/
noncomputable def schmidtNumber (η : ℝ) : ℝ := Real.cosh η / Real.sinh η

/-- **[Entanglement ⟺ `K > 1`] `coth η > 1` for `η > 0`.** -/
lemma schmidtNumber_gt_one (η : ℝ) (hη : 0 < η) : 1 < schmidtNumber η := by
  have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
  unfold schmidtNumber
  rw [lt_div_iff₀ hs, one_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq η, hs, Real.cosh_pos η]

/-- **[The Schmidt number is the thermal-spectrum coth]** `K = coth η = (1+g)/(1−g)` with
`g = e^{−2η}` — the Schmidt number of the geometric spectrum `P_n = (1−g)·gⁿ` of the thermal reduced
state of a pure entangled state (Bogdanov–Bogdanova–Valiev, arXiv:quant-ph/0605208; `η = βħω/2`,
`g = e^{−βħω}`). -/
lemma schmidtNumber_eq_thermal_ratio (η : ℝ) (hη : 0 < η) :
    schmidtNumber η = (1 + Real.exp (-(2 * η))) / (1 - Real.exp (-(2 * η))) := by
  have hs : Real.sinh η ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hη)
  have hg : Real.exp (-(2 * η)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hd : (1 : ℝ) - Real.exp (-(2 * η)) ≠ 0 := by linarith
  have hE : Real.exp η ≠ 0 := Real.exp_ne_zero _
  have h2 : Real.exp (-(2 * η)) = Real.exp (-η) * Real.exp (-η) := by
    rw [← Real.exp_add, show -η + -η = -(2 * η) from by ring]
  unfold schmidtNumber
  rw [div_eq_div_iff hs hd, Real.cosh_eq, Real.sinh_eq]
  simp only [h2, Real.exp_neg]
  field_simp

/-- **[The Schmidt number is the inverse squeezing amplitude]** `K = coth η = 1/tanh η`. With the
two-mode-squeezed concurrence `C = C₀·tanh η` (`tanh η` the Bogoliubov squeezing velocity), the
concurrence-decay ratio is `C₀/C = 1/tanh η = K`. The reciprocity `tanh η · coth η = 1` is
`Bogoliubov.RapidityBoseFermiCothTanh.bogoliubovVelocity_mul_coth` in the full library. -/
lemma schmidtNumber_eq_inv_tanh (η : ℝ) : schmidtNumber η = 1 / Real.tanh η := by
  unfold schmidtNumber
  rw [Real.tanh_eq_sinh_div_cosh, one_div_div]

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic

/-- **The entropic proper distance** `r = λ_C · log K` (`K = coth η` the Schmidt number): the proper
separation, measured in Compton wavelengths, set by the entanglement of the two regions. -/
noncomputable def entropicProperDistance (m c ħ η : ℝ) : ℝ :=
  comptonWavelength m c ħ * Real.log (schmidtNumber η)

/-- **[The entropic distance is the inverted vacuum Bell decay]** if the vacuum concurrence at
spacelike separation `r` decays as `C = C₀·e^{−r/λ_C}` (Reeh–Schlieder cluster decomposition, decay
scale the Compton wavelength; Summers arXiv:0802.1854, Bennett arXiv:1406.0750), then the separation
is `λ_C·log(C₀/C) = r` — the Compton wavelength times the log of the concurrence-decay ratio. With
the Schmidt number `K = C₀/C`, `entropicProperDistance` at `r = λ_C·log K` is exactly this
separation. -/
lemma entropicProperDistance_of_bellDecay (lC C₀ C r : ℝ) (hlC : lC ≠ 0) (hC₀ : 0 < C₀) (hC : 0 < C)
    (hdecay : C = C₀ * Real.exp (-(r / lC))) :
    lC * Real.log (C₀ / C) = r := by
  have hexp : (0 : ℝ) < Real.exp (-(r / lC)) := Real.exp_pos _
  rw [hdecay, Real.log_div (ne_of_gt hC₀) (mul_pos hC₀ hexp).ne',
    Real.log_mul (ne_of_gt hC₀) hexp.ne', Real.log_exp]
  have hstep : Real.log C₀ - (Real.log C₀ + -(r / lC)) = r / lC := by ring
  rw [hstep]
  field_simp

/-- **[The entropic proper distance realizes the Bell-decay separation]** when the concurrence
decays as `C = C₀·e^{−r/λ_C}` and the Schmidt number matches the decay ratio (`K = C₀/C`), the
definition `entropicProperDistance = λ_C·log K` is exactly the separation `r`: the inverted decay
`entropicProperDistance_of_bellDecay` specialized to the `comptonWavelength` and `schmidtNumber`
definitions. -/
lemma entropicProperDistance_eq_of_bellDecay (m c ħ η C₀ C r : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hC₀ : 0 < C₀) (hC : 0 < C)
    (hK : schmidtNumber η = C₀ / C)
    (hdecay : C = C₀ * Real.exp (-(r / comptonWavelength m c ħ))) :
    entropicProperDistance m c ħ η = r := by
  unfold entropicProperDistance
  rw [hK]
  exact entropicProperDistance_of_bellDecay (comptonWavelength m c ħ) C₀ C r
    (div_ne_zero hħ (mul_ne_zero hm hc)) hC₀ hC hdecay

/-- **[Closing the Bell-decay link: the two Ks coincide under `C = C₀·tanh η`]** if the vacuum
concurrence follows the Bell decay to `C₀·tanh η` at separation `r` — `tanh η` the two-mode-squeezed
concurrence / Bogoliubov squeezing velocity — then `entropicProperDistance = r`. The
concurrence-decay ratio `C₀/C = 1/tanh η` equals the Schmidt number `K = coth η`
(`schmidtNumber_eq_inv_tanh`), so the Bell-decay `K` and the Schmidt-number `K` are one and the
same. The identification `concurrence = tanh η` is now a theorem for the two-mode-squeezed pair
(`EntanglementConcurrence.concurrence_twoModeSqueezed_eq_tanh`); the residual external input is the
Reeh–Schlieder exponential decay over `λ_C` itself (Summers/Bennett). -/
lemma entropicProperDistance_of_bellConcurrence (m c ħ η C₀ r : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hη : 0 < η) (hC₀ : 0 < C₀)
    (hconc : C₀ * Real.tanh η = C₀ * Real.exp (-(r / comptonWavelength m c ħ))) :
    entropicProperDistance m c ħ η = r := by
  have htanh : 0 < Real.tanh η := by
    rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr hη) (Real.cosh_pos η)
  have htne : Real.tanh η ≠ 0 := htanh.ne'
  have hC₀ne : C₀ ≠ 0 := hC₀.ne'
  have hK : schmidtNumber η = C₀ / (C₀ * Real.tanh η) := by
    rw [schmidtNumber_eq_inv_tanh, div_eq_div_iff htne (mul_ne_zero hC₀ne htne)]; ring
  exact entropicProperDistance_eq_of_bellDecay m c ħ η C₀ (C₀ * Real.tanh η) r hm hc hħ hC₀
    (mul_pos hC₀ htanh) hK hconc

/-- **The entropic proper time** `τ_ent = r/c = λ_C·log K / c` — the entropic proper distance
`r = λ_C·log K` traversed at the speed of light. This is the imaginary (entropic) part of the
complex proper time `S = S_R + i·S_I` of the entropic-time framework. -/
noncomputable def entropicProperTime (m c ħ η : ℝ) : ℝ :=
  entropicProperDistance m c ħ η / c

/-- **[Rest energy × entropic proper time is the imaginary action]** `mc²·τ_ent = ħ·log K = S_I`:
the entropic proper time is the imaginary (entropic) action `S_I = ħ·log K` (`K = coth η` the
Schmidt number) per rest energy `mc²`. The imaginary part of the complex proper time
`S = S_R + i·S_I` is the entropic-time gap, dimensionally a time, set by the entanglement `log K`.
-/
lemma restEnergy_mul_entropicProperTime (m c ħ η : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    m * c ^ 2 * entropicProperTime m c ħ η = ħ * Real.log (schmidtNumber η) := by
  unfold entropicProperTime entropicProperDistance comptonWavelength
  field_simp

/-- **The non-Hermitian (entropic) amplitude factor** `exp(−S_I/ℏ) = exp(−mc²·τ_ent/ℏ)` — the
non-unitary modulus of the Schrödinger propagator accumulated over the entropic proper time. With
the complex action `S = S_R + i·S_I` the wavefunction is `ψ ~ exp(iS/ℏ) = exp(iS_R/ℏ)·exp(−S_I/ℏ)`;
equivalently, for the non-Hermitian complex energy `E = E_R − i·E_I`
(`NonHermitian.WickRotation.complexEnergy`, `E_I = dS_I/dt` of `BenderIdentity.complexEnergyOfRate`)
the propagator modulus is `|exp(−iEt/ℏ)| = exp(−E_I·t/ℏ) = exp(−S_I/ℏ)` — the imaginary-time /
dissipative part of the Schrödinger evolution. -/
noncomputable def entropicAmplitude (m c ħ η : ℝ) : ℝ :=
  Real.exp (-(m * c ^ 2 * entropicProperTime m c ħ η) / ħ)

/-- **[The non-Hermitian amplitude decay over the entropic time is `1/K`]** `exp(−S_I/ℏ) = 1/K`
(`K = coth η` the Schmidt number): evolving the rest state through one entropic proper time `τ_ent`
damps the amplitude by the reciprocal Schmidt number — the non-Hermitian (imaginary-energy)
Schrödinger evolution with accumulated imaginary action `S_I = mc²·τ_ent = ħ·log K`. -/
lemma entropicAmplitude_eq_inv_schmidt (m c ħ η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hη : 0 < η) :
    entropicAmplitude m c ħ η = 1 / schmidtNumber η := by
  have hK : 0 < schmidtNumber η := by
    unfold schmidtNumber; exact div_pos (Real.cosh_pos η) (Real.sinh_pos_iff.mpr hη)
  unfold entropicAmplitude
  rw [restEnergy_mul_entropicProperTime m c ħ η hm hc]
  have hexp : -(ħ * Real.log (schmidtNumber η)) / ħ = -Real.log (schmidtNumber η) := by
    rw [neg_div, mul_comm ħ, mul_div_assoc, div_self hħ, mul_one]
  rw [hexp, Real.exp_neg, Real.exp_log hK, one_div]

/-- **[The entropic amplitude decay is the concurrence `tanh η`]** `exp(−S_I/ℏ) = 1/K = tanh η`: the
non-Hermitian Schrödinger amplitude damping over the entropic proper time equals the
two-mode-squeezed concurrence (`EntanglementConcurrence.concurrence_twoModeSqueezed_eq_tanh`) — the
entropic-time dissipation is the vacuum entanglement itself. -/
lemma entropicAmplitude_eq_tanh (m c ħ η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hη : 0 < η) :
    entropicAmplitude m c ħ η = Real.tanh η := by
  rw [entropicAmplitude_eq_inv_schmidt m c ħ η hm hc hħ hη, schmidtNumber_eq_inv_tanh,
    one_div_one_div]

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance

end

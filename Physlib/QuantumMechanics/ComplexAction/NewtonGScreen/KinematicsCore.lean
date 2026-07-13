/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Kinematic core for the Newton-`G` screen: Compton wavelength, Schmidt number, entropic distance

The Mathlib-only definitions the Newton-`G` derivation is built on: the reduced Compton wavelength
`λ_C = ħ/(mc)`, the Schmidt number `K = coth η`, and the entropic proper distance `r = λ_C·log K`.

## References

* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. **126** (2011)
  1021, arXiv:1104.3381 — the complex-action framework these definitions live in.
-/

set_option autoImplicit false

@[expose] public section

open Real

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-- **The reduced Compton wavelength** `λ_C = ħ/(mc)` — the natural length scale of a mass `m`. -/
noncomputable def comptonWavelength (m c ħ : ℝ) : ℝ := ħ / (m * c)

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic

/-- **The Schmidt number** `K = coth η = cosh η / sinh η` — the bipartite entanglement measure. -/
noncomputable def schmidtNumber (η : ℝ) : ℝ := Real.cosh η / Real.sinh η

/-- **[Entanglement ⟺ `K > 1`] `coth η > 1` for `η > 0`.** -/
lemma schmidtNumber_gt_one (η : ℝ) (hη : 0 < η) : 1 < schmidtNumber η := by
  have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
  unfold schmidtNumber
  rw [lt_div_iff₀ hs, one_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq η, hs, Real.cosh_pos η]

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic

/-- **The entropic proper distance** `r = λ_C · log K` (`K = coth η` the Schmidt number): the proper
separation, measured in Compton wavelengths, set by the entanglement of the two regions. -/
noncomputable def entropicProperDistance (m c ħ η : ℝ) : ℝ :=
  comptonWavelength m c ħ * Real.log (schmidtNumber η)

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance

end

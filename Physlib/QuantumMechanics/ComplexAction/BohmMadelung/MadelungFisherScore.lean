/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungOsmoticQuantumPotential

/-!
# The osmotic velocity is the Fisher score: the quantum potential as Fisher information

Links the Madelung complex/osmotic velocity (`BohmMadelung.MadelungOsmoticQuantumPotential`) to the repo's
**Fisher-information** reading of the quantum potential (`GravLapse.FisherQuantumPotential`,
`FisherInformationCoercivity`, `BohmianQuantumPotential`).

The osmotic velocity `u = (ħ/2μ)·∂_q ln ρ` is `(ħ/2μ)` times the **Fisher score** `s = ∂_q ln ρ` (the
imaginary part of the Schrödinger–Burgers complex velocity, `complexVelocity_im_is_score`). Hence the
**osmotic-kinetic term** of the quantum potential is, exactly,

  `(μ/2)·u² = (ħ²/8μ)·s²`   (`osmoticKinetic_eq_fisherDensity`),

i.e. `(ħ²/8μ)` times the **Fisher information density** `s² = (∂_q ln ρ)²`, non-negative
(`osmoticKinetic_nonneg`). So the kinetic part of the Bohm quantum potential — the `(μ/2)u²` of the
Burgers form — *is* the Fisher information, exactly as `GravLapse.FisherQuantumPotential` reads the quantum
potential `Q = I(p)·ħ/(2m)` off the Fisher information of the density (no pilot wave). The dissipative
imaginary sector of the complex velocity field is the Fisher score.

* **§A — the osmotic velocity is the Fisher score** (`complexVelocity_im_is_score`).
* **§B — the osmotic-kinetic term is the Fisher information density** (`osmoticKinetic_eq_fisherDensity`,
  `osmoticKinetic_nonneg`).

## References

* The Fisher-information form of the Bohm quantum potential (`⟨Q⟩ ∝ I(p)`). structures:
  `BohmMadelung.MadelungOsmoticQuantumPotential` (`complexVelocity`, `osmoticQuantumPotential`),
  `GravLapse.FisherQuantumPotential` (`fisherQuantumPotential = I(p)·ħ/(2m)`),
  `FisherInformationCoercivity` (`fisherInfo`, `fisherInfo_nonneg`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungFisherScore

open Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungOsmoticQuantumPotential

/-! ## §A — the osmotic velocity is the Fisher score -/

/-- **[The complex velocity's imaginary part is the (scaled) Fisher score] `Im V = (ħ/2μ)·s`.** With the
osmotic velocity `u = (ħ/2μ)·s` set from the Fisher score `s = ∂_q ln ρ`, the imaginary part of the
Schrödinger–Burgers complex velocity `V = v + iu` is `(ħ/2μ)·s` — the dissipative sector is the Fisher
score. -/
theorem complexVelocity_im_is_score (v ħ μ s : ℝ) :
    (complexVelocity v (ħ / (2 * μ) * s)).im = ħ / (2 * μ) * s :=
  complexVelocity_im v (ħ / (2 * μ) * s)

/-! ## §B — the osmotic-kinetic term is the Fisher information density -/

/-- **[The osmotic kinetic energy is the Fisher information density] `(μ/2)u² = (ħ²/8μ)·s²`.** The
kinetic part of the Bohm quantum potential — the `(μ/2)u²` of the osmotic (Burgers) form, with
`u = (ħ/2μ)·s` — is `(ħ²/8μ)` times the Fisher information density `s² = (∂_q ln ρ)²`. The quantum
potential's kinetic sector *is* the Fisher information. -/
theorem osmoticKinetic_eq_fisherDensity (μ ħ s : ℝ) (hμ : μ ≠ 0) :
    μ / 2 * (ħ / (2 * μ) * s) ^ 2 = ħ ^ 2 / (8 * μ) * s ^ 2 := by
  field_simp
  ring

/-- **[The osmotic kinetic / Fisher density is non-negative] `(μ/2)u² ≥ 0`** for `μ > 0` — the Fisher
information density is non-negative (`fisherInfo_nonneg`), with no pilot-wave assumption. -/
theorem osmoticKinetic_nonneg (μ ħ s : ℝ) (hμ : 0 < μ) :
    0 ≤ μ / 2 * (ħ / (2 * μ) * s) ^ 2 := by
  positivity

/-- **[The osmotic velocity is the Fisher score, assembled].** The imaginary part of the
Schrödinger–Burgers complex velocity is the (scaled) Fisher score `(ħ/2μ)·s`, and the osmotic-kinetic
term of the quantum potential is `(ħ²/8μ)·s²` — the (non-negative) Fisher information density. The
dissipative sector of the Madelung complex velocity field is the Fisher information, matching the repo's
pilot-wave-free reading `Q = I(p)·ħ/(2m)`. -/
theorem madelung_osmotic_is_fisher (v μ ħ s : ℝ) (hμ : 0 < μ) :
    (complexVelocity v (ħ / (2 * μ) * s)).im = ħ / (2 * μ) * s
      ∧ μ / 2 * (ħ / (2 * μ) * s) ^ 2 = ħ ^ 2 / (8 * μ) * s ^ 2
      ∧ 0 ≤ μ / 2 * (ħ / (2 * μ) * s) ^ 2 :=
  ⟨complexVelocity_im_is_score v ħ μ s, osmoticKinetic_eq_fisherDensity μ ħ s hμ.ne',
    osmoticKinetic_nonneg μ ħ s hμ⟩

end Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungFisherScore

end

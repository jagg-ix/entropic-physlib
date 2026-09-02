/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic

/-!
# Quantum Drude Oscillator invariants: parameter-free scaling of atomic response

The exact, parameter-free scaling relations of the Quantum Drude Oscillator (QDO) model of Jones, Crain,
Sokhan, Whitfield & Martyna, *Quantum Drude oscillator model of atoms and molecules*, Phys. Rev. B **87**,
144103 (2013). Because the QDO is a Gaussian model, its multipole polarizabilities `α₁, α₂, α₃` (dipole,
quadrupole, octupole) and dispersion coefficients `C₆, C₈, C₁₀, C₉` obey universal ratios that hold for *every*
QDO, independent of the parameters `(μ, ω, q)`. These "combining rules" hold to a few percent for real noble
gases, alkali metals, and first-row hydrides across the periodic table — the atomic-response counterpart of the
shell/valence structure formalized elsewhere.

* **§A — polarizabilities (Eq. 3).** With `L = ℏ/(μω)` (the Gaussian variance), `α₂ = ¾ L α₁`,
  `α₃ = 5/4 L² α₁`. **`polarizability_invariant`** (`9 α₁ α₃ = 20 α₂²`, i.e.
  `γ_pol = (2√5/3)·α₂/√(α₁α₃) = 1`).
* **§B — two-body dispersion (Eqs. 6–8).** `C₆ = ¾ α₁² ℏω`, `C₈ = 5 α₁ α₂ ℏω`,
  `C₁₀ = (21/2 α₁ α₃ + 35/2 α₂²) ℏω`, `C₉ = 3/16 α₁³ ℏω`. **`dispersion_invariant`**
  (`49 C₈² = 40 C₆ C₁₀`, i.e. `γ_disp = (7/2√10)·C₈/√(C₆C₁₀) = 1`).
* **§C — three-body dispersion (Eq. 9).** **`threebody_invariant`** (`α₁ C₆ = 4 C₉`, i.e.
  `γ_3disp = α₁C₆/(4C₉) = 1`).

**Honest layering.** All three are exact ring identities in the QDO parameters (`α₁, L, ℏω`), given the
Gaussian polarizability/dispersion forms of Eqs. 3 and 6. The `γ = 1` readings (with square roots) follow from
the sqrt-free forms proved here; the empirical few-percent agreement with real atoms is the paper's result, not
formalized.

## References

* Jones, Crain, Sokhan, Whitfield & Martyna, Phys. Rev. B **87**, 144103 (2013), Eqs. 3, 6–9. Complements the
  van der Waals / polarizability work in `ComplexAction` (`VanDerWaalsPolarizabilityScaling`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorInvariants


/-- The **quadrupole polarizability** `α₂ = ¾ L α₁` (Eq. 3b), `L = ℏ/(μω)`. -/
noncomputable def alphaQuad (α₁ L : ℝ) : ℝ := 3 / 4 * L * α₁

/-- The **octupole polarizability** `α₃ = 5/4 L² α₁` (Eq. 3c). -/
noncomputable def alphaOct (α₁ L : ℝ) : ℝ := 5 / 4 * L ^ 2 * α₁

/-- **The polarizability invariant** `9 α₁ α₃ = 20 α₂²` — equivalently `γ_pol = (2√5/3)·α₂/√(α₁α₃) = 1`, the
Gaussian relation among the dipole, quadrupole and octupole polarizabilities, holding for every QDO. -/
lemma polarizability_invariant (α₁ L : ℝ) :
    9 * α₁ * alphaOct α₁ L = 20 * alphaQuad α₁ L ^ 2 := by
  unfold alphaOct alphaQuad; ring


/-- The **`C₆` dispersion coefficient** `¾ α₁² ℏω` (Eq. 6). -/
noncomputable def C6 (α₁ hω : ℝ) : ℝ := 3 / 4 * α₁ ^ 2 * hω

/-- The **`C₈` dispersion coefficient** `5 α₁ α₂ ℏω` (Eq. 6). -/
noncomputable def C8 (α₁ L hω : ℝ) : ℝ := 5 * α₁ * alphaQuad α₁ L * hω

/-- The **`C₁₀` dispersion coefficient** `(21/2 α₁ α₃ + 35/2 α₂²) ℏω` (Eq. 6). -/
noncomputable def C10 (α₁ L hω : ℝ) : ℝ := (21 / 2 * α₁ * alphaOct α₁ L + 35 / 2 * alphaQuad α₁ L ^ 2) * hω

/-- The **`C₉` three-body dispersion coefficient** `3/16 α₁³ ℏω` (Eq. 6). -/
noncomputable def C9 (α₁ hω : ℝ) : ℝ := 3 / 16 * α₁ ^ 3 * hω

/-- **The two-body dispersion invariant** `49 C₈² = 40 C₆ C₁₀` — equivalently
`γ_disp = (7/2√10)·C₈/√(C₆C₁₀) = 1`, the Gaussian relation among the `C₆, C₈, C₁₀` van der Waals coefficients. -/
lemma dispersion_invariant (α₁ L hω : ℝ) :
    49 * C8 α₁ L hω ^ 2 = 40 * C6 α₁ hω * C10 α₁ L hω := by
  unfold C8 C6 C10 alphaQuad alphaOct; ring


/-- **The three-body dispersion invariant** `α₁ C₆ = 4 C₉` — equivalently `γ_3disp = α₁C₆/(4C₉) = 1`, relating
the two-body `C₆` and three-body `C₉` (Axilrod–Teller–Muto) coefficients. -/
lemma threebody_invariant (α₁ hω : ℝ) :
    α₁ * C6 α₁ hω = 4 * C9 α₁ hω := by
  unfold C6 C9; ring


/-- **The polarizability multipole ratios scale with the Gaussian width** `α₂/α₁ = ¾ L`, `α₃/α₁ = 5/4 L²` — the
successive multipole polarizabilities grow by one power of the variance `L = ℏ/(μω)` per multipole order. -/
lemma multipole_ratios (α₁ L : ℝ) :
    alphaQuad α₁ L = 3 / 4 * L * α₁ ∧ alphaOct α₁ L = 5 / 4 * L ^ 2 * α₁ := ⟨rfl, rfl⟩


/-- **The QDO frequency is fixed by `C₆` and `α₁`** `4 C₆ = 3 α₁² ℏω`, i.e. `ℏω = (4/3) C₆/α₁²` (Eq. 11): the
oscillator frequency of a fitted QDO is extracted from the measured dipole polarizability and `C₆`. -/
lemma frequency_from_response (α₁ hω : ℝ) : 4 * C6 α₁ hω = 3 * α₁ ^ 2 * hω := by
  unfold C6; ring


/-- **`C₈ = 5 L C₆`** — each higher dispersion coefficient gains one power of the variance `L = ℏ/(μω)`. -/
lemma C8_eq_scaled_C6 (α₁ L hω : ℝ) : C8 α₁ L hω = 5 * L * C6 α₁ hω := by
  unfold C8 C6 alphaQuad; ring

/-- **`C₁₀ = 245/8 · L² C₆`** — two powers of the variance above `C₆`. -/
lemma C10_eq_scaled_C6 (α₁ L hω : ℝ) : C10 α₁ L hω = 245 / 8 * L ^ 2 * C6 α₁ hω := by
  unfold C10 C6 alphaQuad alphaOct; ring


/-- **Only the dipole polarizability survives classically** — as `L = ℏ/(μω) → 0` the quadrupole and octupole
polarizabilities vanish (`α₂, α₃ → 0`): the classical Drude oscillator has dipole polarization only. -/
lemma classical_limit (α₁ : ℝ) : alphaQuad α₁ 0 = 0 ∧ alphaOct α₁ 0 = 0 := by
  refine ⟨?_, ?_⟩
  · unfold alphaQuad; ring
  · unfold alphaOct; ring


/-- The **heteronuclear `C₆^AB`** `= 3/2 α^A α^B ℏ ω_A ω_B/(ω_A+ω_B)` (Eq. 5). -/
noncomputable def C6mixed (αA αB ωA ωB hbar : ℝ) : ℝ := 3 / 2 * αA * αB * hbar * ωA * ωB / (ωA + ωB)

/-- The **homonuclear `C₆^ss`** `= ¾ α² ℏ ω`. -/
noncomputable def C6homo (α ω hbar : ℝ) : ℝ := 3 / 4 * α ^ 2 * hbar * ω

/-- **The Moelwyn–Hughes/London combining rule holds exactly for QDO** (Eq. 10, `γ_mix = 1`):
`C₆^AB (C₆^AA (α^B)² + C₆^BB (α^A)²) = 2 C₆^AA C₆^BB α^A α^B` — the heteronuclear `C₆` is the harmonic
combination of the homonuclear ones, a parameter-free consequence of the Gaussian structure. -/
lemma moelwyn_hughes_combining (αA αB ωA ωB hbar : ℝ) (h : ωA + ωB ≠ 0) :
    C6mixed αA αB ωA ωB hbar * (C6homo αA ωA hbar * αB ^ 2 + C6homo αB ωB hbar * αA ^ 2)
      = 2 * C6homo αA ωA hbar * C6homo αB ωB hbar * αA * αB := by
  unfold C6mixed C6homo
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorInvariants

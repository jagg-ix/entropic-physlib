/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMatter
public import Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

/-!
# The winding mass as the Dirac mass operator (mass leg)

The scalar rest mass `comptonMass ω c ħ = ħω/c²` (`Winding.NumberMass`, the de Broglie internal clock) is here
the **mass parameter of the actual Dirac Hamiltonian operator** `H = α·p + βm`
(`Dirac.FourSpinorDiracHamiltonian.diracHamiltonian4`, `CausalDiamond.DiracMatter.diracEnergy`), so the mass becomes
a spectral statement about a genuine field operator. This is the mass leg complementing the
charge/spin-statistics/Pauli legs of `Winding.ChargeFockRealization`.

* **§A — operator dispersion.** `diracEnergy_comptonMass`: the Dirac energy is `E = √(p² + (ħω/c²)²)`;
 `diracHamiltonian4_sq_comptonMass`: the squared Dirac Hamiltonian operator is `H² = (p² + (ħω/c²)²)·1` — the
 matrix mass-shell with `m = comptonMass`.
* **§B — rest energy = clock energy.** `diracEnergy_rest_comptonMass`: at `p = 0` the Dirac rest energy equals
 the rest mass `E_rest = comptonMass`; `diracRestEnergy_comptonMass_planck`: `E_rest · c² = ħω` — the
 relativistic mass operator's rest energy is the de Broglie internal-clock energy.
* **§C — winding spectrum = Dirac mass spectrum.** `diracEnergy_windingMass`: the Dirac rest energy at winding
 `n` factorizes as `|n|·|comptonMass ω₀|` — the winding mass spectrum `m_n = n m₀` is the spectrum of Dirac
 rest masses (one unit Dirac mass per winding).

Genuine operator facts: `diracEnergy`/`diracHamiltonian4` are the real Dirac field
operator (`H = α·p + βm`, `H² = (p²+m²)·1`); feeding `m = comptonMass` is exact. `diracEnergy` is written in
units where the rest mass enters as `m` (so `E² = p² + m²`); the dimensionful clock energy `ħω` is recovered
by the explicit `·c²` (§B). The identification of the clock frequency with this rest mass is the
`Winding.NumberMass` content (`m = ħω/c²` genuine de Broglie clock; `m_n ∝ n` the winding-number hypothesis).

## References

* `Physlib` (`CausalDiamond.DiracMatter.diracEnergy`/`diracHamiltonian4_sq_energy`,
 `Dirac.FourSpinorDiracHamiltonian.diracHamiltonian4`, `Winding.NumberMass.comptonMass`/`windingMass`).

No additional assumptions.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMatter
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator

/-! ## §A — the Dirac operator with the winding mass -/

/-- **[Dirac dispersion]** `E_D = √(p² + (ħω/c²)²)`: the Dirac one-particle energy with the rest mass
`m = comptonMass ω c ħ`. -/
theorem diracEnergy_comptonMass (p1 p2 p3 ω c ħ : ℝ) :
    diracEnergy p1 p2 p3 (comptonMass ω c ħ)
      = Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + (ħ * ω / c ^ 2) ^ 2) := by
  rw [diracEnergy, comptonMass]

/-- **[The squared Dirac Hamiltonian]** `H² = (p² + (ħω/c²)²)·1` — the matrix mass-shell of the Dirac operator
`H = α·p + βm` with `m = comptonMass ω c ħ`. The mass squared is the operator's mass term. -/
theorem diracHamiltonian4_sq_comptonMass (p1 p2 p3 ω c ħ : ℝ) :
    diracHamiltonian4 p1 p2 p3 (comptonMass ω c ħ) * diracHamiltonian4 p1 p2 p3 (comptonMass ω c ħ)
      = ((p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + (comptonMass ω c ħ) ^ 2 : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [diracHamiltonian4_sq_energy, diracEnergy_sq]

/-! ## §B — rest energy = de Broglie internal-clock energy -/

/-- **[Dirac rest energy = rest mass]** at `p = 0` the Dirac rest energy is `E_rest = comptonMass ω c ħ` (for
nonnegative mass). -/
theorem diracEnergy_rest_comptonMass (ω c ħ : ℝ) (hm : 0 ≤ comptonMass ω c ħ) :
    diracEnergy 0 0 0 (comptonMass ω c ħ) = comptonMass ω c ħ := by
  rw [diracEnergy,
    show (0 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 + (comptonMass ω c ħ) ^ 2 = (comptonMass ω c ħ) ^ 2 from by ring,
    Real.sqrt_sq hm]

/-- **[Rest energy × c² = ħω]** `E_rest · c² = ħω`: the relativistic mass operator's rest energy is the de
Broglie internal-clock energy (`E = mc² = ħω`). -/
theorem diracRestEnergy_comptonMass_planck (ω c ħ : ℝ) (hc : c ≠ 0) (hm : 0 ≤ comptonMass ω c ħ) :
    diracEnergy 0 0 0 (comptonMass ω c ħ) * c ^ 2 = ħ * ω := by
  rw [diracEnergy_rest_comptonMass ω c ħ hm, ← comptonMass_restEnergy ω c ħ hc]

/-! ## §C — the winding spectrum is the Dirac rest-mass spectrum -/

/-- **[Winding spectrum = Dirac mass spectrum]** the Dirac rest energy at winding `n` is
`|n|·|comptonMass ω₀ c ħ|`: the winding mass spectrum `m_n = n m₀` is the spectrum of Dirac rest masses — one
unit Dirac mass per winding. -/
theorem diracEnergy_windingMass (n : ℤ) (ω₀ c ħ : ℝ) :
    diracEnergy 0 0 0 (windingMass n ω₀ c ħ) = |(n : ℝ)| * |comptonMass ω₀ c ħ| := by
  rw [diracEnergy, windingMass_eq_zsmul,
    show (0 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 + ((n : ℝ) * comptonMass ω₀ c ħ) ^ 2
      = ((n : ℝ) * comptonMass ω₀ c ħ) ^ 2 from by ring,
    Real.sqrt_sq_eq_abs, abs_mul]

end Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator

end

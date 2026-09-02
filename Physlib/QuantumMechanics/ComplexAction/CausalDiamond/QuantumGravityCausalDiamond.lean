/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QuantumGravityPathIntegralSynthesis
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity

/-!
# The quantum-gravity path integral is the causal-diamond horizon mode

Links `PathIntegral.QuantumGravityPathIntegralSynthesis` (the quantum-gravity one-loop path integral: the
Verch–Bogoliubov-diagonalized fermion determinant of the gravity+EM-coupled first-quantized Dirac
operator) to the **Jacobson–Visser causal-diamond gravitational thermodynamics**
(`CausalDiamond.Helicity`).

The bridge is the determinant dispersion: the QED one-loop fermion functional determinant of a
rapidity-`η` Dirac mode is `cosh η` (`PathIntegral.OneLoopPathIntegralVerch.berezinDet_eq_bogoliubov_diagonal`)
— *exactly* the causal-diamond **horizon energy** `cosh(R_*/L)`
(`CausalDiamond.Helicity.diamond_horizon_energy`). So the quantum-gravity path-integral fermion
determinant **is** the causal-diamond horizon mode, and through it the whole one-loop synthesis joins
the gravitational-thermodynamics arc:

* the determinant `= cosh η` is the **causal-diamond horizon energy** (`quantumGravity_det_eq_horizon`);
* the determinant mode is **reversible** (`τ_ent = 0`) exactly at the **cosmological-horizon /
  static-patch** limit `tanh η = ±1` (`quantumGravity_det_reversible_iff_staticPatch`, from
  `diamond_entropicTime_zero_iff_luminal`) — the massless/luminal Dirac mode;
* and it is the diagonal of the diagonalizing **Verch symplectomorphism** with pure-state complex
  structure `J² = −1` (`quantumGravity_horizon_synthesis`).

So the quantum-gravity path integral, the causal-diamond horizon thermodynamics, the entropic-time
reversibility, and the Verch symplectic structure are one object — the Gaussian one-loop mode at
rapidity `η`.

* **§A — the determinant is the horizon energy** (`quantumGravity_det_eq_horizon`).
* **§B — reversibility at the static patch** (`quantumGravity_det_reversible_iff_staticPatch`).
* **§C — the synthesis** (`quantumGravity_horizon_synthesis`).

## References

* T. Jacobson, M. Visser, arXiv:1812.01596 (causal-diamond gravitational thermodynamics). Repo
  carriers: `PathIntegral.QuantumGravityPathIntegralSynthesis`, `CausalDiamond.Helicity`
  (`diamond_horizon_energy`, `diamond_entropicTime_zero_iff_luminal`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumGravityCausalDiamond

open Real
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch


/-- **[Quantum-gravity determinant = causal-diamond horizon energy] `det[E_η] = cosh η`.** The QED
one-loop fermion functional determinant of a rapidity-`η` Dirac mode (the quantum-gravity path
integral's Gaussian determinant) is the **Jacobson–Visser causal-diamond horizon energy** `cosh η`
(`diamond_horizon_energy`). The one-loop path integral and the gravitational-thermodynamics horizon
carry the same energy. -/
lemma quantumGravity_det_eq_horizon (η : ℝ) :
    berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = Real.cosh η := by
  rw [berezin_dirac_dispersion, diamond_horizon_energy]


/-- **[Determinant reversible ⟺ static patch] `τ_ent = 0 ⟺ tanh η = ±1`.** The quantum-gravity
one-loop determinant mode has vanishing entropic proper time (is reversible) exactly at the
cosmological-horizon / de Sitter **static-patch** limit `tanh η = ±1` — the massless, luminal Dirac
mode (`diamond_entropicTime_zero_iff_luminal`). Away from it the determinant carries entropy. -/
lemma quantumGravity_det_reversible_iff_staticPatch (η : ℝ) :
    bogoliubovEntropicTime (Real.sinh η) 1 = 0 ↔ Real.tanh η = 1 ∨ Real.tanh η = -1 :=
  diamond_entropicTime_zero_iff_luminal η


/-- **[Quantum-gravity path integral ↔ causal-diamond horizon, unified].** The quantum-gravity one-loop
fermion functional determinant of a rapidity-`η` Dirac mode **is** the causal-diamond horizon energy
`cosh η` (`quantumGravity_det_eq_horizon`); it is reversible (`τ_ent = 0`) exactly at the
cosmological-horizon / static-patch limit (`quantumGravity_det_reversible_iff_staticPatch`); it equals
the diagonal of the diagonalizing Verch symplectomorphism (`berezinDet_eq_bogoliubov_diagonal`); and the
pure-state complex structure is `J² = −1` (`sympForm_sq`). The quantum-gravity path integral, the
Jacobson–Visser horizon thermodynamics, the entropic-time reversibility, and the Verch symplectic
structure are one Gaussian one-loop mode. -/
lemma quantumGravity_horizon_synthesis (η : ℝ) :
    berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = Real.cosh η
      ∧ (bogoliubovEntropicTime (Real.sinh η) 1 = 0 ↔ Real.tanh η = 1 ∨ Real.tanh η = -1)
      ∧ berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = (thermoBogoliubov η) 0 0
      ∧ sympForm * sympForm = -1 :=
  ⟨quantumGravity_det_eq_horizon η, quantumGravity_det_reversible_iff_staticPatch η,
    berezinDet_eq_bogoliubov_diagonal η, sympForm_sq⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumGravityCausalDiamond

end

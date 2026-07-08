/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameReversible

/-!
# `T = 0` thermal frame = reversible Quantum Inertial Frame = no action with no information

This file links the thermodynamic "no action with no information" main result
(`ThermoFieldDynamics.ThermodynamicCanonicalQuantization` §D) to the operator-level **Quantum Inertial Frame**
(`QuantumMechanics.FiniteTarget.QuantumInertialFrame`,
`QuantumMechanics.FiniteTarget.reversibleQIF`).

## The two formalisations of the same physics

* **QIF (operator level).** A `QuantumInertialFrame` bundles `H_R`, a positive dissipator
  `H_I`, and `ℏ`. Its local entropic rate is `λ(ψ) = ⟨H_I⟩_ψ/ℏ`. An *equilibrium* QIF
  (`λ(ψ) = 0`) forces `H_I ψ = 0`, so `H_C ψ = H_R ψ` (unitary), and the `reversibleQIF`
  (`H_I := 0`) is at equilibrium at **every** state.
* **complex-action/entropic-time (matrix / spectral level).** For `H_C = P D P⁻¹` the dissipator is
  `H_I = P·diagonal(−Im λ)·P⁻¹` (`NonHermitianComplexAction.ComplexHamiltonian`), the propagator is
  `greenKernel λ ℏ t = e^{−iλt/ℏ}`, and the entropic action weight is `thermoActionWeight`.
  §D's `no_action_no_information` says `Im λ = 0 ⟺ ‖greenKernel‖ = 1 ∧ ‖thermoActionWeight‖ = 1`.

`Im λ = 0` (spectral) is exactly the eigenvalue form of `H_I = 0` (operator): the reversible
QIF is the regime where the propagator is unimodular and the path weight is a pure phase.

## The `T = 0` connective: the KMS thermal rate

The bridge between *temperature* and the QIF entropic rate is the KMS thermal rate
`λ_KMS = k_B T/ℏ` (`kmsThermalRate`), the universal rate of a stationary thermal frame in
the Connes–Rovelli thermal-time hypothesis. At `T = 0`:

  `T = 0  ⟺  λ_KMS = 0  =  (reversibleQIF).entropicRate ψ  ⟺  H_I = 0  ⟺  S_I = 0`.

So the third-law limit `T → 0` is *literally* the reversible QIF — every state at
equilibrium, no dissipative generator, unitary propagation, zero imaginary action, and (in
the computability reading) no information erased / no Landauer cost
(`RelationalTime.EntropicLandauer.landauer_export`).

## Main theorems

* `kmsThermalRate_eq_zero_iff` — `λ_KMS = k_B T/ℏ = 0 ⟺ T = 0` (third-law / Nernst form).
* `reversibleQIF_entropicRate_eq_kmsThermalRate_zero` — the reversible QIF's entropic rate
  equals the `T = 0` thermal rate (both `0`): the reversible QIF *is* the `T = 0` frame.
* `reversibleQIF_no_action_no_information` — at a reversible QIF every state is at
  equilibrium and (on a real-eigenvalue mode `Im λ = 0`) the Green kernel is unitary and the
  thermodynamic weight is a pure phase.

## References

* Garcia 2026 APS PRL submission v3, §"Equilibrium vs Non-Equilibrium Quantum Reference
  Frames" — the QIF distinction and equilibrium ⟹ TISE chain.
* Connes & Rovelli 1994, Class. Quant. Grav. 11, 2899 — thermal time hypothesis
  (`λ_KMS = 1/(βℏ)`).
* K. Nagao, H. B. Nielsen, arXiv:1104.3381; Sergi & Giaquinta 2016 — `H_C = H_R − iH_I`,
  the `H_I = 0` reversible limit.
* Lima et al., arXiv:2511.14121 — canonical quantization for equilibrium thermodynamics
  (the `b̄`-scaled action weight of §D).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open QuantumMechanics.FiniteTarget
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.QIFThermodynamicReversible

/-! ## §A — `T = 0 ⟺ λ_KMS = 0` (the Nernst / third-law form of the thermal rate) -/

/-- **The KMS thermal rate vanishes iff `T = 0`** (third law / Nernst): with `k_B, ℏ > 0`,
`λ_KMS = k_B T/ℏ = 0 ⟺ T = 0`. The temperature-side of the equilibrium-QIF condition. -/
theorem kmsThermalRate_eq_zero_iff {kB ℏ : ℝ} (hkB : 0 < kB) (hℏ : 0 < ℏ) (T : ℝ) :
    kmsThermalRate kB T ℏ = 0 ↔ T = 0 := by
  unfold kmsThermalRate
  rw [div_eq_zero_iff, mul_eq_zero]
  simp [ne_of_gt hkB, ne_of_gt hℏ]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §B — The reversible QIF is the `T = 0` thermal frame -/

/-- **The reversible QIF is the `T = 0` thermal frame**: its entropic rate `λ(ψ) = 0`
coincides with the KMS thermal rate at `T = 0`, `λ_KMS = k_B·0/ℏ = 0`. Every state of the
reversible (`H_I = 0`) frame sits at the zero-temperature, zero-entropy-production point. -/
theorem reversibleQIF_entropicRate_eq_kmsThermalRate_zero
    (H_R : H →L[ℂ] H) (kB ℏ : ℝ) (hℏ : 0 < ℏ) (ψ : H) :
    (reversibleQIF H_R ℏ hℏ).entropicRate ψ = kmsThermalRate kB 0 ℏ := by
  rw [reversibleQIF_entropicRate]
  simp [kmsThermalRate]

/-! ## §C — Reversible QIF ⟹ no action with no information -/

/-- **Reversible QIF ⟹ no action with no information.** At a reversible QIF (`H_I = 0`) every
state is at equilibrium, and on any real-eigenvalue mode (`Im λ = 0`, the spectral form of
`H_I = 0`) the Green kernel `e^{−iλt/ℏ}` is unitary and the thermodynamic action weight is a
pure phase — the `T = 0`, `S_I = 0`, reversible / Landauer-free regime of §D. -/
theorem reversibleQIF_no_action_no_information
    (H_R : H →L[ℂ] H) (ℏ : ℝ) (hℏ : 0 < ℏ) (ψ : H)
    {t : ℝ} (ht : t ≠ 0) {lam : ℂ} (hI : lam.im = 0) (S_R : ℝ) :
    (reversibleQIF H_R ℏ hℏ).IsEquilibriumAt ψ
      ∧ ‖greenKernel lam ℏ t‖ = 1
      ∧ ‖thermoActionWeight S_R (-lam.im * t) ℏ‖ = 1 :=
  ⟨reversibleQIF_isEquilibriumAt H_R ℏ hℏ ψ,
   (no_action_no_information (ne_of_gt hℏ) ht lam S_R).mp hI⟩

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.QIFThermodynamicReversible

end

end

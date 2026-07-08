/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-!
# Linking the anomalous magnetic moment to the spin projectors and the Maxwell field

Wires `FirstQuantizedQED.AnomalousMagneticMoment` (the Pauli spin tensor `σ^{μν}`, the g-factor) into the rest of
the Bennett / Greaves–Thomas arc:

* **§A — the magnetic-moment operator IS the spin-projector operator.** The `z`-magnetic-moment
  operator `σ^{12} = iγ¹γ²` equals `−γ⁰(γ⁵γ³)` (`spinTensor_12_eq_spinProjectorOp`), where `γ⁵γ³` is
  the rest-frame `z`-spin operator of `FirstQuantizedQED.ChiralityHelicityProjectors.spin_projectors`
  (`s̸ = γ³`). So the Bennett spin projectors `(1 ∓ γ⁵s̸)/2` are exactly the projectors onto the
  magnetic-moment operator's `±1` eigenstates (`γ⁵γ³ = −γ⁰σ^{12}`,
  `spinProjectorOp_eq_magneticMoment`); both are involutions (`γ5γ3_sq`, `spinTensor_12_involution`).

* **§B — the Pauli coupling to the Maxwell field.** The magnetic-moment interaction is the contraction
  `σ^{μν}F_{μν}` (`pauliCoupling`) of the spin tensor with the **Faraday tensor**
  (`PTSymmetricQFT.MaxwellFaraday.faraday`, `F = dA`). Being a contraction with `F`, it is
  **gauge-invariant** (`pauliCoupling_gauge_invariant`, from `faraday_gauge_invariant`). The full
  interaction `(g/2)·σ^{μν}F_{μν}` (`magneticInteraction`) reduces to the pure Dirac coupling at
  `g = 2` (`magneticInteraction_dirac`) and splits as `1 + a` — the Dirac moment plus the anomalous
  correction — at `g = 2(1 + a)` (`magneticInteraction_gFactor`).

So the anomalous moment `a` (Bennett §VI) is the radiative shift of the coefficient of the
gauge-invariant Pauli term `σ^{μν}F_{μν}`, whose operator `σ^{12}` is the Bennett spin projector's
spin operator.

* **§A** (`spinTensor_12_eq_spinProjectorOp`, `spinProjectorOp_eq_magneticMoment`).
* **§B** (`pauliCoupling`, `pauliCoupling_gauge_invariant`, `magneticInteraction`,
  `magneticInteraction_dirac`, `magneticInteraction_gFactor`).
* **§C** (`anomalous_moment_links`).

## References

* A. F. Bennett, arXiv:1406.0750v3, §VI. Repo dependencies: `FirstQuantizedQED.AnomalousMagneticMoment`
  (`spinTensor`, `gFactor`), `FirstQuantizedQED.ChiralityHelicityProjectors` (`spin_projectors`, `γ5γ3_sq`),
  `PTSymmetricQFT.MaxwellFaraday` (`faraday`, `faraday_gauge_invariant`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMomentLinks

open Complex spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-! ## §A — the magnetic-moment operator is the spin-projector operator -/

/-- **[Magnetic moment = spin-projector operator] `σ^{12} = −γ⁰(γ⁵γ³)`.** The `z`-magnetic-moment
operator `σ^{12} = iγ¹γ²` is `−γ⁰` times the rest-frame `z`-spin operator `γ⁵γ³` used by
`FirstQuantizedQED.ChiralityHelicityProjectors.spin_projectors` (with `s̸ = γ³`). -/
theorem spinTensor_12_eq_spinProjectorOp : spinTensor 1 2 = -(γ0 * (γ5 * γ3)) := by
  rw [spinTensor_12_eq, γ5, Matrix.smul_mul, Matrix.mul_smul, ← smul_neg]
  congr 1
  have e : γ0 * (γ0 * γ1 * γ2 * γ3 * γ3) = γ0 * γ0 * γ1 * γ2 * (γ3 * γ3) := by noncomm_ring
  rw [e, γ0_mul_γ0, γ3_mul_γ3, one_mul, mul_neg, mul_one, neg_neg]

/-- **[Spin-projector operator = γ⁰-dressed magnetic moment] `γ⁵γ³ = −γ⁰σ^{12}`.** The Bennett spin
projectors `(1 ∓ γ⁵s̸)/2` are therefore the projectors onto the magnetic-moment operator's `±1`
eigenstates (dressed by the Dirac energy sign `γ⁰`). -/
theorem spinProjectorOp_eq_magneticMoment : γ5 * γ3 = -(γ0 * spinTensor 1 2) := by
  rw [spinTensor_12_eq_spinProjectorOp, mul_neg, ← mul_assoc, γ0_mul_γ0, one_mul, neg_neg]

/-! ## §B — the Pauli coupling to the Maxwell (Faraday) field -/

/-- **The Pauli coupling** `σ^{μν}F_{μν} = ∑_{μν} F_{μν}·σ^{μν}` — the magnetic-moment interaction of
the spin tensor with an antisymmetric field strength `F` (the Pauli term `ψ̄σ^{μν}F_{μν}ψ`). -/
noncomputable def pauliCoupling (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, (F μ ν : ℂ) • spinTensor μ ν

/-- **[Gauge invariance of the Pauli coupling] `σ^{μν}F[A + dχ]_{μν} = σ^{μν}F[A]_{μν}`.** The
magnetic-moment interaction with the Maxwell field `F = dA` is gauge-invariant, since it contracts the
spin tensor with the gauge-invariant Faraday tensor (`faraday_gauge_invariant`). -/
theorem pauliCoupling_gauge_invariant (k A : Fin 4 → ℝ) (χ : ℝ) :
    pauliCoupling (faraday k (fun ρ => A ρ + χ * k ρ)) = pauliCoupling (faraday k A) :=
  congrArg pauliCoupling (faraday_gauge_invariant k A χ)

/-- **The magnetic-moment interaction** `(g/2)·σ^{μν}F_{μν}` — the Pauli coupling weighted by the
gyromagnetic ratio `g/2`. -/
noncomputable def magneticInteraction (g : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((g : ℂ) / 2) • pauliCoupling F

/-- **[Pure Dirac moment at `g = 2`] the interaction is exactly the Pauli coupling.** With the
tree-level Dirac g-factor `g = 2`, the magnetic-moment interaction is the bare `σ^{μν}F_{μν}` (the
Dirac moment `μ_B`), no anomalous part. -/
theorem magneticInteraction_dirac (F : Matrix (Fin 4) (Fin 4) ℝ) :
    magneticInteraction (gFactor 0) F = pauliCoupling F := by
  rw [magneticInteraction, gFactor_dirac]
  push_cast
  rw [show (2 : ℂ) / 2 = 1 from by norm_num, one_smul]

/-- **[Dirac + anomalous split] `(g/2)·σ^{μν}F_{μν} = (1 + a)·σ^{μν}F_{μν}`** at `g = 2(1 + a)`. The
interaction is the Dirac moment (`1`) plus the anomalous correction (`a`, the Schwinger value
`α/(2π)`); at `a = 0` it collapses to the pure Dirac coupling (`magneticInteraction_dirac`). -/
theorem magneticInteraction_gFactor (a : ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ) :
    magneticInteraction (gFactor a) F = ((1 + a : ℂ)) • pauliCoupling F := by
  rw [magneticInteraction, gFactor]
  push_cast
  rw [show ((2 : ℂ) * (1 + a)) / 2 = 1 + a from by ring]

/-! ## §C — the unification -/

/-- **[Anomalous moment, linked] one structure across spin projectors and the Maxwell field.** The
`z`-magnetic-moment operator `σ^{12}` is the Bennett spin-projector operator `γ⁵γ³` dressed by `γ⁰`
(`spinProjectorOp_eq_magneticMoment`); the Pauli coupling `σ^{μν}F_{μν}` to the Maxwell field is
gauge-invariant (`pauliCoupling_gauge_invariant`); and the full interaction is `(1 + a)·σ^{μν}F_{μν}`,
the Dirac moment plus the anomalous correction `a` (`magneticInteraction_gFactor`). -/
theorem anomalous_moment_links (k A : Fin 4 → ℝ) (χ a : ℝ) :
    γ5 * γ3 = -(γ0 * spinTensor 1 2)
      ∧ pauliCoupling (faraday k (fun ρ => A ρ + χ * k ρ)) = pauliCoupling (faraday k A)
      ∧ magneticInteraction (gFactor a) (faraday k A)
          = ((1 + a : ℂ)) • pauliCoupling (faraday k A) :=
  ⟨spinProjectorOp_eq_magneticMoment, pauliCoupling_gauge_invariant k A χ,
    magneticInteraction_gFactor a (faraday k A)⟩

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMomentLinks

end

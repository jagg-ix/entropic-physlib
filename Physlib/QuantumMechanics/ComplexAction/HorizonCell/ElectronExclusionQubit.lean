/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionMutex
public import Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics

/-!
# The exclusion cell is a qubit, not a bit: the Bloch sphere and its classical shadow

A correction and refinement of the electron-exclusion-cell arc. The earlier modules called the cell a
"one-bit register"; that is the *classical shadow*. The exclusion cell — a fermion mode `f` with the
two-level Hilbert space `{|0⟩ empty, |1⟩ occupied}` — is a **qubit**: its pure states are the amplitudes
`α|0⟩ + β|1⟩` on the **Bloch sphere** (`LorenzQubitBlochDynamics.BlochSphere`), with a **phase** (the
`CP¹` ray, `hopfBlochVector_phase_invariant`) that a classical bit has no analogue of. The electron's spin-½ —
the Zitterbewegung double cover, the `m_s = ±½` doublet — *is* this qubit's Bloch two-level.

* the **qubit state** is a spinor `χ : Fin 2 → ℂ` whose Bloch vector lies on the Poincaré/Bloch sphere
 (`exclusionCell_qubit_on_blochSphere`, reusing `hopfBlochVector_lies_on_poincare_sphere`);
* it has a **U(1) phase** invisible to the Bloch vector — the genuinely quantum degree of freedom absent
 in a classical bit (`exclusionCell_qubit_phase_invariant`);
* **Pauli exclusion is the computational-basis projection** `n = f†f`, `n² = n`
 (`exclusionCell_pauli_is_projection`) — the *measurement* along the `|0⟩/|1⟩` axis, whose two outcomes are the
 classical bit;
* the **classical bit is only the two poles**: the maximally-mixed cell is the Bloch-ball *centre*
 `r = 0` — a mixed qubit state (`exclusionCell_maximallyMixed_in_ball`) that is *not* a pure state
 (`exclusionCell_maximallyMixed_not_pure`), with no classical-bit analogue. (This is the massless-critical
 half-occupation of `ElectronExclusionThermalBoundary`, now correctly read as the maximally-mixed qubit
 `⟨n⟩ = 1/2`, not a bit value.)

**So every "one bit" in the arc should be read as "one qubit, whose classical (diagonal) shadow is one bit":**
the exclusion cell holds one *qubit* of information; the Landauer/Bekenstein `bit` counts are its
computational-basis measurement.

* **§A — the qubit state and its phase** (`exclusionCell_qubit_on_blochSphere`,
 `exclusionCell_qubit_phase_invariant`).
* **§B — Pauli is the computational-basis projection** (`exclusionCell_pauli_is_projection`).
* **§C — the classical bit is the poles; mixed qubits fill the ball** (`exclusionCell_maximallyMixed_in_ball`,
 `exclusionCell_maximallyMixed_not_pure`).

All facts are exact reuse of `LorenzQubitBlochDynamics`
(`hopfBlochVector_lies_on_poincare_sphere`, `hopfBlochVector_phase_invariant`, `BlochBall`, `BlochSphere`) and
`ElectronExclusionMutex.pauliExclusion_is_mutexInvariant`. The content is the *correction*: the two-level
exclusion cell is a qubit (Bloch sphere + phase + mixed interior), and the earlier bit results are its
classical shadow. No new axioms.

## References

* Repo dependencies: `LorenzQubitBlochDynamics` (Bloch sphere / Hopf spinor / phase),
 `HorizonCell.ElectronExclusionMutex`, `Particles.AtomicModeBundleGeometry` (the spin doublet `CP¹`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionMutex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionQubit

/-! ## §A — the qubit state and its phase -/

/-- **[The exclusion cell's state is a qubit on the Bloch sphere].** The cell's two-level amplitudes
`χ : Fin 2 → ℂ` (`α|0⟩ + β|1⟩`) determine a Bloch vector `r` lying on the Poincaré/Bloch sphere of radius
`hopfIntensity χ`: the pure states of the exclusion-cell qubit are the Bloch sphere, not two classical
values. -/
theorem exclusionCell_qubit_on_blochSphere (χ : Fin 2 → ℂ) (r : BlochVector)
    (h : IsHopfBlochVector χ r) :
    (r 0 : ℂ) ^ 2 + (r 1 : ℂ) ^ 2 + (r 2 : ℂ) ^ 2 = hopfIntensity χ ^ 2 :=
  hopfBlochVector_lies_on_poincare_sphere χ r h

/-- **[The qubit has a U(1) phase a classical bit lacks].** Rotating the cell's spinor by a global phase
`u` (`|u| = 1`) leaves the Bloch vector unchanged — the qubit state is a `CP¹` ray with a phase degree of
freedom (the equatorial/superposition structure) that is invisible in, and absent from, a classical bit. -/
theorem exclusionCell_qubit_phase_invariant (u : ℂ) (χ : Fin 2 → ℂ) (r : BlochVector)
    (hu : star u * u = 1) (h : IsHopfBlochVector χ r) :
    IsHopfBlochVector (phaseRotate u χ) r :=
  hopfBlochVector_phase_invariant u χ r hu h

/-! ## §B — Pauli exclusion is the computational-basis projection -/

variable {A : Type*} [Ring A] [StarRing A]

/-- **[Pauli exclusion is the qubit's computational-basis projection] `n² = n`.** The occupation
`n = f†f` of the cell's mode is a projection (`mutexInvariant`) — the measurement along the `|0⟩/|1⟩`
(empty/occupied) axis of the qubit, whose two eigenvalues are the classical bit outcomes. The exclusion is the
measurement; the qubit is the state. -/
theorem exclusionCell_pauli_is_projection (f : A) (h : IsFermionMode f) :
    mutexInvariant (fermionNumber f) :=
  pauliExclusion_is_mutexInvariant f h

/-! ## §C — the classical bit is the poles; mixed qubits fill the ball -/

/-- **[The maximally-mixed cell is the Bloch-ball centre] `r = 0 ∈ BlochBall`.** The massless-critical
half-occupied cell (`⟨n⟩ = 1/2` of `ElectronExclusionThermalBoundary`) is the centre of the Bloch ball — a
*mixed* qubit state, a genuine point of the qubit's state space with no classical-bit analogue. -/
theorem exclusionCell_maximallyMixed_in_ball : BlochBall (0 : BlochVector) := by
  simp [BlochBall]

/-- **[The maximally-mixed cell is not a pure state] `r = 0 ∉ BlochSphere`.** The Bloch-ball centre is not on
the Bloch sphere: the maximally-mixed qubit is not a pure state. The pure states (the sphere, with the poles
being the classical bit values `|0⟩, |1⟩`) and the mixed interior together are the qubit — the classical bit
is only the two poles. -/
theorem exclusionCell_maximallyMixed_not_pure : ¬ BlochSphere (0 : BlochVector) := by
  simp [BlochSphere]

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionQubit

end

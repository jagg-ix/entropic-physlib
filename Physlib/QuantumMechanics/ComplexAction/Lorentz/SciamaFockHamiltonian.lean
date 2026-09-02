/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockLadder

/-!
# The single-mode Hamiltonian `H = ℏω(N + ½)` on the bosonic Fock space

The generator of the mode's dynamics — and of its thermal state.  With the number operator `N = a†a`
(`SciamaBosonicFockSpace`), the harmonic-oscillator Hamiltonian is `H = ℏω(N + ½)` (units `ℏ = 1`), diagonal
in the number basis with eigenvalues `E_n = ℏω(n + ½)`.

* `hamiltonianOp`, `oscillatorEnergy` — `H = ω N + (ω/2) 𝟙` and the eigenvalue `E_n = ω(n + ½)`.
* `hamiltonianOp_numberKet` — `H|n⟩ = ω(n + ½)|n⟩`: the number states are energy eigenstates.
* `hamiltonianOp_vacuum` — `H|0⟩ = (ω/2)|0⟩`: the **zero-point energy** `ℏω/2`.
* `oscillatorEnergy_succ_sub` — `E_{n+1} − E_n = ω`: uniform level spacing `ℏω`.

This is the operator whose Gibbs weighting produces the thermality of the arc: the density matrix
`ρ ∝ e^{−βH}` weights level `n` by `e^{−βω n}` (up to the zero-point shift), the Gibbs distribution whose mean
occupation is the Bose–Einstein `n(ω)` (`SciamaThermalDensityMatrix.thermal_mean_occupation`).  In the
entropic-clock reading the mode frequency is the Compton rate `ω = mc²/ℏ`, so the zero-point energy is `mc²/2`.

Honest scope: the diagonal Hamiltonian on the algebraic Fock space and its spectrum; the exponential
`e^{−βH}` as a bounded operator and the trace are contextualized, not built.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockHamiltonian

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockLadder

/-- **The single-mode Hamiltonian** `H = ℏω(N + ½) = ω N + (ω/2) 𝟙` (units `ℏ = 1`). -/
def hamiltonianOp (ω : ℝ) : FockSpace →ₗ[ℂ] FockSpace :=
  (ω : ℂ) • numberOp + ((ω / 2 : ℝ) : ℂ) • LinearMap.id

/-- **The oscillator energy level** `E_n = ℏω(n + ½)`. -/
def oscillatorEnergy (ω : ℝ) (n : ℕ) : ℝ := ω * ((n : ℝ) + 1 / 2)

/-- **[Energy eigenstate] `H|n⟩ = ω(n + ½)|n⟩`.**  The number states are eigenstates of the Hamiltonian with
eigenvalue `E_n = ℏω(n + ½)`. -/
theorem hamiltonianOp_numberKet (ω : ℝ) (n : ℕ) :
    hamiltonianOp ω (numberKet n) = ((oscillatorEnergy ω n : ℝ) : ℂ) • numberKet n := by
  rw [hamiltonianOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    numberOp_numberKet, LinearMap.id_apply, smul_smul, ← add_smul]
  congr 1
  rw [oscillatorEnergy]
  push_cast
  ring

/-- **[Zero-point energy] `H|0⟩ = (ω/2)|0⟩`.**  The vacuum is not annihilated by `H`: it carries the
zero-point energy `ℏω/2` (the vacuum energy whose observer-dependent reshuffling is the whole subject of the
Sciama arc). -/
theorem hamiltonianOp_vacuum (ω : ℝ) :
    hamiltonianOp ω vacuum = ((ω / 2 : ℝ) : ℂ) • vacuum := by
  rw [vacuum, hamiltonianOp_numberKet]
  congr 1
  rw [oscillatorEnergy]
  push_cast
  ring

/-- **[Ground-state eigenvalue] `E_0 = ω/2`.** -/
theorem oscillatorEnergy_zero (ω : ℝ) : oscillatorEnergy ω 0 = ω / 2 := by
  rw [oscillatorEnergy]; push_cast; ring

/-- **[Uniform level spacing] `E_{n+1} − E_n = ℏω`.**  The energy ladder is evenly spaced by one quantum
`ℏω` — the property that makes the mode a harmonic oscillator and its Gibbs sum geometric. -/
theorem oscillatorEnergy_succ_sub (ω : ℝ) (n : ℕ) :
    oscillatorEnergy ω (n + 1) - oscillatorEnergy ω n = ω := by
  rw [oscillatorEnergy, oscillatorEnergy]
  push_cast
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockHamiltonian

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Schrodinger.HamiltonJacobiMadelung
public import Physlib.QuantumMechanics.Schrodinger.BadialiToBohmianQuantumPotential

/-!
# The Hamilton–Jacobi–Madelung equation for the Badiali stochastic amplitude

Links `HamiltonJacobiMadelung` (the quantum Hamilton–Jacobi equation `∂tS + |∇S|²/(2m) + V + Q = 0`) to
`BadialiToBohmianQuantumPotential` (the forward–backward stochastic amplitude `R = √(φ·φ̂)` of Badiali 2005,
with its quantum potential `badialiQuantumPotential = quantumPotential (badialiAmplitude φ φ̂)`).

Instantiating the de Broglie–Bohm equation with the (time-independent) Badiali amplitude makes the quantum
potential the **Badiali quantum potential** of the forward/backward density product:

  `quantumHJResidual S V (fun _ => √(φ·φ̂)) = classicalHJResidual S V + badialiQuantumPotential φ φ̂`
  (`badiali_quantumHJResidual`),

so the phase obeys the Hamilton–Jacobi equation driven by the Badiali quantum potential, and (de Broglie–Bohm)
it is the classical Hamilton–Jacobi equation in the effective potential `V + Q_Badiali`
(`badiali_quantumHamiltonJacobi_iff`). This ties the **phase dynamics** (Hamilton–Jacobi) to the **Badiali
forward–backward density picture** (amplitude/quantum potential).

## References

* J. P. Badiali (2005); D. Bohm (1952). structure: `Physlib`
  (`HamiltonJacobiMadelung`, `BadialiToBohmianQuantumPotential`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.Schrodinger

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **[The de Broglie–Bohm quantum potential of the Badiali amplitude is the Badiali quantum potential].** The
quantum Hamilton–Jacobi residual with amplitude `R = √(φ·φ̂)` is the classical residual plus
`badialiQuantumPotential`. -/
theorem badiali_quantumHJResidual (S V : ℝ → E → ℝ) (φ φ_hat : E → ℝ) (m ℏ t : ℝ) (x : E) :
    quantumHJResidual S V (fun _ => badialiAmplitude φ φ_hat) m ℏ t x
      = classicalHJResidual S V m t x + badialiQuantumPotential φ φ_hat m ℏ x := by
  simp only [quantumHJResidual, badialiQuantumPotential]

/-- **[de Broglie–Bohm picture for the Badiali amplitude]** the quantum Hamilton–Jacobi equation with the
Badiali forward–backward amplitude holds iff the classical equation holds in the effective potential
`V + Q_Badiali`. -/
theorem badiali_quantumHamiltonJacobi_iff (S V : ℝ → E → ℝ) (φ φ_hat : E → ℝ) (m ℏ : ℝ) :
    QuantumHamiltonJacobi S V (fun _ => badialiAmplitude φ φ_hat) m ℏ
      ↔ ClassicalHamiltonJacobi S (fun τ y => V τ y + badialiQuantumPotential φ φ_hat m ℏ y) m :=
  quantumHamiltonJacobi_iff_effective_classical S V (fun _ => badialiAmplitude φ φ_hat) m ℏ

end Physlib.QuantumMechanics.Schrodinger

end

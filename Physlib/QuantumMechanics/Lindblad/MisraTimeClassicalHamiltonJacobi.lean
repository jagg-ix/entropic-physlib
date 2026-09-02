/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
meta import Zil

/-!
# The Misra time operator and classical mechanics: Hamilton–Jacobi is the phase, `[L,T]=−iI` the pair

The classical-mechanics origin of the Misra internal time (`ZenoMisraTimeConjugacy`, `RelationalTime`). Two
classical facts feed it:

* the **Hamilton–Jacobi equation `∂tS = −H`** (`Schrodinger.HamiltonJacobiMadelung.ClassicalHamiltonJacobi`,
  `freeParticle_classicalHamiltonJacobi`: `∂tS = −‖k‖²/2m = −H`) — the classical action's time-derivative is
  minus the energy, so the phase `Ψ = e^{iS/ℏ}` obeys `iℏ ∂tΨ = H Ψ`: the energy *generates* the phase;
* the **canonical structure `{q,p} = 1`** (`ClassicalMechanics.HamiltonsEquations`, the symplectic form
  `J = !![0,1;-1,0]`, `hamilton_velocity`/`hamilton_force` giving `q̇ = ∂H/∂p`, `ṗ = −∂H/∂q`) — of which the Misra
  `i[L, T] = I` is the operator form for the **energy–time** pair.

Putting them together: the classical Hamilton–Jacobi phase `e^{−iHt/ℏ}` *is* the Liouville evolution factor `U_t`,
and the Misra internal time `T = i d/dλ` reads off the elapsed classical time `t` (`ageOperator_reads_evolution_time`).

* **§A — Hamilton–Jacobi generates the phase.** **`hamiltonJacobi_energy_generates_phase`** (`∂tS = −E ⟹
  iℏ ∂tΨ = E Ψ`, `Ψ = e^{iS/ℏ}`): the classical energy is the generator/frequency of the action phase — the
  content of `∂tS = −H`.
* **§B — the free-particle Newtonian energy.** **`freeParticle_energy_generates_phase`** — for the free action
  `S = px₀ − H t` with `H = newtonianHamiltonian m p = p²/2m` (`ComptonClock.NewtonianAndGRLimit`), the Newtonian
  Hamilton's-equations energy generates the phase.
* **§C — the Misra time reads the classical time.** **`misraTime_reads_classical_time`** (at the classical
  frequency `ω = E/ℏ`, `T U_t = t U_t`): the internal time reads the elapsed classical time `t` off the
  Hamilton–Jacobi evolution factor `U_t = e^{−iωt}`, via `ZenoMisraTimeConjugacy.ageOperator_reads_evolution_time`.

**Honest layering.** `hamiltonJacobi_energy_generates_phase` and `freeParticle_energy_generates_phase` are exact
`deriv`/`ring` identities with the Hamilton–Jacobi relation `∂tS = −E` as the (classical) input;
`misraTime_reads_classical_time` reuses the age-operator eigenvalue. The `{q,p}=1 ↔ [L,T]=−iI` correspondence is
the canonical-algebra reading (stated, referencing `symplecticForm2`), not a formal equality of the two objects.

## References

* Hamilton–Jacobi: `Schrodinger.HamiltonJacobiMadelung`; canonical structure: `ClassicalMechanics.HamiltonsEquations`
  (`symplecticForm2`); free Hamiltonian: `ComptonClock.NewtonianAndGRLimit`. Misra time: `ZenoMisraTimeConjugacy`,
  `RelationalTime.LiouvillianAgeOperator` (`i[L,T]=I`).


-/

set_option autoImplicit false

open Complex
open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz
open Physlib.QuantumMechanics.Lindblad.ZenoMisraTimeConjugacy
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit

@[expose] public section

namespace Physlib.QuantumMechanics.Lindblad.MisraTimeClassicalHamiltonJacobi


/-- **The classical energy generates the action phase** `iℏ ∂tΨ = E Ψ`, `Ψ = e^{iS/ℏ}` — given the Hamilton–Jacobi
relation `∂tS = −E` (the classical action's time-derivative is minus the energy,
`HamiltonJacobiMadelung.ClassicalHamiltonJacobi`), the phase oscillates at frequency `E/ℏ` with the energy as its
generator. This is the classical-mechanics source of the Liouville evolution factor whose Misra time is `t`. -/
lemma hamiltonJacobi_energy_generates_phase (S : ℝ → ℝ) (E ℏ t : ℝ) (hℏ : ℏ ≠ 0)
    (hS : HasDerivAt S (-E) t) :
    Complex.I * (ℏ : ℂ) * deriv (fun τ : ℝ => Complex.exp (Complex.I * (S τ : ℂ) / (ℏ : ℂ))) t
      = (E : ℂ) * Complex.exp (Complex.I * (S t : ℂ) / (ℏ : ℂ)) := by
  have hℏc : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  have hSc : HasDerivAt (fun τ : ℝ => (S τ : ℂ)) ((-E : ℝ) : ℂ) t := hS.ofReal_comp
  have hg : HasDerivAt (fun τ : ℝ => Complex.I * (S τ : ℂ) / (ℏ : ℂ))
      (Complex.I * ((-E : ℝ) : ℂ) / (ℏ : ℂ)) t := by
    simpa using (hSc.const_mul Complex.I).div_const (ℏ : ℂ)
  have hexp : HasDerivAt (fun τ : ℝ => Complex.exp (Complex.I * (S τ : ℂ) / (ℏ : ℂ)))
      (Complex.exp (Complex.I * (S t : ℂ) / (ℏ : ℂ)) * (Complex.I * ((-E : ℝ) : ℂ) / (ℏ : ℂ))) t := by
    simpa using hg.cexp
  rw [hexp.deriv]
  rw [show Complex.I * (ℏ : ℂ) *
        (Complex.exp (Complex.I * (S t : ℂ) / (ℏ : ℂ)) * (Complex.I * ((-E : ℝ) : ℂ) / (ℏ : ℂ)))
      = (Complex.I * Complex.I) * ((-E : ℝ) : ℂ) * ((ℏ : ℂ) / (ℏ : ℂ))
          * Complex.exp (Complex.I * (S t : ℂ) / (ℏ : ℂ)) by ring]
  rw [Complex.I_mul_I, div_self hℏc]
  push_cast
  ring


/-- **The free-particle Newtonian energy generates the phase** — for the free action `S(τ) = px₀ − H τ` with
`H = newtonianHamiltonian m p = p²/2m` (the classical Hamilton's-equations Hamiltonian of
`ComptonClock.NewtonianAndGRLimit`), `iℏ ∂tΨ = H Ψ`: the Newtonian energy is the generator of the classical
phase, an instance of `hamiltonJacobi_energy_generates_phase`. -/
lemma freeParticle_energy_generates_phase (m p x₀ ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    Complex.I * (ℏ : ℂ) *
        deriv (fun τ : ℝ =>
          Complex.exp (Complex.I * ((p * x₀ - newtonianHamiltonian m p * τ : ℝ) : ℂ) / (ℏ : ℂ))) t
      = (newtonianHamiltonian m p : ℂ) *
          Complex.exp (Complex.I * ((p * x₀ - newtonianHamiltonian m p * t : ℝ) : ℂ) / (ℏ : ℂ)) := by
  have hS : HasDerivAt (fun τ : ℝ => p * x₀ - newtonianHamiltonian m p * τ)
      (-(newtonianHamiltonian m p)) t := by
    exact ((hasDerivAt_const t (p * x₀)).sub ((hasDerivAt_id t).const_mul (newtonianHamiltonian m p))).congr_deriv (by ring)
  exact hamiltonJacobi_energy_generates_phase _ (newtonianHamiltonian m p) ℏ t hℏ hS


/-- **The internal time reads the elapsed classical time** `T U_t = t · U_t` at the Hamilton–Jacobi frequency
`ω = E/ℏ` — the classical action phase is the Liouville evolution factor `U_t = liouvilleEvolve t 1` evaluated at
the classical frequency `E/ℏ` (`= H/ℏ` by `∂tS = −H`), and the Misra internal time `T = i d/dλ` returns the
elapsed time `t` as its eigenvalue. The classical clock time *is* the Misra internal time. -/
lemma misraTime_reads_classical_time (E ℏ t : ℝ) :
    ageOperator (liouvilleEvolve t (fun _ => 1)) (E / ℏ)
      = (t : ℂ) * liouvilleEvolve t (fun _ => 1) (E / ℏ) :=
  ageOperator_reads_evolution_time t (E / ℏ)

/- ZIL-BEGIN -/

zil attach misraTime_reads_classical_time where
  formalizes @ "claim:misra-internal-time-reads-classical-time",
  requires @ "claim:hamilton-jacobi-energy-generates-the-phase",
  supported_by @ "paper:misra-prigogine-1978",
  caveat @ "claim:plane-wave-eigenfunction-reading-not-a-self-adjointness-theorem"

zil attach hamiltonJacobi_energy_generates_phase where
  formalizes @ "claim:hamilton-jacobi-energy-generates-the-phase",
  supported_by @ "paper:hamilton-jacobi-classical-mechanics"

/- ZIL-END -/

end Physlib.QuantumMechanics.Lindblad.MisraTimeClassicalHamiltonJacobi

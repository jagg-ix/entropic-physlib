/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellSteadyState
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity

/-!
# The Vlasov energy integral, the quantum mass shell, and the Jacobson-diamond time reversal

Connects the steady-state Vlasov–Maxwell first integrals (`Vlasov.MaxwellSteadyState`) to the **quantum**
quasiparticle / mass-shell energy (`Bogoliubov.Transformation.bogoliubovEnergy`) and to the **Jacobson
causal-diamond / Nagao–Nielsen** time-reversal structure of `PTSymmetricQFT.QuantumSpacetimeSymmetry` /
`CausalDiamond.Helicity`. The single unifying fact is antiunitary time reversal as a **velocity-reversing
isometry**: it flips the momentum/velocity while leaving the energy / mass shell invariant.

* **Classical (Vlasov).** The energy integral `R = −α|V|² + φ` is **even in `V`** — `T : V ↦ −V` leaves it
  invariant — while the momentum integral `G = V·d + ψ` has its velocity part flipped.
* **Quantum (Bogoliubov / diamond).** The quasiparticle mass-shell energy `bogoliubovEnergy(ξ,Δ) = √(ξ²+Δ²)`
  is **even in `ξ`**, with dispersion `E² = ξ² + Δ²`; for the diamond mode (`E = cosh θ`, `|p| = sinh θ`,
  `Δ = 1`) this is invariance under the rapidity reversal `θ ↦ −θ`, while the diamond velocity `tanh θ`
  flips. So the Greaves–Thomas antiunitary `conjFactor true` (`z ↦ z̄ ≙ θ ↦ −θ`) reverses momentum and
  preserves the mass shell.

The classical Vlasov particle and the quantum diamond/Bogoliubov quasiparticle obey the *same* time-reversal
law: **energy / mass shell `T`-even, momentum / velocity `T`-odd**.

* **§A — Vlasov time reversal** (`vlasovEnergy`, `vlasovEnergy_timeReversal`, `vlasovMomentum`,
  `vlasovMomentum_timeReversal`). The classical energy is `T`-even, the momentum velocity-part `T`-odd.
* **§B — the quantum mass shell** (`bogoliubovEnergy_sq`, `bogoliubovEnergy_timeReversal`,
  `diamond_energy_even`, `diamond_velocity_timeReversal`). `E² = ξ²+Δ²`; the energy is even in `ξ`; the
  diamond horizon energy is invariant under `θ ↦ −θ` (consuming `diamond_horizon_energy`) while the diamond
  velocity flips.
* **§C — the unifying law** (`timeReversal_classical_and_quantum`, `timeReversal_momentum_flips`). Classical
  and quantum energies are both `T`-even; their momenta are both `T`-odd — one antiunitary `T`.

## References

* Y. Markov et al., Acta Appl. Math. 28 (1992) (the Vlasov energy integral, even in `V`); N. N. Bogoljubov
  (the quasiparticle energy `√(ξ²+Δ²)`); the Jacobson diamond rapidity `θ ↦ −θ`.
* Repo dependencies: `Vlasov.MaxwellSteadyState`; `Bogoliubov.Transformation.bogoliubovEnergy`;
  `CausalDiamond.Helicity.diamond_horizon_energy`; the `θ ↦ −θ` diamond/NN time reversal of
  `PTSymmetricQFT.QuantumSpacetimeSymmetry`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity

/-! ## §A — the classical Vlasov energy/momentum under time reversal `V ↦ −V` -/

/-- **The Vlasov energy integral** `R = −α|V|² + φ`. -/
def vlasovEnergy (α φ : ℝ) (V : Fin 3 → ℝ) : ℝ := -α * (V ⬝ᵥ V) + φ

/-- **[`T`-even] The Vlasov energy is invariant under velocity reversal** `R(−V) = R(V)` — the classical
particle energy is `T`-even (the magnetic field does no work, the potential is `V`-independent). -/
theorem vlasovEnergy_timeReversal (α φ : ℝ) (V : Fin 3 → ℝ) :
    vlasovEnergy α φ (-V) = vlasovEnergy α φ V := by
  simp [vlasovEnergy, dotProduct_neg, neg_dotProduct]

/-- **The Vlasov momentum integral** `G = V·d + ψ`. -/
def vlasovMomentum (d : Fin 3 → ℝ) (ψ : ℝ) (V : Fin 3 → ℝ) : ℝ := V ⬝ᵥ d + ψ

/-- **[`T`-odd] The Vlasov momentum's velocity part flips** `G(−V) = −(V·d) + ψ` — `T`-odd, like the diamond
momentum. -/
theorem vlasovMomentum_timeReversal (d : Fin 3 → ℝ) (ψ : ℝ) (V : Fin 3 → ℝ) :
    vlasovMomentum d ψ (-V) = -(V ⬝ᵥ d) + ψ := by
  simp [vlasovMomentum, neg_dotProduct]

/-! ## §B — the quantum mass shell and the diamond -/

/-- **[Dispersion] The quasiparticle mass shell** `E² = ξ² + Δ²` — the quantum energy–momentum relation. -/
theorem bogoliubovEnergy_sq (ξ Δ : ℝ) : bogoliubovEnergy ξ Δ ^ 2 = ξ ^ 2 + Δ ^ 2 := by
  unfold bogoliubovEnergy; rw [Real.sq_sqrt (by positivity)]

/-- **[`T`-even] The quasiparticle energy is even in momentum** `E(−ξ) = E(ξ)` — the quantum mass shell is
invariant under momentum reversal, the same `T`-evenness as the Vlasov energy. -/
theorem bogoliubovEnergy_timeReversal (ξ Δ : ℝ) :
    bogoliubovEnergy (-ξ) Δ = bogoliubovEnergy ξ Δ := by
  unfold bogoliubovEnergy; rw [neg_pow, neg_one_sq, one_mul]

/-- **[Diamond `T`-even] The diamond horizon energy is invariant under rapidity reversal** `θ ↦ −θ` —
`bogoliubovEnergy(sinh(−θ),1) = cosh θ` (consuming `diamond_horizon_energy`), the diamond's mass shell. -/
theorem diamond_energy_even (θ : ℝ) :
    bogoliubovEnergy (Real.sinh (-θ)) 1 = bogoliubovEnergy (Real.sinh θ) 1 := by
  rw [diamond_horizon_energy, diamond_horizon_energy, Real.cosh_neg]

/-- **[Diamond `T`-odd] The diamond velocity flips** `tanh(−θ) = −tanh θ` — the horizon momentum reverses
while the energy stays fixed, the quantum analogue of the Vlasov velocity reversal. -/
theorem diamond_velocity_timeReversal (θ : ℝ) : Real.tanh (-θ) = -Real.tanh θ := Real.tanh_neg θ

/-! ## §C — the unifying time-reversal law -/

/-- **[Classical = quantum] Both energies are `T`-even.** The classical Vlasov energy `R = −α|V|² + φ` and
the quantum mass-shell energy `√(ξ²+Δ²)` are *both* invariant under the velocity/momentum-reversing
antiunitary `T` — one law, classical and quantum. -/
theorem timeReversal_classical_and_quantum (α φ : ℝ) (V : Fin 3 → ℝ) (ξ Δ : ℝ) :
    vlasovEnergy α φ (-V) = vlasovEnergy α φ V
      ∧ bogoliubovEnergy (-ξ) Δ = bogoliubovEnergy ξ Δ :=
  ⟨vlasovEnergy_timeReversal α φ V, bogoliubovEnergy_timeReversal ξ Δ⟩

/-- **[Momenta `T`-odd] Both momenta flip.** The Vlasov momentum's velocity part and the diamond velocity
both change sign under `T` — the momentum is `T`-odd in both the classical and the quantum sectors. -/
theorem timeReversal_momentum_flips (d : Fin 3 → ℝ) (ψ : ℝ) (V : Fin 3 → ℝ) (θ : ℝ) :
    vlasovMomentum d ψ (-V) = -(V ⬝ᵥ d) + ψ ∧ Real.tanh (-θ) = -Real.tanh θ :=
  ⟨vlasovMomentum_timeReversal d ψ V, diamond_velocity_timeReversal θ⟩

end Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal

end

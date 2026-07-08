/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellSteadyState
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-!
# The Vlasov energy integral and the electromagnetic field strength: one antisymmetry

Links the steady-state Vlasov–Maxwell first integrals (`Vlasov.MaxwellSteadyState`) to the electromagnetic
sector already in physlib (`PTSymmetricQFT.MaxwellFaraday`, and through it the EM superoperator arc). The
connecting fact is a single antisymmetry: **a Lorentz / rotation generator does no work**. The magnetic
field's "no work" `V·(V×B) = 0` — the reason the energy `R = −α|V|² + φ` is conserved
(`Vlasov.MaxwellSteadyState.energyRate_eq`) — and the electromagnetic field strength's "no work on the
4-velocity" `U·(F·U) = 0` are the *same* statement for an antisymmetric matrix, which is exactly the
antisymmetry of `faraday` (`faraday_antisymm`) that makes `F` a `𝔰𝔬(1,3)` element and the basis of the EM
adjoint superoperator `ad_F`.

* **§A — antisymmetric generators do no work** (`antisym_no_work`). For any antisymmetric matrix `M`,
  `V·(M V) = 0` — the quadratic form of a Lorentz/rotation generator vanishes.
* **§B — the EM field strength does no work on the 4-velocity** (`faraday_no_work`). `U·(F U) = 0` for
  `F = dA`, consuming `PTSymmetricQFT.MaxwellFaraday.faraday_antisymm` — the covariant statement that the
  Lorentz force is orthogonal to the 4-velocity (it preserves `U² = c²`), the relativistic form of the
  magnetic "no work".
* **§C — the magnetic field as a rotation generator** (`magGen`, `magGen_mulVec`, `magGen_antisymm`,
  `magnetic_no_work`). `V×B` is the action of the antisymmetric matrix `magGen B`, so `V·(V×B) = 0` is again
  the no-work principle — the magnetic drop in the Vlasov energy rate.

The one antisymmetry thus runs through the whole arc: the magnetic field doing no work on a Vlasov particle,
the EM field strength doing no work on the 4-velocity, the field strength being a Lorentz generator, and the
EM superoperator `ad_F` being traceless (`Electromagnetic.EMSuperoperatorSpacetime.emFieldAdjoint_trace_zero`). The
conserved Vlasov energy is, in turn, the Lyapunov constant of motion underlying steady-state stability
(cf. `Hopf.DualSphereSobolevPerfectSquare`).

## References

* Y. Markov et al., Acta Appl. Math. 28 (1992) (the Vlasov energy integral); the Lorentz force orthogonality
  `F_{μν} U^μ U^ν = 0`.
* Repo dependencies: `Vlasov.MaxwellSteadyState` (`energyRate_eq`); `PTSymmetricQFT.MaxwellFaraday`
  (`faraday`, `faraday_antisymm`); cf. `Electromagnetic.EMSuperoperatorSpacetime.emFieldAdjoint_trace_zero`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM

open Matrix
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-! ## §A — antisymmetric generators do no work -/

/-- **[No work] An antisymmetric matrix `M` does no work on `V`** `V·(M V) = 0` — the quadratic form of a
Lorentz/rotation generator vanishes (a symmetric `Vᵢ Vⱼ` contracted with the antisymmetric `Mᵢⱼ`). -/
theorem antisym_no_work {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j = -M j i) (V : Fin n → ℝ) : V ⬝ᵥ (M *ᵥ V) = 0 := by
  have e : V ⬝ᵥ (M *ᵥ V) = ∑ i, ∑ j, V i * M i j * V j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  have hsw : (∑ i, ∑ j, V i * M i j * V j) = ∑ i, ∑ j, V j * M j i * V i := Finset.sum_comm
  have hz : (∑ i, ∑ j, V i * M i j * V j) + (∑ i, ∑ j, V j * M j i * V i) = 0 := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]; refine Finset.sum_eq_zero fun j _ => ?_
    rw [hM i j]; ring
  rw [← hsw] at hz; linarith

/-! ## §B — the EM field strength does no work on the 4-velocity -/

/-- **[Link to the EM sector] The field strength `F = dA` does no work on the 4-velocity** `U·(F U) = 0`.
This is `antisym_no_work` applied to `faraday`, consuming `faraday_antisymm` — the covariant statement that
the Lorentz force `F^μ_ν U^ν` is orthogonal to `U`, so it preserves `U² = c²` (the relativistic form of the
magnetic field doing no work). -/
theorem faraday_no_work (k A U : Fin 4 → ℝ) : U ⬝ᵥ ((faraday k A) *ᵥ U) = 0 :=
  antisym_no_work (faraday k A) (faraday_antisymm k A) U

/-! ## §C — the magnetic field as a rotation generator -/

/-- **The magnetic field as a rotation generator** — the antisymmetric matrix `magGen B` with
`magGen B · V = V × B`. -/
def magGen (B : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, B 2, -B 1; -B 2, 0, B 0; B 1, -B 0, 0]

/-- **`magGen B · V = V × B`** — the cross product is the action of `magGen B`. -/
theorem magGen_mulVec (B V : Fin 3 → ℝ) : magGen B *ᵥ V = V ⨯₃ B := by
  funext i; fin_cases i <;>
    simp [magGen, mulVec, dotProduct, Fin.sum_univ_three, crossProduct, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- **`magGen B` is antisymmetric** — the magnetic field is an `𝔰𝔬(3)` rotation generator. -/
theorem magGen_antisymm (B : Fin 3 → ℝ) (i j : Fin 3) : magGen B i j = -magGen B j i := by
  fin_cases i <;> fin_cases j <;> simp [magGen]

/-- **[The magnetic drop] The magnetic field does no work** `V·(V×B) = 0` — recovered as the no-work
principle for the rotation generator `magGen B`. This is exactly the term that drops in
`Vlasov.MaxwellSteadyState.energyRate_eq`, leaving the energy conserved. -/
theorem magnetic_no_work (B V : Fin 3 → ℝ) : V ⬝ᵥ (V ⨯₃ B) = 0 := by
  rw [← magGen_mulVec]; exact antisym_no_work (magGen B) (magGen_antisymm B) V

end Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM

end

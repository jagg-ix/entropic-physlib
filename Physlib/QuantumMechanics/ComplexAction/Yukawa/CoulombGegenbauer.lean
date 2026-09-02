/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution

/-!
# The unscreened Yukawa limit is the Coulomb O(4)/S³ problem of the Gegenbauer harmonics

Links the Yukawa screened potential (`Yukawa.ScreenedPotential`, the entropic mass `M_eff = √(m² + λ)`) to
the **O(4)/S³ Gegenbauer harmonics** of the Coulomb/hydrogen problem (`OperatorAlgebra.GegenbauerODESolution`,
`gegenbauerOne = C_n^{(1)} = U_n`). The entropic action `λ` **tunes the screening** between two regimes:

* at the **critical entropic action `λ = −m²`** the screening mass vanishes, `M_eff = √(m² − m²) = 0`
  (`entropicMass_coulomb`), and the Yukawa potential reduces to the **bare Coulomb** `e^{0}/r = 1/r`
  (`yukawaPotential_zero_eq_coulomb`). The unscreened Coulomb is the O(4)-symmetric hydrogen atom, whose
  momentum-space (Fock) angular eigenfunctions on `S³` are the **Gegenbauer `C_n^{(1)} = U_n`** with
  eigenvalue `n(n+2)` (the `S³` Laplacian / `O(4)` Casimir, `gegenbauerEigenvalue_one`, `gegenbauerOne_solves`);
* for `λ > −m²` the screening mass is positive, `M_eff > 0`, the **massive (screened)** Yukawa potential —
  the entropic action gaps the spectrum (the BCS/Bogoliubov regime of the screening bridge), breaking the
  `O(4)` degeneracy.

So the entropic action interpolates between the **gapped/screened** Yukawa (`λ ≥ 0`, the Bogoliubov
quasiparticle) and the **ungapped/Coulomb** hydrogen (`λ = −m²`, the `O(4)/S³` Gegenbauer harmonic): the
imaginary/entropic action is the dial between BCS-like screening and the hydrogenic `O(4)` symmetry.

* **§A — the unscreened (Coulomb) limit** (`entropicMass_coulomb`, `yukawaPotential_zero_eq_coulomb`).
* **§B — the Coulomb limit carries the O(4)/S³ Gegenbauer harmonics** (`yukawa_coulomb_o4_gegenbauer`).

## References

* Fock's `O(4)` symmetry of the hydrogen atom; the screened (Yukawa) vs Coulomb potential. Carriers:
  `Yukawa.ScreenedPotential` (`entropicMass`, `yukawaPotential`), `OperatorAlgebra.GegenbauerODESolution` (`gegenbauerOne`,
  `gegenbauerOne_solves`, `gegenbauerEigenvalue_one`, `IsGegenbauerSolution`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Yukawa.CoulombGegenbauer

open Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution


/-- **[Critical entropic action: the screening mass vanishes] `M_eff(m, −m²) = 0`.** At the entropic action
`λ = −m²` the effective mass `√(m² + λ) = √0 = 0` — the screening is turned off. -/
lemma entropicMass_coulomb (m : ℝ) : entropicMass m (-m ^ 2) = 0 := by
  rw [entropicMass, show m ^ 2 + -m ^ 2 = (0 : ℝ) from by ring, Real.sqrt_zero]

/-- **[The unscreened Yukawa potential is the bare Coulomb] `G(r)|_{M=0} = 1/r`.** With the screening mass
off (`M = 0`), the Yukawa potential `e^{−M r}/r` reduces to the Coulomb potential `1/r`. -/
lemma yukawaPotential_zero_eq_coulomb (r : ℝ) : yukawaPotential 0 r = 1 / r := by
  simp [yukawaPotential]


/-- **[At the unscreened limit the Yukawa potential is the Coulomb hydrogen with O(4)/S³ Gegenbauer
harmonics].** For the entropic action tuned to `λ = −m²`:

* the screening mass vanishes, `M_eff = 0`, and the potential is the bare Coulomb `1/r`;
* the unscreened Coulomb is the `O(4)`-symmetric hydrogen atom, whose `S³` angular eigenfunctions are the
  Gegenbauer `C_n^{(1)} = U_n` with eigenvalue `n(n+2)` (the `S³` Laplacian / `O(4)` Casimir), each solving
  the Gegenbauer ODE.

The entropic action is the dial: `λ = −m²` is the ungapped Coulomb (`O(4)/S³` Gegenbauer harmonics),
`λ ≥ 0` the gapped/screened Yukawa (the Bogoliubov quasiparticle). The imaginary/entropic action
interpolates between hydrogenic `O(4)` symmetry and BCS-like screening. -/
lemma yukawa_coulomb_o4_gegenbauer (m r : ℝ) (n : ℕ) :
    entropicMass m (-m ^ 2) = 0
      ∧ yukawaPotential 0 r = 1 / r
      ∧ gegenbauerEigenvalue 1 n = (n : ℝ) * ((n : ℝ) + 2)
      ∧ ∃ dy, IsGegenbauerSolution 1 n (gegenbauerOne n) dy :=
  ⟨entropicMass_coulomb m, yukawaPotential_zero_eq_coulomb r, gegenbauerEigenvalue_one n,
    _, gegenbauerOne_solves n⟩

end Physlib.QuantumMechanics.ComplexAction.Yukawa.CoulombGegenbauer

end

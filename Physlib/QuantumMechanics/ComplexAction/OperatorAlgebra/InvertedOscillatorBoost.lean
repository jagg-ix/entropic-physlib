/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.ZetaInvertedOscillator
public import Physlib.Relativity.Special.HyperbolicBoost

/-!
# Bhaduri's monodromy is a rapidity Lorentz boost

Links `OperatorAlgebra.ZetaInvertedOscillator` to physlib's special-relativity layer (`HyperbolicBoost`). Bhaduri's
reduced monodromy matrix of the unstable orbit (Eq 19) is, in the isotropic case `ω₂ = 1`, **exactly the
rapidity-form Lorentz boost** of `Physlib.Relativity.Special`:

  `(M̃₁(α)) · (x, t) = (boostX (−α) x t, boostT (−α) x t)`   (`monodromy_one_mulVec_eq_boost`),

i.e. the Gutzwiller monodromy is a hyperbolic rotation by rapidity `α = 2πω₂/ω₁`. So:

* the **symplectic** condition `det M̃₁ = 1` is the **unit-hyperbola** identity `cosh²α − sinh²α = 1`
  (`monodromy_one_unitHyperbola`, joining `monodromy_det` to `unitHyperbola_cosh_sinh`);
* the monodromy **eigenvalues `e^{±α}`** (`monodromy_eigenvalues`) are the boost's null-coordinate Doppler
  factors — equivalently the orbit's **Lyapunov multipliers**. The single number `α` is at once the
  Gutzwiller instability exponent, the Lorentz rapidity, and (via `γ_tanh_eq_cosh`) the boost factor
  `γ = cosh α`.

This unifies the chaotic-orbit stability of the Riemann-zeta caricature with `(1+1)`-D special relativity:
the inverted-oscillator instability *is* a relativistic boost. (The complex resonance energies of
`selberg_factor_eq_zero_iff`, `E = (n+½)ℏω₁ − i(l+½)ℏω₂`, include the same hyperbolic/Bogoliubov rapidity into
the repo's complex-action layer.)

* **§A — the monodromy-as-boost identity** (`monodromy_one_mulVec_eq_boost`, `monodromy_one_unitHyperbola`).

## References

* Bhaduri et al. (1997), Eq 19; the rapidity-form Lorentz boost. structures: `OperatorAlgebra.ZetaInvertedOscillator`
  (`monodromy`, `monodromy_det`, `monodromy_eigenvalues`), `Physlib.Relativity.Special` (`boostX`, `boostT`,
  `UnitHyperbola`, `unitHyperbola_cosh_sinh`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.InvertedOscillatorBoost

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.ZetaInvertedOscillator
open Physlib.Relativity.Special

/-! ## §A — the monodromy-as-boost identity -/

/-- **[Bhaduri's monodromy is the rapidity boost] `M̃₁(α)·(x,t) = (boostX(−α), boostT(−α))`.** In the
isotropic case `ω₂ = 1`, the reduced monodromy matrix of the unstable orbit acts on `(x, t)` exactly as the
`(1+1)`-D rapidity-form Lorentz boost by rapidity `α`. -/
theorem monodromy_one_mulVec_eq_boost (α x t : ℝ) :
    (monodromy 1 α).mulVec ![x, t] = ![boostX (-α) x t, boostT (-α) x t] := by
  funext i
  fin_cases i <;>
    simp [monodromy, boostX, boostT, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cosh_neg,
      Real.sinh_neg] <;> ring

/-- **[Symplectic = unit hyperbola] `det M̃₁ = 1` is `cosh²α − sinh²α = 1`.** The area-preserving condition on
the monodromy is exactly the statement that `(cosh α, sinh α)` lies on the unit hyperbola — the rapidity
parameterisation of the Lorentz boost. -/
theorem monodromy_one_unitHyperbola (α : ℝ) :
    Matrix.det (monodromy 1 α) = 1 ∧ UnitHyperbola (Real.cosh α) (Real.sinh α) :=
  ⟨monodromy_det 1 α one_ne_zero, unitHyperbola_cosh_sinh α⟩

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.InvertedOscillatorBoost

end

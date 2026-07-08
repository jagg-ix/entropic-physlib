/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.Herglotz.Instances
public import Physlib.QuantumMechanics.Lindblad.GreensFunction
public import Physlib.StatisticalMechanics.HerglotzEntropyTime

/-!
# Lindblad ⇒ Herglotz unification

The two independent derivation routes for the entropic-time arrow —

* **Lindblad operator route**: `L†L ⪰ 0` (positivity of a jump-operator
  dissipator) ⇒ entropy-production rate `(2/ℏ)·‖Lψ‖² ≥ 0`
  (`Physlib.QuantumMechanics.Lindblad.GreensFunction`, `NoetherDissipation.LindbladNoether`);

* **Herglotz variational route**: `α = ∂L/∂z ≤ 0` (contact-derivative dissipation
  sign) ⇒ the Noether–Herglotz integrating factor accumulates a monotone `S_I`

— are unified here. A Lindblad jump operator `L` instantiates a **constant-rate**
Herglotz–Noether balance with `α := −(2/ℏ)·‖Lψ‖²`, and the Herglotz dissipation
sign `α ≤ 0` is then a *theorem* from `L†L ⪰ 0` (no extra hypothesis), giving the
explicit Herglotz entropic time `τ_ent = (2/ℏ)·‖Lψ‖²·t` along the worldline.

This is exactly the same rate the Lindblad route delivers via
`lindblad_greenKernel_rate_eq_entropyRate`, so the two routes feed the same
entropic clock.


## References

- **Lindblad 1976** — *On the generators of quantum dynamical semigroups*
- **Gorini, Kossakowski, Sudarshan 1976** — *Completely positive dynamical semigroups of N-level systems*
- **Breuer & Petruccione 2002** — *The Theory of Open Quantum Systems (textbook)*
- **Gough, Ratiu, Smolyanov 2015** — *Noether's theorem for dissipative quantum semigroups*
- **Herglotz 1930** — *Berührungstransformationen (lectures)*
- **Lazo et al. 2018** — *Action principle for action-dependent Lagrangians*
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section


open Physlib.ClassicalMechanics.Herglotz.Instances Physlib.QuantumMechanics.Lindblad.GreensFunction
open Physlib.ClassicalMechanics.Herglotz.Balance
namespace Physlib.QuantumMechanics.Lindblad.HerglotzUnification


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- **Lindblad → Herglotz bridge.** The Lindblad jump operator `L` produces a
constant-rate Herglotz–Noether balance with `α := −(2/ℏ)·‖L ψ‖²`. -/
def ofLindbladRate (L : H →L[ℂ] H) (hbar : ℝ) (ψ : H) (J0 : ℝ) :
    HerglotzNoetherBalance :=
  ofConstantRate (- (2 / hbar) * ‖L ψ‖ ^ 2) J0

/-- **`L†L ⪰ 0` ⇒ Herglotz `α ≤ 0`** — structurally, with no extra hypothesis.
The Herglotz dissipation sign of `ofLindbladRate` is a theorem from the
operator positivity of the Lindblad dissipator. -/
theorem ofLindbladRate_alpha_nonpos
    (L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) (J0 : ℝ) :
    ∀ t, (ofLindbladRate L hbar ψ J0).alpha t ≤ 0 := by
  intro _
  unfold ofLindbladRate ofConstantRate
  have h2h : 0 ≤ 2 / hbar := by positivity
  have hsq : 0 ≤ ‖L ψ‖ ^ 2 := sq_nonneg _
  have : 0 ≤ (2 / hbar) * ‖L ψ‖ ^ 2 := mul_nonneg h2h hsq
  linarith

/-- **The Herglotz entropic time for a Lindblad jump is the Lindblad rate.**
`τ_ent(t) = (2/ℏ)·‖L ψ‖²·t` along the worldline — exactly the rate the operator
route delivers via `lindblad_greenKernel_rate_eq_entropyRate`. The two derivation
routes feed the same entropic clock. -/
theorem ofLindbladRate_tauEnt
    (L : H →L[ℂ] H) (hbar : ℝ) (ψ : H) (J0 t : ℝ) :
    (ofLindbladRate L hbar ψ J0).tauEnt t = (2 / hbar) * ‖L ψ‖ ^ 2 * t := by
  unfold ofLindbladRate ofConstantRate HerglotzNoetherBalance.tauEnt
  ring

end Physlib.QuantumMechanics.Lindblad.HerglotzUnification

end

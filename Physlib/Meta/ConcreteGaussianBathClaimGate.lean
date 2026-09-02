/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.ConcreteGaussianBathWitness
public import Physlib.Meta.HypothesisInhabitationCheck

/-!
# Non-gameable antecedent gate for the weak-coupling one-level claim

A maturity metric is gameable when a conditional theorem `hypothesis → conclusion` is counted as a solved
result even though the hypothesis is never exhibited: the theorem is then kernel-clean but vacuously
conditional, and its carrier type may have no instance at all. This module gates the two flagged claims by
their own honest evidence, using the repository's non-gameable meta-checks rather than a hand-maintained
status count.

* **Weak-coupling reduction — discharged.** The reduction is stated for every `GaussianContinuumBath`, and the
  concrete `resonantUnitBath` inhabits that carrier, so `gaussianBath_nonempty` proves
  `Nonempty GaussianContinuumBath`. The bundled `resonantUnitBath_weakCoupling_closes` then **passes** the
  `#physlib_hypotheses_inhabited` antecedent gate (its non-equilibrium occupation antecedent is witnessed), and
  is additionally certified axiom-clean and non-vacuous. The claim is model-validated — with the exact
  golden-rule rate `2π` — while its calibration and physical-identity axes remain `absent`.

* **Particle stability — not discharged.** `CubicQuinticMildFlow.exists_minimizingOrbit_uniformlyStable` and
  `CubicQuinticConstructedCertificates.exists_identifiedStableMinimizingBranch` are gated on a
  `GlobalConservativeBornMildFlowCertificate`, whose carrier requires an `HOneWeakMildFlowCertificate` — the
  energy-critical global mild flow — for which **no instance is constructed**. There is therefore no analogue
  of `gaussianBath_nonempty`: `Nonempty GlobalConservativeBornMildFlowCertificate` is not provable here. That
  is the honest boundary between a discharged model result and a certificate-conditional one — kernel-clean,
  but its carrier is unwitnessed, so it must not be counted as a validated physical result.
-/

set_option autoImplicit false

namespace Physlib.Meta.ConcreteGaussianBathClaimGate

open QuantumMechanics.LindbladDrivenLeads

/-- The weak-coupling reduction carrier is genuinely inhabited: the concrete `resonantUnitBath` witnesses
`Nonempty GaussianContinuumBath`. No analogous `Nonempty GlobalConservativeBornMildFlowCertificate` is
provable — the particle-stability carrier has no constructed instance. -/
theorem gaussianBath_nonempty : Nonempty GaussianContinuumBath :=
  ⟨resonantUnitBath⟩

/-- Hypothesis-closure witness for the bundled concrete weak-coupling claim: a strictly-interior,
non-equilibrium occupation pair exists. -/
theorem resonantUnitBath_weakCoupling_closes_hypotheses :
    ∃ N f : ℝ, 0 < N ∧ N < 1 ∧ 0 < f ∧ f < 1 ∧ N ≠ f :=
  ⟨1 / 3, 2 / 3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Physlib.Meta.ConcreteGaussianBathClaimGate

open QuantumMechanics.LindbladDrivenLeads
open Physlib.Meta.ConcreteGaussianBathClaimGate

-- The bundled concrete weak-coupling claim's non-equilibrium antecedent is genuinely inhabited.
#physlib_hypotheses_inhabited resonantUnitBath_weakCoupling_closes
  using resonantUnitBath_weakCoupling_closes_hypotheses

-- The discharged claim is kernel-certified: axiom-clean.
#physlib_axiom_clean_all [
  gaussianBath_nonempty,
  resonantUnitBath_weakCoupling_closes,
  resonantUnitBath_rate,
  resonantUnitBath_transform ]

-- The discharged claim is non-vacuous: its conclusion is substantive.
#physlib_non_vacuous_all [
  resonantUnitBath_weakCoupling_closes,
  resonantUnitBath_rate ]

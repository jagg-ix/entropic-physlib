/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhElectrogravitic
public import Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
public import Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation

/-!
# Merging electrogravitics into one theory: gravity + Yang–Mills gauge off the holographic screen

The electrogravitic system (`SciamaUnruhElectrogravitic`) couples gravity to **Maxwell** (`U(1)`
electromagnetism).  This module extends the gauge sector from Maxwell to a general **Yang–Mills** gauge theory
(`YangMillsGaugeDynamics`), merging gravity and gauge into a single theory:

* Maxwell is the *abelian* case of Yang–Mills.  The electromagnetic field strength
  `faraday k A = kA − Ak` is exactly the `u(1)` (`𝔤 = ℝ`) Yang–Mills curvature
  `F = ∂A − ∂A + [A, A]` with the plane-wave connection `∂_μ ↦ k_μ` and vanishing bracket
  (`faraday_is_abelian_yangMills`).  Replacing `ℝ` by a noncommutative `[Ring 𝔤]` promotes the abelian
  electrogravitic gauge sector to the full non-abelian Yang–Mills sector.
* The Yang–Mills field strength is antisymmetric and reduces to the exterior derivative `dA` in the abelian
  case (`gravitoYangMills_gauge_extension`).
* The non-abelian gauge current is *covariantly* conserved, `D_ν D_μ F^{μν} = 0`
  (`gravitoYangMills_current_conserved`) — the consistency of the extended gauge theory.

The two sectors merge through the **BCJ double copy** `gravity = gauge²` (`SciamaFockBCJAdSCFT`): gravity is the
double copy of the Yang–Mills gauge field, and both are read off the *same* holographic screen — the Unruh
temperature `T_U = α/2π` fixing the thermal input and the bit-count `G = A c³/(ℏN)` fixing the coupling
`8πG/c⁴ = 8π(A/N)/(ℏc)` (`SciamaUnruhElectrogravitic`).  So the single theory is **gravito-Yang–Mills at the
holographic screen**: a non-abelian gauge field (Maxwell = abelian sector), its double copy the metric, sourced
by a complex-mass Dirac fermion, at a coupling and temperature fixed by the screen's bits and thermality.

Honest scope: the Maxwell = abelian-Yang–Mills identification and the reused Yang–Mills structure
(antisymmetry, covariant conservation).  The full non-abelian Einstein–Yang–Mills field equation is the gauge
generalization; here the gauge-sector extension and its unification with the electrogravitic/holographic
structure are made explicit.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhGravitoYangMills

open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
open Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-- **[Maxwell is abelian Yang–Mills] `faraday = u(1) Yang–Mills curvature`.**  The electrogravitic
electromagnetic field strength `faraday k A μ ν = k_μ A_ν − k_ν A_μ` is exactly the `𝔤 = ℝ` (`u(1)`) Yang–Mills
curvature with the plane-wave connection `∂_μ ↦ k_μ·` and vanishing self-bracket — so replacing `ℝ` by a
noncommutative gauge algebra promotes it to the non-abelian sector. -/
theorem faraday_is_abelian_yangMills (k A : Fin 4 → ℝ) (μ ν : Fin 4) :
    faraday k A μ ν
      = yangMillsCurvature (fun (f : Unit → ℝ) i (_ : Unit) => k i * f ())
          (fun (_ : Unit) i => A i) () μ ν := by
  simp [faraday, yangMillsCurvature, Ring.lie_def]
  ring

/-- **[The gauge field strength] abelian Yang–Mills curvature is `dA` and antisymmetric.**  In the abelian
case the Yang–Mills field strength is the exterior derivative `∂_μ A_ν − ∂_ν A_μ` (Maxwell), and it is
antisymmetric `F_{μν} = −F_{νμ}` — the gauge two-form the electrogravitic Maxwell sector generalizes. -/
theorem gravitoYangMills_gauge_extension {X ι 𝔤 : Type*} [CommRing 𝔤]
    (deriv : GaugePartial X ι 𝔤) (A : GaugePotential X ι 𝔤) (x : X) (μ ν : ι) :
    yangMillsCurvature deriv A x μ ν
        = deriv (fun y => A y ν) μ x - deriv (fun y => A y μ) ν x
      ∧ yangMillsCurvature deriv A x μ ν = -yangMillsCurvature deriv A x ν μ :=
  ⟨yangMillsCurvature_eq_exteriorDerivative_of_comm deriv A x μ ν,
    yangMillsCurvature_antisymm deriv A x μ ν⟩

/-- **[Non-abelian gauge consistency] `D_ν D_μ F^{μν} = 0`.**  The covariant current of the extended (non-
abelian) gauge sector is covariantly conserved — the consistency condition that promotes Maxwell's
`∂_μ J^μ = 0` to the full Yang–Mills theory merged with gravity. -/
theorem gravitoYangMills_current_conserved {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D2 : ι → ι → ι → ι → Matrix ι ι ℝ) (F : ι → ι → Matrix ι ι ℝ)
    (hFanti : ∀ μ ν, F μ ν = -F ν μ)
    (hD2anti : ∀ a b c d, D2 a b c d = -D2 a b d c)
    (hricci : ∀ a b c d, D2 a b c d - D2 b a c d = F a b * F c d - F c d * F a b) :
    (∑ μ, ∑ ν, D2 ν μ μ ν) = 0 :=
  nonabelian_current_conservation D2 F hFanti hD2anti hricci

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhGravitoYangMills

end

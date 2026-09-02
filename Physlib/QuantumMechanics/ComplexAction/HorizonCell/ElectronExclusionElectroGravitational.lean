/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionComplexEinstein
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.SuperoperatorComplexEinsteinBCJSector
public import Physlib.QuantumMechanics.ComplexAction.Fermion.PhotonExchange

/-!
# The electron's gravity is its photon exchange squared: the BCJ double copy of the exclusion cell

Completes the electron-exclusion-cell arc (`ElectronExclusionMutex` → `…PhotonBifurcation` →
`…ComplexEinstein`). The electron's **entropic gravitational mass** `Im E = m_I c²` (which sources the
imaginary Einstein curvature `Λ`, `ElectronExclusionComplexEinstein.exclusionCell_entropic_is_imaginaryEinstein`)
is the **BCJ double copy** of its **photon exchange** (its gauge sector):

  `exp(−Im E) = exp(−S₁)·exp(−S₂)`  (`SuperoperatorComplexEinsteinBCJSector.entropic_einstein_doublecopy_factorizes`),

and the electron's single-photon-exchange amplitude has exactly this modulus,

  `‖amplitude‖ = e^{−tH_{I,1}/ℏ}·e^{−tH_{I,2}/ℏ}`  (`Fermion.PhotonExchange.exchange_modulus`),

the product of the two fermion-line Cameron–Martin weights (the photon line itself is reversible). Identifying
the two gauge factors with the split `S₁ = tH_{I,1}/ℏ`, `S₂ = tH_{I,2}/ℏ` gives

  **`exp(−Im E) = ‖photonExchangeAmplitude‖`**  (`electron_entropicGravity_eq_photonExchange`):

the electron's **entropic gravity weight *is* its photon-exchange amplitude** — gravity `=` gauge², the
Bern–Carrasco–Johansson double copy realized on the exclusion cell, with the two fermion lines exchanging the
photon as the two gauge factors that square into the entropic gravitational mass.

**At the massless bifurcation the double copy is reversible.** With `m_I = 0` (the photon / lightlike critical
point) the entropic gravity weight is `exp(−Im E) = 1` (`electron_reversible_gravityWeight_unitary`), which is
exactly when the photon exchange is unitary — both fermion lines lossless, `H_{I,1} = H_{I,2} = 0`
(`exchange_unitary_iff`). The reversible real-GR limit of `ElectronExclusionComplexEinstein` is the unitary
(dissipationless) limit of the gauge sector.

* **§A — the double copy** (`electron_entropicGravity_eq_photonExchange`).
* **§B — the reversible / unitary limit** (`electron_reversible_gravityWeight_unitary`).
* **§C — assembled** (`electron_gravity_gauge_double_copy`).

**Honest layering.** Exact reuse of `entropic_einstein_doublecopy_factorizes`, `exchange_modulus`,
`exchange_unitary_iff`, `reversible_no_entropic`. The new content is the *identification* of the electron's
photon-exchange amplitude with its entropic-gravity double-copy weight — the concrete `gravity = gauge²`
statement for the exclusion cell. The identification requires the split hypothesis `m_I c² = S₁ + S₂` with the
`Sᵢ` the fermion-line entropic actions; it is not derived that a given electron's mass equals a particular
photon exchange, only that the two carry the same double-copy weight.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson (colour–kinematics / double copy). Repo carriers:
  `ComplexEinstein.SuperoperatorComplexEinsteinBCJSector`, `Fermion.PhotonExchange`,
  `HorizonCell.ElectronExclusionComplexEinstein`, `ComplexEinstein.ComplexMassEinsteinEquations`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.SuperoperatorComplexEinsteinBCJSector
open Physlib.QuantumMechanics.ComplexAction.Fermion.PhotonExchange

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionElectroGravitational


/-- **[The electron's entropic gravity weight is its photon-exchange amplitude] `exp(−Im E) = ‖amplitude‖`.**
Writing the BCJ split of the entropic gravitational mass `m_I c² = S₁ + S₂` with the two gauge factors the
fermion-line entropic actions `S₁ = tH_{I,1}/ℏ`, `S₂ = tH_{I,2}/ℏ`, the electron's entropic gravity weight
`exp(−Im E)` (the imaginary-Einstein `Λ` damping) equals the modulus of its single-photon-exchange amplitude
`‖e^{−tH_{I,1}/ℏ}·(photon)·e^{−tH_{I,2}/ℏ}‖`: **gravity = gauge²**, the double copy on the exclusion cell. -/
lemma electron_entropicGravity_eq_photonExchange
    (m_R m_I c pf1 pf2 pγ mF HI1 HI2 t ħ : ℝ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2)
    (hsplit : m_I * c ^ 2 = t * HI1 / ħ + t * HI2 / ħ) :
    Real.exp (-(complexEinsteinEnergy m_R m_I c).im)
      = ‖photonExchangeAmplitude pf1 pf2 pγ mF HI1 HI2 t ħ h1 h2‖ := by
  rw [exchange_modulus]
  exact entropic_einstein_doublecopy_factorizes m_R m_I c (t * HI1 / ħ) (t * HI2 / ħ) hsplit


/-- **[At the massless bifurcation the entropic gravity weight is `1`] `exp(−Im E) = 1` at `m_I = 0`.** At the
photon / lightlike critical point the imaginary Einstein energy vanishes (`reversible_no_entropic`), so the
entropic gravity weight is trivial — the reversible real-GR limit, matching the unitary (lossless) limit of the
photon-exchange gauge sector. -/
lemma electron_reversible_gravityWeight_unitary (m_R c : ℝ) :
    Real.exp (-(complexEinsteinEnergy m_R 0 c).im) = 1 := by
  rw [reversible_no_entropic]; simp


/-- **[The electron gravity = gauge² double copy, assembled].** For an electron cell:

* its entropic gravity weight equals its photon-exchange amplitude modulus (`gravity = gauge²`);
* at the massless bifurcation (`m_I = 0`) the gravity weight is `1` (reversible);
* the photon exchange is unitary exactly when both fermion lines are lossless (`H_{I,1} = H_{I,2} = 0`).

So the electron's entropic gravitational mass is the double copy of its photon exchange, and the massless
critical point is where both the gravity and gauge sectors become reversible. -/
lemma electron_gravity_gauge_double_copy
    (m_R m_I c pf1 pf2 pγ mF HI1 HI2 t ħ : ℝ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2)
    (ht : 0 < t) (hħ : 0 < ħ) (hsplit : m_I * c ^ 2 = t * HI1 / ħ + t * HI2 / ħ) :
    Real.exp (-(complexEinsteinEnergy m_R m_I c).im)
        = ‖photonExchangeAmplitude pf1 pf2 pγ mF HI1 HI2 t ħ h1 h2‖
      ∧ Real.exp (-(complexEinsteinEnergy m_R 0 c).im) = 1
      ∧ (‖photonExchangeAmplitude pf1 pf2 pγ mF HI1 HI2 t ħ h1 h2‖ = 1 ↔ HI1 = 0 ∧ HI2 = 0) :=
  ⟨electron_entropicGravity_eq_photonExchange m_R m_I c pf1 pf2 pγ mF HI1 HI2 t ħ h1 h2 hsplit,
    electron_reversible_gravityWeight_unitary m_R c,
    exchange_unitary_iff pf1 pf2 pγ mF HI1 HI2 t ħ h1 h2 ht hħ⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionElectroGravitational

end

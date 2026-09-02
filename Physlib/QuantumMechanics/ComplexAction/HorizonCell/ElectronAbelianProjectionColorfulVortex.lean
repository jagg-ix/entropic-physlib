/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronDeconfinementCenterVortex
public import Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
public import Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant

/-!
# Fig. 1 of Dehghan–Faber: the Abelian projection is the Bloch qubit, the colorful vortex is a Hopf/trefoil loop

Continues the confinement-mechanism link of `ElectronDeconfinementCenterVortex` with the two pictures of Fig. 1
of Dehghan–Faber (arXiv:2412.10767), both of which are structures the electron-cell arc already carries.

**(b) The Abelian projection is the Bloch qubit.** The Maximal Abelian Gauge projects the non-Abelian field onto
a `U(1)` **Cartan** direction — the Pauli `σ₃` axis — and reads off monopole world lines. That Cartan axis is the
Bloch `z`-axis `blochZAxis = (0,0,1)` (`LorenzQubitBlochDynamics`), a point of the Bloch sphere
(`abelianProjection_cartan_poles`); its two `σ₃` eigenstates — the `±z` poles — are the `ℤ/2` center elements
`±1` the center projection `Z_μ = signTr[U]` picks up. So the paper's Abelian projection *is* measuring the
exclusion-cell qubit in the computational (`σ₃`) basis, and the center `±1` are its two poles.

**(a) The colorful vortex is a Hopf/trefoil loop.** A center vortex is a closed colorful line — an `S¹`; in the
arc it is a **Hopf fiber**, invariant under the fiber rotation (`colorfulVortex_is_hopf_fiber`,
`QuaternionIsoclinicHopfFibration.hopf_fiber`). The Wilson loop around it picks up the **ribbon-twist center
element** `θ_a = ribbonTwist(a²/2k)` (`vortex_wilson_center`), and its **trefoil chirality distinguishes the
electron from the positron** (`vortex_trefoil_distinguishes_electron_positron`,
`TrefoilFermionChernSimonsInvariant.trefoil_chiral_distinguishes`) — the same `5̄`/`5` chirality of the
charge-chirality arc.

So Fig. 1 is the arc's own furniture: (b) the Abelian/Cartan projection is the qubit's `σ₃` axis with the center
`±1` at its poles, and (a) the colorful center vortex is a Hopf fiber whose Wilson loop carries the ribbon-twist
center element and whose trefoil chirality is the electron/positron label.

* **§A — Abelian projection = Bloch Cartan `σ₃` axis** (`abelianProjection_cartan_poles`).
* **§B — colorful vortex = Hopf fiber** (`colorfulVortex_is_hopf_fiber`).
* **§C — Wilson loop = ribbon-twist center; trefoil chirality = e⁻/e⁺** (`vortex_wilson_center`,
  `vortex_trefoil_distinguishes_electron_positron`).
* **§D — assembled** (`fig1_abelianProjection_colorfulVortex`).

**Honest layering.** Every statement is exact reuse: `BlochSphere`/`blochZAxis`, `hopf_fiber`,
`wilsonTopologicalSpin`, `trefoil_chiral_distinguishes`. The content is the *identification* of Fig. 1's two
pictures with the arc's Bloch qubit and Hopf/trefoil Wilson loop. No lattice gauge dynamics is formalized. No new
axioms.

## References

* Z. Dehghan, M. Faber, arXiv:2412.10767, Fig. 1 (colorful vortex; Abelian projection to `σ₁,σ₂,σ₃`). Repo
  carriers: `LorenzQubitBlochDynamics`, `Hopf.QuaternionIsoclinicHopfFibration`,
  `ChernSimons.{WilsonLoopBraidingRibbon,TrefoilFermionChernSimonsInvariant}`,
  `HorizonCell.ElectronDeconfinementCenterVortex`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronAbelianProjectionColorfulVortex


/-- **[The Abelian-projection Cartan axis and its center poles are on the Bloch sphere].** The Maximal Abelian
Gauge projects onto the `U(1)` Cartan `σ₃` direction — the Bloch `z`-axis `blochZAxis = (0,0,1)` — and its two
`σ₃` eigenstates, the `±z` poles, are pure qubit states (points of the Bloch sphere). These two poles are the
`ℤ/2` center elements `±1` that the center projection `Z_μ = signTr[U] = ±1` reads off: the Abelian projection
is the computational-basis (`σ₃`) measurement of the exclusion-cell qubit. -/
lemma abelianProjection_cartan_poles :
    BlochSphere blochZAxis ∧ BlochSphere (-blochZAxis) := by
  constructor <;> simp [BlochSphere, blochZAxis]


/-- **[The colorful center vortex is a Hopf fiber] `hopf(q·c(θ)) = hopf(q)`.** A center vortex is a closed
colorful line — an `S¹` — which in the arc is a Hopf fiber: rotating along the fiber circle `c(θ)` leaves the
Hopf base point fixed. The vortex loop is a fiber of the Hopf fibration `S³ → S²`. -/
lemma colorfulVortex_is_hopf_fiber (q : Quaternion ℝ) (θ : ℝ) :
    hopf (q * fiberCircle θ) = hopf q :=
  hopf_fiber q θ


/-- **[The vortex Wilson loop picks up the ribbon-twist center element] `θ_a = ribbonTwist(a²/2k)`.** The Wilson
loop encircling the center vortex carries the topological spin `θ_a = ribbonTwist(a²/2k)` — the `ℤ/2` (fermion)
/ center phase the loop picks up, the Chern–Simons face of the center element of Dehghan–Faber. -/
lemma vortex_wilson_center (k : ℕ) (a : Fin k) :
    wilsonTopologicalSpin k a = ribbonTwist ((a.val : ℝ) ^ 2 / (2 * k)) :=
  wilsonTopologicalSpin_eq_ribbonTwist k a

/-- **[The colorful vortex's trefoil chirality distinguishes electron from positron].** The trefoil Jones
invariant of the electron differs from the positron's (`electronJones 2 ≠ positronJones 2`): the chirality of the
colorful vortex loop is the `5̄`/`5` electron/positron label of the charge-chirality arc. -/
lemma vortex_trefoil_distinguishes_electron_positron : electronJones 2 ≠ positronJones 2 :=
  trefoil_chiral_distinguishes


/-- **[Fig. 1 of Dehghan–Faber, assembled].**

* **(b)** the Abelian-projection Cartan `σ₃` axis and its center poles `±(0,0,1)` are Bloch-sphere states — the
  qubit's computational basis, with the `ℤ/2` center `±1` at the poles;
* **(a)** the colorful vortex is a Hopf fiber, its Wilson loop carries the ribbon-twist center element, and its
  trefoil chirality distinguishes electron from positron.

Fig. 1's two pictures are the arc's Bloch qubit (Abelian projection) and Hopf/trefoil Wilson loop (colorful
vortex). -/
lemma fig1_abelianProjection_colorfulVortex (q : Quaternion ℝ) (θ : ℝ) (k : ℕ) (a : Fin k) :
    (BlochSphere blochZAxis ∧ BlochSphere (-blochZAxis))
      ∧ hopf (q * fiberCircle θ) = hopf q
      ∧ wilsonTopologicalSpin k a = ribbonTwist ((a.val : ℝ) ^ 2 / (2 * k))
      ∧ electronJones 2 ≠ positronJones 2 :=
  ⟨abelianProjection_cartan_poles, colorfulVortex_is_hopf_fiber q θ,
    vortex_wilson_center k a, vortex_trefoil_distinguishes_electron_positron⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronAbelianProjectionColorfulVortex

end

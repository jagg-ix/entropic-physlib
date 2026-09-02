/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib
public import Physlib.Meta.ZilAssert
public import Physlib.Meta.ZilGroupoidReport

/-!
# Gate: the five-carrier temperature groupoid is closed

The temperature square guarded by `Physlib.Meta.EntropicWepDepthGate` — Unruh, Compton,
Gibbons–Hawking-SI, Hawking — extends by Verlinde's entropic-gravity screen temperature to a
**pentagon**: five carriers from five sectors (Rindler thermality, Compton-clock quantum
mechanics, FLRW cosmology, semiclassical black-hole physics, entropic gravity). This gate
asserts, fail-closed on every build, that the pentagon is *categorically closed*: all ten
edges of the complete graph carry a dimensionally homogeneous bridge constraint AND a
connecting theorem. In the `Physlib.Meta.ZilBridgeGroupoid` vocabulary: the groupoid on these
five objects has no underived composites left.

The four Verlinde edges' constraints are the entropic-gravity content itself —
`R²·a ≐ G·M` against Unruh is the equivalence principle in entropic form
(`unruh_eq_gravityTemperature_iff`), and `R²·κ ≐ G·M` against Hawking is the screen-at-horizon
identification (`verlindeTemperature_at_horizon_is_hawking`).

**The information-dimension readout.** Under the repository's information-extended typing
(`G : L³ T⁻² M⁻¹ I⁻¹` — Newton's constant as area per bit, the Brillouin/Landauer bookkeeping)
every Verlinde edge is inhomogeneous by exactly `I⁻¹`: the entropic-gravity carriers differ
from the four purely kinematic ones by one unit of information dimension, edge by edge. That
mismatch is the Verlinde thesis made dimensional, not an error, so this gate asserts the
pentagon under the information-free SI typing of `G`, and separately re-asserts the `G`-free
square under the information typing — the same double-typing discipline as the WEP gate. The
`I⁻¹` residue is build-enforced below by `#zil_assert_edge_defect`: each of the five Verlinde
edges must carry defect exactly `[I]` (kinematic side over entropic side) under the information
typing — the bookkeeping fails the build if it drifts.

**The octagon.** Two further carriers extend the hexagon: `bitScreenTemperature`
(`2Mc²/(N·k_B)` — Verlinde's equipartition screen with a free bit count, no `G`) and
`schwarzschildHawkingTemperature` (`ℏc³/(8πGMk_B)`).  `#zil_groupoid_report` found all 28
octagon edges homogeneous, surfaced the five bit-screen composites, and showed the
Schwarzschild vertex isolated; the twelve welds of
`Cosmology.FLRW.TemperatureOctagonWelds` close every open edge — recovering Verlinde's
holographic bit count `N = Ac³/(Gℏ)`, the Bekenstein count `16πGM² = Nℏc`, and the
Compton–Hawking mass duality `4GMm = ℏc` as rest-point constraints.  The full octagon is
asserted below.

**The three-rung information ladder.** Under the information typing the octagon spans three
rungs: `schwarzschildHawkingTemperature` carries `I^{+1}` (`G` in the *denominator*, like
the holographic densities of `Physlib.Meta.DensitySectorGate`), the six kinematic carriers
`I⁰`, and both Verlinde carriers `I^{-1}` — `verlindeGravityTemperature` through `G`'s
area-per-bit and `bitScreenTemperature` through the explicit bit count `N : I`.  The defect
assertions below enforce the ladder, including its two sharpest readouts: the
`verlinde ⟶ bitScreen` defect is exactly `[1]` — the two information bookkeepings, one
priced through `G` and one through `N`, cancel edge-internally — and the Schwarzschild
vertex sits a full **two nats** (`[I²]`) from the Verlinde rung, because `G` appears in the
denominator of one carrier and the numerator of the other.

**The hexagon.** Extending by `deBroglieTemperature` (the general-`E` Unruh dual),
`#zil_groupoid_report` surfaced three underived composites, all with proven flanks through the
Unruh carrier and no direct theorem. All three are now closed as the pure compositions the
groupoid predicted — `hawking_eq_deBroglieTemperature_iff` (`κ = E·c/ℏ`),
`deBroglie_eq_gibbonsHawkingSI_iff` (`E = ℏ·H`), `gravity_eq_deBroglieTemperature_iff`
(`GM/R² = E·c/ℏ`) — so the asserts below guard the full **hexagon**: fifteen edges, each
homogeneous and proven, and all five edges into the gravity vertex carrying defect exactly
`[I]` under the information typing. The de Broglie edges are `G`-free except the Verlinde one,
so the information-typed sub-diagram grows to the five kinematic carriers.
-/

-- The full octagon under SI typing: twenty-eight edges, each homogeneous and proven.
#zil_assert_diagram Physlib.Thermodynamics.unruhTemperature,
  Physlib.Thermodynamics.comptonTemperature,
  Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI,
  Physlib.Relativity.SemiClassical.hawkingTemperature,
  Physlib.Thermodynamics.verlindeGravityTemperature,
  Physlib.Thermodynamics.deBroglieTemperature,
  Physlib.Thermodynamics.NewtonGIsolation.bitScreenTemperature,
  Physlib.Relativity.SemiClassical.schwarzschildHawkingTemperature
  with "a : L T^-2, H : T^-1, κ : L T^-2, G : L^3 T^-2 M^-1, M : M, R : L, E : L^2 T^-2 M, N : 1"

-- The G-free sub-diagram — now a pentagon with de Broglie — stays closed under the
-- information-extended typing as well.
#zil_assert_diagram Physlib.Thermodynamics.unruhTemperature,
  Physlib.Thermodynamics.comptonTemperature,
  Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI,
  Physlib.Relativity.SemiClassical.hawkingTemperature,
  Physlib.Thermodynamics.deBroglieTemperature
  with "a : L T^-2, H : T^-1, κ : L T^-2, G : L^3 T^-2 M^-1 I^-1, E : L^2 T^-2 M"

-- The Brillouin/Landauer bookkeeping, build-enforced: every Verlinde edge carries the
-- information-dimension defect exactly [I] under the information-extended typing of G.
#zil_assert_edge_defect Physlib.Thermodynamics.unruhTemperature
  Physlib.Thermodynamics.verlindeGravityTemperature "I"
  with "a : L T^-2, G : L^3 T^-2 M^-1 I^-1, M : M, R : L"
#zil_assert_edge_defect Physlib.Thermodynamics.comptonTemperature
  Physlib.Thermodynamics.verlindeGravityTemperature "I"
  with "G : L^3 T^-2 M^-1 I^-1, M : M, R : L"
#zil_assert_edge_defect Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI
  Physlib.Thermodynamics.verlindeGravityTemperature "I"
  with "H : T^-1, G : L^3 T^-2 M^-1 I^-1, M : M, R : L"
#zil_assert_edge_defect Physlib.Relativity.SemiClassical.hawkingTemperature
  Physlib.Thermodynamics.verlindeGravityTemperature "I"
  with "κ : L T^-2, G : L^3 T^-2 M^-1 I^-1, M : M, R : L"
#zil_assert_edge_defect Physlib.Thermodynamics.deBroglieTemperature
  Physlib.Thermodynamics.verlindeGravityTemperature "I"
  with "E : L^2 T^-2 M, G : L^3 T^-2 M^-1 I^-1, M : M, R : L"

-- The three-rung ladder of the octagon extension.  Kinematic ⟶ bit screen: one nat
-- through the explicit bit count.
#zil_assert_edge_defect Physlib.Thermodynamics.unruhTemperature
  Physlib.Thermodynamics.NewtonGIsolation.bitScreenTemperature "I"
  with "a : L T^-2, M : M, N : I"
#zil_assert_edge_defect Physlib.Thermodynamics.deBroglieTemperature
  Physlib.Thermodynamics.NewtonGIsolation.bitScreenTemperature "I"
  with "E : L^2 T^-2 M, M : M, N : I"
-- The two information bookkeepings cancel: G's area-per-bit against the explicit N.
#zil_assert_edge_defect Physlib.Thermodynamics.verlindeGravityTemperature
  Physlib.Thermodynamics.NewtonGIsolation.bitScreenTemperature "1"
  with "G : L^3 T^-2 M^-1 I^-1, M : M, R : L, N : I"
-- The Schwarzschild vertex sits one nat ABOVE the kinematic rung (G in the denominator)...
#zil_assert_edge_defect Physlib.Thermodynamics.unruhTemperature
  Physlib.Relativity.SemiClassical.schwarzschildHawkingTemperature "I^-1"
  with "a : L T^-2, G : L^3 T^-2 M^-1 I^-1, M : M"
-- ...hence a full two nats from the Verlinde rung, in both of its readings.
#zil_assert_edge_defect Physlib.Relativity.SemiClassical.schwarzschildHawkingTemperature
  Physlib.Thermodynamics.verlindeGravityTemperature "I^2"
  with "G : L^3 T^-2 M^-1 I^-1, M : M, R : L"
#zil_assert_edge_defect Physlib.Relativity.SemiClassical.schwarzschildHawkingTemperature
  Physlib.Thermodynamics.NewtonGIsolation.bitScreenTemperature "I^2"
  with "G : L^3 T^-2 M^-1 I^-1, M : M, N : I"

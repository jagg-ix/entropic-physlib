/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.HolographicLandauerBridge
public import Physlib.Meta.ZilAssert
public import Physlib.Meta.ZilDimension

/-!
# Gate: the complex path integral counts nats — dimensionally certified

`PathIntegralBitProcessing` proves the ℝ-level identities: every entropic path-integral
weight is `exp(−S_ent/k_B)`, Caldeira–Leggett decoherence is `exp(−ΔS_bath/k_B)`, and the
Fujiwara/Compton tick count is action over `h`.  This gate pins the **information
dimension** of that reading, fail-closed, in the double-typing discipline of the WEP and
force gates:

* the repository's **default** binder table already carries the Brillouin price
  (`k_B : E Θ⁻¹ I⁻¹`), so with thermodynamic entropy kept neutral the imaginary action
  `S_I = (ℏ/k_B)·S_ent` carries **exactly one nat** (`[L² T⁻¹ M I]`) and the count
  `S_ent/k_B` is **exactly `[I]`** *out of the box* — the path integral's suppression
  exponent is information-dimensional bit processing under the library's own typing;
* neutralizing `k_B` explicitly (`k_B : E Θ⁻¹`) recovers the plain SI reading — an action
  and a dimensionless exponent — so the nat charge is precisely the Brillouin price and
  nothing else;
* pricing the entropy per-nat as well cancels the charge (`[L² T⁻¹ M]` again) — the same
  two-price consistency the force gate certified for Verlinde's entropic force;
* the **honest boundary**: the Fujiwara/Compton tick count is `k_B`-free, so it stays
  dimensionless under either typing — clock ticks are *not* automatically nats, and the
  gate would fail if anyone tried to make them so by typing alone.  Only entropy transfer
  counts.
-/

-- §1 The nat count itself: dimensionless in SI, exactly [I] under the per-nat price.
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing.entropicNatCount
  "1" with "Sent : L^2 T^-2 M Θ^-1, kB : L^2 T^-2 M Θ^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing.entropicNatCount
  "I" with "Sent : L^2 T^-2 M Θ^-1"

-- §2 The entropic imaginary action: an action in SI; one nat under the kB price; neutral
-- again when the entropy is priced per-nat too (the two prices cancel).
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.ImaginaryLagrangian.entropicAction
  "L^2 T^-1 M" with "Sent : L^2 T^-2 M Θ^-1, kB : L^2 T^-2 M Θ^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.ImaginaryLagrangian.entropicAction
  "L^2 T^-1 M I" with "Sent : L^2 T^-2 M Θ^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.ImaginaryLagrangian.entropicAction
  "L^2 T^-1 M" with "Sent : L^2 T^-2 M Θ^-1 I^-1"

-- §3 The honest boundary: the Fujiwara/Compton tick count is information-neutral — it is
-- dimensionless under SI *and* under the per-nat price. Ticks are not nats.
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing.fujiwaraComptonTickCount
  "1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.PathIntegral.PathIntegralBitProcessing.fujiwaraComptonTickCount
  "1" with "kB : L^2 T^-2 M Θ^-1 I^-1"

-- §4 The holographic typing of G, DERIVED: the area-per-bit carrier `A·c³/(ℏN)` with `N`
-- in the information dimension — the same [I] object the path integral counts — has
-- exactly the holographic Newton dimension `L³T⁻²M⁻¹I⁻¹` every information gate assumed.
-- With a dimensionless count it is plain SI Newton. The convention is forced, not chosen.
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.PathIntegral.HolographicLandauerBridge.areaPerBitCoupling
  "L^3 T^-2 M^-1" with "A : L^2"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.PathIntegral.HolographicLandauerBridge.areaPerBitCoupling
  "L^3 T^-2 M^-1 I^-1" with "A : L^2, N : I"

-- §5 The two nat ledgers are the same [I] object: the holographic screen capacity under
-- the priced G and the path-integral nat count under the priced kB both read exactly [I]
-- — the screen-fill constraint `ΔS/k_B = holographicBits` is information-dimensionally
-- homogeneous, which is what makes it a legitimate physical constraint equation.
#zil_assert_dimension Physlib.Thermodynamics.holographicBits
  "1" with "A : L^2"
#zil_assert_dimension Physlib.Thermodynamics.holographicBits
  "I" with "A : L^2, G : L^3 T^-2 M^-1 I^-1"

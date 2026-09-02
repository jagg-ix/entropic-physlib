/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCorrespondence

/-!
# The SU(4) R-symmetry under C, P, T (Gomis 2507.12467, §2): C preserves, P and T break

The central asymmetry of Gomis's analysis: in `𝒩 = 4` SYM, `C` (charge conjugation, an outer automorphism of
the **gauge** group) leaves the `SU(4)` R-symmetry intact, while `P` and `T` (induced by outer automorphisms of
the **Lorentz** algebra) *necessarily* break it — "unlike `C`, these necessarily break the `SU(4)` R-symmetry"
(intro).  Consequently `S`-duality "must be accompanied with an outer automorphism of the `SU(4)` R-symmetry"
(the `SU(4)` outer automorphism `4 ↦ 4̄` combining with `S` in `P ↦ CP`, `T ↦ CT`).

Extending `SciamaAdSCPTCorrespondence`, a discrete symmetry `(c, p, t) ∈ (ℤ/2)³` breaks the `SU(4)` R-symmetry
exactly when its `P`/`T` content is odd:

`breaksRSymmetry(c, p, t) = p + t  (mod 2)`

— the `C`-content is irrelevant (`C` acts on the gauge group, not the R-symmetry).

* `breaksRSymmetry_charge_conjugation` — `C` preserves `SU(4)` (`= 0`);
* `breaksRSymmetry_parity`, `breaksRSymmetry_time_reversal` — `P` and `T` each break it (`= 1`);
* `breaksRSymmetry_PT_restored` — **`PT` preserves `SU(4)`** (`= 0`): the two Lorentz outer automorphisms
  compose to the identity on the R-symmetry;
* `breaksRSymmetry_CPT` — `CPT` preserves `SU(4)` (`= 0`): the `CPT` theorem's symmetry is a genuine symmetry
  of the full theory, R-symmetry included;
* `sDuality_preserves_RSymmetryBreaking` — **`S`-duality preserves the R-breaking parity**: since `S` changes
  only the `C`-content (`P ↦ CP`, `T ↦ CT`), the required `SU(4)` outer automorphism accompanies `S` uniformly,
  consistently across a duality frame (`breaksRSymmetry(P) = breaksRSymmetry(CP) = 1`).

This is the R-symmetry layer of the AdS/C-P-T correspondence: `C` and `CPT` are R-symmetry-preserving (matching
their `S`-invariance in `SciamaAdSCPTCorrespondence`), while `P` and `T` break `SU(4)` and are exchanged with
`CP`, `CT` under the `S`-duality that carries the `SU(4)` outer automorphism.

Honest scope: the `ℤ/2` R-breaking parity of `C, P, T` and its `S`-duality invariance (the paper's stated
`SU(4)` structure).  The representation-theoretic derivation — that the Lorentz outer automorphisms act on the
`SU(4)` as `4 ↦ 4̄` — is the paper's content, contextualized here.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRSymmetry

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCorrespondence

/-- Whether a discrete `C`/`P`/`T` symmetry **breaks the `SU(4)` R-symmetry**: the `P + T` parity of its charge
vector.  `C` acts on the gauge group (R-symmetry-preserving), `P` and `T` on the Lorentz algebra (R-breaking). -/
def breaksRSymmetry (x : CPTCharge) : ZMod 2 := x.2.1 + x.2.2

/-- **[C preserves SU(4)] `breaksRSymmetry(C) = 0`.**  Charge conjugation is an outer automorphism of the gauge
group and leaves the R-symmetry intact. -/
theorem breaksRSymmetry_charge_conjugation : breaksRSymmetry chargeC = 0 := by decide

/-- **[P breaks SU(4)] `breaksRSymmetry(P) = 1`.** -/
theorem breaksRSymmetry_parity : breaksRSymmetry chargeP = 1 := by decide

/-- **[T breaks SU(4)] `breaksRSymmetry(T) = 1`.** -/
theorem breaksRSymmetry_time_reversal : breaksRSymmetry chargeT = 1 := by decide

/-- **[PT restores SU(4)] `breaksRSymmetry(PT) = 0`.**  The two Lorentz outer automorphisms compose to the
identity on the `SU(4)` R-symmetry, so parity-time preserves it even though `P` and `T` each break it. -/
theorem breaksRSymmetry_PT_restored : breaksRSymmetry (chargeP + chargeT) = 0 := by decide

/-- **[CPT preserves SU(4)] `breaksRSymmetry(CPT) = 0`.**  The `CPT`-symmetry is a genuine symmetry of the full
theory, R-symmetry included — matching its `S`-invariance (`sDuality_CPT_invariant`). -/
theorem breaksRSymmetry_CPT : breaksRSymmetry chargeCPT = 0 := by decide

/-- **[S-duality carries the SU(4) outer automorphism uniformly] `breaksRSymmetry(σ x) = breaksRSymmetry(x)`.**
`S`-duality changes only the `C`-content (`P ↦ CP`, `T ↦ CT`), so the R-breaking parity is `S`-invariant: the
`SU(4)` outer automorphism accompanying `S` is consistent across duality frames
(`breaksRSymmetry(P) = breaksRSymmetry(CP) = 1`). -/
theorem sDuality_preserves_RSymmetryBreaking (x : CPTCharge) :
    breaksRSymmetry (sDuality x) = breaksRSymmetry x := by
  unfold breaksRSymmetry sDuality
  rfl

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRSymmetry

end

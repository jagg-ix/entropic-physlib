/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

/-!
# The second Bianchi identity, the second cyclic face: `R^a_{b[cd;e]} = 0` → `∇G = 0` → conservation

Completes the Bianchi side of Van den Bergh (arXiv:1302.6448): alongside the **first** Bianchi `R_{a[bcd]}=0`
(= the frame Jacobi, `Curvature.JacobiRicciBianchiTetrad`, `BCJDoubleCopy.JacobiBianchiDoubleCopyFamily`), the **second** (differential)
Bianchi identity `R^a_{b[cd;e]} = 0` (Eq 17) is the *same cyclic operator* applied to the covariant derivative
of the curvature — a `cyclicSum` over the two curvature indices and the derivative index. Contracting it gives
the **divergence-free Einstein tensor** `∇^a G_{ab} = 0`, the repo's contracted second Bianchi, hence
energy–momentum **conservation** `∇^a T_{ab} = 0` through the field equations.

* **§A — the second Bianchi as a cyclic sum.** `SecondBianchi D` (`D a b c d e = R^a_{bcd;e}`) is
 `∀ …, cyclicSum (D a b) c d e = 0`; `secondBianchi_iff_explicit` is its `R^a_{bcd;e}+R^a_{bde;c}+R^a_{bec;d}=0`
 form — the second face of the one cyclic identity.
* **§B — the contracted consequence: conservation.** Reusing `LeviCivita.BianchiValidation`: the contracted
 second Bianchi `∇G = 0` (`contractedSecondBianchi`) plus the Einstein field equation forces `∇T = 0`
 (`bianchi_validates_fieldEquation`).
* **§C — the main result** `second_bianchi_cyclic_and_conservation`: the second Bianchi is the second cyclic face
 *and* (in contracted form) the source of conservation.

Proven: the second Bianchi identity is recast into the common `cyclicSum` form (reusing
`Curvature.JacobiRicciBianchiTetrad.cyclicSum`), and the contracted-form conservation chain is reused verbatim from
`LeviCivita.BianchiValidation`. The metric contraction `R^a_{b[cd;e]} → ∇^a G_{ab}` (the step from the
uncontracted cyclic identity to `∇G = 0`) is the index-contraction calculus, not mechanized here; the two
faces are stated and the contracted face is the existing `∇G=0 ⟹ ∇T=0` theorem. See also
`BCJDoubleCopy.SecondBianchiConservation` / `Electromagnetic.EMSecondBianchiDoubleCopy` for the gauge-side second Bianchi.

## References

* **Primary source.** N. Van den Bergh, *On the relation between the Einstein field equations and the
 Jacobi–Ricci–Bianchi system*, Class. Quantum Grav. **31** (2014) 145007,
 doi:10.1088/0264-9381/31/14/145007; arXiv:1302.6448v3 [gr-qc] (10 June 2013) — second (differential)
 Bianchi identity: Cartan form `dR^a_b − R^a_c∧Γ^c_b + Γ^a_c∧R^c_b = 0` (Eq (5), p. 3) and the
 component form `R^a_{b[cd;e]} = 0` (Eq (17), p. 3).
* Contracted second Bianchi ⟹ `∇^a G_{ab} = 0` ⟹ `∇^a T_{ab} = 0`: `Physlib`
 (`Curvature.JacobiRicciBianchiTetrad.cyclicSum`, `LeviCivita.BianchiValidation.{contractedSecondBianchi,
 einsteinDivergence_eq_zero_iff, bianchi_validates_fieldEquation}`, `BCJDoubleCopy.SecondBianchiConservation`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad (cyclicSum)
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily

/-! ## §A — the second (differential) Bianchi identity as a cyclic sum -/

/-- **The second (differential) Bianchi identity — Van den Bergh arXiv:1302.6448v3, Eq (17), p. 3**
`R^a_{b[cd;e]} = 0` — the cyclic sum over the two curvature indices `c,d` and the covariant-derivative index
`e` of `D a b c d e = R^a_{bcd;e}` vanishes (Cartan form Eq (5), p. 3). It is the second face of the same
cyclic operator as the first Bianchi identity (Eq (14), p. 3). -/
def SecondBianchi {κ : Type*} (D : κ → κ → κ → κ → κ → ℝ) : Prop :=
  ∀ a b c d e, cyclicSum (D a b) c d e = 0

/-- **[The second Bianchi identity, written out]** `R^a_{bcd;e} + R^a_{bde;c} + R^a_{bec;d} = 0` — the cyclic
identity in the last three (curvature–curvature–derivative) indices. -/
theorem secondBianchi_iff_explicit {κ : Type*} (D : κ → κ → κ → κ → κ → ℝ) :
    SecondBianchi D ↔ ∀ a b c d e, D a b c d e + D a b d e c + D a b e c d = 0 :=
  Iff.rfl

/-! ## §B — the contracted consequence: divergence-free Einstein ⟹ conservation -/

/-- **[The contracted second Bianchi is `∇G = 0`]** the divergence of the Einstein tensor vanishes exactly when
the contracted second Bianchi identity holds (`LeviCivita.BianchiValidation`, reused). -/
theorem contracted_second_bianchi_einstein_divergence {ι : Type*} [Fintype ι]
    (divRicci gradScalar : ι → ℝ) :
    einsteinDivergence divRicci gradScalar = 0 ↔ contractedSecondBianchi divRicci gradScalar :=
  einsteinDivergence_eq_zero_iff divRicci gradScalar

/-! ## §C — the second Bianchi: second cyclic face and source of conservation -/

/-- **[The second Bianchi: the second cyclic face and the source of conservation]** the differential Bianchi
identity is (i) a `cyclicSum`-vanishing `R^a_{bcd;e}+R^a_{bde;c}+R^a_{bec;d}=0` — the second face of the cyclic
identity unified in `BCJDoubleCopy.JacobiBianchiDoubleCopyFamily` — and (ii) in contracted form `∇G = 0`, with the Einstein
field equation, it forces energy–momentum conservation `∇T = 0`. -/
theorem second_bianchi_cyclic_and_conservation {κ : Type*}
    (D : κ → κ → κ → κ → κ → ℝ) (hSB : SecondBianchi D)
    {ι : Type*} [Fintype ι] (divRicci gradScalar divT : ι → ℝ) (kappa : ℝ) (hk : kappa ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-kappa) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) :
    (∀ a b c d e, D a b c d e + D a b d e c + D a b e c d = 0)
      ∧ divT = 0 :=
  ⟨hSB, bianchi_validates_fieldEquation divRicci gradScalar divT kappa hk hField hBianchi⟩

end Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily

end

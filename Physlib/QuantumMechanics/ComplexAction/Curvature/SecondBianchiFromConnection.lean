/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily -/

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

**Honest layering.** Proven: the second Bianchi identity is recast into the common `cyclicSum` form (reusing
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


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad (cyclicSum)
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily


/-- **The second (differential) Bianchi identity — Van den Bergh arXiv:1302.6448v3, Eq (17), p. 3**
`R^a_{b[cd;e]} = 0` — the cyclic sum over the two curvature indices `c,d` and the covariant-derivative index
`e` of `D a b c d e = R^a_{bcd;e}` vanishes (Cartan form Eq (5), p. 3). It is the second face of the same
cyclic operator as the first Bianchi identity (Eq (14), p. 3). -/
def SecondBianchi {κ : Type*} (D : κ → κ → κ → κ → κ → ℝ) : Prop :=
  ∀ a b c d e, cyclicSum (D a b) c d e = 0

/-- **[The second Bianchi identity, written out]** `R^a_{bcd;e} + R^a_{bde;c} + R^a_{bec;d} = 0` — the cyclic
identity in the last three (curvature–curvature–derivative) indices. -/
lemma secondBianchi_iff_explicit {κ : Type*} (D : κ → κ → κ → κ → κ → ℝ) :
    SecondBianchi D ↔ ∀ a b c d e, D a b c d e + D a b d e c + D a b e c d = 0 :=
  Iff.rfl


/-- **[The contracted second Bianchi is `∇G = 0`]** the divergence of the Einstein tensor vanishes exactly when
the contracted second Bianchi identity holds (`LeviCivita.BianchiValidation`, reused). -/
lemma contracted_second_bianchi_einstein_divergence {ι : Type*} [Fintype ι]
    (divRicci gradScalar : ι → ℝ) :
    einsteinDivergence divRicci gradScalar = 0 ↔ contractedSecondBianchi divRicci gradScalar :=
  einsteinDivergence_eq_zero_iff divRicci gradScalar


/-- **[The second Bianchi: the second cyclic face and the source of conservation]** the differential Bianchi
identity is (i) a `cyclicSum`-vanishing `R^a_{bcd;e}+R^a_{bde;c}+R^a_{bec;d}=0` — the second face of the cyclic
identity unified in `BCJDoubleCopy.JacobiBianchiDoubleCopyFamily` — and (ii) in contracted form `∇G = 0`, with the Einstein
field equation, it forces energy–momentum conservation `∇T = 0`. -/
lemma second_bianchi_cyclic_and_conservation {κ : Type*}
    (D : κ → κ → κ → κ → κ → ℝ) (hSB : SecondBianchi D)
    {ι : Type*} [Fintype ι] (divRicci gradScalar divT : ι → ℝ) (kappa : ℝ) (hk : kappa ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-kappa) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) :
    (∀ a b c d e, D a b c d e + D a b d e c + D a b e c d = 0)
      ∧ divT = 0 :=
  ⟨hSB, bianchi_validates_fieldEquation divRicci gradScalar divT kappa hk hField hBianchi⟩

end Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily

end

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection -/

/-!
# The second (differential) Bianchi identity from a connection

The repository has the **first** (algebraic) Bianchi identity proven from a connection
(`riemannFromConnection_firstBianchi`), and the **second** (differential) Bianchi identity
`R^a_{b[cd;e]} = 0` only as an abstract predicate `SecondBianchi` (`SecondBianchiCyclicFamily`) that is
never constructed from an actual connection — so the contracted Bianchi `∇^a G_{ab} = 0` is always a
hypothesis threaded through every conservation theorem.

This module supplies the missing construction, mirroring `riemannFromConnection_firstBianchi`.  At a
point where the connection vanishes (`Γ = 0`, a geodesic normal frame), the covariant derivative of
the curvature reduces to the partial derivative, `∇_e R^ρ_{σμν} = ∂_e(∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ})`,
built from the connection's **second jet** `ddΓ` (`ddΓ e μ ρ = ∂_e ∂_μ Γ^ρ`).  The cyclic sum then
vanishes by the **symmetry of mixed second partials** `∂_e ∂_μ = ∂_μ ∂_e` — exactly as the first
Bianchi reduces to symmetric-jet cancellation.

* `covariantRiemannFlat` — the covariant derivative of the Riemann tensor at `Γ = 0`.
* `covariantRiemannFlat_secondBianchi` — the second Bianchi identity `∇_{[e}R^ρ_{|σ|μν]} = 0`.
* `covariantRiemann_isSecondBianchi` — it satisfies the repository's abstract `SecondBianchi` predicate,
  so `SecondBianchi` is now realized by a genuine connection-built covariant curvature derivative.

Honest scope: this is the `Γ = 0` (normal-frame) specialization — the same specialization
`riemannFromConnection_firstBianchi` uses; the mixed-partial symmetry of the second jet is the labeled
input, and the further metric contraction to `∇^a G_{ab} = 0` (raising and tracing) is not done here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily

variable {ι : Type*} [Fintype ι]

/-- **The covariant derivative of the Riemann curvature at a normal frame** `Γ = 0`:
`∇_e R^ρ_{σμν} = ∂_e(∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ}) = (∂_e∂_μ Γ^ρ)_{νσ} − (∂_e∂_ν Γ^ρ)_{μσ}`, from the
connection's second jet `ddΓ` (`ddΓ e μ ρ = ∂_e ∂_μ Γ^ρ`). -/
def covariantRiemannFlat (ddΓ : ι → ι → ι → Matrix ι ι ℝ) (e ρ σ μ ν : ι) : ℝ :=
  (ddΓ e μ ρ) ν σ - (ddΓ e ν ρ) μ σ

/-- At a normal frame the connection-built Riemann tensor is `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ}`
(the `ΓΓ` terms drop) — so `covariantRiemannFlat` is its `∂_e`, linking to `riemannFromConnection`. -/
lemma riemannFromConnection_flat_eq (dΓ : ι → ι → Matrix ι ι ℝ) (ρ σ μ ν : ι) :
    riemannFromConnection (fun _ => 0) dΓ ρ σ μ ν = (dΓ μ ρ) ν σ - (dΓ ν ρ) μ σ := by
  simp [riemannFromConnection]

/-- **[Antisymmetry in the curvature pair] `∇_e R^ρ_{σμν} = −∇_e R^ρ_{σνμ}`.** -/
lemma covariantRiemannFlat_antisymm (ddΓ : ι → ι → ι → Matrix ι ι ℝ) (e ρ σ μ ν : ι) :
    covariantRiemannFlat ddΓ e ρ σ μ ν = -covariantRiemannFlat ddΓ e ρ σ ν μ := by
  simp only [covariantRiemannFlat]; ring

/-- **The second (differential) Bianchi identity** `R^ρ_{σμν;e} + R^ρ_{σνe;μ} + R^ρ_{σeμ;ν} = 0` at a
normal frame — the cyclic sum over the two curvature indices and the covariant-derivative index
vanishes by the symmetry of mixed second partials of the connection. -/
@[zil_level physical_theorem]
theorem covariantRiemannFlat_secondBianchi (ddΓ : ι → ι → ι → Matrix ι ι ℝ)
    (hsymm : ∀ a b r, ddΓ a b r = ddΓ b a r) (ρ σ e μ ν : ι) :
    covariantRiemannFlat ddΓ e ρ σ μ ν + covariantRiemannFlat ddΓ μ ρ σ ν e
      + covariantRiemannFlat ddΓ ν ρ σ e μ = 0 := by
  simp only [covariantRiemannFlat]
  rw [hsymm μ e ρ, hsymm ν e ρ, hsymm ν μ ρ]
  ring

/-- **The connection-built covariant curvature derivative satisfies the abstract `SecondBianchi`
predicate.**  Packaging `R^a_{bcd;e} := ∇_e R^a_{bcd}` (`covariantRiemannFlat`), the repository's
`SecondBianchi` — hitherto only an assumption — is realized by a genuine connection construction. -/
@[zil_level bridge_theorem]
theorem covariantRiemann_isSecondBianchi (ddΓ : ι → ι → ι → Matrix ι ι ℝ)
    (hsymm : ∀ a b r, ddΓ a b r = ddΓ b a r) :
    SecondBianchi (fun a b c d e => covariantRiemannFlat ddΓ e a b c d) := by
  rw [secondBianchi_iff_explicit]
  intro a b c d e
  simp only [covariantRiemannFlat]
  rw [hsymm c e a, hsymm d e a, hsymm d c a]
  ring

end Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection

zil attach covariantRiemannFlat_secondBianchi where
  formalizes @ "claim:the-second-differential-bianchi-identity-the-cyclic-covariant-derivative-of-the-riemann-curvature-vanishes-at-a-normal-frame-built-from-the-connection-second-jet-by-the-symmetry-of-mixed-second-partials"

zil attach covariantRiemann_isSecondBianchi where
  formalizes @ "claim:the-connection-built-covariant-curvature-derivative-satisfies-the-abstract-second-bianchi-predicate-so-the-repository-second-bianchi-is-realized-by-a-genuine-connection-construction-not-an-assumption",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily.SecondBianchi"

zil_file_contract physlib.secondBianchiFromConnection where
  promises "The second differential Bianchi identity constructed from a connection, filling the gap that the repository's SecondBianchi predicate was never realized by an actual connection. At a normal frame where the connection vanishes, the covariant derivative of the Riemann curvature reduces to the partial derivative built from the connection second jet, and the cyclic sum over the two curvature indices and the covariant-derivative index vanishes by the symmetry of mixed second partials of the connection. This connection-built covariant curvature derivative satisfies the abstract SecondBianchi predicate, so the second Bianchi identity is now realized by a genuine connection construction rather than being assumed. Honest scope: this is the normal-frame specialization mirroring the first Bianchi from a connection; the mixed-partial symmetry of the second jet is the labeled input, and the further metric contraction to the contracted Bianchi divergence of the Einstein tensor equals zero is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.riemannFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily.SecondBianchi"
  ]
  forbids_substitutes [
    "reading the normal-frame second Bianchi as the general covariant-derivative identity away from a normal frame, or as the metric-contracted vanishing divergence of the Einstein tensor"
  ]
  witnessed_by [
    covariantRiemannFlat_secondBianchi,
    covariantRiemann_isSecondBianchi
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.secondBianchiFromConnection

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.RicciSecondBianchiFromConnection -/

/-!
# The once-contracted (Ricci) second Bianchi identity from a connection

Contracting the differential second Bianchi identity `∇_{[e}R^ρ_{|σ|μν]} = 0`
(`covariantRiemannFlat_secondBianchi`) on the upper index with a curvature index gives the Ricci form

`∇_e R_{σν} + ∇_a R^a_{σνe} − ∇_ν R_{σe} = 0`,

using the antisymmetry `R^a_{σea} = −R^a_{σae}` of the curvature.  This is the first metric-free step of
the contraction chain toward `∇^a G_{ab} = 0`; the repository carried the second Bianchi only as an
abstract predicate, so no contracted form existed.

* `ricciDerivFlat` — the covariant Ricci derivative `∇_e R_{σν}` at a normal frame.
* `ricci_secondBianchi` — the once-contracted second Bianchi identity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RicciSecondBianchiFromConnection

open Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection

variable {ι : Type*} [Fintype ι]

/-- **The covariant Ricci derivative at a normal frame** `∇_e R_{σν} = ∑_a ∇_e R^a_{σaν}`. -/
def ricciDerivFlat (ddΓ : ι → ι → ι → Matrix ι ι ℝ) (e σ ν : ι) : ℝ :=
  ∑ a, covariantRiemannFlat ddΓ e a σ a ν

/-- **The covariant Riemann divergence at a normal frame** `∑_a ∇_a R^a_{σνe}`. -/
def riemannDivFlat (ddΓ : ι → ι → ι → Matrix ι ι ℝ) (σ ν e : ι) : ℝ :=
  ∑ a, covariantRiemannFlat ddΓ a a σ ν e

/-- **The once-contracted (Ricci) second Bianchi identity** `∇_e R_{σν} + ∇_a R^a_{σνe} − ∇_ν R_{σe} = 0`
at a normal frame — the metric-free contraction of the differential second Bianchi. -/
@[zil_level physical_theorem]
theorem ricci_secondBianchi (ddΓ : ι → ι → ι → Matrix ι ι ℝ)
    (hsymm : ∀ a b r, ddΓ a b r = ddΓ b a r) (σ ν e : ι) :
    ricciDerivFlat ddΓ e σ ν + riemannDivFlat ddΓ σ ν e - ricciDerivFlat ddΓ ν σ e = 0 := by
  have hsum :
      ∑ a, (covariantRiemannFlat ddΓ e a σ a ν + covariantRiemannFlat ddΓ a a σ ν e
        + covariantRiemannFlat ddΓ ν a σ e a) = 0 :=
    Finset.sum_eq_zero fun a _ => covariantRiemannFlat_secondBianchi ddΓ hsymm a σ e a ν
  have hanti : (∑ a, covariantRiemannFlat ddΓ ν a σ e a) = -ricciDerivFlat ddΓ ν σ e := by
    unfold ricciDerivFlat
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => covariantRiemannFlat_antisymm ddΓ ν a σ e a
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hanti] at hsum
  simp only [ricciDerivFlat, riemannDivFlat] at hsum ⊢
  linarith

end Physlib.QuantumMechanics.ComplexAction.Curvature.RicciSecondBianchiFromConnection

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciSecondBianchiFromConnection

zil attach ricci_secondBianchi where
  formalizes @ "claim:the-once-contracted-ricci-second-bianchi-identity-covariant-ricci-derivative-plus-riemann-divergence-minus-the-transposed-ricci-derivative-vanishes-at-a-normal-frame-the-metric-free-contraction-of-the-differential-second-bianchi",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection.covariantRiemannFlat_secondBianchi"

zil_file_contract physlib.ricciSecondBianchiFromConnection where
  promises "The once-contracted Ricci second Bianchi identity from a connection, the metric-free contraction of the differential second Bianchi. Contracting the second Bianchi on the upper index with a curvature index, using the antisymmetry of the curvature in its last pair, gives the Ricci form: the covariant Ricci derivative del e R sigma nu plus the Riemann divergence sum over a of del a R upper a sigma nu e minus the transposed Ricci derivative del nu R sigma e vanishes at a normal frame. This is the first metric-free step of the contraction chain toward the contracted Bianchi divergence of the Einstein tensor equals zero. Honest scope: this is the once-contracted metric-free form at a normal frame; the further metric raising and second contraction to the vanishing Einstein-tensor divergence are not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection.covariantRiemannFlat_secondBianchi",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection.covariantRiemannFlat"
  ]
  forbids_substitutes [
    "reading the once-contracted metric-free Ricci Bianchi identity as the fully metric-contracted vanishing divergence of the Einstein tensor"
  ]
  witnessed_by [
    ricci_secondBianchi
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.ricciSecondBianchiFromConnection


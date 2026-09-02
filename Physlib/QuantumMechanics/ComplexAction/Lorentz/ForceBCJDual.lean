/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.Electromagnetism.Kinematics.GaugeTransformation
public import Physlib.Electromagnetism.Kinematics.Boosts
public import Physlib.Electromagnetism.ThreeDimension.MaxwellEquations
public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM
meta import Zil

/-!
# The BCJ double-copy dual of the Lorentz force

Uses the Bern–Carrasco–Johansson formalization (`BCJDoubleCopy.ColorKinematicsDoubleCopy`) to construct the
**double-copy dual of the Lorentz force**. The Lorentz force `F^μ_ν V^ν` is the *gauge*-side force on a
charged particle (the field strength `F = dA` contracted with the velocity); being linear in `V` it is
**`T`-odd** under the velocity reversal `V ↦ −V` of the Vlasov / diamond time reversal. Its BCJ double copy —
`(F·V)²/D`, the gauge numerator squared over the mass-shell propagator — is the **gravity**-side dual, and it
is **`T`-even**: the double copy "gravity = gauge²" *squares away* the velocity reversal, exactly as the
Jacobson-diamond channel does (`BCJDoubleCopy.DiamondTimeReversal.diamondBCJ_doublecopy_timeReversal_invariant`).

So the Lorentz force has a gravitational dual that is nonnegative and time-reversal invariant — the BCJ shadow
of the geodesic/tidal force, with the gauge force's `T`-odd sign squared away.

* **§A — the Lorentz force as a gauge BCJ numerator** (`lorentzForceNum`, `lorentzForceNum_timeReversal`,
  `lorentzForceTriple`). `n = (F V)_μ`, `T`-odd; packaged as a BCJ channel with a positive mass-shell
  propagator.
* **§B — the gravitational dual via the double copy** (`lorentzForceDual`, `lorentzForceDual_nonneg`,
  `lorentzForceDual_timeReversal_invariant`). `n²/D ≥ 0` (consuming `bcjDoubleCopy_diagonal_nonneg`) and
  `T`-even — gravity = gauge² removes the sign.
* **§C — the Maxwell instance** (`maxwellLorentzForceDual_nonneg`, `maxwellLorentzForceDual_invariant`). For
  the field strength `F = faraday k A`, the Lorentz-force dual of the Maxwell field; the field does no work
  on the 4-velocity (`F^μ_ν U^μ U^ν = 0`, the antisymmetry — cf. `Vlasov.MaxwellEM.faraday_no_work`),
  yet its double-copy dual `(F U)²/D` is a nonnegative `T`-even gravitational force.
* **§D — force derived from the potential** (`potentialLorentzForceNumerator_apply_eq_derivatives`).
  The repository's differentiable electromagnetic potential is antisymmetrically differentiated and
  contracted with a covariant four-velocity, reproducing Field's Eqs. 3.9--3.11 without introducing a
  second field-strength definition.
* **§E — gauge, induction, and work** (`potentialLorentzForceNumerator_gauge_invariant`,
  `potential_faraday_lenz`, `lorentzThreeForce_power`).  The derived force is gauge invariant, the same
  potential gives Faraday--Lenz induction, and the magnetic term performs exactly zero work.
* **§F — the paper's missing logical boundaries** (`potentialDerivativeCandidate_antisymmetric_iff`,
  `potentialElectricField_longitudinal_boost`, `lorentzThreeForce_work_energy`,
  `pureMagnetic_lorentz_energy_conserved`).  Antisymmetry uniquely fixes the minus sign inside the stated
  two-term derivative ansatz, the longitudinal electric component obeys the proved Lorentz-boost law, and
  the pointwise power identity is integrated to the paper's work--energy equation and pure-magnetic
  conservation corollary.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, arXiv:0805.3993 (the double copy); the gauge/gravity Lorentz
  force ↔ geodesic correspondence.
* Repo carriers: `BCJDoubleCopy.ColorKinematicsDoubleCopy` (`BCJTriple`, `bcjDoubleCopy_diagonal_nonneg`);
  `PTSymmetricQFT.MaxwellFaraday` (`faraday`); cf. `BCJDoubleCopy.DiamondTimeReversal`,
  `Vlasov.DiamondTimeReversal`.
* J. H. Field, *Derivation of the Lorentz Force Law and the Magnetic Field Concept using an Invariant
  Formulation of the Lorentz Transformation* (2003), especially Eqs. 3.4--3.16 and 4.5.

## Scope

The formalization proves the potential-to-field-to-force chain, gauge invariance, Faraday--Lenz law,
four-force orthogonality, the three-force work identity, and its interval-integrated form.  It deliberately
does not encode the paper's informal claim that covariance uniquely selects the minus sign among every
conceivable field definition: both symmetric and antisymmetric covariant derivatives can define tensors.
Instead it proves the exact valid statement for the paper's displayed two-term ansatz: requiring the result
to be antisymmetric for arbitrary derivative data uniquely fixes the relative coefficient to `-1`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual

open Matrix
open Electromagnetism
open Electromagnetism.ElectromagneticPotential
open ContDiff
open SpaceTime
open minkowskiMatrix
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM
open Set MeasureTheory
open scoped Interval


/-- **The Lorentz force numerator** `(F^μ_ν V^ν)_μ` — the gauge field strength contracted with
the velocity, at one component.  The finite index is generic so the same definition applies both to the
`Fin 4` BCJ carrier and the electromagnetic backend's typed `Fin 1 ⊕ Fin d` spacetime index. -/
def lorentzForceNum {I : Type} [Fintype I]
    (F : Matrix I I ℝ) (V : I → ℝ) (μ : I) : ℝ := (F *ᵥ V) μ

/-- **[`T`-odd] The Lorentz force flips under velocity reversal** `(F(−V))_μ = −(F V)_μ` — the gauge force
is `T`-odd, like the Vlasov velocity and the diamond momentum. -/
lemma lorentzForceNum_timeReversal {I : Type} [Fintype I]
    (F : Matrix I I ℝ) (V : I → ℝ) (μ : I) :
    lorentzForceNum F (-V) μ = -(lorentzForceNum F V μ) := by
  simp [lorentzForceNum, Matrix.mulVec_neg]

/-- **The BCJ gauge channel of the Lorentz force** — kinematic numerator `(F V)_μ`, positive mass-shell
propagator `D`. -/
noncomputable def lorentzForceTriple {I : Type} [Fintype I]
    (F : Matrix I I ℝ) (V : I → ℝ) (μ : I) (D : ℝ) (hD : 0 < D) : BCJTriple where
  numerator := lorentzForceNum F V μ
  color := lorentzForceNum F V μ
  propagator := D
  prop_pos := hD


/-- **The double-copy dual of the Lorentz force** `(F V)²/D` — the gravity-side force, the gauge numerator
squared over the mass-shell propagator. -/
noncomputable def lorentzForceDual {I : Type} [Fintype I]
    (F : Matrix I I ℝ) (V : I → ℝ) (μ : I) (D : ℝ) : ℝ :=
  (lorentzForceNum F V μ) ^ 2 / D

/-- **The gravitational dual is nonnegative** — consuming `bcjDoubleCopy_diagonal_nonneg` for the Lorentz
channel. -/
lemma lorentzForceDual_nonneg {I : Type} [Fintype I]
    (F : Matrix I I ℝ) (V : I → ℝ) (μ : I)
    (D : ℝ) (hD : 0 < D) : 0 ≤ lorentzForceDual F V μ D :=
  bcjDoubleCopy_diagonal_nonneg (lorentzForceTriple F V μ D hD)

/-- **[Gravity = gauge² squares `T` away] The Lorentz-force dual is `T`-even** `(F(−V))²/D = (F V)²/D` —
although the gauge Lorentz force is `T`-odd (`lorentzForceNum_timeReversal`), the double-copied gravitational
dual squares the sign away and is time-reversal invariant, exactly as the diamond channel
(`diamondBCJ_doublecopy_timeReversal_invariant`). -/
lemma lorentzForceDual_timeReversal_invariant {I : Type} [Fintype I]
    (F : Matrix I I ℝ) (V : I → ℝ)
    (μ : I) (D : ℝ) : lorentzForceDual F (-V) μ D = lorentzForceDual F V μ D := by
  unfold lorentzForceDual; rw [lorentzForceNum_timeReversal]; ring


/-- **The Maxwell Lorentz-force dual is nonnegative** — for the field strength `F = dA`. -/
lemma maxwellLorentzForceDual_nonneg (k A V : Fin 4 → ℝ) (μ : Fin 4) (D : ℝ) (hD : 0 < D) :
    0 ≤ lorentzForceDual (faraday k A) V μ D :=
  lorentzForceDual_nonneg (faraday k A) V μ D hD

/-- **The Maxwell Lorentz-force dual is `T`-even** — the gravitational dual of the Maxwell field's Lorentz
force is time-reversal invariant. -/
lemma maxwellLorentzForceDual_invariant (k A V : Fin 4 → ℝ) (μ : Fin 4) (D : ℝ) :
    lorentzForceDual (faraday k A) (-V) μ D = lorentzForceDual (faraday k A) V μ D :=
  lorentzForceDual_timeReversal_invariant (faraday k A) V μ D

/-! ## D. The potential-to-field-to-force derivation -/

/-- The Lorentz four-force numerator derived from the repository's electromagnetic potential:
`F^{μν} U_ν`, where `F = dA`.  `Ucov` is explicitly a covariant velocity, so the ordinary finite
sum performs the correct upper/lower-index contraction. -/
noncomputable def potentialLorentzForceNumerator {d : ℕ} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (Ucov : (Fin 1 ⊕ Fin d) → ℝ) : (Fin 1 ⊕ Fin d) → ℝ :=
  fun μ => lorentzForceNum (fun κ ρ => A.fieldStrengthMatrix x (κ, ρ)) Ucov μ

/-- The paper's displayed class of local first-derivative candidates,
`D_μ A_ν + s D_ν A_μ`.  The electromagnetic choice is `s = -1`; keeping the coefficient visible
separates the valid algebraic uniqueness statement below from the paper's broader covariance rhetoric. -/
def potentialDerivativeCandidate {I : Type*} (s : ℝ)
    (D : I → I → ℝ) (μ ν : I) : ℝ :=
  D μ ν + s * D ν μ

/-- **Restricted uniqueness behind Field Eq. 3.4.**  On any index type containing two distinct directions,
the two-term first-derivative candidate is antisymmetric for every derivative jet exactly when its relative
coefficient is `-1`.  The reverse implication is the usual `dA`; the forward implication is witnessed by a
jet with only `D j i = 1`.

This proves uniqueness in the explicitly declared ansatz.  It does not claim that Lorentz covariance by
itself excludes every other local or nonlocal operator. -/
theorem potentialDerivativeCandidate_antisymmetric_iff
    {I : Type*} (i j : I) (hij : i ≠ j) (s : ℝ) :
    (∀ (D : I → I → ℝ) (μ ν : I),
      potentialDerivativeCandidate s D μ ν =
        -potentialDerivativeCandidate s D ν μ) ↔ s = -1 := by
  classical
  constructor
  · intro h
    let D : I → I → ℝ := fun μ ν => if μ = j ∧ ν = i then 1 else 0
    have hs := h D i j
    simpa [potentialDerivativeCandidate, D, hij, hij.symm] using hs
  · rintro rfl D μ ν
    simp [potentialDerivativeCandidate]

/-- **Field Eqs. 3.9--3.11.**  Expanding the derived force gives
`F^{μν}U_ν = Σ_ν (∂^μA^ν - ∂^νA^μ)U_ν` in the diagonal Minkowski basis.
This consumes the actual differentiable-potential field-strength representation; it does not postulate a
second Faraday tensor. -/
theorem potentialLorentzForceNumerator_apply_eq_derivatives {d : ℕ}
    (A : ElectromagneticPotential d) (x : SpaceTime d) (Ucov : (Fin 1 ⊕ Fin d) → ℝ)
    (μ : Fin 1 ⊕ Fin d) :
    potentialLorentzForceNumerator A x Ucov μ =
      ∑ ν, (η μ μ * SpaceTime.deriv μ A x ν -
        η ν ν * SpaceTime.deriv ν A x μ) * Ucov ν := by
  simp only [potentialLorentzForceNumerator, lorentzForceNum, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro ν _
  rw [ElectromagneticPotential.toFieldStrength_basis_repr_apply_eq_single]

/-- The potential-derived Lorentz force is gauge invariant.  This is the dynamical consequence of the
existing theorem `fieldStrengthMatrix_gaugeTransform`: adding the raised gradient of a `C²` scalar to
`A` changes neither `F = dA` nor `F^{μν}U_ν`. -/
theorem potentialLorentzForceNumerator_gauge_invariant {d : ℕ}
    (A : ElectromagneticPotential d) (χ : SpaceTime d → ℝ)
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ)
    (x : SpaceTime d) (Ucov : (Fin 1 ⊕ Fin d) → ℝ) :
    potentialLorentzForceNumerator (gaugeTransform χ A) x Ucov =
      potentialLorentzForceNumerator A x Ucov := by
  funext μ
  unfold potentialLorentzForceNumerator lorentzForceNum
  rw [fieldStrengthMatrix_gaugeTransform A χ hA hχ x]

/-- **Covariant no-work identity.**  The four-force is orthogonal to the covariant four-velocity:
`U_μ F^{μν} U_ν = 0`.  It follows from the already-proved antisymmetry of `dA` through the
shared Vlasov/Maxwell antisymmetric-generator theorem. -/
theorem potentialLorentzForce_orthogonal {d : ℕ}
    (A : ElectromagneticPotential d) (x : SpaceTime d)
    (Ucov : (Fin 1 ⊕ Fin d) → ℝ) :
    Ucov ⬝ᵥ potentialLorentzForceNumerator A x Ucov = 0 := by
  exact antisym_no_work (fun i j => A.fieldStrengthMatrix x (i, j))
    (fun i j => A.fieldStrengthMatrix_antisymm x i j) Ucov

/-- The force derived from the actual electromagnetic potential feeds the existing BCJ double-copy
carrier, and its diagonal gravity-side square is nonnegative for positive propagator denominator. -/
theorem potentialLorentzForceDual_nonneg {d : ℕ}
    (A : ElectromagneticPotential d) (x : SpaceTime d)
    (Ucov : (Fin 1 ⊕ Fin d) → ℝ) (μ : Fin 1 ⊕ Fin d)
    (D : ℝ) (hD : 0 < D) :
    0 ≤ lorentzForceDual (fun κ ρ => A.fieldStrengthMatrix x (κ, ρ)) Ucov μ D :=
  lorentzForceDual_nonneg _ _ _ D hD

/-- The BCJ numerator in `potentialLorentzForceDual_nonneg` is definitionally the same `dA·U`
numerator expanded in `potentialLorentzForceNumerator_apply_eq_derivatives`. -/
theorem potentialLorentzForceDual_eq {d : ℕ}
    (A : ElectromagneticPotential d) (x : SpaceTime d)
    (Ucov : (Fin 1 ⊕ Fin d) → ℝ) (μ : Fin 1 ⊕ Fin d) (D : ℝ) :
    lorentzForceDual (fun κ ρ => A.fieldStrengthMatrix x (κ, ρ)) Ucov μ D =
      potentialLorentzForceNumerator A x Ucov μ ^ 2 / D := by
  rfl

/-- **Field Eq. 3.3, reused from the repository Lorentz geometry.**  Under an `x`-boost, the electric
component parallel to the boost is invariant, evaluated at the Lorentz-transformed event.  This is the
actual covariance result used by the paper; it is obtained from equivariance of the existing potential
field strength rather than from an independently postulated transformation of `E` and `B`. -/
theorem potentialElectricField_longitudinal_boost {d : ℕ} {c : SpeedOfLight}
    (β : ℝ) (hβ : |β| < 1) (A : ElectromagneticPotential d.succ)
    (hA : Differentiable ℝ A) (t : Time) (x : Space d.succ) :
    let Λ := LorentzGroup.boost (d := d.succ) 0 β hβ
    let t' : Time := LorentzGroup.γ β * (t.val + β / c * x 0)
    let x' : Space d.succ := ⟨fun
      | 0 => LorentzGroup.γ β * (x 0 + c * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩
    electricField c (Λ • A) t x 0 = A.electricField c t' x' 0 :=
  ElectromagneticPotential.electricField_apply_x_boost_zero β hβ A hA t x

/-! ## E. Three-force, induction, and energy -/

/-- **Field Eqs. 3.13--3.14.**  The spatial Lorentz force `q(E + v × B)`. -/
def lorentzThreeForce (q : ℝ) (E v B : Fin 3 → ℝ) : Fin 3 → ℝ :=
  q • (E + v ⨯₃ B)

/-- **Field Eq. 4.5.**  The Lorentz-force power is `q v·E`: the magnetic force performs no work because
`v·(v×B)=0`. -/
theorem lorentzThreeForce_power (q : ℝ) (E v B : Fin 3 → ℝ) :
    v ⬝ᵥ lorentzThreeForce q E v B = q * (v ⬝ᵥ E) := by
  simp [lorentzThreeForce, dotProduct_add, dotProduct_smul]

/-- A purely magnetic Lorentz force is orthogonal to the particle velocity and therefore performs no
work.  This is the spatial specialization of `potentialLorentzForce_orthogonal`. -/
theorem magneticLorentzForce_no_work (q : ℝ) (v B : Fin 3 → ℝ) :
    v ⬝ᵥ lorentzThreeForce q 0 v B = 0 := by
  simp [lorentzThreeForce]

/-- **Field Eq. 4.6.**  Integrating the time component of the Lorentz equation gives the exact
work--energy balance
`energy b - energy a = ∫ q v·E dt`.

The derivative premise is the worldline dynamics.  The theorem then replaces its Lorentz-force power by
the already-proved electric-only power and applies the repository's interval fundamental theorem of
calculus; radiation reaction is outside the paper's conservative-system scope. -/
theorem lorentzThreeForce_work_energy
    (energy : ℝ → ℝ) (q : ℝ) (E v B : ℝ → Fin 3 → ℝ) (a b : ℝ)
    (hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt energy (v t ⬝ᵥ lorentzThreeForce q (E t) (v t) (B t)) t)
    (hint : IntervalIntegrable (fun t => q * (v t ⬝ᵥ E t)) volume a b) :
    ∫ t in a..b, q * (v t ⬝ᵥ E t) = energy b - energy a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    simpa only [lorentzThreeForce_power] using hderiv t ht
  · exact hint

/-- **Pure-magnetic energy conservation (paper §4).**  A Lorentz trajectory with no electric field has
constant relativistic energy between any two endpoints.  The result is stronger than the paper's stated
constant-`B` corollary: no constancy assumption on `B` is needed, only the conservative Lorentz dynamics. -/
theorem pureMagnetic_lorentz_energy_conserved
    (energy : ℝ → ℝ) (q : ℝ) (v B : ℝ → Fin 3 → ℝ) (a b : ℝ)
    (hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt energy (v t ⬝ᵥ lorentzThreeForce q 0 (v t) (B t)) t) :
    energy b = energy a := by
  have hint : IntervalIntegrable
      (fun t => q * (v t ⬝ᵥ (0 : Fin 3 → ℝ))) volume a b := by
    simp
  have h := lorentzThreeForce_work_energy energy q (fun _ => 0) v B a b hderiv
    hint
  have hzero : 0 = energy b - energy a := by
    simpa using h
  linarith

/-- **Field Eq. 3.15.**  The same smooth potential that defines the electric and magnetic fields proves
Faraday--Lenz induction `curl E = -∂ₜB`; no Maxwell dynamical field equation is assumed here. -/
theorem potential_faraday_lenz {ℱ : FreeSpace} (A : ElectromagneticPotential 3)
    (t : Time) (x : Space) (hA : ContDiff ℝ ∞ A) :
    (Space.curl (A.electricField ℱ.c t)) x =
      - Time.deriv (fun s => A.magneticField ℱ.c s x) t := by
  exact _root_.Electromagnetism.ThreeDimension.faradayLaw (V := A) t x hA

/-- The paper's equation-level closure in the repository: the potential derivative supplies the covariant
force component, gauge shifts leave it invariant, the induced fields satisfy Faraday--Lenz, and their
three-force transfers energy only through the electric component. -/
theorem potential_lorentz_force_derivation_closure {ℱ : FreeSpace}
    (A : ElectromagneticPotential 3) (χ : SpaceTime 3 → ℝ)
    (hA : ContDiff ℝ ∞ A) (hχ : ContDiff ℝ 2 χ)
    (x₄ : SpaceTime 3) (Ucov : (Fin 1 ⊕ Fin 3) → ℝ) (μ : Fin 1 ⊕ Fin 3)
    (t : Time) (x : Space) (q : ℝ) (v : Fin 3 → ℝ) :
    potentialLorentzForceNumerator A x₄ Ucov μ =
        ∑ ν, (η μ μ * SpaceTime.deriv μ A x₄ ν -
          η ν ν * SpaceTime.deriv ν A x₄ μ) * Ucov ν ∧
    potentialLorentzForceNumerator (gaugeTransform χ A) x₄ Ucov =
        potentialLorentzForceNumerator A x₄ Ucov ∧
    (Space.curl (A.electricField ℱ.c t)) x =
        - Time.deriv (fun s => A.magneticField ℱ.c s x) t ∧
    v ⬝ᵥ lorentzThreeForce q (A.electricField ℱ.c t x) v
        (A.magneticField ℱ.c t x) = q * (v ⬝ᵥ A.electricField ℱ.c t x) := by
  refine ⟨potentialLorentzForceNumerator_apply_eq_derivatives A x₄ Ucov μ,
    potentialLorentzForceNumerator_gauge_invariant A χ (hA.differentiable (by simp)) hχ x₄ Ucov,
    potential_faraday_lenz A t x hA, ?_⟩
  exact lorentzThreeForce_power q (A.electricField ℱ.c t x) v (A.magneticField ℱ.c t x)

/- ZIL-BEGIN -/

zil attach potentialLorentzForceNumerator_apply_eq_derivatives where
  formalizes @ "claim:lorentz-four-force-is-derived-by-contracting-the-antisymmetric-potential-derivative-with-four-velocity",
  supported_by @ "paper:field-2003-equations-3-4-and-3-9-through-3-11",
  supported_by @ "lean:Electromagnetism.ElectromagneticPotential.toFieldStrength_basis_repr_apply_eq_single",
  caveat @ "claim:equation-level-smooth-potential-derivation-not-a-worldline-existence-theorem"

zil attach potentialDerivativeCandidate_antisymmetric_iff where
  formalizes @ "claim:within-the-two-term-first-derivative-potential-ansatz-antisymmetry-uniquely-fixes-the-relative-coefficient-minus-one",
  supported_by @ "paper:field-2003-equations-3-1-and-3-4",
  epistemic_status @ "exact-mathematical-identity",
  caveat @ "claim:antisymmetry-uniqueness-inside-an-explicit-ansatz-not-the-paper-broader-claim-that-lorentz-covariance-alone-excludes-every-other-operator"

zil attach potentialElectricField_longitudinal_boost where
  formalizes @ "claim:the-electric-component-parallel-to-a-lorentz-boost-is-invariant-at-the-transformed-event",
  supported_by @ "paper:field-2003-equation-3-3",
  supported_by @ "lean:Electromagnetism.ElectromagneticPotential.electricField_apply_x_boost_zero",
  caveat @ "claim:special-relativistic-inertial-boost-law-not-a-general-curved-spacetime-coordinate-transformation"

zil attach potentialLorentzForceNumerator_gauge_invariant where
  formalizes @ "claim:the-potential-derived-lorentz-four-force-is-gauge-invariant",
  supported_by @ "lean:Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_gaugeTransform",
  caveat @ "claim:gauge-invariance-under-c2-raised-gradient-shifts-not-uniqueness-among-all-first-order-force-laws"

zil attach potentialLorentzForce_orthogonal where
  formalizes @ "claim:antisymmetry-of-the-potential-derived-field-strength-makes-the-four-force-orthogonal-to-four-velocity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM.antisym_no_work",
  caveat @ "claim:finite-component-covariant-contraction-not-a-solution-of-the-coupled-maxwell-particle-system"

zil attach potentialLorentzForceDual_nonneg where
  formalizes @ "claim:the-potential-derived-lorentz-force-is-the-gauge-numerator-of-the-existing-nonnegative-bcj-double-copy-channel",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcjDoubleCopy_diagonal_nonneg",
  requires @ "claim:positive-bcj-propagator-denominator",
  caveat @ "claim:nonnegative-diagonal-double-copy-square-not-a-derivation-of-a-nonlinear-gravitational-field-solution"

zil attach lorentzThreeForce_power where
  formalizes @ "claim:lorentz-force-power-is-q-v-dot-e-and-the-magnetic-term-performs-no-work",
  supported_by @ "paper:field-2003-equation-4-5",
  supported_by @ "lean:dot_self_cross",
  caveat @ "claim:pointwise-work-identity-not-a-global-energy-estimate-for-radiating-charges"

zil attach lorentzThreeForce_work_energy where
  formalizes @ "claim:integrating-the-lorentz-force-time-component-gives-energy-change-equals-the-electric-work-integral",
  supported_by @ "paper:field-2003-equations-4-5-and-4-6",
  supported_by @ "lean:intervalIntegral.integral_eq_sub_of_hasDerivAt",
  requires @ "claim:worldline-energy-derivative-equals-lorentz-force-power-and-the-electric-power-is-interval-integrable",
  caveat @ "claim:conservative-prescribed-field-work-energy-balance-without-radiation-reaction-or-coupled-worldline-existence"

zil attach pureMagnetic_lorentz_energy_conserved where
  formalizes @ "claim:a-purely-magnetic-lorentz-trajectory-has-constant-relativistic-energy",
  supported_by @ "paper:field-2003-section-4-corollary-after-equation-4-6",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.lorentzThreeForce_work_energy",
  caveat @ "claim:energy-conservation-on-a-supplied-conservative-lorentz-trajectory-not-a-radiating-charge-theorem"

zil attach potential_faraday_lenz where
  formalizes @ "claim:the-same-electromagnetic-potential-derives-faraday-lenz-induction",
  supported_by @ "paper:field-2003-equation-3-15",
  supported_by @ "lean:Electromagnetism.ThreeDimension.faradayLaw",
  caveat @ "claim:kinematic-bianchi-identity-from-a-smooth-potential-not-the-sourced-maxwell-evolution-system"

zil attach potential_lorentz_force_derivation_closure where
  formalizes @ "claim:one-smooth-gauge-potential-jointly-derives-the-lorentz-force-faraday-lenz-gauge-invariance-and-electric-only-work-law",
  supported_by @ "paper:field-2003-equations-3-4-through-3-16-and-4-5",
  caveat @ "claim:does-not-formalize-the-paper-informal-uniqueness-claim-without-a-specified-admissible-operator-class"

zil_file_contract physlib.lorentzForcePotentialDerivation where
  promises "The equation-level Lorentz-force derivation from a smooth electromagnetic potential: the repository field strength dA contracts with a covariant four-velocity, is invariant under C2 gauge shifts, is orthogonal to the four-velocity, induces Faraday-Lenz, and reduces spatially to q(E+v-cross-B) whose magnetic term performs no work. Inside the paper's explicit two-term first-derivative ansatz, antisymmetry uniquely fixes the minus sign; the existing boost geometry proves longitudinal electric-field invariance; and the pointwise power law integrates to the conservative work-energy equation and pure-magnetic energy conservation. The same numerator remains the input to the existing BCJ gauge/gravity dual and D0-D6 force modules."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Electromagnetism.ElectromagneticPotential.toFieldStrength_basis_repr_apply_eq_single",
    "lean:Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_gaugeTransform",
    "lean:Electromagnetism.ElectromagneticPotential.electricField_apply_x_boost_zero",
    "lean:Electromagnetism.ThreeDimension.faradayLaw",
    "lean:intervalIntegral.integral_eq_sub_of_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM.antisym_no_work"
  ]
  forbids_substitutes [
    "claiming covariance uniqueness without defining and excluding the full alternative operator class",
    "conflating antisymmetry uniqueness inside the two-term derivative ansatz with uniqueness from covariance alone",
    "replacing the repository electromagnetic field strength by an unrelated parallel Faraday tensor",
    "calling the pointwise work identity a global existence or radiation-reaction theorem",
    "claiming the BCJ square alone proves a nonlinear Einstein solution"
  ]
  witnessed_by [
    potentialLorentzForceNumerator_apply_eq_derivatives,
    potentialDerivativeCandidate_antisymmetric_iff,
    potentialElectricField_longitudinal_boost,
    potentialLorentzForceNumerator_gauge_invariant,
    potentialLorentzForce_orthogonal,
    potentialLorentzForceDual_nonneg,
    potentialLorentzForceDual_eq,
    lorentzThreeForce_power,
    magneticLorentzForce_no_work,
    lorentzThreeForce_work_energy,
    pureMagnetic_lorentz_energy_conserved,
    potential_faraday_lenz,
    potential_lorentz_force_derivation_closure
  ]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual

end

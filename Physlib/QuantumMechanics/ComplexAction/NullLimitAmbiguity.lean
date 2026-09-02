/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction
public import Physlib.QuantumMechanics.ComplexAction.HaywardJointRapidity
public import Mathlib.Analysis.Calculus.Deriv.Mul

meta import Zil

/-!
# Ambiguities in the null limit from timelike surfaces (Appendix A)

Appendix A of Lehner, Myers, Poisson & Sorkin (arXiv:1609.00207): can the ambiguous null-boundary term
be fixed by approaching the null hypersurface as a **limit of timelike surfaces**? The answer is **no in
general** — the limit diverges logarithmically — with a single exception: a **stationary** limiting
surface (a Killing horizon), where the limit is finite and reproduces the stationary formula
`S = −2κ𝒜(λ₂ − λ₁)` (Eq. 2.68, `NullBoundaryGravitationalAction.stationaryNullAction`).

* **§A — the static joint boost** (Eq. A8). `η = ½ ln((2−G)/(G−2Ṙ))` is `½` the Hayward vibracy
  `½ HaywardJointRapidity.haywardJointEta (2−G) (G−2Ṙ)` (`staticBoost_eq_haywardJointEta`).
* **§B — the logarithmic divergence** (Eqs. A9–A11). As the surface approaches null (`G − 2Ṙ → 0⁺`,
  i.e. `ε → 0⁺`), the joint term `−cR² ln(kε)` diverges to `+∞` (`nullLimit_logDivergence`) — the null
  limit does not exist for a generic (nonstationary) surface.
* **§C — the stationary exception is finite** (Eqs. A12–A14). For a Killing horizon
  `R(v) = r₀[1 + εb(v)]`, `G = 2εκr₀b`, the divergences cancel and `S = −8πr₀²κ(v₂ − v₁)`, independent
  of the arbitrary `b(v)` — exactly `stationaryNullAction κ (4πr₀²) v₂ v₁`
  (`stationaryNullLimit_eq_stationaryNullAction`).
* **§D — the Kerr horizon** (Eqs. A15–A16). The Kerr surface gravity `κ = (r₊−M)/(r₊²+a²)` equals
  `(r₊²−a²)/(2r₊(r₊²+a²))` on the horizon `r₊²−2Mr₊+a² = 0` (`kerrSurfaceGravity_forms_agree`), and the
  null limit `−2κ𝒜(v₂−v₁)` with `𝒜 = 4π(r₊²+a²)` equals `−4π(r₊²−a²)/r₊·(v₂−v₁)` (Eq. A15)
  (`kerr_nullLimit_eq`) — Eq. 2.68 recovered for a rotating black hole.
* **§E — the charged Kerr thermodynamic family.** The horizon equation is solved by
  `M = (r₊²+a²+Q²)/(2r₊)` and `J = aM`. Their actual directional derivatives, together with the
  derivative of the existing area `kerrHorizonArea`, prove the charged Kerr first law
  `δM = κδA/(8π)+Ω_HδJ+Φ_HδQ` (`kerrNewman_firstLaw`). The same parameterization proves the
  Christodoulou–Ruffini irreducible-mass formula (`christodoulouRuffini_mass_formula`), its
  reversible `δA=0` specialization, and conditional local area growth.

The finite exception is precisely the stationary case in which the null-boundary term was already
unambiguous (`NullBoundaryGravitationalAction.reparamAction_stationary`): nonstationarity is the source
of both the parametrization ambiguity and this limiting divergence.

**Honest layering.** Proven: the boost/vibracy identity, the logarithmic divergence of the null limit
(via `Real.tendsto_log_nhdsGT_zero`), the finite stationary value as an instance of `stationaryNullAction`,
and the Kerr surface-gravity identity and null-limit value. Interpretive: the metric functions `G, Ṙ,
b(v)`, the surface gravity `κ`, and the horizon data `r₊, a, M` are the geometric inputs; the integrals
`∫_𝒯 L√−f d³z` are represented by the closed-form joint values Appendix A computes.
Section E proves differential identities on the explicit nondegenerate horizon-coordinate
Kerr–Newman parameter family;
it does not prove the global no-hair theorem or Hawking's global event-horizon area theorem. Its area
growth result makes positive surface gravity and nonnegative work-subtracted absorbed energy explicit
premises.

## References

* L. Lehner, R. C. Myers, E. Poisson, R. D. Sorkin, "Gravitational action with null boundaries",
  arXiv:1609.00207 [`Lehner:2016vdi`], Appendix A, Eqs. (A1)–(A21). Reuses
  `NullBoundaryGravitationalAction` (`stationaryNullAction`, `reparamAction_stationary`) and
  `HaywardJointRapidity` (`haywardJointEta`).
* J.D. Bekenstein, "Black-hole thermodynamics," Physics Today 33 (1980) 24–31: irreducible mass,
  reversible transformations, and the charged Kerr first law.
* D. Christodoulou and R. Ruffini, Phys. Rev. D 4 (1971) 3552: the charged rotating
  irreducible-mass formula.


-/

set_option autoImplicit false

open Filter

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity

open Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction
open Physlib.QuantumMechanics.ComplexAction.HaywardJointRapidity


/-- **The static-spacetime joint boost** `η = ½ ln((2−G)/(G−2Ṙ))` (Eq. A8), the Hayward boost parameter
of the joint between the timelike surface `r = R(v)` and the spacelike `v = r + const`. -/
noncomputable def staticBoost (G Rdot : ℝ) : ℝ :=
  (1 / 2) * (Real.log (2 - G) - Real.log (G - 2 * Rdot))

/-- **The static boost is half the Hayward vibracy** (Eqs. A8 ↔ 2.91): `η = ½ haywardJointEta(2−G, G−2Ṙ)`,
tying the Appendix-A joint to the main-text boost-rapidity `HaywardJointRapidity.haywardJointEta`. -/
lemma staticBoost_eq_haywardJointEta (G Rdot : ℝ) :
    staticBoost G Rdot = (1 / 2) * haywardJointEta (2 - G) (G - 2 * Rdot) := by
  simp only [staticBoost, haywardJointEta]


/-- **The null limit diverges logarithmically** (Eqs. A10–A11): as a nonstationary timelike surface
approaches null (`ε → 0⁺`), the joint term `−cR² ln(kε)` tends to `+∞`. With `c, k > 0`, the boundary
action has no finite null limit — the logarithmic divergence Appendix A exhibits. -/
lemma nullLimit_logDivergence (c k : ℝ) (hc : 0 < c) (hk : 0 < k) :
    Tendsto (fun ε : ℝ => -c * Real.log (k * ε)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hlogε : Tendsto Real.log (nhdsWithin 0 (Set.Ioi 0)) atBot := Real.tendsto_log_nhdsGT_zero
  have hsum : Tendsto (fun ε : ℝ => Real.log k + Real.log ε)
      (nhdsWithin 0 (Set.Ioi 0)) atBot :=
    tendsto_atBot_add_const_left _ (Real.log k) hlogε
  have heq : (fun ε : ℝ => Real.log k + Real.log ε)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun ε => Real.log (k * ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.log_mul (ne_of_gt hk) (ne_of_gt hε)]
  exact (hsum.congr' heq).const_mul_atBot_of_neg (by linarith)


/-- **The stationary null limit** `S = −8πr₀²κ(v₂ − v₁)` (Eq. A14): for a Killing horizon
`R(v) = r₀[1 + εb(v)]`, the logarithmic divergences cancel and the limit is finite and **independent of
the arbitrary function `b(v)`** (the absence of any `b` argument is that independence). -/
noncomputable def stationaryNullLimit (r0 κ v2 v1 : ℝ) : ℝ := -8 * Real.pi * r0 ^ 2 * κ * (v2 - v1)

/-- **The stationary null limit is the stationary null action** (Eqs. A14 ↔ 2.68): with horizon area
`𝒜 = 4πr₀²`, `−8πr₀²κ(v₂−v₁) = −2κ𝒜(v₂−v₁) = stationaryNullAction κ (4πr₀²) v₂ v₁`. The Appendix-A
limit reproduces the main-text stationary formula. -/
lemma stationaryNullLimit_eq_stationaryNullAction (r0 κ v2 v1 : ℝ) :
    stationaryNullLimit r0 κ v2 v1 = stationaryNullAction κ (4 * Real.pi * r0 ^ 2) v2 v1 := by
  unfold stationaryNullLimit stationaryNullAction; ring


/-- **The Kerr surface gravity** `κ = (r₊²−a²)/(2r₊(r₊²+a²))` (Eq. A16). -/
noncomputable def kerrSurfaceGravity (rp a : ℝ) : ℝ := (rp ^ 2 - a ^ 2) / (2 * rp * (rp ^ 2 + a ^ 2))

/-- **The Kerr horizon area** `𝒜 = 4π(r₊²+a²)` (Eq. A16). -/
noncomputable def kerrHorizonArea (rp a : ℝ) : ℝ := 4 * Real.pi * (rp ^ 2 + a ^ 2)

/-- **The two forms of the Kerr surface gravity agree** (Eq. A16): on the outer horizon
`r₊² − 2Mr₊ + a² = 0`, the mass form `κ = (r₊−M)/(r₊²+a²)` equals the geometric form
`(r₊²−a²)/(2r₊(r₊²+a²))`. -/
lemma kerrSurfaceGravity_forms_agree (rp M a : ℝ) (hrp : rp ≠ 0) (hden : rp ^ 2 + a ^ 2 ≠ 0)
    (hHor : rp ^ 2 - 2 * M * rp + a ^ 2 = 0) :
    (rp - M) / (rp ^ 2 + a ^ 2) = kerrSurfaceGravity rp a := by
  unfold kerrSurfaceGravity
  have hden2 : 2 * rp * (rp ^ 2 + a ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hrp) hden
  rw [div_eq_div_iff hden hden2]
  linear_combination (rp ^ 2 + a ^ 2) * hHor

/-- **The Kerr null limit is the stationary null action** (Eqs. A15 ↔ 2.68): with the Kerr surface
gravity and horizon area, `−2κ𝒜(v₂−v₁) = −4π(r₊²−a²)/r₊·(v₂−v₁)` (Eq. A15) — the stationary formula of
Eq. 2.68 recovered for a rotating black hole. -/
lemma kerr_nullLimit_eq (rp a v2 v1 : ℝ) (hrp : rp ≠ 0) (hden : rp ^ 2 + a ^ 2 ≠ 0) :
    stationaryNullAction (kerrSurfaceGravity rp a) (kerrHorizonArea rp a) v2 v1
      = -4 * Real.pi * (rp ^ 2 - a ^ 2) / rp * (v2 - v1) := by
  unfold stationaryNullAction kerrSurfaceGravity kerrHorizonArea
  field_simp [hrp, hden]

/-! ## E. Charged Kerr irreducible mass and the genuine first-law variation -/

/-- The Kerr–Newman mass obtained by solving the charged horizon equation
`r₊² - 2Mr₊ + a² + Q² = 0` for `M`. This parameterizes the black-hole family by its
outer horizon radius, specific angular momentum, and electric charge. -/
noncomputable def kerrNewmanMass (rp a Q : ℝ) : ℝ :=
  (rp ^ 2 + a ^ 2 + Q ^ 2) / (2 * rp)

/-- The physical angular momentum `J = aM` on the Kerr–Newman family. -/
noncomputable def kerrNewmanAngularMomentum (rp a Q : ℝ) : ℝ :=
  a * kerrNewmanMass rp a Q

/-- The Christodoulou–Ruffini irreducible mass
`M_irr = √(r₊²+a²)/2` in geometric units. By the existing
`kerrHorizonArea`, this is equivalent to `A = 16πM_irr²`. -/
noncomputable def kerrNewmanIrreducibleMass (rp a : ℝ) : ℝ :=
  Real.sqrt (rp ^ 2 + a ^ 2) / 2

/-- Kerr–Newman surface gravity
`κ = (r₊²-a²-Q²)/(2r₊(r₊²+a²))`. -/
noncomputable def kerrNewmanSurfaceGravity (rp a Q : ℝ) : ℝ :=
  (rp ^ 2 - a ^ 2 - Q ^ 2) / (2 * rp * (rp ^ 2 + a ^ 2))

/-- Horizon angular velocity `Ω_H = a/(r₊²+a²)`. -/
noncomputable def kerrNewmanAngularVelocity (rp a : ℝ) : ℝ :=
  a / (rp ^ 2 + a ^ 2)

/-- Horizon electric potential `Φ_H = Qr₊/(r₊²+a²)`. -/
noncomputable def kerrNewmanElectricPotential (rp a Q : ℝ) : ℝ :=
  Q * rp / (rp ^ 2 + a ^ 2)

/-- The directional mass variation obtained by differentiating `kerrNewmanMass`
along `(r₊,a,Q)+t(δr₊,δa,δQ)`. -/
noncomputable def kerrNewmanMassVariation
    (rp a Q drp da dQ : ℝ) : ℝ :=
  (rp ^ 2 - a ^ 2 - Q ^ 2) / (2 * rp ^ 2) * drp +
    a / rp * da + Q / rp * dQ

/-- The directional angular-momentum variation derived from `J = aM`. -/
noncomputable def kerrNewmanAngularMomentumVariation
    (rp a Q drp da dQ : ℝ) : ℝ :=
  da * kerrNewmanMass rp a Q +
    a * kerrNewmanMassVariation rp a Q drp da dQ

/-- The directional variation of the existing horizon area
`kerrHorizonArea rp a = 4π(rp²+a²)`. -/
noncomputable def kerrNewmanAreaVariation (rp a drp da : ℝ) : ℝ :=
  8 * Real.pi * (rp * drp + a * da)

/-- Shared affine derivative used to compute the three Kerr–Newman variations. -/
private lemma kerrNewmanAffine_hasDerivAt (x dx : ℝ) :
    HasDerivAt (fun t : ℝ => x + t * dx) dx 0 := by
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id 0).mul_const dx).const_add x

/-- **The displayed Kerr–Newman mass variation is an actual derivative.**
It is not a freely supplied `δM`: differentiating the horizon-solved mass along an arbitrary
direction in `(r₊,a,Q)` gives exactly `kerrNewmanMassVariation`. -/
theorem kerrNewmanMass_hasDerivAt (rp a Q drp da dQ : ℝ) (hrp : rp ≠ 0) :
    HasDerivAt
      (fun t : ℝ =>
        kerrNewmanMass (rp + t * drp) (a + t * da) (Q + t * dQ))
      (kerrNewmanMassVariation rp a Q drp da dQ) 0 := by
  have hnum :=
    (((kerrNewmanAffine_hasDerivAt rp drp).pow 2).add
      ((kerrNewmanAffine_hasDerivAt a da).pow 2)).add
        ((kerrNewmanAffine_hasDerivAt Q dQ).pow 2)
  have hden := (kerrNewmanAffine_hasDerivAt rp drp).const_mul 2
  have h := hnum.div hden (by simpa using mul_ne_zero two_ne_zero hrp)
  rw [show (fun t : ℝ =>
      kerrNewmanMass (rp + t * drp) (a + t * da) (Q + t * dQ)) =
      ((fun t => rp + t * drp) ^ 2 + (fun t => a + t * da) ^ 2 +
        (fun t => Q + t * dQ) ^ 2) / (fun t => 2 * (rp + t * drp)) by
      funext t
      rfl]
  apply h.congr_deriv
  simp only [kerrNewmanMassVariation, zero_mul, add_zero, Pi.add_apply, Pi.pow_apply]
  field_simp
  ring

/-- **The displayed `δJ` is the actual derivative of `J = aM`.** -/
theorem kerrNewmanAngularMomentum_hasDerivAt
    (rp a Q drp da dQ : ℝ) (hrp : rp ≠ 0) :
    HasDerivAt
      (fun t : ℝ =>
        kerrNewmanAngularMomentum (rp + t * drp) (a + t * da) (Q + t * dQ))
      (kerrNewmanAngularMomentumVariation rp a Q drp da dQ) 0 := by
  have h := (kerrNewmanAffine_hasDerivAt a da).mul
    (kerrNewmanMass_hasDerivAt rp a Q drp da dQ hrp)
  rw [show (fun t : ℝ =>
      kerrNewmanAngularMomentum (rp + t * drp) (a + t * da) (Q + t * dQ)) =
      (fun t => a + t * da) *
        (fun t => kerrNewmanMass (rp + t * drp) (a + t * da) (Q + t * dQ)) by
      funext t
      rfl]
  apply h.congr_deriv
  simp [kerrNewmanAngularMomentumVariation]

/-- **The displayed `δA` is the actual derivative of the existing Kerr horizon area.**
Charge changes the horizon equation but not the cross-section formula
`A = 4π(r₊²+a²)`. -/
theorem kerrHorizonArea_hasDerivAt
    (rp a drp da : ℝ) :
    HasDerivAt
      (fun t : ℝ => kerrHorizonArea (rp + t * drp) (a + t * da))
      (kerrNewmanAreaVariation rp a drp da) 0 := by
  have h := (((kerrNewmanAffine_hasDerivAt rp drp).pow 2).add
    ((kerrNewmanAffine_hasDerivAt a da).pow 2)).const_mul (4 * Real.pi)
  rw [show (fun t : ℝ => kerrHorizonArea (rp + t * drp) (a + t * da)) =
      fun t => 4 * Real.pi * ((rp + t * drp) ^ 2 + (a + t * da) ^ 2) by
      funext t
      rfl]
  apply h.congr_deriv
  simp [kerrNewmanAreaVariation]
  ring

/-- The charged surface gravity reduces definitionally to the existing Kerr surface gravity
when `Q = 0`, so the new thermodynamic layer reuses rather than replaces the §D carrier. -/
lemma kerrNewmanSurfaceGravity_zero_charge (rp a : ℝ) :
    kerrNewmanSurfaceGravity rp a 0 = kerrSurfaceGravity rp a := by
  unfold kerrNewmanSurfaceGravity kerrSurfaceGravity
  ring

/-- The irreducible mass obeys `M_irr² = (r₊²+a²)/4`, hence the existing area is
`A = 16πM_irr²`. -/
lemma kerrNewmanIrreducibleMass_sq (rp a : ℝ) :
    kerrNewmanIrreducibleMass rp a ^ 2 = (rp ^ 2 + a ^ 2) / 4 := by
  unfold kerrNewmanIrreducibleMass
  rw [div_pow, Real.sq_sqrt (by positivity)]
  ring

/-- **Horizon area equals sixteen pi times the irreducible mass squared.**
This identifies the §D geometric area carrier with the Christodoulou–Ruffini thermodynamic
carrier, without introducing a second area definition. -/
lemma kerrHorizonArea_eq_irreducibleMass (rp a : ℝ) :
    kerrHorizonArea rp a =
      16 * Real.pi * kerrNewmanIrreducibleMass rp a ^ 2 := by
  rw [kerrNewmanIrreducibleMass_sq]
  unfold kerrHorizonArea
  ring

/-- **[Christodoulou–Ruffini irreducible-mass formula].**
On the horizon-parameterized Kerr–Newman family,
`M² = M_irr² + Q²/2 + (Q⁴+4J²)/(16M_irr²)`.
This is the quantitative separation between extractable rotational/electromagnetic energy
and the irreducible horizon mass used by Bekenstein's reversible-process discussion. -/
theorem christodoulouRuffini_mass_formula (rp a Q : ℝ)
    (hrp : rp ≠ 0) (harea : rp ^ 2 + a ^ 2 ≠ 0) :
    kerrNewmanMass rp a Q ^ 2 =
      kerrNewmanIrreducibleMass rp a ^ 2 + Q ^ 2 / 2 +
        (Q ^ 4 + 4 * kerrNewmanAngularMomentum rp a Q ^ 2) /
          (16 * kerrNewmanIrreducibleMass rp a ^ 2) := by
  rw [kerrNewmanIrreducibleMass_sq]
  unfold kerrNewmanAngularMomentum kerrNewmanMass
  field_simp
  ring

/-- **[Bekenstein 1980: charged Kerr first law].**
For every direction in the explicit Kerr–Newman family, the independently computed derivatives
of `M`, the existing area `A`, and `J` obey
`δM = κ δA/(8π) + Ω_H δJ + Φ_H δQ` in geometric units.
Unlike a proposition carrying the first law as a field, this theorem derives it from the
horizon-solved mass and the three derivative theorems above. -/
theorem kerrNewman_firstLaw (rp a Q drp da dQ : ℝ)
    (hrp : rp ≠ 0) (harea : rp ^ 2 + a ^ 2 ≠ 0) :
    kerrNewmanMassVariation rp a Q drp da dQ =
      kerrNewmanSurfaceGravity rp a Q / (8 * Real.pi) *
          kerrNewmanAreaVariation rp a drp da +
        kerrNewmanAngularVelocity rp a *
          kerrNewmanAngularMomentumVariation rp a Q drp da dQ +
        kerrNewmanElectricPotential rp a Q * dQ := by
  unfold kerrNewmanAngularMomentumVariation kerrNewmanMassVariation
    kerrNewmanSurfaceGravity kerrNewmanAreaVariation kerrNewmanAngularVelocity
    kerrNewmanElectricPotential kerrNewmanMass
  field_simp [Real.pi_ne_zero]
  ring

/-- **The charged Kerr thermodynamic variation, assembled.**
The Christodoulou–Ruffini mass relation, actual derivatives of `M`, `J`, and the reused
horizon area, and the charged first law all hold on one explicit parameter family. This
is the kernel-checked thermodynamic backbone of Bekenstein's charged-Kerr discussion. -/
theorem kerrNewman_thermodynamic_variation
    (rp a Q drp da dQ : ℝ) (hrp : rp ≠ 0) (harea : rp ^ 2 + a ^ 2 ≠ 0) :
    kerrNewmanMass rp a Q ^ 2 =
        kerrNewmanIrreducibleMass rp a ^ 2 + Q ^ 2 / 2 +
          (Q ^ 4 + 4 * kerrNewmanAngularMomentum rp a Q ^ 2) /
            (16 * kerrNewmanIrreducibleMass rp a ^ 2)
      ∧ HasDerivAt
          (fun t : ℝ =>
            kerrNewmanMass (rp + t * drp) (a + t * da) (Q + t * dQ))
          (kerrNewmanMassVariation rp a Q drp da dQ) 0
      ∧ HasDerivAt
          (fun t : ℝ =>
            kerrNewmanAngularMomentum (rp + t * drp) (a + t * da) (Q + t * dQ))
          (kerrNewmanAngularMomentumVariation rp a Q drp da dQ) 0
      ∧ HasDerivAt
          (fun t : ℝ => kerrHorizonArea (rp + t * drp) (a + t * da))
          (kerrNewmanAreaVariation rp a drp da) 0
      ∧ kerrNewmanMassVariation rp a Q drp da dQ =
          kerrNewmanSurfaceGravity rp a Q / (8 * Real.pi) *
              kerrNewmanAreaVariation rp a drp da +
            kerrNewmanAngularVelocity rp a *
              kerrNewmanAngularMomentumVariation rp a Q drp da dQ +
            kerrNewmanElectricPotential rp a Q * dQ := by
  exact ⟨christodoulouRuffini_mass_formula rp a Q hrp harea,
    kerrNewmanMass_hasDerivAt rp a Q drp da dQ hrp,
    kerrNewmanAngularMomentum_hasDerivAt rp a Q drp da dQ hrp,
    kerrHorizonArea_hasDerivAt rp a drp da,
    kerrNewman_firstLaw rp a Q drp da dQ hrp harea⟩

/-- **[Reversible black-hole transformation].**
When the irreducible mass/area is unchanged (`δA = 0`), the charged Kerr first law reduces to
`δM = Ω_HδJ + Φ_HδQ`: only rotational and electromagnetic work is exchanged. -/
theorem kerrNewman_reversible_firstLaw (rp a Q drp da dQ : ℝ)
    (hrp : rp ≠ 0) (harea : rp ^ 2 + a ^ 2 ≠ 0)
    (hreversible : kerrNewmanAreaVariation rp a drp da = 0) :
    kerrNewmanMassVariation rp a Q drp da dQ =
      kerrNewmanAngularVelocity rp a *
          kerrNewmanAngularMomentumVariation rp a Q drp da dQ +
        kerrNewmanElectricPotential rp a Q * dQ := by
  rw [kerrNewman_firstLaw rp a Q drp da dQ hrp harea, hreversible]
  ring

/-- **[Local area-growth consequence].**
For positive surface gravity, nonnegative absorbed energy after subtracting rotational and
electromagnetic work forces `δA ≥ 0`. This is the local first-law implication used by the
thermodynamic argument; it deliberately does not claim Hawking's global causal area theorem. -/
theorem kerrNewmanAreaVariation_nonneg_of_absorbedEnergy_nonneg
    (rp a Q drp da dQ : ℝ) (hrp : rp ≠ 0) (harea : rp ^ 2 + a ^ 2 ≠ 0)
    (hkappa : 0 < kerrNewmanSurfaceGravity rp a Q)
    (hflux : 0 ≤ kerrNewmanMassVariation rp a Q drp da dQ -
      kerrNewmanAngularVelocity rp a *
        kerrNewmanAngularMomentumVariation rp a Q drp da dQ -
      kerrNewmanElectricPotential rp a Q * dQ) :
    0 ≤ kerrNewmanAreaVariation rp a drp da := by
  have hfirst := kerrNewman_firstLaw rp a Q drp da dQ hrp harea
  have hcoeff : 0 < kerrNewmanSurfaceGravity rp a Q / (8 * Real.pi) := by
    positivity
  nlinarith

end Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanMass_hasDerivAt where
  formalizes @ "claim:kerr-newman-horizon-solved-mass-has-explicit-directional-variation",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  caveat @ "claim:the-kerr-newman-horizon-parameter-family-is-the-classical-model-input"

zil attach Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrHorizonArea_hasDerivAt where
  formalizes @ "claim:kerr-newman-horizon-area-has-explicit-directional-variation",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  caveat @ "claim:the-horizon-cross-section-formula-is-reused-not-derived-from-the-einstein-maxwell-equations-here"

zil attach Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.christodoulouRuffini_mass_formula where
  formalizes @ "claim:christodoulou-ruffini-charged-rotating-irreducible-mass-formula",
  supported_by @ "paper:christodoulou-ruffini-1971",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-on-the-explicit-kerr-newman-family-not-a-no-hair-uniqueness-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewman_firstLaw where
  formalizes @ "claim:bekenstein-1980-charged-kerr-first-law-is-derived-from-family-variations",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:kerr-newman-horizon-solved-mass-has-explicit-directional-variation",
  requires @ "claim:kerr-newman-horizon-area-has-explicit-directional-variation",
  epistemic_status @ "conditional-model",
  caveat @ "claim:geometric-units-exact-family-identity-not-a-global-black-hole-evolution-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewman_thermodynamic_variation where
  formalizes @ "claim:bekenstein-1980-charged-kerr-irreducible-mass-and-first-law-capstone",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  supported_by @ "paper:christodoulou-ruffini-1971",
  requires @ "claim:christodoulou-ruffini-charged-rotating-irreducible-mass-formula",
  requires @ "claim:bekenstein-1980-charged-kerr-first-law-is-derived-from-family-variations",
  epistemic_status @ "conditional-model",
  caveat @ "claim:bundles-actual-parameter-derivatives-but-does-not-prove-no-hair-or-global-area-monotonicity"

zil attach Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewman_reversible_firstLaw where
  formalizes @ "claim:bekenstein-1980-reversible-black-hole-transformations-have-zero-area-variation",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:bekenstein-1980-charged-kerr-first-law-is-derived-from-family-variations",
  epistemic_status @ "conditional-model",
  caveat @ "claim:reversibility-is-the-explicit-zero-area-variation-premise"

zil attach Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanAreaVariation_nonneg_of_absorbedEnergy_nonneg where
  formalizes @ "claim:positive-kappa-and-nonnegative-work-subtracted-flux-imply-local-kerr-newman-area-growth",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:bekenstein-1980-charged-kerr-first-law-is-derived-from-family-variations",
  epistemic_status @ "conditional-model",
  caveat @ "claim:local-first-law-consequence-not-hawkings-global-causal-area-theorem"

zil_file_contract physlib.nullLimitAmbiguity where
  promises "The generic logarithmic divergence and stationary exception in the timelike-to-null limit; the Kerr stationary null-action formula; and the Kerr-Newman thermodynamic extension deriving the Christodoulou-Ruffini irreducible-mass formula, actual mass/angular-momentum/area variations, the charged first law, its reversible specialization, and conditional local area growth."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:NullBoundaryGravitationalAction.stationaryNullAction",
    "lean:Real.sqrt", "lean:HasDerivAt"]
  forbids_substitutes ["a no-hair uniqueness theorem",
    "Hawking's global event-horizon area theorem",
    "derivation of the Kerr-Newman family from the Einstein-Maxwell equations"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.nullLimit_logDivergence,
    Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerr_nullLimit_eq,
    Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.christodoulouRuffini_mass_formula,
    Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewman_thermodynamic_variation,
    Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewman_reversible_firstLaw,
    Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanAreaVariation_nonneg_of_absorbedEnergy_nonneg]

/- ZIL-END -/

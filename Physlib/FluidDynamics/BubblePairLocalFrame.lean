/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation
public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus
public import Physlib.Units.GravitationalCouplingDimensions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The bubble-pair local force frame — inclination as a `U(1)` interaction frame, exchange as a braiding phase

Zhang–Liao–Yan–Wu–Qiu–Huang–Liu (*Hydrodynamic Mechanisms of Deformable Bubble Pair Interactions at
Varying Weber and Reynolds Numbers*) study two bubbles held in an incoming flow — governed by the
incompressible Navier–Stokes system, their Eqs. (1)–(2), the `FluidDynamics.ClassicalContinuityEquation`
and `FluidDynamics.MomentumEquation` of `Physlib.FluidDynamics.NavierStokes` — and decompose the
hydrodynamic force on each bubble into a **local frame** set by the pair's inclination angle `θ`
(their Eqs. (6)–(7)):

  `F_i = F_D cos θ + F_L sin θ`  (centerline component: `F_i > 0` = attraction),
  `F_j = F_D sin θ − F_L cos θ`  (transverse component: alignment torque).

This module formalizes the exact mathematics of that decomposition and welds it into three arcs of the
library.

* **§A — the local frame is a `U(1)` interaction frame.** Packaging the drag–lift pair as the complex
  force `F_D − i·F_L`, the local-frame components are its rotation by the frame phase:
  `framedForce = interactionFrame 1 1 θ · (F_D − i F_L)` with
  `ConfigurationSpaceDiracFluctuation.interactionFrame` — the *same* frame `U(t) = e^{iH₀t/ℏ}` of the
  Dirac interaction picture, at `H₀ = 1, ℏ = 1`, with the inclination angle in the time slot
  (`interactionFrame_unit`, `framedForce_eq_localFrame`). The pair `(F_i, F_j)` obeys the frame's
  rotation equation `dF_i/dθ = −F_j`, `dF_j/dθ = F_i` (`localFrameAttraction_hasDerivAt`,
  `localFrameTorque_hasDerivAt`) and the frame is an isometry `F_i² + F_j² = F_D² + F_L²`
  (`localFrame_isometry`) — the abelian shadow of `interactionFrame_mul_inv`. At the interval
  endpoints the interaction reduces to pure channels: tandem `θ = 0` reads the drag difference,
  side-by-side `θ = π/2` reads the lift (`localFrame_tandem`, `localFrame_sideBySide`) — the two
  regimes of the paper's drag-reversal/attraction dichotomy.

* **§B — the critical inclination angle.** The paper identifies a critical angle `θ* ∈ [30°, 45°]`
  where the alignment torque reverses. Exactly: `F_j(θ) = √(F_D² + F_L²) · sin(θ − θ*)` with
  `θ* = arctan(F_L/F_D)` (`localFrameTorque_eq_sin_shift`) — the torque vanishes at `θ*`
  (`criticalAngle_torque_zero`), its sign is the sign of `sin(θ − θ*)`
  (`localFrameTorque_pos_iff`), and the observed window is an exact statement about the
  lift-to-drag ratio: `θ* ∈ [π/6, π/4] ⟺ F_L/F_D ∈ [√3/3, 1]` (`criticalAngle_window`).

* **§C — exchange is the fermionic ribbon twist; the trefoil word.** Exchanging the two bubbles is
  the half-turn `θ ↦ θ + π` of the centerline; on the framed force it acts by the **fermionic ribbon
  twist**: `framedForce (θ + π) = ribbonTwist (1/2) · framedForce θ`
  (`framedForce_exchange`, with `Hopf.ChargeConjugationRibbonTwist.ribbonTwist_fermion : … = −1`),
  while the full rotation `θ ↦ θ + 2π` is bosonic/trivial (`framedForce_full_rotation`). Three
  half-turns are the **trefoil braid word** `σ₁³` — the closure of which is the electron knot of
  `ChernSimons.TrefoilFermionChernSimonsInvariant.electronJones` — and on the frame they act by
  `halfTwist r r` at `r = ribbonTwist (1/2)`, again the fermionic sign
  (`framedForce_trefoil`, `trefoilWord_ribbon_fermion`); the `B₃` full twist `Δ²` — the centre that
  Witten's framing counts — acts trivially (`fullTwist_ribbon_trivial`). This is the
  `U(1)`-abelianized braid representation `σ₁ ↦ e^{iπ}`: the paper's tandem/side-by-side pair
  drags a **double-threaded wake** (Kusuno–Sanada, cited there as the wake-repulsion mechanism) —
  physically a two-strand braid behind the pair.

* **§D — the Weber–Reynolds control plane.** The paper's phase diagram is scanned by `(Re, We, θ)`.
  Formalized: `weberNumber`, `reynoldsNumber`, `capillaryNumber`, `mortonNumber`, `froudeSquared`
  with the exact identities `We = Ca·Re` (`weber_eq_capillary_mul_reynolds`) and
  `We³ = Mo·Fr²·Re⁴` (`weber_cubed_eq_morton_froude_reynolds`) — at fixed fluid (fixed Morton
  number) the `(Re, We)` plane is scanned by speed and diameter alone. Dimensional grounding in the
  `Dimension LTMCTIDimensionBase` group: `[ρU²D] = [σ]`, `[ρUD] = [μ]`, and the drag coefficient of their Eq. (5) is
  dimensionless (`weber_dimensionless`, `reynolds_dimensionless`, `dragCoefficient_dimensionless`).

**Honest layering.** Proven here: the exact kinematics of the local-frame decomposition (rotation
ODE, isometry, endpoint channels, the sine-shift form of the torque and the critical-angle window as
an iff about `F_L/F_D`), the exchange/trefoil phases on the frame, and the dimensionless-group
algebra. The paper's *dynamical* content — which `(Re, We)` regions are attractive, where drag
reversal happens, that `θ*` lands in `[30°, 45°]` — is simulation data, represented here only through
the exact equivalences it instantiates (e.g. the window ⟺ `F_L/F_D ∈ [√3/3, 1]`). The braiding weld
is a structural correspondence on the abelianized braid representation carried by the pair's
half-turn — the statement is about the frame phase, not that bubbles are fermions; the double-threaded
wake is the physical two-strand braid carrier.

## References

* H. Zhang, Y. Liao, H. Yan, D. Wu, Y. Qiu, Y. Huang, L. Liu, *Hydrodynamic Mechanisms of Deformable
  Bubble Pair Interactions at Varying Weber and Reynolds Numbers* (front-tracking + PID; Eqs. (1)–(7)).
* N. Kusuno, T. Sanada — double-threaded wakes behind bubble pairs (cited there).
* E. Witten, *QFT and the Jones Polynomial* — framing/full twist; `Physlib`
  (`ChernSimons.TrefoilFermionChernSimonsInvariant`, `ChernSimons.BraidRelationTrefoilTorus`,
  `Hopf.ChargeConjugationRibbonTwist`, `ChernSimons.WilsonLoopBraidingRibbon`).
* P. A. M. Dirac, *Quantum Electrodynamics without Dead Wood*, Phys. Rev. 139 (1965) B684 — the
  interaction frame `e^{iH₀t/ℏ}`; `Physlib`
  (`AlgebraicQFT.ConfigurationSpaceDiracFluctuation.interactionFrame`).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace FluidDynamics.BubblePairLocalFrame

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus
open Physlib.Units.GravitationalCouplingDimensions
open Physlib.Units.InformationDimensionCollision
open Dimension.LTMCTI


/-! ## §A — the local force frame (paper Eqs. (6)–(7)) -/

/-- **The centerline (attraction) component** `F_i = F_D cos θ + F_L sin θ` of the paper's Eq. (7):
positive values mean the pair attracts along the line of centers. -/
def localFrameAttraction (FD FL θ : ℝ) : ℝ := FD * Real.cos θ + FL * Real.sin θ

/-- **The transverse (alignment-torque) component** `F_j = F_D sin θ − F_L cos θ` of the paper's
Eq. (7): positive values rotate the pair toward side-by-side (horizontal) alignment, negative toward
tandem (vertical) alignment. -/
def localFrameTorque (FD FL θ : ℝ) : ℝ := FD * Real.sin θ - FL * Real.cos θ

/-- **[The frame is an isometry]** `F_i² + F_j² = F_D² + F_L²` — the local-frame decomposition is a
rotation of the drag–lift pair, so the force magnitude is frame-invariant (the abelian shadow of the
interaction frame's unitarity `interactionFrame_mul_inv`). -/
lemma localFrame_isometry (FD FL θ : ℝ) :
    localFrameAttraction FD FL θ ^ 2 + localFrameTorque FD FL θ ^ 2 = FD ^ 2 + FL ^ 2 := by
  unfold localFrameAttraction localFrameTorque
  linear_combination (FD ^ 2 + FL ^ 2) * Real.sin_sq_add_cos_sq θ

/-- **[Tandem endpoint `θ = 0`]** `F_i = F_D`, `F_j = −F_L`: in tandem alignment the attraction is
pure drag difference (the channel of the paper's drag-reversal dichotomy) and the torque is pure
lift. -/
lemma localFrame_tandem (FD FL : ℝ) :
    localFrameAttraction FD FL 0 = FD ∧ localFrameTorque FD FL 0 = -FL := by
  constructor <;> simp [localFrameAttraction, localFrameTorque]

/-- **[Side-by-side endpoint `θ = π/2`]** `F_i = F_L`, `F_j = F_D`: in side-by-side alignment the
attraction is pure lift and the torque is pure drag difference. -/
lemma localFrame_sideBySide (FD FL : ℝ) :
    localFrameAttraction FD FL (Real.pi / 2) = FL
      ∧ localFrameTorque FD FL (Real.pi / 2) = FD := by
  constructor <;> simp [localFrameAttraction, localFrameTorque]

/-- **[The rotation equation, attraction component]** `dF_i/dθ = −F_j` — the local-frame pair obeys
the interaction-frame generator equation (the `SO(2)` case of `interactionPicture_hasDerivAt`). -/
lemma localFrameAttraction_hasDerivAt (FD FL θ : ℝ) :
    HasDerivAt (localFrameAttraction FD FL) (-(localFrameTorque FD FL θ)) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul FD).add ((Real.hasDerivAt_sin θ).const_mul FL)
  have hd : -(localFrameTorque FD FL θ) = FD * -Real.sin θ + FL * Real.cos θ := by
    unfold localFrameTorque; ring
  rw [hd]
  exact h

/-- **[The rotation equation, torque component]** `dF_j/dθ = F_i` — the derivative of the alignment
torque with respect to inclination *is* the attraction component. In particular the torque is
increasing exactly where the pair attracts. -/
lemma localFrameTorque_hasDerivAt (FD FL θ : ℝ) :
    HasDerivAt (localFrameTorque FD FL) (localFrameAttraction FD FL θ) θ := by
  have h := ((Real.hasDerivAt_sin θ).const_mul FD).sub ((Real.hasDerivAt_cos θ).const_mul FL)
  have hd : localFrameAttraction FD FL θ = FD * Real.cos θ - FL * -Real.sin θ := by
    unfold localFrameAttraction; ring
  rw [hd]
  exact h


/-! ## §B — the critical inclination angle (paper §III: `θ* ∈ [30°, 45°]`) -/

/-- **The critical inclination angle** `θ* = arctan(F_L/F_D)` — the angle at which the alignment
torque reverses sign. -/
def criticalAngle (FD FL : ℝ) : ℝ := Real.arctan (FL / FD)

/-- **[The torque is a shifted sine]** `F_j(θ) = √(F_D² + F_L²) · sin(θ − θ*)` — the paper's whole
rotational dichotomy in one identity: the alignment torque vanishes exactly at the critical angle,
is negative (tandem-promoting) below it and positive (side-by-side-promoting) above it, with
amplitude the frame-invariant force magnitude. -/
lemma localFrameTorque_eq_sin_shift (FD FL : ℝ) (hFD : 0 < FD) (θ : ℝ) :
    localFrameTorque FD FL θ
      = Real.sqrt (FD ^ 2 + FL ^ 2) * Real.sin (θ - criticalAngle FD FL) := by
  have hsq : Real.sqrt (FD ^ 2 + FL ^ 2) = FD * Real.sqrt (1 + (FL / FD) ^ 2) := by
    rw [show FD ^ 2 + FL ^ 2 = FD ^ 2 * (1 + (FL / FD) ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg FD), Real.sqrt_sq hFD.le]
  have hpos : (0 : ℝ) < Real.sqrt (1 + (FL / FD) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [Real.sin_sub, criticalAngle, Real.sin_arctan, Real.cos_arctan, hsq]
  unfold localFrameTorque
  field_simp

/-- **[The torque vanishes at the critical angle]** `F_j(θ*) = 0`. -/
lemma criticalAngle_torque_zero (FD FL : ℝ) (hFD : 0 < FD) :
    localFrameTorque FD FL (criticalAngle FD FL) = 0 := by
  rw [localFrameTorque_eq_sin_shift FD FL hFD, sub_self, Real.sin_zero, mul_zero]

/-- **[The torque sign is the sine sign]** `F_j(θ) > 0 ⟺ sin(θ − θ*) > 0` — crossing the critical
angle reverses the alignment torque (the paper's lift-reversal transition). -/
lemma localFrameTorque_pos_iff (FD FL : ℝ) (hFD : 0 < FD) (θ : ℝ) :
    0 < localFrameTorque FD FL θ ↔ 0 < Real.sin (θ - criticalAngle FD FL) := by
  have h0 : (0 : ℝ) < Real.sqrt (FD ^ 2 + FL ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [localFrameTorque_eq_sin_shift FD FL hFD θ]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    nlinarith
  · exact fun h => mul_pos h0 h

/-- **[`arctan(√3/3) = π/6`]** the lower end of the paper's critical window as an arctangent. -/
lemma arctan_sqrt_three_div_three : Real.arctan (Real.sqrt 3 / 3) = Real.pi / 6 := by
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ht : Real.tan (Real.pi / 6) = Real.sqrt 3 / 3 := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_six, Real.cos_pi_div_six]
    field_simp
    linarith [hs3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  rw [← ht]
  exact Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- **[The critical window is a lift-to-drag window]** `θ* ∈ [π/6, π/4] ⟺ F_L/F_D ∈ [√3/3, 1]` —
the paper's observed critical-angle range `30°–45°` is *exactly* the statement that the
lift-to-drag ratio lies between `tan 30° = √3/3` and `tan 45° = 1`. -/
lemma criticalAngle_window (FD FL : ℝ) :
    criticalAngle FD FL ∈ Set.Icc (Real.pi / 6) (Real.pi / 4)
      ↔ FL / FD ∈ Set.Icc (Real.sqrt 3 / 3) 1 := by
  rw [Set.mem_Icc, Set.mem_Icc, criticalAngle, ← arctan_sqrt_three_div_three,
    ← Real.arctan_one]
  exact and_congr Real.arctan_le_arctan_iff Real.arctan_le_arctan_iff


/-! ## §C — exchange as the fermionic ribbon twist; the trefoil braid word -/

/-- **The framed complex force** — the drag–lift pair `F_D − i·F_L` rotated by the *interaction
frame* of the Dirac interaction picture (`ConfigurationSpaceDiracFluctuation.interactionFrame` at
`H₀ = 1`, `ℏ = 1`), with the inclination angle in the time slot. Its real and imaginary parts are
the paper's local-frame components (`framedForce_eq_localFrame`). -/
def framedForce (FD FL θ : ℝ) : ℂ :=
  interactionFrame (1 : ℂ) 1 θ * ((FD : ℂ) - (FL : ℂ) * Complex.I)

/-- **[The interaction frame at `H₀ = 1, ℏ = 1` is the `U(1)` phase]**
`interactionFrame 1 1 θ = e^{iθ}` — the abelian instance of the Dirac interaction frame. -/
lemma interactionFrame_unit (θ : ℝ) :
    interactionFrame (1 : ℂ) 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := by
  unfold interactionFrame interactionGenerator
  rw [← Complex.exp_eq_exp_ℂ]
  simp [smul_eq_mul]

/-- **[The framed force is the local frame]** `framedForce = F_i + i·F_j` — the interaction-frame
rotation of the complex force *is* the paper's Eq. (7) decomposition. -/
theorem framedForce_eq_localFrame (FD FL θ : ℝ) :
    framedForce FD FL θ
      = (localFrameAttraction FD FL θ : ℂ) + (localFrameTorque FD FL θ : ℂ) * Complex.I := by
  rw [framedForce, interactionFrame_unit, Complex.exp_mul_I]
  simp only [localFrameAttraction, localFrameTorque, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  linear_combination (-(FL : ℂ) * (Real.sin θ : ℂ)) * Complex.I_sq

/-- **[Bubble exchange is the fermionic ribbon twist]** exchanging the two bubbles is the half-turn
`θ ↦ θ + π` of the centerline, and on the framed force it acts by `ribbonTwist (1/2) = −1` — the
spin-½ topological phase of `Hopf.ChargeConjugationRibbonTwist`. -/
theorem framedForce_exchange (FD FL θ : ℝ) :
    framedForce FD FL (θ + Real.pi) = ribbonTwist (1 / 2) * framedForce FD FL θ := by
  rw [ribbonTwist_fermion]
  unfold framedForce
  rw [interactionFrame_unit, interactionFrame_unit,
    show ((θ + Real.pi : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- **[The full rotation is bosonic]** `θ ↦ θ + 2π` acts by `ribbonTwist 1 = 1`: a full turn of the
pair is topologically trivial on the frame — the boson/full-twist triviality. -/
theorem framedForce_full_rotation (FD FL θ : ℝ) :
    framedForce FD FL (θ + 2 * Real.pi) = ribbonTwist 1 * framedForce FD FL θ := by
  have hb : ribbonTwist (1 : ℝ) = 1 := by
    simpa using ribbonTwist_boson 1
  rw [hb, one_mul]
  unfold framedForce
  rw [interactionFrame_unit, interactionFrame_unit,
    show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I]
  ring

/-- **[The trefoil braid word is fermionic]** `halfTwist r r = r³ = −1` at `r = ribbonTwist (1/2)`:
the `B₂` trefoil word `σ₁³` — whose closure is the electron knot of
`TrefoilFermionChernSimonsInvariant` — carries the same fermionic sign as a single exchange in the
abelianized braid representation. -/
theorem trefoilWord_ribbon_fermion :
    halfTwist (ribbonTwist (1 / 2)) (ribbonTwist (1 / 2)) = -1 := by
  unfold halfTwist
  rw [ribbonTwist_fermion]
  norm_num

/-- **[The full twist is trivial]** `fullTwist r r = r⁶ = 1` at `r = ribbonTwist (1/2)`: the centre
`Δ²` of `B₃` — the framing that Witten's Chern–Simons invariant counts — acts trivially in the
abelianized representation. -/
theorem fullTwist_ribbon_trivial :
    fullTwist (ribbonTwist (1 / 2)) (ribbonTwist (1 / 2)) = 1 := by
  unfold fullTwist
  rw [ribbonTwist_fermion]
  norm_num

/-- **[Three half-turns act by the trefoil word]** `framedForce (θ + 3π) = (halfTwist r r) ·
framedForce θ` — three successive bubble exchanges compose to the trefoil braid word acting on the
frame, again a net fermionic sign. -/
theorem framedForce_trefoil (FD FL θ : ℝ) :
    framedForce FD FL (θ + 3 * Real.pi)
      = halfTwist (ribbonTwist (1 / 2)) (ribbonTwist (1 / 2)) * framedForce FD FL θ := by
  rw [trefoilWord_ribbon_fermion]
  unfold framedForce
  rw [interactionFrame_unit, interactionFrame_unit,
    show ((θ + 3 * Real.pi : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I
          + ((Real.pi : ℂ) * Complex.I
            + ((Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I)) by push_cast; ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
  ring


/-! ## §D — the Weber–Reynolds control plane (paper §II) -/

/-- **The Weber number** `We = ρU²D/σ` — inertia against surface tension; the paper's deformation
control parameter. -/
def weberNumber (rho U D sigma : ℝ) : ℝ := rho * U ^ 2 * D / sigma

/-- **The Reynolds number** `Re = ρUD/μ` — inertia against viscosity. -/
def reynoldsNumber (rho U D mu : ℝ) : ℝ := rho * U * D / mu

/-- **The capillary number** `Ca = μU/σ` — viscous stress against surface tension. -/
def capillaryNumber (mu U sigma : ℝ) : ℝ := mu * U / sigma

/-- **The Morton number** `Mo = gμ⁴/(ρσ³)` — the fluid-only group: fixed by the working liquid,
independent of bubble speed and size. -/
def mortonNumber (g mu rho sigma : ℝ) : ℝ := g * mu ^ 4 / (rho * sigma ^ 3)

/-- **The squared Froude number** `Fr² = U²/(gD)` — inertia against buoyancy. -/
def froudeSquared (U g D : ℝ) : ℝ := U ^ 2 / (g * D)

/-- **[`We = Ca·Re`]** the Weber number factors through viscosity: deformation is capillary stress
times Reynolds number. -/
theorem weber_eq_capillary_mul_reynolds (rho U D sigma mu : ℝ) (hmu : mu ≠ 0) :
    weberNumber rho U D sigma = capillaryNumber mu U sigma * reynoldsNumber rho U D mu := by
  unfold weberNumber capillaryNumber reynoldsNumber
  field_simp

/-- **[`We³ = Mo·Fr²·Re⁴`]** the paper's two control parameters `(Re, We)` and the fluid-only Morton
number are exactly related: at fixed working fluid (fixed `Mo`) the `(Re, We)` phase plane is
scanned by bubble speed and diameter alone. -/
theorem weber_cubed_eq_morton_froude_reynolds (rho U D sigma mu g : ℝ)
    (hrho : rho ≠ 0) (hsigma : sigma ≠ 0) (hmu : mu ≠ 0) (hg : g ≠ 0) (hD : D ≠ 0) :
    weberNumber rho U D sigma ^ 3
      = mortonNumber g mu rho sigma * froudeSquared U g D * reynoldsNumber rho U D mu ^ 4 := by
  unfold weberNumber mortonNumber froudeSquared reynoldsNumber
  field_simp

/-- **The surface-tension dimension** `[σ] = M·T⁻²` (force per length). -/
def surfaceTension_dim : Dimension LTMCTIDimensionBase := M𝓭 * T𝓭 ^ (-2 : ℚ)

/-- **The dynamic-viscosity dimension** `[μ] = M·L⁻¹·T⁻¹`. -/
def dynamicViscosity_dim : Dimension LTMCTIDimensionBase := M𝓭 * L𝓭⁻¹ * T𝓭⁻¹

/-- **[The Weber number is dimensionless]** `[ρ][U]²[D] = [σ]` in the dimension group. -/
theorem weber_dimensionless :
    massDensity_dim * velocity_dim ^ (2 : ℚ) * L𝓭 / surfaceTension_dim = 1 := by
  ext b <;> cases b <;> norm_num [massDensity_dim, velocity_dim, surfaceTension_dim]

/-- **[The Reynolds number is dimensionless]** `[ρ][U][D] = [μ]` in the dimension group. -/
theorem reynolds_dimensionless :
    massDensity_dim * velocity_dim * L𝓭 / dynamicViscosity_dim = 1 := by
  ext b <;> cases b <;> norm_num [massDensity_dim, velocity_dim, dynamicViscosity_dim]

/-- **[The drag coefficient is dimensionless]** `[F] = [ρ][U]²[A]` — the paper's Eq. (5)
`C_D = 2F_D/(ρU²A)` is a pure number. -/
theorem dragCoefficient_dimensionless :
    force_dim / (massDensity_dim * velocity_dim ^ (2 : ℚ) * area_dim) = 1 := by
  ext b <;> cases b <;> norm_num [force_dim, energy_dim, massDensity_dim, velocity_dim, area_dim]

end FluidDynamics.BubblePairLocalFrame

end

end

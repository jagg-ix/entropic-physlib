/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Physlib.Meta.AxiomWhitelistCheck

meta import Zil

/-!
# The Ibison–Puthoff no-runaway form of the Lorentz–Dirac equation

This module formalizes the central exact constructions in M. Ibison and H. E. Puthoff,
*Relativistic integro-differential form of the Lorentz–Dirac equation in 3D without runaways*,
J. Phys. A 34 (2001), 3421–3428.

* **§A — explicit integrating factor.** `ibisonR` and `ibisonRInv` are the matrices in equations
  (11) and (14). On the unit future mass shell they are mutual inverses.
  `ibisonR_mulVec_lower_self` is the algebraic identity underlying equation (12).
* **§B — future-tail solution.** `lorentzDiracIntegralAcceleration` is equation (18), expressed as
  a genuine Bochner integral over positive dimensionless proper-time displacement.
  `lorentzDiracIntegralAcceleration_eq_zero_of_future_force_zero` proves the advertised no-runaway
  property for a force with finite future support.
* **§C — kinematic consistency.** The transported force remains orthogonal to the current
  four-velocity, and constant velocity reduces the matrix formula to the familiar exponential
  Abraham–Lorentz future average.
* **§D — equations (17) and (18).** `dimensionlessFutureAverage_eq_futureExponentialResolvent`
  proves the positive-time change of variables under explicit continuity and integrability
  hypotheses.
* **§E — transformed differential equation.** The future exponential resolvent is differentiable
  and solves `F - τ₀ F' = h`, the exact first-order equation obtained after the integrating-factor
  transformation.

The coordinate dot product below follows the paper's component convention after lowering the
four-velocity. This is a flat-spacetime point-particle theorem. In particular, the construction does
not formalize the curved-spacetime DeWitt–Brehme self-force. Moreover, eliminating the exponentially
growing homogeneous solution does not eliminate preacceleration: equation (18) deliberately depends
on future values of the applied force.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix
open MeasureTheory Set Filter

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway

/-- The raw four-component carrier used by the paper's explicit coordinate matrices. -/
abbrev FourVector := Fin 4 → ℝ

/-- Ibison–Puthoff equation (11): the velocity-dependent integrating-factor matrix `R(u)`. -/
def ibisonR (u : FourVector) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![u 0, u 1, u 2, u 3;
     u 1, u 0, 0, 0;
     u 2, 0, u 0, 0;
     u 3, 0, 0, u 0]

/-- Ibison–Puthoff equation (14): the explicit inverse of `R(u)` on the unit mass shell. -/
noncomputable def ibisonRInv (u : FourVector) : Matrix (Fin 4) (Fin 4) ℝ :=
  (u 0)⁻¹ •
  !![(u 0)^2, -(u 0 * u 1), -(u 0 * u 2), -(u 0 * u 3);
     -(u 0 * u 1), (u 1)^2 + 1, u 1 * u 2, u 1 * u 3;
     -(u 0 * u 2), u 1 * u 2, (u 2)^2 + 1, u 2 * u 3;
     -(u 0 * u 3), u 1 * u 3, u 2 * u 3, (u 3)^2 + 1]

/-- The unit timelike mass-shell equation in signature `(+---)` and units `c = 1`. -/
def OnUnitMassShell (u : FourVector) : Prop :=
  (u 0)^2 - (u 1)^2 - (u 2)^2 - (u 3)^2 = 1

/-- Equation (14) is a right inverse of equation (11) on the unit mass shell. -/
@[zil_level algebraic]
theorem ibisonR_mul_ibisonRInv
    (u : FourVector) (hu : OnUnitMassShell u) (hu0 : u 0 ≠ 0) :
    ibisonR u * ibisonRInv u = 1 := by
  have hs : u 0 ^ 2 = u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 1 := by
    unfold OnUnitMassShell at hu
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ibisonR, ibisonRInv, Matrix.mul_apply, Fin.sum_univ_four, hu0] <;>
    field_simp <;> try rw [hs]
  all_goals ring

/-- Equation (14) is also a left inverse of equation (11) on the unit mass shell. -/
theorem ibisonRInv_mul_ibisonR
    (u : FourVector) (hu : OnUnitMassShell u) (hu0 : u 0 ≠ 0) :
    ibisonRInv u * ibisonR u = 1 := by
  have hs : u 0 ^ 2 = u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 1 := by
    unfold OnUnitMassShell at hu
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ibisonR, ibisonRInv, Matrix.mul_apply, Fin.sum_univ_four, hu0] <;>
    field_simp <;> try rw [hs]
  all_goals ring

/-- Lower a four-vector with the flat metric of signature `(+---)`. -/
def minkowskiLower (v : FourVector) : FourVector :=
  ![v 0, -v 1, -v 2, -v 3]

/-- The distinguished unit time-basis vector. -/
def timeBasis : FourVector := ![1, 0, 0, 0]

/-- The flat Minkowski square in the paper's signature. -/
def minkowskiSq (v : FourVector) : ℝ :=
  (v 0)^2 - (v 1)^2 - (v 2)^2 - (v 3)^2

/-- The algebraic core of equation (12):
`R(v)` sends the lowered vector to its Minkowski square times the time basis. -/
@[zil_level algebraic]
theorem ibisonR_mulVec_lower_self (v : FourVector) :
    ibisonR v *ᵥ minkowskiLower v = minkowskiSq v • timeBasis := by
  funext i
  fin_cases i <;>
    simp [ibisonR, minkowskiLower, minkowskiSq, timeBasis,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- On the unit mass shell, equation (12) becomes `R(u) u♭ = e₀`. -/
theorem ibisonR_mulVec_lower_velocity
    (u : FourVector) (hu : OnUnitMassShell u) :
    ibisonR u *ᵥ minkowskiLower u = timeBasis := by
  rw [ibisonR_mulVec_lower_self]
  have hsq : minkowskiSq u = 1 := hu
  rw [hsq, one_smul]

/-- Raw component contraction. When its first argument is a four-velocity, the caller supplies the
paper's already-lowered-index component convention. -/
def euclideanDot (u v : FourVector) : ℝ := ∑ i, u i * v i

/-- Contracting `R(u)⁻¹ v` with `u` selects the time component of `v`. -/
theorem velocity_mul_ibisonRInv
    (u : FourVector) (hu : OnUnitMassShell u) (hu0 : u 0 ≠ 0) (v : FourVector) :
    euclideanDot u (ibisonRInv u *ᵥ v) = v 0 := by
  have hs : u 0 ^ 2 = u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 1 := by
    unfold OnUnitMassShell at hu
    linarith
  simp [euclideanDot, ibisonRInv, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four, hu0]
  field_simp
  rw [hs]
  ring

/-- The transport matrix `R(u(τ))⁻¹ R(u(τ'))` appearing in equation (18). -/
def ibisonTransport (uNow uFuture : FourVector) : Matrix (Fin 4) (Fin 4) ℝ :=
  ibisonRInv uNow * ibisonR uFuture

/-- Ibison–Puthoff equation (18), as a Bochner integral over positive dimensionless proper time. -/
noncomputable def lorentzDiracIntegralAcceleration
    (m tau0 : ℝ) (u force : ℝ → FourVector) (tau : ℝ) : FourVector :=
  m⁻¹ • ∫ s in Ioi 0,
    Real.exp (-s) •
      ((ibisonTransport (u tau) (u (tau + s * tau0))) *ᵥ
        force (tau + s * tau0))

/-- **No runaway after the applied force ends.** If `τ₀ ≥ 0`, the force vanishes from a time `T`
onward, and `τ ≥ T`, then the future-tail solution (18) is exactly zero. This theorem does not claim
absence of preacceleration before `T`. -/
@[zil_level physical_theorem]
theorem lorentzDiracIntegralAcceleration_eq_zero_of_future_force_zero
    (m tau0 : ℝ) (u force : ℝ → FourVector) (tau T : ℝ)
    (htau0 : 0 ≤ tau0)
    (ht : T ≤ tau)
    (hforce : ∀ t, T ≤ t → force t = 0) :
    lorentzDiracIntegralAcceleration m tau0 u force tau = 0 := by
  unfold lorentzDiracIntegralAcceleration
  rw [show (∫ s in Ioi 0,
      Real.exp (-s) •
        ((ibisonTransport (u tau) (u (tau + s * tau0))) *ᵥ
          force (tau + s * tau0))) = 0 by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [hforce (tau + s * tau0) (le_trans ht (by
      exact le_add_of_nonneg_right (mul_nonneg hs.le htau0)))]
    simp]
  simp

/-- The transported-force contraction at the current velocity equals the force contraction at its
future velocity. This is the matrix mechanism behind equations (20)–(21). -/
theorem ibisonTransport_force_contraction
    (uNow uFuture force : FourVector)
    (hu : OnUnitMassShell uNow) (hu0 : uNow 0 ≠ 0) :
    euclideanDot uNow (ibisonTransport uNow uFuture *ᵥ force) =
      euclideanDot uFuture force := by
  unfold ibisonTransport
  rw [← Matrix.mulVec_mulVec]
  rw [velocity_mul_ibisonRInv uNow hu hu0]
  simp [ibisonR, euclideanDot, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- A force orthogonal to its future velocity remains orthogonal after transport to the current
velocity. -/
theorem ibisonTransport_force_orthogonal
    (uNow uFuture force : FourVector)
    (hu : OnUnitMassShell uNow) (hu0 : uNow 0 ≠ 0)
    (hforce : euclideanDot uFuture force = 0) :
    euclideanDot uNow (ibisonTransport uNow uFuture *ᵥ force) = 0 := by
  rw [ibisonTransport_force_contraction uNow uFuture force hu hu0, hforce]

/-- For constant four-velocity, equation (18) reduces to the exponential future-force average of
the nonrelativistic Abraham–Lorentz equation (4). -/
@[zil_level bridge_theorem]
theorem lorentzDiracIntegralAcceleration_const_velocity
    (m tau0 : ℝ) (u0 : FourVector) (force : ℝ → FourVector) (tau : ℝ)
    (hu : OnUnitMassShell u0) (hu0 : u0 0 ≠ 0) :
    lorentzDiracIntegralAcceleration m tau0 (fun _ => u0) force tau =
      m⁻¹ • ∫ s in Ioi 0,
        Real.exp (-s) • force (tau + s * tau0) := by
  unfold lorentzDiracIntegralAcceleration ibisonTransport
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [ibisonRInv_mul_ibisonR u0 hu hu0]
  simp

/-- The raw component contraction as a continuous linear map, used to commute it with the Bochner
integral in equation (18). -/
def euclideanDotCLM (u : FourVector) : FourVector →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := euclideanDot u
      map_add' := by
        intro v w
        simp only [euclideanDot, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        simp only [euclideanDot, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [RingHom.id_apply]
        ring }

@[simp]
theorem euclideanDotCLM_apply (u v : FourVector) :
    euclideanDotCLM u v = euclideanDot u v := rfl

/-- Equations (20)–(21): under pointwise force orthogonality, the integral acceleration is
orthogonal to the current four-velocity. -/
@[zil_level physical_theorem]
theorem lorentzDiracIntegralAcceleration_orthogonal
    (m tau0 : ℝ) (u force : ℝ → FourVector) (tau : ℝ)
    (hu : OnUnitMassShell (u tau)) (hu0 : u tau 0 ≠ 0)
    (hforce : ∀ t, tau ≤ t → euclideanDot (u t) (force t) = 0)
    (hint : IntegrableOn
      (fun s => Real.exp (-s) •
        (ibisonTransport (u tau) (u (tau + s * tau0)) *ᵥ
          force (tau + s * tau0))) (Ioi 0))
    (htau0 : 0 ≤ tau0) :
    euclideanDot (u tau)
      (lorentzDiracIntegralAcceleration m tau0 u force tau) = 0 := by
  let raw : ℝ → FourVector := fun s =>
    Real.exp (-s) •
      (ibisonTransport (u tau) (u (tau + s * tau0)) *ᵥ
        force (tau + s * tau0))
  have hmap :
      (∫ s in Ioi 0, euclideanDotCLM (u tau) (raw s)) =
        euclideanDotCLM (u tau) (∫ s in Ioi 0, raw s) := by
    exact (euclideanDotCLM (u tau)).integral_comp_comm hint
  unfold lorentzDiracIntegralAcceleration
  rw [euclideanDotCLM_apply] at hmap
  change euclideanDotCLM (u tau)
    (m⁻¹ • ∫ s in Ioi 0, raw s) = 0
  rw [map_smul, euclideanDotCLM_apply, ← hmap]
  have hzero :
      (∫ s in Ioi 0, euclideanDotCLM (u tau) (raw s)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simp only [raw, euclideanDotCLM_apply, map_smul]
    rw [ibisonTransport_force_contraction
      (u tau) (u (tau + s * tau0)) (force (tau + s * tau0)) hu hu0,
      hforce (tau + s * tau0)
        (le_add_of_nonneg_right (mul_nonneg hs.le htau0)),
      smul_zero]
    rfl
  rw [hzero, smul_zero]

section FutureResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Bochner-integrated future tail of a Banach-valued function. -/
noncomputable def futureTail (g : ℝ → E) (tau : ℝ) : E :=
  ∫ t in Ioi tau, g t

/-- An integrable future tail equals a constant minus the finite interval integral up to `τ`. -/
theorem futureTail_eq_const_sub_interval
    (g : ℝ → E) (hg : Integrable g) (tau : ℝ) :
    futureTail g tau =
      ((∫ t, g t) - ∫ t in Iic 0, g t) - ∫ t in (0 : ℝ)..tau, g t := by
  have hsplit :=
    intervalIntegral.integral_Iic_add_Ioi (f := g) (b := tau)
      hg.integrableOn hg.integrableOn
  have hinterval :=
    intervalIntegral.integral_Iic_sub_Iic (f := g) (b := tau) (a := 0)
      hg.integrableOn hg.integrableOn
  unfold futureTail
  calc
    (∫ t in Ioi tau, g t) =
        ((∫ t in Iic tau, g t) + ∫ t in Ioi tau, g t) -
          ∫ t in Iic tau, g t := by abel
    _ = (∫ t, g t) - ∫ t in Iic tau, g t := by rw [hsplit]
    _ = ((∫ t, g t) - ∫ t in Iic 0, g t) -
        ∫ t in (0 : ℝ)..tau, g t := by
      rw [← hinterval]
      abel

/-- The derivative of an integrable continuous future tail is the negative current integrand. -/
theorem futureTail_hasDerivAt
    (g : ℝ → E) (hg : Integrable g) (hcont : Continuous g) (tau : ℝ) :
    HasDerivAt (futureTail g) (-g tau) tau := by
  have hint :
      HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, g t) (g tau) tau :=
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 tau)
      (hcont.stronglyMeasurableAtFilter volume (nhds tau)) hcont.continuousAt
  have hderiv :=
    (hasDerivAt_const tau ((∫ t, g t) - ∫ t in Iic 0, g t)).sub hint
  have hfun :
      futureTail g =
        fun x => ((∫ t, g t) - ∫ t in Iic 0, g t) -
          ∫ t in (0 : ℝ)..x, g t := by
    funext x
    exact futureTail_eq_const_sub_interval g hg x
  rw [hfun]
  convert hderiv using 1
  · funext x
    rfl
  · simp

/-- The future exponential resolvent in integrating-factor form, corresponding to equation (17). -/
noncomputable def futureExponentialResolvent
    (tau0 : ℝ) (h : ℝ → E) (tau : ℝ) : E :=
  tau0⁻¹ • Real.exp (tau / tau0) •
    futureTail (fun t => Real.exp (-t / tau0) • h t) tau

/-- The same future resolvent written with the kernel `exp ((τ-t)/τ₀)`. -/
noncomputable def futureExponentialTailResolvent
    (tau0 : ℝ) (h : ℝ → E) (tau : ℝ) : E :=
  tau0⁻¹ • ∫ t in Ioi tau,
    Real.exp ((tau - t) / tau0) • h t

/-- The dimensionless positive-time future average used in equation (18). -/
noncomputable def dimensionlessFutureAverage
    (tau0 : ℝ) (h : ℝ → E) (tau : ℝ) : E :=
  ∫ s in Ioi 0, Real.exp (-s) • h (tau + s * tau0)

/-- The tail-kernel and integrating-factor forms of the future exponential resolvent agree. -/
theorem futureExponentialTailResolvent_eq
    (tau0 : ℝ) (h : ℝ → E) (tau : ℝ) :
    futureExponentialTailResolvent tau0 h tau =
      futureExponentialResolvent tau0 h tau := by
  unfold futureExponentialTailResolvent futureExponentialResolvent futureTail
  congr 1
  rw [← MeasureTheory.integral_smul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [smul_smul]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

/-- The positive-time change of variables `t = τ + s τ₀` identifies equations (17) and (18), under
the continuity and Bochner-integrability hypotheses needed by the improper-integral theorem. -/
theorem dimensionlessFutureAverage_eq_tailResolvent
    (tau0 : ℝ) (htau0 : 0 < tau0) (h : ℝ → E) (tau : ℝ)
    (hcont : Continuous h)
    (hg : IntegrableOn
      (fun t => Real.exp ((tau - t) / tau0) • h t) (Ici tau))
    (hs : IntegrableOn
      (fun s => tau0 •
        (Real.exp ((tau - (tau + s * tau0)) / tau0) •
          h (tau + s * tau0))) (Ici 0)) :
    dimensionlessFutureAverage tau0 h tau =
      futureExponentialTailResolvent tau0 h tau := by
  let phi : ℝ → ℝ := fun s => tau + tau0 * s
  let g : ℝ → E := fun t => Real.exp ((tau - t) / tau0) • h t
  have hphi_cont : ContinuousOn phi (Ici 0) := by
    fun_prop
  have hphi_top : Tendsto phi atTop atTop := by
    dsimp [phi]
    convert Filter.tendsto_atTop_add_const_left atTop tau
      (tendsto_id.const_mul_atTop htau0) using 1 <;>
      simp
  have hphi_deriv :
      ∀ s ∈ Ioi 0, HasDerivWithinAt phi tau0 (Ioi s) s := by
    intro s _
    apply HasDerivAt.hasDerivWithinAt
    dsimp [phi]
    have hd := (hasDerivAt_const s tau).add
      ((hasDerivAt_id s).const_mul tau0)
    convert hd using 1
    · funext x
      rfl
    · ring
  have hgcont : ContinuousOn g (phi '' Ioi 0) := by
    apply Continuous.continuousOn
    dsimp [g]
    fun_prop
  have hg1 : IntegrableOn g (phi '' Ici 0) := by
    apply hg.mono_set
    intro t ht
    rcases ht with ⟨s, hs0, rfl⟩
    dsimp [phi]
    exact le_add_of_nonneg_right (mul_nonneg htau0.le hs0)
  have hg2 :
      IntegrableOn (fun s => tau0 • (g ∘ phi) s) (Ici 0) := by
    simpa [g, phi, Function.comp_apply, mul_comm] using hs
  have hchange :=
    integral_deriv_smul_comp_Ioi hphi_cont hphi_top hphi_deriv
      hgcont hg1 hg2
  have hchange' :
      (∫ s in Ioi 0, tau0 • (g ∘ phi) s) =
        ∫ t in Ioi tau, g t := by
    simpa [phi] using hchange
  unfold dimensionlessFutureAverage futureExponentialTailResolvent
  change (∫ s in Ioi 0, Real.exp (-s) • h (tau + s * tau0)) =
    tau0⁻¹ • ∫ t in Ioi tau, g t
  rw [← hchange']
  rw [← MeasureTheory.integral_smul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  simp only [Function.comp_apply, g, phi, smul_smul]
  have hcancel : tau0⁻¹ * tau0 = 1 := inv_mul_cancel₀ htau0.ne'
  rw [show tau + tau0 * s = tau + s * tau0 by ring]
  congr 1
  rw [← mul_assoc, hcancel, one_mul]
  rw [show (tau - (tau + s * tau0)) / tau0 = -s by
    field_simp
    ring]

/-- The dimensionless equation-(18) integral equals the integrating-factor equation-(17)
resolvent. -/
@[zil_level bridge_theorem]
theorem dimensionlessFutureAverage_eq_futureExponentialResolvent
    (tau0 : ℝ) (htau0 : 0 < tau0) (h : ℝ → E) (tau : ℝ)
    (hcont : Continuous h)
    (hg : IntegrableOn
      (fun t => Real.exp ((tau - t) / tau0) • h t) (Ici tau))
    (hs : IntegrableOn
      (fun s => tau0 •
        (Real.exp ((tau - (tau + s * tau0)) / tau0) •
          h (tau + s * tau0))) (Ici 0)) :
    dimensionlessFutureAverage tau0 h tau =
      futureExponentialResolvent tau0 h tau := by
  rw [dimensionlessFutureAverage_eq_tailResolvent
    tau0 htau0 h tau hcont hg hs,
    futureExponentialTailResolvent_eq]

/-- The future resolvent is differentiable, with
`F'(τ) = τ₀⁻¹ (F(τ) - h(τ))`. -/
theorem futureExponentialResolvent_hasDerivAt
    (tau0 : ℝ) (h : ℝ → E)
    (hg : Integrable (fun t => Real.exp (-t / tau0) • h t))
    (hcont : Continuous h) (tau : ℝ) :
    HasDerivAt (futureExponentialResolvent tau0 h)
      (tau0⁻¹ • (futureExponentialResolvent tau0 h tau - h tau)) tau := by
  have hweighted : Continuous (fun t => Real.exp (-t / tau0) • h t) := by
    fun_prop
  have htail := futureTail_hasDerivAt
    (fun t => Real.exp (-t / tau0) • h t) hg hweighted tau
  have hexp :
      HasDerivAt (fun t => Real.exp (t / tau0))
        (tau0⁻¹ * Real.exp (tau / tau0)) tau := by
    change HasDerivAt (Real.exp ∘ fun t => t / tau0)
      (tau0⁻¹ * Real.exp (tau / tau0)) tau
    have hinner :
        HasDerivAt (fun t : ℝ => t / tau0) tau0⁻¹ tau := by
      simpa only [id_eq, one_div] using
        (hasDerivAt_id tau).div_const tau0
    simpa only [mul_comm] using
      (Real.hasDerivAt_exp (tau / tau0)).comp tau hinner
  have hprod := hexp.smul htail
  have hscaled := hprod.const_smul tau0⁻¹
  convert hscaled using 1
  · funext t
    simp [futureExponentialResolvent, smul_smul]
  · simp only [futureExponentialResolvent, smul_add, smul_smul]
    have hexpcancel : Real.exp (tau / tau0) * Real.exp (-tau / tau0) = 1 := by
      calc
        Real.exp (tau / tau0) * Real.exp (-tau / tau0) =
            Real.exp (tau / tau0 + -tau / tau0) := (Real.exp_add _ _).symm
        _ = Real.exp 0 := by congr 1 <;> ring
        _ = 1 := Real.exp_zero
    have hterm :
        (tau0⁻¹ * Real.exp (tau / tau0)) •
            -(Real.exp (-tau / tau0) • h tau) =
          (-tau0⁻¹) • h tau := by
      rw [smul_neg, smul_smul, neg_smul]
      congr 2
      rw [mul_assoc, hexpcancel, mul_one]
    rw [hterm]
    module

/-- The future resolvent solves the exact transformed Lorentz–Dirac first-order equation
`F - τ₀ F' = h`. The nonzero `τ₀` premise is used only to recover this algebraic equation from the
derivative formula. -/
@[zil_level bridge_theorem]
theorem futureExponentialResolvent_solves_transformed_lorentzDirac
    (tau0 : ℝ) (htau0 : tau0 ≠ 0) (h : ℝ → E)
    (hg : Integrable (fun t => Real.exp (-t / tau0) • h t))
    (hcont : Continuous h) (tau : ℝ) :
    HasDerivAt (futureExponentialResolvent tau0 h)
        (tau0⁻¹ • (futureExponentialResolvent tau0 h tau - h tau)) tau ∧
      futureExponentialResolvent tau0 h tau -
          tau0 •
            (tau0⁻¹ • (futureExponentialResolvent tau0 h tau - h tau)) =
        h tau := by
  refine ⟨futureExponentialResolvent_hasDerivAt
    tau0 h hg hcont tau, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ htau0, one_smul]
  abel

end FutureResolvent

end Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway

open Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway in
#physlib_axiom_clean_all [
  ibisonR_mul_ibisonRInv,
  ibisonRInv_mul_ibisonR,
  ibisonR_mulVec_lower_self,
  velocity_mul_ibisonRInv,
  lorentzDiracIntegralAcceleration_eq_zero_of_future_force_zero,
  ibisonTransport_force_contraction,
  lorentzDiracIntegralAcceleration_const_velocity,
  lorentzDiracIntegralAcceleration_orthogonal,
  futureTail_hasDerivAt,
  dimensionlessFutureAverage_eq_futureExponentialResolvent,
  futureExponentialResolvent_hasDerivAt,
  futureExponentialResolvent_solves_transformed_lorentzDirac ]

open Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway in
#physlib_non_vacuous_all [
  ibisonR_mul_ibisonRInv,
  ibisonRInv_mul_ibisonR,
  ibisonR_mulVec_lower_self,
  velocity_mul_ibisonRInv,
  lorentzDiracIntegralAcceleration_eq_zero_of_future_force_zero,
  ibisonTransport_force_contraction,
  lorentzDiracIntegralAcceleration_const_velocity,
  lorentzDiracIntegralAcceleration_orthogonal,
  futureTail_hasDerivAt,
  dimensionlessFutureAverage_eq_futureExponentialResolvent,
  futureExponentialResolvent_hasDerivAt,
  futureExponentialResolvent_solves_transformed_lorentzDirac ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.ibisonR_mul_ibisonRInv where
  formalizes @ "claim:ibison-puthoff-equations-11-and-14-are-mutual-inverses-on-the-unit-timelike-mass-shell",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ibison-puthoff-2001-relativistic-integro-differential-lorentz-dirac-without-runaways",
  caveat @ "claim:explicit-flat-coordinate-matrix-identity-not-a-curved-spacetime-self-force-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.ibisonR_mulVec_lower_self where
  formalizes @ "claim:ibison-puthoff-equation-12-integrating-factor-matrix-sends-a-lowered-four-vector-to-its-minkowski-square-times-the-time-basis",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ibison-puthoff-2001-relativistic-integro-differential-lorentz-dirac-without-runaways"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.lorentzDiracIntegralAcceleration_eq_zero_of_future_force_zero where
  formalizes @ "claim:the-ibison-puthoff-future-tail-lorentz-dirac-solution-has-no-runaway-after-a-finite-support-applied-force-ends",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:ibison-puthoff-2001-relativistic-integro-differential-lorentz-dirac-without-runaways",
  caveat @ "claim:no-exponentially-growing-future-tail-after-force-support-ends-but-no-claim-that-preacceleration-or-future-force-dependence-is-removed"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.lorentzDiracIntegralAcceleration_orthogonal where
  formalizes @ "claim:the-ibison-puthoff-integral-acceleration-is-orthogonal-to-the-current-four-velocity-when-the-applied-four-force-is-pointwise-orthogonal",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:ibison-puthoff-2001-relativistic-integro-differential-lorentz-dirac-without-runaways",
  caveat @ "claim:uses-the-papers-explicit-lowered-index-coordinate-contraction-and-bochner-integrability-premise"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.lorentzDiracIntegralAcceleration_const_velocity where
  formalizes @ "claim:at-constant-four-velocity-the-relativistic-ibison-puthoff-integral-reduces-to-the-exponential-abraham-lorentz-future-force-average",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:ibison-puthoff-2001-relativistic-integro-differential-lorentz-dirac-without-runaways"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.dimensionlessFutureAverage_eq_futureExponentialResolvent where
  formalizes @ "claim:ibison-puthoff-equations-17-and-18-are-related-by-the-positive-proper-time-change-of-variables",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ibison-puthoff-2001-relativistic-integro-differential-lorentz-dirac-without-runaways",
  caveat @ "claim:the-change-of-variables-exposes-the-continuity-and-bochner-integrability-hypotheses-used-in-the-improper-integral"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.futureExponentialResolvent_solves_transformed_lorentzDirac where
  formalizes @ "claim:the-future-exponential-resolvent-differentiates-to-and-solves-the-transformed-first-order-lorentz-dirac-equation",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:ibison-puthoff-2001-relativistic-integro-differential-lorentz-dirac-without-runaways",
  caveat @ "claim:exact-banach-valued-resolvent-identity-not-an-extended-charge-renormalization-quantum-qed-or-curved-spacetime-self-force-theorem"

zil_file_contract physlib.lorentzDiracNoRunaway where
  promises "The Ibison-Puthoff flat-spacetime Lorentz-Dirac construction: the explicit velocity-dependent integrating factor and inverse on the unit mass shell, the future-tail Bochner integral, exact cessation after a finite-support force ends, four-velocity orthogonality, the constant-velocity Abraham-Lorentz reduction, the equation-(17)-to-(18) positive-time change of variables, and the transformed first-order differential equation solved by the future exponential resolvent."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.lorentzForceNum",
    "lean:Matrix.mulVec",
    "lean:MeasureTheory.integral_deriv_smul_comp_Ioi",
    "lean:ContinuousLinearMap.integral_comp_comm"]
  forbids_substitutes ["a claim that the future-tail prescription removes preacceleration or future-force dependence",
    "a generally covariant curved-spacetime DeWitt-Brehme self-force",
    "a derivation of point-charge mass renormalization or quantum electrodynamics",
    "the proper-time and ordinary-time asymptotic derivative series in equations 29 through 37"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.ibisonR_mul_ibisonRInv,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.ibisonR_mulVec_lower_self,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.lorentzDiracIntegralAcceleration_eq_zero_of_future_force_zero,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.lorentzDiracIntegralAcceleration_orthogonal,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.lorentzDiracIntegralAcceleration_const_velocity,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.dimensionlessFutureAverage_eq_futureExponentialResolvent,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.LorentzDiracNoRunaway.futureExponentialResolvent_solves_transformed_lorentzDirac]

/- ZIL-END -/

#zil_formalization_lint physlib.lorentzDiracNoRunaway

end

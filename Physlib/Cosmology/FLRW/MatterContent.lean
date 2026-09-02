/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Jorge A. Garcia
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.HubbleEvolution
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Fin.VecNotation
/-!

# Matter content of FLRW cosmology

The matter content of a Friedmann–Lemaître–Robertson–Walker universe: the
barotropic (linear) equation of state, the resulting continuity and density
scaling laws, and the canonical scalar-field fluid with its Klein–Gordon
equation.  The continuity equation itself is *derived* from the Friedmann pair
upstream (`FriedmannEquation.continuity_from_friedmann`, the Bianchi-identity
consistency); here it is specialized:

* **§A — barotropic fluid.** `BarotropicFluid` (`P = wρc²`);
  `barotropic_continuity` (`ρ̇ = −3(1+w)Hρ`, i.e. `ρ̇ = −nHρ` with `n = 3(1+w)`:
  Gumjudpai Eq. (2)); `density_scaling_solves` (`ρ = D·a^{−n}` solves it —
  dust `w = 0, n = 3`, radiation `w = 1/3, n = 4`, stiff fluid `w = 1, n = 6`);
  `vacuum_energy_frozen` (`w = −1` forces `ρ̇ = 0`).
* **§B — the canonical scalar-field fluid.** `scalarFieldEnergyDensity` /
  `scalarFieldPressure` (`ρ_φc² = ½εφ̇² + V(φ)`, `p_φ = ½εφ̇² − V(φ)`, with
  `ε = +1` canonical and `ε = −1` phantom — Gumjudpai Eq. (4));
  `scalarField_continuity_iff_kleinGordon`: the fluid continuity equation for
  the scalar field is *equivalent* to `φ̇·(ε[φ̈ + 3Hφ̇] + V′(φ)) = 0` — the
  Klein–Gordon equation (Gumjudpai Eq. (6)) on every interval where the field
  rolls (`φ̇ ≠ 0`).

## References

* B. Gumjudpai, Gen. Relativ. Gravit. 41 (2009) 249, §2 (the two-fluid
  cosmological system; `n = 3(1+w)` bookkeeping).
* Repo carriers: `Cosmology.FLRW.FriedmannEquation` (`hubbleConstant`,
  `FirstOrderFriedmann`, `SecondOrderFriedmann`, `continuity_from_friedmann`),
  `Time` (`deriv_const_mul`, `deriv_sq`, `deriv_comp_hasDerivAt`,
  `deriv_rpow_const`).

-/

@[expose] public section

namespace Cosmology.FLRW.MatterContent

open Time
open Cosmology.FLRW.FriedmannEquation

/-! ## §A — the barotropic fluid -/

/-- **The barotropic (linear) equation of state** `P = w·ρ·c²` with constant
coefficient `w`: dust `w = 0`, radiation `w = 1/3`, vacuum energy `w = −1`,
stiff fluid `w = 1`. -/
def BarotropicFluid (ρ p : Time → ℝ) (w c : ℝ) : Prop :=
  ∀ t, p t = w * ρ t * c ^ 2

/-- **[Barotropic continuity] `ρ̇ = −3(1+w)·H·ρ`** — the continuity equation
derived from the Friedmann pair (`continuity_from_friedmann`), specialized to the
barotropic equation of state: with `n = 3(1+w)` this is `ρ̇ = −nHρ`
(Gumjudpai Eq. (2)). -/
theorem barotropic_continuity (a ρ p : Time → ℝ) (w k Λ G c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hG : G ≠ 0) (hc : c ≠ 0)
    (hfirstAll : ∀ s, FirstOrderFriedmann a ρ k Λ G c s)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t)
    (heos : BarotropicFluid ρ p w c) :
    ∂ₜ ρ t = -(3 * (1 + w)) * hubbleConstant a t * ρ t := by
  rw [continuity_from_friedmann a ρ p k Λ G c t ha hd_a haz hH hG hc
    hfirstAll hsecond, heos t]
  field_simp

/-- **[The density scaling law solves the continuity equation]** the power law
`ρ = D·a^{−n}` satisfies `ρ̇ = −n·H·ρ` pointwise: dust `n = 3` (`ρ ∝ a⁻³`),
radiation `n = 4` (`ρ ∝ a⁻⁴`), vacuum energy `n = 0` (`ρ` constant). -/
theorem density_scaling_solves (a : Time → ℝ) (D n : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hapos : 0 < a t) :
    ∂ₜ (fun s => D * a s ^ (-n)) t
      = -n * hubbleConstant a t * (D * a t ^ (-n)) := by
  have hX : DifferentiableAt ℝ (fun s => a s ^ (-n)) t :=
    (((Real.hasDerivAt_rpow_const
      (Or.inl hapos.ne')).hasFDerivAt.comp t ha.hasFDerivAt)).differentiableAt
  rw [Time.deriv_const_mul D t hX, Time.deriv_rpow_const t ha (Or.inl hapos.ne')]
  simp only [hubbleConstant]
  have key : a t ^ (-n - 1) = a t ^ (-n) / a t := by
    rw [eq_div_iff hapos.ne']
    calc a t ^ (-n - 1) * a t
        = a t ^ (-n - 1) * a t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = a t ^ (-n - 1 + 1) := (Real.rpow_add hapos _ _).symm
      _ = a t ^ (-n) := by norm_num
  rw [key]
  ring

/-- **[Vacuum energy is frozen]** a `w = −1` barotropic fluid has constant
density: the continuity equation degenerates to `ρ̇ = 0` — the fluid face of the
cosmological constant. -/
theorem vacuum_energy_frozen (a ρ p : Time → ℝ) (k Λ G c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hG : G ≠ 0) (hc : c ≠ 0)
    (hfirstAll : ∀ s, FirstOrderFriedmann a ρ k Λ G c s)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t)
    (heos : BarotropicFluid ρ p (-1) c) :
    ∂ₜ ρ t = 0 := by
  rw [barotropic_continuity a ρ p (-1) k Λ G c t ha hd_a haz hH hG hc
    hfirstAll hsecond heos]
  ring

/-! ## §B — the canonical scalar-field fluid -/

/-- **The scalar-field energy density** `½εφ̇² + V(φ)` — minimally coupled,
`ε = +1` canonical, `ε = −1` phantom (negative kinetic term). -/
noncomputable def scalarFieldEnergyDensity (ε : ℝ) (φ : Time → ℝ) (V : ℝ → ℝ) :
    Time → ℝ :=
  fun t => ε * (∂ₜ φ t) ^ 2 / 2 + V (φ t)

/-- **The scalar-field pressure** `½εφ̇² − V(φ)`. -/
noncomputable def scalarFieldPressure (ε : ℝ) (φ : Time → ℝ) (V : ℝ → ℝ) :
    Time → ℝ :=
  fun t => ε * (∂ₜ φ t) ^ 2 / 2 - V (φ t)

/-- **[Scalar-field continuity ⟺ Klein–Gordon]** the fluid continuity equation
for the scalar field (mass density `ρ_φ = (½εφ̇² + V)/c²`, pressure
`p_φ = ½εφ̇² − V`) holds at `t` *iff* `φ̇·(ε[φ̈ + 3Hφ̇] + V′(φ)) = 0` — on a
rolling field (`φ̇ ≠ 0`) the continuity equation *is* the Klein–Gordon equation
`ε[φ̈ + 3Hφ̇] + dV/dφ = 0` (Gumjudpai Eq. (6)). -/
theorem scalarField_continuity_iff_kleinGordon (a φ : Time → ℝ) (V : ℝ → ℝ)
    (ε c Vp : ℝ) (t : Time)
    (hφ : DifferentiableAt ℝ φ t) (hφd : DifferentiableAt ℝ (∂ₜ φ) t)
    (hV : HasDerivAt V Vp (φ t)) (hc : c ≠ 0) :
    (∂ₜ (fun s => scalarFieldEnergyDensity ε φ V s / c ^ 2) t
        = -3 * hubbleConstant a t
          * (scalarFieldEnergyDensity ε φ V t / c ^ 2
             + scalarFieldPressure ε φ V t / c ^ 2))
      ↔ ∂ₜ φ t * (ε * (∂ₜ (∂ₜ φ) t + 3 * hubbleConstant a t * ∂ₜ φ t) + Vp)
          = 0 := by
  have hVcomp : DifferentiableAt ℝ (fun s => V (φ s)) t :=
    ((hV.hasFDerivAt.comp t hφ.hasFDerivAt)).differentiableAt
  have hsq : DifferentiableAt ℝ (fun s => (∂ₜ φ s) ^ 2) t := hφd.pow 2
  have hkin : DifferentiableAt ℝ (fun s => ε * (∂ₜ φ s) ^ 2 / 2) t := by
    have h1 : DifferentiableAt ℝ (fun s => ε * (∂ₜ φ s) ^ 2) t := hsq.const_mul ε
    exact h1.mul_const (2 : ℝ)⁻¹
  have hsumD : DifferentiableAt ℝ
      (fun s => ε * (∂ₜ φ s) ^ 2 / 2 + V (φ s)) t := hkin.add hVcomp
  have hd : ∂ₜ (fun s => scalarFieldEnergyDensity ε φ V s / c ^ 2) t
      = (ε * ∂ₜ φ t * ∂ₜ (∂ₜ φ) t + Vp * ∂ₜ φ t) / c ^ 2 := by
    have hshape : (fun s => scalarFieldEnergyDensity ε φ V s / c ^ 2)
        = fun s => (c ^ 2)⁻¹
          * (ε * (∂ₜ φ s) ^ 2 / 2 + V (φ s)) := by
      funext s
      unfold scalarFieldEnergyDensity
      ring
    have hkinshape : (fun s => ε * (∂ₜ φ s) ^ 2 / 2)
        = fun s => ε / 2 * (∂ₜ φ s) ^ 2 := by
      funext s
      ring
    rw [hshape,
      Time.deriv_const_mul _ t hsumD,
      Time.deriv_add _ _ hkin hVcomp, hkinshape,
      Time.deriv_const_mul _ t hsq,
      Time.deriv_sq t hφd,
      Time.deriv_comp_hasDerivAt t hV hφ]
    field_simp
  rw [hd]
  have hsum : scalarFieldEnergyDensity ε φ V t / c ^ 2
      + scalarFieldPressure ε φ V t / c ^ 2 = ε * (∂ₜ φ t) ^ 2 / c ^ 2 := by
    unfold scalarFieldEnergyDensity scalarFieldPressure
    ring
  rw [hsum]
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    linear_combination (1 / c ^ 2) * h


/-! ## §C — the perfect-fluid stress-energy tensor -/

open Matrix

/-- **The perfect-fluid stress-energy tensor** `T_μν = (ρ + P/c²) u_μ u_ν + P g_μν`
— the outer product of the (covariant) 4-velocity `u` with itself, weighted by the
enthalpy density `ρ + P/c²`, plus the pressure times the metric.  Same structural
form as `ComplexEinstein.entropicStressTensor` (outer product `+` scalar·metric). -/
noncomputable def perfectFluidStressEnergy (ρ P c : ℝ) (u : Fin 4 → ℝ)
    (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (ρ + P / c ^ 2) • Matrix.vecMulVec u u + P • g

/-- **[Component form]** `T_μν = (ρ + P/c²)·u_μ u_ν + P·g_μν`. -/
@[simp] lemma perfectFluidStressEnergy_apply (ρ P c : ℝ) (u : Fin 4 → ℝ)
    (g : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) :
    perfectFluidStressEnergy ρ P c u g μ ν
      = (ρ + P / c ^ 2) * (u μ * u ν) + P * g μ ν := by
  simp [perfectFluidStressEnergy, Matrix.vecMulVec_apply]

/-- **[The stress-energy tensor is symmetric]** `T_μν = T_νμ` whenever the metric
is (the outer product `u⊗u` is always symmetric). -/
lemma perfectFluidStressEnergy_symm (ρ P c : ℝ) (u : Fin 4 → ℝ)
    (g : Matrix (Fin 4) (Fin 4) ℝ) (hg : gᵀ = g) :
    (perfectFluidStressEnergy ρ P c u g)ᵀ = perfectFluidStressEnergy ρ P c u g := by
  ext μ ν
  simp only [Matrix.transpose_apply, perfectFluidStressEnergy_apply]
  have hgs : g ν μ = g μ ν := by
    have h := congrFun (congrFun hg μ) ν
    rwa [Matrix.transpose_apply] at h
  rw [hgs]; ring

/-- **The comoving (covariant) 4-velocity** `u_μ = (c, 0, 0, 0)` of a fluid element
at rest in the FLRW frame; it is timelike with `u_μ u^μ = −c²`. -/
def comovingVelocity (c : ℝ) : Fin 4 → ℝ := ![c, 0, 0, 0]

/-- **The FLRW metric** `g_μν = diag(−1, a², a², a²)` (comoving diagonal gauge; the
spatial scale factor `a`, timelike signature `−+++`). -/
noncomputable def flrwMetric (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![-1, a ^ 2, a ^ 2, a ^ 2]

/-- **[The perfect fluid is diagonal in the comoving frame]
`T = diag(ρc², Pa², Pa², Pa²)`.**  In the rest frame `u_μ = (c,0,0,0)` with the
FLRW metric, the enthalpy term fills the time-time slot as the energy density
`ρc²` and the pressure fills the spatial slots as `Pa²`; all off-diagonal
components vanish (no heat flux, no anisotropic stress). -/
theorem perfectFluidStressEnergy_flrw (ρ P a c : ℝ) (hc : c ≠ 0) :
    perfectFluidStressEnergy ρ P c (comovingVelocity c) (flrwMetric a)
      = Matrix.diagonal ![ρ * c ^ 2, P * a ^ 2, P * a ^ 2, P * a ^ 2] := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [perfectFluidStressEnergy_apply, comovingVelocity, flrwMetric]
  all_goals (field_simp; ring)

/-- **[The scalar field's stress-energy tensor]** the canonical scalar field
(`ρ_φ = ½εφ̇² + V`, `p_φ = ½εφ̇² − V` of §B) has the diagonal perfect-fluid
stress-energy `diag(ρ_φc², p_φa², p_φa², p_φa²)`: `T₀₀` is the energy density,
`T_ii` the pressure times the spatial metric.  The scalar field *is* a perfect
fluid. -/
theorem scalarField_stressEnergy_diagonal (ε c a : ℝ) (φ : Time → ℝ) (V : ℝ → ℝ)
    (t : Time) (hc : c ≠ 0) :
    perfectFluidStressEnergy (scalarFieldEnergyDensity ε φ V t)
        (scalarFieldPressure ε φ V t) c (comovingVelocity c) (flrwMetric a)
      = Matrix.diagonal ![scalarFieldEnergyDensity ε φ V t * c ^ 2,
          scalarFieldPressure ε φ V t * a ^ 2,
          scalarFieldPressure ε φ V t * a ^ 2,
          scalarFieldPressure ε φ V t * a ^ 2] :=
  perfectFluidStressEnergy_flrw _ _ a c hc

/-! ## §D — the cosmological constant as a `w = −1` perfect fluid -/

/-- **The vacuum (cosmological-constant) energy density** `ρ_Λ = Λc²/(8πG)`. -/
noncomputable def vacuumEnergyDensity (Λ G c : ℝ) : ℝ := Λ * c ^ 2 / (8 * Real.pi * G)

/-- **The vacuum pressure** `P_Λ = −ρ_Λ c²`. -/
noncomputable def vacuumPressure (Λ G c : ℝ) : ℝ := -(vacuumEnergyDensity Λ G c * c ^ 2)

/-- **[The cosmological constant has equation of state `w = −1`]**
`P_Λ = −1·ρ_Λ·c²`. -/
theorem vacuum_equationOfState (Λ G c : ℝ) :
    vacuumPressure Λ G c = -1 * vacuumEnergyDensity Λ G c * c ^ 2 := by
  unfold vacuumPressure; ring

/-- **[The cosmological constant is pure vacuum stress-energy] `T_Λ = P_Λ·g = −ρ_Λc²·g`.**
Because the vacuum enthalpy density vanishes (`ρ_Λ + P_Λ/c² = 0`), the
velocity-outer-product term drops out and the stress-energy is *isotropic* — pure
metric, the same in every frame.  This is why `Λ` behaves as a `w = −1` fluid: its
stress-energy is Lorentz-invariant (Gliner 1966). -/
theorem vacuum_stressEnergy_eq_metric (Λ G c : ℝ) (u : Fin 4 → ℝ)
    (g : Matrix (Fin 4) (Fin 4) ℝ) (hc : c ≠ 0) :
    perfectFluidStressEnergy (vacuumEnergyDensity Λ G c) (vacuumPressure Λ G c) c u g
      = vacuumPressure Λ G c • g := by
  have h0 : vacuumEnergyDensity Λ G c + vacuumPressure Λ G c / c ^ 2 = 0 := by
    unfold vacuumPressure; field_simp; ring
  rw [perfectFluidStressEnergy, h0, zero_smul, zero_add]

end Cosmology.FLRW.MatterContent

end

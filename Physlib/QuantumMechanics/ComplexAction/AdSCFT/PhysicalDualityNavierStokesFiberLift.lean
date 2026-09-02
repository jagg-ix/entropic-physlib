/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
public import Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
public import Physlib.Mathematics.DimensionalScalingFunctorTower
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
public import Physlib.Mathematics.Geometry.StereographicRiemannSphere
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric

/-!
# The physical AdS/CFT dictionary as a dimensional functor, and the Navier–Stokes fiber

`AmbjornSavvidyHolographicBoundary` reduces the Regge action co-dimension-one but flags that this scaling step
is *not by itself* the physical AdS/CFT correspondence.  This file assembles the physical dictionary out of the
repository's own theorems — the pieces that *do* constitute the duality — and applies it to the 3D Navier–Stokes
problem through the radial (holographic) direction, read as a fiber over the boundary.

The five assembled pillars (each an existing repo theorem):

* **§1 symmetry** (`duality_symmetry_pillar`) — the boundary of `AdS₃` is the Riemann / Bloch sphere
  (`stereoInv_isBlochSphere`), and its conformal group `SL(2,ℂ)` double-covers the bulk Lorentz isometry as a
  homomorphism (`sl2c_toLorentzGroup_hom`): bulk isometry = boundary conformal group.
* **§2 field–operator** (`duality_fieldOperator_pillar`) — a bulk field of mass `m` is dual to a boundary
  operator of dimension `Δ` fixed by `Δ(Δ−d) = m²R²` (`massDimension_relation`), with `Δ₊+Δ₋ = d`
  (`conformalDimension_sum`).
* **§3 correlator** (`duality_correlator_pillar`) — the induced boundary two-point function is conformally
  covariant, `⟨O(λx)O(0)⟩ = λ^{−2Δ}⟨O(x)O(0)⟩` (`cftTwoPoint_scaling`).
* **§4 radial functor** (`duality_radial_functor_pillar`) — the holographic / RG direction is the
  dimensional-scaling transition; it is a *functor* (cocycle) `T_{3→4}∘T_{2→3} = T_{2→4}`
  (`scalingTransition_comp`) carrying boundary lengths to bulk lengths (`scalingTransition_dimLength`).  The
  boundary of the 3D fluid is `CFT₃`; its bulk is `AdS₄`, the `3→4` step.
* **§5 Navier–Stokes fiber** (`navierStokes_fiber_obstruction`) — the 3D enstrophy rate
  `dΩ/dt = 2(VS − νP)` decomposes as the 2D pure-dissipation base `−2νP` plus the fiber term `2·VS`: the
  vortex stretching lives *in the radial fiber* added by the lift.

## Honest scope

The **duality as an equality of two independently-defined theories** is the GKP–Witten *correspondence
postulate* — the generating-functional relation `Z_grav[φ₀] = ⟨e^{∫φ₀O}⟩_CFT` *defines* the dual operator; it
is not, and cannot be, a Lean theorem that the conjecture holds.  What is assembled here is the **dictionary**:
the matched symmetry, field–operator, correlator, and radial-functor identities, each genuinely proved.

Applied to Navier–Stokes this does **not** close the 3D problem.  On the contrary, §5 makes the obstruction
*precise*: the extra dimension the holographic lift adds — the radial fiber over the 2D boundary — is exactly
the direction carrying the vortex stretching `VS` that vanishes in 2D.  The functor lifts the geometry; the
fiber *is* the obstruction, and no amount of boundary regularity transports through it.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.PhysicalDualityNavierStokesFiberLift

open scoped MatrixGroups
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
open Physlib.Mathematics.DimensionalScaling
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect

/-! ### §1 — Symmetry: bulk isometry = boundary conformal group -/

/-- **The boundary conformal group is the bulk isometry.**  The `AdS₃` boundary is the Riemann / Bloch sphere
(`stereoInv_isBlochSphere`), and the boundary conformal group `SL(2,ℂ)` maps homomorphically onto the bulk
Lorentz isometry group (`sl2c_toLorentzGroup_hom`): the symmetry pillar of the correspondence. -/
theorem duality_symmetry_pillar (M N : SL(2, ℂ)) (w : ℂ) :
    BlochSphere (blochVectorOfBoundary w)
      ∧ Lorentz.SL2C.toLorentzGroup (M * N)
          = Lorentz.SL2C.toLorentzGroup M * Lorentz.SL2C.toLorentzGroup N :=
  ⟨stereoInv_isBlochSphere w, sl2c_toLorentzGroup_hom M N⟩

/-! ### §2 — Field–operator: the mass–dimension relation -/

/-- **The field–operator dictionary.**  A bulk field of mass `m` (`μ = m²R²`) is dual to a boundary operator of
conformal dimension `Δ` obeying `Δ(Δ−d) = μ` (`massDimension_relation`), and the two roots sum to the boundary
dimension, `Δ₊ + Δ₋ = d` (`conformalDimension_sum`). -/
theorem duality_fieldOperator_pillar (d μ : ℝ) (h : 0 ≤ (d / 2) ^ 2 + μ) :
    conformalDimension d μ * (conformalDimension d μ - d) = μ
      ∧ conformalDimension d μ + conformalDimensionMinus d μ = d :=
  ⟨massDimension_relation d μ h, conformalDimension_sum d μ⟩

/-! ### §3 — Correlator: conformal covariance of the boundary two-point function -/

/-- **The induced correlator is conformally covariant.**  The boundary two-point function sourced through the
GKP–Witten dictionary scales as `⟨O(λx)O(0)⟩ = λ^{−2Δ}⟨O(x)O(0)⟩` (`cftTwoPoint_scaling`) — the correlator
pillar. -/
theorem duality_correlator_pillar (Δ x lam : ℝ) (hlam : 0 < lam) :
    cftTwoPoint Δ (lam * x) = lam ^ (-2 * Δ) * cftTwoPoint Δ x :=
  cftTwoPoint_scaling Δ x lam hlam

/-! ### §4 — Radial functor: the holographic direction lifts boundary to bulk -/

/-- **The holographic / RG direction is a dimensional functor.**  The radial scaling transition composes as a
cocycle, `T_{3→4} ∘ T_{2→3} = T_{2→4}` (`scalingTransition_comp`) — the 2D solved boundary lifts through the 3D
level to the 4D bulk — and it carries the boundary length to the bulk length,
`T_{3→4}(L₃) = L₄` (`scalingTransition_dimLength`): the `CFT₃ → AdS₄` step under the 3D fluid. -/
theorem duality_radial_functor_pillar (a : ℝ) :
    scalingTransition 3 4 (scalingTransition 2 3 (dimLength a 2)) = scalingTransition 2 4 (dimLength a 2)
      ∧ scalingTransition 3 4 (dimLength a 3) = dimLength a 4 :=
  ⟨scalingTransition_comp (by norm_num) (by norm_num) (dimLength a 2),
    scalingTransition_dimLength a (by norm_num) 4⟩

/-! ### §5 — The Navier–Stokes fiber: the radial direction carries the vortex stretching -/

/-- **The vortex stretching lives in the radial fiber.**  The 3D enstrophy rate `dΩ/dt = 2(VS − νP)`
(`NSVortexStretchingDefect.enstrophyRate`) decomposes as the 2D pure-dissipation base `enstrophyRate 0 ν P`
(the `VS = 0` boundary, globally regular) plus the fiber term `2·VS`.  The extra dimension the holographic lift
adds is exactly the direction carrying the vortex stretching; the fiber *is* the obstruction. -/
theorem navierStokes_fiber_obstruction (VS ν P : ℝ) :
    enstrophyRate VS ν P = enstrophyRate 0 ν P + 2 * VS := by
  unfold enstrophyRate; ring

/-! ### The assembled dictionary at the 3D Navier–Stokes boundary -/

/-- **The physical AdS/CFT dictionary at the `CFT₃` boundary, with the Navier–Stokes fiber obstruction.**  One
statement assembling the five pillars for the 3D fluid (`d = 3`, boundary `CFT₃`, bulk `AdS₄`): the boundary
conformal group is the bulk isometry; the field–operator relation `Δ(Δ−3) = μ` holds; the correlator is
conformally covariant; the radial direction lifts `CFT₃` to `AdS₄` as a functor; and the 3D enstrophy rate is
the regular 2D base plus the radial-fiber vortex stretching `2·VS`.  The dictionary lifts the geometry; the
fiber carries the obstruction, so 3D regularity does not transport. -/
theorem physical_duality_navierStokes_boundary
    (M N : SL(2, ℂ)) (w : ℂ) (μ : ℝ) (hμ : 0 ≤ (3 / 2 : ℝ) ^ 2 + μ)
    (Δ x lam : ℝ) (hlam : 0 < lam) (a : ℝ) (VS ν P : ℝ) :
    (BlochSphere (blochVectorOfBoundary w)
        ∧ Lorentz.SL2C.toLorentzGroup (M * N)
            = Lorentz.SL2C.toLorentzGroup M * Lorentz.SL2C.toLorentzGroup N)
      ∧ conformalDimension 3 μ * (conformalDimension 3 μ - 3) = μ
      ∧ cftTwoPoint Δ (lam * x) = lam ^ (-2 * Δ) * cftTwoPoint Δ x
      ∧ scalingTransition 3 4 (dimLength a 3) = dimLength a 4
      ∧ enstrophyRate VS ν P = enstrophyRate 0 ν P + 2 * VS :=
  ⟨duality_symmetry_pillar M N w,
    massDimension_relation 3 μ hμ,
    duality_correlator_pillar Δ x lam hlam,
    (duality_radial_functor_pillar a).2,
    navierStokes_fiber_obstruction VS ν P⟩

/-! ### Joining 2D leaves: the foliation, the interaction, and the small-space Madelung closure

3D space assembled as an infinite stack of 2D leaves — the foliation `ℝ³ = ℝ² × ℝ` — with the categorical join
step given by the dimensional functor `T_{2→3}` (`scalingTransition_dimLength`), and each leaf carried
**information-intact** to its conformal compactification: the stereographic round-trip is the identity on the
sphere minus its pole (`stereoInv_stereoProj`) — the dual fiber spheres are the leaves' compactifications, and
nothing is lost across the mapping.  On the stack, the **interlayer interaction is exactly the fiber term**
`2·VS` (`navierStokes_fiber_obstruction`): a stack with no interlayer variation has `VS = 0` — the classical
globally regular "2½-dimensional" flows, each leaf solving 2D NS — and all coupling between leaves flows
through the stretching term.

On a **small space** the interaction is dominated *pointwise*: with the spectral gap `λ₁·Ω ≤ P` (small domain
⟹ large `λ₁`) and the Ladyzhenskaya-type interpolation `VS ≤ C·√(Ω³P)` (the functional inequality, taken as
explicit hypothesis with the domain's constant `C`), any enstrophy below the threshold `C²Ω² ≤ ν²λ₁` gives
`dΩ/dt ≤ 0` (`pointwise_threshold_confinement`) — the sub-threshold ball is forward-invariant: the pointwise
dynamical confinement the integral budget cannot supply.  For the **Madelung fluid** at the quantum viscosity
`ν_q = ℏ/2m` the threshold is `C²Ω² ≤ ℏ²λ₁/(4m²)` (`madelung_smallSpace_confinement`): the solvable ball has
radius set by `ℏ` — on a small space, the Madelung stack is solved.

Honest scope: the interpolation inequality and the spectral gap enter as explicit hypotheses (functional
inequalities of the domain, not re-derived here); the leafwise 2½D global regularity is classical context; the
threshold mechanism is the known small-data/small-domain regularity — a pointwise confinement, **not** a
resolution of the large-data 3D problem, which crosses the threshold. -/

open Physlib.Mathematics.Geometry.StereographicRiemannSphere
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms

/-- **Pointwise threshold confinement.**  Below the Ladyzhenskaya threshold `C²Ω² ≤ ν²λ₁`, with the spectral
gap `λ₁Ω ≤ P` and the interpolation `VS ≤ C√(Ω³P)`, the enstrophy rate is nonpositive: the interlayer
interaction is pointwise dominated by the friction, so the sub-threshold ball is forward-invariant. -/
theorem pointwise_threshold_confinement (VS ν P C lam1 Ω : ℝ)
    (hC : 0 ≤ C) (hν : 0 ≤ ν) (hΩ : 0 ≤ Ω) (hP : 0 ≤ P)
    (hVS : VS ≤ C * Real.sqrt (Ω ^ 3 * P))
    (hgap : lam1 * Ω ≤ P)
    (hthresh : C ^ 2 * Ω ^ 2 ≤ ν ^ 2 * lam1) :
    enstrophyRate VS ν P ≤ 0 := by
  have h1 : C ^ 2 * (Ω ^ 3 * P) ≤ (ν * P) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hthresh (mul_nonneg hΩ hP),
               mul_le_mul_of_nonneg_left hgap (mul_nonneg (sq_nonneg ν) hP)]
  have h2 : C * Real.sqrt (Ω ^ 3 * P) ≤ ν * P := by
    have hs := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC, Real.sqrt_sq (mul_nonneg hν hP)] at hs
  exact (enstrophyRate_nonpos_iff VS ν P).mpr (hVS.trans h2)

/-- **The Madelung threshold** `ν_q²·λ₁ = ℏ²λ₁/(4m²)`: at the quantum viscosity the solvable-ball radius is
set by `ℏ`. -/
theorem madelung_threshold_eq (ℏ m lam1 : ℝ) :
    (quantumKinematicViscosity ℏ m) ^ 2 * lam1 = ℏ ^ 2 * lam1 / (4 * m ^ 2) := by
  unfold quantumKinematicViscosity
  rw [div_pow]
  ring

/-- **The small-space Madelung stack is solved.**  At the quantum viscosity `ν_q = ℏ/2m`, enstrophy below the
`ℏ`-set threshold `C²Ω² ≤ ℏ²λ₁/(4m²)` has nonpositive rate: pointwise confinement for the Madelung fluid on a
small space. -/
theorem madelung_smallSpace_confinement (VS ℏ m P C lam1 Ω : ℝ)
    (hℏ : 0 ≤ ℏ) (hm : 0 < m) (hC : 0 ≤ C) (hΩ : 0 ≤ Ω) (hP : 0 ≤ P)
    (hVS : VS ≤ C * Real.sqrt (Ω ^ 3 * P))
    (hgap : lam1 * Ω ≤ P)
    (hthresh : C ^ 2 * Ω ^ 2 ≤ ℏ ^ 2 * lam1 / (4 * m ^ 2)) :
    enstrophyRate VS (quantumKinematicViscosity ℏ m) P ≤ 0 := by
  refine pointwise_threshold_confinement VS _ P C lam1 Ω hC ?_ hΩ hP hVS hgap ?_
  · unfold quantumKinematicViscosity
    exact div_nonneg hℏ (by linarith)
  · rw [madelung_threshold_eq]
    exact hthresh

/-- **The foliation synthesis.**  The construction in one statement: the leaf compactification is
information-intact (the stereographic round-trip is the identity on the sphere minus its pole); the
categorical join step carries the leaf scale to the bulk scale (`T_{2→3}`); the interlayer interaction is
exactly the fiber term `2·VS`; and on a small space the Madelung stack is pointwise confined below the
`ℏ`-set threshold. -/
theorem foliation_madelung_synthesis
    (X Y Z : ℝ) (hsph : X ^ 2 + Y ^ 2 + Z ^ 2 = 1) (hN : Z ≠ 1) (a : ℝ)
    (VS ℏ m P C lam1 Ω : ℝ)
    (hℏ : 0 ≤ ℏ) (hm : 0 < m) (hC : 0 ≤ C) (hΩ : 0 ≤ Ω) (hP : 0 ≤ P)
    (hVS : VS ≤ C * Real.sqrt (Ω ^ 3 * P))
    (hgap : lam1 * Ω ≤ P)
    (hthresh : C ^ 2 * Ω ^ 2 ≤ ℏ ^ 2 * lam1 / (4 * m ^ 2)) :
    stereoInv (stereoProj X Y Z) = (X, Y, Z)
      ∧ scalingTransition 2 3 (dimLength a 2) = dimLength a 3
      ∧ enstrophyRate VS (quantumKinematicViscosity ℏ m) P
          = enstrophyRate 0 (quantumKinematicViscosity ℏ m) P + 2 * VS
      ∧ enstrophyRate VS (quantumKinematicViscosity ℏ m) P ≤ 0 :=
  ⟨stereoInv_stereoProj X Y Z hsph hN,
    scalingTransition_dimLength a (by norm_num) 3,
    navierStokes_fiber_obstruction VS _ P,
    madelung_smallSpace_confinement VS ℏ m P C lam1 Ω hℏ hm hC hΩ hP hVS hgap hthresh⟩

/-! ### The confinement criterion is dilaton-critical; the budget is dilaton-supercritical

The Navier–Stokes zoom `u_λ(x,t) = λ·u(λx, λ²t)` is a **dilaton-group action** — the flow
`λ = e^s = dilationFlow 1 s` of `EntropicTime.ScaleDilationLogMetric` — under which the cascade quantities
carry the classical scaling weights: `Ω ↦ λΩ` (weight 1), `λ₁ ↦ λ²λ₁` (2), `P ↦ λ³P` (3), `VS ↦ λ³VS` (3),
`E ↦ λ⁻¹E` (−1), with `ν` invariant.  The exact scalar covariances:

* **all three confinement hypotheses are weight-0** — threshold (`threshold_dilaton_invariant`), spectral gap
  (`gap_dilaton_invariant`), interpolation (`interpolation_dilaton_invariant`) hold at one zoom iff at every
  zoom: the pointwise criterion is *scaling-critical*, the only kind of statement that can chase a blow-up
  down the scales;
* **the enstrophy rate is weight-3 covariant** (`enstrophyRate_dilaton_covariant`) — in particular its *sign*
  is zoom-invariant, so the confinement conclusion is critical too;
* **the energy budget is weight-(−1)** (`energy_supercritical`): under zoom-in (`λ > 1`) the budget strictly
  shrinks — supercritical, dying exactly where a singularity would live.

`confinement_criterion_scaling_critical` bundles the five at `λ = dilationFlow 1 s`.  This is the
dilaton-group reading of the budget-blindness: blow-up is a zoom-in escape (the dilaton excursion of the Clay
re-evaluation), the weight-(−1) budget cannot follow it, and only weight-0 (critical) criteria — like the
threshold — survive every zoom.  The Millennium gap is the gap between weight-(−1) control and a weight-0
need.  Honest scope: the weights are the classical NS scaling, realized here as exact scalar covariances;
nothing new is estimated. -/

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric

/-- **The enstrophy rate is weight-3 covariant** under the dilaton action: `VS ↦ λ³VS`, `P ↦ λ³P` gives
`rate ↦ λ³·rate` — in particular the *sign* of the rate is zoom-invariant. -/
theorem enstrophyRate_dilaton_covariant (VS ν P lam : ℝ) :
    enstrophyRate (lam ^ 3 * VS) ν (lam ^ 3 * P) = lam ^ 3 * enstrophyRate VS ν P := by
  unfold enstrophyRate
  ring

/-- **The Ladyzhenskaya threshold is weight-0 (dilaton-invariant)**: with `Ω ↦ λΩ`, `λ₁ ↦ λ²λ₁`, the
condition `C²Ω² ≤ ν²λ₁` holds at one zoom iff at every zoom. -/
theorem threshold_dilaton_invariant (C ν Ω lam1 lam : ℝ) (hlam : 0 < lam) :
    C ^ 2 * (lam * Ω) ^ 2 ≤ ν ^ 2 * (lam ^ 2 * lam1) ↔ C ^ 2 * Ω ^ 2 ≤ ν ^ 2 * lam1 := by
  rw [show C ^ 2 * (lam * Ω) ^ 2 = lam ^ 2 * (C ^ 2 * Ω ^ 2) from by ring,
    show ν ^ 2 * (lam ^ 2 * lam1) = lam ^ 2 * (ν ^ 2 * lam1) from by ring]
  exact ⟨fun h => le_of_mul_le_mul_left h (by positivity),
    fun h => mul_le_mul_of_nonneg_left h (by positivity)⟩

/-- **The spectral gap is weight-0 (dilaton-invariant)**: `λ₁Ω ≤ P` holds at one zoom iff at every zoom. -/
theorem gap_dilaton_invariant (lam1 Ω P lam : ℝ) (hlam : 0 < lam) :
    (lam ^ 2 * lam1) * (lam * Ω) ≤ lam ^ 3 * P ↔ lam1 * Ω ≤ P := by
  rw [show (lam ^ 2 * lam1) * (lam * Ω) = lam ^ 3 * (lam1 * Ω) from by ring]
  exact ⟨fun h => le_of_mul_le_mul_left h (by positivity),
    fun h => mul_le_mul_of_nonneg_left h (by positivity)⟩

/-- **The interpolation is weight-0 (dilaton-invariant)**: `VS ≤ C√(Ω³P)` holds at one zoom iff at every
zoom (both sides carry weight 3). -/
theorem interpolation_dilaton_invariant (VS C Ω P lam : ℝ) (hlam : 0 < lam) :
    lam ^ 3 * VS ≤ C * Real.sqrt ((lam * Ω) ^ 3 * (lam ^ 3 * P))
      ↔ VS ≤ C * Real.sqrt (Ω ^ 3 * P) := by
  rw [show (lam * Ω) ^ 3 * (lam ^ 3 * P) = (lam ^ 3) ^ 2 * (Ω ^ 3 * P) from by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
    show C * (lam ^ 3 * Real.sqrt (Ω ^ 3 * P)) = lam ^ 3 * (C * Real.sqrt (Ω ^ 3 * P)) from by ring]
  exact ⟨fun h => le_of_mul_le_mul_left h (by positivity),
    fun h => mul_le_mul_of_nonneg_left h (by positivity)⟩

/-- **The energy budget is weight-(−1) — supercritical.**  Under zoom-in (`λ > 1`) the budget strictly
shrinks: `λ⁻¹E < E`.  The budget dies exactly where a singularity would live. -/
theorem energy_supercritical (E lam : ℝ) (hE : 0 < E) (hlam : 1 < lam) :
    lam⁻¹ * E < E := by
  rw [inv_mul_eq_div, div_lt_iff₀ (by linarith)]
  nlinarith [mul_pos hE (sub_pos.2 hlam)]

/-- **The criticality dichotomy at the dilaton flow.**  At `λ = dilationFlow 1 s` (zoom-in for `s > 0`): the
threshold, gap, and interpolation are weight-0 (hold at one zoom iff at every zoom), the enstrophy rate is
weight-3 covariant (sign zoom-invariant), and the energy budget is weight-(−1) (strictly shrinking).  The
pointwise confinement criterion is scaling-critical; the integral budget is supercritical — the dilaton-group
form of why the budget cannot decide regularity and a criterion of exactly this shape could. -/
theorem confinement_criterion_scaling_critical (s VS C ν Ω lam1 P E : ℝ)
    (hs : 0 < s) (hE : 0 < E) :
    (C ^ 2 * (dilationFlow 1 s * Ω) ^ 2 ≤ ν ^ 2 * ((dilationFlow 1 s) ^ 2 * lam1)
        ↔ C ^ 2 * Ω ^ 2 ≤ ν ^ 2 * lam1)
      ∧ (((dilationFlow 1 s) ^ 2 * lam1) * (dilationFlow 1 s * Ω) ≤ (dilationFlow 1 s) ^ 3 * P
        ↔ lam1 * Ω ≤ P)
      ∧ ((dilationFlow 1 s) ^ 3 * VS
            ≤ C * Real.sqrt ((dilationFlow 1 s * Ω) ^ 3 * ((dilationFlow 1 s) ^ 3 * P))
        ↔ VS ≤ C * Real.sqrt (Ω ^ 3 * P))
      ∧ enstrophyRate ((dilationFlow 1 s) ^ 3 * VS) ν ((dilationFlow 1 s) ^ 3 * P)
          = (dilationFlow 1 s) ^ 3 * enstrophyRate VS ν P
      ∧ (dilationFlow 1 s)⁻¹ * E < E := by
  have hlam : 0 < dilationFlow 1 s := dilationFlow_pos 1 s
  have hlam1 : 1 < dilationFlow 1 s := by
    unfold dilationFlow
    rw [one_mul, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr hs
  exact ⟨threshold_dilaton_invariant C ν Ω lam1 _ hlam,
    gap_dilaton_invariant lam1 Ω P _ hlam,
    interpolation_dilaton_invariant VS C Ω P _ hlam,
    enstrophyRate_dilaton_covariant VS ν P _,
    energy_supercritical E _ hE hlam1⟩

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.PhysicalDualityNavierStokesFiberLift

end

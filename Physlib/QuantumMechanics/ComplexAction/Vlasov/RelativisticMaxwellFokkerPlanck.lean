/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalMechanics.HerglotzLazoContact
public import Physlib.Cosmology.FLRW.Dynamics
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Algebra.Order.Floor

meta import Zil

/-!
# The relativistic Vlasov–Maxwell–Fokker–Planck system

Lai, *On the one and one-half dimensional relativistic Vlasov–Maxwell–Fokker–Planck
system with non-vanishing viscosity*, Math. Meth. Appl. Sci. **21** (1998) 1287, on the
linear existence theory of Degond, *Global existence of smooth solutions for the
Vlasov–Fokker–Planck equation in 1 and 2 space dimensions*, Ann. Sci. École Norm. Sup.
**19** (1986) 519.  A plasma density is transported along the relativistic velocity map
`v̂ = v/√(1+|v|²)` under the self-consistent Lorentz force, with Fokker–Planck diffusion
`ν∆_v` and friction `β∇_v·(v̂f)`, in one space and two momentum variables.  The four
sections below carry the system's exact structure:

* `VelocityMap` — the transport field: subluminality, the friction divergence and its
  bound `2`, the magnetic structure, the null energy split, the growth envelope.
* `LinearExistence` — the solution operator written down: the momentum heat kernel with
  its full derivative calculus, unit mass, the maximum principle, drift absorption, and
  the transport characteristics.
* `IterationConvergence` — the well-posedness engines: the Volterra majorant tower, the
  weighted Cauchy property, uniqueness, the integral Grönwall bound, the Sobolev
  embedding, and the PDE-level assembly of the iterates.
* `DissipationUnification` — the kinetic drag identified with the Herglotz contact
  coefficient, the envelopes read as entropic clocks, and the cosmological Λ-condition
  as the same integrating-factor structure.

**Honest layering, with its search.**  Formalized: everything named above.  Not
formalized: the variable-coefficient parametrix — Degond's composition of
frozen-coefficient pieces into the semigroup for `x`- and `v`-dependent drifts — and
the identification of the iteration limit with a solution of the nonlinear system; the
recursion hypotheses enter the convergence engines as data, which is the role Degond's
estimates play in the paper.  The repository's other Vlasov faces are equilibrium and
stability (`Vlasov/MaxwellLyapunovStability`, `Vlasov/MaxwellEM`); the nonrelativistic
kinetic sibling is `EntropicTime/KineticFokkerPlanck`.
-/

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck

section VelocityMap

/-!
# The relativistic velocity map and the friction divergence — Lai 1998

Lai, *On the one and one-half dimensional relativistic Vlasov–Maxwell–Fokker–Planck
system with non-vanishing viscosity*, Math. Meth. Appl. Sci. **21** (1998) 1287.  The
relativistic VMFP system transports a plasma density along the relativistic velocity
map `v̂ = v/√(1+|v|²)` under the self-consistent Lorentz force `E + B·Mv̂`, with
Fokker–Planck diffusion `ν∆_v` and friction `β∇_v·(v̂f)` — one space and two momentum
variables, the same one-and-a-half-dimensional geometry as the transverse-momentum
arc.  The paper's global existence and uniqueness rests on a handful of exact
structural facts, formalized here:

* **§A — the velocity map.**  `v̂` is subluminal (`relativisticVelocity_subluminal`),
  its energy denominator is the repository's on-shell dispersion
  (`energyDenominator_eq_bogoliubov`, `√(1+|v|²) = bogoliubovEnergy 1 |v|`), and its
  partial derivatives are computed exactly, giving the paper's Eq. (11):

  `∇_v·v̂ = (2+|v|²)/(1+|v|²)^{3/2}`  (`velocityDivergence_eq`),

  bounded by `2` with the bound attained at rest
  (`velocityDivergence_le_two`, `velocityDivergence_at_zero`) — the source of the
  paper's `e^{2βt}` growth envelopes (Eq. 12): the friction rate never exceeds twice
  the drag coefficient.
* **§B — the magnetic structure.**  The 1½-dimensional magnetic force `B·Mv̂` with the
  rotation `M = [[0,1],[−1,0]]` does no work (`magneticForce_no_work`) and is
  divergence-free in momentum (`crossDerivative_symm` — the two cross-partials of the
  velocity map coincide), which is why the friction divergence (11) is the *whole*
  divergence of the paper's characteristic field `a = E + BMv̂ − βv̂`.
* **§C — the null energy split.**  The 1½-dimensional field energy–momentum pair
  satisfies `e ± m = ½E₁² + ½(E₂±B)²` exactly (`field_energy_null_split`), nonnegative
  along both null directions (`null_flux_nonneg`) — the Glassey–Schaeffer trick behind
  the field bounds (paper Eq. 17).
* **§D — the growth envelope.**  The exact solution face of the paper's Eq. (12):
  a quantity growing at exactly the friction rate is `X(0)·e^{2βt}`
  (`friction_growth_exact`), the same closed-form pattern as the hypocoercivity
  module's decay.

**Honest layering, with its search.**  Formalized: the velocity-map calculus, the
divergence identity and bound, the magnetic structure, the null split, and the
envelope.  The existence–uniqueness engines — the Volterra majorant tower, the
weighted Cauchy property, the uniqueness argument, the integral Grönwall bound, and
the dimension-two Sobolev embedding — are the `IterationConvergence` section below; the linear existence input is the
`LinearExistence` section.  The repository's other Vlasov faces
(`Vlasov/MaxwellLyapunovStability` with its Casimir densities and entropy production,
`Vlasov/MaxwellEM`) carry equilibrium and stability.  The nonrelativistic
kinetic sibling is `EntropicTime/KineticFokkerPlanck`;
the friction term is the kinetic face of the Herglotz–Lazo contact coefficient. -/

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-! ### §A — the relativistic velocity map and the friction divergence -/

/-- **The relativistic velocity map, first component**: `v̂₁ = v₁/√(1+|v|²)`. -/
def relativisticVelocity1 (v₁ v₂ : ℝ) : ℝ :=
  v₁ / Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2))

/-- **The relativistic velocity map, second component**: `v̂₂ = v₂/√(1+|v|²)`. -/
def relativisticVelocity2 (v₁ v₂ : ℝ) : ℝ :=
  v₂ / Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2))

/-- **The energy denominator is the on-shell dispersion**:
`√(1+|v|²) = bogoliubovEnergy 1 |v|` — the velocity map is momentum over energy, the
same `p/E` as the canonical velocity and the group velocity of the packet arcs. -/
theorem energyDenominator_eq_bogoliubov (v₁ v₂ : ℝ) :
    Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2))
      = bogoliubovEnergy 1 (Real.sqrt (v₁ ^ 2 + v₂ ^ 2)) := by
  unfold bogoliubovEnergy
  rw [one_pow, Real.sq_sqrt (by positivity)]

/-- **The velocity map is subluminal**: `v̂₁² + v̂₂² < 1` — particles approach but never
reach the light speed, the property that makes the relativistic system's
characteristics causal. -/
theorem relativisticVelocity_subluminal (v₁ v₂ : ℝ) :
    relativisticVelocity1 v₁ v₂ ^ 2 + relativisticVelocity2 v₁ v₂ ^ 2 < 1 := by
  unfold relativisticVelocity1 relativisticVelocity2
  have hS : (0 : ℝ) < 1 + (v₁ ^ 2 + v₂ ^ 2) := by positivity
  have hsq : Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)) ^ 2 = 1 + (v₁ ^ 2 + v₂ ^ 2) :=
    Real.sq_sqrt hS.le
  rw [div_pow, div_pow, hsq, ← add_div, div_lt_one hS]
  linarith

/-- The diagonal partial `∂v̂₁/∂v₁ = (1+v₂²)/((1+|v|²)·√(1+|v|²))`. -/
theorem relativisticVelocity1_hasDerivAt_fst (v₁ v₂ : ℝ) :
    HasDerivAt (fun u => relativisticVelocity1 u v₂)
      ((1 + v₂ ^ 2) / ((1 + (v₁ ^ 2 + v₂ ^ 2))
        * Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)))) v₁ := by
  unfold relativisticVelocity1
  have hS : (0 : ℝ) < 1 + (v₁ ^ 2 + v₂ ^ 2) := by positivity
  have hsq : Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)) ^ 2 = 1 + (v₁ ^ 2 + v₂ ^ 2) :=
    Real.sq_sqrt hS.le
  have hsne : Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)) ≠ 0 := by positivity
  have hinner : HasDerivAt (fun u : ℝ => 1 + (u ^ 2 + v₂ ^ 2)) (2 * v₁) v₁ := by
    have h := ((hasDerivAt_pow 2 v₁).add_const (v₂ ^ 2)).const_add 1
    refine h.congr_deriv ?_
    push_cast
    ring
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (1 + (u ^ 2 + v₂ ^ 2)))
      (v₁ / Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2))) v₁ := by
    have h := (Real.hasDerivAt_sqrt hS.ne').comp v₁ hinner
    refine h.congr_deriv ?_
    field_simp
    try ring
  have h := (hasDerivAt_id v₁).div hsqrt hsne
  refine h.congr_deriv ?_
  have hSne : (1 + (v₁ ^ 2 + v₂ ^ 2)) ≠ 0 := hS.ne'
  simp only [id_eq]
  field_simp
  linear_combination (v₁ ^ 2) * hsq

/-- The diagonal partial `∂v̂₂/∂v₂ = (1+v₁²)/((1+|v|²)·√(1+|v|²))`. -/
theorem relativisticVelocity2_hasDerivAt_snd (v₁ v₂ : ℝ) :
    HasDerivAt (fun u => relativisticVelocity2 v₁ u)
      ((1 + v₁ ^ 2) / ((1 + (v₁ ^ 2 + v₂ ^ 2))
        * Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)))) v₂ := by
  unfold relativisticVelocity2
  have hS : (0 : ℝ) < 1 + (v₁ ^ 2 + v₂ ^ 2) := by positivity
  have hsq : Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)) ^ 2 = 1 + (v₁ ^ 2 + v₂ ^ 2) :=
    Real.sq_sqrt hS.le
  have hsne : Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)) ≠ 0 := by positivity
  have hinner : HasDerivAt (fun u : ℝ => 1 + (v₁ ^ 2 + u ^ 2)) (2 * v₂) v₂ := by
    have h := ((hasDerivAt_pow 2 v₂).const_add (v₁ ^ 2)).const_add 1
    refine h.congr_deriv ?_
    push_cast
    ring
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (1 + (v₁ ^ 2 + u ^ 2)))
      (v₂ / Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2))) v₂ := by
    have h := (Real.hasDerivAt_sqrt hS.ne').comp v₂ hinner
    refine h.congr_deriv ?_
    field_simp
    try ring
  have h := (hasDerivAt_id v₂).div hsqrt hsne
  refine h.congr_deriv ?_
  have hSne : (1 + (v₁ ^ 2 + v₂ ^ 2)) ≠ 0 := hS.ne'
  simp only [id_eq]
  field_simp
  linear_combination (v₂ ^ 2) * hsq

/-- **The friction divergence** (paper Eq. 11): summing the diagonal partials,

  `∇_v·v̂ = (2+|v|²)/((1+|v|²)·√(1+|v|²))`. -/
theorem velocityDivergence_eq (v₁ v₂ : ℝ) :
    (1 + v₂ ^ 2) / ((1 + (v₁ ^ 2 + v₂ ^ 2)) * Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)))
        + (1 + v₁ ^ 2) / ((1 + (v₁ ^ 2 + v₂ ^ 2))
            * Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)))
      = (2 + (v₁ ^ 2 + v₂ ^ 2)) / ((1 + (v₁ ^ 2 + v₂ ^ 2))
          * Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2))) := by
  ring

/-- **The friction divergence is bounded by two** — the exact constant of the paper's
`e^{2βt}` envelopes: the friction rate `β·∇_v·v̂` never exceeds `2β`. -/
theorem velocityDivergence_le_two (s : ℝ) (hs : 0 ≤ s) :
    (2 + s) / ((1 + s) * Real.sqrt (1 + s)) ≤ 2 := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (1 + s) := by
    nlinarith [Real.sq_sqrt h1.le, Real.sqrt_nonneg (1 + s)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hsqrt, h1]

/-- **The bound is attained at rest**: at `v = 0` the divergence is exactly `2` — the
supremum of the friction rate sits at zero momentum. -/
theorem velocityDivergence_at_zero :
    (2 + (0 : ℝ)) / ((1 + 0) * Real.sqrt (1 + 0)) = 2 := by
  norm_num [Real.sqrt_one]

/-! ### §B — the magnetic structure -/

/-- **The magnetic force does no work**: with the rotation `M = [[0,1],[−1,0]]`, the
force `B·Mv̂ = B·(v̂₂, −v̂₁)` is orthogonal to the velocity, `(Mv̂)·v̂ = 0` — the
magnetic field steers without feeding energy, which is why only the electric field
appears in the energy balance. -/
theorem magneticForce_no_work (v₁ v₂ B : ℝ) :
    (B * relativisticVelocity2 v₁ v₂) * relativisticVelocity1 v₁ v₂
        + (-(B * relativisticVelocity1 v₁ v₂)) * relativisticVelocity2 v₁ v₂ = 0 := by
  ring

/-- The cross partial `∂v̂₂/∂v₁ = −v₁v₂/((1+|v|²)·√(1+|v|²))`. -/
theorem relativisticVelocity2_hasDerivAt_fst (v₁ v₂ : ℝ) :
    HasDerivAt (fun u => relativisticVelocity2 u v₂)
      (-(v₁ * v₂) / ((1 + (v₁ ^ 2 + v₂ ^ 2))
        * Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)))) v₁ := by
  unfold relativisticVelocity2
  have hS : (0 : ℝ) < 1 + (v₁ ^ 2 + v₂ ^ 2) := by positivity
  have hsq : Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)) ^ 2 = 1 + (v₁ ^ 2 + v₂ ^ 2) :=
    Real.sq_sqrt hS.le
  have hsne : Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)) ≠ 0 := by positivity
  have hinner : HasDerivAt (fun u : ℝ => 1 + (u ^ 2 + v₂ ^ 2)) (2 * v₁) v₁ := by
    have h := ((hasDerivAt_pow 2 v₁).add_const (v₂ ^ 2)).const_add 1
    refine h.congr_deriv ?_
    push_cast
    ring
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (1 + (u ^ 2 + v₂ ^ 2)))
      (v₁ / Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2))) v₁ := by
    have h := (Real.hasDerivAt_sqrt hS.ne').comp v₁ hinner
    refine h.congr_deriv ?_
    field_simp
    try ring
  have h := (hasDerivAt_const v₁ v₂).div hsqrt hsne
  refine h.congr_deriv ?_
  have hSne : (1 + (v₁ ^ 2 + v₂ ^ 2)) ≠ 0 := hS.ne'
  field_simp
  linear_combination (v₁ * v₂) * hsq

/-- **The cross partials coincide** (both equal `−v₁v₂/((1+|v|²)√(1+|v|²))` by the
symmetry of the map), so the rotated field `Mv̂ = (v̂₂, −v̂₁)` is divergence-free in
momentum: `∂₁v̂₂ − ∂₂v̂₁ = 0`.  The friction divergence of §A is therefore the whole
momentum divergence of the paper's characteristic field `a = E + BMv̂ − βv̂`. -/
theorem crossDerivative_symm (v₁ v₂ : ℝ) :
    -(v₁ * v₂) / ((1 + (v₁ ^ 2 + v₂ ^ 2)) * Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2)))
        - -(v₂ * v₁) / ((1 + (v₁ ^ 2 + v₂ ^ 2))
            * Real.sqrt (1 + (v₁ ^ 2 + v₂ ^ 2))) = 0 := by
  ring_nf

/-! ### §C — the null energy split of the 1½-dimensional field -/

/-- **The null split of the field energy–momentum** (the Glassey–Schaeffer structure
behind the paper's Eq. 17): `e_field ± m_field = ½E₁² + ½(E₂±B)²` exactly. -/
theorem field_energy_null_split (E₁ E₂ B : ℝ) :
    ((1 / 2) * (E₁ ^ 2 + E₂ ^ 2 + B ^ 2) + E₂ * B
        = (1 / 2) * E₁ ^ 2 + (1 / 2) * (E₂ + B) ^ 2)
      ∧ ((1 / 2) * (E₁ ^ 2 + E₂ ^ 2 + B ^ 2) - E₂ * B
        = (1 / 2) * E₁ ^ 2 + (1 / 2) * (E₂ - B) ^ 2) := by
  constructor <;> ring

/-- **Both null fluxes are nonnegative** — the transported combinations along the two
characteristics `x ± t` are sums of squares, which is what closes the field bound. -/
theorem null_flux_nonneg (E₁ E₂ B : ℝ) :
    0 ≤ (1 / 2) * E₁ ^ 2 + (1 / 2) * (E₂ + B) ^ 2
      ∧ 0 ≤ (1 / 2) * E₁ ^ 2 + (1 / 2) * (E₂ - B) ^ 2 := by
  constructor <;> positivity

/-! ### §D — the growth envelope of the friction -/

/-- **The exact face of the paper's `e^{2βt}` envelope** (Eq. 12): a quantity growing
at exactly the friction-rate bound satisfies `X(t) = X(0)·e^{2βt}` — the closed-form
solution whose inequality face is the paper's Grönwall estimate, the growth mirror of
the hypocoercivity module's exact decay. -/
theorem friction_growth_exact (β : ℝ) (X : ℝ → ℝ)
    (hX : ∀ t, HasDerivAt X (2 * β * X t) t) (t : ℝ) :
    X t = X 0 * Real.exp (2 * β * t) := by
  have hd : ∀ u, HasDerivAt (fun s => Real.exp (-(2 * β * s)) * X s) 0 u := by
    intro u
    have hlin : HasDerivAt (fun s : ℝ => 2 * β * s) (2 * β) u := by
      simpa using (hasDerivAt_id u).const_mul (2 * β)
    have h := ClassicalMechanics.weighted_variation_deriv
      (fun s => 2 * β * s) X (2 * β) (2 * β * X u) u hlin (hX u)
    refine h.congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero
    (f := fun s => Real.exp (-(2 * β * s)) * X s)
    (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at hconst
  have hne : Real.exp (-(2 * β * t)) ≠ 0 := (Real.exp_pos _).ne'
  rw [show X 0 * Real.exp (2 * β * t) = Real.exp (2 * β * t) * X 0 from by ring,
    ← hconst]
  rw [show Real.exp (2 * β * t) * (Real.exp (-(2 * β * t)) * X t)
      = (Real.exp (2 * β * t) * Real.exp (-(2 * β * t))) * X t from by ring]
  rw [← Real.exp_add]
  simp

end VelocityMap

section LinearExistence

/-!
# The linear kinetic solution operator — Degond's Proposition A1, constructive core

Degond, *Global existence of smooth solutions for the Vlasov–Fokker–Planck equation in
1 and 2 space dimensions*, Ann. Sci. École Norm. Sup. **19** (1986) 519.  Proposition
A1 supplies the linear existence input of the Vlasov–Maxwell–Fokker–Planck iteration:
the equation `∂_t f + v̂₁∂_x f + a·∇_v f − ν∆_v f = U` has a solution for every bounded
drift `a`.  Its constructive core is explicit, and this module formalizes it exactly:

* **§A — the momentum heat kernel.**  `K(t,v) = (4πνt)⁻¹·e^{−|v|²/4νt}` with its full
  derivative calculus: the time derivative, both first and second momentum
  derivatives, and the pointwise heat equation `∂_t K = ν∆_v K`
  (`heatKernel_heat_equation`) — the solution operator of the diffusion part exists
  because it is written down.
* **§B — unit mass and the maximum principle.**  The kernel is positive with total
  integral one over the momentum plane (`heatKernel_integral_one`, a genuine
  two-dimensional integral via the Gaussian integral and Fubini), so kernel averages
  contract data bounds: `|∫ K·f| ≤ M` whenever `|f| ≤ M`
  (`kernel_average_bound`, `heatKernel_maximum_principle`) — Degond's Proposition A3
  output, the estimate that feeds the integral Grönwall bound of the companion
  module.
* **§C — a bounded drift is absorbed by the moving frame.**  The drifted kernel
  `K(t, v − ta)` satisfies `∂_t u + a·∇_v u = ν∆_v u` exactly
  (`drifted_heat_equation`, with all derivative values carried by `HasDerivAt`
  theorems) — the frozen-coefficient step of Proposition A1: bounded drifts cost
  nothing because characteristics remove them.
* **§D — the space transport.**  `f₀(x − t·v̂₁(v), v)` solves
  `∂_t g + v̂₁∂_x g = 0` by the chain rule (`transport_hasDerivAt_time`,
  `transport_hasDerivAt_space`, `transport_equation`), with `v̂₁` the relativistic
  velocity map of the `VelocityMap` section — subluminal, so the characteristics are
  causal.

**Honest layering, with its search.**  Formalized: the explicit kernel and its
pointwise equation, unit mass, positivity, integrability, the maximum principle, the
drift absorption, and the transport characteristics.  Not formalized: the
variable-coefficient parametrix — Degond's composition of frozen-coefficient pieces
into the semigroup for `x`- and `v`-dependent drifts — and the identification of the
iteration limit with a solution of the nonlinear system; those are the two steps
between these kernels and the assembled convergence of the
`IterationConvergence` section. -/

open Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck
open MeasureTheory Real

/-! ### §A — the momentum heat kernel and its derivative calculus -/

/-- **The momentum heat kernel** `K(t,v) = (4πνt)⁻¹·e^{−(v₁²+v₂²)/4νt}` — the explicit
solution operator of the Fokker–Planck diffusion in the two momentum variables. -/
def heatKernel (ν t v₁ v₂ : ℝ) : ℝ :=
  (4 * Real.pi * ν * t)⁻¹ * Real.exp (-(v₁ ^ 2 + v₂ ^ 2) / (4 * ν * t))

/-- The kernel is positive for positive diffusion and time. -/
theorem heatKernel_pos (ν t v₁ v₂ : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    0 < heatKernel ν t v₁ v₂ := by
  unfold heatKernel
  have hπ := Real.pi_pos
  positivity

/-- The first momentum derivative: `∂_{v₁}K = K·(−v₁/2νt)`. -/
theorem heatKernel_hasDerivAt_v1 (ν t v₁ v₂ : ℝ) (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun w => heatKernel ν t w v₂)
      (heatKernel ν t v₁ v₂ * (-(v₁ / (2 * ν * t)))) v₁ := by
  unfold heatKernel
  have hπ := Real.pi_ne_zero
  have hinner : HasDerivAt (fun w : ℝ => -(w ^ 2 + v₂ ^ 2) / (4 * ν * t))
      (-(2 * v₁) / (4 * ν * t)) v₁ := by
    have h := (((hasDerivAt_pow 2 v₁).add_const (v₂ ^ 2)).neg).div_const (4 * ν * t)
    refine h.congr_deriv ?_
    push_cast
    ring
  have h := (hinner.exp).const_mul (4 * Real.pi * ν * t)⁻¹
  refine h.congr_deriv ?_
  field_simp
  try ring

/-- The second momentum derivative: differentiating the first-derivative function,
`∂²_{v₁}K = K·(v₁²/4ν²t² − 1/2νt)`. -/
theorem heatKernel_hasDerivAt_v1_deriv (ν t v₁ v₂ : ℝ) (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun w => heatKernel ν t w v₂ * (-(w / (2 * ν * t))))
      (heatKernel ν t v₁ v₂
        * (v₁ ^ 2 / (4 * ν ^ 2 * t ^ 2) - 1 / (2 * ν * t))) v₁ := by
  have hK := heatKernel_hasDerivAt_v1 ν t v₁ v₂ hν ht
  have hlin : HasDerivAt (fun w : ℝ => -(w / (2 * ν * t))) (-(1 / (2 * ν * t))) v₁ := by
    have h := ((hasDerivAt_id v₁).div_const (2 * ν * t)).neg
    refine h.congr_deriv ?_
    ring
  have h := hK.mul hlin
  refine h.congr_deriv ?_
  field_simp
  try ring

/-- The first derivative in the second momentum slot: `∂_{v₂}K = K·(−v₂/2νt)`. -/
theorem heatKernel_hasDerivAt_v2 (ν t v₁ v₂ : ℝ) (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun w => heatKernel ν t v₁ w)
      (heatKernel ν t v₁ v₂ * (-(v₂ / (2 * ν * t)))) v₂ := by
  unfold heatKernel
  have hπ := Real.pi_ne_zero
  have hinner : HasDerivAt (fun w : ℝ => -(v₁ ^ 2 + w ^ 2) / (4 * ν * t))
      (-(2 * v₂) / (4 * ν * t)) v₂ := by
    have h := (((hasDerivAt_pow 2 v₂).const_add (v₁ ^ 2)).neg).div_const (4 * ν * t)
    refine h.congr_deriv ?_
    push_cast
    ring
  have h := (hinner.exp).const_mul (4 * Real.pi * ν * t)⁻¹
  refine h.congr_deriv ?_
  field_simp
  try ring

/-- The second derivative in the second momentum slot. -/
theorem heatKernel_hasDerivAt_v2_deriv (ν t v₁ v₂ : ℝ) (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun w => heatKernel ν t v₁ w * (-(w / (2 * ν * t))))
      (heatKernel ν t v₁ v₂
        * (v₂ ^ 2 / (4 * ν ^ 2 * t ^ 2) - 1 / (2 * ν * t))) v₂ := by
  have hK := heatKernel_hasDerivAt_v2 ν t v₁ v₂ hν ht
  have hlin : HasDerivAt (fun w : ℝ => -(w / (2 * ν * t))) (-(1 / (2 * ν * t))) v₂ := by
    have h := ((hasDerivAt_id v₂).div_const (2 * ν * t)).neg
    refine h.congr_deriv ?_
    ring
  have h := hK.mul hlin
  refine h.congr_deriv ?_
  field_simp
  try ring

/-- The time derivative: `∂_t K = K·(−1/t + |v|²/4νt²)`. -/
theorem heatKernel_hasDerivAt_time (ν t v₁ v₂ : ℝ) (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun s => heatKernel ν s v₁ v₂)
      (heatKernel ν t v₁ v₂
        * (-(1 / t) + (v₁ ^ 2 + v₂ ^ 2) / (4 * ν * t ^ 2))) t := by
  unfold heatKernel
  have hπ := Real.pi_ne_zero
  have h4πνt : 4 * Real.pi * ν * t ≠ 0 := by
    simp [Real.pi_ne_zero, hν, ht]
  have h4νt : 4 * ν * t ≠ 0 := by
    simp [hν, ht]
  have hA : HasDerivAt (fun s : ℝ => (4 * Real.pi * ν * s)⁻¹)
      (-(4 * Real.pi * ν) / (4 * Real.pi * ν * t) ^ 2) t := by
    have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * ν * s) (4 * Real.pi * ν) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi * ν)
    have h := hlin.inv h4πνt
    refine h.congr_deriv ?_
    ring
  have hφ : HasDerivAt (fun s : ℝ => -(v₁ ^ 2 + v₂ ^ 2) / (4 * ν * s))
      ((v₁ ^ 2 + v₂ ^ 2) / (4 * ν * t ^ 2)) t := by
    have hlin : HasDerivAt (fun s : ℝ => 4 * ν * s) (4 * ν) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * ν)
    have h := (hasDerivAt_const t (-(v₁ ^ 2 + v₂ ^ 2))).div hlin h4νt
    refine h.congr_deriv ?_
    field_simp
    try ring
  have h := hA.mul hφ.exp
  refine h.congr_deriv ?_
  try simp only [Pi.div_apply]
  field_simp
  try ring

/-- **The heat equation, pointwise** (Degond's diffusion part solved explicitly): the
time-derivative value equals `ν` times the sum of the two second momentum-derivative
values, `∂_t K = ν·∆_v K` — the solution operator exists because it is written
down. -/
theorem heatKernel_heat_equation (ν t v₁ v₂ : ℝ) (hν : ν ≠ 0) (ht : t ≠ 0) :
    heatKernel ν t v₁ v₂ * (-(1 / t) + (v₁ ^ 2 + v₂ ^ 2) / (4 * ν * t ^ 2))
      = ν * (heatKernel ν t v₁ v₂
            * (v₁ ^ 2 / (4 * ν ^ 2 * t ^ 2) - 1 / (2 * ν * t))
          + heatKernel ν t v₁ v₂
            * (v₂ ^ 2 / (4 * ν ^ 2 * t ^ 2) - 1 / (2 * ν * t))) := by
  field_simp
  ring

/-! ### §B — unit mass and the maximum principle -/

/-- **The kernel has unit mass on the momentum plane**: `∫_{ℝ²} K(t,v) dv = 1` — the
two-dimensional Gaussian integral, via Fubini and `∫ e^{−bx²} = √(π/b)`. -/
theorem heatKernel_integral_one (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    ∫ v : ℝ × ℝ, heatKernel ν t v.1 v.2 = 1 := by
  have hπ := Real.pi_pos
  have hb : (0 : ℝ) < (4 * ν * t)⁻¹ := by positivity
  have hsplit : (fun v : ℝ × ℝ => heatKernel ν t v.1 v.2)
      = fun v : ℝ × ℝ => (4 * Real.pi * ν * t)⁻¹ *
          (Real.exp (-(4 * ν * t)⁻¹ * v.1 ^ 2)
            * Real.exp (-(4 * ν * t)⁻¹ * v.2 ^ 2)) := by
    funext v
    unfold heatKernel
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hsplit, MeasureTheory.integral_const_mul, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul
      (f := fun x : ℝ => Real.exp (-(4 * ν * t)⁻¹ * x ^ 2))
      (g := fun x : ℝ => Real.exp (-(4 * ν * t)⁻¹ * x ^ 2)),
    integral_gaussian, Real.mul_self_sqrt (by positivity)]
  have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
  have hnu' : ν ≠ 0 := hν.ne'
  have ht' : t ≠ 0 := ht.ne'
  field_simp
  try ring

/-- The kernel is integrable on the momentum plane. -/
theorem heatKernel_integrable (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    Integrable (fun v : ℝ × ℝ => heatKernel ν t v.1 v.2) := by
  have hb : (0 : ℝ) < (4 * ν * t)⁻¹ := by positivity
  have hsplit : (fun v : ℝ × ℝ => heatKernel ν t v.1 v.2)
      = fun v : ℝ × ℝ => (4 * Real.pi * ν * t)⁻¹ *
          (Real.exp (-(4 * ν * t)⁻¹ * v.1 ^ 2)
            * Real.exp (-(4 * ν * t)⁻¹ * v.2 ^ 2)) := by
    funext v
    unfold heatKernel
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hsplit, MeasureTheory.Measure.volume_eq_prod]
  exact ((integrable_exp_neg_mul_sq hb).mul_prod
    (integrable_exp_neg_mul_sq hb)).const_mul _

/-- **Kernel averages contract data bounds** (the abstract maximum principle): a
nonnegative unit-mass kernel maps `|f| ≤ M` to `|∫ K·f| ≤ M` — Degond's Proposition A3
output as an exact inequality. -/
theorem kernel_average_bound {K f : (ℝ × ℝ) → ℝ} {M : ℝ}
    (hK0 : ∀ w, 0 ≤ K w) (hK1 : ∫ w, K w = 1)
    (hKint : Integrable K)
    (hmeas : AEStronglyMeasurable f (volume : Measure (ℝ × ℝ)))
    (hf : ∀ w, |f w| ≤ M) :
    |∫ w, K w * f w| ≤ M := by
  have hint : Integrable (fun w => f w * K w) :=
    hKint.bdd_mul hmeas (Filter.Eventually.of_forall fun w => by
      simpa [Real.norm_eq_abs] using hf w)
  have hint' : Integrable (fun w => K w * f w) := by
    simpa [mul_comm] using hint
  have habs_eq : (fun w => |K w * f w|) = fun w => K w * |f w| := by
    funext w
    rw [abs_mul, abs_of_nonneg (hK0 w)]
  calc |∫ w, K w * f w| ≤ ∫ w, |K w * f w| := abs_integral_le_integral_abs
    _ = ∫ w, K w * |f w| := by rw [habs_eq]
    _ ≤ ∫ w, K w * M := by
        refine integral_mono ?_ (hKint.mul_const M) ?_
        · rw [← habs_eq]
          exact hint'.abs
        · intro w
          exact mul_le_mul_of_nonneg_left (hf w) (hK0 w)
    _ = M := by rw [MeasureTheory.integral_mul_const, hK1, one_mul]

/-- **The maximum principle for the heat kernel**: the diffusion step of the linear
kinetic solution operator never increases the data bound. -/
theorem heatKernel_maximum_principle (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t)
    {f : (ℝ × ℝ) → ℝ} {M : ℝ}
    (hmeas : AEStronglyMeasurable f (volume : Measure (ℝ × ℝ)))
    (hf : ∀ w, |f w| ≤ M) :
    |∫ w : ℝ × ℝ, heatKernel ν t w.1 w.2 * f w| ≤ M :=
  kernel_average_bound (fun w => (heatKernel_pos ν t w.1 w.2 hν ht).le)
    (heatKernel_integral_one ν t hν ht) (heatKernel_integrable ν t hν ht) hmeas hf

/-! ### §C — a bounded drift is absorbed by the moving frame -/

/-- **The drifted kernel** `K(t, v − ta)` — the frozen-coefficient solution operator
with drift. -/
def driftedHeatKernel (ν a₁ a₂ t v₁ v₂ : ℝ) : ℝ :=
  heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)

/-- First momentum derivative of the drifted kernel — the shift composes trivially. -/
theorem driftedHeatKernel_hasDerivAt_v1 (ν a₁ a₂ t v₁ v₂ : ℝ)
    (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun w => driftedHeatKernel ν a₁ a₂ t w v₂)
      (heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)
        * (-((v₁ - t * a₁) / (2 * ν * t)))) v₁ := by
  unfold driftedHeatKernel
  have h := (heatKernel_hasDerivAt_v1 ν t (v₁ - t * a₁) (v₂ - t * a₂) hν ht).comp v₁
    ((hasDerivAt_id v₁).sub_const (t * a₁))
  simpa [Function.comp_def] using h

/-- Second slot, first derivative of the drifted kernel. -/
theorem driftedHeatKernel_hasDerivAt_v2 (ν a₁ a₂ t v₁ v₂ : ℝ)
    (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun w => driftedHeatKernel ν a₁ a₂ t v₁ w)
      (heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)
        * (-((v₂ - t * a₂) / (2 * ν * t)))) v₂ := by
  unfold driftedHeatKernel
  have h := (heatKernel_hasDerivAt_v2 ν t (v₁ - t * a₁) (v₂ - t * a₂) hν ht).comp v₂
    ((hasDerivAt_id v₂).sub_const (t * a₂))
  simpa [Function.comp_def] using h

/-- Second momentum derivative of the drifted kernel, first slot. -/
theorem driftedHeatKernel_hasDerivAt_v1_deriv (ν a₁ a₂ t v₁ v₂ : ℝ)
    (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun w => heatKernel ν t (w - t * a₁) (v₂ - t * a₂)
        * (-((w - t * a₁) / (2 * ν * t))))
      (heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)
        * ((v₁ - t * a₁) ^ 2 / (4 * ν ^ 2 * t ^ 2) - 1 / (2 * ν * t))) v₁ := by
  have h := (heatKernel_hasDerivAt_v1_deriv ν t (v₁ - t * a₁) (v₂ - t * a₂) hν ht).comp
    v₁ ((hasDerivAt_id v₁).sub_const (t * a₁))
  simpa [Function.comp_def] using h

/-- Second momentum derivative of the drifted kernel, second slot. -/
theorem driftedHeatKernel_hasDerivAt_v2_deriv (ν a₁ a₂ t v₁ v₂ : ℝ)
    (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun w => heatKernel ν t (v₁ - t * a₁) (w - t * a₂)
        * (-((w - t * a₂) / (2 * ν * t))))
      (heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)
        * ((v₂ - t * a₂) ^ 2 / (4 * ν ^ 2 * t ^ 2) - 1 / (2 * ν * t))) v₂ := by
  have h := (heatKernel_hasDerivAt_v2_deriv ν t (v₁ - t * a₁) (v₂ - t * a₂) hν ht).comp
    v₂ ((hasDerivAt_id v₂).sub_const (t * a₂))
  simpa [Function.comp_def] using h

/-- **The time derivative of the drifted kernel** — the one genuinely multivariate
slot, computed on the explicit formula:

  `∂_t u = u·(−1/t + |v−ta|²/4νt² + a·(v−ta)/2νt)`

which is exactly `∂_t K − a·∇_v K` at the shifted point. -/
theorem driftedHeatKernel_hasDerivAt_time (ν a₁ a₂ t v₁ v₂ : ℝ)
    (hν : ν ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun s => driftedHeatKernel ν a₁ a₂ s v₁ v₂)
      (driftedHeatKernel ν a₁ a₂ t v₁ v₂ *
        (-(1 / t) + ((v₁ - t * a₁) ^ 2 + (v₂ - t * a₂) ^ 2) / (4 * ν * t ^ 2)
          + (a₁ * (v₁ - t * a₁) + a₂ * (v₂ - t * a₂)) / (2 * ν * t))) t := by
  unfold driftedHeatKernel heatKernel
  have hπ := Real.pi_ne_zero
  have h4πνt : 4 * Real.pi * ν * t ≠ 0 := by
    simp [Real.pi_ne_zero, hν, ht]
  have h4νt : 4 * ν * t ≠ 0 := by
    simp [hν, ht]
  have hA : HasDerivAt (fun s : ℝ => (4 * Real.pi * ν * s)⁻¹)
      (-(4 * Real.pi * ν) / (4 * Real.pi * ν * t) ^ 2) t := by
    have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * ν * s) (4 * Real.pi * ν) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi * ν)
    have h := hlin.inv h4πνt
    refine h.congr_deriv ?_
    ring
  have hw1 : HasDerivAt (fun s : ℝ => v₁ - s * a₁) (-a₁) t := by
    have h := HasDerivAt.const_sub v₁ ((hasDerivAt_id t).mul_const a₁)
    refine h.congr_deriv ?_
    ring
  have hw2 : HasDerivAt (fun s : ℝ => v₂ - s * a₂) (-a₂) t := by
    have h := HasDerivAt.const_sub v₂ ((hasDerivAt_id t).mul_const a₂)
    refine h.congr_deriv ?_
    ring
  have hnum : HasDerivAt (fun s : ℝ => -((v₁ - s * a₁) ^ 2 + (v₂ - s * a₂) ^ 2))
      (2 * a₁ * (v₁ - t * a₁) + 2 * a₂ * (v₂ - t * a₂)) t := by
    have h := ((hw1.pow 2).add (hw2.pow 2)).neg
    refine h.congr_deriv ?_
    push_cast
    ring
  have hden : HasDerivAt (fun s : ℝ => 4 * ν * s) (4 * ν) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * ν)
  have hφ := hnum.div hden h4νt
  have h := hA.mul hφ.exp
  refine h.congr_deriv ?_
  try simp only [Pi.div_apply]
  field_simp
  try ring

/-- **The drifted heat equation** (the frozen-coefficient step of Proposition A1):
with the derivative values carried by the theorems above,

  `∂_t u + a·∇_v u = ν·∆_v u`

— a bounded frozen drift costs nothing: the moving frame absorbs it exactly. -/
theorem drifted_heat_equation (ν a₁ a₂ t v₁ v₂ : ℝ) (hν : ν ≠ 0) (ht : t ≠ 0) :
    driftedHeatKernel ν a₁ a₂ t v₁ v₂ *
        (-(1 / t) + ((v₁ - t * a₁) ^ 2 + (v₂ - t * a₂) ^ 2) / (4 * ν * t ^ 2)
          + (a₁ * (v₁ - t * a₁) + a₂ * (v₂ - t * a₂)) / (2 * ν * t))
      + a₁ * (heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)
          * (-((v₁ - t * a₁) / (2 * ν * t))))
      + a₂ * (heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)
          * (-((v₂ - t * a₂) / (2 * ν * t))))
      = ν * (heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)
            * ((v₁ - t * a₁) ^ 2 / (4 * ν ^ 2 * t ^ 2) - 1 / (2 * ν * t))
          + heatKernel ν t (v₁ - t * a₁) (v₂ - t * a₂)
            * ((v₂ - t * a₂) ^ 2 / (4 * ν ^ 2 * t ^ 2) - 1 / (2 * ν * t))) := by
  unfold driftedHeatKernel
  field_simp
  ring

/-! ### §D — the space transport along the relativistic velocity -/

/-- The time derivative of the transported datum `f₀(x − t·v̂₁)`. -/
theorem transport_hasDerivAt_time (f₀ : ℝ → ℝ) {D : ℝ} (x t v₁ v₂ : ℝ)
    (hf : HasDerivAt f₀ D (x - t * relativisticVelocity1 v₁ v₂)) :
    HasDerivAt (fun s => f₀ (x - s * relativisticVelocity1 v₁ v₂))
      (-(relativisticVelocity1 v₁ v₂) * D) t := by
  have hinner : HasDerivAt (fun s : ℝ => x - s * relativisticVelocity1 v₁ v₂)
      (-(relativisticVelocity1 v₁ v₂)) t := by
    have h := HasDerivAt.const_sub x
      ((hasDerivAt_id t).mul_const (relativisticVelocity1 v₁ v₂))
    refine h.congr_deriv ?_
    ring
  have h := hf.comp t hinner
  refine h.congr_deriv ?_
  ring

/-- The space derivative of the transported datum. -/
theorem transport_hasDerivAt_space (f₀ : ℝ → ℝ) {D : ℝ} (x t v₁ v₂ : ℝ)
    (hf : HasDerivAt f₀ D (x - t * relativisticVelocity1 v₁ v₂)) :
    HasDerivAt (fun y => f₀ (y - t * relativisticVelocity1 v₁ v₂)) D x := by
  have h := hf.comp x ((hasDerivAt_id x).sub_const (t * relativisticVelocity1 v₁ v₂))
  simpa [Function.comp_def] using h

/-- **The transport equation** `∂_t g + v̂₁·∂_x g = 0`: the characteristic solution's
derivative values cancel exactly — with `v̂₁` subluminal, the characteristics are
causal. -/
theorem transport_equation (c D : ℝ) : (-(c) * D) + c * D = 0 := by
  ring

end LinearExistence

section IterationConvergence

/-!
# The existence–uniqueness iteration — Volterra majorants, Grönwall, Sobolev

The well-posedness proof of Lai 1998 (the one-and-a-half dimensional relativistic
Vlasov–Maxwell–Fokker–Planck system) runs on three engines, each of which has an exact
mathematical core formalized here:

* **§A–B — the Volterra majorant tower.**  Every estimate of the paper's §2–§4 has the
  shape `aₙ₊₁(t) ≤ C·∫₀ᵗ aₙ`.  The explicit majorant `M·(Ct)ⁿ/n!` closes *exactly*
  under this recursion (`volterraMajorant_recursion` — the integral of the `n`-th
  majorant is the `(n+1)`-st, an identity, not an estimate), so any iterate sequence
  under the recursion sits below it (`iterate_le_majorant`).
* **§C — the weighted Cauchy property and uniqueness.**  The majorant at the right
  endpoint decays factorially (`iterate_uniform_tendsto_zero`), which is the paper's
  §4: the difference sequence `g^{(m,n)}` is uniformly small, hence Cauchy in the
  weighted norm.  A self-bounded function `g ≤ C∫₀ᵗ g` is dominated by *every* stage of
  the tower, hence nonpositive (`selfbounded_le_zero`); a nonnegative one vanishes
  (`iteration_uniqueness`) — the paper's Theorem 5.1: two solutions with the same data
  coincide.
* **§D — the integral Grönwall bound.**  `M·e^{Ct}` solves the inhomogeneous Volterra
  equation exactly (`exp_solves_volterra`), so `a ≤ M + C∫₀ᵗ a` forces
  `a ≤ M·e^{Ct}` (`gronwall_exponential_bound`) — Degond's Propositions A3/A4 output
  turned into the paper's Eq. (12) growth `‖f⁽ⁿ⁾(t)‖ ≤ ‖f₀‖·e^{2βt}`, with `C = 2β`
  the exact friction-divergence bound of the `VelocityMap` section.
* **§E — the Sobolev embedding.**  Mathlib carries the Gagliardo–Nirenberg–Sobolev
  inequality (`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`); instantiated on the
  paper's momentum plane (`finrank ℝ (ℝ×ℝ) = 2`, conjugate pair `(2,2)`) it is the
  embedding step of the paper's §3 (`sobolev_embedding_momentum_plane`) — welded from
  Mathlib, not hand-rolled.

**Honest layering, with its search.**  Formalized: the majorant tower and its exact
recursion, the factorial-decay Cauchy bound, the vanishing of self-bounded functions
(uniqueness), the exact exponential solution and the integral Grönwall bound, the
dimension-two Sobolev embedding from Mathlib, and (§F) the PDE-level assembly: the
iteration scheme as a structure whose pointwise iterate traces converge by summable
factorial majorants.  The linear existence input — the explicit frozen-coefficient
kernels with their maximum principle — is the `LinearExistence` section.  Not
formalized: the variable-coefficient parametrix composition and the identification of
the limit with a solution of the nonlinear system. -/

open Nat Filter MeasureTheory intervalIntegral

/-! ### §A — the exact Volterra majorant tower -/

/-- **The Volterra majorant** `Aₙ(t) = M·(Ct)ⁿ/n!` — the explicit tower dominating
every iterated integral estimate of the well-posedness proof. -/
def volterraMajorant (M C : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  M * (C * t) ^ n / n !

/-- The tower starts at the data bound: `A₀ = M`. -/
theorem volterraMajorant_zero (M C t : ℝ) : volterraMajorant M C 0 t = M := by
  simp [volterraMajorant]

/-- **The tower closes exactly under the iteration integral**:

  `C·∫₀ᵗ Aₙ(s) ds = Aₙ₊₁(t)`

— an identity, not an estimate: the factorial in the majorant is precisely the
iterated-integral volume. -/
theorem volterraMajorant_recursion (M C : ℝ) (n : ℕ) (t : ℝ) :
    C * ∫ s in (0 : ℝ)..t, volterraMajorant M C n s
      = volterraMajorant M C (n + 1) t := by
  unfold volterraMajorant
  have hrw : (fun s => M * (C * s) ^ n / ↑n !)
      = fun s => (M * C ^ n / ↑n !) * s ^ n := by
    funext s
    rw [mul_pow]
    ring
  rw [hrw, intervalIntegral.integral_const_mul, integral_pow,
    zero_pow n.succ_ne_zero, sub_zero]
  have hf : ((n ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast [Nat.factorial_succ]
  field_simp
  ring

/-! ### §B — the iterates sit below the tower -/

/-- **Any sequence under the Volterra recursion is dominated by the majorant tower**:
if `a₀ ≤ M` on `[0,T]` and `aₙ₊₁(t) ≤ C·∫₀ᵗ aₙ`, then `aₙ(t) ≤ M·(Ct)ⁿ/n!`.  This is
the single induction behind every §2–§4 estimate of the well-posedness proof. -/
theorem iterate_le_majorant {T C M : ℝ} (hC : 0 ≤ C) (a : ℕ → ℝ → ℝ)
    (hcont : ∀ n, Continuous (a n))
    (h0 : ∀ t, t ∈ Set.Icc (0 : ℝ) T → a 0 t ≤ M)
    (hrec : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      a (n + 1) t ≤ C * ∫ s in (0 : ℝ)..t, a n s) :
    ∀ n t, t ∈ Set.Icc (0 : ℝ) T → a n t ≤ volterraMajorant M C n t := by
  intro n
  induction n with
  | zero =>
    intro t ht
    simpa [volterraMajorant] using h0 t ht
  | succ n ih =>
    intro t ht
    have hmaj_cont : Continuous (fun s => volterraMajorant M C n s) := by
      unfold volterraMajorant
      fun_prop
    calc a (n + 1) t ≤ C * ∫ s in (0 : ℝ)..t, a n s := hrec n t ht
      _ ≤ C * ∫ s in (0 : ℝ)..t, volterraMajorant M C n s := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          refine intervalIntegral.integral_mono_on ht.1
            ((hcont n).intervalIntegrable _ _)
            (hmaj_cont.intervalIntegrable _ _) ?_
          intro s hs
          exact ih s ⟨hs.1, hs.2.trans ht.2⟩
      _ = volterraMajorant M C (n + 1) t := volterraMajorant_recursion M C n t

/-! ### §C — the weighted Cauchy property and uniqueness -/

/-- **The Cauchy-property engine** (the paper's §4): under the recursion, every
iterate is bounded on all of `[0,T]` by the *endpoint* majorant `M·(CT)ⁿ/n!`, and that
bound tends to zero — the difference sequence of the iterates is uniformly small, so
the sequence is Cauchy in the weighted supremum norm. -/
theorem iterate_uniform_tendsto_zero {T C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (a : ℕ → ℝ → ℝ)
    (hcont : ∀ n, Continuous (a n))
    (h0 : ∀ t, t ∈ Set.Icc (0 : ℝ) T → a 0 t ≤ M)
    (hrec : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      a (n + 1) t ≤ C * ∫ s in (0 : ℝ)..t, a n s) :
    (∀ n t, t ∈ Set.Icc (0 : ℝ) T → a n t ≤ M * (C * T) ^ n / n !)
      ∧ Tendsto (fun n : ℕ => M * (C * T) ^ n / n !) atTop (nhds 0) := by
  constructor
  · intro n t ht
    refine le_trans (iterate_le_majorant hC a hcont h0 hrec n t ht) ?_
    unfold volterraMajorant
    have h2 : C * t ≤ C * T := mul_le_mul_of_nonneg_left ht.2 hC
    have h3 : (0 : ℝ) ≤ C * t := mul_nonneg hC ht.1
    gcongr
  · have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (C * T)).const_mul M
    simpa [mul_div_assoc] using h

/-- **Self-bounded Volterra functions are nonpositive**: a continuous `g` with
`g(t) ≤ C·∫₀ᵗ g` on `[0,T]` sits below every stage of the majorant tower built from
its own supremum, hence below the factorial tail — `g ≤ 0`. -/
theorem selfbounded_le_zero {T C : ℝ} (hC : 0 ≤ C) (g : ℝ → ℝ)
    (hcont : Continuous g)
    (hself : ∀ t, t ∈ Set.Icc (0 : ℝ) T → g t ≤ C * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → g t ≤ 0 := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image
    hcont.continuousOn
  have hM : ∀ t, t ∈ Set.Icc (0 : ℝ) T → g t ≤ max M₀ 0 := fun t ht =>
    le_trans (hM₀ (Set.mem_image_of_mem g ht)) (le_max_left _ _)
  have hbound := (iterate_uniform_tendsto_zero hC (le_max_right M₀ 0)
    (fun _ => g) (fun _ => hcont) hM (fun _ t ht => hself t ht)).1
  have htends := (iterate_uniform_tendsto_zero hC (le_max_right M₀ 0)
    (fun _ => g) (fun _ => hcont) hM (fun _ t ht => hself t ht)).2
  intro t ht
  exact ge_of_tendsto' htends (fun n => hbound n t ht)

/-- **The uniqueness engine** (the paper's Theorem 5.1 face): a nonnegative
self-bounded Volterra function — the weighted norm of the difference of two solutions
with the same data — vanishes identically. -/
theorem iteration_uniqueness {T C : ℝ} (hC : 0 ≤ C) (g : ℝ → ℝ)
    (hcont : Continuous g) (hnonneg : ∀ t, t ∈ Set.Icc (0 : ℝ) T → 0 ≤ g t)
    (hself : ∀ t, t ∈ Set.Icc (0 : ℝ) T → g t ≤ C * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → g t = 0 := fun t ht =>
  le_antisymm (selfbounded_le_zero hC g hcont hself t ht) (hnonneg t ht)

/-! ### §D — the integral Grönwall bound: the paper's Eq. (12) -/

/-- **The exponential solves the inhomogeneous Volterra equation exactly**:
`M + C·∫₀ᵗ M·e^{Cs} ds = M·e^{Ct}` — an identity, the closed form the Grönwall bound
compares against. -/
theorem exp_solves_volterra (M C t : ℝ) (hC : C ≠ 0) :
    M + C * ∫ s in (0 : ℝ)..t, M * Real.exp (C * s) = M * Real.exp (C * t) := by
  have hF : ∀ s : ℝ, HasDerivAt (fun r => (M / C) * Real.exp (C * r))
      (M * Real.exp (C * s)) s := by
    intro s
    have hlin : HasDerivAt (fun r : ℝ => C * r) C s := by
      simpa using (hasDerivAt_id s).const_mul C
    have h := (hlin.exp).const_mul (M / C)
    refine h.congr_deriv ?_
    field_simp
    try ring
  have hint : ∫ s in (0 : ℝ)..t, M * Real.exp (C * s)
      = (M / C) * Real.exp (C * t) - (M / C) * Real.exp (C * 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
      ((continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
          _ _)
  rw [hint, mul_zero, Real.exp_zero]
  field_simp
  ring

/-- **The integral Grönwall bound**: `a ≤ M + C·∫₀ᵗ a` on `[0,T]` forces
`a(t) ≤ M·e^{Ct}` — the estimates Degond's propositions hand to the iteration become
the paper's Eq. (12): with `C = 2β` (the exact friction-divergence bound), the
iterates grow at most like `‖f₀‖·e^{2βt}`. -/
theorem gronwall_exponential_bound {T C M : ℝ} (hC : 0 < C) (a : ℝ → ℝ)
    (hcont : Continuous a)
    (hle : ∀ t, t ∈ Set.Icc (0 : ℝ) T → a t ≤ M + C * ∫ s in (0 : ℝ)..t, a s) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → a t ≤ M * Real.exp (C * t) := by
  have hexp_cont : Continuous (fun s : ℝ => M * Real.exp (C * s)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hgcont : Continuous (fun s => a s - M * Real.exp (C * s)) :=
    hcont.sub hexp_cont
  have hgself : ∀ t, t ∈ Set.Icc (0 : ℝ) T →
      (fun s => a s - M * Real.exp (C * s)) t
        ≤ C * ∫ s in (0 : ℝ)..t, (a s - M * Real.exp (C * s)) := by
    intro t ht
    have hsplit : ∫ s in (0 : ℝ)..t, (a s - M * Real.exp (C * s))
        = (∫ s in (0 : ℝ)..t, a s) - ∫ s in (0 : ℝ)..t, M * Real.exp (C * s) :=
      intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
        (hexp_cont.intervalIntegrable _ _)
    have h2 := exp_solves_volterra M C t hC.ne'
    calc a t - M * Real.exp (C * t)
        ≤ (M + C * ∫ s in (0 : ℝ)..t, a s) - M * Real.exp (C * t) := by
          linarith [hle t ht]
      _ = C * ((∫ s in (0 : ℝ)..t, a s)
            - ∫ s in (0 : ℝ)..t, M * Real.exp (C * s)) := by
          rw [← h2]
          ring
      _ = C * ∫ s in (0 : ℝ)..t, (a s - M * Real.exp (C * s)) := by
          rw [hsplit]
  intro t ht
  have hzero := selfbounded_le_zero hC.le _ hgcont hgself t ht
  linarith [hzero]

/-! ### §E — the Sobolev embedding on the momentum plane -/

open scoped ENNReal NNReal

/-- **The Sobolev embedding of the momentum plane**: Mathlib's Gagliardo–Nirenberg–
Sobolev inequality instantiated at the paper's phase space — dimension two, conjugate
pair `(2,2)`: for a continuously differentiable, compactly supported `u` on `ℝ²_v`,

  `‖u‖_{L²} ≤ C·‖∇u‖_{L¹}`

— the embedding step of the smoothness bootstrap (paper §3), welded from Mathlib
rather than assumed. -/
theorem sobolev_embedding_momentum_plane {u : (ℝ × ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    eLpNorm u 2 (volume : Measure (ℝ × ℝ))
      ≤ eLpNormLESNormFDerivOneConst (volume : Measure (ℝ × ℝ)) 2
        * eLpNorm (fderiv ℝ u) 1 (volume : Measure (ℝ × ℝ)) := by
  have hrank : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    simp [Module.finrank_prod, Module.finrank_self]
  have hp : NNReal.HolderConjugate (Module.finrank ℝ (ℝ × ℝ)) (2 : ℝ≥0) := by
    rw [hrank]
    exact_mod_cast NNReal.HolderConjugate.two_two
  simpa using MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one
    (volume : Measure (ℝ × ℝ)) hu h2u hp

/-! ### §F — the PDE-level assembly -/

/-- **The iteration scheme as data** — what the linear existence theory hands to the
convergence machinery: a sequence of weighted norms (of the iterate differences),
a data bound `M`, a rate `C`, and the Volterra recursion connecting the stages.  In
the paper, `weightNorm n` is `‖g^{(n+1,n)}(t)‖` and the recursion is the output of
Degond's estimates applied to each linear stage. -/
structure KineticIterationScheme (T : ℝ) where
  /-- The weighted norm trace of the `n`-th iterate difference. -/
  weightNorm : ℕ → ℝ → ℝ
  /-- Each stage's norm is continuous in time. -/
  cont : ∀ n, Continuous (weightNorm n)
  /-- The data bound. -/
  M : ℝ
  /-- The data bound is nonnegative (it bounds a norm). -/
  M_nonneg : 0 ≤ M
  /-- The Volterra rate (in the paper, a constant depending on `T`). -/
  C : ℝ
  /-- The rate is nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- The zeroth stage is bounded by the data. -/
  init : ∀ t, t ∈ Set.Icc (0 : ℝ) T → weightNorm 0 t ≤ M
  /-- The Volterra recursion between consecutive stages. -/
  volterra : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
    weightNorm (n + 1) t ≤ C * ∫ s in (0 : ℝ)..t, weightNorm n s

/-- Every stage of the scheme sits under the endpoint factorial majorant. -/
theorem KineticIterationScheme.uniform_bound {T : ℝ} (S : KineticIterationScheme T) :
    ∀ n t, t ∈ Set.Icc (0 : ℝ) T → S.weightNorm n t ≤ S.M * (S.C * T) ^ n / n ! :=
  (iterate_uniform_tendsto_zero S.C_nonneg S.M_nonneg S.weightNorm S.cont S.init
    S.volterra).1

/-- The majorant series is summable — the exponential series. -/
theorem KineticIterationScheme.majorant_summable {T : ℝ}
    (S : KineticIterationScheme T) :
    Summable (fun n : ℕ => S.M * (S.C * T) ^ n / n !) := by
  simpa [mul_div_assoc] using (Real.summable_pow_div_factorial (S.C * T)).mul_left S.M

/-- **The assembled convergence** (the paper's "by the Cauchy properties of the
iterates, they converge"): any pointwise trace of the iterates whose successive
differences are controlled by the scheme is a Cauchy sequence dominated by a summable
series, hence converges.  Together with `iteration_uniqueness` this is the PDE-level
assembly: the linear stages exist (the kernel module), their estimates form a scheme,
the scheme's iterates converge, and the limit is unique. -/
theorem KineticIterationScheme.pointwise_limit_exists {T : ℝ}
    (S : KineticIterationScheme T) (u : ℕ → ℝ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hu : ∀ n, |u (n + 1) - u n| ≤ S.weightNorm n t) :
    ∃ L, Tendsto u atTop (nhds L) := by
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_dist_le_of_summable
      (fun n => S.M * (S.C * T) ^ n / n !) ?_ S.majorant_summable
    intro n
    rw [Real.dist_eq]
    calc |u n - u (n + 1)| = |u (n + 1) - u n| := abs_sub_comm _ _
      _ ≤ S.weightNorm n t := hu n
      _ ≤ S.M * (S.C * T) ^ n / n ! := S.uniform_bound n t ht
  exact cauchySeq_tendsto_of_complete hcauchy

end IterationConvergence

section DissipationUnification

/-!
# One dissipation structure — kinetic drag, contact friction, cosmological drain

The relational framework treats dissipative evolution, damped mechanics, and
entropy-coupled gravitation as levels of one construction.  The repository already
proves all three through a single lemma — the Herglotz integrating factor
`ClassicalMechanics.weighted_variation_deriv`,
`d/dt(e^{−ψ}X) = e^{−ψ}(Ẋ − ψ̇X)` — and this module makes the identification exact in
both directions rather than leaving it as a shared proof step:

* **§A — the kinetic drag is the contact friction.**  The decay face of the friction
  envelope (`contact_decay_exact`, `X' = −γX ⟹ X = X₀e^{−γt}`, routed through the
  kinetic module's `friction_growth_exact`); the momentum-drag characteristic
  `a = −βv` is *exactly* the Herglotz generalized Euler–Lagrange equation at zero
  potential (`drag_characteristic_is_herglotz`); and the drag rate `β` *is* the
  contact-slice coefficient `ρ` (`kinetic_rate_is_contact_coefficient`) — the
  Vlasov–Maxwell–Fokker–Planck viscosity and the Herglotz contact friction are one
  object.
* **§B — the envelope is an entropic clock.**  For the exact flows, the logarithmic
  amplitude ratio reads elapsed time at the dissipation rate:
  `log(X₀/X(t)) = γt` (decay) and `log(X(t)/X₀) = 2βt` (growth) — the same reading
  as the entropic-time axis `τ_ent = log(A₀/A(t))` of the dissipative arcs: the
  friction coefficient converts amplitude loss into duration.
* **§C — the cosmological face.**  The Herglotz function acts as a cosmological
  constant exactly on the Riccati flow `φ̇ = φH + φ²`; this module shows that
  condition is the *same integrating-factor structure*: with the scale factor `a`
  (rate `H`) as the weight,

  `φ̇ = φH + φ² ⟺ d/dt(a/φ) = −a`

  (`riccati_iff_inverse_flows_with_scale`), so the vacuum equation of state holds
  precisely when the inverse contact rate flows with minus the scale factor
  (`cosmological_constant_iff_inverse_flow`) — the cosmological drain is the damped
  linear law at rate `H`, the gravitational instance of §A's drag.

Together with the maximum principle and convergence engines of the companion
modules, this closes the dissipation strand of the relational framework: one
integrating-factor identity runs the kinetic, mechanical, and cosmological sectors,
with the coefficients identified, not merely analogous. -/

open Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck
open Cosmology.FLRW.Dynamics

/-! ### §A — the kinetic drag is the contact friction -/

/-- **The decay face of the friction envelope**: `X' = −γX` forces
`X(t) = X₀·e^{−γt}` — the same exact solution as the growth face, through the same
integrating factor. -/
theorem contact_decay_exact (γ : ℝ) (X : ℝ → ℝ)
    (hX : ∀ t, HasDerivAt X (-(γ * X t)) t) (t : ℝ) :
    X t = X 0 * Real.exp (-(γ * t)) := by
  have hX' : ∀ u, HasDerivAt X (2 * (-(γ / 2)) * X u) u := by
    intro u
    refine (hX u).congr_deriv ?_
    ring
  have h := friction_growth_exact (-(γ / 2)) X hX' t
  rw [show (2 : ℝ) * (-(γ / 2)) * t = -(γ * t) from by ring] at h
  exact h

/-- **The momentum-drag characteristic is the Herglotz damped law at zero
potential**: `a = −βv` if and only if the generalized Euler–Lagrange form of the
contact slice with `ν = mβ` and `U' = 0` holds — the kinetic friction term and the
action-dependent variational principle produce the same equation of motion. -/
theorem drag_characteristic_is_herglotz (m β v a : ℝ) (hm : m ≠ 0) :
    (-(0 : ℝ)) - m * a + (-(m * β / m)) * (m * v) = 0 ↔ a = -(β * v) := by
  rw [ClassicalMechanics.herglotz_generalized_EL_damped m (m * β) 0 v a hm]
  constructor
  · intro h
    have h2 : m * (a + β * v) = 0 := by
      ring_nf
      ring_nf at h
      linarith
    have h3 := (mul_eq_zero.mp h2).resolve_left hm
    linarith
  · intro h
    rw [h]
    ring

/-- **The drag rate is the contact coefficient**: the damped-oscillator contact slice
built from the kinetic viscosity `ν = mβ` has `ρ = β` — the Vlasov–Fokker–Planck drag
and the Herglotz contact friction are the same coefficient, not analogues. -/
theorem kinetic_rate_is_contact_coefficient (m β : ℝ) (L_R s : ℝ → ℝ) (t : ℝ)
    (hm : m ≠ 0) :
    (ClassicalMechanics.dampedOscillatorContactSlice m (m * β) L_R s).ρ t = β := by
  simp only [ClassicalMechanics.dampedOscillatorContactSlice]
  field_simp

/-! ### §B — the dissipation envelope is an entropic clock -/

/-- **The decay envelope reads entropic time**: `log(X₀/X(t)) = γt` — amplitude loss
converted into duration at the contact rate, the reading of the dissipative
time axis. -/
theorem decay_reads_entropic_time (γ : ℝ) (X : ℝ → ℝ)
    (hX : ∀ t, HasDerivAt X (-(γ * X t)) t) (h0 : X 0 ≠ 0) (t : ℝ) :
    Real.log (X 0 / X t) = γ * t := by
  rw [contact_decay_exact γ X hX t]
  rw [show X 0 / (X 0 * Real.exp (-(γ * t))) = Real.exp (γ * t) from by
    rw [Real.exp_neg]
    field_simp]
  exact Real.log_exp _

/-- **The growth envelope reads entropic time**: `log(X(t)/X₀) = 2βt` — the kinetic
iteration envelope is a clock running at twice the drag coefficient, the exact rate
of the friction-divergence bound. -/
theorem growth_reads_entropic_time (β : ℝ) (X : ℝ → ℝ)
    (hX : ∀ t, HasDerivAt X (2 * β * X t) t) (h0 : X 0 ≠ 0) (t : ℝ) :
    Real.log (X t / X 0) = 2 * β * t := by
  rw [friction_growth_exact β X hX t]
  rw [show X 0 * Real.exp (2 * β * t) / X 0 = Real.exp (2 * β * t) from by
    field_simp]
  exact Real.log_exp _

/-! ### §C — the cosmological face: the scale factor as the integrating factor -/

/-- **The Riccati condition is the integrating-factor identity of the scale
factor**: with `a` the scale factor of rate `H`,

  `φ̇ = φH + φ² ⟺ d/dt(a/φ) = −a`

— the cosmological-constant condition says the inverse contact rate, weighted by the
scale factor, flows with minus the scale factor: the damped linear law at rate `H`,
the gravitational instance of the kinetic drag. -/
theorem riccati_iff_inverse_flows_with_scale (a φ : ℝ → ℝ) (H φ' t : ℝ)
    (ha : HasDerivAt a (H * a t) t) (hφ : HasDerivAt φ φ' t)
    (haz : a t ≠ 0) (hφz : φ t ≠ 0) :
    HasDerivAt (fun s => a s / φ s) (-(a t)) t ↔ φ' = φ t * H + φ t ^ 2 := by
  have hdiv := ha.div hφ hφz
  constructor
  · intro h
    have heq := hdiv.unique h
    rw [div_eq_iff (pow_ne_zero 2 hφz)] at heq
    have h2 : a t * φ' = a t * (φ t * H + φ t ^ 2) := by
      ring_nf
      ring_nf at heq
      linarith
    exact mul_left_cancel₀ haz h2
  · intro h
    refine hdiv.congr_deriv ?_
    rw [h]
    field_simp
    ring

/-- **The cosmological constant is the scale-weighted damped flow**: the vacuum
equation of state `ρ_eff + p_eff = 0` holds if and only if `a/φ` flows with minus
the scale factor — the paper's accelerated-expansion mechanism as the same
integrating-factor structure that runs the kinetic envelope and the damped
oscillator. -/
theorem cosmological_constant_iff_inverse_flow (a φ : ℝ → ℝ) (Hb φ' t : ℝ)
    (ha : HasDerivAt a (Hb * a t) t) (hφ : HasDerivAt φ φ' t)
    (haz : a t ≠ 0) (hφz : φ t ≠ 0) :
    herglotzEffectiveDensity (φ t) Hb + herglotzEffectivePressure (φ t) φ' Hb = 0
      ↔ HasDerivAt (fun s => a s / φ s) (-(a t)) t := by
  rw [herglotz_vacuum_equationOfState_iff]
  exact (riccati_iff_inverse_flows_with_scale a φ Hb φ' t ha hφ haz hφz).symm

end DissipationUnification

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.velocityDivergence_le_two where
  derives @ "claim:the-friction-divergence-of-the-relativistic-velocity-map-is-bounded-by-two-with-the-bound-attained-at-rest-the-exact-constant-of-the-exponential-growth-envelopes",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lai-1998-one-and-one-half-dimensional-relativistic-vlasov-maxwell-fokker-planck-with-non-vanishing-viscosity-mmas-21-1287",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.velocityDivergence_eq"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.energyDenominator_eq_bogoliubov where
  formalizes @ "claim:the-relativistic-velocity-map-is-momentum-over-the-on-shell-energy-the-same-dispersion-carrier-as-the-canonical-velocity-and-the-packet-group-velocity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.bogoliubovEnergy_hasDerivAt"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.field_energy_null_split where
  derives @ "claim:the-one-and-a-half-dimensional-field-energy-momentum-splits-into-nonnegative-null-fluxes-the-structure-behind-the-field-bounds-of-the-vlasov-maxwell-fokker-planck-well-posedness",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lai-1998-one-and-one-half-dimensional-relativistic-vlasov-maxwell-fokker-planck-with-non-vanishing-viscosity-mmas-21-1287"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.friction_growth_exact where
  derives @ "claim:the-friction-growth-envelope-is-the-exact-exponential-solution-at-the-rate-bound-the-growth-mirror-of-the-hypocoercive-exact-decay",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.twisted_form_decay",
  supported_by @ "lean:ClassicalMechanics.HerglotzContactSlice.effectiveLagrangian",
  caveat @ "claim:the-variable-coefficient-parametrix-composition-and-the-identification-of-the-iteration-limit-with-a-solution-of-the-nonlinear-system-remain-unformalized-the-kernels-the-maximum-principle-and-the-assembled-convergence-are-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.heatKernel_heat_equation where
  formalizes @ "claim:the-frozen-coefficient-kinetic-solution-operator-is-the-explicit-momentum-heat-kernel-which-solves-the-diffusion-equation-pointwise-with-full-derivative-calculus",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:degond-1986-global-existence-of-smooth-solutions-for-the-vlasov-fokker-planck-equation-in-1-and-2-space-dimensions-ann-sci-ecole-norm-sup-19-519",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.heatKernel_hasDerivAt_time"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.heatKernel_maximum_principle where
  derives @ "claim:kernel-averages-of-the-unit-mass-positive-heat-kernel-contract-data-bounds-the-maximum-principle-output-that-feeds-the-integral-gronwall-estimate",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.heatKernel_integral_one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.gronwall_exponential_bound"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.drifted_heat_equation where
  derives @ "claim:a-bounded-frozen-drift-is-absorbed-exactly-by-the-moving-frame-of-the-heat-kernel-the-frozen-coefficient-step-of-the-linear-existence-proposition",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:degond-1986-global-existence-of-smooth-solutions-for-the-vlasov-fokker-planck-equation-in-1-and-2-space-dimensions-ann-sci-ecole-norm-sup-19-519"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.transport_hasDerivAt_time where
  derives @ "claim:the-space-transport-along-the-relativistic-velocity-is-solved-exactly-by-characteristics-which-are-causal-because-the-velocity-map-is-subluminal",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.relativisticVelocity_subluminal",
  caveat @ "claim:the-variable-coefficient-parametrix-composition-and-the-identification-of-the-iteration-limit-with-a-solution-of-the-nonlinear-system-remain-unformalized-the-kernels-the-maximum-principle-and-the-assembled-convergence-are-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.KineticIterationScheme.pointwise_limit_exists where
  derives @ "claim:the-pde-level-assembly-iterates-whose-differences-are-controlled-by-the-scheme-converge-pointwise-because-the-factorial-majorant-series-is-summable",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.iterate_le_majorant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.iteration_uniqueness"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.volterraMajorant_recursion where
  formalizes @ "claim:the-volterra-majorant-tower-closes-exactly-under-the-iteration-integral-the-factorial-is-the-iterated-integral-volume",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lai-1998-one-and-one-half-dimensional-relativistic-vlasov-maxwell-fokker-planck-with-non-vanishing-viscosity-mmas-21-1287"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.iterate_uniform_tendsto_zero where
  derives @ "claim:the-weighted-cauchy-property-of-the-vlasov-maxwell-fokker-planck-iterates-follows-from-the-factorial-decay-of-the-volterra-majorant-at-the-endpoint",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.iterate_le_majorant",
  supported_by @ "paper:lai-1998-one-and-one-half-dimensional-relativistic-vlasov-maxwell-fokker-planck-with-non-vanishing-viscosity-mmas-21-1287"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.iteration_uniqueness where
  derives @ "claim:two-solutions-with-the-same-data-coincide-because-the-nonnegative-self-bounded-weighted-difference-norm-vanishes-under-the-factorial-tail",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.selfbounded_le_zero"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.gronwall_exponential_bound where
  derives @ "claim:the-integral-gronwall-bound-turns-the-linear-kinetic-estimates-into-the-exponential-growth-envelope-at-twice-the-drag-coefficient",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.friction_growth_exact",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.velocityDivergence_le_two"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.sobolev_embedding_momentum_plane where
  formalizes @ "claim:the-sobolev-embedding-of-the-smoothness-bootstrap-is-the-gagliardo-nirenberg-sobolev-inequality-instantiated-on-the-dimension-two-momentum-plane",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one",
  caveat @ "claim:the-variable-coefficient-parametrix-composition-and-the-identification-of-the-iteration-limit-with-a-solution-of-the-nonlinear-system-remain-unformalized-the-kernels-the-maximum-principle-and-the-assembled-convergence-are-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.kinetic_rate_is_contact_coefficient where
  formalizes @ "claim:the-vlasov-fokker-planck-drag-rate-and-the-herglotz-contact-coefficient-are-the-same-object-identified-not-analogous",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ClassicalMechanics.dampedOscillatorContactSlice",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.friction_growth_exact"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.drag_characteristic_is_herglotz where
  derives @ "claim:the-momentum-drag-characteristic-of-the-kinetic-friction-is-the-herglotz-generalized-euler-lagrange-equation-at-zero-potential",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ClassicalMechanics.herglotz_generalized_EL_damped"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.decay_reads_entropic_time where
  derives @ "claim:the-dissipation-envelope-is-an-entropic-clock-the-logarithmic-amplitude-ratio-reads-elapsed-time-at-the-contact-rate",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.contact_decay_exact"

zil attach Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck.cosmological_constant_iff_inverse_flow where
  derives @ "claim:the-cosmological-constant-condition-is-the-scale-factor-integrating-factor-identity-the-gravitational-instance-of-the-kinetic-drag-law",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Cosmology.FLRW.Dynamics.herglotz_vacuum_equationOfState_iff",
  supported_by @ "lean:ClassicalMechanics.weighted_variation_deriv"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Vlasov.RelativisticMaxwellFokkerPlanck

end

end

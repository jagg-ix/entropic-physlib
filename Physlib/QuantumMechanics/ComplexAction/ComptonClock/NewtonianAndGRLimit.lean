/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit
public import Physlib.ClassicalMechanics.FreeParticle.Basic
public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde
meta import Zil

/-!
# From the boosted Compton clock to Newton's equations and General Relativity

The entangled / moving Compton clock carries the energy `E = mc²·cosh θ` with momentum `p = mc·sinh θ`
(`EntanglementReparametrization.einsteinEnergy_eq_rest_cosh_rapidity`), the Schmidt boost `cosh η` of
`EntropicProperDistance` acting on the same value. This module discharges that relativistic energy down to
**Newton's equations** — in both Hamiltonian and Lagrangian form — and up to the **local-Lorentz / tetrad**
structure of General Relativity, reusing the mechanics and tetrad-gravity infrastructure already in the
library.

* **§A — the Newtonian Hamiltonian.** `newtonianHamiltonian m p = p²/2m`, its exact rapidity form
  `= mc²·sinh²θ/2` (`newtonianHamiltonian_eq_rapidity`, `p = mc·sinh θ`), and the rigorous non-relativistic
  limit `lim_{c→∞}(E − mc²) = p²/2m` (`newtonianHamiltonian_is_nonrel_limit`, reusing the proven
  `EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger`): the free Hamiltonian is the leading
  kinetic term of the relativistic clock energy.
* **§B — Hamilton's equations give Newton.** `hamilton_velocity` (`∂H/∂p = p/m = v`, i.e. `p = mv`) and
  `hamilton_force_free` (`∂H/∂q = 0 ⇒ ṗ = 0`, Newton's first law) — Hamilton's canonical equations
  `q̇ = ∂H/∂p`, `ṗ = −∂H/∂q` (`ClassicalMechanics.hamiltonEqOp`) evaluated on this `H`.
* **§C — the Lagrangian, Legendre transform, and Newton's second law.** `newtonianLagrangian m v = ½mv²`,
  `lagrange_momentum` (`∂L/∂v = mv = p`, the canonical momentum), `legendre_transform_free`
  (`p·v − L = H`, the Legendre transform to §A) and `newtonianLagrangian_eq_freeParticle_kineticEnergy`
  (the free Lagrangian is `ClassicalMechanics.FreeParticle.kineticEnergy`, whose Euler–Lagrange equation is
  `FreeParticle.NewtonsSecondLaw`, `m·q̈ = 0`).
* **§D — General Relativity: the local mass-shell and the equivalence principle.**
  `massShell_defect_eq_twice_mass_hamiltonian` (`(E/c)² − (mc)² = 2m·H`): the Minkowski mass-shell defect is
  twice the mass times the Newtonian Hamiltonian, so the flat energy–momentum invariant `einstein_massShell`
  *is* the Newtonian energy in the tangent space. That flat `η` is the *local* tetrad metric
  (`CanonicalTetradGravity.tetradMetric` `g = EᵀηE`); its local-Lorentz-gauge invariance
  (`fourMomentum_norm_tetrad_gauge_invariant`) is the **Einstein equivalence principle**, and the tetrad
  promotes the free-particle straight line to the geodesic sourced by the ADM Hamiltonian constraint
  (`TetradADMGravity.hamiltonianConstraint`, the Einstein `G_{nn}`).

* **§E — Newton's second law with a force, and the equivalence principle.** `hamilton_force`
  (`ṗ = −∂H/∂x = F` for `H = p²/2m + V(x)`, upgrading §B's free case), `gravitational_force`
  (`V = m·Φ ⇒ F = −m·Φ'`) and `equivalence_principle_acceleration` (`a = F/m = −Φ'`, the gravitational mass in
  the force cancels the inertial mass in `m·a`) — the concrete equivalence principle behind §D.
* **§F — the weak-field metric `g₀₀ = 1 + 2Φ/c²`.** `weakFieldG00`, `weakFieldG00_flat` (`Φ = 0 ⇒ g₀₀ = 1`,
  the flat `η₀₀` of §D), `newtonianPotential_from_weakFieldG00` (`Φ = (g₀₀ − 1)c²/2`, the metric perturbation
  *is* the Newtonian potential), `weakFieldG00_schwarzschild` (`g₀₀ = 1 − r_s/r` for `Φ = −GM/r`, reusing
  `Relativity.SemiClassical.schwarzschildRadius`) and `weakFieldG00_tendsto_flat` (`lim_{c→∞} g₀₀ = 1`, the GR
  counterpart of §A's kinetic limit — curvature `2Φ/c²` vanishes and Newtonian absolute time returns).
* **§G — the geodesic returns Newton's gravity `ẍ = −∇Φ`.** `weakFieldG00_hasDerivAt` (`∂_x g₀₀ = 2Φ'/c²`),
  `weakFieldChristoffel` `Γˣ₀₀ = ∂_xΦ/c²` with `weakFieldChristoffel_eq_half_metricGradient`
  (`Γˣ₀₀ = ½ ∂_x g₀₀`), `weakField_geodesic_acceleration_eq_newton` (the slow-particle spatial geodesic
  `ẍ = −Γˣ₀₀·c² = −∂_xΦ`) and `geodesic_recovers_newton_gravity` (the mass-free geodesic acceleration equals
  the mass-cancelled Newtonian `a = −∂_xΦ` of §E — GR's geometric explanation of *why* the equivalence
  principle holds).
* **§H — the field equation sources the metric: `∇²Φ = 4πGρ`.** `weakFieldRicci00` `R₀₀ = ∇²Φ/c²` with
  `weakFieldRicci00_eq_half_metric_secondDeriv` (`R₀₀ = ½ ∂²_x g₀₀`), and `weakField_einstein_poisson` (the
  trace-reversed Einstein `R₀₀ = 4πGρ/c²` for dust *is* Newton's Poisson equation) — the source counterpart of
  §G's geodesic (matter curves the metric), the weak-field limit of the ADM constraint
  `TetradADMGravity.sourcedHamiltonianConstraint`.

**Honest layering.** §A's rapidity form, §C's Legendre transform and Lagrangian↔kinetic-energy identity,
§D's mass-shell defect, §E's force/equivalence-principle algebra, §F's metric identities, §G's
Christoffel/geodesic reduction and §H's Ricci/Poisson equation are exact; §A's and §F's `c → ∞` statements are
genuine `Filter.Tendsto` limits; §B/§C/§E/§G's derivatives are `HasDerivAt`. §G/§H are the standard weak-field,
slow-motion, static reduction in one spatial dimension (`Γˣ₀₀ = ∂_xΦ/c²`, `R₀₀ = ∇²Φ/c²`), with the linearized
Christoffel and Ricci written directly rather than obtained from the metric via the connection. The library
*does* carry the tensor API to close that gap — `Curvature.RiemannCurvatureTensor` (`ricci`,
`scalarCurvature`, `constantCurvature`), `ComplexEinstein.EinsteinFieldEquationsPhysLean` (`einsteinTensor`
`G = R − ½Rg`, `einsteinFieldEquation` `G = κT`) and `EntropicTime.ConnectionCovariantHessian`
(`IsTorsionFree`, `covariantHessian`) — and the companion module `NewtonianLimitCurvatureAPI` re-derives the
Newtonian `R₀₀` through the library `ricci` contraction and reads the field equation off the library
`einsteinFieldEquation`, so these quantities are grounded, not posited. The exact nonlinear ADM constraint
(`TetradADMGravity.sourcedHamiltonianConstraint`) whose limit §H is remains cited.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
open ClassicalMechanics
open Filter Topology


/-- **The free-particle Hamiltonian** `H(p) = p²/2m`: the momentum-space energy whose canonical equations
are Newton's laws (§B). -/
noncomputable def newtonianHamiltonian (m p : ℝ) : ℝ := p ^ 2 / (2 * m)

/-- **The Newtonian Hamiltonian in rapidity form** `p²/2m = mc²·sinh²θ/2`: with the momentum
`p = mc·sinh θ` of the boosted clock (`einsteinEnergy_eq_rest_cosh_rapidity`), the free kinetic energy is the
second-order (`sinh²θ`) part of the boost — exactly the `½mv²` term, `v = c·sinh θ` to leading order. -/
lemma newtonianHamiltonian_eq_rapidity (m c θ : ℝ) (hm : m ≠ 0) :
    newtonianHamiltonian m (m * c * Real.sinh θ) = m * c ^ 2 * Real.sinh θ ^ 2 / 2 := by
  unfold newtonianHamiltonian
  field_simp

/-- **[Newtonian limit] the free Hamiltonian is the `c → ∞` limit of the relativistic clock energy**
`lim_{c→∞}(E − mc²) = p²/2m`: the relativistic kinetic energy `√((mc²)²+(pc)²) − mc²` of the moving Compton
clock tends to the Newtonian Hamiltonian, a genuine `Filter.Tendsto` limit (reusing the proven
`EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger`). -/
lemma newtonianHamiltonian_is_nonrel_limit (m p : ℝ) (hm : 0 < m) :
    Filter.Tendsto
      (fun c => Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency.einsteinEnergy
        m c p - m * c ^ 2)
      Filter.atTop (nhds (newtonianHamiltonian m p)) := by
  unfold newtonianHamiltonian
  exact Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger
    m p hm


/-- **[Hamilton's first equation] `∂H/∂p = p/m = v`**: the velocity is the momentum derivative of the
Hamiltonian, `q̇ = ∂H/∂p = p/m`, i.e. the Newtonian relation `p = mv`. -/
lemma hamilton_velocity (m p : ℝ) :
    HasDerivAt (fun p' => newtonianHamiltonian m p') (p / m) p := by
  have h : HasDerivAt (fun p' : ℝ => p' ^ 2) (2 * p) p := by simpa using hasDerivAt_pow 2 p
  have h2 : HasDerivAt (fun p' : ℝ => p' ^ 2 / (2 * m)) (2 * p / (2 * m)) p := h.div_const (2 * m)
  have hv : 2 * p / (2 * m) = p / m := by
    rw [mul_comm 2 p, mul_comm 2 m, mul_div_mul_right p m two_ne_zero]
  rw [hv] at h2
  simpa [newtonianHamiltonian] using h2

/-- **[Hamilton's second equation, free particle] `∂H/∂q = 0 ⇒ ṗ = 0`**: the free Hamiltonian is
independent of position, so `ṗ = −∂H/∂q = 0` — Newton's first law, momentum is conserved. -/
lemma hamilton_force_free (m p q : ℝ) :
    HasDerivAt (fun _ : ℝ => newtonianHamiltonian m p) 0 q :=
  hasDerivAt_const q (newtonianHamiltonian m p)


/-- **The free-particle Lagrangian** `L(v) = ½mv²`: the velocity-space kinetic energy whose Euler–Lagrange
equation is Newton's second law. -/
noncomputable def newtonianLagrangian (m v : ℝ) : ℝ := m * v ^ 2 / 2

/-- **[Canonical momentum] `∂L/∂v = mv = p`**: the velocity derivative of the Lagrangian is the momentum,
the Legendre-conjugate variable of §B. -/
lemma lagrange_momentum (m v : ℝ) :
    HasDerivAt (fun v' => newtonianLagrangian m v') (m * v) v := by
  have h : HasDerivAt (fun v' : ℝ => v' ^ 2) (2 * v) v := by simpa using hasDerivAt_pow 2 v
  have h2 : HasDerivAt (fun v' : ℝ => m * v' ^ 2 / 2) (m * (2 * v) / 2) v :=
    (h.const_mul m).div_const 2
  have hv : m * (2 * v) / 2 = m * v := by ring
  rw [hv] at h2
  simpa [newtonianLagrangian] using h2

/-- **[Legendre transform] `p·v − L = H`**: the Legendre transform of the free Lagrangian, at the canonical
momentum `p = mv`, is exactly the Newtonian Hamiltonian `p²/2m` of §A — closing the Hamiltonian and
Lagrangian pictures. -/
lemma legendre_transform_free (m v : ℝ) (hm : m ≠ 0) :
    (m * v) * v - newtonianLagrangian m v = newtonianHamiltonian m (m * v) := by
  unfold newtonianLagrangian newtonianHamiltonian
  field_simp
  ring

/-- **The free Lagrangian is the free-particle kinetic energy**
`newtonianLagrangian m (q̇) = FreeParticle.kineticEnergy`: at velocity `v = q̇`, `L = ½mv²` is exactly
`ClassicalMechanics.FreeParticle.kineticEnergy`, whose Euler–Lagrange equation is
`FreeParticle.NewtonsSecondLaw` (`m·q̈ = 0`, `accel_zero`). This grounds the Lagrangian side in the
existing free-particle Newton machinery. -/
lemma newtonianLagrangian_eq_freeParticle_kineticEnergy
    (s : ClassicalMechanics.FreeParticle)
    (q : ClassicalMechanics.FreeParticle.Trajectory) (t : Time) :
    newtonianLagrangian s.mass (s.velocity q t) = s.kineticEnergy q t := by
  unfold newtonianLagrangian ClassicalMechanics.FreeParticle.kineticEnergy
  ring


/-- **[Mass-shell defect is the Newtonian energy] `(E/c)² − (mc)² = 2m·H`**: the Minkowski mass-shell defect
of the full Einstein 4-momentum (`einstein_massShell`, `(E/c)² − p² = (mc)²`) equals twice the mass times the
Newtonian Hamiltonian `H = p²/2m`. The flat energy–momentum invariant of the tangent space *is* the
Newtonian energy content — the bridge from §A to the Lorentz/GR mass-shell. -/
lemma massShell_defect_eq_twice_mass_hamiltonian (m c p : ℝ) (hc : c ≠ 0) (hm : m ≠ 0) :
    (einsteinEnergy m c p / c) ^ 2 - (m * c) ^ 2 = 2 * m * newtonianHamiltonian m p := by
  have h := einstein_massShell m c p hc
  have hrhs : 2 * m * newtonianHamiltonian m p = p ^ 2 := by
    unfold newtonianHamiltonian; field_simp
  rw [hrhs]; linarith [h]


/-- **[Newton's second law with a force] Hamilton's `ṗ = −∂H/∂x = F`**: for the interacting Hamiltonian
`H = p²/2m + V(x)`, the position derivative is `V'(x)`, so `ṗ = −V'(x)` is the force `F = −∂V/∂x` — Newton's
second law with a potential, upgrading the free case (`hamilton_force_free`) of §B. -/
lemma hamilton_force (m p x : ℝ) (V : ℝ → ℝ) (F' : ℝ) (hV : HasDerivAt V F' x) :
    HasDerivAt (fun x' => newtonianHamiltonian m p + V x') F' x := by
  have h := (hasDerivAt_const x (newtonianHamiltonian m p)).add hV
  rwa [zero_add] at h

/-- **The gravitational potential energy** `V = m·Φ` has position derivative `m·Φ'(x)`: the gravitational
force `F = −m·Φ'(x)` is proportional to the (gravitational, source) mass `m`. -/
lemma gravitational_force (m x : ℝ) (Φ : ℝ → ℝ) (g : ℝ) (hΦ : HasDerivAt Φ g x) :
    HasDerivAt (fun x' => m * Φ x') (m * g) x :=
  hΦ.const_mul m

/-- **[Equivalence principle] the gravitational acceleration is mass-independent** `a = F/m = −Φ'(x)`:
Newton's second law `m·a = −m·Φ'(x)` cancels the mass — the gravitational mass appearing in the force equals
the inertial mass in `m·a`, so the acceleration `a = −Φ'(x)` is the same for every body, independent of `m`.
This is the concrete form of the equivalence principle behind §D's
`fourMomentum_norm_tetrad_gauge_invariant`. -/
lemma equivalence_principle_acceleration (m g : ℝ) (hm : m ≠ 0) :
    (-(m * g)) / m = -g := by
  rw [neg_div, mul_div_cancel_left₀ g hm]


/-- **The weak-field metric time–time component** `g₀₀ = 1 + 2Φ/c²`: the Newtonian potential `Φ` is the
leading general-relativistic correction to the flat time metric `η₀₀ = 1`. -/
noncomputable def weakFieldG00 (Φ c : ℝ) : ℝ := 1 + 2 * Φ / c ^ 2

/-- **The flat metric is the zero-potential value** `g₀₀|_{Φ=0} = 1 = η₀₀`: with no gravitational potential
the weak-field metric is the flat Minkowski time component of §D. -/
lemma weakFieldG00_flat (c : ℝ) : weakFieldG00 0 c = 1 := by
  unfold weakFieldG00; simp

/-- **The Newtonian potential is read back from the metric** `Φ = (g₀₀ − 1)·c²/2`: the metric perturbation
`h₀₀ = g₀₀ − 1 = 2Φ/c²` is exactly twice the Newtonian potential in units of `c²` — the general-relativistic
field variable and the Newtonian potential are the same datum. -/
lemma newtonianPotential_from_weakFieldG00 (Φ c : ℝ) (hc : c ≠ 0) :
    (weakFieldG00 Φ c - 1) * c ^ 2 / 2 = Φ := by
  unfold weakFieldG00; field_simp; ring

/-- **[GR → Newton] the weak-field metric is Schwarzschild to first order** `g₀₀ = 1 − r_s/r`: for the
point-mass potential `Φ = −GM/r`, the weak-field time–time metric equals `1 − r_s/r` with
`r_s = schwarzschildRadius M G c` (`Relativity.SemiClassical.schwarzschildRadius`, `= 2GM/c²`). The Newtonian
potential of §E is the leading term of the Schwarzschild metric; the geodesic in this metric returns Newton's
`ẍ = −∇Φ`. -/
lemma weakFieldG00_schwarzschild (M G c r : ℝ) (hc : c ≠ 0) (hr : r ≠ 0) :
    weakFieldG00 (-(G * M / r)) c
      = 1 - Physlib.Relativity.SemiClassical.schwarzschildRadius M G c / r := by
  unfold weakFieldG00 Physlib.Relativity.SemiClassical.schwarzschildRadius
  field_simp
  ring

/-- **[Newtonian `c → ∞` limit] the metric flattens** `lim_{c→∞} g₀₀ = 1`: as `c → ∞` the weak-field metric
tends to the flat Minkowski value, the GR counterpart of §A's kinetic-energy limit — the curvature correction
`2Φ/c²` vanishes and Newtonian absolute time is recovered. -/
lemma weakFieldG00_tendsto_flat (Φ : ℝ) :
    Filter.Tendsto (fun c => weakFieldG00 Φ c) Filter.atTop (nhds 1) := by
  unfold weakFieldG00
  have h : Filter.Tendsto (fun c : ℝ => 2 * Φ / c ^ 2) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop (by norm_num))
  simpa using tendsto_const_nhds.add h


/-- **The metric gradient** `∂_x g₀₀ = 2Φ'/c²`: differentiating the weak-field time–time metric
`g₀₀ = 1 + 2Φ(x)/c²` in the (static) spatial coordinate gives twice the potential gradient in units of
`c²`. -/
lemma weakFieldG00_hasDerivAt (Φ : ℝ → ℝ) (dΦ c x : ℝ) (hΦ : HasDerivAt Φ dΦ x) :
    HasDerivAt (fun x' => weakFieldG00 (Φ x') c) (2 * dΦ / c ^ 2) x := by
  unfold weakFieldG00
  have h := (hasDerivAt_const x (1 : ℝ)).add ((hΦ.const_mul 2).div_const (c ^ 2))
  rwa [zero_add] at h

/-- **The weak-field Christoffel symbol** `Γˣ₀₀ = ∂_xΦ/c²`: for the static weak field with flat spatial
metric, the only geodesic-relevant connection component is `Γˣ₀₀ = ½ gˣˣ(−∂_x g₀₀) = ½ ∂_x g₀₀ = ∂_xΦ/c²`
(`weakFieldChristoffel_eq_half_metricGradient`). It carries no particle mass — it is pure geometry. -/
noncomputable def weakFieldChristoffel (dΦ c : ℝ) : ℝ := dΦ / c ^ 2

/-- **The Christoffel symbol is half the metric gradient** `Γˣ₀₀ = ½ ∂_x g₀₀`: with flat spatial metric
`gˣˣ = −1`, the standard formula `Γˣ₀₀ = −½ gˣˣ ∂_x g₀₀` is `½ ∂_x g₀₀`, i.e. half the metric gradient
`2Φ'/c²` of `weakFieldG00_hasDerivAt`. -/
lemma weakFieldChristoffel_eq_half_metricGradient (dΦ c : ℝ) :
    weakFieldChristoffel dΦ c = (1 / 2) * (2 * dΦ / c ^ 2) := by
  unfold weakFieldChristoffel; ring

/-- **[GR ⇒ Newton] the weak-field geodesic is Newton's gravity** `ẍ = −Γˣ₀₀·(dx⁰/dτ)² = −∂_xΦ`: for a slow
particle (`dx⁰/dτ ≈ c`, `dτ ≈ dt`) the spatial geodesic equation `ẍ + Γˣ₀₀ c² = 0` becomes Newton's
gravitational acceleration `ẍ = −(∂_xΦ/c²)·c² = −∂_xΦ`. No mass enters — the geodesic is mass-independent by
construction. -/
lemma weakField_geodesic_acceleration_eq_newton (dΦ c : ℝ) (hc : c ≠ 0) :
    -(weakFieldChristoffel dΦ c) * c ^ 2 = -dΦ := by
  unfold weakFieldChristoffel
  field_simp

/-- **[The geometric origin of the equivalence principle]** the mass-free GR geodesic acceleration equals the
mass-cancelled Newtonian acceleration `a = −∂_xΦ` of §E: the weak-field geodesic
(`weakField_geodesic_acceleration_eq_newton`, no mass present) and Newton's second law for gravity
(`equivalence_principle_acceleration`, inertial mass cancels gravitational mass) give the *same* acceleration
`−∂_xΦ`. GR explains *why* the equivalence principle holds — gravity is the geometry of the geodesic, not a
mass-dependent force. -/
lemma geodesic_recovers_newton_gravity (m dΦ c : ℝ) (hc : c ≠ 0) (hm : m ≠ 0) :
    -(weakFieldChristoffel dΦ c) * c ^ 2 = (-(m * dΦ)) / m := by
  rw [weakField_geodesic_acceleration_eq_newton dΦ c hc, equivalence_principle_acceleration m dΦ hm]


/-- **The linearized time–time Ricci curvature** `R₀₀ = ∇²Φ/c²`: for the weak static field the standard
Newtonian-limit value of the time–time Ricci tensor is the Laplacian of the potential in units of `c²`
(`d2Φ = ∇²Φ`, the 1D `Φ''`). It equals half the second spatial derivative of the metric,
`R₀₀ = ½ ∂²_x g₀₀` (`weakFieldRicci00_eq_half_metric_secondDeriv`, since `∂²_x g₀₀ = 2Φ''/c²`), the
curvature counterpart of the Christoffel `Γˣ₀₀ = ½ ∂_x g₀₀` of §G. -/
noncomputable def weakFieldRicci00 (d2Φ c : ℝ) : ℝ := d2Φ / c ^ 2

/-- **The Ricci curvature is half the metric's second gradient** `R₀₀ = ½ ∂²_x g₀₀`: the metric second
derivative is `∂²_x g₀₀ = 2Φ''/c²` (differentiating `weakFieldG00_hasDerivAt`), and the linearized Ricci is
half of it, matching `Γˣ₀₀ = ½ ∂_x g₀₀`. -/
lemma weakFieldRicci00_eq_half_metric_secondDeriv (d2Φ c : ℝ) :
    weakFieldRicci00 d2Φ c = (1 / 2) * (2 * d2Φ / c ^ 2) := by
  unfold weakFieldRicci00; ring

/-- **[Einstein ⇒ Newton] the field equation in the weak static limit is the Poisson equation**
`∇²Φ = 4πGρ`: the trace-reversed Einstein equation `R₀₀ = (8πG/c⁴)(T₀₀ − ½T g₀₀) = 4πGρ/c²` for dust
(`T₀₀ = ρc²`), with the linearized `R₀₀ = ∇²Φ/c²`, is exactly Newton's gravitational Poisson equation. This is
the source counterpart of §G's geodesic: §G is how matter *moves* in the metric, §H is how matter *curves* it,
both reducing to Newton. It is the weak-field limit of the ADM energy constraint
`TetradADMGravity.sourcedHamiltonianConstraint` (`³R + (tr K)² − K·K = κρ`, the Einstein `G_{nn}`). -/
lemma weakField_einstein_poisson (d2Φ c G ρ : ℝ) (hc : c ≠ 0)
    (hEin : weakFieldRicci00 d2Φ c = 4 * Real.pi * G * ρ / c ^ 2) :
    d2Φ = 4 * Real.pi * G * ρ := by
  unfold weakFieldRicci00 at hEin
  rw [div_eq_div_iff (pow_ne_zero 2 hc) (pow_ne_zero 2 hc)] at hEin
  exact mul_right_cancel₀ (pow_ne_zero 2 hc) hEin

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.newtonianHamiltonian_eq_rapidity where
  formalizes @ "claim:the-newtonian-hamiltonian-is-the-nonrelativistic-limit-of-the-clock-rapidity-energy",
  supported_by @ "paper:caticha-entropic-dynamics",
  caveat @ "claim:the-clock-energy-mc2-cosh-eta-is-the-carrier-newton-is-its-small-rapidity-expansion"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.newtonianPotential_from_weakFieldG00 where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-newtonian-potential-is-read-off-the-weak-field-metric-g00",
  requires @ "claim:the-newtonian-hamiltonian-is-the-nonrelativistic-limit-of-the-clock-rapidity-energy"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.weakFieldG00_schwarzschild where
  formalizes @ "claim:the-weak-field-g00-agrees-with-the-schwarzschild-metric-to-first-order",
  requires @ "claim:the-newtonian-potential-is-read-off-the-weak-field-metric-g00",
  caveat @ "claim:first-order-weak-field-agreement-not-the-full-nonlinear-metric"

zil_file_contract physlib.newtonianAndGRLimit where
  promises "Newton and the GR weak field from the clock: the Newtonian Hamiltonian is the small-rapidity limit of the clock energy mc2 cosh eta, the Newtonian potential is read off the weak-field metric component g00, and that g00 agrees with the Schwarzschild metric to first order."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.newtonianHamiltonian",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.weakFieldG00"]
  forbids_substitutes ["the full nonlinear Einstein metric, only the first-order weak field is matched"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.newtonianHamiltonian_eq_rapidity,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.newtonianPotential_from_weakFieldG00,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.weakFieldG00_schwarzschild]

/- ZIL-END -/

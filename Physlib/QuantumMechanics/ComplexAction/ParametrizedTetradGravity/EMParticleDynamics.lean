/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.YorkADMEnergy
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone

/-!
# The Einstein–Maxwell-particle dynamics: Coulomb, radiation gauge & the weak ADM energy (Alba–Lusanna 2012)

Formalizes the dynamical layer of *D. Alba, L. Lusanna, Can. J. Phys. 90 (2012) 1017* — the **generalized
Coulomb interaction**, the **transverse-EM radiation gauge**, and the structure of the **weak ADM energy** (the
Dirac Hamiltonian) — completing `ParametrizedTetradGravity.YorkADMEnergy` (the York-time energy term).

* the noninertial generalization of the **Coulomb potential** among the charged particles is `Q₁Q₂/(4πr)`
  (`coulombPotential`) — *literally* the charges times the retarded kernel's Coulomb tail `1/4πr`
  (`CanonicalTetradGravity.RetardedKernelLightCone.retardedAmplitude`); like charges repel (`coulomb_repulsive`);
* the **radiation gauge** decomposes the EM field `A = A_T + A_L` into a transverse (physical, Dirac-observable)
  part `A_T = P A` and a longitudinal (Coulomb) part `A_L = A − PA`, with `P` the **transverse projector**
  (idempotent, `RadiationGauge`); `A_T` is transverse (`longitudinal_killed`, `P A_L = 0`);
* the **weak ADM energy** `Ê_ADM` (the Dirac Hamiltonian) is `tidal-kinetic + curvature + York-time + EM +
  Coulomb` (`weakADMEnergy`), in which the inertial **York-time term is negative** (`yorkKineticTerm`), so the
  York time *lowers* the energy (`weakADMEnergy_york_le`).

The four sets of Hamilton equations are: (i) the **contracted Bianchi identities** (the time-preservation of
the super-Hamiltonian/super-momentum constraints — the first-class closure of `NonHermitianComplexAction.DiracConstraints`),
(ii) the inertial gauge variables (lapse/shift/York time), (iii) the tidal variables (the canonical
`sympForm` pair `(R_ā, Π_ā)` of `CanonicalTetradGravity.TidalPairsGWDispersion`), (iv) the matter (the Coulomb-coupled
particles). The explicit volume integrals and PDEs are the analytic layer; the Coulomb/radiation-gauge/energy
kernel is formalized here.

* **§A — the generalized Coulomb interaction** (`coulombPotential`, `coulombPotential_eq`, `coulomb_symm`,
  `coulomb_repulsive`).
* **§B — the transverse-EM radiation gauge** (`RadiationGauge`, `helmholtz_decomp`, `transverse_fixed`,
  `longitudinal_killed`).
* **§C — the weak ADM energy** (`weakADMEnergy`, `weakADMEnergy_york_le`).

## References

* D. Alba, L. Lusanna, Can. J. Phys. 90 (2012) 1017 (the Coulomb interaction, the radiation gauge, the weak
  ADM energy, the four sets of Hamilton equations).
* Repo carriers: `CanonicalTetradGravity.RetardedKernelLightCone` (`retardedAmplitude = 1/4πr`), `ParametrizedTetradGravity.YorkADMEnergy`
  (`yorkKineticTerm`), `NonHermitianComplexAction.DiracConstraints` (the first-class constraint algebra = the Bianchi set).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.EMParticleDynamics

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone
open Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.YorkADMEnergy


/-- **[Generalized Coulomb potential] `V = Q₁Q₂/(4πr)`** — the noninertial analogue of the Coulomb interaction
among the charged particles, the charges times the retarded kernel's Coulomb tail
(`retardedAmplitude = 1/4πr`). -/
noncomputable def coulombPotential (Q1 Q2 r : ℝ) : ℝ := Q1 * Q2 * retardedAmplitude r

/-- **`V = Q₁Q₂/(4πr)`** — the explicit Coulomb form. -/
lemma coulombPotential_eq (Q1 Q2 r : ℝ) :
    coulombPotential Q1 Q2 r = Q1 * Q2 / (4 * Real.pi * r) := by
  rw [coulombPotential, retardedAmplitude]; ring

/-- **The Coulomb interaction is symmetric** `V(Q₁,Q₂) = V(Q₂,Q₁)` (Newton's third law). -/
lemma coulomb_symm (Q1 Q2 r : ℝ) : coulombPotential Q1 Q2 r = coulombPotential Q2 Q1 r := by
  rw [coulombPotential, coulombPotential, mul_comm Q1 Q2]

/-- **[Like charges repel] `V > 0` for `Q₁Q₂ > 0`** at positive separation — the repulsive Coulomb potential. -/
lemma coulomb_repulsive (Q1 Q2 r : ℝ) (hQ : 0 < Q1 * Q2) (hr : 0 < r) :
    0 < coulombPotential Q1 Q2 r :=
  mul_pos hQ (retardedAmplitude_pos r hr)


variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **[Radiation gauge] a transverse projector** — an idempotent linear map `P` (`P∘P = P`) splitting the EM
field into transverse (`A_T = PA`, the physical Dirac observable) and longitudinal (`A_L = A − PA`, the
Coulomb) parts. -/
structure RadiationGauge (P : V →ₗ[ℝ] V) : Prop where
  /-- `P` is idempotent. -/
  idem : ∀ a, P (P a) = P a

/-- **[Helmholtz decomposition] `A = A_T + A_L`** — every EM field splits into its transverse `PA` and
longitudinal `A − PA` parts. -/
lemma helmholtz_decomp (P : V →ₗ[ℝ] V) (A : V) : A = P A + (A - P A) := by abel

/-- **The transverse part is fixed by `P`** `P A_T = A_T` — `A_T = PA` is already transverse. -/
lemma transverse_fixed (P : V →ₗ[ℝ] V) (h : RadiationGauge P) (A : V) : P (P A) = P A := h.idem A

/-- **[`A_T` is transverse] the longitudinal part is killed by `P`** `P A_L = 0` — `P (A − PA) = 0`, so the
radiation-gauge transverse field carries no longitudinal (Coulomb) component. -/
lemma longitudinal_killed (P : V →ₗ[ℝ] V) (h : RadiationGauge P) (A : V) :
    P (A - P A) = 0 := by rw [map_sub, h.idem, sub_self]


/-- **[The weak ADM energy] `Ê_ADM = tidal-kinetic + curvature + York-time + EM + Coulomb`** — the Dirac
Hamiltonian as the sum of its contributions: the (positive) tidal kinetic and curvature energy, the (negative)
inertial York-time term `yorkKineticTerm`, the EM field energy, and the particle Coulomb interaction. -/
noncomputable def weakADMEnergy (tidalKinetic curvature yorkA K3 emEnergy Q1 Q2 r : ℝ) : ℝ :=
  tidalKinetic + curvature + yorkKineticTerm yorkA K3 + emEnergy + coulombPotential Q1 Q2 r

/-- **[The York time lowers the ADM energy] `Ê_ADM ≤ Ê_ADM∖{York time}`.** The inertial York-time contribution
is non-positive (`yorkKineticTerm_nonpos`), so including it can only decrease the weak ADM energy — the
general-relativistic inertial effect (vanishing only in the `³K = 0` gauge). -/
lemma weakADMEnergy_york_le (tidalKinetic curvature yorkA K3 emEnergy Q1 Q2 r : ℝ)
    (ha : 0 ≤ yorkA) :
    weakADMEnergy tidalKinetic curvature yorkA K3 emEnergy Q1 Q2 r
      ≤ tidalKinetic + curvature + emEnergy + coulombPotential Q1 Q2 r := by
  rw [weakADMEnergy]
  have := yorkKineticTerm_nonpos yorkA K3 ha
  linarith

end Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.EMParticleDynamics

end

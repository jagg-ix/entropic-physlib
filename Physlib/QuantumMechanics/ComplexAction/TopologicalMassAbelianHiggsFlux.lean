/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Topological mass vs. the Abelian Higgs vortex: mass and flux without a vacuum expectation value

Section II.A of Deser–Jackiw–Templeton, *Topologically Massive Gauge Theories* (Ann. Phys. **281**
(2000) 409, `Deser:1982vy`), continuing `TopologicallyMassiveGauge`: the paper's explicit analogy
(around Eqs. 2.16–2.19) between the topologically massive vector theory and the three-dimensional
**Abelian Higgs model**. Both give a **gauge-invariantly massive** vector field, but by opposite means:

  * the **Higgs** mechanism gives the gauge boson its mass `m_A = e·v` from a nonzero **vacuum
    expectation value** `v = ⟨φ⟩`, and its vortex carries a **quantized** magnetic flux
    `Φ_n = 2πn/e` (`n ∈ ℤ`, the winding), the vortex being electrically neutral;
  * the **topological** mass `μ` enters the Lagrangian gauge-invariantly with **no scalar field and no
    VEV**, and produces a flux **directly proportional to the charge**, `−∫B = Q/μ` (Eq. 2.16),
    with *"no reason for quantizing any of the parameters"* (Deser et al., p. 415).

So the topological mass is a concrete counter-example to the necessity of a Higgs VEV: a massive gauge
field with magnetic flux, generated with no vacuum expectation value. (The Higgs boson, its potential,
its VEV `v² = μ²/λ`, and the VEV/DJT separation are formalized in `Particles.HiggsBoson`; this file adds
the flux analogy and the mass-without-VEV contrast.)

* **§A — the topological flux** `Φ = −Q/μ` (Eq. 2.16). `deserFlux`, `deserFlux_mul_mass` (`μΦ = −Q`),
  `deserFlux_proportional` (linear in the charge — *continuous*, unquantized).
* **§B — the Higgs vortex flux** `Φ_n = 2πn/e`. `higgsVortexFlux`, `higgsVortexFlux_quantum` (successive
  windings differ by the quantum `2π/e`), `higgsVortexFlux_winding` (`eΦ/2π = n ∈ ℤ`).
* **§C — the contrast.** `deserFlux_eq_higgsVortex_iff`: the continuous topological flux coincides with a
  quantized Higgs value only for a fine-tuned charge. `massive_without_vev`: at zero VEV the Higgs gauge
  mass `e·v` vanishes while the topological mass `μ` stays positive — a gauge mass with no VEV.

**Honest layering.** Proven: the algebra of the two flux formulae, the quantization of the vortex flux,
and the mass-without-VEV contrast. Interpretive: identifying `Φ` with the integrated magnetic field,
`Q` with the total charge, `v` with the Higgs VEV, and reading `massive_without_vev` as "the Higgs VEV
is not necessary for a gauge-boson mass," is the physical content of the Deser–Jackiw–Templeton analogy;
the field theory itself lives in `TopologicallyMassiveGauge` / `Particles.HiggsBoson`.

## References

* S. Deser, R. Jackiw, S. Templeton, Ann. Phys. **281** (2000) 409 (§II.A, Eqs. 2.16–2.19, p. 415).
  Complements `TopologicallyMassiveGauge` and `Particles.HiggsBoson`.


-/

set_option autoImplicit false

open Real (pi)

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TopologicalMassAbelianHiggsFlux


/-- **The topological magnetic flux** `Φ = −Q/μ` (Eq. 2.16): with the topological mass `μ`, the total
magnetic flux is directly proportional to the total charge `Q`. No scalar field or VEV is involved. -/
noncomputable def deserFlux (Q mu : ℝ) : ℝ := -Q / mu

/-- **Eq. 2.16 rearranged** `μ·Φ = −Q`: the topological mass times the flux is minus the charge. -/
lemma deserFlux_mul_mass (Q mu : ℝ) (hmu : mu ≠ 0) : mu * deserFlux Q mu = -Q := by
  unfold deserFlux; field_simp

/-- **The topological flux is proportional to the charge** `Φ(kQ) = k·Φ(Q)`: it varies *continuously*
with `Q` — there is no quantization. -/
lemma deserFlux_proportional (k Q mu : ℝ) : deserFlux (k * Q) mu = k * deserFlux Q mu := by
  unfold deserFlux; ring


/-- **The Abelian Higgs vortex flux** `Φ_n = 2πn/e` (`n ∈ ℤ` the winding number): the vortex of the
three-dimensional Higgs model carries a magnetic flux quantized in units of `2π/e`. -/
noncomputable def higgsVortexFlux (e : ℝ) (n : ℤ) : ℝ := 2 * pi * (n : ℝ) / e

/-- **The flux is quantized** `Φ_{n+1} − Φ_n = 2π/e`: successive windings differ by the flux quantum. -/
lemma higgsVortexFlux_quantum (e : ℝ) (n : ℤ) (he : e ≠ 0) :
    higgsVortexFlux e (n + 1) - higgsVortexFlux e n = 2 * pi / e := by
  unfold higgsVortexFlux; push_cast; field_simp; ring

/-- **The winding number is an integer** `eΦ_n/(2π) = n`: the dimensionless flux is exactly `n ∈ ℤ`. -/
lemma higgsVortexFlux_winding (e : ℝ) (n : ℤ) (he : e ≠ 0) :
    e * higgsVortexFlux e n / (2 * pi) = (n : ℝ) := by
  unfold higgsVortexFlux
  field_simp [Real.pi_ne_zero]


/-- **The topological flux hits a quantized Higgs value only for a fine-tuned charge**
`Φ_top = Φ_n ↔ Q·e = −2πnμ`: the *continuous* topological flux `−Q/μ` coincides with a *quantized*
Higgs vortex flux `2πn/e` only when the charge is fine-tuned — generically it does not. -/
lemma deserFlux_eq_higgsVortex_iff (Q mu e : ℝ) (n : ℤ) (hmu : mu ≠ 0) (he : e ≠ 0) :
    deserFlux Q mu = higgsVortexFlux e n ↔ Q * e = -(2 * pi * (n : ℝ) * mu) := by
  unfold deserFlux higgsVortexFlux
  rw [div_eq_div_iff hmu he]
  constructor <;> intro h <;> linarith

/-- **The Abelian-Higgs gauge-boson mass** `m_A = e·v`: generated by the vacuum expectation value `v`. -/
noncomputable def higgsGaugeBosonMass (e v : ℝ) : ℝ := e * v

/-- **The Higgs gauge mass vanishes without a VEV** `m_A = 0 ↔ e = 0 ∨ v = 0`: the Higgs mechanism
*requires* a nonzero vacuum expectation value to give the gauge boson a mass. -/
lemma higgsGaugeBosonMass_eq_zero_iff (e v : ℝ) :
    higgsGaugeBosonMass e v = 0 ↔ e = 0 ∨ v = 0 :=
  mul_eq_zero

/-- **The topological mass** `μ` — a Lagrangian coupling, carrying no vacuum expectation value. -/
def deserTopologicalMass (mu : ℝ) : ℝ := mu

/-- **A gauge-boson mass without a VEV**: at zero vacuum expectation value (`v = 0`, unbroken symmetry)
the Higgs gauge mass `e·v` vanishes, yet the topological mass `μ` stays positive — a gauge-invariant
mass generated with no Higgs VEV. This is the Deser–Jackiw–Templeton counter-example to the necessity of
a vacuum expectation value. -/
lemma massive_without_vev (mu e : ℝ) (hmu : 0 < mu) :
    higgsGaugeBosonMass e 0 = 0 ∧ 0 < deserTopologicalMass mu := by
  refine ⟨?_, hmu⟩
  simp [higgsGaugeBosonMass]

/-! ## The Mexican-hat vacuum manifold behind the VEV

Ports the verified core of `CATEPTMain/Integration/ElectroweakCATEPTBridge.lean` (reference
tree, own authorship; the CATEPT plugin-slot glue is not reproduced): the quartic Higgs
potential whose degenerate minima *are* the vacuum expectation value `±v` that
`higgsGaugeBosonMass` consumes — completing this file's comparison, since the topological
mass route needs no such vacuum manifold.  In the CATEPT Euclidean reading `V(φ)` is the
imaginary action of the Higgs sector and `V = 0` on the vacuum manifold means the entropic
clock does not tick in the broken vacuum. -/

/-- **The Higgs Mexican-hat potential** `V(φ) = (λ/4)·(φ² − v²)²`: quartic coupling `λ`,
vacuum radius `v`. -/
noncomputable def higgsVacuumPotential (v lam φ : ℝ) : ℝ :=
  lam / 4 * (φ ^ 2 - v ^ 2) ^ 2

/-- The Mexican-hat potential is nonnegative for `λ ≥ 0`. -/
lemma higgsVacuumPotential_nonneg (v lam φ : ℝ) (hlam : 0 ≤ lam) :
    0 ≤ higgsVacuumPotential v lam φ :=
  mul_nonneg (by linarith) (sq_nonneg _)

/-- The potential is even in the field: `V(−φ) = V(φ)` — the `ℤ₂` symmetry the vacuum
manifold spontaneously breaks. -/
lemma higgsVacuumPotential_even (v lam φ : ℝ) :
    higgsVacuumPotential v lam (-φ) = higgsVacuumPotential v lam φ := by
  unfold higgsVacuumPotential
  ring

/-- **The vacuum manifold is exactly `{±v}`**: for `λ > 0` the potential vanishes precisely
at the two degenerate minima `φ = ±v` — the spontaneously broken vacuum whose radius `v` is
the VEV entering `higgsGaugeBosonMass`. -/
lemma higgsVacuumPotential_eq_zero_iff (v lam φ : ℝ) (hlam : 0 < lam) :
    higgsVacuumPotential v lam φ = 0 ↔ φ = v ∨ φ = -v := by
  unfold higgsVacuumPotential
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (by positivity)
    · have hsq : φ ^ 2 = v ^ 2 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        linarith [sub_eq_zero.mp this]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  · rintro (rfl | rfl)
    · right
      ring
    · right
      ring

/-- **The broken vacuum is the global minimum**: `V(±v) = 0 ≤ V(φ)` for all `φ`. -/
lemma higgsVacuumPotential_vev_min (v lam φ : ℝ) (hlam : 0 ≤ lam) :
    higgsVacuumPotential v lam v ≤ higgsVacuumPotential v lam φ := by
  have hzero : higgsVacuumPotential v lam v = 0 := by
    unfold higgsVacuumPotential
    ring
  rw [hzero]
  exact higgsVacuumPotential_nonneg v lam φ hlam

end Physlib.QuantumMechanics.ComplexAction.TopologicalMassAbelianHiggsFlux

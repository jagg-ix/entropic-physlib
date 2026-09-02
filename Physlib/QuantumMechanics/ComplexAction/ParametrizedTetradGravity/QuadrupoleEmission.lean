/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

/-!
# The quadrupole emission formula & GW energy balance (Alba–Lusanna 2012, Part 2)

Formalizes the central result of *D. Alba, L. Lusanna, "The Einstein–Maxwell-particle system in the York
canonical basis of ADM tetrad gravity. Part 2", Can. J. Phys. 90 (2012) 1077* (§7.2–7.3) — the **quadrupole
emission formula** for the post-Minkowskian gravitational waves and the **energy balance** — completing the
Einstein-Maxwell-particle arc (`ParametrizedTetradGravity.EMParticleDynamics`, the dynamical layer).

The radiating source has a **reduced (traceless) mass quadrupole moment**
`Q_ij = m(x_i x_j − ⅓δ_ij r²)` (`quadrupoleMoment`), trace-free (`quadrupole_traceless`) — the transverse-
traceless structure of `CanonicalTetradGravity.HPMGravitationalWaves.gw_traceless`. Einstein's **quadrupole emission formula**
gives the radiated power

  `P = (G/5c⁵) Q⃛_ij Q⃛^ij`   (`quadrupolePower`),

a sum of squares, hence **non-negative** (`quadrupolePower_nonneg`) — energy flows *out*, never in — vanishing
exactly when the quadrupole's third time-derivative vanishes (`quadrupolePower_eq_zero_iff`; a static or
uniformly-moving source does not radiate). The **energy balance** is then `dÊ_ADM/dt = −P ≤ 0`
(`adm_energy_decreases`): the conserved ADM energy is carried away by the GWs — the back-reaction, recovered
without a gravitational self-force thanks to the Grassmann regularization.

* **§A — the reduced (traceless) mass quadrupole moment** (`quadrupoleMoment`, `quadrupole_traceless`,
  `quadrupole_symm`).
* **§B — the quadrupole emission power** (`quadrupolePower`, `quadrupolePower_nonneg`,
  `quadrupolePower_eq_zero_iff`).
* **§C — the energy balance** (`admEnergyRadiationRate`, `adm_energy_decreases`).

The multipolar expansion of the energy–momentum tensor (Dixon multipoles), the far-field PM `4`-metric, and
the explicit radiation-reaction force are the analytic layer; the quadrupole-power/energy-balance kernel is
formalized here.

## References

* D. Alba, L. Lusanna, Can. J. Phys. 90 (2012) 1077, §7.2–7.3 (the PM quadrupole emission formula, the energy
  balance); A. Einstein (the quadrupole formula `P = (G/5c⁵)⟨Q⃛_ij Q⃛^ij⟩`).
* Repo carrier: `CanonicalTetradGravity.HPMGravitationalWaves` (`gw_traceless`, the transverse-traceless GW),
  `ParametrizedTetradGravity.YorkADMEnergy` (the conserved weak ADM energy).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.QuadrupoleEmission

open Matrix Finset


/-- **The reduced mass quadrupole moment** `Q_ij = m(x_i x_j − ⅓δ_ij r²)` — the trace-free `3×3` tensor sourcing
the gravitational radiation. -/
noncomputable def quadrupoleMoment (m : ℝ) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => m * (x i * x j - (if i = j then (1 / 3) * ∑ k, x k ^ 2 else 0))

/-- **[Trace-free] `Tr Q = 0`** — the reduced quadrupole is traceless, the transverse-traceless structure of
the gravitational wave (`gw_traceless`); the trace is carried by the conformal factor, not the radiation. -/
lemma quadrupole_traceless (m : ℝ) (x : Fin 3 → ℝ) : (quadrupoleMoment m x).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, quadrupoleMoment, Matrix.of_apply, ↓reduceIte]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]; ring

/-- **The quadrupole moment is symmetric** `Q_ij = Q_ji`. -/
lemma quadrupole_symm (m : ℝ) (x : Fin 3 → ℝ) (i j : Fin 3) :
    quadrupoleMoment m x i j = quadrupoleMoment m x j i := by
  simp only [quadrupoleMoment, Matrix.of_apply, eq_comm (a := i) (b := j)]; ring_nf


/-- **[Einstein's quadrupole formula] the radiated power** `P = (G/5c⁵) Q⃛_ij Q⃛^ij` — the gravitational
luminosity, the contraction of the third time-derivative of the quadrupole with itself (`Q3 = Q⃛`). -/
noncomputable def quadrupolePower (G c : ℝ) (Q3 : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (G / (5 * c ^ 5)) * ∑ i, ∑ j, Q3 i j ^ 2

/-- **[Energy flows out] `P ≥ 0`** — the radiated power is a sum of squares, hence non-negative: the source
*emits* gravitational waves, it never absorbs from the radiation field. -/
lemma quadrupolePower_nonneg (G c : ℝ) (Q3 : Matrix (Fin 3) (Fin 3) ℝ) (hG : 0 ≤ G) (hc : 0 < c) :
    0 ≤ quadrupolePower G c Q3 := by
  rw [quadrupolePower]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- **[No radiation iff no quadrupole acceleration] `P = 0 ⟺ Q⃛ = 0`** (for `G, c > 0`) — a source whose mass
quadrupole has vanishing third time-derivative (static, uniformly moving, or spherically symmetric) emits no
gravitational waves. -/
lemma quadrupolePower_eq_zero_iff (G c : ℝ) (Q3 : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : 0 < G) (hc : 0 < c) : quadrupolePower G c Q3 = 0 ↔ ∀ i j, Q3 i j = 0 := by
  rw [quadrupolePower, mul_eq_zero, or_iff_right (by positivity)]
  constructor
  · intro h i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (Q3 i j))).mp h i (Finset.mem_univ i)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (Q3 i j))).mp h2 j (Finset.mem_univ j)
    exact pow_eq_zero_iff (by norm_num) |>.mp h3
  · intro h; simp [h]


/-- **[Energy balance] the ADM energy radiation rate** `dÊ_ADM/dt = −P` — the conserved weak ADM energy
decreases at exactly the radiated power. -/
noncomputable def admEnergyRadiationRate (G c : ℝ) (Q3 : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  -quadrupolePower G c Q3

/-- **[Back-reaction] `dÊ_ADM/dt ≤ 0`** — the ADM energy is monotonically carried away by gravitational
radiation; the conserved ADM energy supplies the GW luminosity (Grassmann-regularized, no self-force). -/
lemma adm_energy_decreases (G c : ℝ) (Q3 : Matrix (Fin 3) (Fin 3) ℝ) (hG : 0 ≤ G) (hc : 0 < c) :
    admEnergyRadiationRate G c Q3 ≤ 0 := by
  rw [admEnergyRadiationRate, neg_nonpos]
  exact quadrupolePower_nonneg G c Q3 hG hc

end Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.QuadrupoleEmission

end

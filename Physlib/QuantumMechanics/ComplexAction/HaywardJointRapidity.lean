/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction
public import Physlib.Relativity.Special.RapidityVibracy

/-!
# The Hayward joint term is a boost rapidity (Lehner–Myers–Poisson–Sorkin §II.D–E)

The second joint family of Lehner, Myers, Poisson & Sorkin (arXiv:1609.00207): where two **spacelike or
timelike** boundary segments meet, the boundary action acquires Hayward's joint term `±2∮_ℬ η dS`
(Eqs. 2.89, 2.94), where `η` is the **boost parameter** relating the two unit normals. This module
formalizes `η` and identifies it with the special-relativistic **rapidity** and **vibracy** of
`Physlib.Relativity.Special.RapidityVibracy` — the joint term of the gravitational action is a
Lorentz-boost rapidity read off a ratio of null projections.

The two orthonormal normal pairs `{n, r}` (on `𝒮`) and `{m, s}` (on `𝒯`) at the joint `ℬ` are related
by a Lorentz boost of rapidity `η`:

  `n^α = cosh η m^α + sinh η s^α`,   `r^α = sinh η m^α + cosh η s^α`   (Eq. 2.81),

with `sinh η = n·s` (Eq. 2.87) and, in terms of null normals `k^α`, `η = ln(−n·k) − ln(−s·k)`
(Eq. 2.91) — a **difference of logs**, i.e. a vibracy of the two null projections.

* **§A — the boost preserves orthonormality** (Eq. 2.81). `n·n = −1`, `n·r = 0` are preserved by the
  boost (`boostedNormal_timelike`, `boostedNormals_orthogonal`), via `cosh²η − sinh²η = 1`.
* **§B — the rapidity form** `sinh η = n·s`, `η = arsinh(n·s)` (Eqs. 2.87) — `haywardBoost`,
  `sinh_haywardBoost`.
* **§C — the vibracy form** `η = ln(−n·k) − ln(−s·k) = vibracy(−n·k, −s·k)` (Eq. 2.91) — the Hayward
  joint parameter **is** a `RapidityVibracy.vibracy` (`haywardJointEta_eq_vibracy`).
* **§D — the boost exponential** `exp η = (−n·k)/(−s·k)` and `cosh η + sinh η = exp η`
  (`exp_haywardJointEta`, `dopplerRatio_haywardJointEta`, reusing `dopplerRatio_eq_exp`).
* **§E — additivity of the joint rules** `η(A,C) = η(A,B) + η(B,C)` (Eqs. 2.95–2.98, the `η_a…η_g`
  chain) — `haywardJointEta_chain`.
* **§F — the joint boundary contribution** `±2∮η dS` (Eq. 2.94) — `haywardActionJoints`.
* **§G — the rapidity is the entanglement entropy** (full-circle): when the boost/Doppler ratio equals
  the Schmidt coefficient `K`, the Hayward joint rapidity is `log K` — the same
  `rapidity_eq_entanglementEntropy_of_doppler_eq_schmidt` (`haywardBoost_eq_schmidtRapidity`).

**Honest layering.** Proven: the boost preservation of orthonormality, `sinh η = n·s`, the identity of
`η` with the vibracy/rapidity and its exponential and chain law, and the entanglement-entropy value.
Interpretive: the tensorial content (the normals `n^α, r^α, m^α, s^α`, the null basis `k^α, k̄^α`, the
surface element `√γ d²θ`) is the geometry behind the scalar inner products `n·s`, `n·k`, `s·k`, taken
here as the data; the joints' integrals are represented by their integrated values.

## References

* L. Lehner, R. C. Myers, E. Poisson, R. D. Sorkin, "Gravitational action with null boundaries",
  arXiv:1609.00207 [`Lehner:2016vdi`], §II.D–E, Eqs. (2.81), (2.87), (2.89), (2.91)–(2.98). Hayward's
  joint term: G. Hayward, Phys. Rev. D **47**, 3275 (1993). Reuses
  `Physlib.Relativity.Special.RapidityVibracy` (`vibracy`, `dopplerRatio_eq_exp`,
  `rapidity_eq_entanglementEntropy_of_doppler_eq_schmidt`) and the null-boundary joint arc
  `NullBoundaryGravitationalAction`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HaywardJointRapidity

open Physlib.Relativity.Special.RapidityVibracy


/-- **The boosted timelike-normal squared** `n·n = cosh²η (m·m) + 2 cosh η sinh η (m·s) + sinh²η (s·s)`
for `n = cosh η m + sinh η s` (Eq. 2.81). -/
noncomputable def boostedNn (η mm ms ss : ℝ) : ℝ :=
  (Real.cosh η) ^ 2 * mm + 2 * Real.cosh η * Real.sinh η * ms + (Real.sinh η) ^ 2 * ss

/-- **The boosted cross term** `n·r = cosh η sinh η (m·m) + (cosh²η + sinh²η)(m·s) + sinh η cosh η (s·s)`
for `n = cosh η m + sinh η s`, `r = sinh η m + cosh η s` (Eq. 2.81). -/
noncomputable def boostedNr (η mm ms ss : ℝ) : ℝ :=
  Real.cosh η * Real.sinh η * mm + ((Real.cosh η) ^ 2 + (Real.sinh η) ^ 2) * ms
    + Real.sinh η * Real.cosh η * ss

/-- **The boost preserves the timelike normalization** `n·n = −1` (Eq. 2.81): with `m·m = −1`,
`m·s = 0`, `s·s = +1`, the boosted normal `n` stays a future-directed unit timelike vector, because
`cosh²η − sinh²η = 1`. -/
lemma boostedNormal_timelike (η : ℝ) : boostedNn η (-1) 0 1 = -1 := by
  have h : Real.cosh η ^ 2 - Real.sinh η ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq η
  unfold boostedNn; nlinarith [h]

/-- **The boost preserves orthogonality** `n·r = 0` (Eq. 2.81): the boosted normals `n` and `r` remain
orthogonal, a pure consequence of the boost structure (no identity needed). -/
lemma boostedNormals_orthogonal (η : ℝ) : boostedNr η (-1) 0 1 = 0 := by
  unfold boostedNr; ring


/-- **The Hayward boost parameter** `η = arsinh(n·s)` (Eq. 2.87): the rapidity of the boost relating the
two normal pairs, read off the inner product `n·s`. -/
noncomputable def haywardBoost (nDots : ℝ) : ℝ := Real.arsinh nDots

/-- **`sinh η = n·s`** (Eq. 2.87): the boost parameter's hyperbolic sine is the inner product of the two
unit normals. -/
lemma sinh_haywardBoost (nDots : ℝ) : Real.sinh (haywardBoost nDots) = nDots :=
  Real.sinh_arsinh nDots


/-- **The Hayward joint value in null-projection form** `η = ln A − ln B` (Eq. 2.91), with
`A = −n·k > 0`, `B = −s·k > 0` the projections of the null normal `k^α` onto the two unit normals. -/
noncomputable def haywardJointEta (A B : ℝ) : ℝ := Real.log A - Real.log B

/-- **The Hayward joint parameter is a vibracy** (Eq. 2.91): `η = ln(−n·k) − ln(−s·k) =
vibracy(−n·k, −s·k) = log((−n·k)/(−s·k))`. The gravitational-action joint term is a
`RapidityVibracy.vibracy` — a log-ratio of the two null projections. -/
lemma haywardJointEta_eq_vibracy (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    haywardJointEta A B = vibracy A B := by
  unfold haywardJointEta vibracy
  rw [Real.log_div (ne_of_gt hA) (ne_of_gt hB)]


/-- **The exponentiated joint is the projection ratio** `exp η = (−n·k)/(−s·k)` (Eq. 2.91): the boost
rapidity exponentiates to the ratio of the two null projections. -/
lemma exp_haywardJointEta (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Real.exp (haywardJointEta A B) = A / B := by
  unfold haywardJointEta
  rw [Real.exp_sub, Real.exp_log hA, Real.exp_log hB]

/-- **The Doppler/boost form of the joint** `cosh η + sinh η = (−n·k)/(−s·k)` (Eqs. 2.81 ↔ 2.91): the
boost defining the joint has Doppler ratio equal to the ratio of null projections, uniting the
`n = cosh η m + sinh η s` form with the `η = ln A − ln B` form via `dopplerRatio_eq_exp`. -/
lemma dopplerRatio_haywardJointEta (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Real.cosh (haywardJointEta A B) + Real.sinh (haywardJointEta A B) = A / B := by
  rw [dopplerRatio_eq_exp, exp_haywardJointEta A B hA hB]


/-- **The joint rules compose additively** `η(A,C) = η(A,B) + η(B,C)` (Eqs. 2.95–2.98, the `η_a…η_g`
family): consecutive joints add their boost parameters — the vibracy chain rule. -/
lemma haywardJointEta_chain (A B C : ℝ) :
    haywardJointEta A B + haywardJointEta B C = haywardJointEta A C := by
  unfold haywardJointEta; ring


/-- **The Hayward joint contribution to the boundary action** `+2∮_{ℬ₂} η dS − 2∮_{ℬ₁} η dS`
(Eq. 2.94, the future/past joints of a `𝒮 ∪ 𝒯 ∪ 𝒮` boundary), represented by the integrated joint
values and cross-sectional areas. -/
noncomputable def haywardActionJoints (etaTop etaBot areaTop areaBot : ℝ) : ℝ :=
  2 * etaTop * areaTop - 2 * etaBot * areaBot

/-- **Equal, opposite joints cancel** (Eq. 2.94): a symmetric joint (`η₁ = η₂`, `𝒜₁ = 𝒜₂`) makes no net
contribution to the boundary action — the Hayward analogue of the null-joint cancellation
`NullBoundaryGravitationalAction.stationaryNullAction_eq`. -/
lemma haywardActionJoints_symmetric (eta area : ℝ) :
    haywardActionJoints eta eta area area = 0 := by
  unfold haywardActionJoints; ring


/-- **The Hayward joint value is `log` of the projection ratio** (Eq. 2.91): `η = log(A/B)`. -/
lemma haywardJointEta_eq_log_ratio (A B K : ℝ) (hA : 0 < A) (hB : 0 < B) (hK : A / B = K) :
    haywardJointEta A B = Real.log K := by
  unfold haywardJointEta
  rw [← Real.log_div (ne_of_gt hA) (ne_of_gt hB), hK]

/-- **The Hayward joint rapidity is the special-relativistic rapidity / entanglement entropy**
(full-circle): if the joint's null-projection ratio `A/B` equals the Schmidt/Doppler coefficient `K`
(i.e. `cosh α + sinh α = K`), then the Hayward boost parameter equals the rapidity `α = log K` — the
same `RapidityVibracy.rapidity_eq_entanglementEntropy_of_doppler_eq_schmidt`. The gravitational-action
joint term and the entanglement-entropy rapidity are one boost parameter. -/
lemma haywardBoost_eq_schmidtRapidity (A B α K : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hAB : A / B = K) (hDoppler : Real.cosh α + Real.sinh α = K) :
    haywardJointEta A B = α := by
  rw [haywardJointEta_eq_log_ratio A B K hA hB hAB]
  exact (rapidity_eq_entanglementEntropy_of_doppler_eq_schmidt α K hDoppler).symm

end Physlib.QuantumMechanics.ComplexAction.HaywardJointRapidity

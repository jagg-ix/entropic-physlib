/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Partial bosonization for the two-dimensional Hubbard model

The exact algebraic skeleton of Denz–Mitter–Pawlowski–Wetterich–Yamada,
*Partial bosonization for the two-dimensional Hubbard model*, Phys. Rev. B **101**,
155115 (2020) — extending the configuration-space arc's `SU(2)`/Pauli layer to the
lattice-fermion setting where the four-fermion vertex is decomposed into
antiferromagnetic-boson exchange plus a residual vertex.

## §A — the `SU(2)` Fierz identity (paper Eq. 8)

`pauli_fierz` — `Σⱼ(σʲ)_{αβ}(σʲ)_{γδ} = 2δ_{αδ}δ_{βγ} − δ_{αβ}δ_{γδ}`: **the
algebraic engine of the Hubbard–Stratonovich spin-channel decomposition** — it is
what turns the boson-exchange diagram back into the pointlike four-fermion vertex
(the inversion of the HS transformation, paper Eq. 9), and what reorders the spin
indices between the two exchange processes of Eq. 10.  Proved on the arc's
`pauliVec` carriers — the same three generators as the configuration-space spin
embedding.

## §B — the antiferromagnetic boson and the exchange vertex (Eqs 5, 9, 13)

* `afBosonPropagatorInv` — the AF boson inverse propagator
  `(Ĝ^{(a)})⁻¹(Q) = m² + A·[Q − Π]²` (Eq. 5).
* `afBosonPropagatorInv_min` — for `A > 0` it is minimal **exactly at the ordering
  vector** `Q = Π = (π,π)`, with minimum `m²`: a nonzero `⟨φ(Π)⟩` is
  antiferromagnetic order, and `m² → 0` is its onset.
* `crossedParticleHole_exchange` — **Eq. 13**: the boson-exchange vertex
  `λ^{(a)} = 2Ĝ(P₂−P₃) + Ĝ(P₁−P₂)` (Eq. 9) evaluated on the crossed particle-hole
  configuration `(P, P, −P, −P)` is
  `2/(m² + A[(2pₓ−π)² + (2p_y−π)²]) + 1/(m² + 2π²A)`.
* `exchange_peak_at_nesting` — the exchange vertex is **maximal at the nesting
  momenta** `2P = Π`, i.e. `(pₓ, p_y) = (±π/2, ±π/2)`: the pronounced peaks of the
  paper's Fig. 1, produced by the propagator minimum.

## §C — the Hubbard dispersion and the nesting property (Eqs 20, 21)

* `hubbardDispersion` — `ξ_q = −μ − 2t(cos qₓ + cos q_y)` on the square lattice.
* `nesting_property` — **Eq. 21**: at half filling the band energy satisfies
  `ε_{q+Π} = −ε_q` — the umklapp/nesting symmetry that makes the particle-hole
  channels at transfer `Π` strong and drives antiferromagnetic ordering for any
  `U > 0`; the nesting vector `Π` is the same `(π,π)` at which the AF propagator of
  §B is minimal.
* `halfFilling_umklapp` — the `μ = 0` Fermi surface is the umklapp square
  `cos qₓ + cos q_y = 0`.

## §D — the temperature regulator (Eqs 25–27)

* `matsubara_regulator_identity` — Eq. 25: on the Matsubara frequency
  `ω = 2π(n+½)T`, the regulator `iω(T_k/T − 1)` equals `2πi(n+½)(T_k − T)` —
  temperature itself regulates the fermions.
* `effectiveTemperature` — Eq. 27: `T_k = (T⁴ + (k²/π)⁴)^{1/4}` (the `p = 4`
  scale-dependent effective temperature).
* `effectiveTemperature_at_zero` / `effectiveTemperature_ge` /
  `effectiveTemperature_tendsto_atTop` — the regulator conditions (Eq. 23) hold:
  at `k = 0` the effective temperature is exactly `T` (so `R_{k→0} = 0` and the
  flow ends on the physical theory), `T_k ≥ T` along the flow, and `T_k → ∞` as
  `k → ∞` (so `R_{k→Λ} → ∞` and the UV initial condition is the classical
  action).

## Honest scope

Exact identities on matrix/momentum/scalar carriers.  Recorded, not re-derived: the
FRG flow equation (Wetterich Eq. 22) and its `N`-patching projection, the Matsubara
sums, the numerical fit `(m²_k, A_k, U⁰_k)` of Eq. 15, and the smallness of the
residual vertex `Δλ^{(ψ)}` (the paper's numerical finding).  The channel bookkeeping
(PH/CPH/PP) exists on the SBE side in
`QFT.HamiltonianRenormalisation.SingleBosonExchangeSchwingerDyson`; the smeared
CAR/CCR with a shared kernel — the operator content the bosonization rearranges —
is the configuration-space arc (`smearedField_CAR_kernel`, `smeared_CCR_kernel`).

## References

* T. Denz, M. Mitter, J. M. Pawlowski, C. Wetterich, M. Yamada, Phys. Rev. B
  **101**, 155115 (2020): Eq. 8 (Fierz), Eqs 5/9/13 (AF exchange), Eqs 20–21
  (dispersion, nesting), Eqs 25–27 (regulator).
* Carriers: `AlgebraicQFT.ConfigurationSpaceGaugeGeometry` (`pauliVec`),
  `QFT.HamiltonianRenormalisation.SingleBosonExchangeSchwingerDyson` (channels).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry
open Physlib.QuantumMechanics.SpinDensityFunctionalOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HubbardPartialBosonization

/-! ## §A — the `SU(2)` Fierz identity -/

/-- **The `SU(2)` Fierz identity** (paper Eq. 8):
`Σⱼ(σʲ)_{αβ}(σʲ)_{γδ} = 2δ_{αδ}δ_{βγ} − δ_{αβ}δ_{γδ}` — the spin-index
rearrangement that inverts the Hubbard–Stratonovich transformation: it converts the
antiferromagnetic-boson exchange back into the pointlike four-fermion vertex and
accounts for the reordering between the two exchange processes of Eq. 10. -/
theorem pauli_fierz (α β γ δ : Fin 2) :
    ∑ j : Fin 3, pauliVec j α β * pauliVec j γ δ
      = 2 * (if α = δ then 1 else 0) * (if β = γ then 1 else 0)
        - (if α = β then 1 else 0) * (if γ = δ then 1 else 0) := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;> fin_cases δ <;>
    simp [pauliVec, pauliX, pauliY, pauliZ, Fin.sum_univ_three] <;>
    first
      | rfl
      | norm_num [Complex.I_mul_I, Complex.I_sq, mul_assoc]

/-! ## §B — the antiferromagnetic boson and the exchange vertex -/

/-- **The antiferromagnetic boson inverse propagator** (paper Eq. 5):
`(Ĝ^{(a)})⁻¹(Q) = m² + A·[Q − Π]²`, `Π = (π,π)` the ordering vector. -/
noncomputable def afBosonPropagatorInv (m A : ℝ) (Q : ℝ × ℝ) : ℝ :=
  m ^ 2 + A * ((Q.1 - Real.pi) ^ 2 + (Q.2 - Real.pi) ^ 2)

/-- **The propagator is minimal exactly at the ordering vector**: for `A > 0`,
`(Ĝ^{(a)})⁻¹ ≥ m²` with equality iff `Q = Π` — a nonzero expectation `⟨φ(Π)⟩` is
antiferromagnetic order, and `m² → 0` signals its onset. -/
theorem afBosonPropagatorInv_min (m A : ℝ) (hA : 0 < A) (Q : ℝ × ℝ) :
    m ^ 2 ≤ afBosonPropagatorInv m A Q
      ∧ (afBosonPropagatorInv m A Q = m ^ 2 ↔ Q = (Real.pi, Real.pi)) := by
  constructor
  · unfold afBosonPropagatorInv
    nlinarith [sq_nonneg (Q.1 - Real.pi), sq_nonneg (Q.2 - Real.pi)]
  · constructor
    · intro h
      unfold afBosonPropagatorInv at h
      have hS : A * ((Q.1 - Real.pi) ^ 2 + (Q.2 - Real.pi) ^ 2) = 0 := by linarith
      have hS0 : (Q.1 - Real.pi) ^ 2 + (Q.2 - Real.pi) ^ 2 = 0 :=
        (mul_eq_zero.mp hS).resolve_left (ne_of_gt hA)
      have h1 : Q.1 - Real.pi = 0 := by
        nlinarith [sq_nonneg (Q.1 - Real.pi), sq_nonneg (Q.2 - Real.pi)]
      have h2 : Q.2 - Real.pi = 0 := by
        nlinarith [sq_nonneg (Q.1 - Real.pi), sq_nonneg (Q.2 - Real.pi)]
      exact Prod.ext (by linarith) (by linarith)
    · rintro rfl
      unfold afBosonPropagatorInv
      norm_num

/-- **The crossed particle-hole exchange vertex** (paper Eq. 13): the boson-exchange
contribution `λ^{(a)} = 2Ĝ(P₂−P₃) + Ĝ(P₁−P₂)` (Eq. 9) at the configuration
`(P, P, −P, −P)` — momentum transfers `2P` and `0` — evaluates to
`2/(m² + A[(2pₓ−π)² + (2p_y−π)²]) + 1/(m² + 2π²A)`. -/
theorem crossedParticleHole_exchange (m A px py : ℝ) :
    2 * (afBosonPropagatorInv m A (2 * px, 2 * py))⁻¹
        + (afBosonPropagatorInv m A (0, 0))⁻¹
      = 2 / (m ^ 2 + A * ((2 * px - Real.pi) ^ 2 + (2 * py - Real.pi) ^ 2))
        + 1 / (m ^ 2 + 2 * Real.pi ^ 2 * A) := by
  unfold afBosonPropagatorInv
  rw [div_eq_mul_inv, one_div]
  congr 2
  ring

/-- **The exchange vertex peaks at the nesting momenta** (the `(±π/2, ±π/2)` peaks
of the paper's Fig. 1): the boson-exchange propagator at transfer `2P` is maximal
where `2P = Π`, i.e. at `(pₓ, p_y) = (π/2, π/2)` and its images. -/
theorem exchange_peak_at_nesting (m A px py : ℝ) (hm : 0 < m) (hA : 0 < A) :
    (afBosonPropagatorInv m A (2 * px, 2 * py))⁻¹
      ≤ (afBosonPropagatorInv m A (Real.pi, Real.pi))⁻¹ := by
  have hmin : afBosonPropagatorInv m A (Real.pi, Real.pi) = m ^ 2 := by
    unfold afBosonPropagatorInv
    norm_num
  rw [hmin]
  have hle := (afBosonPropagatorInv_min m A hA (2 * px, 2 * py)).1
  have := one_div_le_one_div_of_le (by positivity : (0:ℝ) < m ^ 2) hle
  simpa [one_div] using this

/-! ## §C — the Hubbard dispersion and the nesting property -/

/-- **The square-lattice Hubbard dispersion** (paper Eq. 20):
`ξ_q = −μ − 2t(cos qₓ + cos q_y)`. -/
noncomputable def hubbardDispersion (t μ : ℝ) (q : ℝ × ℝ) : ℝ :=
  -μ - 2 * t * (Real.cos q.1 + Real.cos q.2)

/-- The band energy `ε_q = ξ_q + μ = −2t(cos qₓ + cos q_y)`. -/
noncomputable def hubbardEnergy (t : ℝ) (q : ℝ × ℝ) : ℝ :=
  -(2 * t) * (Real.cos q.1 + Real.cos q.2)

/-- **The nesting property** (paper Eq. 21): `ε_{q+Π} = −ε_q` — shifting by the
nesting vector `Π = (π,π)` flips the band energy.  This umklapp symmetry of the
half-filled square lattice is what makes the particle-hole channels at transfer `Π`
strong (electron-hole condensation — antiferromagnetic ordering — for any `U > 0`),
and `Π` is exactly the vector at which the §B boson propagator is minimal. -/
theorem nesting_property (t : ℝ) (q : ℝ × ℝ) :
    hubbardEnergy t (q.1 + Real.pi, q.2 + Real.pi) = -hubbardEnergy t q := by
  unfold hubbardEnergy
  rw [Real.cos_add_pi, Real.cos_add_pi]
  ring

/-- **The half-filled Fermi surface is the umklapp square**: at `μ = 0`,
`ξ_q = 0 ↔ cos qₓ + cos q_y = 0`. -/
theorem halfFilling_umklapp (t : ℝ) (ht : t ≠ 0) (q : ℝ × ℝ) :
    hubbardDispersion t 0 q = 0 ↔ Real.cos q.1 + Real.cos q.2 = 0 := by
  unfold hubbardDispersion
  constructor
  · intro h
    have h2 : 2 * t * (Real.cos q.1 + Real.cos q.2) = 0 := by linarith
    have h3 : 2 * t ≠ 0 := mul_ne_zero two_ne_zero ht
    exact (mul_eq_zero.mp h2).resolve_left h3
  · intro h
    rw [h]
    ring

/-! ## §D — the temperature regulator -/

/-- **The temperature-regulator identity** (paper Eq. 25): on the Matsubara
frequency `ω = 2π(n+½)T`, the regulator `ω·(T_k/T − 1)` equals `2π(n+½)(T_k − T)`
— replacing the physical temperature by the scale-dependent effective temperature
regulates the fermions. -/
theorem matsubara_regulator_identity (T Tk : ℝ) (n : ℤ) (hT : T ≠ 0) :
    (2 * Real.pi * ((n : ℝ) + 1 / 2) * T) * (Tk / T - 1)
      = 2 * Real.pi * ((n : ℝ) + 1 / 2) * (Tk - T) := by
  field_simp

/-- **The scale-dependent effective temperature** (paper Eq. 27, `p = 4`):
`T_k = (T⁴ + (k²/π)⁴)^{1/4}`. -/
noncomputable def effectiveTemperature (T k : ℝ) : ℝ :=
  (T ^ 4 + (k ^ 2 / Real.pi) ^ 4) ^ ((1 : ℝ) / 4)

/-- **The flow ends on the physical theory**: `T_{k=0} = T`, so the regulator
vanishes at `k = 0` (the first condition of Eq. 23). -/
theorem effectiveTemperature_at_zero (T : ℝ) (hT : 0 ≤ T) :
    effectiveTemperature T 0 = T := by
  unfold effectiveTemperature
  rw [show T ^ 4 + ((0 : ℝ) ^ 2 / Real.pi) ^ 4 = T ^ 4 by norm_num,
    ← Real.rpow_natCast T 4, ← Real.rpow_mul hT]
  norm_num

/-- **The effective temperature never drops below the physical one**: `T ≤ T_k` —
the coarse-graining only heats. -/
theorem effectiveTemperature_ge (T k : ℝ) (hT : 0 ≤ T) :
    T ≤ effectiveTemperature T k := by
  have h1 : T = (T ^ 4) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast T 4, ← Real.rpow_mul hT]
    norm_num
  conv_lhs => rw [h1]
  unfold effectiveTemperature
  exact Real.rpow_le_rpow (by positivity)
    (le_add_of_nonneg_right (by positivity)) (by norm_num)

/-- **The UV limit suppresses all fluctuations**: `T_k → ∞` as `k → ∞` (the second
regulator condition of Eq. 23) — the flow starts from the classical action. -/
theorem effectiveTemperature_tendsto_atTop (T : ℝ) :
    Filter.Tendsto (effectiveTemperature T) Filter.atTop Filter.atTop := by
  unfold effectiveTemperature
  refine (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp ?_
  refine Filter.tendsto_atTop_add_const_left _ _ ?_
  refine (Filter.tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp ?_
  exact (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const Real.pi_pos

end Physlib.QuantumMechanics.ComplexAction.HubbardPartialBosonization

end

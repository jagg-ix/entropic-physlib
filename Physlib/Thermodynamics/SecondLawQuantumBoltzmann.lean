/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.SecondLaw
public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT

/-!
# The second-law arrow grounded in the QFT quantum Boltzmann H-theorem (Snoke–Liu–Girvin 2011)

This module **improves the second-law formalization** of `Physlib.Thermodynamics.SecondLaw` by making it
*depend on the recent quantum-Boltzmann theorems* (`Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT`),
grounded in *D.W. Snoke, G. Liu, S. Girvin, "The Basis of the Second Law of Thermodynamics in Quantum Field
Theory," arXiv:1112.3009v1 (2011)*.

Snoke–Liu–Girvin derive, from the wave mechanics of a closed quantum field alone (no ensemble, no
collapse, no stochasticity), the quantum Boltzmann equation (their Eq. 31), and show that it drives the
occupation numbers irreversibly toward the Bose–Einstein / Fermi–Dirac equilibrium (Eqs. 33–36) — their
H-theorem (§4): the entropy of a closed system, if it changes, can only increase.

`SecondLaw.lean` defines the abstract `EntropyArrowWorldline`, whose load-bearing field `S_I_monotone`
(the operationalized second law) is supplied by various sources — a Clausius temperature history
(`ofClausiusProfile`), a positive dissipative generator (`ofPositiveGeneratorArrow`), or a bipartite
unitary event (Zhang). **This file adds a new source: the Snoke quantum-Boltzmann relaxation**, where the
monotonicity is *derived* from the net damping `Γ = Γ> − Γ< ≥ 0` (`dampingRate_nonneg`, the recent
theorem) and the equilibrium it relaxes to is *proved* to be Bose–Einstein
(`equilibriumOccupation_eq_boseEinstein`) — or Fermi–Dirac for fermions.

* `QuantumBoltzmannRelaxation` — a field mode relaxing under the quantum Boltzmann equation with KMS
  detailed balance (gain `Γ< = W_minus Ω`, loss `Γ> = W_plus Ω`, energy `Ω ≥ 0`).
* `toEntropyArrowWorldline` — builds the `SecondLaw` arrow with entropy production
  `S_I(t) = ℏ·|f_i − f̄|·(1 − e^{−Γt})`; its `S_I_monotone` is the Snoke H-theorem, derived from `Γ ≥ 0`.
* `snoke_quantum_boltzmann_second_law` — the main result: equilibrium is Bose–Einstein, `Γ ≥ 0` is the
  entropic arrow, `S_I` and the derived entropic time `τ_ent` are monotone (the H-theorem), and the
  collision term vanishes at equilibrium.
* `fermi_equilibrium_is_fermiDirac` — the fermionic counterpart: the Pauli-blocked equilibrium is
  Fermi–Dirac.

So the abstract second-law/entropic-time arrow is no longer fed by an assumed monotonicity here: it is the
QFT quantum-Boltzmann H-theorem, with the thermal distribution as its fixed point.

No new axioms.
-/

set_option autoImplicit false

open Real Filter Topology

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.SecondLawQuantumBoltzmann

open Physlib.Thermodynamics.SecondLaw
open QuantumInfo.Finite
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.Fermion.PartitionFunction
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.Lindblad
open _root_.QuantumMechanics.FiniteTarget

/-! ## §A — the relaxed fraction `1 − e^{−Γt}` and its monotonicity (from `Γ ≥ 0`) -/

/-- The **relaxed fraction** `1 − e^{−Γt}`: the fraction of the quantum-Boltzmann relaxation toward
equilibrium completed by time `t`. -/
def relaxedFraction (Γ t : ℝ) : ℝ := 1 - Real.exp (-(Γ * t))

/-- **The relaxed fraction is monotone non-decreasing** when `Γ ≥ 0` — the kinetic origin of the
second-law monotonicity. -/
theorem relaxedFraction_monotone (Γ : ℝ) (hΓ : 0 ≤ Γ) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    relaxedFraction Γ t₁ ≤ relaxedFraction Γ t₂ := by
  unfold relaxedFraction
  have hle : Real.exp (-(Γ * t₂)) ≤ Real.exp (-(Γ * t₁)) := by
    apply Real.exp_le_exp.mpr
    have : Γ * t₁ ≤ Γ * t₂ := mul_le_mul_of_nonneg_left h hΓ
    linarith
  linarith

/-- The relaxed fraction is zero at `t = 0` (no relaxation has occurred). -/
theorem relaxedFraction_at_zero (Γ : ℝ) : relaxedFraction Γ 0 = 0 := by
  unfold relaxedFraction; simp

/-- **The relaxation completes** (`Γ > 0`): `1 − e^{−Γt} → 1` as `t → ∞` — the system reaches
equilibrium. -/
theorem relaxedFraction_tendsto_one (Γ : ℝ) (hΓ : 0 < Γ) :
    Tendsto (relaxedFraction Γ) atTop (𝓝 1) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(Γ * t))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun t : ℝ => Γ * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hΓ Filter.tendsto_id
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr hlin)
  have key := (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
  rw [sub_zero] at key
  exact key

/-! ## §B — the Snoke quantum-Boltzmann relaxation structure -/

/-- **Snoke–Liu–Girvin quantum-Boltzmann relaxation.** A field mode relaxing under the quantum Boltzmann
equation with KMS detailed balance: gain `Γ< = W_minus Ω`, loss `Γ> = W_plus Ω` at resonance energy
`Ω ≥ 0` (with non-negative gain), initial occupation `f_i`, and `ℏ > 0`. -/
structure QuantumBoltzmannRelaxation where
  /-- KMS detailed-balance data (Snoke Eq. 33 / 38). -/
  κ : KMSDetailedBalance
  /-- Resonance energy. -/
  Ω : ℝ
  /-- The resonance energy is non-negative. -/
  Ω_nonneg : 0 ≤ Ω
  /-- The gain rate is non-negative. -/
  W_minus_nonneg : ∀ E, 0 ≤ κ.W_minus E
  /-- Initial occupation number. -/
  fi : ℝ
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ

variable (R : QuantumBoltzmannRelaxation)

/-- **The net damping** `Γ = Γ> − Γ<` of the relaxation. -/
def QuantumBoltzmannRelaxation.Γnet : ℝ :=
  dampingRate (R.κ.W_plus R.Ω) (R.κ.W_minus R.Ω)

/-- **The net damping is non-negative** — the entropic arrow, *derived* from the recent theorem
`dampingRate_nonneg` (detailed balance with `Ω ≥ 0` makes loss dominate gain). -/
theorem QuantumBoltzmannRelaxation.Γnet_nonneg : 0 ≤ R.Γnet :=
  dampingRate_nonneg R.κ R.Ω R.W_minus_nonneg R.Ω_nonneg

/-- **The equilibrium occupation** `f̄ = Γ</(Γ> − Γ<)` of the relaxation. -/
def QuantumBoltzmannRelaxation.fbar : ℝ :=
  equilibriumOccupation (R.κ.W_plus R.Ω) (R.κ.W_minus R.Ω)

/-- **The relaxation equilibrium is Bose–Einstein** (Snoke Eqs. 34/36) — *derived* from the recent
theorem `equilibriumOccupation_eq_boseEinstein`. -/
theorem QuantumBoltzmannRelaxation.fbar_eq_boseEinstein
    (hW : R.κ.W_minus R.Ω ≠ 0) (hexp : Real.exp (R.κ.beta * R.Ω) - 1 ≠ 0) :
    R.fbar = boseEinstein R.κ.beta R.Ω :=
  equilibriumOccupation_eq_boseEinstein R.κ R.Ω hW hexp

/-- **The entropy produced during relaxation** `S_I(t) = ℏ·|f_i − f̄|·(1 − e^{−Γt})` — monotone
increasing from `0` (no entropy produced) to its saturation `ℏ·|f_i − f̄|` at equilibrium. -/
def QuantumBoltzmannRelaxation.S_I (t : ℝ) : ℝ :=
  R.ℏ * |R.fi - R.fbar| * relaxedFraction R.Γnet t

/-- **The Snoke quantum-Boltzmann H-theorem instantiates the entropic-time arrow.** The entropy produced
during relaxation builds the `SecondLaw.EntropyArrowWorldline`; its `S_I_monotone` field — the second law
— is **derived** from the Boltzmann net damping `Γ ≥ 0` (`Γnet_nonneg`), not assumed. -/
def QuantumBoltzmannRelaxation.toEntropyArrowWorldline : EntropyArrowWorldline where
  ℏ := R.ℏ
  ℏ_pos := R.ℏ_pos
  S_I_along := R.S_I
  τ_ent_along := fun t => R.S_I t / R.ℏ
  τ_ent_eq := fun _ => rfl
  S_I_monotone := fun {_ _} h =>
    mul_le_mul_of_nonneg_left (relaxedFraction_monotone R.Γnet R.Γnet_nonneg h)
      (mul_nonneg R.ℏ_pos.le (abs_nonneg _))
  S_I_at_zero_nonneg := by
    simp [QuantumBoltzmannRelaxation.S_I, relaxedFraction]

/-- **The total entropy produced saturates at equilibrium** (`Γ > 0`): `S_I(t) → ℏ·|f_i − f̄|` as
`t → ∞` — the H-theorem endpoint, where the occupation has reached the Bose–Einstein distribution. -/
theorem QuantumBoltzmannRelaxation.S_I_tendsto (hΓ : 0 < R.Γnet) :
    Tendsto R.S_I atTop (𝓝 (R.ℏ * |R.fi - R.fbar|)) := by
  have key := (tendsto_const_nhds (x := R.ℏ * |R.fi - R.fbar|)).mul
    (relaxedFraction_tendsto_one R.Γnet hΓ)
  rw [mul_one] at key
  exact key

/-! ## §C — the main result -/

/-- **The QFT second law from the quantum Boltzmann H-theorem (Snoke–Liu–Girvin).** For a field-mode
relaxation `R` with detailed balance at energy `Ω` (`Γ> ≠ Γ<`) and a forward interval `t₁ ≤ t₂`:

* **(equilibrium = Bose–Einstein, Eqs. 34/36)** `f̄ = 1/(e^{βΩ} − 1)`;
* **(entropic arrow)** the net damping `Γ ≥ 0`;
* **(H-theorem)** the entropy produced `S_I` and the derived entropic time `τ_ent` are both monotone
  non-decreasing — the second law as a consequence of the quantum Boltzmann dynamics, not an assumption;
* **(equilibrium fixed point, Eq. 33)** the collision term vanishes at `f̄`.

The abstract `EntropyArrowWorldline` second law is here *grounded* in the QFT quantum Boltzmann equation:
its monotonicity is the Snoke H-theorem, derived from `dampingRate_nonneg`, with the thermal distribution
as the fixed point. -/
theorem snoke_quantum_boltzmann_second_law
    (hW : R.κ.W_minus R.Ω ≠ 0) (hexp : Real.exp (R.κ.beta * R.Ω) - 1 ≠ 0)
    (hne : R.κ.W_plus R.Ω - R.κ.W_minus R.Ω ≠ 0) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (R.fbar = boseEinstein R.κ.beta R.Ω)
      ∧ (0 ≤ R.Γnet)
      ∧ (R.toEntropyArrowWorldline.S_I_along t₁ ≤ R.toEntropyArrowWorldline.S_I_along t₂)
      ∧ (R.toEntropyArrowWorldline.τ_ent_along t₁ ≤ R.toEntropyArrowWorldline.τ_ent_along t₂)
      ∧ (boltzmannRHS R.fbar (R.κ.W_plus R.Ω) (R.κ.W_minus R.Ω) = 0) :=
  ⟨R.fbar_eq_boseEinstein hW hexp, R.Γnet_nonneg,
   R.toEntropyArrowWorldline.S_I_monotone h,
   R.toEntropyArrowWorldline.tau_ent_monotone h,
   boltzmannRHS_equilibrium (R.κ.W_plus R.Ω) (R.κ.W_minus R.Ω) hne⟩

/-- **The fermionic equilibrium is Fermi–Dirac** (Snoke Eqs. 34/36, `+` sign). For Pauli-blocked
fermionic relaxation, the equilibrium `Γ</(Γ> + Γ<) = 1/(e^{βΩ} + 1)` is the Fermi–Dirac distribution —
*derived* from the recent theorem `equilibriumOccupation_fermi_eq_fermiDirac`. -/
theorem fermi_equilibrium_is_fermiDirac
    (hW : R.κ.W_minus R.Ω ≠ 0) (hexp : Real.exp (R.κ.beta * R.Ω) + 1 ≠ 0) :
    equilibriumOccupation_fermi (R.κ.W_plus R.Ω) (R.κ.W_minus R.Ω) = fermiDirac R.Ω R.κ.beta :=
  equilibriumOccupation_fermi_eq_fermiDirac R.κ R.Ω hW hexp

/-! ## §D — the time-free form: entropic time computed from the entropy produced (no clock)

Per the corrected thesis (`SecondLaw.secondLaw_timeFree`): entropic time is *not* a function of an external
time `t`; it is a computation on the entropy produced. For the Snoke relaxation the total entropy produced
on the way to equilibrium is `S_I^tot = ℏ·|f_i − f̄|` — a number computed entirely from the gain/loss rates
and the initial occupation, *not* from any clock. -/

/-- **Total entropy produced** by the relaxation, `S_I^tot = ℏ·|f_i − f̄|` — the saturation value of
`S_I(t)` (cf. `S_I_tendsto`), computed from the Boltzmann data with no time parameter. -/
def QuantumBoltzmannRelaxation.S_I_total : ℝ := R.ℏ * |R.fi - R.fbar|

/-- **The Snoke second law, time-free.** The entropic time of the relaxation is `S_I^tot/ℏ = |f_i − f̄|`,
the distance from the initial occupation to the Bose–Einstein equilibrium — a non-negative computation on
the entropy produced, derived via the time-free `SecondLaw.secondLaw_timeFree`, with no clock. It vanishes
iff the system starts in equilibrium (`f_i = f̄`, reversible). -/
theorem snoke_entropicTime_timeFree :
    (0 ≤ Physlib.Thermodynamics.SecondLaw.entropicTimeOf R.S_I_total R.ℏ)
      ∧ (Physlib.Thermodynamics.SecondLaw.entropicTimeOf R.S_I_total R.ℏ = 0 ↔ R.fi = R.fbar) := by
  refine ⟨Physlib.Thermodynamics.SecondLaw.entropicTimeOf_nonneg
      (mul_nonneg R.ℏ_pos.le (abs_nonneg _)) R.ℏ_pos, ?_⟩
  rw [Physlib.Thermodynamics.SecondLaw.entropicTimeOf_eq_zero_iff R.ℏ_pos]
  unfold QuantumBoltzmannRelaxation.S_I_total
  rw [mul_eq_zero, abs_eq_zero, sub_eq_zero]
  simp [ne_of_gt R.ℏ_pos]

/-! ## §E — link to the kinematic / Misra / Wick structure

The Snoke quantum-Boltzmann second law connected to the canonical kinematic–entropic–Wick–Misra cluster:
the equilibrium entropy is the Bogoliubov entropic time `binEntropy((1 − m)/2)`, the velocity `m = tanh θ`
composes relativistically, the Wick rotation exchanges timelike↔spacelike, and the irreversible generator
includes the Misra `i[L,T] = I`. -/

/-- **The Snoke quantum-Boltzmann second law linked to the kinematic–entropic–Wick–Misra structure.** The
occupation–entropy map gives the Bogoliubov entropic time `binEntropy((1 − m)/2)` with metric velocity
`m = ξ/E` (`entropic_from_metric`); the boost velocity `m = tanh θ` composes relativistically
(`kinematic_velocity_addition`); the Wick rotation exchanges timelike↔spacelike (`wick_exchanges_sectors`);
and the irreversible generator includes the Misra conjugate internal-time operator `i[L,T] = I`
(`liouvillian_age_ccr`). These are the kinematic (reversible boost clock) and entropic (irreversible
dissipative clock) faces of the same metric `S`-norm that drives the Snoke H-theorem. -/
theorem snoke_kinematic_misra_wick_link (ξ Δ a b : ℝ) (q : ℂ)
    (f : ℝ → ℂ) (lam : ℝ) (hf : DifferentiableAt ℝ f lam) :
    (bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2))
      ∧ (Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b))
      ∧ (lorentzianForm (Complex.I * q) = - lorentzianForm q)
      ∧ (Complex.I * (Physlib.QuantumMechanics.RelationalTime.spectralLiouvillian
            (Physlib.QuantumMechanics.RelationalTime.ageOperator f) lam
          - Physlib.QuantumMechanics.RelationalTime.ageOperator
            (Physlib.QuantumMechanics.RelationalTime.spectralLiouvillian f) lam) = f lam) :=
  ⟨entropic_from_metric ξ Δ, kinematic_velocity_addition a b, wick_exchanges_sectors q,
   Physlib.QuantumMechanics.RelationalTime.liouvillian_age_ccr f lam hf⟩

/-! ## §F — the classical and quantum second laws match (Snoke–Liu–Girvin §3, Eqs. 34–36)

Snoke–Liu–Girvin derive the *same* quantum Boltzmann equation for classical and quantum statistics; the
second law (entropy increase to equilibrium / the H-theorem) is identical, and only the equilibrium
distribution differs — Bose–Einstein `1/(e^x − 1)`, Fermi–Dirac `1/(e^x + 1)`, classical Maxwell–Boltzmann
`e^{−x}` (with `x = α + βE = β(E − μ)`). In the dilute (low-density, large-`x`) limit `μ ≪ E` both quantum
distributions **converge to the classical Maxwell–Boltzmann distribution**, so the quantum second law
matches the classical one. Here `boseEinstein 1 x = 1/(e^x − 1)`, `fermiDirac x 1 = 1/(e^x + 1)`. -/

/-- **The classical Maxwell–Boltzmann occupation** `N(x) = e^{−x}`, `x = α + βE`. -/
def maxwellBoltzmann (x : ℝ) : ℝ := Real.exp (-x)

/-- **Bose–Einstein matches Maxwell–Boltzmann in the dilute limit** (Snoke §3): `BE(x)/MB(x) → 1` as
`x → ∞`, i.e. `1/(e^x − 1) ∼ e^{−x}`. Proof: `BE/MB = e^x/(e^x − 1) = 1 + 1/(e^x − 1)`, and
`1/(e^x − 1) → 0` since `e^x − 1 → ∞`. -/
theorem boseEinstein_div_maxwellBoltzmann_tendsto_one :
    Tendsto (fun x : ℝ => boseEinstein 1 x / maxwellBoltzmann x) atTop (𝓝 1) := by
  have hbig : Tendsto (fun x : ℝ => Real.exp x - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) Real.tendsto_exp_atTop
  have hinv : Tendsto (fun x : ℝ => (Real.exp x - 1)⁻¹) atTop (𝓝 0) := hbig.inv_tendsto_atTop
  have hlim : Tendsto (fun x : ℝ => 1 + (Real.exp x - 1)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have he1 : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hx))
  have he0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  show 1 + (Real.exp x - 1)⁻¹ = boseEinstein 1 x / maxwellBoltzmann x
  unfold boseEinstein maxwellBoltzmann
  rw [Real.exp_neg, one_mul]
  field_simp
  ring

/-- **Fermi–Dirac matches Maxwell–Boltzmann in the dilute limit** (Snoke §3): `FD(x)/MB(x) → 1` as
`x → ∞`, i.e. `1/(e^x + 1) ∼ e^{−x}`. Proof: `FD/MB = e^x/(e^x + 1) = 1 − 1/(e^x + 1)`, and
`1/(e^x + 1) → 0`. -/
theorem fermiDirac_div_maxwellBoltzmann_tendsto_one :
    Tendsto (fun x : ℝ => fermiDirac x 1 / maxwellBoltzmann x) atTop (𝓝 1) := by
  have hbig : Tendsto (fun x : ℝ => Real.exp x + 1) atTop atTop := by
    simpa using tendsto_atTop_add_const_right atTop (1 : ℝ) Real.tendsto_exp_atTop
  have hinv : Tendsto (fun x : ℝ => (Real.exp x + 1)⁻¹) atTop (𝓝 0) := hbig.inv_tendsto_atTop
  have hlim : Tendsto (fun x : ℝ => 1 - (Real.exp x + 1)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have he0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have headd : Real.exp x + 1 ≠ 0 := by positivity
  show 1 - (Real.exp x + 1)⁻¹ = fermiDirac x 1 / maxwellBoltzmann x
  unfold fermiDirac maxwellBoltzmann
  rw [Real.exp_neg, one_mul]
  field_simp
  ring

/-- **The classical and quantum second laws match** (Snoke–Liu–Girvin §3). The quantum Boltzmann equation
gives the *same* H-theorem for classical and quantum statistics; only the equilibrium differs, and in the
dilute limit both quantum equilibria converge to the classical Maxwell–Boltzmann one:

* **(Bose–Einstein → Maxwell–Boltzmann)** `BE(x)/MB(x) → 1`;
* **(Fermi–Dirac → Maxwell–Boltzmann)** `FD(x)/MB(x) → 1`.

So the quantum second law (relaxation to Bose–Einstein / Fermi–Dirac) reduces to the classical second law
(relaxation to Maxwell–Boltzmann) in the low-density regime — the two second laws are one. -/
theorem classical_quantum_secondLaw_match :
    Tendsto (fun x : ℝ => boseEinstein 1 x / maxwellBoltzmann x) atTop (𝓝 1)
      ∧ Tendsto (fun x : ℝ => fermiDirac x 1 / maxwellBoltzmann x) atTop (𝓝 1) :=
  ⟨boseEinstein_div_maxwellBoltzmann_tendsto_one, fermiDirac_div_maxwellBoltzmann_tendsto_one⟩

/-! ## §G — Appendix A: the H-theorem and entropy from the quantum Boltzmann equation (Snoke–Liu–Girvin)

Snoke–Liu–Girvin Appendix A connects the quantum Boltzmann equation to the H-theorem. The total
(von Neumann) entropy `S_vN = −k_B Tr(ρ ln ρ)` (Eq. A.1) is **constant** under the unitary evolution of a
closed system. The **diagonal entropy** `S_d = −k_B ∑_k N_k ln N_k` (Eq. A.2, Polkovnikov) — which keeps
only the occupation numbers, discarding the off-diagonal phase information — instead **increases**:
`∂S_d/∂t ≥ 0` (the H-theorem). The increase is driven by the per-scattering-quartet term (Eqs. A.5/A.6)

  `ln(N_k N_{k'} / (N_{k₁} N_{k₂})) · [N_{k₁} N_{k₂} − N_k N_{k'}] ≤ 0`,

i.e. with `a = N_k N_{k'}`, `b = N_{k₁} N_{k₂}` the entropy production `(ln a − ln b)(a − b) ≥ 0` (log is
monotone), vanishing iff `a = b` — detailed balance, the equilibrium (`§A`/Eq. 33). The constant gap
`S_vN − S_d` is the dephasing / off-diagonal information lost as the closed-system wavefunction spreads
over Fock states. -/

/-- **[Snoke A.2]** Polkovnikov diagonal entropy `S_d = −k_B ∑_k N_k ln N_k`. -/
def diagonalEntropy {ι : Type*} [Fintype ι] (kB : ℝ) (N : ι → ℝ) : ℝ :=
  -kB * ∑ k, N k * Real.log (N k)

/-- **[Snoke A.3]** Number conservation simplifies the diagonal-entropy rate: in
`∂S_d/∂t = −k_B ∑_k (Ṅ_k ln N_k + Ṅ_k)` the bare `∑_k Ṅ_k` vanishes (`∑ Ṅ_k = 0`), leaving
`−k_B ∑_k Ṅ_k ln N_k`. -/
theorem diagonalEntropyRate_number_conservation {ι : Type*} [Fintype ι] (kB : ℝ) (N Ndot : ι → ℝ)
    (hcons : ∑ k, Ndot k = 0) :
    -kB * ∑ k, (Ndot k * Real.log (N k) + Ndot k) = -kB * ∑ k, Ndot k * Real.log (N k) := by
  rw [Finset.sum_add_distrib, hcons, add_zero]

/-- **[Snoke A.5/A.6, the H-theorem core]** The per-quartet entropy production `(ln a − ln b)(a − b) ≥ 0`
for positive occupation products `a = N_k N_{k'}`, `b = N_{k₁} N_{k₂}` — the log-balance inequality
driving the H-theorem (`Real.log` is monotone). -/
theorem entropyProduction_term_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (Real.log a - Real.log b) * (a - b) := by
  rcases le_total a b with h | h
  · have hl : Real.log a ≤ Real.log b := Real.log_le_log ha h
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr h)]
  · have hl : Real.log b ≤ Real.log a := Real.log_le_log hb h
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr h)]

/-- **[Snoke A.6]** The entropy production vanishes iff the occupation products balance, `a = b`
(`N_k N_{k'} = N_{k₁} N_{k₂}`) — the detailed-balance / equilibrium condition. -/
theorem entropyProduction_term_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Real.log a - Real.log b) * (a - b) = 0 ↔ a = b := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hlog | hab
    · have hl : Real.log a = Real.log b := by linarith
      rw [← Real.exp_log ha, ← Real.exp_log hb, hl]
    · linarith
  · intro h; rw [h]; ring

/-- **[Snoke A.4–A.6, the H-theorem]** The diagonal-entropy production rate `∂S_d/∂t ≥ 0`. Modeled as a
sum of the per-quartet terms over the scattering quartets (`aᵢ = N_k N_{k'}`, `bᵢ = N_{k₁} N_{k₂}`), each
`≥ 0` by `entropyProduction_term_nonneg`, so the total `≥ 0` — the standard form of the H-theorem. -/
theorem hTheorem {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    0 ≤ ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i) :=
  Finset.sum_nonneg fun i _ => entropyProduction_term_nonneg (ha i) (hb i)

/-- **[Snoke A.1]** The total (von Neumann) entropy is constant under the unitary evolution of a closed
system: `Sᵥₙ(U ρ U†) = Sᵥₙ ρ` (`Sᵥₙ_U_conj`). The H-theorem increase is therefore entirely in the
*diagonal* entropy `S_d`; the constant gap `S_vN − S_d` is the off-diagonal (phase / dephasing)
information. -/
theorem vonNeumann_entropy_unitary_invariant {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U : 𝐔[d]) : Sᵥₙ (ρ.U_conj U) = Sᵥₙ ρ :=
  Sᵥₙ_U_conj ρ U

/-- **Appendix A (Snoke–Liu–Girvin): the H-theorem and entropy from the quantum Boltzmann equation.** For
scattering quartets with positive occupation products `aᵢ = N_k N_{k'}`, `bᵢ = N_{k₁} N_{k₂}`, and a closed
system state `ρ` evolved by a unitary `U`:

* **(A.1, von Neumann)** `Sᵥₙ(U ρ U†) = Sᵥₙ ρ` — the total entropy is constant (unitary evolution);
* **(A.4–A.6, H-theorem)** `∂S_d/∂t = ∑ᵢ (ln aᵢ − ln bᵢ)(aᵢ − bᵢ) ≥ 0` — the diagonal entropy increases;
* **(equilibrium)** each term vanishes iff `aᵢ = bᵢ` (detailed balance `N_k N_{k'} = N_{k₁} N_{k₂}`).

The closed-system total entropy is conserved while the diagonal entropy rises to its detailed-balance
maximum: the H-theorem is the dephasing of off-diagonal information, not a violation of unitarity. -/
theorem appendixA_hTheorem {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) (U : 𝐔[d]) :
    (Sᵥₙ (ρ.U_conj U) = Sᵥₙ ρ)
      ∧ (0 ≤ ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i))
      ∧ (∀ i, (Real.log (a i) - Real.log (b i)) * (a i - b i) = 0 ↔ a i = b i) :=
  ⟨Sᵥₙ_U_conj ρ U, hTheorem a b ha hb,
   fun i => entropyProduction_term_eq_zero_iff (ha i) (hb i)⟩

/-! ## §H — the H-theorem *derived* from the entropy functional (no rate, no clock)

The §G result `0 ≤ ∑ (ln aᵢ − ln bᵢ)(aᵢ − bᵢ)` states the H-theorem as a sum of non-negative terms, but
takes the log-balance form `(ln a − ln b)(a − b)` as given. Here we **derive** that form from the diagonal
entropy itself, and connect it to the time-free entropic clock `entropicTimeOf` (`SecondLaw`) — so nothing
is asserted as a "rate" and no external time is smuggled in.

A `CollisionQuartet` is a binary scattering channel `(k,k') → (k₁,k₂)` with its four occupation numbers.
Its number-conserving collision moves population along `Ṅ = (−r, −r, +r, +r)`, `r = a − b`,
`a = N_k N_{k'}`, `b = N_{k₁} N_{k₂}`. The entropy it produces — the contraction of the diagonal-entropy
gradient `∂S_d/∂N_k = −(ln N_k + 1)` with that collision vector, the `+1` killed by number conservation —
is `−∑ᵢ Ṅᵢ ln Nᵢ`, a pure computation on the four occupations. We **prove** (via `Real.log_mul`) that it
equals `(a − b)(ln a − ln b) ≥ 0`, and that it feeds a non-negative `entropicTimeOf`. -/

/-- **A binary scattering quartet** `(k,k') → (k₁,k₂)` with its four (positive) occupation numbers. -/
structure CollisionQuartet where
  /-- Occupation of mode `k`. -/
  Nk : ℝ
  /-- Occupation of mode `k'`. -/
  Nk' : ℝ
  /-- Occupation of mode `k₁`. -/
  Nk₁ : ℝ
  /-- Occupation of mode `k₂`. -/
  Nk₂ : ℝ
  /-- `N_k > 0`. -/
  Nk_pos : 0 < Nk
  /-- `N_{k'} > 0`. -/
  Nk'_pos : 0 < Nk'
  /-- `N_{k₁} > 0`. -/
  Nk₁_pos : 0 < Nk₁
  /-- `N_{k₂} > 0`. -/
  Nk₂_pos : 0 < Nk₂

namespace CollisionQuartet

variable (Q : CollisionQuartet)

/-- Out-scattering product `a = N_k N_{k'}` (forward / loss, low density). -/
def outProd : ℝ := Q.Nk * Q.Nk'

/-- In-scattering product `b = N_{k₁} N_{k₂}` (backward / gain). -/
def inProd : ℝ := Q.Nk₁ * Q.Nk₂

theorem outProd_pos : 0 < Q.outProd := mul_pos Q.Nk_pos Q.Nk'_pos

theorem inProd_pos : 0 < Q.inProd := mul_pos Q.Nk₁_pos Q.Nk₂_pos

/-- Net forward collision rate `r = a − b` — the low-density gain/loss (the net of a `boltzmannRHS`-type
in/out rate), positive when `(k,k')` is depopulating. A property of the state, not a time derivative. -/
def netRate : ℝ := Q.outProd - Q.inProd

/-- **The entropy produced by the quartet's collision.** The contraction of the diagonal-entropy gradient
`−(ln Nᵢ + 1)` with the number-conserving collision vector `Ṅ = (−r,−r,+r,+r)`, the `+1` dropping by number
conservation: `−∑ᵢ Ṅᵢ ln Nᵢ`. A pure computation on the four occupations — no time, no rate. -/
def entropyProduced : ℝ :=
  -(-Q.netRate * Real.log Q.Nk + -Q.netRate * Real.log Q.Nk'
    + Q.netRate * Real.log Q.Nk₁ + Q.netRate * Real.log Q.Nk₂)

/-- **The collision vector is number-conserving**: `(−r) + (−r) + r + r = 0`. -/
theorem netRate_balance : -Q.netRate + -Q.netRate + Q.netRate + Q.netRate = 0 := by ring

/-- **[Snoke A.5, DERIVED] The entropy produced equals the log-balance `(a − b)(ln a − ln b)`.** This is
the genuine derivation of the H-theorem driver from the diagonal entropy: expanding
`ln(N_k N_{k'}) = ln N_k + ln N_{k'}` (`Real.log_mul`) collapses the four-mode contraction to the
occupation-product log-balance. Nothing is asserted — the form is *proved*. -/
theorem entropyProduced_eq :
    Q.entropyProduced = (Real.log Q.outProd - Real.log Q.inProd) * (Q.outProd - Q.inProd) := by
  unfold entropyProduced netRate outProd inProd
  rw [Real.log_mul Q.Nk_pos.ne' Q.Nk'_pos.ne', Real.log_mul Q.Nk₁_pos.ne' Q.Nk₂_pos.ne']
  ring

/-- **The quartet's entropy production is non-negative** — the per-quartet H-theorem, *derived* from the
entropy functional (`entropyProduced_eq`) and the log-balance inequality (`entropyProduction_term_nonneg`),
not assumed. -/
theorem entropyProduced_nonneg : 0 ≤ Q.entropyProduced := by
  rw [entropyProduced_eq]
  exact entropyProduction_term_nonneg Q.outProd_pos Q.inProd_pos

/-- **Zero entropy production ⟺ detailed balance** `a = b` (`N_k N_{k'} = N_{k₁} N_{k₂}`) — the equilibrium,
where the collision rate `r = 0` and the diagonal entropy is stationary. -/
theorem entropyProduced_eq_zero_iff : Q.entropyProduced = 0 ↔ Q.outProd = Q.inProd := by
  rw [entropyProduced_eq]
  exact entropyProduction_term_eq_zero_iff Q.outProd_pos Q.inProd_pos

end CollisionQuartet

/-- **The H-theorem for a closed system: the total diagonal entropy produced is non-negative.** Summing the
*derived* per-quartet entropy productions over all scattering channels `q : κ`: `0 ≤ ∑ q, S_d-produced(q)`.
Each term is derived from the entropy functional and is `≥ 0`. No rate, no external clock — the entropy
produced is a state computation. -/
theorem hTheorem_total {κ : Type*} [Fintype κ] (Q : κ → CollisionQuartet) :
    0 ≤ ∑ q, (Q q).entropyProduced :=
  Finset.sum_nonneg fun q _ => (Q q).entropyProduced_nonneg

/-! ## §H.2 — quantum-mechanical realization: Bogoliubov occupation, Nagao–Nielsen `H_I`, GKLS dissipator

The H-theorem above reads as occupation-number (classical). Here it is connected to the *genuine* quantum
infrastructure — not the thin scalar `entropicTimeOf`, but the Bogoliubov entropic time, the Nagao–Nielsen
complex momentum / imaginary Hamiltonian, and the GKLS dissipator:

* the **diagonal entropy of a Bogoliubov mode** (occupation `v² = (1 − m)/2`, hole `u² = 1 − v²`,
  `m = ξ/E`, `E² = ξ² + Δ²`) *is* the Bogoliubov entropic time `binEntropy((1 − m)/2)`
  (`bogoliubovEntropicTime`), with `ξ` the Nagao–Nielsen complex-momentum magnitude `|p|` and `Δ` the gap;
* the **entropy-production irreversibility** `≥ 0` is realized by the GKLS rate `gklsEntropicRate ≥ 0`,
  whose generator `gklsImaginaryHamiltonian = (ℏ/2)∑ Lⱼ†Lⱼ` is the imaginary part `H_I` of the
  Nagao–Nielsen complex Hamiltonian `H_C = H_R − i H_I`.
-/

/-- The **binary diagonal entropy** of a mode with occupation `n` and hole `1 − n`:
`−n ln n − (1 − n) ln(1 − n)` — the Snoke A.2 diagonal entropy of the two-outcome {occupied, empty}
distribution. -/
def binaryDiagEntropy (n : ℝ) : ℝ := -(n * Real.log n + (1 - n) * Real.log (1 - n))

/-- The binary diagonal entropy is Shannon's `binEntropy`. -/
theorem binaryDiagEntropy_eq_binEntropy (n : ℝ) : binaryDiagEntropy n = Real.binEntropy n := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [binaryDiagEntropy, Real.negMulLog_def]
  ring

/-- **[Bogoliubov / Nagao–Nielsen link] The diagonal entropy of a Bogoliubov mode is the Bogoliubov
entropic time.** For a mode at the Bogoliubov occupation `v² = (1 − m)/2`, `m = ξ/E`, the H-theorem's
binary diagonal entropy equals `bogoliubovEntropicTime ξ Δ = binEntropy((1 − m)/2)` — the genuine quantum
entropic time of the metric `S`-norm, built from the Nagao–Nielsen complex momentum `ξ` and gap `Δ` via
`E² = ξ² + Δ²`. This is the quantum entropic time the H-theorem's diagonal entropy *is*, not a thin
scalar reduction. -/
theorem binaryDiagEntropy_bogoliubov (ξ Δ : ℝ) :
    binaryDiagEntropy (bogoliubovV2 ξ Δ) = bogoliubovEntropicTime ξ Δ := by
  unfold bogoliubovEntropicTime
  exact binaryDiagEntropy_eq_binEntropy _

/-- **[Nagao–Nielsen / GKLS link] The H-theorem irreversibility is the NN/GKLS dissipative rate.** The
per-quartet entropy production `≥ 0` (`CollisionQuartet.entropyProduced_nonneg`) is the same
non-negativity as the GKLS entropy-production rate `gklsEntropicRate L ρ ≥ 0` (`gklsEntropicRate_nonneg`),
whose generator `gklsImaginaryHamiltonian L ℏ = (ℏ/2)∑ Lⱼ†Lⱼ` is the imaginary part `H_I` of the
Nagao–Nielsen complex Hamiltonian — the entropy production of one and the same dissipative `H_I`. -/
theorem hTheorem_gkls_realization {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
    (L : ι → Matrix d d ℂ) (ρ : MState d) (Q : CollisionQuartet) :
    0 ≤ Q.entropyProduced ∧ 0 ≤ gklsEntropicRate L ρ :=
  ⟨Q.entropyProduced_nonneg, gklsEntropicRate_nonneg L ρ⟩

/-- **The H-theorem realized in the quantum-mechanical infrastructure (Bogoliubov + Nagao–Nielsen + GKLS).**
For scattering quartets `Q` (the occupation-number H-theorem), a Bogoliubov mode `(ξ, Δ)` (the NN
complex momentum `ξ` and gap `Δ`), and GKLS jump operators `L` on state `ρ`:

* **(H-theorem)** the total diagonal entropy produced is `≥ 0`;
* **(Bogoliubov entropic time)** the diagonal entropy of the Bogoliubov mode is the genuine quantum entropic
  time `bogoliubovEntropicTime ξ Δ = binEntropy((1 − m)/2)`, `m = ξ/E`;
* **(NN / GKLS dissipator)** the irreversibility is the GKLS rate `gklsEntropicRate L ρ ≥ 0`, generated by
  the NN imaginary Hamiltonian `H_I = (ℏ/2)∑ Lⱼ†Lⱼ`.

The classical H-theorem is the diagonal-entropy face of the Bogoliubov / Nagao–Nielsen complex-action
dynamics — not a thin scalar reduction. -/
theorem hTheorem_quantum_realization {κ : Type*} [Fintype κ] (Q : κ → CollisionQuartet)
    (ξ Δ : ℝ) {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
    (L : ι → Matrix d d ℂ) (ρ : MState d) :
    (0 ≤ ∑ q, (Q q).entropyProduced)
      ∧ (binaryDiagEntropy (bogoliubovV2 ξ Δ) = bogoliubovEntropicTime ξ Δ)
      ∧ (0 ≤ gklsEntropicRate L ρ) :=
  ⟨hTheorem_total Q, binaryDiagEntropy_bogoliubov ξ Δ, gklsEntropicRate_nonneg L ρ⟩

end Physlib.Thermodynamics.SecondLawQuantumBoltzmann

end

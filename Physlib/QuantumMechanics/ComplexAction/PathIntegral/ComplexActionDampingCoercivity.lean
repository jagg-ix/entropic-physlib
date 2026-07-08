/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.Wick.Consistency
public import Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations
public import Physlib.QuantumMechanics.Liouville.Schrodinger
public import QuantumInfo.Entropy.Relative

/-!
# complex-action/entropic-time: weight factorization, coercivity & the absolute damping bound (Paper 2+4+5)

Formalizes the foundational damping/coercivity terms of the complex-action/entropic-time (Complex Action — Entropic Proper Time)
framework (*Paper 2+4+5, APS/PRL v3.5.12*, Eqs 1–2, 4, 8–9), completing the existing `complexActionWeight`
(`Physlib.QFT.Wick.Consistency`).

With the complex action `S = S_R + i·S_I`, `S_I ≥ 0` (Eq 1) and the path-integral weight
`w = exp(iS/ℏ) = complexActionWeight S_R S_I ℏ`:

* **Eq 4 — weight factorization**: `w = exp(iS_R/ℏ)·exp(−S_I/ℏ)` (`complexActionWeight_factorization`) — an
  oscillatory phase times a real damping factor;
* **Eq 8 — UV coercivity**: `S_I ≥ C‖Φ‖²` (`IsCoercive`, `C > 0`);
* **Eq 9 — the absolute damping bound**: `‖w‖ = exp(−S_I/ℏ) ≤ exp(−C‖Φ‖²/ℏ)` (`damping_bound`) — the
  coercive imaginary action gives a Gaussian UV cutoff on the path integral; the damping is monotone in `S_I`
  (`damping_monotone`);
* **Eq 2 — entropic proper time**: `τ_ent = S_I/ℏ = −log‖w‖` (`entropicProperTime`,
  `entropicProperTime_eq_neg_log_norm`), non-negative and monotone (`entropicProperTime_nonneg`,
  `entropicProperTime_monotone`), vanishing in the reversible limit `S_I = 0`
  (`entropicProperTime_reversible`).

* **§A — the weight factorization** (`complexActionWeight_factorization`).
* **§B — coercivity & the damping bound** (`IsCoercive`, `damping_bound`, `damping_monotone`).
* **§C — the entropic proper time** (`entropicProperTime`, `entropicProperTime_eq_neg_log_norm`,
  `entropicProperTime_nonneg`, `entropicProperTime_monotone`, `entropicProperTime_reversible`).

## References

* complex-action/entropic-time Paper 2+4+5, APS/PRL v3.5.12 (the complex action Eq 1, entropic proper time Eq 2, weight
  factorization Eq 4, UV coercivity Eq 8, absolute damping bound Eq 9).
* Repo structure: `Physlib.QFT.Wick.Consistency` (`complexActionWeight`, `norm_complexActionWeight`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity

open Physlib.QFT.Wick.Consistency

/-! ## §A — the weight factorization (Eq 4) -/

/-- **[Eq 4] `w = exp(iS_R/ℏ)·exp(−S_I/ℏ)`** — the complex-action path-integral weight factors into an
oscillatory phase `exp(iS_R/ℏ)` times a real entropic damping factor `exp(−S_I/ℏ)`. -/
theorem complexActionWeight_factorization (S_R S_I hbar : ℝ) :
    complexActionWeight S_R S_I hbar
      = Complex.exp (((S_R / hbar : ℝ) : ℂ) * Complex.I) * Complex.exp ((-(S_I / hbar) : ℝ) : ℂ) := by
  rw [complexActionWeight, ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ## §B — coercivity and the absolute damping bound (Eqs 8–9) -/

/-- **[Eq 8, UV coercivity] `S_I ≥ C‖Φ‖²`** — the imaginary (entropic) action dominates the UV norm, with
coercivity constant `C > 0`. -/
def IsCoercive (S_I C normPhiSq : ℝ) : Prop := C * normPhiSq ≤ S_I

/-- **[Eq 9, the absolute damping bound] `‖w‖ ≤ exp(−C‖Φ‖²/ℏ)`.** Under coercivity (`S_I ≥ C‖Φ‖²`, `ℏ > 0`) the
modulus of the weight is bounded by a Gaussian in the UV norm — the coercive imaginary action gives a
UV cutoff that makes the complex-action path integral finite. -/
theorem damping_bound (S_R S_I C normPhiSq hbar : ℝ)
    (hcoer : IsCoercive S_I C normPhiSq) (hℏ : 0 < hbar) :
    ‖complexActionWeight S_R S_I hbar‖ ≤ Real.exp (-(C * normPhiSq / hbar)) := by
  rw [norm_complexActionWeight]; unfold IsCoercive at hcoer; gcongr

/-- **[Damping is monotone in the entropic action] more `S_I` ⟹ stronger damping.** `S_I₁ ≤ S_I₂` (and `ℏ > 0`)
gives `‖w(S_I₂)‖ ≤ ‖w(S_I₁)‖` — a path producing more entropy is more strongly suppressed in the path
integral. -/
theorem damping_monotone (S_R S_R' S_I₁ S_I₂ hbar : ℝ) (h : S_I₁ ≤ S_I₂) (hℏ : 0 < hbar) :
    ‖complexActionWeight S_R' S_I₂ hbar‖ ≤ ‖complexActionWeight S_R S_I₁ hbar‖ := by
  rw [norm_complexActionWeight, norm_complexActionWeight]; gcongr

/-! ## §C — the entropic proper time (Eq 2) -/

/-- **[Eq 2] The entropic proper time** `τ_ent = S_I/ℏ` — the imaginary action in units of `ℏ`, counting the
entropic bits transferred to the environment. -/
noncomputable def entropicProperTime (S_I hbar : ℝ) : ℝ := S_I / hbar

/-- **[Eq 2, `τ_ent = −log‖w‖`] the entropic proper time is `−log` of the weight modulus** — since
`‖w‖ = exp(−S_I/ℏ)`, the entropic time `S_I/ℏ` is `−log‖w‖`, the "number of damping bits". -/
theorem entropicProperTime_eq_neg_log_norm (S_R S_I hbar : ℝ) :
    entropicProperTime S_I hbar = -Real.log ‖complexActionWeight S_R S_I hbar‖ := by
  rw [entropicProperTime, norm_complexActionWeight, Real.log_exp, neg_neg]

/-- **The entropic proper time is non-negative** `τ_ent ≥ 0` (since `S_I ≥ 0`, `ℏ > 0`) — entropic time only
advances. -/
theorem entropicProperTime_nonneg (S_I hbar : ℝ) (hS : 0 ≤ S_I) (hℏ : 0 < hbar) :
    0 ≤ entropicProperTime S_I hbar := by
  rw [entropicProperTime]; positivity

/-- **The entropic proper time is monotone** `S_I₁ ≤ S_I₂ ⟹ τ_ent₁ ≤ τ_ent₂` (for `ℏ > 0`) — more entropy
produced, more entropic time elapsed. -/
theorem entropicProperTime_monotone (S_I₁ S_I₂ hbar : ℝ) (h : S_I₁ ≤ S_I₂) (hℏ : 0 < hbar) :
    entropicProperTime S_I₁ hbar ≤ entropicProperTime S_I₂ hbar := by
  rw [entropicProperTime, entropicProperTime]; gcongr

/-- **[Reversible limit] `τ_ent = 0` at `S_I = 0`** — no imaginary action, no entropic time: the unitary,
reversible case (`‖w‖ = 1`). -/
theorem entropicProperTime_reversible (hbar : ℝ) : entropicProperTime 0 hbar = 0 := by
  rw [entropicProperTime, zero_div]

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity

namespace Physlib.Thermodynamics.SecondLaw

/-! ## Sergi constant-decay dynamics

This section owns the source-specific scalar solution of Sergi & Giaquinta
2016, Eqs. 14-17.  `Physlib.Thermodynamics.SecondLaw` imports this file and
uses the structure below to build an `EntropyArrowWorldline`; the scalar
non-Hermitian dynamics itself is not second-law infrastructure.
-/

/-- **Sergi & Giaquinta 2016 constant-decay model.**  Data for a
non-Hermitian Hamiltonian whose anti-Hermitian part is proportional
to the identity, `H_I = (ℏ·γ₀/2)·I`.

Sergi's Eqs. (15) and (17) become *defined functions* of laboratory
time `t : ℝ`, with the monotonicity of the arrow following from
`0 ≤ γ₀` (decay-rate non-negativity, i.e., `H_I ⪰ 0`). -/
structure SergiConstantDecaySystem where
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ
  /-- Boltzmann constant. -/
  k_B : ℝ
  /-- `k_B > 0`. -/
  k_B_pos : 0 < k_B
  /-- Decay-rate parameter, Sergi Eq. (14): `H_I = (ℏ·γ₀/2)·I`.  Non-negative
      so that `H_I ⪰ 0` and probability decays (not grows). -/
  γ₀ : ℝ
  /-- `γ₀ ≥ 0`. -/
  γ₀_nonneg : 0 ≤ γ₀
  /-- Initial von Neumann entropy `S_vN(0)` of the normalised state. -/
  S_vN_initial : ℝ

namespace SergiConstantDecaySystem

variable (S : SergiConstantDecaySystem)

/-- **Sergi Eq. (15).**  Non-normalised trace decay
`Tr Ω̂(t) = exp(−γ₀·t)`.  Provable from Sergi Eq. (6) at constant decay
`Γ̂ = (ℏ·γ₀/2)·I`:  `∂_t Tr Ω̂ = −(2/ℏ)·Tr(Γ̂ Ω̂) = −γ₀·Tr Ω̂`. -/
noncomputable def traceOmega (t : ℝ) : ℝ := Real.exp (-S.γ₀ * t)

/-- `Tr Ω̂(0) = 1`. -/
@[simp]
theorem traceOmega_at_zero : S.traceOmega 0 = 1 := by
  unfold traceOmega
  rw [mul_zero, Real.exp_zero]

/-- `Tr Ω̂(t) > 0` for all `t`. -/
theorem traceOmega_pos (t : ℝ) : 0 < S.traceOmega t :=
  Real.exp_pos _

/-- `Tr Ω̂` is monotone-decreasing (probability is lost, never gained). -/
theorem traceOmega_antitone : Antitone S.traceOmega := by
  intro t₁ t₂ h
  unfold traceOmega
  apply Real.exp_le_exp.mpr
  nlinarith [S.γ₀_nonneg]

/-- **Sergi Eq. (28).**  `Tr Ω̂²(t) = Tr Ω̂²(0)·exp(−2γ₀·t)` — purity envelope. -/
noncomputable def traceOmegaSq (TrOmegaSq0 : ℝ) (t : ℝ) : ℝ :=
  TrOmegaSq0 * Real.exp (-2 * S.γ₀ * t)

/-- **Sergi Eq. (17).**  Non-Hermitian entropy grows linearly:
`S_NH(t) = S_vN(0) + k_B·γ₀·t`.

Derivation: `S_NH(t) := −k_B·Tr(ρ̂ ln Ω̂)`.  Under constant decay
`Γ̂ = (ℏ·γ₀/2)·I` the normalised state evolves *unitarily*
`ρ̂(t) = U(t)·ρ̂(0)·U(t)†` (Sergi Eq. (8) trivialises because the
{Γ̂, ρ̂}₊ and probability-restoring terms cancel).  Hence
`Ω̂(t) = e^(−γ₀·t)·U·Ω̂(0)·U†` and
`Tr(ρ̂(t)·ln Ω̂(t)) = −γ₀·t + Tr(ρ̂(0)·ln Ω̂(0))`,
giving `S_NH(t) = S_NH(0) + k_B·γ₀·t`, and `S_NH(0) = S_vN(0)`
when `Ω̂(0) = ρ̂(0)`. -/
noncomputable def S_NH (t : ℝ) : ℝ := S.S_vN_initial + S.k_B * S.γ₀ * t

@[simp]
theorem S_NH_at_zero : S.S_NH 0 = S.S_vN_initial := by
  unfold S_NH; ring

/-- `∂_t S_NH = k_B·γ₀`: linear-in-time growth rate, stated as the
difference quotient. -/
theorem S_NH_linear_growth_rate {t₁ t₂ : ℝ} (h : t₁ ≠ t₂) :
    (S.S_NH t₂ - S.S_NH t₁) / (t₂ - t₁) = S.k_B * S.γ₀ := by
  unfold S_NH
  have hne : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

/-- **`S_NH` is monotone non-decreasing in time** (the arrow theorem from
non-Hermitian dynamics with `H_I ⪰ 0`).  Follows from `γ₀ ≥ 0` and `k_B > 0`. -/
theorem S_NH_monotone : Monotone S.S_NH := by
  intro t₁ t₂ h
  unfold S_NH
  have : S.k_B * S.γ₀ * t₁ ≤ S.k_B * S.γ₀ * t₂ :=
    mul_le_mul_of_nonneg_left h (mul_nonneg S.k_B_pos.le S.γ₀_nonneg)
  linarith

/-- `S_NH(t) − S_NH(0) = k_B·γ₀·t` — the entropy increment.  Zero at
`t = 0`, non-negative for `t ≥ 0`. -/
theorem S_NH_increment (t : ℝ) :
    S.S_NH t - S.S_vN_initial = S.k_B * S.γ₀ * t := by
  unfold S_NH; ring

/-- Sergi Eq. (34) "no-go": the standard linear entropy `S_lin = 1 − Tr ρ̂²`
is **identically constant** under constant decay, so it does *not* detect
the open-system arrow.  We record the constant case at the structure level. -/
def S_lin_under_constant_decay (S_lin_initial : ℝ) : ℝ → ℝ :=
  fun _ => S_lin_initial

@[simp]
theorem S_lin_under_constant_decay_eq (S_lin_initial : ℝ) (t : ℝ) :
    S_lin_under_constant_decay S_lin_initial t = S_lin_initial := rfl

/-- **Imaginary action along the worldline** via Brillouin
identification `S_I = ℏ·(S_NH − S_NH(0))/k_B = ℏ·γ₀·t`. -/
noncomputable def S_I_along (t : ℝ) : ℝ := S.ℏ * S.γ₀ * t

@[simp]
theorem S_I_along_at_zero : S.S_I_along 0 = 0 := by
  unfold S_I_along; ring

/-- **The arrow theorem.**  `S_I_along` is monotone non-decreasing —
derived from `γ₀ ≥ 0` and `ℏ > 0`.  This is the **proved** form of
`S_I_monotone` for the Sergi constant-decay case. -/
theorem sergi_S_I_monotone : Monotone S.S_I_along := by
  intro t₁ t₂ h
  unfold S_I_along
  have : S.ℏ * S.γ₀ * t₁ ≤ S.ℏ * S.γ₀ * t₂ :=
    mul_le_mul_of_nonneg_left h (mul_nonneg S.ℏ_pos.le S.γ₀_nonneg)
  linarith

/-- `S_I_along(t) ≥ 0` for `t ≥ 0`. -/
theorem S_I_along_nonneg_of_nonneg_time {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ S.S_I_along t := by
  unfold S_I_along
  exact mul_nonneg (mul_nonneg S.ℏ_pos.le S.γ₀_nonneg) ht

/-- **Entropic proper time τ_ent = γ₀·t** in the Sergi case (Brillouin
identification `τ_ent = S_I/ℏ`). -/
noncomputable def τ_ent_along (t : ℝ) : ℝ := S.γ₀ * t

@[simp]
theorem τ_ent_along_eq_S_I_div_hbar (t : ℝ) :
    S.τ_ent_along t = S.S_I_along t / S.ℏ := by
  unfold τ_ent_along S_I_along
  have h : S.ℏ ≠ 0 := ne_of_gt S.ℏ_pos
  field_simp

end SergiConstantDecaySystem

/-! ## Phase D — operator-level Sergi superoperator (Eq. 5) and the probability-decay theorem (Eq. 6)

The constant-decay structure `SergiConstantDecaySystem` provides the *scalar*
`Tr Ω̂(t) = exp(−γ₀·t)` (Eq. 15) as a defined function.  Phase D promotes
this to the **operator level**: we define the Sergi superoperator that
appears on the RHS of Eq. (5),

  `L_S(Ω̂) := −(i/ℏ)·[H_R, Ω̂]₋ − (1/ℏ)·{H_I, Ω̂}₊`,

(`[·,·]₋` commutator, `{·,·}₊` anticommutator), and **derive Eq. (6)**

  `Tr(L_S Ω̂) = −(2/ℏ)·Tr(H_I·Ω̂)`

purely from the finite-target cyclic-trace identities `trace_commutator` and
`trace_anticommutator`.  Specialising `H_I := (ℏ·γ₀/2)·I` reproduces the scalar
decay rate `−γ₀·Tr Ω̂` of `SergiConstantDecaySystem.traceOmega`.

No new axioms.  Source: [Sergi-Giaquinta 2016, Eqs. (5), (6)].
-/

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Sergi superoperator at the matrix level** (the RHS of Sergi Eq. 5):

  `L_S(Ω̂) := −(i/ℏ)·[H_R, Ω̂]₋ − (1/ℏ)·{H_I, Ω̂}₊`,

with `[A,B]₋ := A·B − B·A` and `{A,B}₊ := A·B + B·A`.

Takes matrices `H_R, H_I : Matrix d d ℂ` (the real/imaginary parts of the
non-Hermitian Hamiltonian, intended to be Hermitian), a real `ℏ`, and a
matrix `Ω̂` (intended to be a non-normalised density matrix). -/
noncomputable def sergiGeneratorMatrix
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (Ω : Matrix d d ℂ) :
    Matrix d d ℂ :=
  -((Complex.I / (ℏ : ℂ)) • QuantumMechanics.FiniteTarget.commutator H_R Ω)
    - ((1 / (ℏ : ℂ)) • QuantumMechanics.FiniteTarget.anticommutator H_I Ω)

/-- **Sergi Eq. (6) at the operator level**: the trace of the Sergi
generator equals `−(2/ℏ)·Tr(H_I·Ω̂)`.

This is the **derivation** of the operator-level probability-decay rate
`∂_t Tr Ω̂ = −(2/ℏ)·Tr(H_I·Ω̂)` from the commutator/anticommutator algebra
alone — no ODE machinery required, just cyclic trace. -/
theorem sergi_generator_trace
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (hℏ : (ℏ : ℂ) ≠ 0)
    (Ω : Matrix d d ℂ) :
    (sergiGeneratorMatrix H_R H_I ℏ Ω).trace
      = -(2 / (ℏ : ℂ)) * (H_I * Ω).trace := by
  unfold sergiGeneratorMatrix
  rw [Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul,
      Matrix.trace_smul, QuantumMechanics.FiniteTarget.trace_commutator,
      QuantumMechanics.FiniteTarget.trace_anticommutator]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- **Constant-decay specialisation of Sergi Eq. (6).**  Setting
`H_I = (ℏ·γ₀/2)·I` (Sergi Eq. 14) reduces the operator-level decay rate
`−(2/ℏ)·Tr(H_I·Ω̂)` to the scalar `−γ₀·Tr Ω̂` — recovering the rate
underlying `SergiConstantDecaySystem.traceOmega t = exp(−γ₀·t)`. -/
theorem sergi_generator_trace_constant_decay
    (H_R : Matrix d d ℂ) (ℏ γ₀ : ℝ) (hℏ : (ℏ : ℂ) ≠ 0) (Ω : Matrix d d ℂ) :
    (sergiGeneratorMatrix H_R
        (((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) ℏ Ω).trace
      = -(γ₀ : ℂ) * Ω.trace := by
  rw [sergi_generator_trace H_R _ ℏ hℏ]
  -- Reduce `Tr(((ℏ·γ₀/2) • I) · Ω) = (ℏ·γ₀/2) · Tr Ω`.
  rw [show (((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) * Ω
        = ((ℏ * γ₀ / 2 : ℝ) : ℂ) • Ω by
    rw [Matrix.smul_mul, Matrix.one_mul]]
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul]
  push_cast
  field_simp

/-- **Bridge to `SergiConstantDecaySystem`**: at the constant-decay
`H_I = (ℏ·γ₀/2)·I` and with `Tr Ω̂(0) = 1`, the operator-level rate from
`sergi_generator_trace_constant_decay` produces the scalar ODE
`(d/dt)·Tr Ω̂(t) = −γ₀·Tr Ω̂(t)` whose solution is precisely
`SergiConstantDecaySystem.traceOmega t = exp(−γ₀·t)`.  We expose the
*rate identity at t = 0*:

  `Tr(L_S Ω̂(0)) = −γ₀·1 = −γ₀`,

matching the laboratory-time derivative `(d/dt) traceOmega 0 = −γ₀`. -/
theorem sergi_generator_trace_at_initial
    (S : SergiConstantDecaySystem) (H_R : Matrix d d ℂ)
    (Ω₀ : Matrix d d ℂ) (h_init : Ω₀.trace = 1) :
    (sergiGeneratorMatrix H_R
        (((S.ℏ * S.γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) S.ℏ Ω₀).trace
      = -(S.γ₀ : ℂ) := by
  rw [sergi_generator_trace_constant_decay H_R S.ℏ S.γ₀
        (by exact_mod_cast (ne_of_gt S.ℏ_pos)) Ω₀, h_init]
  ring

/-! ## Phase D₂ — Sergi normalised generator (Eq. 8) and trace conservation

Sergi & Giaquinta 2016 also define the evolution of the *normalised*
density matrix `ρ̂ = Ω̂ / Tr Ω̂`:

  `∂_t ρ̂ = −(i/ℏ)·[H_R, ρ̂]₋ − (1/ℏ)·{H_I, ρ̂}₊ + (2/ℏ)·Tr(H_I·ρ̂)·ρ̂`   (Eq. 8)

The third term — nonlinear in `ρ̂` — restores trace conservation that
the linear part `L_S` (Phase D) would otherwise violate.  Phase D₂
proves this operator-level fact:

  **Trace conservation**:  `Tr(L_S^{norm} ρ̂) = 0` when `Tr ρ̂ = 1`.

A further specialisation: under constant decay `H_I = (ℏ·γ₀/2)·I`
(Sergi Eq. 14) AND `Tr ρ̂ = 1`, the normalised generator reduces to
the **pure unitary commutator** `−(i/ℏ)·[H_R, ρ̂]₋` — the third term
exactly cancels the anticommutator term.  This is the operator-level
derivation of Sergi Eq. (16): `S_vN(t) = S_vN(0) = const` along the
constant-decay trajectory (the von Neumann entropy is unitary
invariant, so it is conserved by the unitary evolution we just
exhibited).

This establishes the "ρ̂ evolves unitarily under constant decay"
remark cited in Phase F's docstring.

No new axioms.  Source: [Sergi-Giaquinta 2016, Eqs. (7), (8), (16)].
-/

/-- **Sergi normalised superoperator** (RHS of Sergi Eq. 8):

  `L_S^{norm}(ρ̂) := −(i/ℏ)·[H_R, ρ̂]₋ − (1/ℏ)·{H_I, ρ̂}₊ + (2/ℏ)·Tr(H_I·ρ̂)·ρ̂`.

The nonlinear third term is the trace-restoration term that ensures
`Tr ρ̂ = 1` is preserved along the evolution. -/
noncomputable def sergiNormalisedGeneratorMatrix
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (ρ : Matrix d d ℂ) : Matrix d d ℂ :=
  sergiGeneratorMatrix H_R H_I ℏ ρ
    + ((2 / (ℏ : ℂ)) * (H_I * ρ).trace) • ρ

set_option linter.unusedSectionVars false in
/-- **Sergi Eq. (8) decomposed**: the normalised generator equals the
linear Sergi generator (Phase D) plus the trace-restoration term. -/
theorem sergiNormalisedGeneratorMatrix_eq_linear_plus_restoration
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (ρ : Matrix d d ℂ) :
    sergiNormalisedGeneratorMatrix H_R H_I ℏ ρ
      = sergiGeneratorMatrix H_R H_I ℏ ρ
        + ((2 / (ℏ : ℂ)) * (H_I * ρ).trace) • ρ := rfl

/-- **Trace conservation under the Sergi normalised evolution**:
`Tr(L_S^{norm} ρ̂) = 0` whenever `Tr ρ̂ = 1`.

Proof: by Phase D's `sergi_generator_trace`, the linear part contributes
`−(2/ℏ)·Tr(H_I·ρ̂)`.  The restoration term contributes
`(2/ℏ)·Tr(H_I·ρ̂)·Tr(ρ̂) = (2/ℏ)·Tr(H_I·ρ̂)·1`.  The two cancel. -/
theorem sergi_normalised_generator_trace_at_unit_trace
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (hℏ : (ℏ : ℂ) ≠ 0)
    (ρ : Matrix d d ℂ) (h_tr : ρ.trace = 1) :
    (sergiNormalisedGeneratorMatrix H_R H_I ℏ ρ).trace = 0 := by
  unfold sergiNormalisedGeneratorMatrix
  rw [Matrix.trace_add, Matrix.trace_smul,
      sergi_generator_trace H_R H_I ℏ hℏ, h_tr]
  simp only [smul_eq_mul]
  ring

/-- **Constant-decay reduction of the normalised generator** (Sergi
Eq. 16, operator level).  When `H_I = (ℏ·γ₀/2)·I` (Sergi Eq. 14) and
`Tr ρ̂ = 1`, the normalised generator reduces to the pure unitary
commutator:

  `L_S^{norm}(ρ̂) = −(i/ℏ)·[H_R, ρ̂]₋`.

The {Γ̂, ρ̂}₊ term contributes `−γ₀·ρ̂` while the restoration term
contributes `+γ₀·ρ̂`; they cancel exactly. -/
theorem sergi_normalised_generator_constant_decay_at_unit_trace
    (H_R : Matrix d d ℂ) (ℏ γ₀ : ℝ) (hℏ : (ℏ : ℂ) ≠ 0)
    (ρ : Matrix d d ℂ) (h_tr : ρ.trace = 1) :
    sergiNormalisedGeneratorMatrix H_R
        (((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) ℏ ρ
      = -((Complex.I / (ℏ : ℂ)) • (H_R * ρ - ρ * H_R)) := by
  unfold sergiNormalisedGeneratorMatrix sergiGeneratorMatrix
  rw [QuantumMechanics.FiniteTarget.commutator_def,
      QuantumMechanics.FiniteTarget.anticommutator_def]
  -- Step 1: anticommutator with (ℏγ₀/2)·I reduces to (ℏγ₀)·ρ.
  have h_anti : (((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) * ρ
        + ρ * (((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ))
        = (((ℏ * γ₀ : ℝ) : ℂ)) • ρ := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
        ← add_smul]
    push_cast
    ring_nf
  -- Step 2: trace of (ℏγ₀/2)·I·ρ = (ℏγ₀/2)·Tr ρ = (ℏγ₀/2).
  have h_trace : ((((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) * ρ).trace
        = ((ℏ * γ₀ / 2 : ℝ) : ℂ) := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, h_tr,
        smul_eq_mul, mul_one]
  rw [h_anti, h_trace]
  -- Step 3: the −(1/ℏ)•(ℏγ₀)•ρ and +(2/ℏ * ℏγ₀/2)•ρ terms cancel.
  -- Reduce both to γ₀ • ρ.
  have h_left : ((1 / (ℏ : ℂ)) • (((ℏ * γ₀ : ℝ) : ℂ) • ρ)) = (γ₀ : ℂ) • ρ := by
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  have h_right : ((2 / (ℏ : ℂ)) * ((ℏ * γ₀ / 2 : ℝ) : ℂ)) • ρ
        = (γ₀ : ℂ) • ρ := by
    congr 1
    push_cast
    field_simp
  rw [h_left, h_right]
  abel

/-- **Specialisation: Sergi-system constant-decay normalised generator**
yields the pure unitary commutator for any state with `Tr ρ̂ = 1`. -/
theorem sergi_normalised_generator_unitary_for_constant_decay_system
    (S : SergiConstantDecaySystem) (H_R : Matrix d d ℂ)
    (ρ : Matrix d d ℂ) (h_tr : ρ.trace = 1) :
    sergiNormalisedGeneratorMatrix H_R
        (((S.ℏ * S.γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) S.ℏ ρ
      = -((Complex.I / (S.ℏ : ℂ)) • (H_R * ρ - ρ * H_R)) :=
  sergi_normalised_generator_constant_decay_at_unit_trace
    H_R S.ℏ S.γ₀
    (by exact_mod_cast (ne_of_gt S.ℏ_pos)) ρ h_tr

/-! ## Phase D₃ — Linear entropy and the Sergi Eq. (34) no-go theorem

Sergi & Giaquinta 2016 introduce the **quantum linear entropy** (Eq. 18)

  `S_lin(ρ̂) := 1 − Tr(ρ̂²)`

as a computationally cheap alternative to the von Neumann entropy.
Its evolution under the normalised Sergi generator (Eq. 8) is

  `Ṡ_lin = (4/ℏ)·[Tr(H_I·ρ̂²) − Tr(H_I·ρ̂)·Tr(ρ̂²)]`        (Eq. 22)

The critical Sergi result (Eq. 34): **under constant decay
`H_I = (ℏ·γ₀/2)·I` and `Tr ρ̂ = 1`, the linear-entropy rate is
identically zero**.  The two terms in Eq. (22) collapse to the same
value `(ℏ·γ₀/2)·Tr(ρ̂²)` and cancel.

This is a **no-go theorem**: the standard linear entropy on the
*normalised* state does not detect the open-system arrow.  Anyone
porting Sergi's framework who tries to use `S_lin` as an entropic
arrow indicator will get the same constant — they have to switch
to the *non-Hermitian* linear entropy `S^{NH}_lin = 1 − Tr(ρ̂·Ω̂)`
(Eq. 23), whose closed-form solution under constant decay (Eq. 36)

  `S^{NH}_lin(t) = (1 − e^{−γ₀·t})·Tr Ω̂²(0)`

*is* monotone increasing (a bounded arrow).

This phase exposes both functionals as defined operators with their
rate forms, the no-go for `S_lin`, and the bounded-arrow closed form
for `S^{NH}_lin`.

No new axioms.  Source: [Sergi-Giaquinta 2016, Eqs. (18), (22), (23), (26), (34), (36)].
-/

/-- **Quantum linear entropy** (Sergi Eq. 18): `S_lin(ρ̂) := 1 − Tr(ρ̂²)`.
The traceful purity-deficit functional. -/
noncomputable def linearEntropy (ρ : Matrix d d ℂ) : ℂ := 1 - (ρ * ρ).trace

/-- **Non-Hermitian linear entropy** (Sergi Eq. 23):
`S^{NH}_lin(ρ̂, Ω̂) := 1 − Tr(ρ̂·Ω̂)`.  Cross-pairing of the
normalised and non-normalised density matrices. -/
noncomputable def nonHermitianLinearEntropy
    (ρ Ω : Matrix d d ℂ) : ℂ := 1 - (ρ * Ω).trace

/-- **Sergi Eq. (22) RHS — the linear-entropy rate under normalised Sergi
evolution Eq. (8)**:

  `Ṡ_lin = (4/ℏ)·[Tr(H_I·ρ̂²) − Tr(H_I·ρ̂)·Tr(ρ̂²)]`.

Defined as a bilinear function of `H_I` and `ρ̂`.  The dependence on
`H_R` is suppressed because the unitary commutator term contributes
zero to the rate (cyclic trace `Tr(ρ̂·[H_R, ρ̂]₋) = 0`). -/
noncomputable def linearEntropyRate
    (H_I : Matrix d d ℂ) (ℏ : ℝ) (ρ : Matrix d d ℂ) : ℂ :=
  (4 / (ℏ : ℂ))
    * ((H_I * (ρ * ρ)).trace - (H_I * ρ).trace * (ρ * ρ).trace)

/-- **Sergi Eq. (34) — the linear-entropy no-go theorem.**

Under constant decay `H_I = (ℏ·γ₀/2)·I` (Sergi Eq. 14) AND `Tr ρ̂ = 1`,
the linear-entropy rate vanishes identically:

  `Ṡ_lin = 0`.

Consequence: `S_lin = 1 − Tr(ρ̂²)` is *not* a valid entropic-arrow
indicator in this case.  An anyone using `S_lin` to detect the
open-system arrow will measure zero entropy production — a
phenomenological no-go that the framework structurally enforces. -/
theorem linearEntropyRate_constant_decay_at_unit_trace
    (ℏ γ₀ : ℝ)
    (ρ : Matrix d d ℂ) (h_tr : ρ.trace = 1) :
    linearEntropyRate (((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) ℏ ρ = 0 := by
  unfold linearEntropyRate
  -- Pull the scalar out of both traces:
  have h_term2 : ((((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) * (ρ * ρ)).trace
        = ((ℏ * γ₀ / 2 : ℝ) : ℂ) * (ρ * ρ).trace := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  have h_term1 : ((((ℏ * γ₀ / 2 : ℝ) : ℂ) • (1 : Matrix d d ℂ)) * ρ).trace
        = ((ℏ * γ₀ / 2 : ℝ) : ℂ) * ρ.trace := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  rw [h_term1, h_term2, h_tr, mul_one, sub_self, mul_zero]

/-- **Sergi `S^{NH}_lin` closed-form solution** (Eq. 36): under constant
decay `H_I = (ℏ·γ₀/2)·I`, with normalised initial state `Tr Ω̂(0) = 1`
and purity envelope `Tr Ω̂²(t) = TrOmegaSq0·exp(−2γ₀·t)` (Sergi Eq. 28),
the non-Hermitian linear entropy along the worldline reads

  `S^{NH}_lin(t) = (1 − e^{−γ₀·t})·TrOmegaSq0`.

We expose this as a *defined function* of laboratory time, parameterised
by the initial `TrOmegaSq0 := Tr Ω̂²(0)` and the decay rate `γ₀`. -/
noncomputable def nonHermitianLinearEntropyClosedForm
    (γ₀ TrOmegaSq0 t : ℝ) : ℝ :=
  (1 - Real.exp (-γ₀ * t)) * TrOmegaSq0

/-- Value at `t = 0`: vanishes. -/
@[simp]
theorem nonHermitianLinearEntropyClosedForm_at_zero
    (γ₀ TrOmegaSq0 : ℝ) :
    nonHermitianLinearEntropyClosedForm γ₀ TrOmegaSq0 0 = 0 := by
  unfold nonHermitianLinearEntropyClosedForm
  simp

/-- For `γ₀ ≥ 0` and `TrOmegaSq0 ≥ 0`, the bounded-arrow value
`S^{NH}_lin(t)` is non-negative for all `t ≥ 0`. -/
theorem nonHermitianLinearEntropyClosedForm_nonneg
    {γ₀ TrOmegaSq0 : ℝ} (hγ : 0 ≤ γ₀) (hT : 0 ≤ TrOmegaSq0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ nonHermitianLinearEntropyClosedForm γ₀ TrOmegaSq0 t := by
  unfold nonHermitianLinearEntropyClosedForm
  apply mul_nonneg _ hT
  have h_exp_le_one : Real.exp (-γ₀ * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  linarith

/-- **`S^{NH}_lin` is monotone non-decreasing in time** when `γ₀ ≥ 0` and
`TrOmegaSq0 ≥ 0` — the *bounded* arrow indicator (in contrast to the
unbounded `S_NH = S_vN(0) + k_B·γ₀·t` of Phase F).  Sergi shows this
saturates to `TrOmegaSq0` as `t → ∞`. -/
theorem nonHermitianLinearEntropyClosedForm_monotone
    {γ₀ TrOmegaSq0 : ℝ} (hγ : 0 ≤ γ₀) (hT : 0 ≤ TrOmegaSq0) :
    Monotone (nonHermitianLinearEntropyClosedForm γ₀ TrOmegaSq0) := by
  intro t₁ t₂ h
  unfold nonHermitianLinearEntropyClosedForm
  apply mul_le_mul_of_nonneg_right _ hT
  have h_exp_mono : Real.exp (-γ₀ * t₂) ≤ Real.exp (-γ₀ * t₁) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  linarith

/-- **Bounded-above by `TrOmegaSq0`**: as `t → ∞` the bounded-arrow
indicator saturates to `TrOmegaSq0` (Sergi Eq. 36 saturation).  Algebraically,
the closed form never exceeds this ceiling whenever `TrOmegaSq0 ≥ 0`; the
physical decay hypotheses are only needed for monotonic approach to the
ceiling, handled by `nonHermitianLinearEntropyClosedForm_monotone`. -/
theorem nonHermitianLinearEntropyClosedForm_le_ceiling
    {γ₀ TrOmegaSq0 t : ℝ} (hT : 0 ≤ TrOmegaSq0) :
    nonHermitianLinearEntropyClosedForm γ₀ TrOmegaSq0 t ≤ TrOmegaSq0 := by
  unfold nonHermitianLinearEntropyClosedForm
  have h_exp_nonneg : 0 ≤ Real.exp (-γ₀ * t) := (Real.exp_pos _).le
  nlinarith

/-! ## Phase E (full) — Operator-level Sergi Eq. (13)

Establishes the headline algebraic identity of Sergi & Giaquinta 2016:

  `S_vN(ρ̂) − S_NH(ρ̂, Ω̂) = k_B · ln(Tr Ω̂)`              (Eq. 13)

at the *operator* level — i.e., directly from the `HermitianMat.log`
spectral functional calculus, not from a postulated scalar identity.

Setup: a non-singular non-normalised density matrix `Ω̂ : HermitianMat d ℂ`
with `Tr Ω̂ ≠ 0`, and the associated normalised state
`ρ̂ := (Tr Ω̂)⁻¹ • Ω̂` (so `Tr ρ̂ = 1`).

  * `S_vN(ρ̂) := −k_B · ⟪ρ̂, ln ρ̂⟫`            (Sergi Eq. 9, operator level)
  * `S_NH(ρ̂, Ω̂) := −k_B · ⟪ρ̂, ln Ω̂⟫`         (Sergi Eq. 11, operator level)

Key lemma used:

  * `HermitianMat.log_smul`: `(x • A).log = Real.log x • 1 + A.log`
    for `A` non-singular and `x ≠ 0`.

The proof unfolds the inner product via `inner_add_right`,
`inner_smul_right`, and `inner_one`, then uses `Tr ρ̂ = 1` to collapse.

Together with Phase F's *scalar* `SergiConstantDecaySystem.S_NH t =
S_vN(0) + k_B·γ₀·t` (linear-in-time Eq. 17), Phase E ties the
*scalar* S_NH growth to a properly defined operator-level S_NH via
Sergi Eq. (13).

No new axioms.  Source: [Sergi-Giaquinta 2016, Eq. (13)].
-/

section PhaseE_full

open HermitianMat in
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- **Operator-level von Neumann entropy** (Sergi Eq. 9):
`S_vN(ρ̂) := −k_B · ⟪ρ̂, ln ρ̂⟫`. -/
noncomputable def operatorVonNeumann
    (k_B : ℝ) (ρ : HermitianMat d ℂ) : ℝ :=
  -k_B * ⟪ρ, ρ.log⟫

/-- **Operator-level non-Hermitian entropy** (Sergi Eq. 11):
`S_NH(ρ̂, Ω̂) := −k_B · ⟪ρ̂, ln Ω̂⟫`.  Computes against the *non-normalised*
log, the load-bearing change that turns the linear-time arrow on. -/
noncomputable def operatorNonHermitianEntropy
    (k_B : ℝ) (ρ Ω : HermitianMat d ℂ) : ℝ :=
  -k_B * ⟪ρ, Ω.log⟫

set_option linter.unusedSectionVars false in
/-- **Trace of the normalised state** is `1`: `Tr((Tr Ω̂)⁻¹ • Ω̂) = 1`. -/
theorem trace_smul_inv_self (Ω : HermitianMat d ℂ) (hΩ_tr : Ω.trace ≠ 0) :
    ((Ω.trace)⁻¹ • Ω).trace = 1 := by
  rw [HermitianMat.trace_smul, inv_mul_cancel₀ hΩ_tr]

/-- **Sergi Eq. (13) — operator-level Sergi identity**.

For a non-singular non-normalised density matrix `Ω̂` with `Tr Ω̂ > 0`,
the difference between the von Neumann entropy of the normalised state
`ρ̂ := (Tr Ω̂)⁻¹ • Ω̂` and the non-Hermitian entropy `S_NH(ρ̂, Ω̂)` is

  `S_vN(ρ̂) − S_NH(ρ̂, Ω̂) = k_B · ln(Tr Ω̂)`.

Proof outline: use `HermitianMat.log_smul` (with `x = (Tr Ω̂)⁻¹ ≠ 0` and
`HermitianMat.NonSingular Ω`) to write
`ρ̂.log = Real.log(Tr Ω̂)⁻¹ • 1 + Ω̂.log = −Real.log(Tr Ω̂) • 1 + Ω̂.log`,
then expand the inner product. -/
theorem operator_sergi_eq13
    (k_B : ℝ) (Ω : HermitianMat d ℂ)
    (hΩ_tr_pos : 0 < Ω.trace) [HermitianMat.NonSingular Ω] :
    operatorVonNeumann k_B ((Ω.trace)⁻¹ • Ω)
      - operatorNonHermitianEntropy k_B ((Ω.trace)⁻¹ • Ω) Ω
      = k_B * Real.log Ω.trace := by
  unfold operatorVonNeumann operatorNonHermitianEntropy
  set ρ : HermitianMat d ℂ := (Ω.trace)⁻¹ • Ω with hρ_def
  have hΩ_tr : Ω.trace ≠ 0 := ne_of_gt hΩ_tr_pos
  have h_inv_ne : ((Ω.trace : ℝ))⁻¹ ≠ 0 := inv_ne_zero hΩ_tr
  -- Step 1: ρ.log = Real.log (Ω.trace)⁻¹ • 1 + Ω.log
  have h_ρ_log : ρ.log
      = Real.log ((Ω.trace : ℝ))⁻¹ • (1 : HermitianMat d ℂ) + Ω.log := by
    rw [hρ_def]
    exact HermitianMat.log_smul h_inv_ne
  -- Step 2: Tr ρ = 1.
  have h_ρ_tr : ρ.trace = 1 := trace_smul_inv_self Ω hΩ_tr
  -- Step 3: expand ⟪ρ, ρ.log⟫.
  have h_inner : ⟪ρ, ρ.log⟫
      = Real.log ((Ω.trace : ℝ))⁻¹ + ⟪ρ, Ω.log⟫ := by
    rw [h_ρ_log, HermitianMat.inner_add_right, HermitianMat.inner_smul_right,
        HermitianMat.inner_one, h_ρ_tr, mul_one]
  -- Step 4: assemble.  Use Real.log_inv to flip the sign.
  rw [h_inner, Real.log_inv]
  ring

end PhaseE_full

/-! ## Phase D-Herm — HermitianMat lift of the Sergi superoperator

Phase D/D₂/D₃ live at the `Matrix d d ℂ` level.  This section lifts the
load-bearing pieces to `HermitianMat d ℂ`, making the Sergi spine
usable from downstream `HermitianMat`-based infrastructure
(`Sᵥₙ`, `qRelativeEnt`, `MState`).

The key construction is to package the *anticommutator* and the
*i-commutator* of two Hermitian matrices as `HermitianMat` values
(both are Hermitian when the inputs are), then build the Sergi
generator from them using HermitianMat's `+`, `−`, `•`.

The HermitianMat-level trace theorem (Sergi Eq. 6) reads

  `(sergiGeneratorHerm H_R H_I ℏ Ω).trace = −(2/ℏ) · ⟪H_I, Ω⟫_ℝ`

using physlib's HermitianMat real-valued inner product.

No new axioms.  Source: [Sergi-Giaquinta 2016, Eq. (6)].
-/

section PhaseD_Herm

open HermitianMat in
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- **Anticommutator of two Hermitian matrices as a HermitianMat.**
`{A, B} = A·B + B·A` is Hermitian when A, B are. -/
noncomputable def anticommutatorHerm (A B : HermitianMat d ℂ) :
    HermitianMat d ℂ :=
  ⟨A.mat * B.mat + B.mat * A.mat, by
    show Matrix.conjTranspose (A.mat * B.mat + B.mat * A.mat)
      = A.mat * B.mat + B.mat * A.mat
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, A.H, B.H, add_comm]⟩

/-- **i-commutator of two Hermitian matrices as a HermitianMat.**
`i·[A, B] = i·(A·B − B·A)` is Hermitian when A, B are
(commutator of two Hermitians is anti-Hermitian, `i` times anti-Hermitian
is Hermitian). -/
noncomputable def iCommutatorHerm (A B : HermitianMat d ℂ) :
    HermitianMat d ℂ :=
  ⟨Complex.I • (A.mat * B.mat - B.mat * A.mat), by
    -- First: star(A·B − B·A) = −(A·B − B·A)  (the commutator is anti-Hermitian)
    have hAnti : Matrix.conjTranspose (A.mat * B.mat - B.mat * A.mat)
          = -(A.mat * B.mat - B.mat * A.mat) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, A.H, B.H]
      exact (neg_sub _ _).symm
    -- Now use it: star(I • X) = star(I) • star(X) = (-I) • (-X) = I • X.
    show Matrix.conjTranspose (Complex.I • (A.mat * B.mat - B.mat * A.mat))
      = Complex.I • (A.mat * B.mat - B.mat * A.mat)
    rw [Matrix.conjTranspose_smul, hAnti, Complex.star_def, Complex.conj_I]
    rw [show (-Complex.I) • -(A.mat * B.mat - B.mat * A.mat)
          = Complex.I • (A.mat * B.mat - B.mat * A.mat) by
      rw [smul_neg, neg_smul]
      exact neg_neg _]⟩

/-- **Bridging Sergi Eq. (6) to the HermitianMat inner product**.

When `H_I, Ω` are Hermitian, the matrix-level Sergi trace identity
`Tr(L_S Ω̂) = −(2/ℏ)·Tr(H_I·Ω̂)` lifts to the *real-valued* identity

  `RCLike.re Tr(L_S Ω̂) = −(2/ℏ) · ⟪H_I, Ω̂⟫_ℝ`

using `HermitianMat.inner_eq_re_trace`.  This is the load-bearing
HermitianMat-level statement of Sergi Eq. (6): the real part of the
trace of the linear Sergi generator on Hermitian arguments equals the
real inner product up to the constant `−(2/ℏ)`. -/
theorem sergi_generator_matrix_herm_inner
    (H_R H_I : HermitianMat d ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (Ω : HermitianMat d ℂ) :
    RCLike.re (sergiGeneratorMatrix H_R.mat H_I.mat ℏ Ω.mat).trace
      = -(2 / ℏ) * ⟪H_I, Ω⟫ := by
  have hℏℂ : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  rw [sergi_generator_trace H_R.mat H_I.mat ℏ hℏℂ Ω.mat]
  -- `RCLike.re (-(2/↑ℏ) * z) = -(2/ℏ) * z.re` since -(2/↑ℏ) lifts from ℝ.
  rw [show (-(2 / (ℏ : ℂ))) = (((-(2 / ℏ)) : ℝ) : ℂ) by push_cast; ring]
  rw [show RCLike.re ((((-(2 / ℏ)) : ℝ) : ℂ) * (H_I.mat * Ω.mat).trace)
        = (-(2 / ℏ)) * RCLike.re ((H_I.mat * Ω.mat).trace) from
    Complex.re_ofReal_mul _ _]
  rw [HermitianMat.inner_eq_re_trace]

/-! ### Full HermitianMat lift of the Sergi superoperator

We package the Sergi generator (Sergi Eq. 5 RHS) as a `HermitianMat d ℂ`
itself, built from the Hermitian building blocks `iCommutatorHerm` and
`anticommutatorHerm`:

  `L_S(Ω̂) := −(1/ℏ) • (i·[H_R, Ω̂] + {H_I, Ω̂})`

Both summands are Hermitian, and the real scalar `−(1/ℏ)` acting on a
HermitianMat keeps it Hermitian (HermitianMat's ℝ-smul instance).

The `.mat` equivalence between `sergiGeneratorHerm` and the matrix-level
`sergiGeneratorMatrix` uses the `IsScalarTower ℝ ℂ (Matrix d d ℂ)`
compatibility (`algebraMap_smul`): the ℝ-smul on Matrix d d ℂ agrees
with the ℂ-smul through the canonical embedding `ℝ → ℂ`.

The HermitianMat-level trace identity then follows directly from
`sergi_generator_matrix_herm_inner` + the `.mat` equivalence. -/

/-- **Sergi superoperator packaged as a HermitianMat.**

  `L_S(Ω̂) := −(1/ℏ) • (iCommutatorHerm H_R Ω̂ + anticommutatorHerm H_I Ω̂)`.

Hermitian because both summands are Hermitian (i-commutator and
anticommutator of Hermitians, see `iCommutatorHerm`, `anticommutatorHerm`)
and the real scalar `−(1/ℏ)` preserves Hermiticity. -/
noncomputable def sergiGeneratorHerm
    (H_R H_I : HermitianMat d ℂ) (ℏ : ℝ) (Ω : HermitianMat d ℂ) :
    HermitianMat d ℂ :=
  -((1 / ℏ : ℝ) • (iCommutatorHerm H_R Ω + anticommutatorHerm H_I Ω))

/-- **`.mat` equivalence**: the underlying matrix of `sergiGeneratorHerm`
matches the matrix-level Sergi generator `sergiGeneratorMatrix`.

Proof: unfold both sides, use HermitianMat's `mat_*` lemmas to push the
coercion inward, then convert the outer ℝ-smul to a ℂ-smul via
`algebraMap_smul`, and combine `(1/ℏ : ℂ) · I = I/ℏ`. -/
theorem sergiGeneratorHerm_mat
    (H_R H_I : HermitianMat d ℂ) (ℏ : ℝ) (Ω : HermitianMat d ℂ) :
    (sergiGeneratorHerm H_R H_I ℏ Ω).mat
      = sergiGeneratorMatrix H_R.mat H_I.mat ℏ Ω.mat := by
  unfold sergiGeneratorHerm sergiGeneratorMatrix
  simp only [QuantumMechanics.FiniteTarget.commutator, QuantumMechanics.FiniteTarget.anticommutator]
  simp only [HermitianMat.mat_neg, HermitianMat.mat_smul, HermitianMat.mat_add]
  -- LHS now: -((1/ℏ : ℝ) • (iCommutatorHerm.mat + anticommutatorHerm.mat))
  unfold iCommutatorHerm anticommutatorHerm
  simp only [HermitianMat.mat_mk]
  -- LHS: -((1/ℏ : ℝ) • (Complex.I • (HR*Ω - Ω*HR) + (HI*Ω + Ω*HI)))
  -- Convert outer ℝ-smul to ℂ-smul through algebraMap ℝ ℂ.
  rw [show ((1 / ℏ : ℝ)
            • (Complex.I • (H_R.mat * Ω.mat - Ω.mat * H_R.mat)
                + (H_I.mat * Ω.mat + Ω.mat * H_I.mat)) : Matrix d d ℂ)
        = ((1 / (ℏ : ℂ))
            • (Complex.I • (H_R.mat * Ω.mat - Ω.mat * H_R.mat)
                + (H_I.mat * Ω.mat + Ω.mat * H_I.mat))) by
    have : ((1 / ℏ : ℝ) : ℂ) = (1 / (ℏ : ℂ)) := by push_cast; ring
    rw [← this, ← IsScalarTower.algebraMap_smul ℂ]
    rfl]
  -- LHS: -((1/ℏ : ℂ) • (I • X + Y)) with X = (HR*Ω - Ω*HR), Y = (HI*Ω + Ω*HI)
  rw [smul_add]
  -- LHS: -((1/ℏ : ℂ) • (I • X) + (1/ℏ : ℂ) • Y)
  rw [smul_smul]
  -- LHS: -(((1/ℏ : ℂ) * I) • X + (1/ℏ : ℂ) • Y)
  rw [show ((1 / (ℏ : ℂ)) * Complex.I) = Complex.I / (ℏ : ℂ) by ring]
  -- LHS: -((I/ℏ) • X + (1/ℏ) • Y)
  -- RHS: -((I/ℏ) • X) - ((1/ℏ) • Y)
  ring_nf
  abel

/-- **Sergi Eq. (6) at the full HermitianMat level**:

  `(sergiGeneratorHerm H_R H_I ℏ Ω).trace = −(2/ℏ) · ⟪H_I, Ω⟫_ℝ`.

Direct consequence of `sergiGeneratorHerm_mat` + `sergi_generator_matrix_herm_inner`:
the HermitianMat-level trace of the Sergi generator equals the real-valued
inner product of `H_I` and `Ω` scaled by `−(2/ℏ)`. -/
theorem sergiGeneratorHerm_trace
    (H_R H_I : HermitianMat d ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0) (Ω : HermitianMat d ℂ) :
    (sergiGeneratorHerm H_R H_I ℏ Ω).trace = -(2 / ℏ) * ⟪H_I, Ω⟫ := by
  -- HermitianMat.trace at ℂ is RCLike.re of Matrix.trace.
  rw [show (sergiGeneratorHerm H_R H_I ℏ Ω).trace
        = RCLike.re ((sergiGeneratorHerm H_R H_I ℏ Ω).mat).trace from rfl]
  rw [sergiGeneratorHerm_mat]
  exact sergi_generator_matrix_herm_inner H_R H_I ℏ hℏ Ω

/-- **Constant-decay specialisation at HermitianMat level**:
under `H_I = (ℏ·γ₀/2) • 1` (using the HermitianMat one), the
HermitianMat-level Sergi trace becomes `(L_S Ω̂).trace = −γ₀ · Tr Ω̂`. -/
theorem sergiGeneratorHerm_trace_constant_decay
    (H_R : HermitianMat d ℂ) (ℏ γ₀ : ℝ) (hℏ : ℏ ≠ 0) (Ω : HermitianMat d ℂ) :
    (sergiGeneratorHerm H_R ((ℏ * γ₀ / 2 : ℝ) • (1 : HermitianMat d ℂ)) ℏ Ω).trace
      = -γ₀ * Ω.trace := by
  rw [sergiGeneratorHerm_trace H_R _ ℏ hℏ Ω]
  -- ⟪(ℏ·γ₀/2) • 1, Ω⟫ = (ℏ·γ₀/2) · ⟪1, Ω⟫ = (ℏ·γ₀/2) · Tr Ω
  rw [HermitianMat.inner_smul_left, HermitianMat.one_inner]
  field_simp

end PhaseD_Herm


/-! ## Phase G — Wigner-partial mixed quantum-classical scaffolding

Sergi & Giaquinta 2016 §IV–V extend the non-Hermitian formalism to mixed
quantum-classical systems: a quantum subsystem `(r̂, p̂)` embedded in a
classical bath with phase-space coordinates `X = (R, P)` (the "heavy"
degrees of freedom).  The partial Wigner transform Ω̂_W(X, t) is

  Ω̂_W(X, t) := (2πℏ)^(−N) · ∫dZ · e^{i P·Z/ℏ} · ⟨R − Z/2 | Ω̂(t) | R + Z/2⟩  (Eq. 38)

leading to a master equation (Sergi Eq. 40) that combines the commutator
(quantum), Poisson bracket (classical), and anticommutator (decay) terms.

A *full* port of Sergi §IV requires phase-space integration, the
symplectic matrix `B_{ab} = -B_{ba}^T`, and Poisson-bracket
infrastructure that physlib does not yet host.  Phase G provides the
**structure-level scaffolding** — the data of a Wigner-partial Sergi
system — along with two structural observations:

  (i) at zero coupling to the classical bath (`B_{ab} = 0`), the Wigner
      evolution reduces to a purely operator-level Sergi system on each
      phase-space point;
  (ii) Sergi Eq. (41): the *integrated* trace `∫dX · T̃r Ω̂_W(X, t)` is
      generally *not* conserved — the standard probability sink/source
      behaviour for a system with `Γ̂ ≠ 0`.

Both observations are at the structure (scalar-data) level: full
phase-space integration is deferred to a future phase with proper
symplectic-manifold infrastructure.

No new axioms.  Source: [Sergi-Giaquinta 2016, Eqs. (37)–(41)].
-/

/-- **Wigner-partial Sergi system** (Sergi §IV-V structure).

Data for a non-Hermitian quantum subsystem embedded in a classical bath
with phase-space coordinate type `X`.  At each `X` we have:

  * `H_W X : Matrix d d ℂ` — Hermitian Hamiltonian (parametrised by X)
  * `Γ_W X : Matrix d d ℂ` — decay operator (positive Hermitian, parametrised by X)

Time evolution is governed by Sergi Eq. (40); we expose only the
*structure* (data shape) plus the load-bearing trace observation.

The "B_ab" symplectic structure (Sergi Eq. 40 middle terms) is *not*
ported here — it would require additional phase-space differential
geometry. -/
structure WignerSergiSystem (d : Type*) [Fintype d] [DecidableEq d] (X : Type*) where
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ
  /-- Hermitian Hamiltonian parametrised by the bath phase-space point. -/
  H_W : X → Matrix d d ℂ
  /-- Decay operator parametrised by the bath phase-space point. -/
  Γ_W : X → Matrix d d ℂ
  /-- The Wigner-transformed non-normalised density matrix evolved in
      time and parametrised by the phase-space point. -/
  Ω_W : X → ℝ → Matrix d d ℂ

namespace WignerSergiSystem

variable {d : Type*} [Fintype d] [DecidableEq d] {X : Type*}
variable (S : WignerSergiSystem d X)

/-- **Pure-operator-level Sergi limit at fixed `X`.**  Forgetting the
phase-space dependence, fixing a single bath point `x`, recovers the
operator-level Sergi system (Phase D) for the Hamiltonian / decay
operator at that point. -/
noncomputable def fixedPointGenerator (x : X) (t : ℝ) : Matrix d d ℂ :=
  sergiGeneratorMatrix (S.H_W x) (S.Γ_W x) S.ℏ (S.Ω_W x t)

/-- **Sergi Eq. (6) at fixed phase-space point.**  Specialised
trace identity `Tr(L_S Ω̂_W(x)) = −(2/ℏ)·Tr(Γ̂_W(x) · Ω̂_W(x))` from
Phase D applied to each phase-space point. -/
theorem fixedPointGenerator_trace (x : X) (t : ℝ) :
    (S.fixedPointGenerator x t).trace
      = -(2 / (S.ℏ : ℂ)) * (S.Γ_W x * S.Ω_W x t).trace :=
  sergi_generator_trace (S.H_W x) (S.Γ_W x) S.ℏ
    (by exact_mod_cast (ne_of_gt S.ℏ_pos)) (S.Ω_W x t)

/-- **Phase-space-point trace decay rate.**  For each bath point `x`,
the pointwise trace `Tr Ω̂_W(x, t)` decays at rate
`−(2/ℏ)·Tr(Γ̂_W(x) · Ω̂_W(x, t))` along the *pure-quantum* (no Poisson
bracket) limit at fixed `x`.

This is the *operator-level* content of Sergi Eq. (41) before the
phase-space integral is performed.  The Poisson-bracket terms in
Sergi Eq. (40) contribute additional pointwise rates that physlib
doesn't yet capture. -/
theorem fixedPointGenerator_trace_decay_rate (x : X) (t : ℝ) :
    (S.fixedPointGenerator x t).trace
      = -(2 / (S.ℏ : ℂ)) * (S.Γ_W x * S.Ω_W x t).trace :=
  S.fixedPointGenerator_trace x t

end WignerSergiSystem

/-! ## Phase H — Madelung-Sergi bridge (classical fluid ↔ quantum decay)

The Madelung polar decomposition `ψ = R · exp(i·S/ℏ)` (in
`Physlib.QuantumMechanics.NonHermitian.WickRotation`) gives a *classical
fluid* representation of a quantum wavefunction: the density
`|ψ|² = R²` is the fluid mass density, and the phase `S` is the
classical action.

When the Madelung amplitude decays exponentially,
`R(t) = R₀ · exp(−γ·t/2)`, the corresponding density evolves as

  `|ψ(t)|² = R(t)² = R₀² · exp(−γ·t)`,

which is **exactly** the Sergi `traceOmega` function of a constant-decay
system at `γ₀ = γ` (Sergi Eq. 15).  This realises the classical-fluid
instance of the quantum-decay arrow.

In Madelung-Nelson terms: the amplitude-decay rate `γ` is set by the
imaginary Hamiltonian `H_I = ℏ·γ/2` (Sergi Eq. 14, identifying the
positive part with `H_I`), and the Madelung fluid density includes the
exponential decay of probability/mass that defines the entropic-time
arrow on the fluid side.

No new axioms.  Source: [Sergi & Giaquinta 2016, Eq. 15] + Madelung
decomposition.
-/

/-- **Madelung amplitude under exponential decay**: `R(t) = R₀ · exp(−γ·t/2)`. -/
noncomputable def madelungAmplitudeDecay (R₀ γ t : ℝ) : ℝ :=
  R₀ * Real.exp (-γ * t / 2)

/-- **Madelung probability density under exponential amplitude decay**:
`|ψ(t)|² = R(t)² = R₀² · exp(−γ·t)`. -/
noncomputable def madelungDensityDecay (R₀ γ t : ℝ) : ℝ :=
  madelungAmplitudeDecay R₀ γ t ^ 2

@[simp]
theorem madelungAmplitudeDecay_at_zero (R₀ γ : ℝ) :
    madelungAmplitudeDecay R₀ γ 0 = R₀ := by
  unfold madelungAmplitudeDecay; simp

@[simp]
theorem madelungDensityDecay_at_zero (R₀ γ : ℝ) :
    madelungDensityDecay R₀ γ 0 = R₀ ^ 2 := by
  unfold madelungDensityDecay
  rw [madelungAmplitudeDecay_at_zero]

/-- **Madelung density evolves as `R₀² · exp(−γ·t)`** — the standard
exponential-decay formula for the probability density under amplitude
decay `R(t) = R₀ · exp(−γ·t/2)`. -/
theorem madelungDensityDecay_eq (R₀ γ t : ℝ) :
    madelungDensityDecay R₀ γ t = R₀ ^ 2 * Real.exp (-γ * t) := by
  unfold madelungDensityDecay madelungAmplitudeDecay
  rw [mul_pow]
  congr 1
  rw [show (Real.exp (-γ * t / 2)) ^ 2 = Real.exp (-γ * t / 2 + -γ * t / 2) by
    rw [Real.exp_add]; ring]
  congr 1; ring

/-- **Madelung density is non-negative**: `R₀² · exp(−γ·t) ≥ 0`. -/
theorem madelungDensityDecay_nonneg (R₀ γ t : ℝ) :
    0 ≤ madelungDensityDecay R₀ γ t := by
  unfold madelungDensityDecay
  positivity

/-- **Madelung-Sergi bridge (normalised case `R₀ = 1`)**: the Madelung
density `|ψ(t)|² = exp(−γ·t)` matches exactly Sergi's `traceOmega(t)`
for a constant-decay system with `γ₀ = γ`. -/
theorem madelungDensityDecay_eq_sergi_traceOmega
    (S : SergiConstantDecaySystem) (t : ℝ) :
    madelungDensityDecay 1 S.γ₀ t = S.traceOmega t := by
  rw [madelungDensityDecay_eq]
  unfold SergiConstantDecaySystem.traceOmega
  rw [one_pow, one_mul]

/-- **Bridge constructor: Madelung amplitude-decay → Sergi constant-decay system.**

Given the Madelung amplitude-decay rate `γ ≥ 0`, ℏ > 0, k_B > 0, and an
initial von Neumann entropy `S_vN_initial`, build the corresponding
`SergiConstantDecaySystem` with `γ₀ := γ`.

The classical-fluid `|ψ(t)|² = exp(−γ·t)` density and the quantum
`traceOmega(t) = exp(−γ₀·t)` are then the same function — the fluid
density-decay rate IS the Sergi `γ₀`. -/
noncomputable def SergiConstantDecaySystem.ofMadelungAmplitudeDecay
    (ℏ : ℝ) (ℏ_pos : 0 < ℏ) (k_B : ℝ) (k_B_pos : 0 < k_B)
    (γ : ℝ) (γ_nonneg : 0 ≤ γ) (S_vN_initial : ℝ) :
    SergiConstantDecaySystem where
  ℏ := ℏ
  ℏ_pos := ℏ_pos
  k_B := k_B
  k_B_pos := k_B_pos
  γ₀ := γ
  γ₀_nonneg := γ_nonneg
  S_vN_initial := S_vN_initial

/-- The Sergi system built from a Madelung amplitude decay has the
expected `γ₀ = γ`. -/
@[simp]
theorem SergiConstantDecaySystem.ofMadelungAmplitudeDecay_γ₀
    (ℏ : ℝ) (ℏ_pos : 0 < ℏ) (k_B : ℝ) (k_B_pos : 0 < k_B)
    (γ : ℝ) (γ_nonneg : 0 ≤ γ) (S_vN_initial : ℝ) :
    (SergiConstantDecaySystem.ofMadelungAmplitudeDecay
        ℏ ℏ_pos k_B k_B_pos γ γ_nonneg S_vN_initial).γ₀ = γ := rfl

/-- **Round-trip equality**: feeding a Madelung amplitude-decay rate
into the Sergi bridge and computing `traceOmega` gives back the
Madelung density `|ψ(t)|² = exp(−γ·t)` (normalised case `R₀ = 1`). -/
theorem ofMadelungAmplitudeDecay_traceOmega_eq_madelungDensity
    (ℏ : ℝ) (ℏ_pos : 0 < ℏ) (k_B : ℝ) (k_B_pos : 0 < k_B)
    (γ : ℝ) (γ_nonneg : 0 ≤ γ) (S_vN_initial t : ℝ) :
    (SergiConstantDecaySystem.ofMadelungAmplitudeDecay
        ℏ ℏ_pos k_B k_B_pos γ γ_nonneg S_vN_initial).traceOmega t
      = madelungDensityDecay 1 γ t :=
  (madelungDensityDecay_eq_sergi_traceOmega _ t).symm

/-! ## Phase I — Sergi generator as a Liouville-space matrix method

The direct finite-type Liouville structure and its zero-trajectory existence
theorem live in `Physlib.QuantumMechanics.Liouville.Schrodinger`. This section
only connects the Sergi normalised density-matrix equation (Eq. 8 of
Sergi-Giaquinta 2016) to that shared Liouville infrastructure.

Sources: Breuer & Petruccione, *The Theory of Open Quantum Systems*
(Oxford University Press 2002, doi:10.1093/acprof:oso/9780199213900.001.0001),
§3.2 (Liouville space); Sergi & Giaquinta, Entropy **18**, 451 (2016),
doi:10.3390/e18120451, Eq. (8).  Re-derived self-contained here.  No new axioms.
-/

open Physlib.QuantumMechanics.Liouville.Schrodinger

/-- **Bridge: Sergi normalised generator → Liouville-space generator**.
The Sergi normalised superoperator (Sergi Eq. 8 RHS) is a linear map
on `Matrix d d ℂ ≃ MatrixLiouvilleKet d`. This bundles it as a
time-independent Liouville-space generator. -/
noncomputable def sergiLiouvilleGenerator
    {d : Type*} [Fintype d] [DecidableEq d]
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) :
    ℝ → MatrixLiouvilleKet d → MatrixLiouvilleKet d :=
  fun _ ρ => sergiNormalisedGeneratorMatrix H_R H_I ℏ ρ

/-- **Existence of a Liouville-space trajectory for the Sergi
normalised superoperator** — the zero trajectory is a (trivial)
solution. -/
theorem exists_liouville_trajectory_sergi
    {d : Type*} [Fintype d] [DecidableEq d]
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) :
    ∃ traj : MatrixLiouvilleTrajectory d,
      matrixLiouvilleSchrodinger (sergiLiouvilleGenerator H_R H_I ℏ) traj := by
  apply exists_matrix_liouville_trajectory
  intro _
  show sergiNormalisedGeneratorMatrix H_R H_I ℏ 0 = 0
  unfold sergiNormalisedGeneratorMatrix sergiGeneratorMatrix
  simp [QuantumMechanics.FiniteTarget.commutator, QuantumMechanics.FiniteTarget.anticommutator]

end Physlib.Thermodynamics.SecondLaw

end

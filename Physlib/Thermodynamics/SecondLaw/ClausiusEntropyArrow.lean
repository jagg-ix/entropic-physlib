/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.EntropyProductionWorldline
public import Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger
public import Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations
public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # SecondLaw — part `ClausiusEntropyArrow`. Full docstring in the umbrella module `Physlib.Thermodynamics.SecondLaw`;
namespace and declaration names are unchanged (the umbrella re-exports them). -/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QFT.Wick.Consistency

namespace Physlib.Thermodynamics.SecondLaw

open QuantumInfo.Finite QuantumMechanics.FiniteTarget

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §1 — Second law: Clausius / Boltzmann entropy -/

/-- **Boltzmann/Clausius entropy** at temperature `T` relative to reference `T₀`
with Boltzmann constant `k_B`: `S(T) = k_B · log(T/T₀)`. -/
def clausiusEntropy (k_B T T₀ : ℝ) : ℝ := k_B * Real.log (T / T₀)

/-- The Clausius entropy vanishes at the reference temperature. -/
theorem clausiusEntropy_at_reference (k_B T₀ : ℝ) (hT₀ : 0 < T₀) :
    clausiusEntropy k_B T₀ T₀ = 0 := by
  unfold clausiusEntropy
  rw [div_self (ne_of_gt hT₀), Real.log_one, mul_zero]

/-- **Second law (canonical form)**: the Clausius entropy is monotone increasing
in temperature for `k_B > 0`, `T₀ > 0`. -/
theorem clausiusEntropy_monotone (k_B T₀ : ℝ) (hk : 0 < k_B) (hT₀ : 0 < T₀)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (h : T₁ ≤ T₂) :
    clausiusEntropy k_B T₁ T₀ ≤ clausiusEntropy k_B T₂ T₀ := by
  unfold clausiusEntropy
  gcongr

/-- The Clausius entropy is strictly positive above the reference temperature. -/
theorem clausiusEntropy_pos_above_reference (k_B T₀ T : ℝ)
    (hk : 0 < k_B) (hT₀ : 0 < T₀) (h : T₀ < T) :
    0 < clausiusEntropy k_B T T₀ := by
  unfold clausiusEntropy
  exact mul_pos hk (Real.log_pos ((one_lt_div hT₀).mpr h))

/-! ## §2 — The entropic-time arrow as a derived quantity -/

/-- **Entropy-increase worldline structure** (Paper 2 §5). The imaginary action
`S_I_along` is primary, with a monotonicity assumption (the operationalised
second law); the entropic proper time `τ_ent_along := S_I_along/ℏ` is derived. -/
structure EntropyArrowWorldline where
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ
  /-- Imaginary action / entropy production along the worldline. -/
  S_I_along : ℝ → ℝ
  /-- Derived entropic proper time. -/
  τ_ent_along : ℝ → ℝ
  /-- Defining identity `τ_ent(t) = S_I(t)/ℏ`: time is *defined from* entropy. -/
  τ_ent_eq : ∀ t, τ_ent_along t = S_I_along t / ℏ
  /-- **Load-bearing assumption (second law)**: entropy production is monotone
      non-decreasing along the worldline. -/
  S_I_monotone : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ → S_I_along t₁ ≤ S_I_along t₂
  /-- Initial imaginary action is non-negative. -/
  S_I_at_zero_nonneg : 0 ≤ S_I_along 0

namespace EntropyArrowWorldline

variable (W : EntropyArrowWorldline)

/-- Forgetful map to the generic QuantumInfo entropy-production worldline structure. -/
def toEntropyProductionWorldline (W : EntropyArrowWorldline) :
    QuantumInfo.Finite.EntropyProductionWorldline where
  S_I := W.S_I_along
  hbar := W.ℏ
  hbar_pos := W.ℏ_pos
  S_I_monotone := fun _ _ h => W.S_I_monotone h

/-- The generic QuantumInfo entropic proper time is the `SecondLaw` clock. -/
theorem toEntropyProductionWorldline_entropicProperTime (t : ℝ) :
    W.toEntropyProductionWorldline.entropicProperTime t = W.τ_ent_along t := by
  rw [W.τ_ent_eq]
  rfl

/-- **Entropic-time arrow (derived)**: `τ_ent` is monotone non-decreasing — a
consequence of entropy increase, not an independent postulate.

Does not prove: discreteness of `τ_ent`; minimum positive step;
uniqueness as a clock. The same conclusion holds for the boring
linear model `S_I(t) := ℏ·t`, which gives `τ_ent = t`.
-/
theorem tau_ent_monotone {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    W.τ_ent_along t₁ ≤ W.τ_ent_along t₂ := by
  rw [← W.toEntropyProductionWorldline_entropicProperTime t₁,
    ← W.toEntropyProductionWorldline_entropicProperTime t₂]
  exact W.toEntropyProductionWorldline.entropicProperTime_monotone h

/-- Strict arrow: strict entropy increase ⇒ strict time increase. -/
theorem tau_ent_strict_when_S_I_strict {t₁ t₂ : ℝ}
    (h : W.S_I_along t₁ < W.S_I_along t₂) :
    W.τ_ent_along t₁ < W.τ_ent_along t₂ := by
  rw [W.τ_ent_eq, W.τ_ent_eq]
  exact (div_lt_div_iff_of_pos_right W.ℏ_pos).mpr h

/-- **The crux of "side effect, not cause"**: the time order is *exactly* the
entropy order. `τ_ent` adds no ordering information of its own — it is a strictly
monotone readout of `S_I`. -/
theorem time_order_iff_entropy_order {t₁ t₂ : ℝ} :
    W.τ_ent_along t₁ ≤ W.τ_ent_along t₂ ↔ W.S_I_along t₁ ≤ W.S_I_along t₂ := by
  rw [← W.toEntropyProductionWorldline_entropicProperTime t₁,
    ← W.toEntropyProductionWorldline_entropicProperTime t₂]
  exact W.toEntropyProductionWorldline.entropicProperTime_le_iff t₁ t₂

/-- The entropic clock never falls below its initial reading. -/
theorem tau_ent_nonneg_along_worldline {t : ℝ} (h : 0 ≤ t) :
    0 ≤ W.τ_ent_along t := by
  rw [← W.toEntropyProductionWorldline_entropicProperTime t]
  exact W.toEntropyProductionWorldline.entropicProperTime_nonneg_of_S_I_nonneg t
    (le_trans W.S_I_at_zero_nonneg (W.S_I_monotone h))

/-- Extraction at the origin. -/
theorem entropy_arrow_at_zero : W.τ_ent_along 0 = W.S_I_along 0 / W.ℏ :=
  W.τ_ent_eq 0

/-- If entropy production vanishes identically, the entropic clock is frozen at
zero — no entropy increase, no time. -/
theorem worldline_S_I_zero_implies_tau_ent_zero
    (h : ∀ t, W.S_I_along t = 0) : ∀ t, W.τ_ent_along t = 0 := by
  intro t; rw [W.τ_ent_eq, h]; simp

/-- The entropic-time increment between two parameters is non-negative. -/
theorem tau_ent_delta_nonneg {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    0 ≤ W.τ_ent_along t₂ - W.τ_ent_along t₁ := by
  have := W.tau_ent_monotone h; linarith

/-! ### Reversible processes — the frozen-LRF counterpart -/

/-- **Definition of a reversible process.** An `EntropyArrowWorldline` describes
a *reversible* process when its entropy production `S_I_along` is constant —
equivalently, no net entropy is produced between any two parameter values. This
is the entropic-side definition that matches the thermodynamic notion of
"reversible". -/
def IsReversible (W : EntropyArrowWorldline) : Prop :=
  ∀ t₁ t₂ : ℝ, W.S_I_along t₁ = W.S_I_along t₂

/-- **Reversibility ⇔ frozen entropy production (C3).** A worldline is reversible
iff its derived entropic time is identically constant. This is the load-bearing
*equivalence* between two perspectives on a "reversible" process:

* thermodynamic: no net entropy is produced;
* temporal:    the entropic clock is frozen.

In particular it specialises the inverted-ProperTime thesis: at zero entropy
production, the entropic-time layer has no temporal content, so all of
"proper time" reduces to its geometric (Minkowski) residue. -/
theorem isReversible_iff_tau_ent_constant :
    W.IsReversible ↔ (∀ t₁ t₂ : ℝ, W.τ_ent_along t₁ = W.τ_ent_along t₂) := by
  unfold IsReversible
  constructor
  · intro hS t₁ t₂
    rw [W.τ_ent_eq, W.τ_ent_eq, hS t₁ t₂]
  · intro hτ t₁ t₂
    have := hτ t₁ t₂
    rw [W.τ_ent_eq, W.τ_ent_eq, div_left_inj' (ne_of_gt W.ℏ_pos)] at this
    exact this

/-- **Clausius equality (B1) — reversible processes have zero entropic-time gap.**
Along a reversible worldline (constant `S_I`), the derived entropic-time gap
between any two parameter values is zero — the "frozen-LRF residue" form of the
Clausius equality `dS_rev = dQ_rev / T = 0` (no entropy change ⇒ no heat flow
divided by T). -/
theorem clausius_equality_at_frozen (hrev : W.IsReversible) {t₁ t₂ : ℝ} :
    W.τ_ent_along t₂ - W.τ_ent_along t₁ = 0 := by
  have : W.τ_ent_along t₁ = W.τ_ent_along t₂ :=
    (W.isReversible_iff_tau_ent_constant.mp hrev) t₁ t₂
  linarith

/-- **Clausius inequality (B2) — irreversible processes have non-negative
entropic-time gap.** This is the *general* form of the second law on the
worldline structure: the entropic-time increment is non-negative on every forward
interval, with equality iff the process is reversible. -/
theorem clausius_inequality_irreversible {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    0 ≤ W.τ_ent_along t₂ - W.τ_ent_along t₁ :=
  W.tau_ent_delta_nonneg h

/-- **Equality case of the Clausius inequality.** The entropic-time increment
between two parameters vanishes iff the entropy production is equal at both —
the operational definition of "reversible on this interval". -/
theorem clausius_inequality_eq_iff_locally_reversible {t₁ t₂ : ℝ} :
    W.τ_ent_along t₂ - W.τ_ent_along t₁ = 0
      ↔ W.S_I_along t₁ = W.S_I_along t₂ := by
  rw [W.τ_ent_eq, W.τ_ent_eq, sub_eq_zero, div_left_inj' (ne_of_gt W.ℏ_pos)]
  exact ⟨Eq.symm, Eq.symm⟩

end EntropyArrowWorldline

/-! ### Global second law — sum over a finite ensemble of worldlines -/

/-- **Global entropy production** at parameter `t`: the sum of
`S_I_along t` over a finite ensemble of `EntropyArrowWorldline`s.
This is the universe-scale aggregate of imaginary action. -/
def globalEntropyProduction (Ws : List EntropyArrowWorldline) (t : ℝ) : ℝ :=
  (Ws.map (fun W => W.S_I_along t)).sum

/-- **B6 — Global second law.** The aggregate entropy production over
*any* finite ensemble of `EntropyArrowWorldline`s is monotone
non-decreasing in the worldline parameter.  This is the universal
`dS_universe/dt ≥ 0` statement.

The proof composes the per-worldline `S_I_monotone` field across the
sum — there is no extra postulate; the global second law is the
sum-of-locals on the worldline structure. -/
theorem globalEntropyProduction_monotone (Ws : List EntropyArrowWorldline)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    globalEntropyProduction Ws t₁ ≤ globalEntropyProduction Ws t₂ := by
  unfold globalEntropyProduction
  induction Ws with
  | nil => simp
  | cons W rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (W.S_I_monotone h) ih

/-- The empty ensemble produces zero entropy at every parameter. -/
@[simp] theorem globalEntropyProduction_nil (t : ℝ) :
    globalEntropyProduction [] t = 0 := by
  simp [globalEntropyProduction]

/-- The global entropy production of a single worldline equals its
own `S_I_along`. -/
@[simp] theorem globalEntropyProduction_singleton
    (W : EntropyArrowWorldline) (t : ℝ) :
    globalEntropyProduction [W] t = W.S_I_along t := by
  simp [globalEntropyProduction]

/-- The change in global entropy production over a forward interval
is non-negative — the integrated form of B6. -/
theorem globalEntropyProduction_delta_nonneg
    (Ws : List EntropyArrowWorldline) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    0 ≤ globalEntropyProduction Ws t₂ - globalEntropyProduction Ws t₁ := by
  have := globalEntropyProduction_monotone Ws h
  linarith


end Physlib.Thermodynamics.SecondLaw

end

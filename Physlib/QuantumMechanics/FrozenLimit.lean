/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.Relativity.Special.ProperTime
public import Physlib.SpaceAndTime.ProblemOfTimeInstance
public import Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger
public import Physlib.QuantumMechanics.GravitationalDecoherenceRedshift

/-!
# Entropic-time frozen limit: recovery of standard physics

The integrated entropic-time bridge theorem. A `FrozenContext` packages the frozen
data (diagonal state `ρ`, units `U`, lapse `L`, entropy-controlled system `S`
with `H_I = 0`). At this frozen limit the `FrozenRecovery` record collects the
independent consequences across quantum information, the dimensional time lift,
relativity, non-Hermitian QM, and the lapse/Tolman layer:

* entropic and metric-entropic times vanish on the diagonal;
* total / complex proper time reduce to the geometric Lorentz proper time;
* the complex Hamiltonian reduces to the reversible generator, with zero entropy
  production and zero norm decay;
* local entropic time vanishes and obeys its Tolman law; decoherence obeys its
  Tolman law.

Also: a unit-lapse specialization, the frozen-origin representation witness, the
geometric ≤ total contrast, and the finite-transition identity
`τ_metric = scale · entropyRate · Δt`.

No new axioms — every field is a component reduction lemma.

## References

- **Pauli 1933** — *Die allgemeinen Prinzipien der Wellenmechanik*
- **Kuchař 1992** — *Time and interpretations of quantum gravity*
- **Isham 1993** — *Canonical quantum gravity and the problem of time*
-/

set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section


namespace Physlib.QuantumMechanics.FrozenLimit

open _root_.QuantumInfo.Finite _root_.QuantumMechanics _root_.QuantumMechanics.FiniteTarget
open Physlib.SpaceTime
open Physlib.SpaceAndTime

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {sd : ℕ}

/-- **Frozen entropic-time context**: the data needed to state the standard-physics
recovery theorem — a diagonal state `ρ`, unit data `U`, a lapse `L`, an
entropy-controlled non-Hermitian system `S`, and the frozen condition
`H_I = 0`. -/
structure FrozenContext where
  /-- Unit data (ℏ, k_B, T_∞). -/
  U : EntropicTimeUnits
  /-- Diagonal state. -/
  ρ : MState d
  /-- The lapse. -/
  L : Lapse sd
  /-- The entropy-controlled non-Hermitian Schrödinger system. -/
  S : EntropyControlledSchrodingerSystem (H := H)
  /-- The frozen condition: vanishing irreversible generator. -/
  H_I_zero : S.H_I = 0

/-- The conclusions recovered in the frozen entropic-time limit (each field a concrete
reduction theorem, not a slogan). -/
structure FrozenRecovery
    (C : FrozenContext (H := H) (d := d) (sd := sd))
    (q p : SpaceTime sd) (ψ : H) (x : SpaceTime sd) (Γ_inf : ℝ) : Prop where
  /-- Relative-entropy diagonal vanishes. -/
  entropic_zero : entropicProperTime C.ρ C.ρ = 0
  /-- Dimensionally scaled entropic time vanishes. -/
  metric_entropic_zero : entropicProperTimeMetric C.U C.ρ C.ρ = 0
  /-- Total proper time reduces to geometric Lorentz proper time. -/
  total_time_recovers_geometric :
    totalProperTimeMetric C.U q p C.ρ C.ρ = SpaceTime.properTime q p
  /-- Complex proper time reduces to real geometric proper time. -/
  complex_time_recovers_geometric :
    complexProperTimeMetric C.U q p C.ρ C.ρ = (SpaceTime.properTime q p : ℂ)
  /-- Complex Hamiltonian reduces to the reversible generator. -/
  generator_recovers_reversible : C.S.H_C = C.S.H_R
  /-- Entropy-production rate vanishes. -/
  entropyRate_zero : C.S.entropyRate ψ = 0
  /-- Norm-squared decay rate vanishes. -/
  normDecayRate_zero : C.S.normDecayRate ψ = 0
  /-- Local entropic proper time vanishes under any positive lapse. -/
  local_entropic_zero : entropicProperTimeLocalMetric C.U C.L C.ρ C.ρ x = 0
  /-- Local entropic time satisfies its Tolman law. -/
  local_entropic_tolman :
    entropicProperTimeLocalMetric C.U C.L C.ρ C.ρ x * C.L.N x =
      entropicProperTimeMetric C.U C.ρ C.ρ
  /-- Decoherence rate satisfies its assumed Tolman law. -/
  decoherence_tolman : decoherenceRateLocal Γ_inf C.L x * C.L.N x = Γ_inf

/-- **Frozen-limit recovery theorem**: at zero relative entropy and zero
irreversible generator, the entropic-time framework collapses to ordinary geometric proper time and
ordinary reversible quantum evolution. -/
theorem frozen_limit_recovers_standard_physics
    (C : FrozenContext (H := H) (d := d) (sd := sd))
    (q p : SpaceTime sd) (ψ : H) (x : SpaceTime sd) (Γ_inf : ℝ) :
    FrozenRecovery C q p ψ x Γ_inf where
  entropic_zero := entropicProperTime_self C.ρ
  metric_entropic_zero := entropicProperTimeMetric_self C.U C.ρ
  total_time_recovers_geometric := totalProperTimeMetric_at_frozen C.U q p C.ρ
  complex_time_recovers_geometric := complexProperTimeMetric_at_frozen C.U q p C.ρ
  generator_recovers_reversible := C.S.zero_HI_implies_unitary_generator C.H_I_zero
  entropyRate_zero := C.S.zero_HI_implies_zero_entropyRate C.H_I_zero ψ
  normDecayRate_zero := (C.S.zero_HI_frozen_reduction C.H_I_zero ψ).2.2
  local_entropic_zero := entropicProperTimeLocalMetric_self C.U C.L C.ρ x
  local_entropic_tolman := entropicProperTimeLocalMetric_satisfies_tolman C.U C.L C.ρ C.ρ x
  decoherence_tolman := decoherenceRate_tolman_invariant Γ_inf C.L x

/-- **Unit-lapse (Minkowski) frozen limit**: the recovery holds at the flat
lapse `N ≡ 1`. -/
theorem frozen_limit_unit_lapse
    (U : EntropicTimeUnits) (ρ : MState d)
    (S : EntropyControlledSchrodingerSystem (H := H)) (hzero : S.H_I = 0)
    (q p : SpaceTime sd) (ψ : H) (x : SpaceTime sd) (Γ_inf : ℝ) :
    FrozenRecovery
      ({ U := U, ρ := ρ, L := Lapse.unit (d := sd), S := S, H_I_zero := hzero } :
        FrozenContext (H := H) (d := d) (sd := sd)) q p ψ x Γ_inf :=
  frozen_limit_recovers_standard_physics _ q p ψ x Γ_inf

/-- **SR ⇒ TDSE ⇒ TISE chain bridge at the Frozen-LRF.**  Given a frozen
context `C` and a vector `ψ` that is an eigenvector of the reversible
generator `H_R` with eigenvalue `E`, the full chain reduces consistently:

* **(SR side)** `totalProperTimeMetric U q p ρ ρ = SpaceTime.properTime q p`
  — at the frozen LRF the entropic contribution to total proper time
  vanishes and the bare Minkowski/SR proper time is recovered.
* **(TDSE side)** the complex (non-Hermitian) generator collapses to the
  reversible Hermitian generator: `H_C = H_R`, with vanishing
  entropy-production rate.
* **(TISE side)** the same `ψ` is an eigenvector of `H_C` with the
  *same* eigenvalue `E`, i.e. `H_C ψ = E • ψ` — the **TISE eigenvalue
  equation is recovered from the TDSE complex generator** at the frozen
  limit, with the SR proper time as the geometric residue of total
  proper time.

This is the integrated `Special-Relativity ↔ TDSE ↔ TISE` reduction step
of the entropic-time chain, in its frozen-limit form.  No new axioms; it
composes the `H_I = 0` reduction theorems of `EntropyControlledSchrodingerSystem`
with `totalProperTimeMetric_at_frozen`. -/
theorem tise_recovered_at_frozen_limit
    (C : FrozenContext (H := H) (d := d) (sd := sd))
    (q p : SpaceTime sd) (ψ : H) (E : ℂ)
    (hψ : C.S.H_R ψ = E • ψ) :
    totalProperTimeMetric C.U q p C.ρ C.ρ = SpaceTime.properTime q p
    ∧ C.S.H_C = C.S.H_R
    ∧ C.S.entropyRate ψ = 0
    ∧ C.S.H_C ψ = E • ψ := by
  refine ⟨totalProperTimeMetric_at_frozen C.U q p C.ρ,
          C.S.zero_HI_implies_unitary_generator C.H_I_zero,
          C.S.zero_HI_implies_zero_entropyRate C.H_I_zero ψ, ?_⟩
  rw [C.S.zero_HI_implies_unitary_generator C.H_I_zero, hψ]

/-- **Frozen context represents the metric-time origin**: links the frozen
recovery to the witness-based problem-of-time layer. -/
def frozen_context_represents_time_origin
    (C : FrozenContext (H := H) (d := d) (sd := sd)) :
    EntropicTimeRepresentation (d := d) (⟨0⟩ : Time) :=
  frozenOriginRepresentation C.U C.ρ

/-- **Geometric ≤ total**: the (unsigned) entropic contribution never decreases
the total proper time. -/
theorem totalProperTimeMetric_geometric_le_total
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ σ : MState d) :
    SpaceTime.properTime q p ≤ totalProperTimeMetric U q p ρ σ := by
  unfold totalProperTimeMetric
  have hnonneg : 0 ≤ entropicProperTimeMetric U ρ σ :=
    entropicProperTimeMetric_nonneg U ρ σ
  linarith

/-- **Finite-transition identity**: the dimensionally scaled entropic time
interval equals `unit scale · entropy-production rate · elapsed external time`. -/
theorem finite_transition_metric_time_eq_scaled_rate_time
    {S : EntropyControlledSchrodingerSystem (H := H)}
    (U : EntropicTimeUnits) (T : EntropicTransition (d := d) S) :
    entropicProperTimeMetric U T.ρ₁ T.ρ₀ =
      U.scale * (S.entropyRate T.ψ * T.Δt) := by
  unfold entropicProperTimeMetric entropicGap
  rw [T.rate_relation]

end Physlib.QuantumMechanics.FrozenLimit

end

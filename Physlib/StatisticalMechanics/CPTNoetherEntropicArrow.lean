/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Lindblad.GreensFunction

/-!
# The entropic arrow as the obstruction to CPT symmetry, Noether conservation, and geometric time

This module links the geometric/entropic arrow built in the chain to two classical
physics laws, by **proof by contradiction**: strict entropy production is shown to
be incompatible with each of

* **Noether conservation** — norm/probability conservation is the conserved charge
 of the unitary (time-translation) symmetry; `normDecayRate = 0`;
* **CPT / time-reversal symmetry** — the reversible, Hermitian sector `H_I = 0`
 (`H_C = H_R`) is the time-reversal-invariant limit;
* **purely geometric proper time** — the complex proper time
 `S = τ_geom + i τ_ent` is real (its imaginary, entropic part vanishes).

Each link is a genuine `¬ (… ∧ …)` / `… ≠ 0` derived from the already-proven
facts `normDecayRate = −entropyRate` and `entropyRate_nonneg`
(`Physlib.QuantumMechanics.FiniteTarget`), and from `L†L ⪰ 0`
(`Physlib.QuantumMechanics.Lindblad.GreensFunction`). The arrow of time is thus the single
structural obstruction to all three; a genuine Lindblad jump (`L ψ ≠ 0`) triggers
it (`lindblad_jump_breaks_reversibility`, `lindblad_jump_breaks_conservation`).

## Scope

This does not re-derive the CPT theorem or Noether's theorem from scratch. It
formalises, at the operator level, the *direction* relevant here:
**time-reversal symmetry (Hermiticity, `H_I = 0`) ⟹ conservation (Noether charge
constant) ⟹ no entropy production ⟹ geometric proper time**, and that strict
entropy production contradicts each. The continuous-symmetry origin of the
conservation law is the unitarity of the `H_I = 0` evolution
(`zero_HI_implies_unitary_generator`).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.QuantumMechanics.Lindblad.GreensFunction
open Physlib.Thermodynamics.SecondLaw
namespace Physlib.StatisticalMechanics.CPTNoetherEntropicArrow

open QuantumInfo.Finite QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §1 — Noether: norm conservation ⟺ no entropy production -/

/-- **Noether's symmetry ⟹ conservation.** Time-reversal symmetry of the generator
(`H_I = 0`, the unitary sector) makes the Noether charge — the norm/probability —
conserved: `normDecayRate = 0`. -/
theorem reversible_conserves (S : EntropyControlledSchrodingerSystem (H := H))
    (ψ : H) (hrev : S.H_I = 0) : S.normDecayRate ψ = 0 := by
  rw [S.normDecayRate_eq_neg_entropyRate ψ, S.zero_HI_implies_zero_entropyRate hrev ψ]; ring

/-- **Proof by contradiction**: the Noether charge cannot be conserved while
entropy is strictly produced. -/
theorem conservation_excludes_production
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) :
    ¬ (S.normDecayRate ψ = 0 ∧ 0 < S.entropyRate ψ) := by
  rintro ⟨hcons, hprod⟩
  rw [S.normDecayRate_eq_neg_entropyRate ψ] at hcons
  linarith

/-- Conserved Noether charge ⟹ no entropy production. -/
theorem conservation_implies_no_production
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H)
    (hcons : S.normDecayRate ψ = 0) : S.entropyRate ψ = 0 := by
  rw [S.normDecayRate_eq_neg_entropyRate ψ] at hcons; linarith

/-- Strict entropy production ⟹ the Noether charge is **not** conserved. -/
theorem production_breaks_conservation
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H)
    (hprod : 0 < S.entropyRate ψ) : S.normDecayRate ψ ≠ 0 := by
  rw [S.normDecayRate_eq_neg_entropyRate ψ]; intro h; linarith

/-! ## §2 — CPT / time reversal: reversibility ⟺ no entropy production -/

/-- **Proof by contradiction**: strict entropy production forces a non-vanishing
irreversible generator — the dynamics cannot lie in the time-reversal/CPT-symmetric
(Hermitian) sector `H_I = 0`. -/
theorem irreversibility_of_production
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H)
    (hprod : 0 < S.entropyRate ψ) : S.H_I ≠ 0 := by
  intro hzero
  have := S.zero_HI_implies_zero_entropyRate hzero ψ
  linarith

/-- The time-reversal/CPT-symmetric sector (`H_I = 0`) has zero entropy production
and unitary (norm-preserving) evolution `H_C = H_R`. -/
theorem reversible_no_production_unitary
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) (hrev : S.H_I = 0) :
    S.entropyRate ψ = 0 ∧ S.H_C = S.H_R :=
  ⟨S.zero_HI_implies_zero_entropyRate hrev ψ, S.zero_HI_implies_unitary_generator hrev⟩

/-! ## §3 — Geometry: purely geometric proper time ⟺ no entropic gap -/

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
/-- **Proof by contradiction (geometry).** Over a finite transition with elapsed
time `Δt > 0`, the complex proper time cannot be purely geometric (zero entropic
gap `D(ρ₁‖ρ₀) = 0`) while entropy is strictly produced: the entropic proper time
is `entropyRate · Δt`, which would then be both `0` and `> 0`. The imaginary part
of `complexProperTimeMetric` (the entropic proper time) is forced positive. -/
theorem geometric_proper_time_excludes_production
    (S : EntropyControlledSchrodingerSystem (H := H)) (E : EntropicTransition (d := d) S)
    (hΔt : 0 < E.Δt) :
    ¬ ((entropicProperTime E.ρ₁ E.ρ₀).toReal = 0 ∧ 0 < S.entropyRate E.ψ) := by
  rintro ⟨hgeom, hprod⟩
  rw [E.rate_relation] at hgeom
  have hpos : 0 < S.entropyRate E.ψ * E.Δt := mul_pos hprod hΔt
  rw [hgeom] at hpos
  exact lt_irrefl 0 hpos

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
/-- Purely geometric proper time (zero entropic gap) over `Δt > 0` ⟹ no entropy
production: the geometric (real) Lorentzian clock cannot host irreversibility. -/
theorem geometric_proper_time_implies_no_production
    (S : EntropyControlledSchrodingerSystem (H := H)) (E : EntropicTransition (d := d) S)
    (hΔt : 0 < E.Δt) (hgeom : (entropicProperTime E.ρ₁ E.ρ₀).toReal = 0) :
    S.entropyRate E.ψ = 0 := by
  rw [E.rate_relation] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right (ne_of_gt hΔt)

/-! ## §4 — A Lindblad jump triggers the arrow and breaks all three -/

/-- A genuine jump (`L ψ ≠ 0`) produces strict entropy at the Lindblad rate. -/
theorem lindblad_jump_produces_entropy
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) (hL : L ψ ≠ 0) :
    0 < (positiveGeneratorSystem H_R (lindbladDissipator L) hbar hbar_pos
        (lindbladDissipator_isPositive L)).entropyRate ψ := by
  rw [lindblad_greenKernel_rate_eq_entropyRate]
  refine mul_pos (by positivity) ?_
  rw [lindbladRate_eq_normSq]
  exact pow_pos (norm_pos_iff.mpr hL) 2

/-- **A Lindblad jump breaks CPT/time-reversal symmetry.** The dissipator `L†L`
cannot vanish when the jump acts (`L ψ ≠ 0`). -/
theorem lindblad_jump_breaks_reversibility
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) (hL : L ψ ≠ 0) :
    lindbladDissipator L ≠ 0 :=
  irreversibility_of_production _ ψ (lindblad_jump_produces_entropy H_R L hbar hbar_pos ψ hL)

/-- **A Lindblad jump breaks Noether conservation.** The norm/probability is not
conserved when the jump acts. -/
theorem lindblad_jump_breaks_conservation
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) (hL : L ψ ≠ 0) :
    (positiveGeneratorSystem H_R (lindbladDissipator L) hbar hbar_pos
        (lindbladDissipator_isPositive L)).normDecayRate ψ ≠ 0 :=
  production_breaks_conservation _ ψ (lindblad_jump_produces_entropy H_R L hbar hbar_pos ψ hL)

end Physlib.StatisticalMechanics.CPTNoetherEntropicArrow

end

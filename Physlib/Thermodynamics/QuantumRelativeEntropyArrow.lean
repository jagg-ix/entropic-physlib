/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import QuantumInfo.Entropy.EntropicProperTime
public import QuantumInfo.Entropy.DPI
public import QuantumInfo.Channels.CPTP

/-!
# Entropic-time arrow from a solved quantum orbit (not a postulated ramp)

`Physlib.Thermodynamics.SecondLaw` builds its entropy-time arrow from a
**postulated** linear ramp `S_I_along t := slope · t`. Nothing there solves an
equation of motion, so "frozen clock at `H_I = 0`" is true only by definition.
This module replaces the postulate with `S_I` read off an *actual* discrete
quantum orbit and proves the monotonicity from the data-processing inequality
(DPI) for the quantum relative entropy — turning a layer-2 assumption into a
layer-1 theorem.

An orbit is the iterate of one CPTP step (a Lindblad channel at a fixed
timestep is a CPTP map; iterating it *is* discrete time evolution). The
entropic proper time `entropicProperTime ρ σ = qRelativeEnt ρ σ` of the running
state `ρ(n)` against a reference `σ` is the clock. The behaviour depends on the
*pair* (dynamics, reference):

* **Dissipative dynamics, fixed-point reference** (`Φ σ = σ`):
  `n ↦ entropicProperTime (Φⁿ ρ₀) σ` is **antitone** — a genuine arrow toward
  equilibrium, by DPI. This is the quantum H-theorem, derived, not assumed.

* **Unitary dynamics, invariant reference** (`σ.U_conj U = σ`):
  `n ↦ entropicProperTime (Uⁿ ◃ ρ₀) σ` is **constant** — the clock is frozen,
  by unitary invariance of the relative entropy. Reversible evolution accrues
  *no* entropic time toward equilibrium.

* **Unitary dynamics, initial-state reference**: at a recurrence time
  (`Uᴺ ◃ ρ₀ = ρ₀`) the clock to `ρ₀` returns to `0`. The "distance to the
  initial state" is periodic, not a monotone arrow.

This is the precise, faithfulness-free form of the contrast flagged as
counterexample **C-A4** in `CLAIMS_AUDIT_ENTROPIC_TIME.md`: under reversible
dynamics the relative entropy to the initial state oscillates/returns while the
relative entropy to an invariant equilibrium is constant; only dissipation
gives a monotone clock.

## What this proves and does not prove

Proved: the three monotonicity/constancy/recurrence facts above, each reduced
to a single named QuantumInfo input (`sandwichedRenyiEntropy_DPI_eq_one`,
`sandwichedRenyiEntropy_conj_unitary`, `entropicProperTime_self`); and (§8) the
*non-monotonicity* of the reversible clock to its initial state, faithfulness-free.
When the running state's support is not contained in the reference's support the
relative entropy is `⊤` (the `else ⊤` branch of `SandwichedRelRentropy`), so a
reversible orbit visiting a state orthogonal to its start reads `⊤` there and `0`
at recurrence — neither `Monotone` nor `Antitone`. This is exhibited concretely on
a qubit (`qubitPingPong_clock_not_monotone`), with no faithfulness assumed.

Not proved: *strict positivity* in the support-**compatible** mid-orbit case
(`0 < qRelativeEnt ρ σ < ⊤` for `ρ ≠ σ` with matching supports). That needs a
general faithfulness lemma (`ρ ≠ σ → 0 < qRelativeEnt ρ σ`), still **not** in the
vendored QuantumInfo library — but it is no longer needed to break monotonicity.

## Origin

The relative-entropy DPI and unitary-invariance lemmas are from Meiburg's
`Lean-QuantumInfo` (vendored under `QuantumInfo/`). This module only assembles
them into the discrete-orbit statements; it adds no new quantum-information
infrastructure.
-/

set_option autoImplicit false

namespace Physlib.Thermodynamics.QuantumRelativeEntropyArrow

open QuantumInfo.Finite
open scoped ENNReal

@[expose] public section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-!

`entropicProperTime = qRelativeEnt = D̃_1`, so the sandwiched-Rényi DPI and
unitary-invariance lemmas specialise definitionally. -/

/-- **Data-processing for entropic proper time.** A CPTP step never increases
the entropic proper time of a state pair. (Meiburg `sandwichedRenyiEntropy_DPI_eq_one`
at `α = 1`.) -/
lemma entropicProperTime_DPI (Φ : CPTPMap d d) (ρ σ : MState d) :
    entropicProperTime (Φ ρ) (Φ σ) ≤ entropicProperTime ρ σ :=
  sandwichedRenyiEntropy_DPI_eq_one ρ σ Φ

/-- **Unitary invariance of entropic proper time.** Conjugating both arguments
by the same unitary leaves the entropic proper time unchanged. (Meiburg
`sandwichedRenyiEntropy_conj_unitary` at `α = 1`.) -/
lemma entropicProperTime_U_conj (U : Matrix.unitaryGroup d ℂ) (ρ σ : MState d) :
    entropicProperTime (ρ.U_conj U) (σ.U_conj U) = entropicProperTime ρ σ :=
  sandwichedRenyiEntropy_conj_unitary one_pos ρ σ U


/-- The discrete dissipative orbit: iterate the CPTP step `Φ` from `ρ₀`. -/
noncomputable def channelOrbit (Φ : CPTPMap d d) (ρ₀ : MState d) (n : ℕ) : MState d :=
  (fun ρ => Φ ρ)^[n] ρ₀

@[simp] lemma channelOrbit_zero (Φ : CPTPMap d d) (ρ₀ : MState d) :
    channelOrbit Φ ρ₀ 0 = ρ₀ := rfl

lemma channelOrbit_succ (Φ : CPTPMap d d) (ρ₀ : MState d) (n : ℕ) :
    channelOrbit Φ ρ₀ (n + 1) = Φ (channelOrbit Φ ρ₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- The discrete unitary orbit: iterate the conjugation `ρ ↦ U ◃ ρ` from `ρ₀`. -/
noncomputable def unitaryOrbit (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) (n : ℕ) : MState d :=
  (fun ρ => ρ.U_conj U)^[n] ρ₀

@[simp] lemma unitaryOrbit_zero (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) :
    unitaryOrbit U ρ₀ 0 = ρ₀ := rfl

lemma unitaryOrbit_succ (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) (n : ℕ) :
    unitaryOrbit U ρ₀ (n + 1) = (unitaryOrbit U ρ₀ n).U_conj U :=
  Function.iterate_succ_apply' _ _ _


/-- **One dissipative step contracts the clock.** If `σ` is a fixed point of the
channel, a single step cannot increase the entropic proper time to `σ`. -/
lemma dissipative_step_contracts (Φ : CPTPMap d d) (ρ σ : MState d) (hfix : Φ σ = σ) :
    entropicProperTime (Φ ρ) σ ≤ entropicProperTime ρ σ := by
  calc entropicProperTime (Φ ρ) σ
      = entropicProperTime (Φ ρ) (Φ σ) := by rw [hfix]
    _ ≤ entropicProperTime ρ σ := entropicProperTime_DPI Φ ρ σ

/-- **Step-wise monotonicity along the dissipative orbit.** -/
lemma dissipative_orbit_succ_le (Φ : CPTPMap d d) (ρ₀ σ : MState d) (hfix : Φ σ = σ)
    (n : ℕ) :
    entropicProperTime (channelOrbit Φ ρ₀ (n + 1)) σ
      ≤ entropicProperTime (channelOrbit Φ ρ₀ n) σ := by
  rw [channelOrbit_succ]
  exact dissipative_step_contracts Φ _ σ hfix

/-- **The quantum H-theorem, derived from DPI.** Along a dissipative orbit, the
entropic proper time to a fixed-point reference is antitone — a genuine arrow
toward equilibrium, with no postulated linear ramp. -/
lemma dissipative_orbit_antitone (Φ : CPTPMap d d) (ρ₀ σ : MState d) (hfix : Φ σ = σ) :
    Antitone (fun n => entropicProperTime (channelOrbit Φ ρ₀ n) σ) :=
  antitone_nat_of_succ_le (dissipative_orbit_succ_le Φ ρ₀ σ hfix)


/-- **Unitary evolution freezes the clock to an invariant reference.** If `σ` is
invariant under the conjugation, the entropic proper time of the unitary orbit
to `σ` is constant in `n` — reversible dynamics accrues no entropic time toward
equilibrium. -/
lemma unitary_orbit_const_to_invariant (U : Matrix.unitaryGroup d ℂ) (ρ₀ σ : MState d)
    (hinv : σ.U_conj U = σ) (n : ℕ) :
    entropicProperTime (unitaryOrbit U ρ₀ n) σ = entropicProperTime ρ₀ σ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [unitaryOrbit_succ]
    calc entropicProperTime ((unitaryOrbit U ρ₀ k).U_conj U) σ
        = entropicProperTime ((unitaryOrbit U ρ₀ k).U_conj U) (σ.U_conj U) := by rw [hinv]
      _ = entropicProperTime (unitaryOrbit U ρ₀ k) σ := entropicProperTime_U_conj U _ σ
      _ = entropicProperTime ρ₀ σ := ih


/-- **Recurrence: the clock to the initial state returns to zero.** At any
recurrence time `N` (where the orbit comes back to `ρ₀`) the entropic proper
time to `ρ₀` is `0`, as it is at `n = 0`. The distance-to-initial-state is
periodic, not a monotone arrow. -/
lemma unitary_orbit_recurs_to_init (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) {N : ℕ}
    (hper : unitaryOrbit U ρ₀ N = ρ₀) :
    entropicProperTime (unitaryOrbit U ρ₀ N) ρ₀ = 0 := by
  rw [hper, entropicProperTime_self]

/-- The clock to the initial state starts at `0`. -/
@[simp] lemma unitary_orbit_init_at_zero (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) :
    entropicProperTime (unitaryOrbit U ρ₀ 0) ρ₀ = 0 := by
  rw [unitaryOrbit_zero, entropicProperTime_self]

/-!

For one and the same reference `σ`: reversible (unitary) dynamics freezes the
entropic-time clock, while dissipative dynamics turns it into a monotone arrow.
This is the honest content the postulated linear ramp could not express. -/

/-- **Reversible ⇒ frozen clock, dissipative ⇒ monotone arrow**, against a
common reference `σ` that is both unitary-invariant and a channel fixed point. -/
lemma clock_frozen_under_reversible_arrow_under_dissipative
    (U : Matrix.unitaryGroup d ℂ) (Φ : CPTPMap d d) (ρ₀ σ : MState d)
    (hinv : σ.U_conj U = σ) (hfix : Φ σ = σ) :
    (∀ n, entropicProperTime (unitaryOrbit U ρ₀ n) σ = entropicProperTime ρ₀ σ)
      ∧ Antitone (fun n => entropicProperTime (channelOrbit Φ ρ₀ n) σ) :=
  ⟨fun n => unitary_orbit_const_to_invariant U ρ₀ σ hinv n,
    dissipative_orbit_antitone Φ ρ₀ σ hfix⟩

/-!

The dissipative witness is the physically meaningful one: the replacement
channel `Φ ρ = σ` resets to `σ` in a single step, so the clock to `σ` drops to
its floor `0` after one step — a real arrow, not the boring constant. The
unitary witness uses the identity conjugation, confirming the invariant-reference
hypothesis is satisfiable. -/

/-- The replacement channel `ρ ↦ σ` has `σ` as a fixed point. -/
lemma replacement_fixed [Nonempty d] (σ : MState d) :
    (CPTPMap.replacement σ : CPTPMap d d) σ = σ :=
  CPTPMap.replacement_apply σ σ

/-- **A real dissipative arrow.** Under the replacement channel, the clock to
`σ` reaches its floor `0` after one step, for any initial state. -/
lemma replacement_orbit_one_eq_zero [Nonempty d] (ρ₀ σ : MState d) :
    entropicProperTime (channelOrbit (CPTPMap.replacement σ) ρ₀ 1) σ = 0 := by
  rw [channelOrbit_succ, channelOrbit_zero, CPTPMap.replacement_apply, entropicProperTime_self]

/-- The replacement-channel orbit is a genuine (antitone) entropic-time clock. -/
lemma replacement_orbit_antitone [Nonempty d] (ρ₀ σ : MState d) :
    Antitone (fun n => entropicProperTime (channelOrbit (CPTPMap.replacement σ) ρ₀ n) σ) :=
  dissipative_orbit_antitone _ ρ₀ σ (replacement_fixed σ)

/-- The identity conjugation leaves any state invariant — the unitary-invariant
hypothesis is satisfiable. -/
lemma U_conj_one_self (ρ : MState d) : ρ.U_conj 1 = ρ := by
  apply MState.ext_m
  unfold MState.m MState.U_conj MState.uConj
  change (ρ.M.conj (1 : Matrix d d ℂ)).mat = ρ.M.mat
  exact congrArg HermitianMat.mat (HermitianMat.conj_one ρ.M)

/-!

§5 only gave "the clock to the initial state *returns to* `0`" — that refutes
*strict* monotonicity but not the stronger informal "reversible ⇒ no entropic
time elapsed". The missing piece was strict positivity in between, which in
general needs faithfulness (`ρ ≠ σ → 0 < qRelativeEnt ρ σ`) — absent from the
vendored library.

There is a faithfulness-free shortcut for the *support-incompatible* case. When
the running state's support is not contained in the reference's support
(`¬ σ.M.ker ≤ ρ.M.ker`), the relative entropy is not merely positive, it is
`⊤` — directly from the definition of `SandwichedRelRentropy` (its `else ⊤`
branch). Two distinct *pure* states are always support-incompatible, so a
reversible orbit that visits a pure state orthogonal to its starting point has a
clock reading of `⊤` there and `0` at the recurrence — visibly non-monotone, no
faithfulness required. -/

/-- **`⊤` from support incompatibility.** If the reference support is not
contained in the state's support, the relative entropy is `⊤`. This is the
`else ⊤` branch of `SandwichedRelRentropy` at `α = 1`, named. -/
lemma qRelativeEnt_eq_top_of_not_ker_le {ρ σ : MState d}
    (h : ¬ σ.M.ker ≤ ρ.M.ker) : qRelativeEnt ρ σ = ⊤ := by
  have hred : qRelativeEnt ρ σ = SandwichedRelRentropy 1 ρ σ := rfl
  rw [hred]
  unfold SandwichedRelRentropy
  rw [dif_pos one_pos, dif_neg h]

/-- The same, phrased for `entropicProperTime`. -/
lemma entropicProperTime_eq_top_of_not_ker_le {ρ σ : MState d}
    (h : ¬ σ.M.ker ≤ ρ.M.ker) : entropicProperTime ρ σ = ⊤ :=
  qRelativeEnt_eq_top_of_not_ker_le h

/-- A single `mulVec` witness `x` in `σ`'s kernel but not `ρ`'s certifies the
support incompatibility. -/
lemma not_ker_le_of_mulVec_witness {ρ σ : MState d} (x : EuclideanSpace ℂ d)
    (hσ : σ.M.mat.mulVec x = 0) (hρ : ρ.M.mat.mulVec x ≠ 0) :
    ¬ σ.M.ker ≤ ρ.M.ker := fun hle =>
  hρ ((ρ.M.mem_ker_iff_mulVec_zero x).mp
    (hle ((σ.M.mem_ker_iff_mulVec_zero x).mpr hσ)))

/-- `(pure ψ).M` is the outer product `ψ ψ†` (entrywise, in `HermitianMat`
`FunLike` form, which is what `mulVec` normalises to). -/
private lemma pure_M_apply (ψ : Ket d) (i j : d) :
    (MState.pure ψ).M i j = ψ i * (starRingEnd ℂ) (ψ j) := rfl

/-! ### A concrete reversible witness: a qubit visiting an orthogonal pure state

`pure |1⟩` and `pure |0⟩` are orthogonal pure states, hence support-incompatible,
hence at entropic proper time `⊤` from one another — while each is at `0` from
itself. This is the explicit, non-vacuous instance the abstract theorem needs. -/

/-- **Orthogonal pure states are at clock-distance `⊤`.** The entropic proper
time between the two computational-basis pure states of a qubit is `⊤`. -/
lemma entropicProperTime_qubit_basis_eq_top :
    entropicProperTime (MState.pure (Ket.basis (1 : Fin 2)))
      (MState.pure (Ket.basis (0 : Fin 2))) = ⊤ := by
  rw [entropicProperTime_eq_qRelativeEnt]
  refine qRelativeEnt_eq_top_of_not_ker_le
    (not_ker_le_of_mulVec_witness (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) ?_ ?_)
  · -- |1⟩ is orthogonal to |0⟩, so it lies in the kernel of `pure |0⟩`.
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pure_M_apply,
        Ket.basis, Ket.apply, EuclideanSpace.single_apply]
  · -- |1⟩ is an eigenvector of `pure |1⟩` with eigenvalue 1, so not in its kernel.
    intro hcontra
    have h1 := congrFun hcontra (1 : Fin 2)
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pure_M_apply,
      Ket.basis, Ket.apply, EuclideanSpace.single_apply] at h1

/-! ### The non-monotone theorem

For any state-history `f` that starts and ends (at a recurrence) on `ρ₀` but
passes through a support-incompatible state at an interior step, the clock
reading `n ↦ entropicProperTime (f n) ρ₀` is *neither* monotone *nor* antitone —
it leaves `0`, hits `⊤`, and comes back. No faithfulness, no postulated ramp. -/

/-- **Reversible recurrence is not a monotone clock.** A history that is `ρ₀` at
times `0` and `N` but support-incompatible with `ρ₀` at an interior time `k`
makes the entropic-time reading non-monotone and non-antitone. -/
lemma clock_reading_not_monotone_of_top
    (f : ℕ → MState d) (ρ₀ : MState d) {k N : ℕ} (hkN : k < N)
    (h0 : f 0 = ρ₀) (hN : f N = ρ₀)
    (htop : entropicProperTime (f k) ρ₀ = ⊤) :
    ¬ Monotone (fun n => entropicProperTime (f n) ρ₀)
      ∧ ¬ Antitone (fun n => entropicProperTime (f n) ρ₀) := by
  have hr0 : entropicProperTime (f 0) ρ₀ = 0 := by rw [h0]; exact entropicProperTime_self ρ₀
  have hrN : entropicProperTime (f N) ρ₀ = 0 := by rw [hN]; exact entropicProperTime_self ρ₀
  refine ⟨fun hmono => ?_, fun hanti => ?_⟩
  · have := hmono hkN.le
    simp only [htop, hrN] at this
    simp at this
  · have := hanti (Nat.zero_le k)
    simp only [htop, hr0] at this
    simp at this

/-- The qubit "ping-pong" history: `|0⟩` except at step `1`, where it is the
orthogonal `|1⟩`. A reversible swap visiting an orthogonal state. -/
noncomputable def qubitPingPong (n : ℕ) : MState (Fin 2) :=
  if n = 1 then MState.pure (Ket.basis 1) else MState.pure (Ket.basis 0)

/-- **A fully concrete, non-vacuous non-monotone clock.** The qubit ping-pong
reading to its initial state is neither monotone nor antitone: `0` at steps `0`
and `2`, `⊤` at step `1`. This is counterexample C-A4 as a Lean theorem — the
reversible clock genuinely leaves and returns, with no faithfulness assumed. -/
lemma qubitPingPong_clock_not_monotone :
    ¬ Monotone (fun n => entropicProperTime (qubitPingPong n) (MState.pure (Ket.basis 0)))
      ∧ ¬ Antitone (fun n => entropicProperTime (qubitPingPong n) (MState.pure (Ket.basis 0))) :=
  clock_reading_not_monotone_of_top qubitPingPong (MState.pure (Ket.basis 0))
    (k := 1) (N := 2) (by norm_num)
    (by simp [qubitPingPong]) (by simp [qubitPingPong])
    (by simpa [qubitPingPong] using entropicProperTime_qubit_basis_eq_top)

/-! ## 9. Genuine discrete Spohn production from quantum relative-entropy contraction

For a finite CPTP step `Φ` with fixed reference `σ`, the correct discrete
entropy production is the relative-entropy loss

`D(ρ ‖ σ) - D(Φρ ‖ σ)`.

Unlike the positive jump-count intensity, this quantity vanishes on every
fixed state.  DPI proves the exact one-step balance, and summing that balance
along the channel orbit gives a finite telescope: accumulated production plus
the residual relative entropy equals the initial relative entropy.  This is a
genuine discrete Spohn theorem.  It is not the continuous-time derivative
formula for an unbounded or type-III quantum dynamical semigroup. -/

/-- The discrete Spohn production of one channel step relative to a reference
state: the decrease in Umegaki quantum relative entropy.  Subtraction is the
ordered subtraction of `ENNReal`; the fixed-reference DPI theorem below proves
that it is an exact, non-truncated difference. -/
noncomputable def discreteSpohnProduction
    (Φ : CPTPMap d d) (ρ σ : MState d) : ENNReal :=
  entropicProperTime ρ σ - entropicProperTime (Φ ρ) σ

/-- Discrete Spohn production is nonnegative in its native extended
nonnegative-real codomain.  Its substantive relationship to the dynamics is
the exact balance theorem `discreteSpohnProduction_add_processed_eq`. -/
lemma discreteSpohnProduction_nonneg
    (Φ : CPTPMap d d) (ρ σ : MState d) :
    0 ≤ discreteSpohnProduction Φ ρ σ :=
  bot_le

/-- **One-step discrete Spohn balance.** If `σ` is fixed by the CPTP step, the
relative entropy before the step splits exactly into the entropy produced plus
the relative entropy remaining after the step.  DPI supplies the order needed
to cancel ordered subtraction. -/
lemma discreteSpohnProduction_add_processed_eq
    (Φ : CPTPMap d d) (ρ σ : MState d) (hfix : Φ σ = σ) :
    discreteSpohnProduction Φ ρ σ + entropicProperTime (Φ ρ) σ =
      entropicProperTime ρ σ := by
  unfold discreteSpohnProduction
  exact tsub_add_cancel_of_le (dissipative_step_contracts Φ ρ σ hfix)

/-- The discrete Spohn production vanishes on every state fixed by the
channel, for any chosen reference state. -/
lemma discreteSpohnProduction_zero_of_state_fixed
    (Φ : CPTPMap d d) (ρ σ : MState d) (hρ : Φ ρ = ρ) :
    discreteSpohnProduction Φ ρ σ = 0 := by
  simp [discreteSpohnProduction, hρ]

/-- In particular, an invariant equilibrium reference produces no entropy
when it is itself evolved. -/
lemma discreteSpohnProduction_equilibrium_zero
    (Φ : CPTPMap d d) (σ : MState d) (hfix : Φ σ = σ) :
    discreteSpohnProduction Φ σ σ = 0 :=
  discreteSpohnProduction_zero_of_state_fixed Φ σ σ hfix

/-- Entropy production accumulated over the first `n` steps of a finite CPTP
orbit. -/
noncomputable def accumulatedDiscreteSpohnProduction
    (Φ : CPTPMap d d) (ρ₀ σ : MState d) (n : ℕ) : ENNReal :=
  ∑ k ∈ Finset.range n,
    discreteSpohnProduction Φ (channelOrbit Φ ρ₀ k) σ

/-- **Finite discrete Spohn H-theorem.** For a fixed-point reference, the
accumulated production through step `n` plus the residual relative entropy at
step `n` is exactly the initial relative entropy.  This is the additive budget
behind `dissipative_orbit_antitone`, not merely another monotonicity statement. -/
lemma accumulatedDiscreteSpohnProduction_add_residual_eq
    (Φ : CPTPMap d d) (ρ₀ σ : MState d) (hfix : Φ σ = σ) (n : ℕ) :
    accumulatedDiscreteSpohnProduction Φ ρ₀ σ n +
        entropicProperTime (channelOrbit Φ ρ₀ n) σ =
      entropicProperTime ρ₀ σ := by
  induction n with
  | zero => simp [accumulatedDiscreteSpohnProduction]
  | succ n ih =>
      rw [accumulatedDiscreteSpohnProduction, Finset.sum_range_succ]
      change
        (∑ k ∈ Finset.range n,
            discreteSpohnProduction Φ (channelOrbit Φ ρ₀ k) σ) +
            discreteSpohnProduction Φ (channelOrbit Φ ρ₀ n) σ +
            entropicProperTime (channelOrbit Φ ρ₀ (n + 1)) σ =
          entropicProperTime ρ₀ σ
      rw [channelOrbit_succ]
      rw [add_assoc,
        discreteSpohnProduction_add_processed_eq Φ (channelOrbit Φ ρ₀ n) σ hfix]
      exact ih

/-- The replacement channel is a nontrivial exact witness: it produces the
entire initial relative entropy in one step because the residual state is the
reference itself. -/
lemma replacement_discreteSpohnProduction_eq_relativeEntropy
    [Nonempty d] (ρ σ : MState d) :
    discreteSpohnProduction (CPTPMap.replacement σ) ρ σ =
      entropicProperTime ρ σ := by
  simp [discreteSpohnProduction, CPTPMap.replacement_apply]

/-! ## 10. Positive-time CPTP semigroups and interval Spohn production

A dissipative continuous-time carrier must be indexed by nonnegative time.
Using all of `ℝ`, as in a group action, would also provide CPTP inverses and is
therefore too strong for irreversible dynamics.  The following algebraic
semigroup records the channel law on `ℝ≥0` without assuming continuity.  DPI
then proves time-ordered relative-entropy contraction and an exact cocycle for
production over adjacent time intervals.

Strong continuity, identification of the infinitesimal generator with a GKLS
operator, and differentiating the relative entropy at `t = 0` remain separate
analytic obligations. -/

/-- A positive-time CPTP semigroup: a channel `Φₜ` for every `t : ℝ≥0`, with
`Φ₀ = id` and `Φₛ₊ₜ = Φₛ ∘ Φₜ`.  This is the algebraic carrier underlying a
finite-dimensional quantum dynamical semigroup; no continuity is included. -/
structure CPTPPositiveTimeSemigroup (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The CPTP channel at nonnegative time `t`. -/
  channel : NNReal → CPTPMap d d
  /-- Evolution for zero elapsed time is the identity channel. -/
  channel_zero : channel 0 = CPTPMap.id
  /-- Evolution respects addition of nonnegative elapsed times. -/
  channel_add : ∀ s t, channel (s + t) = channel s ∘ₘ channel t

namespace CPTPPositiveTimeSemigroup

/-- The state obtained by evolving `ρ` for nonnegative time `t`. -/
noncomputable def stateAt (S : CPTPPositiveTimeSemigroup d) (ρ : MState d)
    (t : NNReal) : MState d :=
  S.channel t ρ

/-- A state is a fixed point of the positive-time semigroup when every channel
in the family leaves it invariant. -/
def IsFixedPoint (S : CPTPPositiveTimeSemigroup d) (σ : MState d) : Prop :=
  ∀ t, S.stateAt σ t = σ

/-- The positive-time evolution starts at the supplied state. -/
@[simp] lemma stateAt_zero (S : CPTPPositiveTimeSemigroup d) (ρ : MState d) :
    S.stateAt ρ 0 = ρ := by
  rw [stateAt, S.channel_zero]
  exact CPTPMap.id_MState ρ

/-- The semigroup law transported from channels to their action on states. -/
lemma stateAt_add (S : CPTPPositiveTimeSemigroup d) (ρ : MState d) (s t : NNReal) :
    S.stateAt ρ (s + t) = S.stateAt (S.stateAt ρ t) s := by
  rw [stateAt, S.channel_add]
  exact CPTPMap.compose_eq ρ

/-- Adding elapsed time cannot increase relative entropy to a semigroup fixed
point.  This is the positive-time semigroup form of one-step DPI. -/
lemma relativeEntropy_add_right_le (S : CPTPPositiveTimeSemigroup d) (ρ σ : MState d)
    (hfix : S.IsFixedPoint σ) (s t : NNReal) :
    entropicProperTime (S.stateAt ρ (s + t)) σ ≤
      entropicProperTime (S.stateAt ρ s) σ := by
  rw [add_comm, S.stateAt_add]
  exact dissipative_step_contracts (S.channel t) (S.stateAt ρ s) σ (hfix t)

/-- **Positive-time quantum H-theorem.** Relative entropy to a fixed-point
reference is antitone along every algebraic positive-time CPTP semigroup. -/
lemma relativeEntropy_antitone (S : CPTPPositiveTimeSemigroup d) (ρ σ : MState d)
    (hfix : S.IsFixedPoint σ) :
    Antitone (fun t => entropicProperTime (S.stateAt ρ t) σ) := by
  intro s t hst
  obtain ⟨u, rfl⟩ := exists_add_of_le hst
  exact S.relativeEntropy_add_right_le ρ σ hfix s u

/-- Spohn production over the time interval `[s,t]`, defined as the decrease
of quantum relative entropy to the reference state. -/
noncomputable def intervalSpohnProduction (S : CPTPPositiveTimeSemigroup d)
    (ρ σ : MState d) (s t : NNReal) : ENNReal :=
  entropicProperTime (S.stateAt ρ s) σ - entropicProperTime (S.stateAt ρ t) σ

/-- For `s ≤ t`, interval production plus the relative entropy remaining at
`t` equals the relative entropy present at `s`. -/
lemma intervalSpohnProduction_add_residual_eq (S : CPTPPositiveTimeSemigroup d)
    (ρ σ : MState d) (hfix : S.IsFixedPoint σ) {s t : NNReal} (hst : s ≤ t) :
    S.intervalSpohnProduction ρ σ s t + entropicProperTime (S.stateAt ρ t) σ =
      entropicProperTime (S.stateAt ρ s) σ := by
  unfold intervalSpohnProduction
  exact tsub_add_cancel_of_le (S.relativeEntropy_antitone ρ σ hfix hst)

/-- **Interval-production cocycle.** Production is exactly additive on
adjacent ordered intervals: `Σ[s,t] + Σ[t,u] = Σ[s,u]`. -/
lemma intervalSpohnProduction_cocycle (S : CPTPPositiveTimeSemigroup d)
    (ρ σ : MState d) (hfix : S.IsFixedPoint σ) {s t u : NNReal}
    (hst : s ≤ t) (htu : t ≤ u) :
    S.intervalSpohnProduction ρ σ s t + S.intervalSpohnProduction ρ σ t u =
      S.intervalSpohnProduction ρ σ s u := by
  unfold intervalSpohnProduction
  exact tsub_add_tsub_cancel
    (S.relativeEntropy_antitone ρ σ hfix hst)
    (S.relativeEntropy_antitone ρ σ hfix htu)

/-- Interval production vanishes for a trajectory that is fixed throughout
the positive-time semigroup, independently of the chosen reference state. -/
lemma intervalSpohnProduction_zero_of_fixed_state (S : CPTPPositiveTimeSemigroup d)
    (ρ σ : MState d) (hρ : S.IsFixedPoint ρ) (s t : NNReal) :
    S.intervalSpohnProduction ρ σ s t = 0 := by
  simp [intervalSpohnProduction, hρ s, hρ t]

end CPTPPositiveTimeSemigroup

/-! ## 11. Strongly continuous CPTP semigroups and right generators

This section upgrades the algebraic positive-time carrier with strong
continuity of every state orbit.  Its generator is defined by the right-hand
matrix difference quotient, matching the nonnegative time domain.  The
identity semigroup supplies a concrete inhabitant with zero generator, while
the fixed-point theorem is reusable by any downstream GKLS realization. -/

/-- A finite-dimensional `C₀` CPTP semigroup: an algebraic positive-time CPTP
semigroup whose orbit through every mixed state is continuous. -/
structure CPTPC0Semigroup (d : Type*) [Fintype d] [DecidableEq d]
    extends CPTPPositiveTimeSemigroup d where
  /-- Every mixed-state orbit is continuous in nonnegative time. -/
  strong_continuous : ∀ ρ : MState d, Continuous (fun t => channel t ρ)

namespace CPTPC0Semigroup

open Filter Set

/-- The identity channel at every time, packaged as a strongly continuous CPTP
semigroup.  It is the reversible zero-generator boundary case. -/
noncomputable def identity (d : Type*) [Fintype d] [DecidableEq d] :
    CPTPC0Semigroup d where
  channel := fun _ => CPTPMap.id
  channel_zero := rfl
  channel_add := fun _ _ => (CPTPMap.id_compose CPTPMap.id).symm
  strong_continuous := fun _ => continuous_const

/-- Strong continuity and the identity law give initial-state recovery
`Φₜρ → ρ` as `t → 0` within nonnegative time. -/
lemma initial_recovery (S : CPTPC0Semigroup d) (ρ : MState d) :
    Tendsto (fun t => S.toCPTPPositiveTimeSemigroup.stateAt ρ t)
      (nhds 0) (nhds ρ) := by
  have h : Tendsto (fun t => S.channel t ρ) (nhds 0) (nhds (S.channel 0 ρ)) :=
    (S.strong_continuous ρ).continuousAt
  simpa [CPTPPositiveTimeSemigroup.stateAt, S.channel_zero] using h

/-- A matrix operator `A` is the infinitesimal generator when every mixed-state
orbit has right difference quotient converging to `Aρ` at time zero. -/
def HasInfinitesimalGenerator (S : CPTPC0Semigroup d)
    (A : Matrix d d ℂ → Matrix d d ℂ) : Prop :=
  ∀ ρ : MState d,
    Tendsto
      (fun t : NNReal => (((t : ℝ) : ℂ)⁻¹) • ((S.channel t ρ).m - ρ.m))
      (nhdsWithin 0 (Ioi 0)) (nhds (A ρ.m))

/-- The identity CPTP semigroup has the zero infinitesimal generator. -/
lemma identity_hasInfinitesimalGenerator_zero :
    (identity d).HasInfinitesimalGenerator (fun _ => 0) := by
  intro ρ
  simp [identity]

/-- A semigroup-fixed trajectory lies in the kernel of every identified
infinitesimal generator.  The proof compares its identically zero difference
quotient with the generator limit. -/
lemma generator_eq_zero_of_fixedPoint (S : CPTPC0Semigroup d)
    (A : Matrix d d ℂ → Matrix d d ℂ) (hgen : S.HasInfinitesimalGenerator A)
    (ρ : MState d) (hfix : S.toCPTPPositiveTimeSemigroup.IsFixedPoint ρ) :
    A ρ.m = 0 := by
  have heq :
      (fun t : NNReal => (((t : ℝ) : ℂ)⁻¹) • ((S.channel t ρ).m - ρ.m)) =
        fun _ => 0 := by
    funext t
    rw [show S.channel t ρ = ρ from hfix t]
    simp
  have hzero : Tendsto
      (fun t : NNReal => (((t : ℝ) : ℂ)⁻¹) • ((S.channel t ρ).m - ρ.m))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hzero (hgen ρ) |>.symm

end CPTPC0Semigroup

end

end Physlib.Thermodynamics.QuantumRelativeEntropyArrow

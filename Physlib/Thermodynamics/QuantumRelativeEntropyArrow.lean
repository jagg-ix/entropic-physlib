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

/-! ## §1 — The two QuantumInfo inputs, as `entropicProperTime` facts

`entropicProperTime = qRelativeEnt = D̃_1`, so the sandwiched-Rényi DPI and
unitary-invariance lemmas specialise definitionally. -/

/-- **Data-processing for entropic proper time.** A CPTP step never increases
the entropic proper time of a state pair. (Meiburg `sandwichedRenyiEntropy_DPI_eq_one`
at `α = 1`.) -/
theorem entropicProperTime_DPI (Φ : CPTPMap d d) (ρ σ : MState d) :
    entropicProperTime (Φ ρ) (Φ σ) ≤ entropicProperTime ρ σ :=
  sandwichedRenyiEntropy_DPI_eq_one ρ σ Φ

/-- **Unitary invariance of entropic proper time.** Conjugating both arguments
by the same unitary leaves the entropic proper time unchanged. (Meiburg
`sandwichedRenyiEntropy_conj_unitary` at `α = 1`.) -/
theorem entropicProperTime_U_conj (U : Matrix.unitaryGroup d ℂ) (ρ σ : MState d) :
    entropicProperTime (ρ.U_conj U) (σ.U_conj U) = entropicProperTime ρ σ :=
  sandwichedRenyiEntropy_conj_unitary one_pos ρ σ U

/-! ## §2 — Discrete orbits -/

/-- The discrete dissipative orbit: iterate the CPTP step `Φ` from `ρ₀`. -/
noncomputable def channelOrbit (Φ : CPTPMap d d) (ρ₀ : MState d) (n : ℕ) : MState d :=
  (fun ρ => Φ ρ)^[n] ρ₀

@[simp] theorem channelOrbit_zero (Φ : CPTPMap d d) (ρ₀ : MState d) :
    channelOrbit Φ ρ₀ 0 = ρ₀ := rfl

theorem channelOrbit_succ (Φ : CPTPMap d d) (ρ₀ : MState d) (n : ℕ) :
    channelOrbit Φ ρ₀ (n + 1) = Φ (channelOrbit Φ ρ₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- The discrete unitary orbit: iterate the conjugation `ρ ↦ U ◃ ρ` from `ρ₀`. -/
noncomputable def unitaryOrbit (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) (n : ℕ) : MState d :=
  (fun ρ => ρ.U_conj U)^[n] ρ₀

@[simp] theorem unitaryOrbit_zero (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) :
    unitaryOrbit U ρ₀ 0 = ρ₀ := rfl

theorem unitaryOrbit_succ (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) (n : ℕ) :
    unitaryOrbit U ρ₀ (n + 1) = (unitaryOrbit U ρ₀ n).U_conj U :=
  Function.iterate_succ_apply' _ _ _

/-! ## §3 — Dissipative dynamics: a monotone (antitone) clock — derived, not postulated -/

/-- **One dissipative step contracts the clock.** If `σ` is a fixed point of the
channel, a single step cannot increase the entropic proper time to `σ`. -/
theorem dissipative_step_contracts (Φ : CPTPMap d d) (ρ σ : MState d) (hfix : Φ σ = σ) :
    entropicProperTime (Φ ρ) σ ≤ entropicProperTime ρ σ := by
  calc entropicProperTime (Φ ρ) σ
      = entropicProperTime (Φ ρ) (Φ σ) := by rw [hfix]
    _ ≤ entropicProperTime ρ σ := entropicProperTime_DPI Φ ρ σ

/-- **Step-wise monotonicity along the dissipative orbit.** -/
theorem dissipative_orbit_succ_le (Φ : CPTPMap d d) (ρ₀ σ : MState d) (hfix : Φ σ = σ)
    (n : ℕ) :
    entropicProperTime (channelOrbit Φ ρ₀ (n + 1)) σ
      ≤ entropicProperTime (channelOrbit Φ ρ₀ n) σ := by
  rw [channelOrbit_succ]
  exact dissipative_step_contracts Φ _ σ hfix

/-- **The quantum H-theorem, derived from DPI.** Along a dissipative orbit, the
entropic proper time to a fixed-point reference is antitone — a genuine arrow
toward equilibrium, with no postulated linear ramp. -/
theorem dissipative_orbit_antitone (Φ : CPTPMap d d) (ρ₀ σ : MState d) (hfix : Φ σ = σ) :
    Antitone (fun n => entropicProperTime (channelOrbit Φ ρ₀ n) σ) :=
  antitone_nat_of_succ_le (dissipative_orbit_succ_le Φ ρ₀ σ hfix)

/-! ## §4 — Unitary dynamics: a frozen clock to an invariant reference -/

/-- **Unitary evolution freezes the clock to an invariant reference.** If `σ` is
invariant under the conjugation, the entropic proper time of the unitary orbit
to `σ` is constant in `n` — reversible dynamics accrues no entropic time toward
equilibrium. -/
theorem unitary_orbit_const_to_invariant (U : Matrix.unitaryGroup d ℂ) (ρ₀ σ : MState d)
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

/-! ## §5 — Unitary dynamics: recurrence of the clock to the initial state -/

/-- **Recurrence: the clock to the initial state returns to zero.** At any
recurrence time `N` (where the orbit comes back to `ρ₀`) the entropic proper
time to `ρ₀` is `0`, as it is at `n = 0`. The distance-to-initial-state is
periodic, not a monotone arrow. -/
theorem unitary_orbit_recurs_to_init (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) {N : ℕ}
    (hper : unitaryOrbit U ρ₀ N = ρ₀) :
    entropicProperTime (unitaryOrbit U ρ₀ N) ρ₀ = 0 := by
  rw [hper, entropicProperTime_self]

/-- The clock to the initial state starts at `0`. -/
@[simp] theorem unitary_orbit_init_at_zero (U : Matrix.unitaryGroup d ℂ) (ρ₀ : MState d) :
    entropicProperTime (unitaryOrbit U ρ₀ 0) ρ₀ = 0 := by
  rw [unitaryOrbit_zero, entropicProperTime_self]

/-! ## §6 — The distinguishing theorem (C-A4, made precise)

For one and the same reference `σ`: reversible (unitary) dynamics freezes the
entropic-time clock, while dissipative dynamics turns it into a monotone arrow.
This is the content the postulated linear ramp could not express. -/

/-- **Reversible ⇒ frozen clock, dissipative ⇒ monotone arrow**, against a
common reference `σ` that is both unitary-invariant and a channel fixed point. -/
theorem clock_frozen_under_reversible_arrow_under_dissipative
    (U : Matrix.unitaryGroup d ℂ) (Φ : CPTPMap d d) (ρ₀ σ : MState d)
    (hinv : σ.U_conj U = σ) (hfix : Φ σ = σ) :
    (∀ n, entropicProperTime (unitaryOrbit U ρ₀ n) σ = entropicProperTime ρ₀ σ)
      ∧ Antitone (fun n => entropicProperTime (channelOrbit Φ ρ₀ n) σ) :=
  ⟨fun n => unitary_orbit_const_to_invariant U ρ₀ σ hinv n,
    dissipative_orbit_antitone Φ ρ₀ σ hfix⟩

/-! ## §7 — Concrete witnesses (non-vacuity)

The dissipative witness is the physically meaningful one: the replacement
channel `Φ ρ = σ` resets to `σ` in a single step, so the clock to `σ` drops to
its floor `0` after one step — a real arrow, not the boring constant. The
unitary witness uses the identity conjugation, confirming the invariant-reference
hypothesis is satisfiable. -/

/-- The replacement channel `ρ ↦ σ` has `σ` as a fixed point. -/
theorem replacement_fixed [Nonempty d] (σ : MState d) :
    (CPTPMap.replacement σ : CPTPMap d d) σ = σ :=
  CPTPMap.replacement_apply σ σ

/-- **A real dissipative arrow.** Under the replacement channel, the clock to
`σ` reaches its floor `0` after one step, for any initial state. -/
theorem replacement_orbit_one_eq_zero [Nonempty d] (ρ₀ σ : MState d) :
    entropicProperTime (channelOrbit (CPTPMap.replacement σ) ρ₀ 1) σ = 0 := by
  rw [channelOrbit_succ, channelOrbit_zero, CPTPMap.replacement_apply, entropicProperTime_self]

/-- The replacement-channel orbit is a genuine (antitone) entropic-time clock. -/
theorem replacement_orbit_antitone [Nonempty d] (ρ₀ σ : MState d) :
    Antitone (fun n => entropicProperTime (channelOrbit (CPTPMap.replacement σ) ρ₀ n) σ) :=
  dissipative_orbit_antitone _ ρ₀ σ (replacement_fixed σ)

/-- The identity conjugation leaves any state invariant — the unitary-invariant
hypothesis is satisfiable. -/
theorem U_conj_one_self (ρ : MState d) : ρ.U_conj 1 = ρ := by
  apply MState.ext_m
  simp [MState.U_conj]

/-! ## §8 — Strict positivity in mid-orbit, faithfulness-free (closing C-A4)

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
theorem qRelativeEnt_eq_top_of_not_ker_le {ρ σ : MState d}
    (h : ¬ σ.M.ker ≤ ρ.M.ker) : qRelativeEnt ρ σ = ⊤ := by
  have hred : qRelativeEnt ρ σ = SandwichedRelRentropy 1 ρ σ := rfl
  rw [hred]
  unfold SandwichedRelRentropy
  rw [dif_pos one_pos, dif_neg h]

/-- The same, phrased for `entropicProperTime`. -/
theorem entropicProperTime_eq_top_of_not_ker_le {ρ σ : MState d}
    (h : ¬ σ.M.ker ≤ ρ.M.ker) : entropicProperTime ρ σ = ⊤ :=
  qRelativeEnt_eq_top_of_not_ker_le h

/-- A single `mulVec` witness `x` in `σ`'s kernel but not `ρ`'s certifies the
support incompatibility. -/
theorem not_ker_le_of_mulVec_witness {ρ σ : MState d} (x : EuclideanSpace ℂ d)
    (hσ : σ.M.mat.mulVec x = 0) (hρ : ρ.M.mat.mulVec x ≠ 0) :
    ¬ σ.M.ker ≤ ρ.M.ker := fun hle =>
  hρ ((ρ.M.mem_ker_iff_mulVec_zero x).mp
    (hle ((σ.M.mem_ker_iff_mulVec_zero x).mpr hσ)))

/-- `(pure ψ).M` is the outer product `ψ ψ†` (entrywise, in `HermitianMat`
`FunLike` form, which is what `mulVec` normalises to). -/
private theorem pure_M_apply (ψ : Ket d) (i j : d) :
    (MState.pure ψ).M i j = ψ i * (starRingEnd ℂ) (ψ j) := rfl

/-! ### A concrete reversible witness: a qubit visiting an orthogonal pure state

`pure |1⟩` and `pure |0⟩` are orthogonal pure states, hence support-incompatible,
hence at entropic proper time `⊤` from one another — while each is at `0` from
itself. This is the explicit, non-vacuous instance the abstract theorem needs. -/

/-- **Orthogonal pure states are at clock-distance `⊤`.** The entropic proper
time between the two computational-basis pure states of a qubit is `⊤`. -/
theorem entropicProperTime_qubit_basis_eq_top :
    entropicProperTime (MState.pure (Ket.basis (1 : Fin 2)))
      (MState.pure (Ket.basis (0 : Fin 2))) = ⊤ := by
  rw [entropicProperTime_eq_qRelativeEnt]
  refine qRelativeEnt_eq_top_of_not_ker_le
    (not_ker_le_of_mulVec_witness (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) ?_ ?_)
  · -- |1⟩ is orthogonal to |0⟩, so it lies in the kernel of `pure |0⟩`.
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, pure_M_apply, Ket.basis, Ket.apply]
  · -- |1⟩ is an eigenvector of `pure |1⟩` with eigenvalue 1, so not in its kernel.
    intro hcontra
    have h1 := congrFun hcontra (1 : Fin 2)
    simp [Matrix.mulVec, dotProduct, pure_M_apply, Ket.basis, Ket.apply] at h1

/-! ### The non-monotone theorem

For any state-history `f` that starts and ends (at a recurrence) on `ρ₀` but
passes through a support-incompatible state at an interior step, the clock
reading `n ↦ entropicProperTime (f n) ρ₀` is *neither* monotone *nor* antitone —
it leaves `0`, hits `⊤`, and comes back. No faithfulness, no postulated ramp. -/

/-- **Reversible recurrence is not a monotone clock.** A history that is `ρ₀` at
times `0` and `N` but support-incompatible with `ρ₀` at an interior time `k`
makes the entropic-time reading non-monotone and non-antitone. -/
theorem clock_reading_not_monotone_of_top
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
theorem qubitPingPong_clock_not_monotone :
    ¬ Monotone (fun n => entropicProperTime (qubitPingPong n) (MState.pure (Ket.basis 0)))
      ∧ ¬ Antitone (fun n => entropicProperTime (qubitPingPong n) (MState.pure (Ket.basis 0))) :=
  clock_reading_not_monotone_of_top qubitPingPong (MState.pure (Ket.basis 0))
    (k := 1) (N := 2) (by norm_num)
    (by simp [qubitPingPong]) (by simp [qubitPingPong])
    (by simpa [qubitPingPong] using entropicProperTime_qubit_basis_eq_top)

end

end Physlib.Thermodynamics.QuantumRelativeEntropyArrow

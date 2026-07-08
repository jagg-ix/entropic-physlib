/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockUniqueness
public import Mathlib.Data.Matrix.Mul

/-!
# Quantized relational time: a δ·ℕ lattice on Page–Wootters physical states

`Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockUniqueness` proves a
per-event **floor**: on a Landauer-bounded (erasure-driven) worldline every
strictly positive `τ_ent` increment is at least `δ_τ = k_B·log 2 / ℏ`
(`tau_ent_minimum_step`).  A floor `Δτ ≥ δ` is weaker than a **lattice**
`τ ∈ δ·ℕ`: the floor allows the increments to be any reals above `δ`, whereas a
lattice fixes them to be exact integer multiples of `δ`.

This module supplies the missing lattice.  It does so by adding the two inputs a
lattice needs beyond the floor, and keeping them explicit:

1. a **discrete event ladder** — the physical states are indexed by `ℕ`, one per
   irreversible event (the discrete clock-spectrum input); and
2. an **exact one-bit-per-event** reading — the `n`-th state reads time
   `n · δ_τ` exactly, not merely `≥ δ_τ` above its predecessor.

Under those two inputs the relational clock reads values in `δ_τ·ℕ`
(`reading_mem_lattice`), advances by exactly `δ_τ` per event
(`reading_step_eq`), and recovers the floor as a corollary
(`reading_min_step`).  The quantum `δ_τ` is **not** planted: the constructor
`EntropicTimeLadder.ofLandauerQuantum` sets `δ_τ = k_B·log 2 / ℏ`, the same value
the minimum-step theorem produces, and `ladder_step_eq_landauer_floor` records
the equality.

The Page–Wootters tie is in §2: the lattice is defined on genuine physical
states — kernel elements of a `HamiltonianConstraint` (`H_total|Ψ⟩ = 0`) — so the
quantized readings are read off Wheeler–DeWitt physical states, not off an
auxiliary parameter.  §3 exhibits a concrete diagonal clock observable whose
eigenvalues are exactly the lattice points `{0, δ, 2δ}` — a discrete spectrum
realised, not assumed in the abstract.  §4 generalises this to the `n`-level
operator `entropicTimeOperator δ n`, whose eigenvalues are the first `n` lattice
points with uniform gap `δ`; the 3-level observable is its `n = 3` truncation.

## What this proves

* `reading_mem_lattice` — every clock reading is an integer multiple of `δ_τ`
  (the `τ ∈ δ·ℕ` bar).
* `reading_step_eq` — consecutive readings differ by exactly `δ_τ` (the lattice
  spacing; strictly stronger than the floor).
* `reading_min_step` — any two distinct readings differ by at least `δ_τ`
  (the floor, recovered from the lattice).
* `reading_strictMono` — readings strictly increase with the event index, so the
  reading map is an order embedding `ℕ ↪ ℝ` with discrete (closed, gapped) image.
* `clockMatrix_eigenvector` / `clockMatrix_eigenvalue_lattice` — a concrete
  3-level clock observable with eigenvalues `{0, δ, 2δ} ⊆ δ·ℕ`.
* `entropicTimeOperator_eigenvector` / `entropicTimeOperator_gap` — the `n`-level
  family generalising it: eigenvalues `{0, δ, …, (n-1)·δ} ⊆ δ·ℕ` with uniform gap
  `δ`, equal to the Landauer quantum `k_B·log 2 / ℏ`
  (`entropicTimeOperator_gap_landauer`).

## What this does NOT prove

* It does **not** derive quantization from continuous Hamiltonian dynamics plus
  the second law.  Both inputs above are assumptions: the event ladder is
  discrete by construction (index `ℕ`), and the exact `n·δ_τ` reading is the
  one-bit-per-event model, not a consequence of unitary evolution.  For a
  genuinely continuous `S_I(t)` no such ladder exists — the increments shrink to
  zero, violating the Landauer floor — which is exactly why the floor theorem
  lives on erasure-driven worldlines.
* The Page–Wootters structure here records that the ladder states are physical
  (constraint kernel); it does not derive the discrete clock spectrum from the
  constraint.  §3's discrete spectrum is exhibited on a chosen diagonal
  observable, not forced by `H_total`.

## The three layers, kept separate

1. **Pure math (Lean-provable):** an `ℕ`-indexed reading `n ↦ n·δ_τ` lands in
   the lattice `δ_τ·ℕ`, steps by `δ_τ`, and a diagonal matrix has its diagonal
   as spectrum.  No physics.
2. **Operational identification:** one irreversible event ↔ one `k_B·log 2`
   erasure ↔ a clock advance of `δ_τ = k_B·log 2 / ℏ`.
3. **Physical claim:** entropy production sets the time quantum `δ_τ`.

Refuting the (1)↔(3) identification leaves the layer-1 theorems untouched.

## Origin and references

- Page & Wootters 1983, *Evolution without evolution*, Phys. Rev. D **27**, 2885.
- R. Landauer 1961, *Irreversibility and heat generation in the computing
  process*, IBM J. Res. Dev. **5**, 183.
- Weberszpil & Sotolongo-Costa 2026, *Entropy as a Clock*, Int. J. Theor. Phys.
  **65**:15, DOI 10.1007/s10773-025-06212-1.

This is an independent Lean formalisation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.RelationalTime.QuantizedTime

open _root_.QuantumMechanics.RelationalTime
open Physlib.Thermodynamics.Landauer
open Constants

/-! ## §1 — The entropic-time lattice

An abstract reading function `reading : ℕ → ℝ` of the form `n ↦ n·δ_τ`.  This is
the lattice the floor theorem of `EntropicTime.ClockUniqueness` does not reach: the
floor bounds increments below by `δ_τ`; here every increment is exactly `δ_τ`. -/

/-- **Entropic-time ladder.** A clock whose `n`-th physical event reads exactly
`n · δ_τ`, with quantum `δ_τ > 0`.  The exact (rather than `≥ δ_τ`) reading is
the one-bit-per-event model. -/
structure EntropicTimeLadder where
  /-- The time quantum. -/
  δ_τ : ℝ
  /-- The quantum is strictly positive. -/
  δ_τ_pos : 0 < δ_τ
  /-- The clock reading at event index `n`. -/
  reading : ℕ → ℝ
  /-- Each event reads an exact integer multiple of the quantum. -/
  reading_eq : ∀ n, reading n = (n : ℝ) * δ_τ

namespace EntropicTimeLadder

variable (Λ : EntropicTimeLadder)

/-- The clock starts at zero. -/
@[simp] theorem reading_zero : Λ.reading 0 = 0 := by
  rw [Λ.reading_eq]; simp

/-- **Lattice membership** (`τ ∈ δ·ℕ`): every reading is an integer multiple of
the quantum `δ_τ`. -/
theorem reading_mem_lattice (n : ℕ) : ∃ k : ℕ, Λ.reading n = k • Λ.δ_τ :=
  ⟨n, by rw [Λ.reading_eq, nsmul_eq_mul]⟩

/-- **Lattice spacing**: consecutive events differ by exactly `δ_τ`.  This is the
content the floor `Δτ ≥ δ_τ` does not give — the step is `δ_τ`, not merely
above it. -/
theorem reading_step_eq (n : ℕ) : Λ.reading (n + 1) - Λ.reading n = Λ.δ_τ := by
  rw [Λ.reading_eq, Λ.reading_eq]; push_cast; ring

/-- **Floor recovered**: any two distinct readings differ by at least `δ_τ`.
This is the `tau_ent_minimum_step` floor, now a corollary of the lattice rather
than an independent hypothesis. -/
theorem reading_min_step {m n : ℕ} (hmn : m < n) :
    Λ.δ_τ ≤ Λ.reading n - Λ.reading m := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
    have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  rw [Λ.reading_eq, Λ.reading_eq]
  nlinarith [Λ.δ_τ_pos]

/-- The reading is strictly increasing in the event index: the clock never
stalls or reverses.  Hence it is an order embedding `ℕ ↪ ℝ` with discrete
image. -/
theorem reading_strictMono : StrictMono Λ.reading := by
  intro a b hab
  rw [Λ.reading_eq, Λ.reading_eq]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hab) Λ.δ_τ_pos

/-- The reading is injective: distinct events read distinct times. -/
theorem reading_injective : Function.Injective Λ.reading :=
  Λ.reading_strictMono.injective

end EntropicTimeLadder

/-- **Landauer time quantum constructor.** The ladder with quantum
`δ_τ = k_B·log 2 / ℏ` — the same value `tau_ent_minimum_step` produces.  The
quantum is therefore derived from the Landauer bit, not chosen freely. -/
def EntropicTimeLadder.ofLandauerQuantum (ℏ : ℝ) (hℏ : 0 < ℏ) :
    EntropicTimeLadder where
  δ_τ := kB * Real.log 2 / ℏ
  δ_τ_pos := div_pos (mul_pos kB_pos (Real.log_pos (by norm_num))) hℏ
  reading n := (n : ℝ) * (kB * Real.log 2 / ℏ)
  reading_eq _ := rfl

/-- The lattice spacing of the Landauer ladder equals the
`tau_ent_minimum_step` floor `k_B·log 2 / ℏ`: the per-event step is exactly the
worldline floor, so the lattice does not introduce a second, looser quantum. -/
theorem ladder_step_eq_landauer_floor (ℏ : ℝ) (hℏ : 0 < ℏ) :
    (EntropicTimeLadder.ofLandauerQuantum ℏ hℏ).δ_τ = kB * Real.log 2 / ℏ := rfl

/-! ## §2 — Page–Wootters physical-state ladder

The lattice defined on genuine Wheeler–DeWitt physical states: each ladder state
is a kernel element of a `HamiltonianConstraint` (`H_total|Ψ⟩ = 0`).  The
quantized readings are then read off physical states, not an external
parameter. -/

/-- **Quantized relational clock.** A Page–Wootters constraint together with an
`ℕ`-indexed ladder of physical states and an entropic-time lattice reading them.
The reading lattice (`ladder`) supplies the quantization; the constraint
supplies the relational (physical-state) content. -/
structure QuantizedRelationalClock (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The Page–Wootters Hamiltonian constraint `H_total|Ψ⟩ = 0`. -/
  constraint : HamiltonianConstraint H
  /-- The entropic-time lattice read off the ladder. -/
  ladder : EntropicTimeLadder
  /-- The ladder of clock states, one per irreversible event. -/
  clockState : ℕ → H
  /-- Every ladder state is physical (a kernel element of the constraint). -/
  clockState_physical : ∀ n, constraint.IsPhysical (clockState n)

namespace QuantizedRelationalClock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (Q : QuantizedRelationalClock H)

/-- The relational time read off the `n`-th physical state. -/
def relationalTime (n : ℕ) : ℝ := Q.ladder.reading n

/-- The relational clock starts at zero. -/
@[simp] theorem relationalTime_zero : Q.relationalTime 0 = 0 :=
  Q.ladder.reading_zero

/-- **Quantization on physical states** (`τ ∈ δ·ℕ`): every relational reading on
a Page–Wootters physical state is an integer multiple of the quantum. -/
theorem relationalTime_mem_lattice (n : ℕ) :
    ∃ k : ℕ, Q.relationalTime n = k • Q.ladder.δ_τ :=
  Q.ladder.reading_mem_lattice n

/-- **Per-event advance**: between consecutive physical states the relational
clock advances by exactly the quantum `δ_τ`. -/
theorem relationalTime_step_eq (n : ℕ) :
    Q.relationalTime (n + 1) - Q.relationalTime n = Q.ladder.δ_τ :=
  Q.ladder.reading_step_eq n

/-- **Floor on physical states**: distinct physical states are separated by at
least the quantum `δ_τ` — the Page–Wootters realisation of
`tau_ent_minimum_step`. -/
theorem relationalTime_min_step {m n : ℕ} (hmn : m < n) :
    Q.ladder.δ_τ ≤ Q.relationalTime n - Q.relationalTime m :=
  Q.ladder.reading_min_step hmn

/-- The relational time strictly increases along the physical-state ladder. -/
theorem relationalTime_strictMono : StrictMono Q.relationalTime :=
  Q.ladder.reading_strictMono

end QuantizedRelationalClock

/-- **Non-vacuity witness.** The trivial constraint (`H_total := 0`, every state
physical) has a Landauer-quantum clock on `EuclideanSpace ℂ (Fin 1)`.  The
ladder states are the zero vector — minimal, used only to inhabit the structure;
the quantization content is in `ladder`, independent of the chosen states. -/
def landauerQuantizedClock (ℏ : ℝ) (hℏ : 0 < ℏ) :
    QuantizedRelationalClock (EuclideanSpace ℂ (Fin 1)) where
  constraint := HamiltonianConstraint.trivial _
  ladder := EntropicTimeLadder.ofLandauerQuantum ℏ hℏ
  clockState _ := 0
  clockState_physical _ := (HamiltonianConstraint.trivial _).isPhysical_zero

/-! ## §3 — A concrete discrete clock spectrum

A diagonal clock observable on `Fin 3` with eigenvalues `{0, g, 2g}`.  Its
spectrum is the lattice `g·ℕ` truncated to three levels — a discrete clock
spectrum realised concretely, in contrast to assuming one abstractly.  The
eigenvectors are the standard basis vectors. -/

/-- **Three-level clock observable**: the diagonal operator with entries
`0, g, 2g`. -/
def clockMatrix (g : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => (i : ℂ) * (g : ℂ))

/-- **Eigenvector equation**: the `k`-th standard basis vector is an eigenvector
of the clock observable with eigenvalue `k·g`. -/
theorem clockMatrix_eigenvector (g : ℝ) (k : Fin 3) :
    (clockMatrix g).mulVec (fun i => if i = k then (1 : ℂ) else 0)
      = ((k : ℂ) * (g : ℂ)) • (fun i => if i = k then (1 : ℂ) else 0) := by
  funext i
  rw [clockMatrix, Matrix.mulVec_diagonal]
  by_cases h : i = k
  · subst h; simp
  · simp [Pi.smul_apply, smul_eq_mul, h]

/-- **Spectrum in the lattice**: each eigenvalue `k·g` of the clock observable is
an integer multiple of the quantum `g` — the discrete spectrum lies on `g·ℕ`. -/
theorem clockMatrix_eigenvalue_lattice (g : ℝ) (k : Fin 3) :
    ((k : ℕ) : ℝ) * g = (k : ℕ) • g :=
  (nsmul_eq_mul _ _).symm

/-! ## §4 — The n-level entropic-time operator

The 3-level `clockMatrix` of §3 is the truncation to three events of a single
`n`-level family.  For each `n`, `entropicTimeOperator g n` is the diagonal
observable on `Fin n` whose eigenvalues are the first `n` lattice points
`0, g, 2g, …, (n-1)·g`: a discrete spectrum with **uniform gap `g`**.  The
3-level observable is the case `n = 3` (`clockMatrix_eq_entropicTimeOperator`),
and for the Landauer quantum the gap is `k_B·log 2 / ℏ`
(`entropicTimeOperator_gap_landauer`).

This generalises the discrete-spectrum witness from a fixed three levels to an
arbitrary event count.  It is still a layer-1 statement: the operator is
*exhibited*, and the discreteness of its spectrum is a property of the chosen
diagonal observable, not derived from `H_total`.  The lattice-from-dynamics
question (does continuous unitary evolution force a discrete clock spectrum?)
remains open and is not addressed here. -/

/-- **n-level entropic-time operator**: the diagonal observable on `Fin n` with
eigenvalues `k·g`, `k = 0, …, n-1`.  Generalises the 3-level `clockMatrix` to an
arbitrary number of events. -/
def entropicTimeOperator (g : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun k => (k : ℂ) * (g : ℂ))

/-- The 3-level `clockMatrix` is the `n = 3` member of the family. -/
theorem clockMatrix_eq_entropicTimeOperator (g : ℝ) :
    clockMatrix g = entropicTimeOperator g 3 := rfl

/-- **Eigenvector equation**: the `k`-th standard basis vector is an eigenvector
of `entropicTimeOperator g n` with eigenvalue `k·g`.  All `n` eigenpairs are
exhibited explicitly, so the spectrum contains every lattice point `{k·g : k < n}`. -/
theorem entropicTimeOperator_eigenvector (g : ℝ) {n : ℕ} (k : Fin n) :
    (entropicTimeOperator g n).mulVec (fun i => if i = k then (1 : ℂ) else 0)
      = ((k : ℂ) * (g : ℂ)) • (fun i => if i = k then (1 : ℂ) else 0) := by
  funext i
  rw [entropicTimeOperator, Matrix.mulVec_diagonal]
  by_cases h : i = k
  · subst h; simp
  · simp [Pi.smul_apply, smul_eq_mul, h]

/-- The diagonal entries — the eigenvalues — of `entropicTimeOperator g n` are
exactly the lattice points `k·g`. -/
theorem entropicTimeOperator_diagonal (g : ℝ) {n : ℕ} (k : Fin n) :
    entropicTimeOperator g n k k = (k : ℂ) * (g : ℂ) := by
  rw [entropicTimeOperator, Matrix.diagonal_apply_eq]

/-- **Spectrum in the lattice**: each eigenvalue `k·g` is an integer multiple of
the quantum `g` — the discrete spectrum lies on `g·ℕ`, for every level count. -/
theorem entropicTimeOperator_eigenvalue_lattice (g : ℝ) {n : ℕ} (k : Fin n) :
    ((k : ℕ) : ℝ) * g = (k : ℕ) • g :=
  (nsmul_eq_mul _ _).symm

/-- **Uniform gap**: consecutive eigenvalues differ by exactly the quantum `g`.
The spectrum is an arithmetic progression of common difference `g`, independent
of the level — the discrete gap the floor theorem bounds below. -/
theorem entropicTimeOperator_gap (g : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * g - (k : ℝ) * g = g := by
  push_cast; ring

/-- **The gap is the Landauer quantum.** With `δ = k_B·log 2 / ℏ` the uniform
level spacing of the n-level operator is exactly the entropic-time quantum
`tau_ent_minimum_step` produces — the same `δ_τ` encoded in
`EntropicTimeLadder.ofLandauerQuantum`. -/
theorem entropicTimeOperator_gap_landauer (ℏ : ℝ) (hℏ : 0 < ℏ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * (EntropicTimeLadder.ofLandauerQuantum ℏ hℏ).δ_τ
      - (k : ℝ) * (EntropicTimeLadder.ofLandauerQuantum ℏ hℏ).δ_τ
      = kB * Real.log 2 / ℏ := by
  show ((k + 1 : ℕ) : ℝ) * (kB * Real.log 2 / ℏ)
    - (k : ℝ) * (kB * Real.log 2 / ℏ) = kB * Real.log 2 / ℏ
  push_cast; ring

end Physlib.QuantumMechanics.RelationalTime.QuantizedTime

end

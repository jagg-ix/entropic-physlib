/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Badiali quantum diffusion as the Einstein Brownian template — bits per path-cell

Port of the complex-action/entropic-time analysis from
`/Users/macbookpro/Downloads/paths-bits-eins.md` REPLYID
20260519-017.

**Einstein's 1905 Brownian-motion logic** is the template:

  `microscopic random paths
   → macroscopic diffusion (D)
   → measurable transport coefficient
   → thermodynamic interpretation`.

Quantitatively: `⟨x²⟩ = 2·D·t` (1D) or `⟨r²⟩ = 2·d·D·t` (in
`d` dimensions), with the Stokes–Einstein relation
`D = k_B·T / (6πη·a)` connecting `D` to the viscosity `η`.

**Badiali 2005's primary irreversible diffusion** (paper Eq. 3)

  `−∂_t φ + D·Δφ − u·φ/ℏ = 0`

has the **same Einsteinian skeleton**, but with a *quantum*
diffusion coefficient

  `D_q = ℏ / (2m)`

instead of `D = k_B·T / (6πη·a)`.  Substituting:

  `⟨r²⟩ = 2·d·D_q·t = (d·ℏ·t) / m`.

In 1D this collapses to the Badiali postulate
`(Δx)² / Δt = ℏ / m` exactly — the *origin* of the quantum
mean-square displacement.

This file formalises the **Einstein-template content** of
Badiali's quantum diffusion in three pieces:

1. The **mean-square displacement** `⟨r²⟩(t) := 2·d·D_q·t`.
2. The **information growth** `I(t) ∼ (d/2) · log₂(2·d·D_q·t / ℓ²)`
   from spatial-cell counting.
3. The **time-per-bit** `t_bit := m·ℓ²/ℏ` — the elementary
   time-scale at which one distinguishable quantum path-bit is
   produced.

**Physical reading**: heavier systems (large `m`) produce
distinguishable quantum path bits more slowly; quantum bit
*generation* takes time `t_bit = m·ℓ²/ℏ`, inversely proportional
to `ℏ`.

## Contents

### §1 — Badiali quantum diffusion coefficient

* `badialiQuantumDiffusionCoeff ℏ m := ℏ / (2·m)`.
* `badialiQuantumDiffusionCoeff_pos`.

### §2 — Einstein mean-square displacement

* `einsteinMeanSquareDisplacement D t d := 2·d·D·t`.
* `badialiQuantumMeanSquareDisplacement ℏ m t d := d·ℏ·t / m`.
* `badialiMSD_eq_einsteinMSD` — the two coincide at `D = ℏ/(2m)`.

### §3 — Information growth from spatial-cell counting

* `numCellsExplored ℓ d t D := (Real.sqrt (2·d·D·t) / ℓ)^d` —
  Einstein-style.
* `infoBitsExplored ℓ d t D` — `log₂(N_cells)`.

### §4 — Time-per-bit

* `timePerQuantumBit m ℓ ℏ := m·ℓ² / ℏ`.
* `timePerQuantumBit_pos`.
* **`timePerQuantumBit_eq_msd_per_2D`** — the structural
  identification `t_bit = ℓ² / (2·D_q)`.

## References

* Einstein 1905 *Ann. Phys.* 17, 549 — Brownian motion.
* Badiali 2005 *J. Phys. A* 38, 2835 §2.1, §2.2 — discrete
  spacetime, diffusion coefficient `D = ℏ/(2m)`.
* Landauer 1961 — bits-as-degrees-of-freedom.
* Source: `/Users/macbookpro/Downloads/paths-bits-eins.md`
  REPLYID 20260519-017.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

open Real

/-! ## §1 — Badiali quantum diffusion coefficient `D_q = ℏ/(2m)` -/

/-- **Badiali quantum diffusion coefficient** `D_q := ℏ / (2·m)`.

Continuum limit of the Badiali discrete-spacetime postulate
`m·(Δx)² / Δt = ℏ`; identical to
`Physlib.QuantumMechanics.Schrodinger.badialiDiffusionCoeff` in
`BadialiForwardBackwardDecomposition.lean`.  Re-exposed here in the
Einstein-template form for the bits-per-path-cell construction. -/
def badialiQuantumDiffusionCoeff (ℏ m : ℝ) : ℝ := ℏ / (2 * m)

/-- **The quantum diffusion coefficient is strictly positive**. -/
theorem badialiQuantumDiffusionCoeff_pos {ℏ m : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m) :
    0 < badialiQuantumDiffusionCoeff ℏ m := by
  unfold badialiQuantumDiffusionCoeff
  exact div_pos hℏ (mul_pos two_pos hm)

/-! ## §2 — Einstein mean-square displacement `⟨r²⟩ = 2·d·D·t` -/

/-- **Einstein mean-square displacement**:

  `⟨r²⟩(t) := 2·d·D·t`.

For Brownian motion in `d` spatial dimensions with diffusion
coefficient `D`, the mean-square displacement grows linearly with
time (Einstein 1905). -/
def einsteinMeanSquareDisplacement (D t : ℝ) (d : ℕ) : ℝ :=
  2 * (d : ℝ) * D * t

/-- **Badiali quantum mean-square displacement**:

  `⟨r²⟩_q(t) := d·ℏ·t / m`.

Specialisation of the Einstein formula at the Badiali quantum
diffusion coefficient `D = ℏ/(2m)`. -/
def badialiQuantumMeanSquareDisplacement (ℏ m t : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * ℏ * t / m

/-- **The Badiali quantum MSD is the Einstein MSD at `D = ℏ/(2m)`**.

  `badialiQuantumMeanSquareDisplacement ℏ m t d
    = einsteinMeanSquareDisplacement (ℏ/(2m)) t d`. -/
theorem badialiMSD_eq_einsteinMSD
    {ℏ m t : ℝ} (d : ℕ) (hm : m ≠ 0) :
    badialiQuantumMeanSquareDisplacement ℏ m t d
      = einsteinMeanSquareDisplacement (badialiQuantumDiffusionCoeff ℏ m) t d := by
  unfold badialiQuantumMeanSquareDisplacement einsteinMeanSquareDisplacement
        badialiQuantumDiffusionCoeff
  field_simp

/-- **1D specialisation**: `⟨x²⟩ / t = ℏ / m` — the **Badiali
discrete-spacetime postulate** at the continuum-limit MSD level.

In one spatial dimension, the Badiali quantum mean-square
displacement satisfies the exact discrete-spacetime relation
`(Δx)²/Δt = ℏ/m`. -/
theorem badialiMSD_1D_eq_hbar_over_m
    {ℏ m t : ℝ} (ht : t ≠ 0) (hm : m ≠ 0) :
    badialiQuantumMeanSquareDisplacement ℏ m t 1 / t = ℏ / m := by
  unfold badialiQuantumMeanSquareDisplacement
  push_cast
  field_simp

/-! ## §3 — Information growth from spatial-cell counting -/

/-- **Number of spatial cells explored** by Brownian/diffusion in
`d` dimensions with resolution `ℓ` after time `t`:

  `N_cells(t) := (√⟨r²⟩ / ℓ)^d ≈ (√(2·d·D·t) / ℓ)^d`.

Each cell is a `ℓ`-sized region of physical space; `N_cells`
counts how many such cells are reached by the diffusing
particle. -/
def numCellsExplored (ℓ : ℝ) (d : ℕ) (D t : ℝ) : ℝ :=
  (Real.sqrt (2 * (d : ℝ) * D * t) / ℓ) ^ d

/-- **Information in bits** from cell counting:

  `I(t) := log(N_cells(t)) / log 2`.

The Landauer bits-from-nats conversion `bit := nat / ln 2`. -/
def infoBitsExplored (ℓ : ℝ) (d : ℕ) (D t : ℝ) : ℝ :=
  Real.log (numCellsExplored ℓ d D t) / Real.log 2

/-! ## §4 — Time-per-bit for Badiali quantum diffusion -/

/-- **Time per quantum path-bit** `t_bit := m·ℓ² / ℏ`.

The elementary time needed to resolve **one bit** of quantum
path distinction at spatial resolution `ℓ` for a particle of
mass `m`.  Heavy particles produce distinguishable quantum path
bits *slowly*; the ℏ dependence is inverse. -/
def timePerQuantumBit (m ℓ ℏ : ℝ) : ℝ := m * ℓ^2 / ℏ

/-- **Time-per-bit positivity**. -/
theorem timePerQuantumBit_pos
    {m ℓ ℏ : ℝ} (hm : 0 < m) (hℓ : ℓ ≠ 0) (hℏ : 0 < ℏ) :
    0 < timePerQuantumBit m ℓ ℏ := by
  unfold timePerQuantumBit
  apply div_pos _ hℏ
  apply mul_pos hm
  have : 0 ≤ ℓ^2 := sq_nonneg ℓ
  exact lt_of_le_of_ne this (Ne.symm (pow_ne_zero 2 hℓ))

/-- **Structural identification**: `t_bit = ℓ² / (2·D_q)`.

The time per quantum bit equals the time it takes a Brownian
particle with diffusion coefficient `D_q := ℏ/(2m)` to traverse
a cell of size `ℓ` — exactly Einstein's `⟨x²⟩ = 2·D·t` solved for
`t` at `⟨x²⟩ = ℓ²`.

**Algebraic core**: `ℓ² / (2 · (ℏ/(2m))) = ℓ² · m / ℏ`. -/
theorem timePerQuantumBit_eq_msd_per_2D
    {m ℓ ℏ : ℝ} (hℏ : ℏ ≠ 0) (hm : m ≠ 0) :
    timePerQuantumBit m ℓ ℏ = ℓ^2 / (2 * badialiQuantumDiffusionCoeff ℏ m) := by
  unfold timePerQuantumBit badialiQuantumDiffusionCoeff
  field_simp

/-- **Physical reading of `t_bit`**: at time `t_bit`, the
quantum mean-square displacement in 1D equals `ℓ²` — the system
has *just* explored one bit's worth of spatial cells.

  `badialiQuantumMeanSquareDisplacement ℏ m t_bit 1 = ℓ²`. -/
theorem badialiMSD_at_timePerQuantumBit_eq_ℓ_sq
    {m ℓ ℏ : ℝ} (hℏ : ℏ ≠ 0) (hm : m ≠ 0) :
    badialiQuantumMeanSquareDisplacement ℏ m (timePerQuantumBit m ℓ ℏ) 1
      = ℓ^2 := by
  unfold badialiQuantumMeanSquareDisplacement timePerQuantumBit
  push_cast
  field_simp

end Physlib.QuantumMechanics.Schrodinger

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic

/-!
# Spin density in density-functional theory

The exact spin-density algebra of open-shell DFT (Jacob & Reiher, *Spin in Density-Functional Theory*,
Int. J. Quantum Chem. **112**, 3661–3684 (2012), arXiv:1206.2234), §2.3.

An open-shell electron density splits into an `α`- and a `β`-spin part, `ρ = ρ_α + ρ_β` (Eq. 24), and the
**spin density** is their difference `Q = ρ_α − ρ_β` (Eq. 26). Integrating, `N = N_α + N_β` and the magnetic spin
quantum number is `M_S = ½(N_α − N_β)` (Eq. 29). Across the `2S+1` states of a spin multiplet the total density
is `M_S`-independent (Eq. 32) while the spin density scales **linearly** with `M_S`,
`Q^{M_S} = (M_S/S)·Q^{M_S=S}` (Eq. 33) — from which `Q^{−M_S} = −Q^{M_S}` and the spin density **vanishes for**
`M_S = 0` follow at once.

* **§A — the spin structure of the density** (Eqs. 24–29). `chargeDensity`, `spinDensity`, their inversion to
 `ρ_α, ρ_β`; `magneticSpinNumber`, the electron counts `N_α = N/2 + M_S`, `N_β = N/2 − M_S`.
* **§B — the `2S+1` multiplet** (Eqs. 32–33). `spinDensityAtMS` `= (M_S/S)Q_S`; `_highest`, `_antisymm`,
 `_vanishes_at_zero`, and the integrated `∫Q^{M_S} = 2M_S`.
* **§C — the many-electron total spin** (Eqs. 7, 19). `totalSpinSquaredEigenvalue` `S(S+1)ℏ²`; the spin-½
 special case `ŝ² = (3/4)ℏ²`.

**Scope.** These are the exact real-valued identities of the spin-density algebra — `ρ_α, ρ_β, Q, N_α,
N_β, M_S, S` as real numbers (densities at a point, or their integrals). The operator / many-electron
Hilbert-space content (Pauli matrices, the antisymmetrizer, the `Ŝ²` two-electron operator of Eq. 17, and the
Hohenberg–Kohn / Kohn–Sham functionals of §§3–4) is not formalized here.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.SpinDensityFunctionalTheory

/-! ## §A — the spin structure of the electron density (Eqs. 24–29) -/

/-- **The (total) electron density** `ρ = ρ_α + ρ_β` (Jacob–Reiher Eq. 24). -/
def chargeDensity (ρα ρβ : ℝ) : ℝ := ρα + ρβ

/-- **The spin density** `Q = ρ_α − ρ_β` (Eq. 26): the excess of `α`-electrons at a point. -/
def spinDensity (ρα ρβ : ℝ) : ℝ := ρα - ρβ

/-- **[Recover the `α`-density] `ρ_α = ½(ρ + Q)`** — the spin-up density from the charge and spin densities. -/
theorem alphaDensity_from_charge_spin (ρα ρβ : ℝ) :
    ρα = (chargeDensity ρα ρβ + spinDensity ρα ρβ) / 2 := by
  unfold chargeDensity spinDensity; ring

/-- **[Recover the `β`-density] `ρ_β = ½(ρ − Q)`**. -/
theorem betaDensity_from_charge_spin (ρα ρβ : ℝ) :
    ρβ = (chargeDensity ρα ρβ - spinDensity ρα ρβ) / 2 := by
  unfold chargeDensity spinDensity; ring

/-- **The magnetic spin quantum number** `M_S = ½(N_α − N_β)` (Eq. 29), from the integrated spin density. -/
noncomputable def magneticSpinNumber (Nα Nβ : ℝ) : ℝ := (Nα - Nβ) / 2

/-- **[The integrated spin density is `2M_S`] `∫Q = N_α − N_β = 2M_S`** (Eq. 29). -/
theorem integratedSpinDensity_eq_two_magneticSpinNumber (Nα Nβ : ℝ) :
    spinDensity Nα Nβ = 2 * magneticSpinNumber Nα Nβ := by
  unfold spinDensity magneticSpinNumber; ring

/-- **The `α`-electron count** `N_α = N/2 + M_S` in terms of the total number `N` and `M_S`. -/
noncomputable def alphaCount (N MS : ℝ) : ℝ := N / 2 + MS

/-- **The `β`-electron count** `N_β = N/2 − M_S`. -/
noncomputable def betaCount (N MS : ℝ) : ℝ := N / 2 - MS

/-- **[The counts recover `N` and `M_S`] `N_α + N_β = N` and `½(N_α − N_β) = M_S`** — the electron numbers are
fixed by the total number and the magnetic spin quantum number. -/
theorem alphaCount_add_betaCount (N MS : ℝ) : alphaCount N MS + betaCount N MS = N := by
  unfold alphaCount betaCount; ring

theorem magneticSpinNumber_alphaCount_betaCount (N MS : ℝ) :
    magneticSpinNumber (alphaCount N MS) (betaCount N MS) = MS := by
  unfold magneticSpinNumber alphaCount betaCount; ring

/-! ## §B — the `2S+1` multiplet: the spin density scales linearly with `M_S` (Eqs. 32–33) -/

/-- **The spin density of the `M_S` state** `Q^{M_S} = (M_S/S)·Q^{M_S=S}` (Eq. 33): all `2S+1` members of a spin
multiplet share the total density (Eq. 32) and have spin densities of the *same functional form*, scaled by
`M_S/S`. -/
noncomputable def spinDensityAtMS (S MS QS : ℝ) : ℝ := (MS / S) * QS

/-- **[Highest-weight state] `Q^{M_S=S} = Q_S`** — at `M_S = S` the scaling factor is `1`. -/
theorem spinDensityAtMS_highest (S QS : ℝ) (hS : S ≠ 0) : spinDensityAtMS S S QS = QS := by
  unfold spinDensityAtMS; rw [div_self hS, one_mul]

/-- **[The spin density is antisymmetric in `M_S`] `Q^{−M_S} = −Q^{M_S}`** (Eq. 33) — the spin-up and spin-down
`M_S` states encode opposite spin densities. -/
theorem spinDensityAtMS_antisymm (S MS QS : ℝ) :
    spinDensityAtMS S (-MS) QS = -spinDensityAtMS S MS QS := by
  unfold spinDensityAtMS; ring

/-- **[The spin density vanishes for `M_S = 0`] `Q^{M_S=0} = 0`** (Eq. 33) — a state with zero `z`-projection of
the total spin has *no* spin density, even when the total spin `S ≠ 0`. -/
theorem spinDensityAtMS_vanishes_at_zero (S QS : ℝ) : spinDensityAtMS S 0 QS = 0 := by
  unfold spinDensityAtMS; simp

/-- **[The integrated spin density is `2M_S`]** — given the highest-weight normalization `∫Q_S = 2S`, the `M_S`
state has `∫Q^{M_S} = (M_S/S)·2S = 2M_S`, consistent with `M_S = ½∫Q` (Eq. 29). -/
theorem spinDensityAtMS_integral (S MS IQS : ℝ) (hS : S ≠ 0) (hIQS : IQS = 2 * S) :
    spinDensityAtMS S MS IQS = 2 * MS := by
  unfold spinDensityAtMS; rw [hIQS]; field_simp

/-! ## §C — the many-electron total spin (Eqs. 7, 19) -/

/-- **The `Ŝ²` eigenvalue** `S(S+1)ℏ²` (Eq. 19): the squared total spin of a state with spin quantum number
`S`. -/
def totalSpinSquaredEigenvalue (S ℏ : ℝ) : ℝ := S * (S + 1) * ℏ ^ 2

/-- **[Spin-½ gives `ŝ² = (3/4)ℏ²`] (Eq. 7)** — the one-electron special case `S = ½` of `S(S+1)ℏ²`: every
electron is a spin-½ particle. -/
theorem spinHalf_spinSquared (ℏ : ℝ) : totalSpinSquaredEigenvalue (1 / 2) ℏ = 3 / 4 * ℏ ^ 2 := by
  unfold totalSpinSquaredEigenvalue; ring

end Physlib.QuantumMechanics.SpinDensityFunctionalTheory

end

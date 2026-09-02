/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-!
# MIW Ehrenfest theorem and Heisenberg-type uncertainty (Hall–Deckert–Wiseman 1402.6144, §IV.A, §IV.F)

Extends `SciamaAdSCPTManyInteractingWorlds` (which already has the mutual-repulsion zero-point energy) with the
two remaining "quantum phenomena as generic MIW effects" of Hall–Deckert–Wiseman that are cleanly algebraic:

**Ehrenfest theorem (translation invariance, §IV.A).**  The interworld potential
`U_N = (ℏ²/8m) Σ [1/(x_{n+1}−x_n) − 1/(x_n−x_{n−1})]²` depends only on world *gaps*, hence is translation
invariant, `U_N(x + y·𝟙) = U_N(x)`.  Differentiating at `y = 0` gives `Σ_n ∂U_N/∂x_n = 0`: the total interworld
force vanishes.  So the mean momentum obeys only the *external* force,
`d⟨p⟩_N/dt = −⟨∇V⟩_N` (Eq. ehrenfest) — for any `N`, the MIW Ehrenfest theorem.

* `total_interworld_force_zero` — the per-world force `σ(n+1) − σ(n)` telescopes to a vanishing boundary
  difference: the internal forces cancel (translation invariance).
* `ehrenfest_mean_momentum` — with the internal force cancelled, the mean-momentum rate is exactly `−⟨∇V⟩_N`.

**Heisenberg-type uncertainty (§IV.F).**  The nonclassical momentum
`p^{nc}_n = (ℏ/2)[1/(x_{n+1}−x_n) − 1/(x_n−x_{n−1})]` has `⟨p^{nc}⟩_N = 0`
(`nonclassicalMomentum_average_zero`), and the energy bound rewrites as a Heisenberg-type relation with the MIW
uncertainty bound `Δx·Δp^{nc} ≥ (ℏ/2)·(N−1)/N`:

* `heisenbergBound_pos` — the bound is positive (`N ≥ 2`).
* `heisenbergBound_lt_quantum` — it lies strictly below the quantum bound `ℏ/2`.
* `heisenbergBound_mono` — it increases with `N`, tending to the exact Heisenberg bound `ℏ/2` as `N → ∞` — the
  quantum uncertainty relation recovered in the many-worlds limit.

So the same `(N−1)/N` factor that governs the MIW zero-point energy governs its uncertainty bound: both the
Heisenberg relation and the zero-point energy of quantum mechanics emerge, in the `N → ∞` limit, from the finite
interacting worlds.

Honest scope: the internal-force cancellation (translation invariance), the Ehrenfest mean-momentum identity,
and the `(N−1)/N` uncertainty/zero-point factor.  The full dynamical `⟨φ⟩_N` averages, wavepacket spreading, and
barrier tunneling are the paper's numerical/analytic content, contextualized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwEhrenfestHeisenberg

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-! ## A. Ehrenfest theorem: translation invariance -/

/-- The per-world interworld force `σ(n+1) − σ(n)` of a translation-invariant potential (which depends only on
world gaps `σ`). -/
def interworldForce (σ : ℕ → ℝ) (n : ℕ) : ℝ := σ (n + 1) - σ n

/-- **[Ehrenfest: internal forces cancel] `Σ_n interworldForce = 0`.**  Translation invariance of `U_N` makes the
total interworld force telescope to a vanishing boundary difference (`σ_0 = σ_N = 0` from `x_0 = −∞`,
`x_{N+1} = ∞`) — so no net internal force acts on the world ensemble. -/
theorem total_interworld_force_zero (N : ℕ) (σ : ℕ → ℝ) (h0 : σ 0 = 0) (hN : σ N = 0) :
    ∑ n ∈ Finset.range N, interworldForce σ n = 0 := by
  simp only [interworldForce]
  rw [Finset.sum_range_sub σ N, h0, hN, sub_zero]

/-- The MIW mean-momentum rate: minus the mean external force, minus the mean interworld (internal) force. -/
def meanMomentumRate (N : ℕ) (meanGradV : ℝ) (internal : ℕ → ℝ) : ℝ :=
  -meanGradV - (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, internal n

/-- **[MIW Ehrenfest theorem] `d⟨p⟩_N/dt = −⟨∇V⟩_N`.**  With the internal (interworld) force cancelled by
translation invariance, the mean-momentum rate is exactly minus the mean external force — the classical
Ehrenfest law, for any number of worlds. -/
theorem ehrenfest_mean_momentum (N : ℕ) (meanGradV : ℝ) (σ : ℕ → ℝ) (h0 : σ 0 = 0) (hN : σ N = 0) :
    meanMomentumRate N meanGradV (interworldForce σ) = -meanGradV := by
  unfold meanMomentumRate
  rw [total_interworld_force_zero N σ h0 hN, mul_zero, sub_zero]

/-! ## B. Heisenberg-type uncertainty relation -/

/-- The MIW Heisenberg-type lower bound on `Δx·Δp^{nc}`: `(ℏ/2)·(N−1)/N`. -/
def heisenbergBound (N : ℕ) (hbar : ℝ) : ℝ := hbar / 2 * (((N : ℝ) - 1) / (N : ℝ))

/-- **[The MIW uncertainty bound is positive] `N ≥ 2`, `ℏ > 0`.** -/
theorem heisenbergBound_pos (N : ℕ) (hN : 2 ≤ N) {hbar : ℝ} (hb : 0 < hbar) :
    0 < heisenbergBound N hbar := by
  unfold heisenbergBound
  have hNpos : 0 < (N : ℝ) := by positivity
  have hN1 : 0 < (N : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  exact mul_pos (by positivity) (div_pos hN1 hNpos)

/-- **[Below the quantum bound] the MIW uncertainty bound is strictly less than `ℏ/2`.** -/
theorem heisenbergBound_lt_quantum (N : ℕ) (hN : 1 ≤ N) {hbar : ℝ} (hb : 0 < hbar) :
    heisenbergBound N hbar < hbar / 2 := by
  unfold heisenbergBound
  have hfac : ((N : ℝ) - 1) / (N : ℝ) < 1 := miwGroundEnergyFactor_lt_one N hN
  nlinarith [hfac, hb]

/-- **[Tends to the quantum Heisenberg bound] the MIW uncertainty bound increases with `N`.**  The same
`(N−1)/N` factor as the zero-point energy carries `(ℏ/2)(N−1)/N` up to the exact Heisenberg bound `ℏ/2` as
`N → ∞`. -/
theorem heisenbergBound_mono {N M : ℕ} (hN : 1 ≤ N) (h : N < M) {hbar : ℝ} (hb : 0 < hbar) :
    heisenbergBound N hbar < heisenbergBound M hbar := by
  unfold heisenbergBound
  have hfac : ((N : ℝ) - 1) / (N : ℝ) < ((M : ℝ) - 1) / (M : ℝ) := miwGroundEnergyFactor_mono hN h
  nlinarith [hfac, hb]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwEhrenfestHeisenberg

end

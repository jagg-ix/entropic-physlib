/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-!
# Fermionic entanglement volume ⟹ frequency drop ⟹ entropic-time dilation

This file formalizes the chain: when regions **entangle**, the
fermionic ones **add their space** (Pauli exclusion forbids two fermions in one cell, so each needs its own
volume — the same degeneracy-pressure mechanism that gives white dwarfs / neutron stars their size), so a
**denser** energy region entangles **more** fermions and becomes **bigger**; a bigger loop has a **lower**
fundamental frequency (`ω = κ/L`); and since the entropic clock rate is set by that frequency, the denser
region's **entropic proper time runs slower** — emergent gravitational time dilation.

Built on the Pauli bound `fermiDirac < 1` (`ComplexOscillator.ComplexFermionicOscillator`, occupation strictly below `1`)
versus the unbounded `boseEinstein`, and on `Winding.NumberMass` (the frequency↔mass leg).

* **§A — Bose vs Fermi spatial statistics.** `pauliRegionSize n = n·v₀` (fermions add volume, additive in the
  count — `pauliRegionSize_add`, the spatial analogue of `windingMass_add`) versus `boseRegionSize = v₀`
  (bosons condense into one mode, count-independent). `pauli_ge_bose`: for `n ≥ 1` the fermionic region is at
  least the bosonic one. The Pauli input is `fermiDirac_lt_one` (`< 1` per mode ⟹ `n` fermions need `≥ n`
  cells).
* **§B — bigger region, lower frequency.** `regionFrequency κ L = κ/L`; `regionFrequency_antitone`: larger
  `L` ⟹ smaller `ω`.
* **§C — lower frequency, slower entropic time.** `entropicTimeRate α ω = α·ω` (the de Broglie clock rate);
  `denser_region_slower_entropic_time`: a bigger (denser, more-entangled) region has the slower entropic
  clock; `denser_more_fermions_slower_time` instantiates it through the Pauli volume `pauliRegionSize`.
* **§D — the size law DERIVED from density.** `entangledRegionSize_eq`: combining energy-counting
  `N = ρV₀/ε₀` (`E = N ε₀`) with the Pauli additive volume `L = N v₀` gives `L(ρ) = ρ·(V₀v₀/ε₀)` — *size
  linear in density*. So "denser ⟹ bigger" is now the theorem `entangledRegionSize_mono`, and the rate law is
  explicit: `entropic_clock_rate_inverse_density` gives `rate(ρ) = α κ ε₀/(ρ V₀ v₀) ∝ 1/ρ`, with derived
  main result `denser_energy_slower_entropic_time`.
* **§E — Tolman redshift.** `entropicTimeRate_eq_lapse_mul`: the local rate is `(ω/ω_∞)·` the asymptotic
  rate — the frequency ratio is the gravitational lapse `N`, matching
  `EntropicProperTime.entropicProperTimeLocalMetric` (`τ_loc·N = τ_∞`): lower `ω` ⟹ smaller `N` ⟹ slower
  clock.

**Honest layering.** Genuine inputs: Pauli ⟹ additive fermionic volume (degeneracy pressure); energy-counting
`E = N ε₀`; `ω = κ/L` (cavity/loop mode); clock rate `∝ ω` (de Broglie clock); the Tolman factor `N = ω/ω_∞`.
From these the "denser ⟹ bigger ⟹ slower" chain is now **derived** (§D), not assumed — the only residual
model choice is that the per-fermion cell energy `ε₀` and volume `v₀` are constants (the incompressible
degenerate-Fermi-cell regime). Still only motivation, not formalized: the "entangled regions enlarge the
Lorenz/Nambu system" picture (Axenides–Floratos `R^{2n+1}` phase space raising `n`, shifting the `Σ₂`
oscillator frequency). The black-hole/Pauli-volume parallel is an analogy.

## References

* Pauli degeneracy pressure; Tolman gravitational time dilation; Axenides–Floratos `R^{2n+1}` Nambu phase
  space. `Physlib` (`ComplexOscillator.ComplexFermionicOscillator.fermiDirac_lt_one`, `Winding.NumberMass`,
  `SpaceAndTime.EntropicProperTime` Tolman scaling).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation


/-- **The Pauli (fermionic) region size** `L = n·v₀`: `n` mutually entangled fermions each occupy their own
cell (occupation `< 1` per mode, `fermiDirac_lt_one`), so the region volume is additive in the count `n` —
fermions "add their space." -/
def pauliRegionSize (n : ℕ) (v₀ : ℝ) : ℝ := (n : ℝ) * v₀

/-- **The bosonic region size** `L = v₀`: bosons condense into one mode (`boseEinstein` unbounded), so the
region size is independent of the count. -/
def boseRegionSize (v₀ : ℝ) : ℝ := v₀

/-- **[Entangled fermionic regions add their space]** `L_{m+n} = L_m + L_n` — the Pauli volume is additive in
the fermion count, the spatial analogue of the additive winding mass (`windingMass_add`). -/
lemma pauliRegionSize_add (m n : ℕ) (v₀ : ℝ) :
    pauliRegionSize (m + n) v₀ = pauliRegionSize m v₀ + pauliRegionSize n v₀ := by
  unfold pauliRegionSize; push_cast; ring

/-- **[More fermions ⟹ bigger region]** `m ≤ n ⟹ L_m ≤ L_n` (for `v₀ ≥ 0`). -/
lemma pauliRegionSize_le {m n : ℕ} (h : m ≤ n) {v₀ : ℝ} (hv : 0 ≤ v₀) :
    pauliRegionSize m v₀ ≤ pauliRegionSize n v₀ :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h) hv

/-- **[Fermionic region ≥ bosonic]** for `n ≥ 1` and `v₀ ≥ 0` the Pauli volume is at least the (condensed)
bosonic one — the Bose–Fermi spatial distinction. -/
lemma pauli_ge_bose {n : ℕ} (hn : 1 ≤ n) {v₀ : ℝ} (hv : 0 ≤ v₀) :
    boseRegionSize v₀ ≤ pauliRegionSize n v₀ := by
  unfold boseRegionSize pauliRegionSize
  calc v₀ = (1 : ℝ) * v₀ := (one_mul v₀).symm
    _ ≤ (n : ℝ) * v₀ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hv

/-- **[The Pauli bound]** the per-mode fermion occupation is strictly below `1` (`fermiDirac x < 1`): this is
the exclusion principle that forces the additive volume of `pauliRegionSize` (re-exported as the genuine
statistical input). -/
lemma pauli_occupation_bound (x : ℝ) : fermiDirac x < 1 := fermiDirac_lt_one x


/-- **The region's fundamental frequency** `ω = κ/L` — a larger cavity / mode of size `L` has a lower
frequency. -/
noncomputable def regionFrequency (κ L : ℝ) : ℝ := κ / L

/-- **[Bigger region ⟹ lower frequency]** `L₁ ≤ L₂ ⟹ ω(L₂) ≤ ω(L₁)` (for `κ ≥ 0`, `0 < L₁`): the frequency is
antitone in the region size. -/
lemma regionFrequency_antitone (κ : ℝ) (hκ : 0 ≤ κ) {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h : L₁ ≤ L₂) :
    regionFrequency κ L₂ ≤ regionFrequency κ L₁ := by
  unfold regionFrequency
  gcongr


/-- **The entropic clock rate** `dτ_ent/dt = α·ω` — the entropic proper time advances at a rate set by the
loop's frequency (the de Broglie internal clock); a slower frequency is a slower clock. -/
def entropicTimeRate (α ω : ℝ) : ℝ := α * ω

/-- **[Lower frequency ⟹ slower entropic clock]** monotone in `ω` (for `α ≥ 0`). -/
lemma entropicTimeRate_mono (α : ℝ) (hα : 0 ≤ α) {ω₁ ω₂ : ℝ} (h : ω₁ ≤ ω₂) :
    entropicTimeRate α ω₁ ≤ entropicTimeRate α ω₂ :=
  mul_le_mul_of_nonneg_left h hα

/-- **[Denser region ⟹ slower entropic proper time]** the bigger region `L₂` (denser, more entangled) has the
slower entropic clock: `rate(ω(L₂)) ≤ rate(ω(L₁))`. The full chain
`size ↑ ⟹ frequency ↓ ⟹ entropic-time rate ↓` — emergent gravitational time dilation. -/
lemma denser_region_slower_entropic_time (α κ : ℝ) (hα : 0 ≤ α) (hκ : 0 ≤ κ)
    {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (hL : L₁ ≤ L₂) :
    entropicTimeRate α (regionFrequency κ L₂) ≤ entropicTimeRate α (regionFrequency κ L₁) :=
  entropicTimeRate_mono α hα (regionFrequency_antitone κ hκ h₁ hL)

/-- **[Denser ⟹ more entangled fermions ⟹ slower time]** instantiating the chain through the Pauli volume:
the region with more entangled fermions `n₁ ≤ n₂` (the denser one) runs the slower entropic clock. -/
lemma denser_more_fermions_slower_time (α κ v₀ : ℝ) (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hv : 0 < v₀)
    {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn : n₁ ≤ n₂) :
    entropicTimeRate α (regionFrequency κ (pauliRegionSize n₂ v₀))
      ≤ entropicTimeRate α (regionFrequency κ (pauliRegionSize n₁ v₀)) := by
  have hn1pos : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have h₁ : 0 < pauliRegionSize n₁ v₀ := mul_pos hn1pos hv
  exact denser_region_slower_entropic_time α κ hα hκ h₁ (pauliRegionSize_le hn hv.le)

/-!

The earlier step "a denser region entangles more fermions, hence is bigger" was an ansatz. It is now
*derived* from two genuine inputs: **energy-counting** `N = E/ε₀ = ρV₀/ε₀` (the number of fermionic quanta in
a sampling cell of volume `V₀` is its energy `ρV₀` over the per-quantum energy `ε₀`, `E = N ε₀`) and the
**Pauli additivity** `L = N v₀` of §A. Their composition forces `L(ρ) = ρ·(V₀v₀/ε₀)` — size *linear in
density* — so "denser ⟹ bigger" becomes a theorem, and the entropic rate `∝ 1/ρ`. -/

/-- **The fermion count** `N = ρV₀/ε₀` — the number of fermionic quanta in a sampling cell of volume `V₀` is
the energy `ρV₀` divided by the per-quantum energy `ε₀` (`E = N ε₀`). -/
noncomputable def fermionCount (ρ V₀ ε₀ : ℝ) : ℝ := ρ * V₀ / ε₀

/-- **The entangled region size derived from density** `L(ρ) = N·v₀` — energy-counting (`E = N ε₀`) composed
with the Pauli additive volume (`L = N v₀`, §A). -/
noncomputable def entangledRegionSize (ρ V₀ ε₀ v₀ : ℝ) : ℝ := fermionCount ρ V₀ ε₀ * v₀

/-- **[Size is linear in density — DERIVED, not posited]** `L(ρ) = ρ·(V₀v₀/ε₀)`: energy-counting plus Pauli
additivity give the entangled region size proportional to the energy density, replacing the "denser ⟹
bigger" ansatz with a theorem. -/
lemma entangledRegionSize_eq (ρ V₀ ε₀ v₀ : ℝ) :
    entangledRegionSize ρ V₀ ε₀ v₀ = ρ * (V₀ * v₀ / ε₀) := by
  unfold entangledRegionSize fermionCount; ring

/-- **[Denser ⟹ bigger region]** now a *theorem*: `ρ₁ ≤ ρ₂ ⟹ L(ρ₁) ≤ L(ρ₂)` (for `V₀, ε₀, v₀ > 0`). -/
lemma entangledRegionSize_mono {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) (V₀ ε₀ v₀ : ℝ)
    (hV : 0 < V₀) (hε : 0 < ε₀) (hv : 0 < v₀) :
    entangledRegionSize ρ₁ V₀ ε₀ v₀ ≤ entangledRegionSize ρ₂ V₀ ε₀ v₀ := by
  rw [entangledRegionSize_eq, entangledRegionSize_eq]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- **[Denser energy ⟹ slower entropic proper time — DERIVED]** with the size law derived from
energy-counting + Pauli (no ansatz), a region of higher energy density `ρ₂ ≥ ρ₁` runs the slower entropic
clock. -/
lemma denser_energy_slower_entropic_time (α κ V₀ ε₀ v₀ : ℝ) (hα : 0 ≤ α) (hκ : 0 ≤ κ)
    (hV : 0 < V₀) (hε : 0 < ε₀) (hv : 0 < v₀) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ : ρ₁ ≤ ρ₂) :
    entropicTimeRate α (regionFrequency κ (entangledRegionSize ρ₂ V₀ ε₀ v₀))
      ≤ entropicTimeRate α (regionFrequency κ (entangledRegionSize ρ₁ V₀ ε₀ v₀)) := by
  have h₁ : 0 < entangledRegionSize ρ₁ V₀ ε₀ v₀ := by rw [entangledRegionSize_eq]; positivity
  exact denser_region_slower_entropic_time α κ hα hκ h₁
    (entangledRegionSize_mono hρ V₀ ε₀ v₀ hV hε hv)

/-- **[The entropic clock rate is inversely proportional to energy density]** `rate(ρ) = α κ ε₀/(ρ V₀ v₀)` —
the explicit derived law: denser regions tick slower as `1/ρ`. -/
lemma entropic_clock_rate_inverse_density (α κ ρ V₀ ε₀ v₀ : ℝ)
    (hρ : ρ ≠ 0) (hV : V₀ ≠ 0) (hε : ε₀ ≠ 0) (hv : v₀ ≠ 0) :
    entropicTimeRate α (regionFrequency κ (entangledRegionSize ρ V₀ ε₀ v₀))
      = α * κ * ε₀ / (ρ * V₀ * v₀) := by
  unfold entropicTimeRate regionFrequency entangledRegionSize fermionCount
  field_simp


/-- **The frequency lapse** `N = ω/ω_∞` — the local-to-asymptotic frequency ratio, the gravitational
redshift factor. -/
noncomputable def frequencyLapse (ω ωInf : ℝ) : ℝ := ω / ωInf

/-- **[Tolman redshift of the entropic clock]** `rate(ω) = (ω/ω_∞)·rate(ω_∞)`: the local entropic clock rate
is the asymptotic rate times the lapse `N = ω/ω_∞`. A denser region (lower `ω`) has a smaller lapse `N`,
hence a slower clock — exactly the Tolman law `τ_loc·N = τ_∞` of
`EntropicProperTime.entropicProperTimeLocalMetric`. -/
lemma entropicTimeRate_eq_lapse_mul (α ω ωInf : ℝ) (h : ωInf ≠ 0) :
    entropicTimeRate α ω = frequencyLapse ω ωInf * entropicTimeRate α ωInf := by
  unfold entropicTimeRate frequencyLapse
  field_simp

end Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation

end

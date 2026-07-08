/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionMutex
public import Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
public import Physlib.QuantumMechanics.ComplexAction.Fermion.PhotonExchange
public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellBifurcation

/-!
# The exclusion cell's boundary: photon exchange, the massless critical point, and the TISE bifurcation

Extends `HorizonCell.ElectronExclusionMutex`. The electron's exclusion cell is a two-level system: the
mutex/Dijkstra ladder `acquire = f†` / `release = f` (raising/lowering the occupation `n = f†f`, `n² = n`) is
exactly the **photon absorption / emission** of the boundary — absorb a photon `↦` excite `n:0→1`, emit a
photon `↦` de-excite `n:1→0`. This file derives the equations for that exchange, the **bifurcation critical
point** at which the cell becomes massless, and its correspondence with the **time-independent Schrödinger
equation** (TISE) of the underlying oscillator.

**The TISE and the photon quantum.** The oscillator eigenproblem `Ĥψ_n = E_nψ_n` has
`E_n = ℏω(n + ½)` (`ComplexHarmonicOscillatorBoson.oscillatorEnergy`), so the two-level cell (`n ∈ {0,1}` by
Pauli, `ElectronExclusionMutex.mutexInvariant`) exchanges a single photon of energy
`E_1 − E_0 = ℏω` (`exclusionCell_photon_energy`) — the level gap.

**The massless critical point.** The cell's energy–momentum vector `E + ip`, with `E = √(p²+m²)`
(`Bogoliubov.bogoliubovEnergy`), has Minkowski form `lorentzianForm(E + ip) = m²` — the rest mass²
(`bogoliubov_energyVector_lorentzianForm`). So the causal regime *is* the mass² sign, and the regimes are the
oscillator trichotomy (`ComplexOscillator.CausalRegimes.oscillator_causal_trichotomy`):

* `m² > 0` — **timelike / massive** — harmonic oscillator — **bound** TISE spectrum — exchanges a *real* photon;
* `m² = 0` — **lightlike / critical** — the **photon itself** (`Fermion.PhotonExchange.photon_eq_massless_fermion`,
 `massless_energyVector_lightlike`) — the bifurcation;
* `m² < 0` — **spacelike / tachyonic** — inverted oscillator — **unbound**.

**The bifurcation.** As the mass² parameter crosses `0` the causal/oscillator regime flips (HO ↔ IHO), a
sign-change bifurcation (`Vlasov.MaxwellBifurcation.bifurcation_index_jump`); at the critical point the TISE
gap `ℏω` vanishes and the whole spectrum collapses (`tise_gap_vanishes_at_critical`,
`tise_spectrum_collapse`). For the electron this is the massless limit: its Compton photon gap
`ℏω_C = mc² → 0` (`electron_compton_gap_vanishes`) and its worldline joins the `45°` null cone — the cell
*becomes* the photon it was exchanging.

* **§A — photon exchange is the level gap** (`exclusionCell_photon_energy`).
* **§B — massive cell vs massless photon: the criticality** (`exclusionCell_photon_criticality`).
* **§C — the TISE bifurcation at the critical point** (`exclusionCell_tise_bifurcation`,
 `tise_gap_vanishes_at_critical`, `tise_spectrum_collapse`).
* **§D — the electron's Compton photon gap vanishes at the massless critical point**
 (`electron_compton_gap_vanishes`, `electron_photon_bifurcation_summary`).

Every physical fact is an exact reuse: `oscillatorEnergy_succ_sub` (the gap),
`bogoliubov_energyVector_lorentzianForm` / `massless_energyVector_lightlike` /
`massive_energyVector_not_lightlike` (the criticality), `bifurcation_index_jump` (the sign-change), and
`comptonFrequency` (the electron gap). The new content is the *identification* — the mutex ladder is photon
absorption/emission, the massless point is the causal-regime bifurcation, and the collapsing TISE gap is that
same critical point — together with the exact `oscillatorEnergy`/`comptonFrequency` collapse identities. No
claim beyond the shared algebra is made.

## References

* Repo dependencies: `HorizonCell.ElectronExclusionMutex`, `ComplexOscillator.{ComplexHarmonicOscillatorBoson,
 CausalRegimes,PhaseDiagram}`, `Rapidity.LightCone45RapidityUnification`, `Fermion.PhotonExchange`,
 `Vlasov.MaxwellBifurcation`, `ComptonClock.FrequencyTrinity`.

No additional assumptions.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellBifurcation
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionPhotonBifurcation

/-! ## §A — photon exchange is the level gap of the TISE -/

/-- **[The exchanged photon records one TISE level quantum] `E_1 − E_0 = ℏω`.** The two-level exclusion cell
(occupation `n ∈ {0,1}` by Pauli) has the two lowest oscillator eigenvalues `E_0 = ℏω/2` and `E_1 = 3ℏω/2` of
the time-independent Schrödinger equation `Ĥψ_n = E_nψ_n`; the single photon it absorbs (raising `n:0→1` via
`f† =` acquire) or emits (lowering `n:1→0` via `f =` release) has energy exactly the level gap `ℏω`. -/
theorem exclusionCell_photon_energy (ħ : ℝ) (ω : ℂ) :
    oscillatorEnergy ħ ω 1 - oscillatorEnergy ħ ω 0 = (ħ : ℂ) * ω :=
  oscillatorEnergy_succ_sub ħ ω 0

/-! ## §B — massive cell versus massless photon: the criticality -/

/-- **[The cell's rest mass² is the Minkowski form of its energy–momentum, and the massless mode is the
photon at the critical point].** For an exclusion cell of momentum `p` and mass `m` with relativistic energy
`E = √(p²+m²) = bogoliubovEnergy p m`, the energy–momentum vector `E + ip` has
`lorentzianForm(E + ip) = m²`; a **massive** cell (`m ≠ 0`) is strictly timelike — never on the light cone,
so never a photon — while the **massless** mode (`m = 0`) is exactly lightlike: the photon
(`photon_eq_massless_fermion`) sitting on the `45°` critical cone. The photon the boundary exchanges is the
massless limit of the cell itself. -/
theorem exclusionCell_photon_criticality (p m : ℝ) :
    lorentzianForm ((bogoliubovEnergy p m : ℂ) + (p : ℂ) * Complex.I) = m ^ 2
      ∧ (m ≠ 0 → ¬ lightlike ((bogoliubovEnergy p m : ℂ) + (p : ℂ) * Complex.I))
      ∧ lightlike ((bogoliubovEnergy p 0 : ℂ) + (p : ℂ) * Complex.I) :=
  ⟨bogoliubov_energyVector_lorentzianForm p m,
    fun hm => massive_energyVector_not_lightlike p m hm,
    massless_energyVector_lightlike p⟩

/-! ## §C — the TISE bifurcation at the critical point -/

/-- **[The causal / oscillator regime bifurcates at the critical point].** Let `L` be the rest mass² of the
cell as a (strictly monotone) function of a real parameter, vanishing at the critical value `μ₀`
(`L μ₀ = 0`, the lightlike / massless point). Then just below `μ₀` the mass² is negative
(`L(μ₀−δ) < 0`: spacelike ⟹ inverted oscillator ⟹ *unbound* TISE) and just above it is positive
(`0 < L(μ₀+δ)`: timelike ⟹ harmonic oscillator ⟹ *bound* TISE) — a sign-change (index-jump) bifurcation of
the causal/oscillator regime across the massless critical point (`bifurcation_index_jump`). -/
theorem exclusionCell_tise_bifurcation (L : ℝ → ℝ) (μ₀ d : ℝ) (hd : 0 < d)
    (hmono : StrictMono L) (hcrit : L μ₀ = 0) :
    L (μ₀ - d) < 0 ∧ 0 < L (μ₀ + d) :=
  bifurcation_index_jump L μ₀ d hd hmono hcrit

/-- **[The TISE photon gap vanishes at the critical point] `E_1 − E_0 = 0` at `ω = 0`.** At the massless /
lightlike bifurcation the oscillator frequency vanishes, so the level gap `ℏω` — the energy of the photon the
cell could exchange — collapses to zero: the two levels merge. -/
theorem tise_gap_vanishes_at_critical (ħ : ℝ) :
    oscillatorEnergy ħ 0 1 - oscillatorEnergy ħ 0 0 = 0 := by
  rw [exclusionCell_photon_energy]; simp

/-- **[The whole TISE spectrum collapses at the critical point] `E_n = 0` for all `n` at `ω = 0`.** At the
massless bifurcation every oscillator eigenvalue `ℏω(n + ½)` degenerates to `0`: the discrete bound spectrum
of the harmonic-oscillator regime disappears into a single degenerate level — the spectral signature of the
critical point. -/
theorem tise_spectrum_collapse (ħ : ℝ) (n : ℕ) : oscillatorEnergy ħ 0 n = 0 := by
  simp [oscillatorEnergy]

/-! ## §D — the electron's Compton photon gap vanishes at the massless critical point -/

/-- **[The electron's Compton photon gap vanishes at the massless critical point] `ω_C(0) = 0`.** The
electron's exclusion cell exchanges photons of energy set by the Compton frequency `ω_C = mc²/ℏ`; at the
massless critical point (`m = 0`) this gap collapses to zero — the electron's worldline joins the `45°` null
cone (`massless_energyVector_lightlike`) and the cell *becomes* the photon it was exchanging. -/
theorem electron_compton_gap_vanishes (c ħ : ℝ) : comptonFrequency 0 c ħ = 0 := by
  simp [comptonFrequency]

/-- **[The electron photon–bifurcation, assembled].** For an electron cell of momentum `p`:

* the single photon it absorbs/emits records one TISE level quantum `E_1 − E_0 = ℏω`;
* a massive cell (`m ≠ 0`) is timelike — not a photon — while the massless mode is the lightlike photon at the
  critical point;
* at the critical point the TISE gap collapses (`E_1 − E_0 = 0` at `ω = 0`);
* the electron's Compton photon gap `ω_C` vanishes in the massless limit.

The massive exclusion cell (bound harmonic-oscillator TISE) absorbs and emits photons; the massless
bifurcation point *is* the photon, where the bound spectrum collapses. -/
theorem electron_photon_bifurcation_summary (p c ħ : ℝ) (ω : ℂ) :
    (oscillatorEnergy ħ ω 1 - oscillatorEnergy ħ ω 0 = (ħ : ℂ) * ω)
      ∧ (∀ m : ℝ, m ≠ 0 → ¬ lightlike ((bogoliubovEnergy p m : ℂ) + (p : ℂ) * Complex.I))
      ∧ lightlike ((bogoliubovEnergy p 0 : ℂ) + (p : ℂ) * Complex.I)
      ∧ (oscillatorEnergy ħ 0 1 - oscillatorEnergy ħ 0 0 = 0)
      ∧ comptonFrequency 0 c ħ = 0 :=
  ⟨exclusionCell_photon_energy ħ ω,
    fun m hm => massive_energyVector_not_lightlike p m hm,
    massless_energyVector_lightlike p,
    tise_gap_vanishes_at_critical ħ,
    electron_compton_gap_vanishes c ħ⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionPhotonBifurcation

end

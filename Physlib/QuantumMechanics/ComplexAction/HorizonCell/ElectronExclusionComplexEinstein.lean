/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionPhotonBifurcation
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-!
# The electron exclusion cell as a source of the complex Einstein field equations

Places the electron's exclusion cell (`HorizonCell.ElectronExclusionMutex` /
`ElectronExclusionPhotonBifurcation`) into the **complex Einstein field equation** already built in
`ComplexEinstein.FieldEquations`:

  `𝒢_μν = G_μν + i Λ_μν = κ (T_μν + i S_μν)`,

which splits (`complexEinsteinFieldEquation_iff`) into the real Einstein equation `G_μν = κ T_μν` (ordinary GR)
and the imaginary/entropic equation `Λ_μν = κ S_μν`. The exclusion cell is a **Dirac matter source of complex
mass** `m = m_R + i m_I` (`ComplexMassEinsteinEquations.complexMass`), and the two sectors are exactly its two
faces:

* the **real mass** `m_R` gives `Re E = m_R c²` (`complexEinsteinEnergy_re`) — the real stress `T` sourcing the
  ordinary curvature `G`; and the cell's Minkowski invariant is `lorentzianForm(E + ip) = m_R²`
  (`ElectronExclusionPhotonBifurcation.exclusionCell_photon_criticality`), the real-mass mass shell;
* the **imaginary / entropic mass** `m_I` gives `Im E = m_I c²` (`complexEinsteinEnergy_im`) — the entropic
  stress `S` sourcing the imaginary curvature `Λ`. This `Im E` is exactly the entropic gap of the cell's
  photon-exchange dissipation (`ComplexMassEinsteinEquations.dirac_entropic_gap_eq_imaginary_einstein`):
  the Cameron–Martin damping `e^{−tH_I/ℏ}` of the fermion line, the horizon imaginary action `S_I`.

**The bifurcation critical point is the reversible limit of the complex equation.** The massless / photon point
of `ElectronExclusionPhotonBifurcation` — where the TISE gap collapses and the cell becomes the photon it was
exchanging — is precisely `m_I = 0`: the imaginary Einstein energy vanishes
(`reversible_no_entropic`), so `S = 0`, `Λ = 0`, and the complex equation reduces to real GR `G = κT`. The
electron's Compton photon gap also vanishes there (`electron_compton_gap_vanishes`). **The bifurcation is the
vanishing of the imaginary Einstein sector.**

* **§A — the cell's real mass shell sources the real Einstein sector** (`exclusionCell_realEinstein_source`).
* **§B — the cell's photon-exchange entropy is the imaginary Einstein energy** (`exclusionCell_entropic_is_imaginaryEinstein`).
* **§C — the complex equation splits into real GR and entropic curvature** (`exclusionCell_complexEinstein_splits`).
* **§D — the bifurcation critical point is the reversible real-GR limit** (`exclusionCell_bifurcation_is_reversible`).
* **§E — assembled** (`electron_exclusion_complexEinstein_source`).

**Honest layering.** Every equation is exact reuse: `complexEinsteinEnergy_re`/`_im`,
`bogoliubov_energyVector_lorentzianForm`, `dirac_entropic_gap_eq_imaginary_einstein`,
`complexEinsteinFieldEquation_iff`, `reversible_no_entropic`, and `electron_compton_gap_vanishes`. The new
content is the *identification* — the exclusion cell's real mass is the real Einstein source `T/G`, its
photon-exchange entropic mass is the imaginary Einstein source `S/Λ`, and its massless bifurcation point is the
reversible collapse `Λ → 0`. The Einstein *tensor* `G` (`ComplexEinstein.EinsteinFieldEquationsPhysLean`) is
used as a given geometric object; no new gravitational dynamics is claimed.

## References

* Repo carriers: `HorizonCell.{ElectronExclusionMutex,ElectronExclusionPhotonBifurcation}`,
  `ComplexEinstein.{ComplexMassEinsteinEquations,FieldEquations}`,
  `Rapidity.LightCone45RapidityUnification`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionComplexEinstein


/-- **[The exclusion cell's real-mass shell is the real Einstein source].** The cell's energy–momentum vector
`E + ip` (with `E = √(p²+m_R²)`) has Minkowski invariant `lorentzianForm(E + ip) = m_R²` — the real-mass mass
shell — and the complex Einstein energy has real part `Re E = m_R c²`, the ordinary rest energy that sources
the real curvature `G_μν = κT_μν`. The observable (real) mass of the cell is the real Einstein source. -/
lemma exclusionCell_realEinstein_source (p m_R m_I c : ℝ) :
    lorentzianForm ((bogoliubovEnergy p m_R : ℂ) + (p : ℂ) * Complex.I) = m_R ^ 2
      ∧ (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2 :=
  ⟨bogoliubov_energyVector_lorentzianForm p m_R, complexEinsteinEnergy_re m_R m_I c⟩


/-- **[The cell's photon-exchange entropic gap is the imaginary Einstein energy] `m_I c² = Im E`.** The
imaginary / entropic mass `m_I` of the exclusion cell — carried by the Cameron–Martin damping `e^{−tH_I/ℏ}` of
its photon-exchange fermion line (the horizon imaginary action `S_I`) — is exactly the imaginary part of the
complex Einstein energy, the term that sources the imaginary curvature `Λ_μν`. -/
lemma exclusionCell_entropic_is_imaginaryEinstein (m_R m_I c : ℝ) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im :=
  dirac_entropic_gap_eq_imaginary_einstein m_R m_I c


/-- **[The exclusion cell's complex Einstein equation splits] `𝒢 = κ(T + iS) ⟺ (G = κT) ∧ (Λ = κS)`.** With the
cell as source, its real stress `T` (from `m_R`) sources the ordinary curvature `G` (standard GR) and its
entropic stress `S` (from `m_I`, the photon-exchange dissipation) sources the imaginary curvature `Λ`. -/
lemma exclusionCell_complexEinstein_splits {ι : Type*} (G Λ T S : Matrix ι ι ℝ) (κ : ℝ) :
    complexEinsteinFieldEquation G Λ T S κ ↔ G = κ • T ∧ Λ = κ • S :=
  complexEinsteinFieldEquation_iff G Λ T S κ


/-- **[The massless bifurcation is the reversible limit of the complex Einstein equation].** At the cell's
massless / photon bifurcation point the entropic mass vanishes (`m_I = 0`), so the imaginary Einstein energy
is zero (`reversible_no_entropic`) — no entropic stress `S`, hence `Λ = 0` and the complex equation collapses
to real GR `G = κT`. Simultaneously the electron's Compton photon gap `ω_C(0) = 0`
(`electron_compton_gap_vanishes`): the TISE-gap collapse of `ElectronExclusionPhotonBifurcation` *is* the
vanishing of the imaginary Einstein sector. -/
lemma exclusionCell_bifurcation_is_reversible (m_R c ħ : ℝ) :
    (complexEinsteinEnergy m_R 0 c).im = 0 ∧ comptonFrequency 0 c ħ = 0 :=
  ⟨reversible_no_entropic m_R c,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionPhotonBifurcation.electron_compton_gap_vanishes c ħ⟩


/-- **[The electron exclusion cell as a complex Einstein source, assembled].** For an exclusion cell of
momentum `p`, real mass `m_R`, entropic mass `m_I`:

* the real-mass shell `m_R²` and the real Einstein energy `m_R c²` are the real (`G/T`) source;
* the entropic mass gives `m_I c² = Im E`, the imaginary (`Λ/S`) source (the photon-exchange dissipation);
* the complex equation splits into real GR `G = κT` and entropic curvature `Λ = κS`;
* at the massless bifurcation (`m_I = 0`) the imaginary Einstein energy vanishes and the cell's Compton photon
  gap collapses — the reversible real-GR limit.

The electron's spacetime region is a Dirac cell of complex mass: real mass → ordinary curvature, entropic
photon-exchange mass → imaginary curvature, massless bifurcation → reversible GR. -/
lemma electron_exclusion_complexEinstein_source
    {ι : Type*} (p m_R m_I c ħ : ℝ) (G Λ T S : Matrix ι ι ℝ) (κ : ℝ) :
    lorentzianForm ((bogoliubovEnergy p m_R : ℂ) + (p : ℂ) * Complex.I) = m_R ^ 2
      ∧ (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2
      ∧ (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im
      ∧ (complexEinsteinFieldEquation G Λ T S κ ↔ G = κ • T ∧ Λ = κ • S)
      ∧ (complexEinsteinEnergy m_R 0 c).im = 0
      ∧ comptonFrequency 0 c ħ = 0 :=
  ⟨bogoliubov_energyVector_lorentzianForm p m_R,
    complexEinsteinEnergy_re m_R m_I c,
    dirac_entropic_gap_eq_imaginary_einstein m_R m_I c,
    complexEinsteinFieldEquation_iff G Λ T S κ,
    reversible_no_entropic m_R c,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionPhotonBifurcation.electron_compton_gap_vanishes c ħ⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionComplexEinstein

end

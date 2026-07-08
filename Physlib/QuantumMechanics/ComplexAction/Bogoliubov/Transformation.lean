/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.KramersKronig.EntropyHamiltonian

/-!
# The Bogoliubov transformation: coherence factors, gap dispersion, and the full Poincaré sphere

`Bogoliubov.BogoljubovPoincareActionConsistency` and `KramersKronig.EntropyHamiltonian` used the order
parameter `Δ = χ₀^* χ₁` only as a *phase* stand-in (the azimuthal Poincaré angle). This file
formalizes the **actual Bogoliubov transformation** — the BCS coherence factors `u, v` — and
shows it completes the picture:

* the **quasiparticle dispersion** `E = √(ξ² + |Δ|²)` is *exactly* Saito's/Dirac's gapped
  dispersion `photonDispersion` (`bogoliubov_energy_eq_photonDispersion`);
* `u² + v² = 1` (fermionic normalisation) and `u² − v² = ξ/E`
  (`bogoliubov_normalization`, `bogoliubov_uv_diff`);
* `u² − v² = ξ/E` is the **polar** Poincaré coordinate `S₃` of the quasiparticle spinor
  `(u, v)` (`bogoliubov_polar_stokesS3`) — the angle the previous files left undetermined; with
  the order-parameter phase (azimuth) this fixes the **full** point on the Poincaré sphere;
* at `Δ = 0` (no pairing) the transformation is trivial (`u² = 1, v² = 0`, the normal/reversible
  state); `Δ ≠ 0` (pairing) mixes the modes (`v² > 0`) — the irreversible / Kramers–Kronig sector.

## Main results

* `bogoliubovEnergy`, `bogoliubovU2`, `bogoliubovV2` — the Bogoliubov data.
* `bogoliubov_normalization` — `u² + v² = 1`.
* `bogoliubov_uv_diff` — `u² − v² = ξ/E`.
* `bogoliubov_energy_eq_photonDispersion` — `E = photonDispersion Δ 1 ξ` (Saito/Dirac gap dispersion).
* `bogoliubov_normal_state` — `Δ = 0, ξ > 0 ⟹ u² = 1, v² = 0`.
* `stokesS3_real_spinor`, `bogoliubov_polar_stokesS3` — `S₃ = u² − v² = ξ/E` (the polar Poincaré
  coordinate from the Bogoliubov coefficients).

## References

* N. N. Bogoljubov, Nuovo Cim. 7 (1958) 794; BCS theory. `Dirac.ConfinedPhotonDiracDispersion`,
  `Hopf.StokesSpinorIsomorphism`, `KramersKronig.EntropyHamiltonian` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
open Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-! ## §A — the Bogoliubov coherence factors and the gap dispersion -/

/-- **The Bogoliubov quasiparticle energy** `E = √(ξ² + Δ²)` (BCS gap dispersion). -/
def bogoliubovEnergy (ξ Δ : ℝ) : ℝ := Real.sqrt (ξ ^ 2 + Δ ^ 2)

/-- **The Bogoliubov coherence factor** `u² = ½(1 + ξ/E)`. -/
def bogoliubovU2 (ξ Δ : ℝ) : ℝ := (1 + ξ / bogoliubovEnergy ξ Δ) / 2

/-- **The Bogoliubov coherence factor** `v² = ½(1 − ξ/E)` (the quasiparticle occupation). -/
def bogoliubovV2 (ξ Δ : ℝ) : ℝ := (1 - ξ / bogoliubovEnergy ξ Δ) / 2

/-- **Fermionic normalisation** `u² + v² = 1`. -/
theorem bogoliubov_normalization (ξ Δ : ℝ) : bogoliubovU2 ξ Δ + bogoliubovV2 ξ Δ = 1 := by
  unfold bogoliubovU2 bogoliubovV2; ring

/-- **`u² − v² = ξ/E`** — the coherence difference (the polar Poincaré coordinate). -/
theorem bogoliubov_uv_diff (ξ Δ : ℝ) :
    bogoliubovU2 ξ Δ - bogoliubovV2 ξ Δ = ξ / bogoliubovEnergy ξ Δ := by
  unfold bogoliubovU2 bogoliubovV2; ring

/-- **The Bogoliubov quasiparticle dispersion is Saito's/Dirac's gap dispersion**:
`E = √(ξ² + Δ²) = photonDispersion Δ 1 ξ`. -/
theorem bogoliubov_energy_eq_photonDispersion (ξ Δ : ℝ) :
    bogoliubovEnergy ξ Δ = photonDispersion Δ 1 ξ := by
  unfold bogoliubovEnergy photonDispersion
  congr 1
  ring

/-- **Normal (unpaired) state**: at `Δ = 0`, `ξ > 0` the Bogoliubov transformation is trivial,
`u² = 1`, `v² = 0` (no mode mixing — the reversible normal state). -/
theorem bogoliubov_normal_state (ξ : ℝ) (hξ : 0 < ξ) :
    bogoliubovU2 ξ 0 = 1 ∧ bogoliubovV2 ξ 0 = 0 := by
  unfold bogoliubovU2 bogoliubovV2 bogoliubovEnergy
  have hsqrt : Real.sqrt (ξ ^ 2 + 0 ^ 2) = ξ := by
    rw [show ξ ^ 2 + 0 ^ 2 = ξ ^ 2 by ring]; exact Real.sqrt_sq hξ.le
  rw [hsqrt, div_self hξ.ne']
  norm_num

/-! ## §B — the polar Poincaré coordinate `S₃ = u² − v²` -/

/-- **`S₃` of a real spinor** `(a, b)` is `a² − b²`. -/
theorem stokesS3_real_spinor (a b : ℝ) :
    stokesS (Sum.inr 2) ![(a : ℂ), (b : ℂ)] = ((a ^ 2 - b ^ 2 : ℝ) : ℂ) := by
  rw [stokesS3_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.star_def,
    Complex.conj_ofReal]
  push_cast
  ring

/-- **The Bogoliubov quasiparticle's polar Poincaré coordinate** is `S₃ = u² − v² = ξ/E`. With
the order-parameter phase as the azimuth, this fixes the full point of the quasiparticle on the
Poincaré sphere — the polar angle the previous files (`Bogoliubov.BogoljubovPoincareActionConsistency`) left
undetermined. -/
theorem bogoliubov_polar_stokesS3 (ξ Δ : ℝ) (hu : 0 ≤ bogoliubovU2 ξ Δ)
    (hv : 0 ≤ bogoliubovV2 ξ Δ) :
    stokesS (Sum.inr 2)
        ![(Real.sqrt (bogoliubovU2 ξ Δ) : ℂ), (Real.sqrt (bogoliubovV2 ξ Δ) : ℂ)]
      = ((ξ / bogoliubovEnergy ξ Δ : ℝ) : ℂ) := by
  rw [stokesS3_real_spinor, Real.sq_sqrt hu, Real.sq_sqrt hv, bogoliubov_uv_diff]

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

end

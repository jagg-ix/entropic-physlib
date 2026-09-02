/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockAdSCFT

/-!
# AdS/CFT as the holographic BCJ double copy: gravity = gauge² across four levels

The gauge → gravity **double copy** — "gravity = gauge²" — is one squaring operation seen at four levels, and
AdS/CFT is its holographic realization tying the Sciama Fock/string arc to the gravity side:

* **Kinematic (Levi-Civita / tetrad).**  The metric is the *square* of the frame field, `g = EᵀηE`
  (`LeviCivita.TetradInvariant`, `properSeparationSq = xᵀ g x`): the graviton is the tetrad ⊗ tetrad, and the
  Levi-Civita connection is built from that squared metric (`Curvature.LeviCivitaFromMetric`,
  `LeviCivita.LeviCivitaUniqueness`).
* **Amplitude (BCJ).**  The gravity-side force is the gauge numerator squared, `(F V)²/D`
  (`Lorentz.ForceBCJDual.lorentzForceDual`), and the four-graviton amplitude is the double copy of gauge
  (`ChernSimons.GravitonDoubleCopy`).  The squaring is `T`-even — it *squares away* the velocity reversal
  (`ForceBCJDiamond`).
* **Worldsheet (KLT).**  Closed-string (gravity) amplitudes are the square of open-string (gauge) amplitudes;
  the closed-string modes are the double of the open-string Fock oscillators of this arc
  (`SciamaFockStringCasimir`), continued on the Nagao–Nielsen / Witten Chern–Simons contour
  (`SciamaFockNagaoNielsenZeta`, `ComplexDelta.Contour`).
* **Coupling (AdS/CFT).**  The ’t Hooft coupling *squares* the gauge coupling, `λ = g²N`, and this sets the
  bulk gravity scale (`adsRadius_gauge_doubleCopy`, `R⁴ = 2λα'²`): the gravity radius scales as the gauge
  coupling **squared**, while the string amplitude scale is **linear** in `g` — the single vs. double copy.

* `adsRadius_gauge_doubleCopy` — `R⁴ = 2·λ·α'²` with `λ = g²N`: the AdS (gravity) radius is `2·(gauge²·N)·α'²`.
* `stringLevel_doubleCopy` — `((mR)²)² = 32n²·g²N`: the string level's amplitude scale `(mR)² ∝ g` (single
  copy, linear in the gauge coupling) squares to the geometric scale `(mR)⁴ ∝ g²` (double copy).

So the same squaring that turns a gauge frame into a metric (`EᵀηE`), a gauge numerator into a gravity force
(`(FV)²/D`), and an open string into a closed one (KLT), turns the gauge coupling into the ’t Hooft coupling
`g²N` that AdS/CFT reads as the bulk gravitational radius — with the boundary `𝒩 = 4` Casimir `−N²/96`
(`SciamaFockAdSCFT.n4SYM_cylinderCasimir`) and the string level `Δ(Δ−4) = 4n√(2λ)`
(`stringLevel_adsDimension`) both governed by it.

Honest scope: the coupling-level identities (`λ = g²N`, `R⁴ = 2λα'²`, `(mR)⁴ = g²`-scaling).  The kinematic,
amplitude, and worldsheet double copies are the referenced modules; this is the holographic-coupling face that
ties them to the arc.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockBCJAdSCFT

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum

/-- **[Coupling double copy] `R⁴ = 2λα'²`, `λ = g²N`.**  The AdS (gravity) radius is `2·(gauge²·N)·α'²`: the
’t Hooft coupling `λ` squares the gauge coupling `g`, and the bulk gravitational scale is that square — the
holographic face of "gravity = gauge²". -/
theorem adsRadius_gauge_doubleCopy (R g N α : ℝ) (hR4 : R ^ 4 = 2 * N * g ^ 2 * α ^ 2) :
    R ^ 4 = 2 * tHooftCoupling g N * α ^ 2 ∧ tHooftCoupling g N = g ^ 2 * N :=
  ⟨adsRadius_fourth_tHooft R g N α hR4, rfl⟩

/-- **[String single ⟹ double copy] `((mR)²)² = 32n²·g²N`.**  The `n`-th string level's amplitude scale
`(mR)² ∝ g` is *linear* in the gauge coupling (the single copy); its square is the geometric scale
`(mR)⁴ = 32n²·g²N ∝ g²` (the double copy) — the same squaring, now on the holographic string spectrum. -/
theorem stringLevel_doubleCopy (m R n g N : ℝ) (hN : 0 ≤ N)
    (hbarrier : (m * R) ^ 2 = 4 * n * g * Real.sqrt (2 * N)) :
    ((m * R) ^ 2) ^ 2 = 32 * n ^ 2 * (g ^ 2 * N) := by
  rw [show ((m * R) ^ 2) ^ 2 = (m * R) ^ 4 from by ring,
    massRadius_fourth_lambda m R n g N hN hbarrier, tHooftCoupling]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockBCJAdSCFT

end

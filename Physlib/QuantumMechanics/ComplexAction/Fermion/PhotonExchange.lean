/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.ComplexPathIntegralSignatures

/-!
# Fermions exchanging photons: the QED vertex in the complex path integral

Constructs the basic QED process — two fermions exchanging a photon — inside the complex/Euclidean path
integral of the Wigner–Dunkl arc, using the boson/fermion (reflecting/absorbing) split of
`Dunkl.MatsubaraSpinor`. The fermions are Dirac modes (the **absorbing**, antiperiodic, *gapped*
sector, dispersion `E = bogoliubovEnergy(p, m) = √(p²+m²)`); the photon is the **reflecting**, periodic,
*massless* sector (`E = bogoliubovEnergy(p, 0) = |p|`, a bosonic *zero mode*). Each line is a complex
Hamiltonian `Ĥ = H_R − iH_I` whose Lorentzian propagator is `lorentzianPropagator`.

The physical content the formalization pins down:

* **§A — dispersions.** `photon_energy_eq_abs`: the photon energy is `|p|`; `photon_eq_massless_fermion`:
  the photon is the `m → 0` limit of the Dirac fermion.
* **§B — the photon line is reversible (unitary).** `photon_propagator_unitary`: a free photon has `H_I = 0`,
  so its propagator has modulus `1` — it has no entropy/Cameron–Martin damping. The fermion line is
  damped (`fermion_propagator_norm`).
* **§C — the exchange amplitude.** `exchange_modulus`: for the amplitude
  `U_fermion · U_photon · U_fermion`, the modulus is the **product of the two fermion Cameron–Martin
  weights** `e^{−tH_{I,1}/ℏ}·e^{−tH_{I,2}/ℏ}` — the photon drops out (pure phase), so *all* the
  irreversibility of a photon exchange is encoded in the fermion lines.
* **§D — masslessness is the bosonic zero mode.** `photon_zero_mode` / `fermion_no_zero_mode`: the photon's
  masslessness is the bosonic Matsubara zero mode `ω_0 = 0`, while the fermion has no zero mode
  (antiperiodic), i.e. the Dirac mass gap — the exchanged boson is exactly the gapless sector that mediates
  between the gapped fermion sectors.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.PhotonExchange

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-! ## §A — the photon and fermion complex Hamiltonians and their dispersions -/

/-- **The photon as a complex Hamiltonian**: a massless boson, reversible (`H_I = 0`), with the massless
dispersion `H_R = bogoliubovEnergy(p, 0) = |p|`. -/
noncomputable def photonHamiltonian (p : ℝ) : ComplexHamiltonian :=
  { H_R := bogoliubovEnergy p 0, H_I := 0, H_I_nonneg := le_rfl }

/-- **The fermion (Dirac mode) as a complex Hamiltonian**: dispersion `H_R = bogoliubovEnergy(p, m) =
√(p²+m²)` and a dissipative part `H_I ≥ 0` (the entropic/Cameron–Martin damping of the line). -/
noncomputable def fermionHamiltonian (p m HI : ℝ) (hI : 0 ≤ HI) : ComplexHamiltonian :=
  { H_R := bogoliubovEnergy p m, H_I := HI, H_I_nonneg := hI }

/-- **The photon energy is `|p|`** — the massless dispersion `bogoliubovEnergy(p, 0) = √(p²) = |p|`. -/
theorem photon_energy_eq_abs (p : ℝ) : (photonHamiltonian p).H_R = |p| := by
  simp [photonHamiltonian, bogoliubovEnergy, Real.sqrt_sq_eq_abs]

/-- **The photon is the `m → 0` limit of the Dirac fermion**: same reversible energy. -/
theorem photon_eq_massless_fermion (p HI : ℝ) (hI : 0 ≤ HI) :
    (photonHamiltonian p).H_R = (fermionHamiltonian p 0 HI hI).H_R := rfl

/-! ## §B — the photon line is reversible (unitary); the fermion line is damped -/

/-- **[Photon reversibility] A free photon's propagator is unitary** (`‖·‖ = 1`): with `H_I = 0` the
massless boson has no entropy/Cameron–Martin damping — a real photon propagates without dissipation. -/
theorem photon_propagator_unitary (p t ℏ : ℝ) :
    ‖lorentzianPropagator (photonHamiltonian p) t ℏ‖ = 1 := by
  rw [lorentzianPropagator_norm_is_damping]; simp [photonHamiltonian]

/-- **The fermion line includes the Cameron–Martin damping** `e^{−tH_I/ℏ}`. -/
theorem fermion_propagator_norm (p m HI t ℏ : ℝ) (hI : 0 ≤ HI) :
    ‖lorentzianPropagator (fermionHamiltonian p m HI hI) t ℏ‖ = Real.exp (-(t * HI / ℏ)) := by
  rw [lorentzianPropagator_norm_is_damping]; simp [fermionHamiltonian]

/-! ## §C — the photon-exchange amplitude -/

/-- **The fermion–photon–fermion exchange amplitude**: a photon line (reversible) between two fermion lines
(damped) — the basic QED single-photon-exchange diagram in the complex path integral. -/
noncomputable def photonExchangeAmplitude
    (pf1 pf2 pγ m HI1 HI2 t ℏ : ℝ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) : ℂ :=
  lorentzianPropagator (fermionHamiltonian pf1 m HI1 h1) t ℏ
    * lorentzianPropagator (photonHamiltonian pγ) t ℏ
    * lorentzianPropagator (fermionHamiltonian pf2 m HI2 h2) t ℏ

/-- **[Exchange] The dissipation of a photon exchange is entirely fermionic.** The modulus of the
single-photon-exchange amplitude is the **product of the two fermion Cameron–Martin weights**
`e^{−tH_{I,1}/ℏ}·e^{−tH_{I,2}/ℏ}`: the photon line contributes only a pure (unitary) phase, so all the
entropic damping comes from the fermion lines. -/
theorem exchange_modulus (pf1 pf2 pγ m HI1 HI2 t ℏ : ℝ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    ‖photonExchangeAmplitude pf1 pf2 pγ m HI1 HI2 t ℏ h1 h2‖
      = Real.exp (-(t * HI1 / ℏ)) * Real.exp (-(t * HI2 / ℏ)) := by
  unfold photonExchangeAmplitude
  rw [norm_mul, norm_mul, photon_propagator_unitary, mul_one,
    lorentzianPropagator_norm_is_damping, lorentzianPropagator_norm_is_damping]
  simp [fermionHamiltonian]

/-- **The exchange is reversible iff both fermion lines are**: for `t > 0`, `ℏ > 0` the amplitude has unit
modulus exactly when `H_{I,1} = H_{I,2} = 0` — only on-shell (lossless) fermions exchange a photon
unitarily; any fermion damping makes the whole exchange dissipative. -/
theorem exchange_unitary_iff (pf1 pf2 pγ m HI1 HI2 t ℏ : ℝ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2)
    (ht : 0 < t) (hℏ : 0 < ℏ) :
    ‖photonExchangeAmplitude pf1 pf2 pγ m HI1 HI2 t ℏ h1 h2‖ = 1 ↔ HI1 = 0 ∧ HI2 = 0 := by
  rw [exchange_modulus, ← Real.exp_add, Real.exp_eq_one_iff]
  have hc : 0 < t / ℏ := div_pos ht hℏ
  constructor
  · intro h
    have hsum : t * HI1 / ℏ + t * HI2 / ℏ = 0 := by linarith
    have e1 : 0 ≤ t * HI1 / ℏ := div_nonneg (mul_nonneg ht.le h1) hℏ.le
    have e2 : 0 ≤ t * HI2 / ℏ := div_nonneg (mul_nonneg ht.le h2) hℏ.le
    have hz1 : t * HI1 / ℏ = 0 := by linarith
    have hz2 : t * HI2 / ℏ = 0 := by linarith
    refine ⟨?_, ?_⟩
    · have := (div_eq_zero_iff.mp hz1).resolve_right hℏ.ne'
      exact (mul_eq_zero.mp this).resolve_left ht.ne'
    · have := (div_eq_zero_iff.mp hz2).resolve_right hℏ.ne'
      exact (mul_eq_zero.mp this).resolve_left ht.ne'
  · rintro ⟨rfl, rfl⟩; simp

/-! ## §D — masslessness is the bosonic zero mode; the fermion gap is antiperiodicity -/

/-- **[Photon = bosonic zero mode] The exchanged photon is the gapless (massless) bosonic Matsubara mode**
`ω_0 = 0`: the reflecting (even, periodic) sector has a static mode, which is the photon's masslessness. -/
theorem photon_zero_mode (β : ℝ) : matsubaraFreqBoson β 0 = 0 :=
  matsubaraFreqBoson_zero β

/-- **[Fermion gap = antiperiodicity] The fermion has no zero mode** `(2n+1)π/β ≠ 0`: the absorbing (odd,
antiperiodic) Dirac sector is gapped — the mass `m` in `bogoliubovEnergy(p, m)`. So a photon exchange is
the gapless bosonic line mediating between two gapped fermionic lines. -/
theorem fermion_no_zero_mode (β : ℝ) (hβ : β ≠ 0) (n : ℤ) :
    fermionicMatsubaraFreq β n ≠ 0 :=
  fermionicMatsubaraFreq_ne_zero β hβ n

end Physlib.QuantumMechanics.ComplexAction.Fermion.PhotonExchange

end

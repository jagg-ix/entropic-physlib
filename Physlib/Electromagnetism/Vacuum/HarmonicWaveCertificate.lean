/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Electromagnetism.Vacuum.HarmonicWave
meta import Zil

/-!
# Vacuum harmonic-wave criterion certificate

The vacuum electromagnetism layer already constructs a smooth monochromatic
potential and separately proves that it satisfies Maxwell's equations and is a
plane wave. This file combines those results into one criterion-level theorem
for the OpenWave EM-wave row.

The certificate is a free-field theorem. It does not prove photon quantization,
CAT/EPT emergence of electromagnetism, or empirical calibration of units.
-/

set_option autoImplicit false

@[expose] public section

namespace Electromagnetism.ElectromagneticPotential

/-- A nonzero-wave-number harmonic vacuum potential simultaneously solves the
source-free Maxwell equations and is a plane wave in its propagation direction. -/
theorem harmonicWaveX_maxwell_planeWave {d : ℕ}
    (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    IsExtrema 𝓕 (harmonicWaveX 𝓕 k E₀ φ) 0 ∧
      IsPlaneWave 𝓕 (harmonicWaveX 𝓕 k E₀ φ)
        ⟨Space.basis 0, by simp⟩ := by
  exact ⟨harmonicWaveX_isExtrema 𝓕 k hk E₀ φ,
    harmonicWaveX_isPlaneWave 𝓕 k hk E₀ φ⟩

/-- The Maxwell/plane-wave certificate exposes the exact transverse electric
field component of the harmonic solution. -/
theorem harmonicWaveX_transverse_electric_component {d : ℕ}
    (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ)
    (t : Time) (x : Space d.succ) (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ =
      E₀ i * Real.cos (k * 𝓕.c * t.val - k * x 0 + φ i) :=
  harmonicWaveX_electricField_succ 𝓕 k hk E₀ φ t x i

end Electromagnetism.ElectromagneticPotential

/- ZIL-BEGIN -/

zil attach Electromagnetism.ElectromagneticPotential.harmonicWaveX_maxwell_planeWave where
  formalizes @ "claim:a-smooth-nonzero-wave-number-harmonic-vacuum-potential-satisfies-source-free-maxwell-and-is-a-plane-wave",
  supported_by @ "lean:Electromagnetism.ElectromagneticPotential.harmonicWaveX_isExtrema",
  supported_by @ "lean:Electromagnetism.ElectromagneticPotential.harmonicWaveX_isPlaneWave",
  caveat @ "claim:this-is-a-free-field-maxwell-wave-certificate-not-photon-quantization-or-a-calibrated-emergence-theorem"

zil attach Electromagnetism.ElectromagneticPotential.harmonicWaveX_transverse_electric_component where
  formalizes @ "claim:the-harmonic-maxwell-wave-has-the-declared-transverse-cosine-electric-component"

zil_file_contract physlib.m9.harmonicMaxwellWave where
  promises "One theorem combining the existing source-free Maxwell and plane-wave proofs for the smooth harmonic vacuum potential, together with its exact transverse electric component."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Electromagnetism.ElectromagneticPotential.harmonicWaveX_isExtrema",
    "lean:Electromagnetism.ElectromagneticPotential.harmonicWaveX_isPlaneWave",
    "lean:Electromagnetism.ElectromagneticPotential.harmonicWaveX_electricField_succ"]
  forbids_substitutes ["photon quantization or a calibrated emergence theorem, this is a free-field Maxwell wave certificate",
    "CAT/EPT emergence of electromagnetism, which is not derived here"]
  witnessed_by [
    Electromagnetism.ElectromagneticPotential.harmonicWaveX_maxwell_planeWave,
    Electromagnetism.ElectromagneticPotential.harmonicWaveX_transverse_electric_component ]

/- ZIL-END -/

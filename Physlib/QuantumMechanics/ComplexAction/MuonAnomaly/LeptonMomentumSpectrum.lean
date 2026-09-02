/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity

/-!
# The lepton `g − 2` operating-point momentum spectrum from one rapidity

Closing the loop between the lepton mass hierarchy (`Winding.NumberMass`/`Particles.ChargedLeptonGenerations`) and the
`g − 2` operating-point rapidity (`MuonAnomaly.AnomalyRapidity`): the storage-ring **operating-point momentum** at which the
anomalous moment `a` satisfies the cancellation condition, for a particle of rest mass `m`, is

  `p = m/√a = m·sinh η = m/√(K²−1)`   (`momentum`, `momentum_eq_mass_mul_sinh`),

since `a = 1/sinh²η = K²−1` (the same Schmidt number `K = coth η`). At leading order the lepton anomaly is
universal (`a ≈ α/2π`), so the three charged leptons share one rapidity `η` (one `K`), and their operating-point
momenta scale with mass: `p_e : p_μ : p_τ = m_e : m_μ : m_τ`. For the muon `m_μ = 105.66 MeV`,
`a ≈ 1.166×10⁻³` gives `p_μ ≈ 3.094 GeV/c` — the actual ring momentum.

* **§A — the operating-point momentum.** `momentum m a = m/√a`; `momentum_eq_mass_mul_sinh`
  (`= m·sinh η`, the momentum-per-mass `sinh η = 1/√(K²−1)` is the rapidity), `momentum_pos`.
* **§B — the spectrum inherits the mass hierarchy.** `momentum_ratio`: `p₂/p₁ = m₂/m₁` (the common `√a`
  cancels) — the lepton operating-point momenta are in the same ratio as the masses, i.e. the same dimensionless
  number that is the internal-clock frequency ratio (`Winding.NumberMass`).

**Honest layering.** Exact relations: `p = m/√a = m·sinh η`, and `p₂/p₁ = m₂/m₁`. These are kinematic
consequences of the operating-point momentum condition (`a = 1/(γ²−1)`), tying the lepton masses, the `g − 2` anomaly,
and the Schmidt-number rapidity together. The anomaly *value* `a` is still QED + BSM (not predicted here);
what is predicted is the *relation* — each lepton's operating-point momentum from its mass and `a`, cross-checked by the
muon's `3.094 GeV/c`.

## References

* Muon `g − 2` operating-point momentum `p = m/√a`. `Physlib` (`MuonAnomaly.AnomalyRapidity.anomaly`/`schmidtNumber`,
  `Winding.NumberMass` lepton masses).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.LeptonMomentumSpectrum


/-- **The operating-point momentum** `p = m/√a` — the storage-ring momentum at which the electric-field spin
precession cancels, for a particle of rest mass `m` and anomalous moment `a`. -/
noncomputable def momentum (m a : ℝ) : ℝ := m / Real.sqrt a

/-- **[Operating-point momentum is `m·sinh η`]** `p = m·sinh η` — the momentum-per-mass is the rapidity sinh
(`sinh η = 1/√(K²−1)`, with `a = 1/sinh²η = K²−1`). -/
lemma momentum_eq_mass_mul_sinh (m η : ℝ) (hη : 0 < η) :
    momentum m (anomaly η) = m * Real.sinh η := by
  have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
  unfold momentum anomaly
  rw [show (1 : ℝ) / (Real.sinh η) ^ 2 = (1 / Real.sinh η) ^ 2 from by ring,
    Real.sqrt_sq (by positivity)]
  field_simp

/-- **[Operating-point momentum is positive]** `p > 0` for positive mass and anomaly. -/
lemma momentum_pos (m a : ℝ) (hm : 0 < m) (ha : 0 < a) : 0 < momentum m a := by
  unfold momentum
  positivity


/-- **[Operating-point momentum ratio = mass ratio]** `p₂/p₁ = m₂/m₁`: at the *same* anomaly `a` (universal at leading
order), the common `√a` cancels, so the lepton operating-point momenta are in the ratio of their masses — the same
dimensionless number that is the internal-clock frequency ratio (`Winding.NumberMass`). -/
lemma momentum_ratio (m₁ m₂ a : ℝ) (ha : 0 < a) :
    momentum m₂ a / momentum m₁ a = m₂ / m₁ := by
  unfold momentum
  rw [div_div_div_cancel_right₀]
  exact (Real.sqrt_pos.mpr ha).ne'

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.LeptonMomentumSpectrum

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition
public import Physlib.QuantumMechanics.Schrodinger.MadelungPolarDecomposition

/-!
# Bridge: Badiali forward–backward decomposition is a Madelung polar form

Companion to
`Physlib/QuantumMechanics/Schrodinger/BadialiForwardBackwardDecomposition.lean`
and
`Physlib/QuantumMechanics/Schrodinger/MadelungPolarDecomposition.lean`.

**The load-bearing identification**:

Badiali 2005 writes the complex wavefunction from a forward density
`φ > 0` and a backward density `φ̂ > 0` as

  `Ψ_Bd := exp(R_Bd + i·S_Bd)`

with `R_Bd := (1/2)·ln(φ·φ̂)` and `S_Bd := (1/2)·ln(φ̂/φ)`
(paper Eq. 34).

Madelung 1927 writes the wavefunction in polar form as

  `ψ_M := R · exp(i · S / ℏ)`

with amplitude `R ≥ 0` and phase `S`.

These are **the same object** under the identification

* `R    := √(φ · φ̂)`   = `exp(R_Bd)`,
* `S/ℏ  := S_Bd`        i.e.  `S := ℏ · S_Bd`.

This file makes that identification a Lean theorem.

## Why this matters

The previous Badiali file proved `|Ψ_Bd|² = φ·φ̂` (Born rule from
forward–backward decomposition) as a self-contained algebraic
identity.  The previous Madelung file proved `‖R·exp(i·S/ℏ)‖ = R`
and `madelungDensity = R²` (Born rule from Madelung polar form).
These two Born-rule statements look formally distinct but
**describe the same physics**.

The bridge theorems below **certify the equality** at primitive-statement level:
the Born rule from Badiali's discrete-spacetime forward–backward
ontology is the **same Born rule** that emerges from Madelung's
polar decomposition — they coincide on the nose.

This closes the interpretive gap "is `|Ψ_Bd|² = φ·φ̂` really the
Madelung Born rule or a *different* probabilistic claim?" with a
machine-checked: it is the same claim.

## Contents

* `badialiToMadelung φ φ_hat ℏ` — the Madelung wavefunction
  attached to a positive forward/backward pair at Planck scale `ℏ`.
* **`badialiToMadelung_density_eq`** — `madelungDensity = φ·φ̂`.
* **`badialiPsi_eq_madelungForm`** — `Ψ_Bd = R · exp(i·S/ℏ)`
  with `R = √(φ·φ̂)` and `S = ℏ · S_Bd`.
* **`badialiPsi_normSq_eq_madelungDensity`** — `|Ψ_Bd|² =
  madelungDensity` — the explicit equality of the two Born-rule
  statements.

## References

* Madelung 1927 *Z. Phys.* 40, 322 — original polar form.
* Badiali 2005 *J. Phys. A* 38, 2835 §6 — Eq. (34).
* `Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition`.
* `Physlib.QuantumMechanics.Schrodinger.MadelungPolarDecomposition`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

open Real Complex

/-! ## §1 — Badiali → Madelung constructor -/

/-- **Badiali → Madelung constructor**.

Given positive forward density `φ > 0`, positive backward density
`φ̂ > 0`, and Planck constant `ℏ > 0`, returns the
`MadelungWaveFunction` whose polar form matches Badiali's
`Ψ_Bd = exp(R_Bd + i·S_Bd)`:

* amplitude `R := √(φ · φ̂)`,
* phase     `S := ℏ · S_Bd = (ℏ/2) · ln(φ̂/φ)`,
* hbar      `ℏ`.

The amplitude is non-negative because square root is, and `ℏ > 0`
by hypothesis. -/
def badialiToMadelung
    (φ φ_hat ℏ : ℝ) (_hφ : 0 < φ) (_hφ_hat : 0 < φ_hat) (hℏ : 0 < ℏ) :
    MadelungWaveFunction where
  amplitude        := Real.sqrt (φ * φ_hat)
  amplitude_nonneg := Real.sqrt_nonneg _
  phase            := ℏ * badialiS φ φ_hat
  hbar             := ℏ
  hbar_pos         := hℏ

/-! ## §2 — Madelung density of the Badiali decomposition -/

/-- **The Madelung density of the Badiali → Madelung construction
equals the forward · backward product**:

  `madelungDensity (badialiToMadelung φ φ̂ ℏ) = φ · φ̂`.

This is the **Born rule from the Madelung side** applied to the
Badiali decomposition.  It identifies Badiali's Born density
`μ = φ · φ̂` (paper Eq. 37) with the Madelung Born density
`ρ = R²` (Madelung 1927). -/
theorem badialiToMadelung_density_eq
    {φ φ_hat ℏ : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) (hℏ : 0 < ℏ) :
    madelungDensity (badialiToMadelung φ φ_hat ℏ hφ hφ_hat hℏ) = φ * φ_hat := by
  unfold madelungDensity badialiToMadelung
  simp only
  rw [Real.sq_sqrt (le_of_lt (mul_pos hφ hφ_hat))]

/-! ## §3 — Badiali wavefunction equals Madelung polar form -/

/-- **Badiali's `Ψ_Bd` is the Madelung polar form** of the
`badialiToMadelung` construction:

  `badialiPsi φ φ̂ = (√(φ·φ̂) : ℂ) · exp(i · (ℏ·S_Bd) / ℏ)`.

The `(ℏ·S_Bd)/ℏ = S_Bd` cancellation reveals that the two
representations are literally the same complex number.

**Proof sketch**: Badiali's `Ψ = exp(R + i·S)` with `R = ln(√(φφ̂))`
unfolds to `exp(ln √(φφ̂)) · exp(i·S) = √(φφ̂) · exp(i·S)`. -/
theorem badialiPsi_eq_madelungForm
    {φ φ_hat ℏ : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) (hℏ : 0 < ℏ) :
    badialiPsi φ φ_hat
      = ((Real.sqrt (φ * φ_hat) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (((ℏ * badialiS φ φ_hat) : ℂ) / (ℏ : ℂ))) := by
  have hℏ_ne : (ℏ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hℏ
  have hsqrt_pos : 0 < Real.sqrt (φ * φ_hat) :=
    Real.sqrt_pos.mpr (mul_pos hφ hφ_hat)
  -- Amplitude: exp(R_Bd) = √(φφ̂)
  have h_amp :
      Complex.exp (badialiR φ φ_hat : ℂ)
        = ((Real.sqrt (φ * φ_hat) : ℝ) : ℂ) := by
    unfold badialiR
    have h_log_eq : (1 / 2 : ℝ) * Real.log (φ * φ_hat)
                    = Real.log (Real.sqrt (φ * φ_hat)) := by
      rw [Real.log_sqrt (le_of_lt (mul_pos hφ hφ_hat))]
      ring
    rw [show ((1 / 2 * Real.log (φ * φ_hat) : ℝ) : ℂ)
          = ((Real.log (Real.sqrt (φ * φ_hat)) : ℝ) : ℂ) from by
      exact_mod_cast h_log_eq]
    rw [← Complex.ofReal_exp, Real.exp_log hsqrt_pos]
  -- Phase: I · (ℏ·S/ℏ) = S · I
  have h_phase :
      Complex.I * ((ℏ : ℂ) * (badialiS φ φ_hat : ℂ) / (ℏ : ℂ))
        = (badialiS φ φ_hat : ℂ) * Complex.I := by
    field_simp
  unfold badialiPsi
  rw [h_phase, Complex.exp_add, h_amp]

/-! ## §4 — Equality of the two Born rules -/

/-- **The two Born rules coincide**:

  `Complex.normSq (badialiPsi φ φ̂) = madelungDensity (badialiToMadelung φ φ̂ ℏ)`.

The Badiali Born rule (`|Ψ_Bd|² = φ·φ̂`, paper Eq. 37) and the
Madelung Born rule (`ρ = R²`) are **machine-certified equal** for
the Badiali decomposition.

This forecloses the interpretive question "is the Badiali
forward–backward Born rule the same as the Madelung Born rule?":
they are formally identical. -/
theorem badialiPsi_normSq_eq_madelungDensity
    {φ φ_hat ℏ : ℝ} (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) (hℏ : 0 < ℏ) :
    Complex.normSq (badialiPsi φ φ_hat)
      = madelungDensity (badialiToMadelung φ φ_hat ℏ hφ hφ_hat hℏ) := by
  rw [badialiPsi_normSq hφ hφ_hat]
  rw [badialiToMadelung_density_eq hφ hφ_hat hℏ]

/-! ## §5 — Companion Bohmian-quantum-potential constructor -/

/-- **Badiali → Bohmian quantum potential constructor**.

Given positive forward/backward densities `φ, φ̂ > 0`, positive
mass `m > 0`, positive `ℏ > 0`, and a Laplacian-of-amplitude value
`ΔR : ℝ` (analytic input, deferred to a Sobolev-equipped scope),
returns the Bohmian quantum-potential record whose Madelung
wavefunction is `badialiToMadelung`.

The pre-Laplacian scale factor `Q · R / ΔR = −ℏ²/(2m)` is then
automatically `quantumPotentialScale_neg`-negative, certifying the
sign of the quantum potential `Q` in regions of positive amplitude
curvature without further work. -/
def badialiToBohmianQuantumPotential
    (φ φ_hat ℏ m ΔR : ℝ)
    (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) (hℏ : 0 < ℏ) (hm : 0 < m) :
    BohmianQuantumPotential where
  mass               := m
  mass_pos           := hm
  wf                 := badialiToMadelung φ φ_hat ℏ hφ hφ_hat hℏ
  laplacianAmplitude := ΔR

/-- **Quantum-potential scale is `−ℏ²/(2m) < 0`** for the Badiali
→ Bohmian construction.

Direct corollary of `quantumPotentialScale_neg`; certifies that
the Badiali-derived Bohmian quantum potential has the standard
attractive/repulsive sign convention of de Broglie–Bohm
mechanics. -/
theorem badialiToBohmian_quantumPotentialScale_neg
    {φ φ_hat ℏ m ΔR : ℝ}
    (hφ : 0 < φ) (hφ_hat : 0 < φ_hat) (hℏ : 0 < ℏ) (hm : 0 < m) :
    quantumPotentialScale
        (badialiToBohmianQuantumPotential φ φ_hat ℏ m ΔR hφ hφ_hat hℏ hm) < 0 :=
  quantumPotentialScale_neg _

end Physlib.QuantumMechanics.Schrodinger

end

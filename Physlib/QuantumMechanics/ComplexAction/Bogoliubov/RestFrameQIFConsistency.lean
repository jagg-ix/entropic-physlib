/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrame

/-!
# Consistency of the QIF and the Bogoliubov rest frame: conditions, transformation, and the metric

`Bogoliubov.RestFrame` established that the QIF equilibrium (`H_I = 0`, entropic) and the Bogoliubov
diagonal rest frame (`p = 0`, kinematic) are *distinct* reductions. This file makes precise the
**transformation** and the **conditions** under which the two are nonetheless *consistent*, and shows
how the consistency rests on the **metric**.

## The frame data and the transformation

A matter frame records energy–momentum `(E/c, p)` (the `H_R` sector) and an entropic rate
`λ = ⟨H_I⟩/ℏ` (the `H_I` / QIF sector) — `FrameData`. The transformation is the bosonic Bogoliubov
**boost** `boostFrame θ`, which acts on `(E/c, p)` by `lorentzBoost θ` and leaves `λ` fixed.

## The conditions (what is needed for the link)

1. **Metric condition** — the transformation is a genuine Bogoliubov boost, preserving the symplectic
   metric `S = diag(1, −1)`: `𝒱ᵀ S 𝒱 = S ⟺ u² − v² = 1` (`metric_condition`,
   `Bogoliubov.BosonicBogoliubovDiagonalization`). This is what makes `boostFrame` a Lorentz boost.
2. **Sector condition** — the entropic rate `λ` lives in the `H_I` sector, transverse to the boosted
   energy–momentum, so the boost leaves it invariant (`boostFrame_entropicRate`). This is the
   finite-dimensional shadow of the QIF `entropicRate_lorentz_invariant`.
3. **Timelike condition** — `|p| < E/c` (sub-luminal), so a rest frame exists.

## How it relates to the metric

The rest mass squared **is** the metric `S`-norm of the energy–momentum,
`restMassSq (E/c) p = ⟨(E/c, p), S(E/c, p)⟩ = (E/c)² − p²` (`restMass_is_metric_norm`), and the boost
preserves it (`boostFrame_restMass`, from `lorentzBoost_preserves_form`). The metric signature
`(+1, −1)` separates the boosted energy–momentum (the `S`-norm = rest mass) from the entropic scalar
`λ` (invariant). So the **same** metric-preserving boost transports the rest mass and the entropic
rate consistently.

## The consistency theorem

`restFrame_qif_consistency`: under the conditions, the boost to the rest frame (`p' = 0`) takes the
energy to the rest mass `√((E/c)² − p²)` (the metric `S`-norm) **and** leaves the entropic rate
unchanged, so **QIF-equilibrium (`λ = 0`) holds in the rest frame iff it holds in the original
frame**. The QIF entropic structure and the Bogoliubov kinematic rest frame are compatible — matched consistently by the one metric-preserving boost — even though they are distinct reductions.

## References

* Garcia 2026 (QIF; `FiniteTarget.QuantumInertialFrame`, `QIFLorentzFrameChange.entropicRate_lorentz_invariant`).
* P. T. Nam, M. Napiórkowski, J. P. Solovej, J. Funct. Anal. **270** (2016) 4340.
  doi:10.1016/j.jfa.2015.12.007.
* This development: `Bogoliubov.RestFrame`, `Bogoliubov.BosonicBogoliubovDiagonalization`,
  `TimeOperator.HyperbolicPoincareLorentzMisra`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency

/-! ## §A — the frame data and the boost transformation -/

/-- **A matter frame**: energy–momentum `(E/c, p)` (the `H_R` sector) and the entropic rate
`λ = ⟨H_I⟩/ℏ` (the `H_I` / QIF sector). -/
structure FrameData where
  /-- The time component `E/c` of the 4-momentum. -/
  energy : ℝ
  /-- The spatial momentum `p`. -/
  momentum : ℝ
  /-- The QIF entropic rate `λ = ⟨H_I⟩/ℏ`. -/
  entropicRate : ℝ

/-- **The rest mass squared** `(E/c)² − p²` — the metric `S`-norm of the energy–momentum. -/
def restMassSq (t x : ℝ) : ℝ := t ^ 2 - x ^ 2

/-- **The Bogoliubov boost on a frame**: `lorentzBoost θ` on `(E/c, p)`, the entropic rate fixed. -/
def boostFrame (θ : ℝ) (F : FrameData) : FrameData where
  energy := (lorentzBoost θ F.energy F.momentum).1
  momentum := (lorentzBoost θ F.energy F.momentum).2
  entropicRate := F.entropicRate

/-! ## §B — the conditions: the metric condition and the sector (entropic) condition -/

/-- **Condition 1 — the metric condition**: the transformation preserves the symplectic metric
`S = diag(1, −1)` iff `u² − v² = 1` (a genuine Bogoliubov boost). -/
theorem metric_condition (u v : ℝ) :
    (bosonicBogoliubov u v)ᵀ * symplecticS * bosonicBogoliubov u v = symplecticS
      ↔ u ^ 2 - v ^ 2 = 1 :=
  bosonicBogoliubov_preserves_S_iff u v

/-- **The rest mass is the metric `S`-norm** `restMassSq (E/c) p = ⟨(E/c,p), S(E/c,p)⟩`. -/
theorem restMass_is_metric_norm (t x : ℝ) :
    restMassSq t x = ![t, x] ⬝ᵥ (symplecticS *ᵥ ![t, x]) := by
  unfold restMassSq
  rw [symplecticS_quadratic_form]

/-- **Metric invariant**: the boost preserves the rest mass (the metric `S`-norm). -/
theorem boostFrame_restMass (θ : ℝ) (F : FrameData) :
    restMassSq (boostFrame θ F).energy (boostFrame θ F).momentum = restMassSq F.energy F.momentum :=
  lorentzBoost_preserves_form θ F.energy F.momentum

/-- **Condition 2 — the sector condition**: the entropic rate is in the `H_I` sector, transverse to
the boosted energy–momentum, so the boost leaves it invariant (the finite-dimensional
`entropicRate_lorentz_invariant`). -/
theorem boostFrame_entropicRate (θ : ℝ) (F : FrameData) :
    (boostFrame θ F).entropicRate = F.entropicRate := rfl

/-- **The QIF-equilibrium condition is boost-invariant** (`λ = 0` is preserved). -/
theorem boostFrame_equilibrium_iff (θ : ℝ) (F : FrameData) :
    (boostFrame θ F).entropicRate = 0 ↔ F.entropicRate = 0 := by
  rw [boostFrame_entropicRate]

/-! ## §C — the boost to the rest frame, and the consistency -/

/-- **The boost to the rest frame.** For a timelike frame (`0 < E/c`, `|p| < E/c`) there is a
rapidity `θ` whose boost takes the matter to its rest frame: the spatial momentum vanishes
(`p' = 0`), the energy becomes the rest mass `√((E/c)² − p²)` (the metric `S`-norm), and the entropic
rate is unchanged. -/
theorem boost_to_rest_frame (F : FrameData) (ht : 0 < F.energy) (hsub : |F.momentum| < F.energy) :
    ∃ θ : ℝ, (boostFrame θ F).momentum = 0
      ∧ (boostFrame θ F).energy = Real.sqrt (restMassSq F.energy F.momentum)
      ∧ (boostFrame θ F).entropicRate = F.entropicRate := by
  obtain ⟨α, hx, ht'⟩ := exists_diagonalizing_rapidity F.energy F.momentum ht hsub
  refine ⟨-α, ?_, ?_, rfl⟩
  · show Real.sinh (-α) * F.energy + Real.cosh (-α) * F.momentum = 0
    rw [Real.sinh_neg, Real.cosh_neg]
    linear_combination -Real.sinh α * ht' + Real.cosh α * hx
  · show Real.cosh (-α) * F.energy + Real.sinh (-α) * F.momentum
        = Real.sqrt (restMassSq F.energy F.momentum)
    rw [Real.cosh_neg, Real.sinh_neg,
      show Real.sqrt (restMassSq F.energy F.momentum)
        = diagonalizedFrequency F.energy F.momentum from rfl]
    linear_combination Real.cosh α * ht' - Real.sinh α * hx
      + diagonalizedFrequency F.energy F.momentum * Real.cosh_sq_sub_sinh_sq α

/-- **The QIF–rest-frame consistency.** Under the conditions (metric-preserving boost, entropic
sector, timelike), the boost to the rest frame:

* sends the spatial momentum to `0` (the kinematic rest frame);
* sends the energy to the rest mass `√((E/c)² − p²)` (the metric `S`-norm), preserved by the boost;
* leaves the entropic rate `λ` unchanged (the QIF sector is boost-invariant);
* so **QIF-equilibrium (`λ = 0`) holds in the rest frame iff in the original frame**.

The QIF entropic structure and the Bogoliubov kinematic rest frame are consistent — encoded in the
one metric-preserving boost — even though they are distinct reductions. -/
theorem restFrame_qif_consistency (F : FrameData) (ht : 0 < F.energy)
    (hsub : |F.momentum| < F.energy) :
    ∃ θ : ℝ, (boostFrame θ F).momentum = 0
      ∧ (boostFrame θ F).energy = Real.sqrt (restMassSq F.energy F.momentum)
      ∧ (boostFrame θ F).entropicRate = F.entropicRate
      ∧ ((boostFrame θ F).entropicRate = 0 ↔ F.entropicRate = 0) := by
  obtain ⟨θ, hp, hE, hlam⟩ := boost_to_rest_frame F ht hsub
  exact ⟨θ, hp, hE, hlam, by rw [boostFrame_entropicRate]⟩

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency

end

end

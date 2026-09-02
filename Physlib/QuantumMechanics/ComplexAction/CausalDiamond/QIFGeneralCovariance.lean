/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium

/-!
# The QIF zeroth law is general covariance: the boost fixes the metric, so the temperature is invariant

Improves the **kinematic zeroth law** of `CausalDiamond.QIFEquilibrium`
(`qifEntropicRate_lorentz_invariant`: the QIF entropic rate `λ` is unchanged under the Bogoliubov boost)
by **grounding it in Levi-Civita's general covariance** (`LeviCivita.ArbitraryCoordinates`). The boost is
not just an abstract symmetry of the frame data — it is an **arbitrary-coordinate change that fixes the
metric**:

* a Lorentz frame `Λ ∈ SO(1,3)` acts on the cotetrad by `E ↦ ΛE`, and the metric — the
  arbitrary-coordinate transform of the flat metric `g = EᵀηE = coordCongruence E η`
  (`tetradMetric_eq_coordCongruence`) — is **invariant** under it,
  `coordCongruence (ΛE) η = coordCongruence E η` (`metric_lorentz_coordInvariant`); the Lorentz boost is a
  coordinate Jacobian that leaves the flat metric `η` fixed.

Because the surface gravity `κ`, the Hawking/Unruh temperature `T = ℏκ/2πck_B`, and the QIF entropic rate
`λ = k_B T/ℏ` are all **scalars built from the metric**, the metric's invariance under the boost makes
each of them coordinate-invariant. So the kinematic zeroth law (the entropic rate is boost-invariant) and
the geometric zeroth law (`κ` constant on `𝓗`) are **two faces of one general-covariance statement**: under
the boost — an arbitrary-coordinate change fixing the metric — the horizon temperature is unchanged
(`qif_zerothLaw_generalCovariance`).

This improves the previous QIF picture: the entropic-rate invariance is no longer a standalone kinematic
fact but a **consequence of Levi-Civita general covariance** — the same congruence `JᵀMJ` that refers the
field equations to arbitrary co-ordinates fixes the metric under the horizon-generating Lorentz boost,
hence fixes the temperature on every generator.

* **§A — the Lorentz boost fixes the metric (general covariance)** (`metric_lorentz_coordInvariant`).
* **§B — the QIF zeroth law as general covariance** (`qif_zerothLaw_generalCovariance`).

## References

* T. Levi-Civita (arXiv:physics/9906004), reference to arbitrary co-ordinates. Carriers:
  `LeviCivita.ArbitraryCoordinates` (`coordCongruence`, `tetradMetric_eq_coordCongruence`),
  `CanonicalTetradGravity.TetradADMGravity` (`tetradMetric_lorentz_gauge`, `minkowskiMatrix`),
  `CausalDiamond.QIFEquilibrium` (`qifEntropicRate_lorentz_invariant`, `qif_zerothLaw_equilibrium`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFGeneralCovariance

open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium


/-- **[The horizon-generating Lorentz boost fixes the metric] `coordCongruence (ΛE) η = coordCongruence E η`.**
Read through Levi-Civita's congruence `JᵀMJ`, the local Lorentz frame rotation `E ↦ ΛE` (`Λ ∈ SO(1,3)`,
the Bogoliubov boost / conformal Killing flow) is an **arbitrary-coordinate change that leaves the metric
invariant**: the curved metric `g = EᵀηE = coordCongruence E η` is unchanged. The boost is a coordinate
Jacobian fixing the flat Minkowski metric `η`. -/
lemma metric_lorentz_coordInvariant {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d) :
    coordCongruence (Λ * E) minkowskiMatrix = coordCongruence E minkowskiMatrix := by
  rw [← tetradMetric_eq_coordCongruence, ← tetradMetric_eq_coordCongruence]
  exact tetradMetric_lorentz_gauge hΛ


/-- **[The QIF zeroth law is general covariance].** For a horizon-generating Lorentz boost `Λ ∈ SO(1,3)` on
a cotetrad `E`, frame data `F`, and a constant surface gravity `κ = κ'` (the zeroth law):

* **general covariance** — the boost fixes the metric, `coordCongruence (ΛE) η = coordCongruence E η`
  (the metric is invariant under this arbitrary-coordinate change);
* **kinematic zeroth law** — the QIF entropic rate is boost-invariant,
  `(boostFrame θ F).entropicRate = F.entropicRate`;
* **geometric zeroth law** — the QIF entropic rate, the Hawking temperature, and the Unruh temperature are
  uniform, the same `T = ℏκ/2πck_B` on every generator.

All three are one statement: under the Lorentz boost — an arbitrary-coordinate change fixing the metric —
the surface gravity, the temperature, and the entropic rate (all metric scalars) are unchanged. The
kinematic boost-invariance of `λ` is a **consequence of Levi-Civita general covariance**, not a separate
fact: the same congruence `JᵀMJ` that refers the field equations to arbitrary co-ordinates fixes the
metric under the boost, hence fixes the horizon temperature. -/
lemma qif_zerothLaw_generalCovariance {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (θ : ℝ) (F : FrameData) (ℏ κ κ' c kB : ℝ) (h : κ = κ') :
    coordCongruence (Λ * E) minkowskiMatrix = coordCongruence E minkowskiMatrix
      ∧ (boostFrame θ F).entropicRate = F.entropicRate
      ∧ qifEntropicRate κ c = qifEntropicRate κ' c
      ∧ hawkingTemperature ℏ κ c kB = hawkingTemperature ℏ κ' c kB
      ∧ Physlib.Thermodynamics.unruhTemperature ℏ kB c κ
        = Physlib.Thermodynamics.unruhTemperature ℏ kB c κ' := by
  obtain ⟨hr, hh, hu⟩ := qif_zerothLaw_equilibrium ℏ κ κ' c kB h
  exact ⟨metric_lorentz_coordInvariant Λ E hΛ, qifEntropicRate_lorentz_invariant θ F, hr, hh, hu⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFGeneralCovariance

end

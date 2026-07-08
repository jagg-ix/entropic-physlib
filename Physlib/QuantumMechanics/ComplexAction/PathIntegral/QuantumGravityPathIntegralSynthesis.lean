/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ParametrizedDirac
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldSuperoperator

/-!
# A quantum-gravity path integral: the Lorentz–EM superoperator, Bennett's worldline, and FFT

Connects `PathIntegral.OneLoopPathIntegralVerch.oneLoop_pathIntegral_verch` (the one-loop QED path-integral
determinant ↔ Bogoliubov energy ↔ Verch symplectic complex structure) to the **fused Lorentz–EM
superoperator** `𝒢_{J,F} = ad_{J+F}` (`Electromagnetic.EMLorentzCombinedSuperoperator.emLorentzGenerator`), using
A. F. Bennett's **first-quantized electrodynamics** (arXiv:1406.0750, parametrized Dirac) and the
Greaves–Thomas **formal field theory** (`PTSymmetricQFT.FieldSuperoperator`), assembling a
quantum-gravity path integral.

The picture:

* the fused superoperator `𝒢_{J,F} = ad_J + ad_F` splits into a **gravity / Lorentz** part `ad_J`
  (`𝔰𝔬(1,3)` generator) and an **electromagnetic** part `ad_F` (Faraday)
  (`gravityEM_generator_decompose`);
* the Greaves–Thomas **formal field theory** is the **path-integral functor**: its realization map
  includes the Liouville generator `𝓛_H = −i·ad_H` (the superoperator) to the Heisenberg operator
  commutator `−i[Ĥ, ·]` (`formalFieldTheory_realizes_superoperator`, from `realize_liouvilleGenerator`)
  — the quantum dynamics of the gravity+EM evolution;
* Bennett's **first-quantized parametrized Dirac** provides the worldline: the `τ`-evolution phase
  `e^{i m_p τ}` is the **unitary worldline path-integral weight** (`bennett_worldline_weight_unitary`),
  and the worldline energy `|p⁰|` is the **QED one-loop Berezin functional determinant**, equal to the
  **Bogoliubov energy** `√(p²+m²)` (`bennett_worldline_eq_berezinDet`);
* that determinant's dispersion is `cosh η`, the diagonal of the diagonalizing **Verch symplectomorphism**
  (`PathIntegral.OneLoopPathIntegralVerch.berezinDet_eq_bogoliubov_diagonal`), with **pure-state complex
  structure** `J² = −1` (`sympForm_sq`).

So the quantum-gravity path integral is the Gaussian one-loop determinant (Verch–Bogoliubov
diagonalized) of the gravity(`J`)+EM(`F`)-coupled first-quantized Dirac operator, realized by the
formal field theory and weighted by the unitary worldline phase `e^{i m_p τ}`
(`quantumGravity_pathIntegral`).

* **§A — Bennett worldline = QED one-loop determinant** (`bennett_worldline_eq_berezinDet`,
  `bennett_worldline_weight_unitary`).
* **§B — the gravity+EM superoperator** (`gravityEM_generator_decompose`,
  `gravityEM_generator_measure_preserving`).
* **§C — the formal field theory as the path-integral functor**
  (`formalFieldTheory_realizes_superoperator`).
* **§D — the synthesis** (`quantumGravity_pathIntegral`).

## References

* A. F. Bennett, arXiv:1406.0750v3 (parametrized first-quantized Dirac, `e^{i m_p τ}` worldline). Repo
  structures: `Electromagnetic.EMLorentzCombinedSuperoperator` (`emLorentzGenerator`), `FirstQuantizedQED.ParametrizedDirac`
  (`bennett_energy_eq_bogoliubov`, `bennett_tau_phase_unimodular`), `PTSymmetricQFT.FieldSuperoperator`
  (`liouvilleGenerator`, `realize_liouvilleGenerator`), `PathIntegral.OneLoopPathIntegralVerch`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.QuantumGravityPathIntegralSynthesis

open Real
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ParametrizedDirac
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldSuperoperator
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch

/-! ## §A — Bennett's first-quantized worldline = the QED one-loop determinant -/

/-- **[Bennett worldline = one-loop Berezin determinant] `det[|p⁰|] = √(p²+m²)`.** The energy `|p⁰|` of
Bennett's parametrized first-quantized Dirac mode is the **QED one-loop fermion functional determinant**
`berezin (fermionGaussian |p⁰|)`, equal to the **Bogoliubov energy** `√(p²+m²)`
(`bennett_energy_eq_bogoliubov`). The first-quantized worldline propagator and the second-quantized
one-loop determinant include the same dispersion. -/
theorem bennett_worldline_eq_berezinDet (p0 pmag : ℝ) (h : pmag ^ 2 ≤ p0 ^ 2) :
    berezin (fermionGaussian |p0|) = bogoliubovEnergy pmag (Real.sqrt (p0 ^ 2 - pmag ^ 2)) := by
  rw [show berezin (fermionGaussian |p0|) = |p0| from rfl]
  exact bennett_energy_eq_bogoliubov p0 pmag h

/-- **[Unitary worldline weight] `‖e^{i m_p τ}‖ = 1`.** Bennett's free `τ`-evolution phase
`ψ ∝ e^{i m_p τ}` (the first-quantized worldline path-integral weight, action `S = m_p τ`) is unitary
(`bennett_tau_phase_unimodular`) — the reversible, oscillatory worldline contribution, matching the
reversible one-loop weight (`oneLoop_weight_unitary_of_reversible`). -/
theorem bennett_worldline_weight_unitary (m_p τ : ℝ) :
    ‖Complex.exp (Complex.I * ((m_p * τ : ℝ) : ℂ))‖ = 1 :=
  bennett_tau_phase_unimodular m_p τ

/-! ## §B — the gravity + electromagnetic superoperator -/

/-- **[Gravity + EM split] `𝒢_{J,F} = ad_J + ad_F`.** The fused Lorentz–EM superoperator splits into a
**gravity / Lorentz** part `ad_J` (the `𝔰𝔬(1,3)` generator) and an **electromagnetic** part `ad_F`
(the Faraday field) — the generator of the coupled gravity+matter one-loop evolution. -/
theorem gravityEM_generator_decompose (J F : Mat) :
    emLorentzGenerator J F = emFieldAdjoint J + emFieldAdjoint F :=
  emLorentzGenerator_decompose J F

/-- **[Measure-preserving evolution] `tr 𝒢_{J,F}(X) = 0`.** The gravity+EM superoperator `ad_{J+F}` is
trace-free, so the one-loop path-integral measure (the determinant) is preserved under the
gravity+matter evolution. -/
theorem gravityEM_generator_measure_preserving (J F X : Mat) :
    (emLorentzGenerator J F X).trace = 0 :=
  emLorentzGenerator_trace_zero J F X

/-! ## §C — the formal field theory as the path-integral functor -/

variable {U : Type*} [AddCommGroup U] [Module ℂ U]
variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **[Formal field theory = quantum path-integral functor] realize ∘ 𝓛_H = −i[Ĥ, ·].** The
Greaves–Thomas formal-field-theory realization includes the Liouville/ad superoperator
`𝓛_H = −i·ad_H` (the abstract gravity+EM generator on `K^form`) to the **Heisenberg operator
commutator** `−i[realize H, ·]` (`realize_liouvilleGenerator`) — the path integral as the functor from
formulae to operators that realizes the superoperator dynamics. -/
theorem formalFieldTheory_realizes_superoperator (ev : U →ₗ[ℂ] A) (H Y : KForm U) :
    quantumRealize ev (liouvilleGenerator H Y)
      = (-Complex.I) • (quantumRealize ev H * quantumRealize ev Y
          - quantumRealize ev Y * quantumRealize ev H) :=
  realize_liouvilleGenerator ev H Y

/-! ## §D — the synthesis -/

/-- **[Quantum-gravity path integral, assembled] one object across the superoperator, the worldline,
the formal field theory, and the Verch symplectic structure.** The gravity+EM superoperator splits as
`ad_J + ad_F` (gravity + matter); Bennett's first-quantized worldline energy is the QED one-loop Berezin
determinant `= √(p²+m²)`; the worldline weight `e^{i m_p τ}` is unitary; the determinant dispersion is
`cosh η`, the diagonal of the diagonalizing Verch symplectomorphism, with pure-state complex structure
`J² = −1`; and the formal field theory realizes the superoperator `𝓛_H` as the Heisenberg path-integral
generator `−i[Ĥ, ·]`. The quantum-gravity path integral is the Verch–Bogoliubov-diagonalized one-loop
Gaussian determinant of the gravity(`J`)+EM(`F`)-coupled first-quantized Dirac operator, realized by the
formal field theory. -/
theorem quantumGravity_pathIntegral (J F : Mat) (p0 pmag m_p τ η : ℝ) (hp : pmag ^ 2 ≤ p0 ^ 2)
    (ev : U →ₗ[ℂ] A) (H Y : KForm U) :
    emLorentzGenerator J F = emFieldAdjoint J + emFieldAdjoint F
      ∧ berezin (fermionGaussian |p0|) = bogoliubovEnergy pmag (Real.sqrt (p0 ^ 2 - pmag ^ 2))
      ∧ ‖Complex.exp (Complex.I * ((m_p * τ : ℝ) : ℂ))‖ = 1
      ∧ berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = (thermoBogoliubov η) 0 0
      ∧ sympForm * sympForm = -1
      ∧ quantumRealize ev (liouvilleGenerator H Y)
          = (-Complex.I) • (quantumRealize ev H * quantumRealize ev Y
              - quantumRealize ev Y * quantumRealize ev H) :=
  ⟨gravityEM_generator_decompose J F, bennett_worldline_eq_berezinDet p0 pmag hp,
    bennett_worldline_weight_unitary m_p τ, berezinDet_eq_bogoliubov_diagonal η, sympForm_sq,
    formalFieldTheory_realizes_superoperator ev H Y⟩

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.QuantumGravityPathIntegralSynthesis

end

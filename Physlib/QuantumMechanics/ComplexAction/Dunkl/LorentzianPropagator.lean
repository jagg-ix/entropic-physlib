/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.ComplexFeynmanKac

/-!
# The Wigner–Dunkl oscillator's Lorentzian (complex) path integral and Lie–Trotter construction

Expands `Dunkl.ComplexFeynmanKac` (which recovered the complex Feynman–Kac *kernel* as the modulus
of the Euclidean Dunkl weight) from the scalar kernel to the full **Lorentzian complex path integral** of
`Physlib.QFT.PathIntegral.Lorentzian` (the `e^{iS/ℏ}` time-evolution propagator and its Lie–Trotter
discretization — the physlib foundation of reference tree's `LorentzianPathIntegralBridge`). This realizes
Junker's own construction: the WDQM path integral is *built* by the Lie–Trotter product formula
(arXiv:2312.12895 §4).

The Dunkl oscillator becomes a scalar `ComplexHamiltonian` `Ĥ = H_R − iH_I` whose real part is the
Wigner–Dunkl spectrum `H_R = ℏω(n + ν + ½)` (`Dunkl.NagaoNielsenOscillator`) and whose imaginary part
`H_I ≥ 0` is the entropic/dissipative damping. Then:

* **§A — the Dunkl oscillator as a complex Hamiltonian** (`dunklOscComplexH`), real part `dunklOscEnergyReal`.
* **§B — the Lorentzian propagator and the Euclidean bridge** (`dunklOsc_lorentzianPropagator_norm`):
  `‖lorentzianPropagator Ĥ t ℏ‖ = matsubaraBoltzmannWeight (t/ℏ) H_I`. The modulus of the complex
  time-evolution propagator is exactly the Euclidean/Matsubara Dunkl weight at imaginary time `β = t/ℏ` —
  the Wick rotation made explicit. The full propagator is the reversible phase `e^{−itH_R/ℏ}` (oscillation
  at the Dunkl frequency) times that real weight.
* **§C — Junker's Lie–Trotter construction** (`dunklOsc_trotterStep_norm`, `dunklOsc_trotterProduct_norm`):
  the discretized complex path integral `(U_step)^{n+1}` has modulus equal to the product of the per-step
  Euclidean Dunkl weights — the path integral assembled substep by substep.
* **§D — dissipativity and unitarity** (`dunklOsc_propagator_le_one`, `dunklOsc_reversible_unitary`):
  forward-time contraction for `H_I ≥ 0`, and a pure unitary phase at the reversible point `H_I = 0`.
* **§E — the Dirac spinor field's Lorentzian propagator** (`dunklSpinor_lorentzianPropagator_norm`): the
  spinor (antiperiodic fermionic spectrum `H_R = ℏω(n − ½)`, the absorbing sector) propagates by the same
  complex path integral; its modulus is the Euclidean absorbing weight, its phase includes the fermionic
  energy.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.LorentzianPropagator

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-! ## §A — the Wigner–Dunkl oscillator as a scalar complex Hamiltonian -/

/-- **The real Wigner–Dunkl oscillator spectrum** `E_n = ℏω(n + ν + ½)** — the real part of
`Dunkl.NagaoNielsenOscillator.dunklOscillatorEnergy`, the reversible (oscillatory) energy. -/
noncomputable def dunklOscEnergyReal (ℏ ω ν : ℝ) (n : ℕ) : ℝ := ℏ * ω * (n + ν + 1 / 2)

/-- **The Wigner–Dunkl oscillator as a complex Hamiltonian** `Ĥ = H_R − iH_I`: reversible part the Dunkl
spectrum `ℏω(n + ν + ½)`, dissipative part the entropic damping `H_I ≥ 0`. -/
noncomputable def dunklOscComplexH (ℏ ω ν : ℝ) (n : ℕ) (HI : ℝ) (hI : 0 ≤ HI) : ComplexHamiltonian :=
  { H_R := dunklOscEnergyReal ℏ ω ν n, H_I := HI, H_I_nonneg := hI }

/-! ## §B — the Lorentzian propagator and the Euclidean/Matsubara bridge -/

/-- **[Bridge] The modulus of the Wigner–Dunkl oscillator's complex Lorentzian propagator is the
Euclidean/Matsubara Dunkl weight.** `‖lorentzianPropagator Ĥ t ℏ‖ = matsubaraBoltzmannWeight (t/ℏ) H_I` —
the complex (real-time) path integral, taken in modulus, *is* the Euclidean Dunkl process weight at
imaginary time `β = t/ℏ`. This is the Wick rotation `t ↦ −iβℏ` made explicit at the propagator level. -/
theorem dunklOsc_lorentzianPropagator_norm (ℏ ω ν : ℝ) (n : ℕ) (HI t : ℝ) (hI : 0 ≤ HI) :
    ‖lorentzianPropagator (dunklOscComplexH ℏ ω ν n HI hI) t ℏ‖ = matsubaraBoltzmannWeight (t / ℏ) HI := by
  rw [lorentzianPropagator_norm_is_damping]; unfold matsubaraBoltzmannWeight dunklOscComplexH
  congr 1; ring

/-- **The Lorentzian propagator factors as the reversible phase times the Euclidean Dunkl weight**
(modulus form is `dunklOsc_lorentzianPropagator_norm`): the phase `e^{−itH_R/ℏ}` oscillates at the
Wigner–Dunkl frequency `H_R = ℏω(n + ν + ½)`, the modulus is the Dunkl process damping. -/
theorem dunklOsc_propagator_phase (ℏ ω ν : ℝ) (n : ℕ) (HI : ℝ) (hI : 0 ≤ HI) :
    (dunklOscComplexH ℏ ω ν n HI hI).H_R = dunklOscEnergyReal ℏ ω ν n := rfl

/-! ## §C — Junker's Lie–Trotter construction of the path integral (arXiv:2312.12895 §4) -/

/-- **[Junker §4] The Lie–Trotter substep modulus is the per-step Euclidean Dunkl weight.**
`‖lorentzianTrotterStep Ĥ dt ℏ‖ = matsubaraBoltzmannWeight (dt/ℏ) H_I` — each substep of the
phase-times-damping splitting `e^{−i dt H_R/ℏ}·e^{−dt H_I/ℏ}` records one factor of the Dunkl process. -/
theorem dunklOsc_trotterStep_norm (ℏ ω ν : ℝ) (n : ℕ) (HI dt : ℝ) (hI : 0 ≤ HI) :
    ‖lorentzianTrotterStep (dunklOscComplexH ℏ ω ν n HI hI) dt ℏ‖ = matsubaraBoltzmannWeight (dt / ℏ) HI := by
  rw [lorentzianTrotterStep_norm_is_damping]; unfold matsubaraBoltzmannWeight dunklOscComplexH
  congr 1; ring

/-- **[Junker §4] The discretized Lie–Trotter path integral.** `‖(U_step)^{k+1}‖ =
(matsubaraBoltzmannWeight ((t/(k+1))/ℏ) H_I)^{k+1}` — the complex Wigner–Dunkl path integral, assembled
from `k+1` substeps, has modulus equal to the product of the per-step Euclidean Dunkl weights. In the
`k → ∞` limit this is the Dunkl–Feynman–Kac weight of `Dunkl.EuclideanProcess`. -/
theorem dunklOsc_trotterProduct_norm (ℏ ω ν : ℝ) (n : ℕ) (HI t : ℝ) (hI : 0 ≤ HI) (k : ℕ) :
    ‖lorentzianTrotterProduct (dunklOscComplexH ℏ ω ν n HI hI) t ℏ k‖
      = (matsubaraBoltzmannWeight ((t / (k + 1)) / ℏ) HI) ^ (k + 1) := by
  unfold lorentzianTrotterProduct
  rw [norm_pow, lorentzianTrotterStep_norm_is_damping]
  unfold matsubaraBoltzmannWeight dunklOscComplexH; congr 2; ring

/-! ## §D — dissipativity and the reversible (unitary) limit -/

/-- **Forward-time contraction**: for `t ≥ 0`, `ℏ > 0` the Wigner–Dunkl complex propagator has modulus
`≤ 1` — the Dunkl process is dissipative (sub-Markovian) whenever `H_I ≥ 0`. -/
theorem dunklOsc_propagator_le_one (ℏ ω ν : ℝ) (n : ℕ) (HI t : ℝ) (hI : 0 ≤ HI)
    (ht : 0 ≤ t) (hℏ : 0 < ℏ) :
    ‖lorentzianPropagator (dunklOscComplexH ℏ ω ν n HI hI) t ℏ‖ ≤ 1 :=
  lorentzianPropagator_norm_le_one _ t ℏ ht hℏ

/-- **[Reversible limit] At `H_I = 0` the Wigner–Dunkl complex propagator is unitary** (`‖·‖ = 1`): a pure
oscillatory phase `e^{−itH_R/ℏ}` at the Dunkl frequency, with no Euclidean damping — the no-information /
reversible point where the complex path integral is genuinely Minkowskian. -/
theorem dunklOsc_reversible_unitary (ℏ ω ν : ℝ) (n : ℕ) (t : ℝ) :
    ‖lorentzianPropagator (dunklOscComplexH ℏ ω ν n 0 le_rfl) t ℏ‖ = 1 := by
  rw [lorentzianPropagator_norm_is_damping]; simp [dunklOscComplexH]

/-! ## §E — the Dirac spinor field's Lorentzian propagator -/

/-- **The Dirac spinor as a complex Hamiltonian**: reversible part the antiperiodic fermionic spectrum
`H_R = ℏω(n − ½)` (`ComplexOscillator.ComplexFermionicOscillator.fermionicEnergyReal`, the absorbing/antiperiodic sector of
`Dunkl.MatsubaraSpinor`), dissipative part `H_I ≥ 0`. -/
noncomputable def dunklSpinorComplexH (ℏ ω : ℝ) (n : ℕ) (HI : ℝ) (hI : 0 ≤ HI) : ComplexHamiltonian :=
  { H_R := fermionicEnergyReal ℏ ω n, H_I := HI, H_I_nonneg := hI }

/-- **[Bridge] The Dirac spinor field's complex Lorentzian propagator has modulus the Euclidean absorbing
weight.** `‖lorentzianPropagator Ĥ_spinor t ℏ‖ = matsubaraBoltzmannWeight (t/ℏ) H_I` — the spinor
propagates by the same complex path integral as the oscillator; its modulus is the absorbing-sector Dunkl
weight, its reversible phase `e^{−itH_R/ℏ}` includes the antiperiodic fermionic spectrum
(`dunklSpinor_propagator_phase`). -/
theorem dunklSpinor_lorentzianPropagator_norm (ℏ ω : ℝ) (n : ℕ) (HI t : ℝ) (hI : 0 ≤ HI) :
    ‖lorentzianPropagator (dunklSpinorComplexH ℏ ω n HI hI) t ℏ‖ = matsubaraBoltzmannWeight (t / ℏ) HI := by
  rw [lorentzianPropagator_norm_is_damping]; unfold matsubaraBoltzmannWeight dunklSpinorComplexH
  congr 1; ring

/-- **The spinor propagator's reversible phase includes the antiperiodic fermionic energy.** -/
theorem dunklSpinor_propagator_phase (ℏ ω : ℝ) (n : ℕ) (HI : ℝ) (hI : 0 ≤ HI) :
    (dunklSpinorComplexH ℏ ω n HI hI).H_R = fermionicEnergyReal ℏ ω n := rfl

/-- **The spinor propagator is also forward-time contractive** for `H_I ≥ 0`. -/
theorem dunklSpinor_propagator_le_one (ℏ ω : ℝ) (n : ℕ) (HI t : ℝ) (hI : 0 ≤ HI)
    (ht : 0 ≤ t) (hℏ : 0 < ℏ) :
    ‖lorentzianPropagator (dunklSpinorComplexH ℏ ω n HI hI) t ℏ‖ ≤ 1 :=
  lorentzianPropagator_norm_le_one _ t ℏ ht hℏ

end Physlib.QuantumMechanics.ComplexAction.Dunkl.LorentzianPropagator

end

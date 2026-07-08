/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# The full Einstein dispersion `E² = (pc)² + (mc²)²` and its consistency with Dirac, the
Nagao–Nielsen complex oscillator, the TDSE, and the TISE

`ComplexEinstein.ComplexMassEinsteinEquations` gave only the *rest* term `E = mc²`. This file completes it with the
**full Einstein energy–momentum relation** (the missing `+ (pc)²`):

  `E² = (pc)² + (mc²)²`   (`einstein_fullDispersion`),

and proves it consistent, inside the complex-action/entropic-time framework (`H_C = H_R − iĤ_I`), with all four pillars:

* **Dirac equation.** `E` is an eigenvalue of the Dirac Hamiltonian `H = (mc²)σ₃ + (cp)σ₁`
  (`einstein_dirac_eigenvalue`); the `(pc)` term is precisely the off-diagonal `cp σ₁`. The Dirac
  factorization `H² = ((mc²)² + (cp)²)·1` realizes the dispersion.
* **Nagao–Nielsen complex oscillator.** With the complex mass `m = m_R + i m_I`, the physical mass is
  the effective mass `m_eff = |m|²/Re m`, and the full dispersion holds with it
  (`fullEinstein_complexMass`); the reversible limit `m_I = 0` recovers the real mass.
* **TDSE.** The on-shell mode `Ψ(t) = e^{−iEt/ℏ}` solves the time-dependent Schrödinger equation
  `iℏ ∂_t Ψ = E Ψ` (`greenKernel_satisfies_tdse`) — the `H_C`-evolution at eigenvalue `E`.
* **TISE.** The same `E` is the stationary eigenvalue of the (Hermitian, `H_R`) Dirac Hamiltonian,
  `H ψ = E ψ` (`einstein_dirac_eigenvalue`, the `det(E·1 − H) = 0` solvability).

## Main results

* `einsteinEnergy`, `einsteinEnergy_sq`, `einstein_fullDispersion` — `E² = (mc²)² + (cp)²`.
* `einsteinEnergy_rest` (`p = 0 ⟹ E = mc²`), `einsteinEnergy_massless` (`m = 0 ⟹ E = c|p|`).
* `einstein_dirac_eigenvalue` — Dirac/TISE: `E` is an eigenvalue of `H = (mc²)σ₃ + (cp)σ₁`.
* `greenKernel_hasDerivAt_time`, `schrodinger_eigenrelation`, `greenKernel_satisfies_tdse` — TDSE.
* `fullEinstein_complexMass` — Nagao–Nielsen effective mass `m_eff = |m|²/Re m`.
* `fullEinstein_dirac_tdse_tise` — the bundled four-pillar consistency.

## Key equations

* `E² = (pc)² + (mc²)²` — relativistic energy–momentum relation (Einstein 1905; rest term
  `E = mc²` is the `p = 0` slice).
* `H = c α·p + mc² β`, `{γ^μ, γ^ν} = 2η^{μν}`, `H² = ((mc²)² + (cp)²)·1` — Dirac equation and its
  Klein–Gordon factorization (Dirac 1928).
* `iℏ ∂_t Ψ = H_C Ψ`, `H_C = H_R − iĤ_I`, `Ψ(t) = e^{−iEt/ℏ}` — the (non-Hermitian) TDSE; and
  `H_C ψ = E ψ` — the TISE. (The complex Hamiltonian `H_C = H_R − iĤ_I` is defined and referenced
  in `FiniteTarget.NagaoNielsenSchrodinger`.)

## References

* A. Einstein, *Ist die Trägheit eines Körpers von seinem Energieinhalt abhängig?*, Ann. Phys.
  **323** (13) (1905) 639–641. doi:10.1002/andp.19053231314 (`E = mc²`).
* P. A. M. Dirac, *The Quantum Theory of the Electron*, Proc. R. Soc. Lond. A **117** (778) (1928)
  610–624. doi:10.1098/rspa.1928.0023 (the Dirac equation).
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. **126** (2011)
  1021–1049. doi:10.1143/PTP.126.1021 (arXiv:1104.3381); momentum/Feynman path integral:
  arXiv:1304.4017; complex `m, ω` oscillator: arXiv:1902.01424.
* This development: `ComplexEinstein.ComplexMassEinsteinEquations`, `Dirac.KleinGordonDiracFactorization`,
  `Dirac.ConfinedPhotonDiracDispersion`, `NonHermitianComplexAction.GreenFunction`, `PathIntegral.MomentumPathIntegral`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency

/-! ## §A — the full Einstein energy–momentum relation `E² = (pc)² + (mc²)²` -/

/-- **The full Einstein on-shell energy** `E = √((mc²)² + (cp)²)` — rest energy `mc²` *and* the
momentum term `cp`. -/
def einsteinEnergy (m c p : ℝ) : ℝ := photonDispersion (m * c ^ 2) c p

/-- **The full Einstein energy–momentum relation** `E² = (mc²)² + (cp)²` (the `+ (pc)²` the rest
formula `E = mc²` was missing). -/
theorem einsteinEnergy_sq (m c p : ℝ) :
    einsteinEnergy m c p ^ 2 = (m * c ^ 2) ^ 2 + (c * p) ^ 2 :=
  photonDispersion_sq (m * c ^ 2) c p

/-- **The full Einstein relation as a Klein–Gordon mass-shell** with rest energy `mc²`, velocity `c`,
momentum `p`. -/
theorem einstein_fullDispersion (m c p : ℝ) :
    kleinGordonRelation (m * c ^ 2) c p (einsteinEnergy m c p) :=
  photonDispersion_kleinGordon (m * c ^ 2) c p

/-- **Rest limit** `p = 0 ⟹ E = mc²`: recovers the rest energy (`ComplexEinstein.ComplexMassEinsteinEquations`). -/
theorem einsteinEnergy_rest (m c : ℝ) (h : 0 ≤ m * c ^ 2) :
    einsteinEnergy m c 0 = m * c ^ 2 := by
  unfold einsteinEnergy
  rw [photonDispersion_rest]
  exact abs_of_nonneg h

/-- **Massless limit** `m = 0 ⟹ E = c|p|`: the pure momentum term `pc` — the photon on the `45°`
light cone (`Rapidity.LightCone45RapidityUnification`). -/
theorem einsteinEnergy_massless (c p : ℝ) : einsteinEnergy 0 c p = |c * p| := by
  unfold einsteinEnergy photonDispersion
  rw [show (0 : ℝ) * c ^ 2 = 0 by ring, show (0 : ℝ) ^ 2 + (c * p) ^ 2 = (c * p) ^ 2 by ring,
    Real.sqrt_sq_eq_abs]

/-! ## §B — consistency with the Dirac equation (and the TISE) -/

/-- **Dirac / TISE consistency**: the full-Einstein energy `E` is an eigenvalue of the Dirac
Hamiltonian `H = (mc²)σ₃ + (cp)σ₁` — `det(E·1 − H) = 0`, the stationary (TISE) condition
`H ψ = E ψ`. The momentum term `cp` is the off-diagonal `σ₁` block; the Dirac factorization
`H² = ((mc²)² + (cp)²)·1` is the Klein–Gordon dispersion. -/
theorem einstein_dirac_eigenvalue (m c p : ℝ) :
    (einsteinEnergy m c p • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        - diracHamiltonian (m * c ^ 2) (c * p)).det = 0 :=
  (diracHamiltonian_eigenvalue_iff_kleinGordon (m * c ^ 2) c p (einsteinEnergy m c p)).mpr
    (einstein_fullDispersion m c p)

/-! ## §C — consistency with the Nagao–Nielsen complex oscillator (complex mass) -/

/-- **Complex-mass consistency**: with the Nagao–Nielsen complex mass `m = m_R + i m_I` the physical
mass is the effective mass `m_eff = |m|²/Re m`, and the full Einstein dispersion holds with it. The
imaginary mass enters only through the (real) effective mass; the reversible limit `m_I = 0` gives
the real mass `m_R`. -/
theorem fullEinstein_complexMass (m_R m_I c p : ℝ) (hm_R : m_R ≠ 0) :
    effectiveMass m_R m_I = Complex.normSq (complexMass m_R m_I) / m_R
      ∧ kleinGordonRelation (effectiveMass m_R m_I * c ^ 2) c p
          (einsteinEnergy (effectiveMass m_R m_I) c p) :=
  ⟨effectiveMass_eq_complexMass_normSq_div m_R m_I hm_R,
   einstein_fullDispersion (effectiveMass m_R m_I) c p⟩

/-! ## §D — consistency with the TDSE `iℏ ∂_t Ψ = E Ψ` -/

/-- **The on-shell mode is differentiable in time**, with `d/dt e^{−iEt/ℏ} = e^{−iEt/ℏ}·(−iE/ℏ)`. -/
theorem greenKernel_hasDerivAt_time (lam : ℂ) (ℏ t : ℝ) :
    HasDerivAt (fun s : ℝ => greenKernel lam ℏ s)
      (greenKernel lam ℏ t * (-Complex.I * lam * 1 / (ℏ : ℂ))) t := by
  have hofR : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  exact ((hofR.const_mul (-Complex.I * lam)).div_const (ℏ : ℂ)).cexp

/-- **The Schrödinger eigen-relation** `iℏ · (e^{−iEt/ℏ}·(−iE/ℏ)) = E · e^{−iEt/ℏ}` (algebraic core
of the TDSE; `i(−i) = 1` and the `ℏ` cancels). -/
theorem schrodinger_eigenrelation (lam G : ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    (Complex.I * (ℏ : ℂ)) * (G * (-Complex.I * lam * 1 / (ℏ : ℂ))) = lam * G := by
  have hℏc : (ℏ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
  rw [mul_one,
    show (Complex.I * (ℏ : ℂ)) * (G * (-Complex.I * lam / (ℏ : ℂ)))
      = (Complex.I * -Complex.I) * lam * G * ((ℏ : ℂ) / (ℏ : ℂ)) by ring,
    div_self hℏc, mul_one, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

/-- **The on-shell mode solves the TDSE** `iℏ ∂_t Ψ = E Ψ` with `Ψ(t) = e^{−iEt/ℏ}` (the
`H_C`-evolution at eigenvalue `E`). -/
theorem greenKernel_satisfies_tdse (lam : ℂ) (ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    (Complex.I * (ℏ : ℂ)) * deriv (fun s : ℝ => greenKernel lam ℏ s) t
      = lam * greenKernel lam ℏ t := by
  rw [(greenKernel_hasDerivAt_time lam ℏ t).deriv]
  exact schrodinger_eigenrelation lam (greenKernel lam ℏ t) ℏ hℏ

/-! ## §E — the bundled four-pillar consistency -/

/-- **The full Einstein dispersion is consistent with Dirac, the TISE, and the TDSE.** For a physical
mass `m`, momentum `p`, speed `c`, and `ℏ ≠ 0`:

* **(full dispersion)** `E² = (mc²)² + (cp)²` — the complete energy–momentum relation;
* **(Dirac / TISE)** `E` is an eigenvalue of the Dirac Hamiltonian `(mc²)σ₃ + (cp)σ₁` (`H ψ = E ψ`);
* **(TDSE)** the on-shell mode `e^{−iEt/ℏ}` solves `iℏ ∂_t Ψ = E Ψ`.

Together with `fullEinstein_complexMass` (the Nagao–Nielsen effective mass `|m|²/Re m`), this is the
complete consistency of the full Einstein relation across the four pillars. -/
theorem fullEinstein_dirac_tdse_tise (m c p ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    einsteinEnergy m c p ^ 2 = (m * c ^ 2) ^ 2 + (c * p) ^ 2
      ∧ (einsteinEnergy m c p • (1 : Matrix (Fin 2) (Fin 2) ℝ)
          - diracHamiltonian (m * c ^ 2) (c * p)).det = 0
      ∧ (Complex.I * (ℏ : ℂ))
            * deriv (fun s : ℝ => greenKernel (einsteinEnergy m c p : ℂ) ℏ s) t
          = (einsteinEnergy m c p : ℂ) * greenKernel (einsteinEnergy m c p : ℂ) ℏ t :=
  ⟨einsteinEnergy_sq m c p, einstein_dirac_eigenvalue m c p,
   greenKernel_satisfies_tdse (einsteinEnergy m c p : ℂ) ℏ t hℏ⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency

end

end

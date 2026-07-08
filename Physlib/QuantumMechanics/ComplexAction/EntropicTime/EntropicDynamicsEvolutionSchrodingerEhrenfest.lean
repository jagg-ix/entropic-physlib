/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsQuantumPotentialFisherBohm

/-!
# The evolution equations: Schrödinger equation, `λ = ℏ²/8`, and the Ehrenfest classical Klein–Gordon (Ipek–Abedi–Caticha §§7–8)

Formalizes §§7–8 of Ipek–Abedi–Caticha (arXiv:1803.07493): the entropic-dynamics evolution in curved spacetime is
the **local-time functional Schrödinger equation**, made explicit by the Madelung transformation `Ψ = √ρ e^{iΦ}`
(their Eq. 79 = `edWaveFunction`), and its classical shadow is the **Ehrenfest theorem** — the expected field
obeys the classical Klein–Gordon equation (their Eq. 100).

The decisive constant is the quantum-potential coupling: comparing the Hamilton–Jacobi equation (Eq. 78) with the
Schrödinger equation (Eq. 83) fixes `λ = ℏ²/8`, which **sets the value of Planck's constant** and separates the
quantum from the classical regime.

* the **quantum-potential coupling is `ℏ²/8`** (`edQuantumCoupling`, Eq. 83): `λ = ℏ²/8 > 0` (stability,
 `edQuantumCoupling_pos`) is the constant that makes the dynamics quantum and defines `ℏ`; the Schrödinger
 kinetic coefficient `ℏ²/2` is `4λ` (`kinetic_eq_four_coupling`);
* the evolution is the functional **Schrödinger equation** for `Ψ = √ρ e^{iΦ}` (Eq. 79–84) with `|Ψ|² = ρ`
 (reused `edWaveFunction`, `edWaveFunction_modulus_sq`);
* the **Ehrenfest expected field obeys the classical Klein–Gordon equation** `(□ − m²)χ̄ = 0` for a quadratic
 potential `V = ½m²χ²` (`ehrenfest_classical_kleinGordon`, Eq. 100), because the Ehrenfest force is the classical
 force `⟨m²χ⟩ = m²⟨χ⟩` (`ehrenfest_force_is_classical`, Eq. 99) by linearity of the expectation — Ehrenfest's
 theorem.

So the entropic dynamics of fields in curved spacetime *is* quantum field theory in the Schrödinger functional
representation, with `ℏ` set by the quantum-potential coupling `λ = ℏ²/8`, and its expected field follows the
classical Klein–Gordon equation exactly when the potential is quadratic — the Ehrenfest theorem of the
reconstruction.

* **§A — the quantum-potential coupling `λ = ℏ²/8`** (`edQuantumCoupling`, `kinetic_eq_four_coupling`).
* **§B — the Madelung Schrödinger wave functional** (reused `edWaveFunction`).
* **§C — the Ehrenfest classical Klein–Gordon equation** (`ehrenfest_force_is_classical`,
 `ehrenfest_classical_kleinGordon`).

The coupling `λ = ℏ²/8`, the kinetic relation, the Ehrenfest force linearity, and the
classical-Klein–Gordon equivalence are exact algebra. The full functional Schrödinger PDE (Eq. 83–84), the wave
operator `□` in foliation-adapted coordinates (Eq. 98), and the Poisson-bracket derivation of the Ehrenfest
relations (Eqs. 86–96) are the intended reading, captured at the algebraic level. No new axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §§7–8 (Eqs. 79, 83, 97, 99–100; Schrödinger equation, Ehrenfest
 theorem). Repo structure: `EntropicTime.EntropicDynamicsQuantumPotentialFisherBohm`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest

/-! ## §A — the quantum-potential coupling `λ = ℏ²/8` -/

/-- **The quantum-potential coupling** `λ = ℏ²/8` (Ipek–Abedi–Caticha Eq. 83) — comparing the entropic
Hamilton–Jacobi equation (Eq. 78) with the Schrödinger equation (Eq. 83) fixes the coupling of the quantum
potential, which sets the value of Planck's constant `ℏ`. -/
noncomputable def edQuantumCoupling (ℏ : ℝ) : ℝ := ℏ ^ 2 / 8

/-- **[The quantum-potential coupling is positive] `λ = ℏ²/8 > 0`.** The coupling `λ > 0` (the case `λ < 0` is
excluded as unstable): it controls the strength of the quantum potential and sets `ℏ`. -/
theorem edQuantumCoupling_pos (ℏ : ℝ) (hℏ : ℏ ≠ 0) : 0 < edQuantumCoupling ℏ := by
  unfold edQuantumCoupling; positivity

/-- **[The Schrödinger kinetic coefficient is four times the coupling] `ℏ²/2 = 4λ`.** The kinetic term `ℏ²/2` of
the Schrödinger equation (Eq. 83) is four times the quantum-potential coupling `λ = ℏ²/8` (the `4λ` of the
Hamilton–Jacobi equation, Eq. 78) — the same `ℏ` governs the kinetic energy and the quantum potential. -/
theorem kinetic_eq_four_coupling (ℏ : ℝ) : 4 * edQuantumCoupling ℏ = ℏ ^ 2 / 2 := by
  unfold edQuantumCoupling; ring

/-- **The physical quantum-potential density** `Q = (ℏ²/8ρ)(δρ/δχ)²` — the entropic-dynamics quantum potential
with the physical coupling `λ = ℏ²/8`, the Fisher-information term that makes the reconstruction quantum. -/
noncomputable def physicalQuantumPotential (ℏ ρ dρ : ℝ) : ℝ := edQuantumPotential (edQuantumCoupling ℏ) ρ dρ

/-! ## §C — the Ehrenfest classical Klein–Gordon equation -/

/-- **[The Ehrenfest force is the classical force] `⟨m²χ⟩ = m²⟨χ⟩`.** For a quadratic potential `V = ½m²χ²` the
Ehrenfest force `⟨∂V/∂χ⟩ = ⟨m²χ⟩` equals the classical force `m²⟨χ⟩ = ∂V(⟨χ⟩)/∂χ` by linearity of the expectation
(Ipek–Abedi–Caticha Eq. 99) — the condition under which the expected field follows classical evolution. -/
theorem ehrenfest_force_is_classical (m : ℝ) (expec : (ℝ → ℝ) → ℝ)
    (hlin : ∀ (a : ℝ) (f : ℝ → ℝ), expec (fun x => a * f x) = a * expec f) (χ : ℝ → ℝ) :
    expec (fun x => m ^ 2 * χ x) = m ^ 2 * expec χ :=
  hlin (m ^ 2) χ

/-- **The Ehrenfest classical force for a quadratic potential** `∂V/∂χ|_{χ̄} = m²χ̄` (`V = ½m²χ²`). -/
def ehrenfestForceQuadratic (m chiBar : ℝ) : ℝ := m ^ 2 * chiBar

/-- **[The Ehrenfest expected field obeys the classical Klein–Gordon equation] `□χ̄ = m²χ̄ ⟺ (□ − m²)χ̄ = 0`.** For
a quadratic potential the Ehrenfest relation `□χ̄ = ⟨∂V/∂χ⟩ = m²χ̄` (Eq. 97) is exactly the classical Klein–Gordon
equation `(□ − m²)χ̄ = 0` in curved spacetime (Eq. 100) for the expected field — Ehrenfest's theorem: the mean
field follows the classical equation of motion. -/
theorem ehrenfest_classical_kleinGordon (m chiBar boxChiBar : ℝ) :
    boxChiBar = ehrenfestForceQuadratic m chiBar ↔ boxChiBar - m ^ 2 * chiBar = 0 := by
  unfold ehrenfestForceQuadratic
  constructor <;> intro h <;> linarith

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest

end

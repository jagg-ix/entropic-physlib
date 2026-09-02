/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
meta import Zil

/-!
# Madelung polar decomposition `ψ = R · exp(i·S/ℏ)`

Port of the Bohmian / Madelung core abstractions from
``
into physlib's QM scope.

The Madelung 1927 polar decomposition writes a quantum
wavefunction as

  `ψ(x) = R(x) · exp(i · S(x) / ℏ)`

with `R : ℝⁿ → ℝ≥0` the **amplitude** and `S : ℝⁿ → ℝ` the
**phase**.  This is the structural basis of Bohmian mechanics
(de Broglie 1927, Bohm 1952): from the polar form one extracts a
guidance velocity `v = ∇S / m` and a quantum potential
`Q = −ℏ²·ΔR / (2m·R)`.  The Born rule `|ψ|² = R²` falls out
algebraically.

This file provides the **kernel-safe algebraic content** of the
polar form:

* The `MadelungWaveFunction` structure carrying `(R, S, ℏ)`.
* The Madelung density `ρ := R²` and its non-negativity.
* The Madelung Born rule `madelungDensity_eq_wavefunctionNormSq : ρ = ‖ψ‖²`.
* The norm identity `madelung_wf_norm : ‖R·exp(i·S/ℏ)‖ = R`.
* The complex-observable identity `‖z‖² = re² + im²`.

The Phase-2 PDE content (the quantum potential `Q = −ℏ²·ΔR/(2m·R)`,
the continuity equation `∂tρ + ∇·(ρv) = 0`, the Hamilton–Jacobi–
Madelung equation `∂tS + |∇S|²/(2m) + V − Q = 0`) requires
Sobolev / PDE infrastructure and is a separate scope.

## Contents


* `MadelungWaveFunction` — record `(amplitude, phase, ℏ)` with
  `0 ≤ amplitude`, `0 < ℏ`.
* `madelungDensity : MadelungWaveFunction → ℝ` — `ρ := R²`.
* `madelungDensity_nonneg`.
* `madelung_born_rule` — `ρ = R²` (definitional value identity, consumed downstream).
* `madelungDensity_eq_wavefunctionNormSq` — `ρ = ‖ψ‖²` (the genuine Born-rule identity, via `madelung_wf_norm`).


* `madelung_phase_factor_norm` — `‖exp(iθ)‖ = 1`.
* `madelung_wf_norm` — `‖R · exp(i·S/ℏ)‖ = R`.


* `BohmianQuantumPotential` — record `(mass, wf, ΔR)`.
* `quantumPotentialScale : Q · R / ΔR := −ℏ²/(2m)` — the
  pre-Laplacian scale factor.
* `quantumPotentialScale_neg` — strictly negative.
* `bohmianVelocityProxy` — `S / (m·ℏ)` (guidance-velocity proxy).

## References

* Madelung 1927, *Z. Phys.* 40, 322 — original polar form.
* de Broglie 1927 — pilot-wave theory.
* Bohm 1952, *Phys. Rev.* 85, 166 — Bohmian mechanics.
* Source: ``
  (commit imported as-of 2026-06-05).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

open Real Complex


/-- **Madelung polar decomposition data** `ψ = R·exp(i·S/ℏ)`.

* `amplitude` is the non-negative real amplitude `R`.
* `phase` is the real phase `S` (in units of action).
* `hbar` is Planck's constant `ℏ > 0`.

Following Madelung 1927; identical structure to
`MadelungWaveFunction`. -/
structure MadelungWaveFunction where
  amplitude : ℝ
  amplitude_nonneg : 0 ≤ amplitude
  phase : ℝ
  hbar : ℝ
  hbar_pos : 0 < hbar

/-- **Madelung / Born density** `ρ := R²`. -/
def madelungDensity (ψ : MadelungWaveFunction) : ℝ := ψ.amplitude ^ 2

/-- The Madelung density is non-negative. -/
lemma madelungDensity_nonneg (ψ : MadelungWaveFunction) :
    0 ≤ madelungDensity ψ := by
  unfold madelungDensity
  positivity

/-- **Madelung density value** `ρ = R²` — the density unfolds to the squared amplitude (a definitional
identity). The genuine Born-rule statement `ρ = ‖ψ‖²`, in which the wavefunction modulus-squared actually
appears, is `madelungDensity_eq_wavefunctionNormSq`; this lemma records only the amplitude value that
downstream rewrites (e.g. `BohmQuantumPotential`) consume. -/
lemma madelung_born_rule (ψ : MadelungWaveFunction) :
    madelungDensity ψ = ψ.amplitude ^ 2 := rfl


/-- **Pure phase factor has unit modulus**: `‖exp(i·θ)‖ = 1`. -/
lemma madelung_phase_factor_norm (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- **Madelung wavefunction norm equals amplitude**:

  `‖R · exp(i · S / ℏ)‖ = R`

provided `R ≥ 0`.  This is the load-bearing identity for
recovering the amplitude `R` from the wavefunction `ψ`. -/
lemma madelung_wf_norm (ψ : MadelungWaveFunction) :
    ‖(ψ.amplitude : ℂ) * Complex.exp (Complex.I * ((ψ.phase : ℂ) / (ψ.hbar : ℂ)))‖
      = ψ.amplitude := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ψ.amplitude_nonneg, mul_comm,
      show Complex.I * ((ψ.phase : ℂ) / (ψ.hbar : ℂ)) =
          ((ψ.phase / ψ.hbar : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **Madelung Born rule** `ρ = ‖ψ‖²` — the Madelung density equals the **modulus-squared of the
wavefunction** `ψ = R·exp(i S/ℏ)`, not merely the squared amplitude. This is the genuine Born-rule identity:
the wavefunction `‖ψ‖²` appears explicitly, established by `madelung_wf_norm` (`‖ψ‖ = R`), so `ρ = R² = ‖ψ‖²`
is the algebraic content of the polar decomposition rather than a fresh quantum postulate. -/
theorem madelungDensity_eq_wavefunctionNormSq (ψ : MadelungWaveFunction) :
    madelungDensity ψ
      = ‖(ψ.amplitude : ℂ) * Complex.exp (Complex.I * ((ψ.phase : ℂ) / (ψ.hbar : ℂ)))‖ ^ 2 := by
  rw [madelungDensity, madelung_wf_norm]


/-- **Bohmian quantum-potential record**.

Carries the mass `m`, the Madelung wavefunction `ψ`, and the
amplitude Laplacian `ΔR`.  The quantum potential is
`Q = −(ℏ² / (2m)) · (ΔR / R)` — this file provides the
*pre-Laplacian* scale factor `−ℏ²/(2m)`; the full
`Q := scale · ΔR / R` definition would require Sobolev/PDE
machinery for `R(x)` and is deferred. -/
structure BohmianQuantumPotential where
  mass : ℝ
  mass_pos : 0 < mass
  wf : MadelungWaveFunction
  laplacianAmplitude : ℝ

/-- **Universal Bohmian quantum-potential scale**: `−ℏ² / (2m)`.

The dimensional/sign-carrying prefactor of the full quantum
potential `Q = scale · ΔR / R`.  Strictly negative when `ℏ, m > 0`. -/
def quantumPotentialScale (q : BohmianQuantumPotential) : ℝ :=
  -(q.wf.hbar ^ 2) / (2 * q.mass)

/-- The Bohmian quantum-potential scale is **strictly negative**.

Encodes the sign of the quantum potential in regions of positive
amplitude curvature (`ΔR > 0`): `Q = scale · ΔR / R < 0` there. -/
lemma quantumPotentialScale_neg (q : BohmianQuantumPotential) :
    quantumPotentialScale q < 0 := by
  unfold quantumPotentialScale
  apply div_neg_of_neg_of_pos
  · linarith [sq_pos_of_pos q.wf.hbar_pos]
  · exact mul_pos two_pos q.mass_pos

/-- **Guidance-velocity proxy** `v ≃ S / (m·ℏ)`.

The Bohmian guidance equation reads `m · ẋ = ∇S`, so the
position-space velocity scales as `∇S / m`.  The action-scaled
proxy `S / (m·ℏ)` is dimensionally `(velocity / ℏ)` and is the
phase-driven evolution rate in natural units. -/
def bohmianVelocityProxy (q : BohmianQuantumPotential) : ℝ :=
  q.wf.phase / (q.mass * q.wf.hbar)

/-- The Bohmian-velocity-proxy denominator is **strictly positive**. -/
lemma bohmianVelocity_denom_pos (q : BohmianQuantumPotential) :
    0 < q.mass * q.wf.hbar :=
  mul_pos q.mass_pos q.wf.hbar_pos

end Physlib.QuantumMechanics.Schrodinger

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.Schrodinger.madelung_born_rule where
  formalizes @ "claim:the-madelung-density-equals-the-squared-amplitude",
  supported_by @ "paper:madelung-1927-hydrodynamic-form-of-the-schrodinger-equation"

zil attach Physlib.QuantumMechanics.Schrodinger.madelungDensity_eq_wavefunctionNormSq where
  formalizes @ "claim:the-madelung-density-is-the-born-rule-modulus-squared-of-the-wavefunction",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.madelung_wf_norm",
  supported_by @ "paper:madelung-1927-hydrodynamic-form-of-the-schrodinger-equation"

zil attach Physlib.QuantumMechanics.Schrodinger.quantumPotentialScale_neg where
  formalizes @ "claim:the-madelung-quantum-potential-scale-is-negative-the-minus-hbar-squared-over-two-m-prefactor",
  requires @ "claim:the-madelung-density-is-the-born-rule-modulus-squared-of-the-wavefunction"

zil_file_contract physlib.madelungPolarDecomposition where
  promises "The Madelung polar decomposition of the wavefunction: the density is the Born-rule modulus squared, the phase factor is unimodular, and the quantum-potential prefactor is the negative minus-hbar-squared-over-two-m scale, casting the Schrodinger equation in hydrodynamic form."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.Schrodinger.madelungDensity",
    "lean:Physlib.QuantumMechanics.Schrodinger.quantumPotentialScale"]
  forbids_substitutes ["the full nonlinear Madelung hydrodynamics, only the polar-decomposition identities",
    "an interpretation of the quantum potential, kinematic decomposition only"]
  witnessed_by [Physlib.QuantumMechanics.Schrodinger.madelung_born_rule,
    Physlib.QuantumMechanics.Schrodinger.madelungDensity_eq_wavefunctionNormSq,
    Physlib.QuantumMechanics.Schrodinger.quantumPotentialScale_neg]

/- ZIL-END -/

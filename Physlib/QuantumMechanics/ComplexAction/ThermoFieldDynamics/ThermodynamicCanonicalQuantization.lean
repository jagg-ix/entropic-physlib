/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.InnerProductHeisenberg
public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.GreenFunction
public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator

/-!
# Canonical quantization of thermodynamics: pseudo-Hermiticity = Q-formalism, `[ŝ,T̂] = ib̄`

This file links the periodic Q-Hermitian `Q`-formalism / complex Schrödinger generator
(`PeriodicQHermitian.Basic`, `NonHermitianComplexAction.ComplexHamiltonian`, `NonHermitian.Propagator`) and the
Misra internal-time operator (`RelationalTime.LiouvillianAgeOperator`) to **F. C. E. Lima,
et al., *Canonical quantization for Equilibrium Thermodynamics*, arXiv:2511.14121**, which
quantizes thermodynamics à la Dirac.

## §A — Pseudo-Hermiticity (App. C) *is* the `Q`-formalism / complex Schrödinger generator

The paper's pseudo-Hermitian condition (Eq. C1) `Ĥ† = Θ̂ Ĥ Θ̂⁻¹` with a Hermitian metric
`Θ̂` is **exactly** Nagao–Nielsen `Q`-Hermiticity `Ĥ^{†Q} = Ĥ` (`Θ̂ = Q`):

* `pseudoHermitian_iff_qHermitian` — `Ĥ† = Θ Ĥ Θ⁻¹ ↔ qDagger Θ Ĥ = Ĥ`. The paper's metric
  `Θ̂` is the `Q` of `PeriodicQHermitian.Basic`; its `Θ̂`-inner product `⟨ϕ,ψ⟩_Θ = ⟨ϕ,Θ̂ψ⟩` (Eq. C2)
  is `qInner Θ` (`= I_Q`, `NonHermitianComplexAction.InnerProductHeisenberg`), and its quasi-Hermitian
  observables `Ô† = Θ̂ Ô Θ̂⁻¹` (Eq. C9–C10), whose expectation values are real, are the
  `Q`-Hermitian `Ô` of `qExpect_qHermitian_real`.

The paper's central point (Eq. C10): since `Θ̂(t)` is generally time-dependent, the
non-Hermitian `Ĥ(t)` is **the generator of evolution, not the observable** — the observable
energy is the associated Hermitian `ĥ = H_R`. This is precisely the complex Schrödinger
generator `H_C = H_R − i H_I` (`FiniteTarget.NagaoNielsenSchrodinger`,
`NonHermitianComplexAction.ComplexHamiltonian`): `H_C` generates evolution (its propagator is
`NonHermitianComplexAction.GreenFunction.greenMatrix`), while the observable is its `Q`-Hermitian part
`H_R = Ĥ_Qh` (`qHermPart_eq_HR`). The dynamical metric relation (Eq. C4),
`iℏ ∂_t Θ̂ = Ĥ† Θ̂ − Θ̂ Ĥ`, is the `Q`-formalism's statement that probability is conserved
iff the generator is `Q`-Hermitian (`PeriodicQHermitian.Ehrenfest.trace_dissipativeGen`).

## §B — The thermodynamic canonical pair `[ŝ,T̂] = i b̄` *is* the Misra time operator

The paper promotes the thermodynamic Poisson bracket `{s, T} = 1` (entropy `s`, temperature
`T`) to the commutator (Eq. 37) `[ŝ, T̂] = i b̄`, with `b̄` a positive constant of dimension
energy — the **quantum of thermodynamics** (the `ℏ` of thermodynamics). In the spectral
representation `ŝ =` multiplication by `s`, `T̂ = −i b̄ d/ds`:

* `entropy_temperature_commutator` — **`[ŝ, T̂] = i b̄`** (Eq. 37). This is structurally the
  Misra–Prigogine–Courbage canonical conjugacy `i[L, T] = I`
  (`RelationalTime.LiouvillianAgeOperator.liouvillian_age_ccr`): the **entropy operator `ŝ`
  plays the role of the Liouvillian `L`** (multiplication by the spectral variable) and the
  **temperature operator `T̂` the role of the internal-time / age operator** (`±i·d/d·`),
  with `b̄` in place of `ℏ`. So the Misra internal time conjugate to the generator and the
  thermodynamic temperature conjugate to entropy are the *same* canonical structure.

## §C — Link to `QFT.Wick` and `Lindblad`

`b̄` is the thermodynamic `ℏ`: the path-integral / complex-action weight is `e^{iS/b̄}`,
modulus `e^{−S_I/b̄}`, the entropic damping with `b̄` setting the entropy scale. *Proved here*
(mirroring `QFT.Wick.Consistency.complexActionWeight` / `NonHermitianComplexAction.EntropicDampingEquivalence`):

* `thermoActionWeight`, `norm_thermoActionWeight` — `‖e^{iS/b̄}‖ = e^{−S_I/b̄}`.
* `log_norm_thermoActionWeight` — `S_I/b̄ = −log‖w‖` (the entropy = `−b̄·log‖w‖`).
* `norm_greenKernel_eq_thermoActionWeight` — the modified Green function's decay
  (`NonHermitianComplexAction.GreenFunction.norm_greenKernel`) *is* this entropic damping, with
  `S_I = −Im λ·t = Γt`.

The dissipative (anti-`Q`-Hermitian) part `H_I` is the entropy-production generator; from a
Lindblad jump `L` it is `H_I = L†L ≥ 0` (`Lindblad.GreensFunction.lindbladDissipator`), and
the Green-function decay rate `Γ = ‖Lψ‖²` is the entropy-production rate `(2/b̄)Γ`
(`Lindblad.GreensFunction.lindblad_greenKernel_rate_eq_entropyRate`; left as a cross-module
reference, since that operator-level material lives in the heavier `Lindblad` layer). Thus
entropy quantization (`[ŝ,T̂] = ib̄`), the non-Hermitian generator (`H_C`), the modified Green
function, and the Lindblad dissipation are one structure, with `b̄` the unifying
thermodynamic quantum.

Reference: F. C. E. Lima et al., arXiv:2511.14121, §III (Eq. 37), App. C (Eqs. C1–C10);
Nagao–Nielsen arXiv:1104.3381 (`Q`-formalism); Misra–Prigogine–Courbage 1979 (time
operator).
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization

open ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.RelationalTime

/-! ## §A — Pseudo-Hermiticity (App. C) = `Q`-Hermiticity -/

/-- **Pseudo-Hermiticity (Eq. C1) is `Q`-Hermiticity**: for an invertible metric `Θ`,
`Ĥ† = Θ Ĥ Θ⁻¹` iff `Ĥ^{†Q} = Ĥ` (with `Θ = Q`). The paper's metric operator `Θ̂` is the
Nagao–Nielsen `Q`; the two non-Hermitian frameworks coincide. -/
theorem pseudoHermitian_iff_qHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {Θ H : Matrix n n ℂ} (hΘ : IsUnit Θ.det) :
    Hᴴ = Θ * H * Θ⁻¹ ↔ qDagger Θ H = H := by
  rw [qDagger]
  constructor
  · intro h
    rw [h]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul Θ hΘ, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul Θ hΘ, Matrix.one_mul]
  · intro h
    have key : Θ * (Θ⁻¹ * Hᴴ * Θ) * Θ⁻¹ = Hᴴ := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv Θ hΘ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv Θ hΘ, Matrix.one_mul]
    rw [← key, h]

/-! ## §B — The thermodynamic canonical pair `[ŝ,T̂] = i b̄` -/

/-- **The entropy operator** `ŝ`: multiplication by the entropy variable `s`, `(ŝ f)(s) =
s·f(s)` — the thermodynamic analogue of Misra's Liouvillian `L` (multiplication by the
spectral variable). -/
def entropyOperator (f : ℝ → ℂ) : ℝ → ℂ := fun s => (s : ℂ) * f s

/-- **The temperature operator** `T̂ = −i b̄ d/ds` — the thermodynamic momentum conjugate to
entropy (the analogue of Misra's internal-time/age operator `T = i d/dλ`). -/
noncomputable def temperatureOperator (b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun s => -Complex.I * (b : ℂ) * deriv f s

/-- **The entropy operator *is* the Misra Liouvillian** — both are multiplication by the
spectral variable: `entropyOperator = spectralLiouvillian`. (The equivalence the §B
docstring asserts, proved.) -/
theorem entropyOperator_eq_spectralLiouvillian :
    (entropyOperator : (ℝ → ℂ) → ℝ → ℂ) = spectralLiouvillian := rfl

/-- **The temperature operator *is* `−b̄·` the Misra internal-time/age operator**:
`T̂ = −b̄·(i d/ds) = −b̄·T_age`. Together with `entropyOperator_eq_spectralLiouvillian` this
shows the thermodynamic conjugate pair `(ŝ, T̂)` is the Misra conjugate pair `(L, T)`,
rescaled by the thermodynamic quantum `b̄ ↔ ℏ`. -/
theorem temperatureOperator_eq_neg_smul_ageOperator (b : ℝ) (f : ℝ → ℂ) :
    temperatureOperator b f = fun s => -(b : ℂ) * ageOperator f s := by
  funext s
  simp only [temperatureOperator, ageOperator]
  ring

/-- **`[ŝ, T̂] = i b̄`** (arXiv:2511.14121 Eq. 37), **derived from the Misra–Prigogine
canonical conjugacy** `[L, T] = −i` (`liouvillian_age_commutator`, the infinitesimal form of
`i[L,T] = I`) via the operator identifications `ŝ = L`, `T̂ = −b̄·T`. The thermodynamic
commutator is thus literally `−b̄` times the Misra commutator: `[ŝ,T̂] = −b̄·[L,T] = −b̄·(−i)
= i b̄`. -/
theorem entropy_temperature_commutator (b : ℝ) (f : ℝ → ℂ) (s : ℝ)
    (hf : DifferentiableAt ℝ f s) :
    entropyOperator (temperatureOperator b f) s - temperatureOperator b (entropyOperator f) s
      = Complex.I * (b : ℂ) * f s := by
  have e1 : entropyOperator (temperatureOperator b f) s
      = -(b : ℂ) * spectralLiouvillian (ageOperator f) s := by
    simp only [entropyOperator, temperatureOperator, spectralLiouvillian, ageOperator]; ring
  have e2 : temperatureOperator b (entropyOperator f) s
      = -(b : ℂ) * ageOperator (spectralLiouvillian f) s := by
    rw [entropyOperator_eq_spectralLiouvillian]
    simp only [temperatureOperator, ageOperator]; ring
  rw [e1, e2,
    show -(b : ℂ) * spectralLiouvillian (ageOperator f) s
        - -(b : ℂ) * ageOperator (spectralLiouvillian f) s
      = -(b : ℂ) * (spectralLiouvillian (ageOperator f) s
        - ageOperator (spectralLiouvillian f) s) by ring,
    liouvillian_age_commutator f s hf]
  ring

/-! ## §C — The `b̄`-scaled action weight and the Green-function entropic damping -/

/-- **The thermodynamic action weight** `e^{iS/b̄} = e^{(S_R/b̄)·i − S_I/b̄}` — the complex
action weight (`QFT.Wick.Consistency.complexActionWeight`) with the thermodynamic quantum
`b̄` in place of `ℏ`. -/
noncomputable def thermoActionWeight (S_R S_I b : ℝ) : ℂ :=
  Complex.exp (((S_R / b : ℝ) : ℂ) * Complex.I - ((S_I / b : ℝ) : ℂ))

/-- **The thermodynamic action weight's modulus is the entropic damping** `‖e^{iS/b̄}‖ =
e^{−S_I/b̄}` — mirroring `norm_complexActionWeight`, with the imaginary action `S_I` damped on
the entropy scale `b̄`. (The §C claim, proved.) -/
theorem norm_thermoActionWeight (S_R S_I b : ℝ) :
    ‖thermoActionWeight S_R S_I b‖ = Real.exp (-(S_I / b)) := by
  rw [thermoActionWeight, Complex.norm_exp]
  congr 1
  simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]

/-- **The entropy is `−b̄·log‖w‖ = S_I`**: the dimensionless entropy `S_I/b̄` is `−log‖w‖`,
the thermodynamic-`b̄` analogue of the entropic time `S_I/ℏ = −log‖w‖`. -/
theorem log_norm_thermoActionWeight (S_R S_I b : ℝ) :
    Real.log ‖thermoActionWeight S_R S_I b‖ = -(S_I / b) := by
  rw [norm_thermoActionWeight, Real.log_exp]

/-- **The modified Green function's decay is the entropic damping**: the dissipative Green
kernel modulus equals the thermodynamic action weight modulus,
`‖e^{−iλt/ℏ}‖ = ‖e^{iS/ℏ}‖`, with imaginary action `S_I = −Im λ·t = Γt` (the accumulated
entropy, `Γ = −Im λ = H_I`-eigenvalue). This makes the `NonHermitianComplexAction.GreenFunction` decay and
the `complexActionWeight`/entropic damping one and the same. -/
theorem norm_greenKernel_eq_thermoActionWeight (lam : ℂ) (ℏ t S_R : ℝ) :
    ‖greenKernel lam ℏ t‖ = ‖thermoActionWeight S_R (-lam.im * t) ℏ‖ := by
  rw [norm_greenKernel, norm_thermoActionWeight]
  congr 1
  ring

/-! ## §D — No action with no information: `H_I = 0 ⟺ unitary ⟺ S_I = 0` (third law / computability)

At absolute zero `T → 0` the third law (Nernst) sends the entropy to its minimum and the
dynamics becomes reversible; in the computability reading of thermodynamics this is the
regime where **no information is erased**, so by Landauer there is **no entropic cost**
(`RelationalTime.EntropicLandauer.landauer_export`: erasing one bit exports `≥ ln 2`; no
erasure exports `0`). In the complex-action/`Q`-formalism this is `H_I = 0`: the dissipative
(anti-`Q`-Hermitian) generator vanishes, all eigenvalues are real (`Im λ = 0`), the
evolution is unitary, the imaginary action / entropy `S_I` vanishes, and the path weight is
a pure phase. The theorems below make each `⟺` precise — "no action with no information". -/

/-- **No information ⟺ no imaginary action**: the thermodynamic path weight is unimodular
(`‖e^{iS/b̄}‖ = 1`, a pure phase — unitary, no entropic cost) iff the imaginary action
`S_I = 0`. -/
theorem thermoActionWeight_norm_one_iff {b : ℝ} (hb : b ≠ 0) (S_R S_I : ℝ) :
    ‖thermoActionWeight S_R S_I b‖ = 1 ↔ S_I = 0 := by
  rw [norm_thermoActionWeight, Real.exp_eq_one_iff, neg_eq_zero, div_eq_zero_iff]
  simp [hb]

/-- **Unitary evolution ⟺ no dissipative generator**: the Green function is unimodular
(`‖e^{−iλt/ℏ}‖ = 1`, no decay) iff `Im λ = 0`, i.e. the `H_I`-eigenvalue `−Im λ = 0` — the
dissipative/imaginary part of the Hamiltonian vanishes. -/
theorem greenKernel_norm_one_iff {ℏ t : ℝ} (hℏ : ℏ ≠ 0) (ht : t ≠ 0) (lam : ℂ) :
    ‖greenKernel lam ℏ t‖ = 1 ↔ lam.im = 0 := by
  rw [norm_greenKernel, Real.exp_eq_one_iff, div_eq_zero_iff, mul_eq_zero]
  simp [ht, hℏ]

/-- **No action with no information — the main result**: vanishing of the dissipative generator
`H_I` (`Im λ = 0`) is equivalent to a unitary propagator (`‖greenKernel‖ = 1`), zero entropy
production (`S_I = −Im λ·t = 0`), and a pure-phase path weight (`‖thermoActionWeight‖ = 1`).
The reversible / `T → 0` / Landauer-free regime: no entropic action, no information. -/
theorem no_action_no_information {ℏ t : ℝ} (hℏ : ℏ ≠ 0) (ht : t ≠ 0) (lam : ℂ) (S_R : ℝ) :
    lam.im = 0 ↔
      (‖greenKernel lam ℏ t‖ = 1 ∧ ‖thermoActionWeight S_R (-lam.im * t) ℏ‖ = 1) := by
  constructor
  · intro h
    refine ⟨(greenKernel_norm_one_iff hℏ ht lam).mpr h, ?_⟩
    rw [thermoActionWeight_norm_one_iff hℏ]
    rw [h]; ring
  · intro h
    exact (greenKernel_norm_one_iff hℏ ht lam).mp h.1

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.CliffordAlgebra
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit

/-!
# The genuine four-spinor Dirac Hamiltonian `H = α·p + βm` (Acharya–Sudarshan 1960)

`Dirac.SpinorReductionSchrodinger` performed the lower-component elimination in a two-component
(1+1-dimensional) toy model. This file builds the **genuine four-spinor** Dirac Hamiltonian in 3+1
dimensions — Eq. (12) of R. Acharya, E. C. G. Sudarshan, *"Front" Description in Relativistic Quantum
Mechanics*, J. Math. Phys. **1** (1960) 532 —

 `i ∂ψ/∂t = (α·p + βm) ψ`,

with the **3-D Dirac matrices** `α = (α₁,α₂,α₃)`, `β`. Rather than redefine them, it reuses physlib's
canonical Dirac-representation gamma matrices `spaceTime.γ0,…,γ3` (`Relativity/CliffordAlgebra`) via

 `β = γ⁰`, `αⁱ = γ⁰ γⁱ`.

## What is proved

* **The 3-D Dirac (Clifford) algebra** (`diracBeta_sq`, `diracAlphaᵢ_sq`, `diracAlphaᵢ_beta_anticomm`,
 `diracAlpha_anticomm₁₂` …): `β² = 1`, `αⁱ² = 1`, `{αⁱ, β} = 0`, `{αⁱ, αʲ} = 0` (`i ≠ j`) — the
 anticommutation relations, in the canonical Dirac representation.
* **The four-spinor dispersion** (`diracHamiltonian4_sq`): `H² = (p₁²+p₂²+p₃²+m²)·1`, the genuine 3-D
 Einstein relation `E² = p² + m²` (natural units `c = 1`) — the four-spinor generalization of the
 two-component `diracHamiltonian_sq`.
* **The velocity operator** `α` (Acharya's remark after Eq. (12)): `αⁱ² = 1` so the velocity
 eigenvalues are `±1` (the speed of light — Zitterbewegung), and `α₁α₂ ≠ α₂α₁`
 (`diracAlpha_not_commute`), so the velocity components are not simultaneously diagonalizable.
* **The Foldy–Wouthuysen target is isospectral** (`fw_beta_energy_sq`, `fourSpinor_dispersion_eq_fw`):
 with `E = √(p²+m²)`, the block-diagonal `E·β` (Eq. (14), `i∂φ/∂t = β(p²+m²)^½ φ`) squares to `E²·1`,
 the same as `H²`. `β = diag(1,1,−1,−1)` decouples positive (upper two) from negative (lower two)
 energy; the positive-energy block `+√(p²+m²)` is Eq. (15)'s two-component Schrödinger Hamiltonian,
 whose non-relativistic limit `→ m + p²/2m` is `ComplexEinstein.EinsteinSchrodingerNonrelLimit`.

## Scope

The Clifford algebra, the dispersion `H² = (p²+m²)·1`, and the velocity operator are proved exactly.
The Foldy–Wouthuysen *transformation* itself (Eq. (13), `φ = exp{(βα·p/2|p|)·tan⁻¹(|p|/m)}ψ`) is a
matrix exponential and is **not** formalized; this file proves the *isospectrality* `H² = (E·β)² =
E²·1` the transformation realizes, not the conjugating unitary. The position/front operators of
Acharya–Sudarshan Secs. 2, 4 are out of scope.

## References

* R. Acharya, E. C. G. Sudarshan, J. Math. Phys. **1** (1960) 532. doi:10.1063/1.1703689.
 L. L. Foldy, S. A. Wouthuysen, Phys. Rev. **78** (1950) 29. This development:
 `Relativity/CliffordAlgebra` (gamma matrices), `Dirac.SpinorReductionSchrodinger`,
 `ComplexEinstein.EinsteinSchrodingerNonrelLimit`.

No new axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section

noncomputable section

open Matrix spaceTime Complex

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-! ## §A — the 3-D Dirac matrices `β = γ⁰`, `αⁱ = γ⁰γⁱ` (concrete forms) -/

/-- **The Dirac `β` matrix** `β = γ⁰`. -/
def diracBeta : Matrix (Fin 4) (Fin 4) ℂ := γ0

/-- **The Dirac `α₁` matrix** `α₁ = γ⁰γ¹`. -/
def diracAlpha1 : Matrix (Fin 4) (Fin 4) ℂ := γ0 * γ1

/-- **The Dirac `α₂` matrix** `α₂ = γ⁰γ²`. -/
def diracAlpha2 : Matrix (Fin 4) (Fin 4) ℂ := γ0 * γ2

/-- **The Dirac `α₃` matrix** `α₃ = γ⁰γ³`. -/
def diracAlpha3 : Matrix (Fin 4) (Fin 4) ℂ := γ0 * γ3

/-- `α₁ = [[0,σ₁],[σ₁,0]]` (the off-diagonal Pauli-`σ₁` block). -/
theorem diracAlpha1_eq : diracAlpha1 = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  simp [diracAlpha1, γ0, γ1]

/-- `α₂ = [[0,σ₂],[σ₂,0]]`. -/
theorem diracAlpha2_eq :
    diracAlpha2 = !![0, 0, 0, -I; 0, 0, I, 0; 0, -I, 0, 0; I, 0, 0, 0] := by
  simp [diracAlpha2, γ0, γ2]

/-- `α₃ = [[0,σ₃],[σ₃,0]]`. -/
theorem diracAlpha3_eq :
    diracAlpha3 = !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0] := by
  simp [diracAlpha3, γ0, γ3]

/-! ## §B — the Clifford algebra `β² = 1`, `αⁱ² = 1`, `{αⁱ,β} = 0`, `{αⁱ,αʲ} = 0` -/

/-- **`β² = 1`**. -/
theorem diracBeta_sq : diracBeta * diracBeta = 1 := γ0_mul_γ0

/-- **`α₁² = 1`** (velocity eigenvalues `±1`). -/
theorem diracAlpha1_sq : diracAlpha1 * diracAlpha1 = 1 := by
  rw [diracAlpha1_eq]; simp [Matrix.one_fin_four]

/-- **`α₂² = 1`**. -/
theorem diracAlpha2_sq : diracAlpha2 * diracAlpha2 = 1 := by
  rw [diracAlpha2_eq]; simp [Matrix.one_fin_four, Complex.I_mul_I]

/-- **`α₃² = 1`**. -/
theorem diracAlpha3_sq : diracAlpha3 * diracAlpha3 = 1 := by
  rw [diracAlpha3_eq]; simp [Matrix.one_fin_four]

/-- **`{α₁, β} = 0`**. -/
theorem diracAlpha1_beta_anticomm : diracAlpha1 * diracBeta + diracBeta * diracAlpha1 = 0 := by
  rw [diracAlpha1_eq, diracBeta, γ0]; ext a b; fin_cases a <;> fin_cases b <;> simp

/-- **`{α₂, β} = 0`**. -/
theorem diracAlpha2_beta_anticomm : diracAlpha2 * diracBeta + diracBeta * diracAlpha2 = 0 := by
  rw [diracAlpha2_eq, diracBeta, γ0]; ext a b; fin_cases a <;> fin_cases b <;> simp

/-- **`{α₃, β} = 0`**. -/
theorem diracAlpha3_beta_anticomm : diracAlpha3 * diracBeta + diracBeta * diracAlpha3 = 0 := by
  rw [diracAlpha3_eq, diracBeta, γ0]; ext a b; fin_cases a <;> fin_cases b <;> simp

/-- **`{α₁, α₂} = 0`**. -/
theorem diracAlpha_anticomm₁₂ : diracAlpha1 * diracAlpha2 + diracAlpha2 * diracAlpha1 = 0 := by
  rw [diracAlpha1_eq, diracAlpha2_eq]; ext a b; fin_cases a <;> fin_cases b <;> simp

/-- **`{α₁, α₃} = 0`**. -/
theorem diracAlpha_anticomm₁₃ : diracAlpha1 * diracAlpha3 + diracAlpha3 * diracAlpha1 = 0 := by
  rw [diracAlpha1_eq, diracAlpha3_eq]; ext a b; fin_cases a <;> fin_cases b <;> simp

/-- **`{α₂, α₃} = 0`**. -/
theorem diracAlpha_anticomm₂₃ : diracAlpha2 * diracAlpha3 + diracAlpha3 * diracAlpha2 = 0 := by
  rw [diracAlpha2_eq, diracAlpha3_eq]; ext a b; fin_cases a <;> fin_cases b <;> simp

/-! ## §C — the four-spinor Dirac Hamiltonian `H = α·p + βm` and its square -/

/-- **The four-spinor Dirac Hamiltonian** `H = α·p + βm = p₁α₁ + p₂α₂ + p₃α₃ + mβ` (Acharya–Sudarshan
Eq. (12)). -/
def diracHamiltonian4 (p1 p2 p3 m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (p1 : ℂ) • diracAlpha1 + (p2 : ℂ) • diracAlpha2 + (p3 : ℂ) • diracAlpha3 + (m : ℂ) • diracBeta

/-- **`H` in the block form** `[[m, σ·p],[σ·p, −m]]`. -/
theorem diracHamiltonian4_concrete (p1 p2 p3 m : ℝ) :
    diracHamiltonian4 p1 p2 p3 m
      = !![(m : ℂ), 0, p3, p1 - p2 * I; 0, m, p1 + p2 * I, -p3;
           p3, p1 - p2 * I, -m, 0; p1 + p2 * I, -p3, 0, -m] := by
  rw [diracHamiltonian4, diracAlpha1_eq, diracAlpha2_eq, diracAlpha3_eq, diracBeta, γ0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> ring

/-- **The four-spinor Dirac dispersion** `H² = (p₁² + p₂² + p₃² + m²)·1` — the genuine 3-D Einstein
relation `E² = p² + m²` (natural units `c = 1`), the four-spinor generalization of the two-component
`diracHamiltonian_sq`. The off-diagonal cross terms cancel by the Clifford anticommutators; the
squares give `αⁱ² = β² = 1`. -/
theorem diracHamiltonian4_sq (p1 p2 p3 m : ℝ) :
    diracHamiltonian4 p1 p2 p3 m * diracHamiltonian4 p1 p2 p3 m
      = ((p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [diracHamiltonian4_concrete]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    push_cast <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-! ## §D — the velocity operator `α` (Acharya's remark after Eq. (12)) -/

/-- **The velocity components do not commute**: `α₁ α₂ ≠ α₂ α₁`, so the components of the Dirac
velocity are not simultaneously diagonalizable (Acharya–Sudarshan, after Eq. (12)). -/
theorem diracAlpha_not_commute : diracAlpha1 * diracAlpha2 ≠ diracAlpha2 * diracAlpha1 := by
  intro hcomm
  -- with `α₁α₂ = α₂α₁`, the anticommutator gives `2 • (α₁α₂) = 0`, so `α₁α₂ = 0`
  have hanti := diracAlpha_anticomm₁₂
  rw [← hcomm, ← two_smul ℂ] at hanti
  have h2 : diracAlpha1 * diracAlpha2 = 0 :=
    (smul_eq_zero.mp hanti).resolve_left (by norm_num)
  -- but `(α₁α₂)(α₂α₁) = α₁(α₂²)α₁ = α₁² = 1 ≠ 0`
  have hinv : (diracAlpha1 * diracAlpha2) * (diracAlpha2 * diracAlpha1) = 1 := by
    calc (diracAlpha1 * diracAlpha2) * (diracAlpha2 * diracAlpha1)
        = diracAlpha1 * ((diracAlpha2 * diracAlpha2) * diracAlpha1) := by
          rw [mul_assoc, ← mul_assoc diracAlpha2]
      _ = 1 := by rw [diracAlpha2_sq, one_mul, diracAlpha1_sq]
  rw [h2, zero_mul] at hinv
  exact zero_ne_one hinv

/-! ## §E — the Foldy–Wouthuysen target is isospectral with `H` -/

/-- **The Foldy–Wouthuysen Hamiltonian is isospectral with `H`.** With `E² = p² + m²`, the
block-diagonal `E·β` of Eq. (14) (`i∂φ/∂t = β(p²+m²)^½ φ`) squares to `E²·1` — the same as `H²`
(`diracHamiltonian4_sq`). `β = diag(1,1,−1,−1)` decouples positive- (upper two) from negative-energy
(lower two) components, the positive block being Eq. (15)'s two-component Schrödinger Hamiltonian
`+√(p²+m²)`. -/
theorem fw_beta_energy_sq (E : ℝ) :
    ((E : ℂ) • diracBeta) * ((E : ℂ) • diracBeta)
      = ((E ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [smul_mul_smul_comm, diracBeta_sq]
  congr 1
  push_cast
  ring

/-- **The four-spinor dispersion equals the Foldy–Wouthuysen square.** Both `H` and `E·β` (with
`E² = p² + m²`) square to `E²·1`: the genuine four-spinor Dirac equation and its Foldy–Wouthuysen
two-component reduction share the spectrum `±√(p²+m²)` — the full Einstein dispersion whose
non-relativistic limit is the Schrödinger kinetic energy (`ComplexEinstein.EinsteinSchrodingerNonrelLimit`). -/
theorem fourSpinor_dispersion_eq_fw (p1 p2 p3 m E : ℝ)
    (hE : E ^ 2 = p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2) :
    diracHamiltonian4 p1 p2 p3 m * diracHamiltonian4 p1 p2 p3 m
      = ((E : ℂ) • diracBeta) * ((E : ℂ) • diracBeta) := by
  rw [diracHamiltonian4_sq, fw_beta_energy_sq, hE]

/-! ## §F — Zitterbewegung: the trembling of the velocity operator

Schrödinger's *Zitterbewegung*: the Dirac velocity operator `v = cα` does **not** commute with `H`, so in
the Heisenberg picture the position trembles. Setting `c = ℏ = 1`, the velocity `α₁` has eigenvalues `±1`
only (`velocity_operator_luminal`, `α₁²=1`) — instantaneous luminal motion — while its *mean* is the
conserved drift `p₁/H`. The difference oscillates: defining the **Zitterbewegung operator**
`η₁ = Hα₁ − p₁` (the un-inverted `H·(α₁ − p₁/H)`), the velocity's Heisenberg derivative is
`[H,α₁] = 2η₁` (`velocity_heisenberg_derivative`) and `η₁` itself obeys `[H,η₁] = 2H·η₁`
(`zitter_oscillation`), so `η₁(t) = e^{2iHt} η₁(0)` — oscillation at angular frequency `2E/ℏ`. At rest
(`p=0`) `H = mβ` (`restFrame_hamiltonian`) with `H² = m²·1` (`restFrame_zitter_gap`), giving the
Zitterbewegung frequency `ω_Z = 2m = 2mc²/ℏ` (the Compton scale; cf. `ComptonClock.FrequencyTrinity`). -/

/-- **[The velocity operator is luminal]** `α₁² = 1`: the Dirac velocity `v = cα₁` has eigenvalues `±c`
only — the instantaneous velocity is always luminal, the kinematic root of the Zitterbewegung. -/
theorem velocity_operator_luminal : diracAlpha1 * diracAlpha1 = 1 := diracAlpha1_sq

/-- **[Velocity–Hamiltonian anticommutator]** `{α₁, H} = α₁H + Hα₁ = 2p₁·1` — from `{α₁,αⁱ}=2δ₁ᵢ` and
`{α₁,β}=0`. The anticommutator (not the commutator) is the `c`-number `2p₁`, the seed of the
Zitterbewegung decomposition of the velocity into drift `+` trembling. -/
theorem diracAlpha1_hamiltonian_anticomm (p1 p2 p3 m : ℝ) :
    diracAlpha1 * diracHamiltonian4 p1 p2 p3 m + diracHamiltonian4 p1 p2 p3 m * diracAlpha1
      = (2 * (p1 : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [diracHamiltonian4_concrete, diracAlpha1_eq]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> push_cast <;> ring

/-- **The Zitterbewegung velocity operator** `η₁ = Hα₁ − p₁·1` — the Dirac velocity `α₁` minus its
conserved mean drift `p₁/H`, multiplied through by `H` (so no operator inverse is needed). -/
def zitterVelocity1 (p1 p2 p3 m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  diracHamiltonian4 p1 p2 p3 m * diracAlpha1 - (p1 : ℂ) • 1

/-- **[Heisenberg derivative of the velocity]** `[H, α₁] = Hα₁ − α₁H = 2 η₁`, so `α̇₁ = i[H,α₁] = 2i η₁`:
the velocity is **not** conserved (the commutator is `2η₁ ≠ 0`) — the operator statement of the trembling.
Follows from the anticommutator `α₁H = 2p₁·1 − Hα₁`. -/
theorem velocity_heisenberg_derivative (p1 p2 p3 m : ℝ) :
    diracHamiltonian4 p1 p2 p3 m * diracAlpha1 - diracAlpha1 * diracHamiltonian4 p1 p2 p3 m
      = (2 : ℂ) • zitterVelocity1 p1 p2 p3 m := by
  have h : diracAlpha1 * diracHamiltonian4 p1 p2 p3 m
      = (2 * (p1 : ℂ)) • 1 - diracHamiltonian4 p1 p2 p3 m * diracAlpha1 :=
    eq_sub_of_add_eq (diracAlpha1_hamiltonian_anticomm p1 p2 p3 m)
  unfold zitterVelocity1
  rw [smul_sub, smul_smul, h, two_smul]
  abel

/-- **[Zitterbewegung oscillation]** `[H, η₁] = Hη₁ − η₁H = 2H·η₁`, so `η̇₁ = i[H,η₁] = 2iH·η₁` and
`η₁(t) = e^{2iHt} η₁(0)` — the velocity's trembling part rotates at angular frequency `2E/ℏ` (the spectral
gap between positive- and negative-energy sheets). This is the algebraic core of Schrödinger's
Zitterbewegung. -/
theorem zitter_oscillation (p1 p2 p3 m : ℝ) :
    diracHamiltonian4 p1 p2 p3 m * zitterVelocity1 p1 p2 p3 m
        - zitterVelocity1 p1 p2 p3 m * diracHamiltonian4 p1 p2 p3 m
      = (2 : ℂ) • (diracHamiltonian4 p1 p2 p3 m * zitterVelocity1 p1 p2 p3 m) := by
  -- the `p₁·1` part is central, so `[H,η₁] = [H, Hα₁] = H·[H,α₁] = H·(2η₁) = 2H·η₁`
  have e1 : diracHamiltonian4 p1 p2 p3 m * zitterVelocity1 p1 p2 p3 m
        - zitterVelocity1 p1 p2 p3 m * diracHamiltonian4 p1 p2 p3 m
      = diracHamiltonian4 p1 p2 p3 m * (diracHamiltonian4 p1 p2 p3 m * diracAlpha1)
        - diracHamiltonian4 p1 p2 p3 m * diracAlpha1 * diracHamiltonian4 p1 p2 p3 m := by
    unfold zitterVelocity1
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    abel
  rw [e1, mul_assoc, ← mul_sub, velocity_heisenberg_derivative, mul_smul_comm]

/-- **[The rest-frame Hamiltonian]** `H(p=0) = mβ` — at rest the Dirac Hamiltonian is pure mass term. -/
theorem restFrame_hamiltonian (m : ℝ) :
    diracHamiltonian4 0 0 0 m = (m : ℂ) • diracBeta := by
  simp [diracHamiltonian4]

/-- **[The rest-frame Zitterbewegung gap]** `H(p=0)² = m²·1`: the rest spectrum is `±m`, so the
Zitterbewegung oscillation operator `2H = 2mβ` records angular frequency `ω_Z = 2m = 2mc²/ℏ` — the
Compton-scale trembling frequency. -/
theorem restFrame_zitter_gap (m : ℝ) :
    diracHamiltonian4 0 0 0 m * diracHamiltonian4 0 0 0 m
      = ((m ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [diracHamiltonian4_sq]; congr 1; push_cast; ring

end Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

end

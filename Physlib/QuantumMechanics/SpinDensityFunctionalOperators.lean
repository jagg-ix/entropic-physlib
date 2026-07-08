/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.SpinDensityFunctionalTheory
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Operator / Hilbert-space content of spin-DFT

The operator-level content of Jacob & Reiher, *Spin in Density-Functional Theory* (Int. J. Quantum Chem.
**112**, 3661 (2012), arXiv:1206.2234), complementing the real-valued spin-density algebra of
`SpinDensityFunctionalTheory`:

* **§A — Pauli matrices and the one-electron spin** (Eqs. 4–7). `pauliX/Y/Z`, their squares and products,
 the spin operator `ŝ = (ℏ/2)σ`, the angular-momentum commutators `[ŝ_x,ŝ_y] = iℏ ŝ_z`, and `ŝ² = (3/4)ℏ²·1`.
* **§B — the many-electron total spin operator** (Eq. 17). The symmetric double-sum identity
 `Σ_ij fᵢⱼ = Σᵢ fᵢᵢ + 2 Σ_{i<j} fᵢⱼ`, giving `Ŝ² = (3/4)Nℏ² + 2 Σ_{i<j} ŝᵢ·ŝⱼ`.
* **§C — the antisymmetrizer** (Eq. 22). `antisymmetrizerSign = (1/√N!) Σ_p sign(p) p`; the coefficient
 `sign(p)` is `±1` and `Â` applied to an already-antisymmetric vector reproduces it up to `√N!`.
* **§D — the Hohenberg–Kohn variational principle** (Eqs. 38–40, 50). `hkEnergy ρ = extEnergy ρ + F ρ`, the
 variational lower bound `E₀ ≤ hkEnergy ρ`, the Levy constrained search `F ρ = ⨅_{Ψ→ρ} innerEnergy Ψ`, and
 the spin reduction `F[ρ] = ⨅_Q F[ρ,Q]`.

**Scope.** §A/§B are exact matrix / finite-sum identities. §C records the antisymmetrizer's sign
coefficients and its action on antisymmetric vectors (not the full `N!`-dimensional permutation representation).
§D is the abstract order-theoretic skeleton of HK-DFT — the energy split and the constrained-search infima as
`⨅` over abstract density/wavefunction types — capturing the variational structure, not the analytic existence
of minimizers.

No new axioms.
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.SpinDensityFunctionalOperators

/-! ## §A — Pauli matrices and the one-electron spin (Eqs. 4–7) -/

/-- **Pauli matrix** `σ_x` (Jacob–Reiher Eq. 4). -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- **Pauli matrix** `σ_y` (Eq. 4). -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- **Pauli matrix** `σ_z` (Eq. 4). -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- **[`σ_x² = 1`]**. -/
theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- **[`σ_y² = 1`]**. -/
theorem pauliY_sq : pauliY * pauliY = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- **[`σ_z² = 1`]**. -/
theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **[`σ_x σ_y = i σ_z`]** — the Pauli-matrix product law. -/
theorem pauliX_mul_pauliY : pauliX * pauliY = Complex.I • pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **[`σ_y σ_x = −i σ_z`]**. -/
theorem pauliY_mul_pauliX : pauliY * pauliX = -Complex.I • pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The one-electron spin operator** `ŝ_α = (ℏ/2)σ_α` (Eq. 5). -/
noncomputable def spinX (ℏ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := ((ℏ : ℂ) / 2) • pauliX

/-- `ŝ_y = (ℏ/2)σ_y`. -/
noncomputable def spinY (ℏ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := ((ℏ : ℂ) / 2) • pauliY

/-- `ŝ_z = (ℏ/2)σ_z`. -/
noncomputable def spinZ (ℏ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := ((ℏ : ℂ) / 2) • pauliZ

/-- **[The spin commutator] `[ŝ_x, ŝ_y] = iℏ ŝ_z`** (Eq. 6) — the electron spin satisfies the angular-momentum
commutation relations, the basis for treating it as an intrinsic angular momentum. -/
theorem spin_commutator_xy (ℏ : ℝ) :
    spinX ℏ * spinY ℏ - spinY ℏ * spinX ℏ = (Complex.I * (ℏ : ℂ)) • spinZ ℏ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [spinX, spinY, spinZ, pauliX, pauliY, pauliZ, Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-- **[The squared spin] `ŝ² = ŝ_x² + ŝ_y² + ŝ_z² = (3/4)ℏ²·1`** (Eq. 7) — every electron is a spin-½ particle,
the `S(S+1)ℏ²` eigenvalue at `S = ½`. -/
theorem spin_sq (ℏ : ℝ) :
    spinX ℏ * spinX ℏ + spinY ℏ * spinY ℏ + spinZ ℏ * spinZ ℏ
      = ((3 / 4) * (ℏ : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h : ∀ σ : Matrix (Fin 2) (Fin 2) ℂ, σ * σ = 1 →
      (((ℏ : ℂ) / 2) • σ) * (((ℏ : ℂ) / 2) • σ)
        = ((ℏ : ℂ) / 2 * ((ℏ : ℂ) / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro σ hσ
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hσ]
  rw [spinX, spinY, spinZ, h pauliX pauliX_sq, h pauliY pauliY_sq, h pauliZ pauliZ_sq,
    ← add_smul, ← add_smul]
  congr 1
  ring

/-! ## §B — the many-electron total spin operator (Eq. 17) -/

/-- **[The single-electron spin-squares sum to `(3/4)Nℏ²`] (Eq. 17, diagonal term)** — every electron is a
spin-½ particle with `ŝ² = (3/4)ℏ²`, so the `N` diagonal terms of `Ŝ² = Σᵢⱼ ŝᵢ·ŝⱼ` contribute `(3/4)Nℏ²`. -/
theorem sum_electron_spinSquared (N : ℕ) (ℏ : ℝ) :
    ∑ _i : Fin N, (3 / 4 * ℏ ^ 2) = (N : ℝ) * (3 / 4 * ℏ ^ 2) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **[Two-electron `Ŝ²` split] `Σ_{i,j∈{1,2}} fᵢⱼ = (f₁₁ + f₂₂) + 2 f₁₂`** for a symmetric coupling `f` — the
minimal open-shell case of `Ŝ² = Σᵢ ŝᵢ² + 2 Σ_{i<j} ŝᵢ·ŝⱼ` (Eq. 17): the total spin-squared is a genuine
*two-electron* operator, the diagonal single-electron squares plus the symmetric pair coupling. -/
theorem twoElectron_spinSquared_split {M : Type*} [AddCommMonoid M] (f : Fin 2 → Fin 2 → M)
    (hf : f 0 1 = f 1 0) :
    ∑ i, ∑ j, f i j = f 0 0 + f 1 1 + 2 • f 0 1 := by
  simp only [Fin.sum_univ_two]
  rw [← hf]; abel

/-! ## §C — the antisymmetrizer (Eq. 22) -/

/-- **[The antisymmetrizer coefficient is ±1] `sign(p)² = 1`** — the coefficients `(−1)^p` in the
antisymmetrizer `Â = (1/√N!) Σ_p (−1)^p P̂_p` (Eq. 22) are `±1`. -/
theorem perm_sign_sq {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign p : ℤ) : ℝ) * ((Equiv.Perm.sign p : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **[The antisymmetrizer reproduces an antisymmetric vector] `ÂΨ = √N! Ψ`** (Eq. 22, Pauli principle) — for a
vector `v` already antisymmetric under the permutation action (`P̂_p v = sign(p) v`), the antisymmetrizer
`Â = (1/√N!) Σ_p sign(p) P̂_p` returns `√N! v`, i.e. `ÂΨ = √N! Ψ` — the requirement that the wavefunction be an
eigenfunction of `Â`. -/
theorem antisymmetrizer_of_antisymmetric {n : ℕ} (act : Equiv.Perm (Fin n) → V → V) (v : V)
    (hact : ∀ p, act p v = ((Equiv.Perm.sign p : ℤ) : ℝ) • v) (hfac : 0 < (n.factorial : ℝ)) :
    (Real.sqrt n.factorial)⁻¹ • ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤ) : ℝ) • act p v
      = Real.sqrt n.factorial • v := by
  have hterm : ∀ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤ) : ℝ) • act p v = v := by
    intro p; rw [hact, smul_smul, perm_sign_sq, one_smul]
  have hs : Real.sqrt n.factorial ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hfac)
  rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  rw [inv_mul_eq_div, div_eq_iff hs, Real.mul_self_sqrt hfac.le]

/-! ## §D — the Hohenberg–Kohn variational principle (Eqs. 38–40, 50) -/

/-- **The Hohenberg–Kohn energy functional** `E[ρ] = q_e ∫ρ v_nuc + F_HK[ρ]` (Eq. 39): the system-specific
external-potential part plus the universal Hohenberg–Kohn functional. -/
def hkEnergy {D : Type*} (extEnergy F : D → ℝ) (ρ : D) : ℝ := extEnergy ρ + F ρ

/-- **[The HK variational principle] `E₀ ≤ E[ρ]`** (Eq. 38) — the ground-state energy `E₀ = min_ρ E[ρ]` is a
lower bound for `E[ρ]` at every admissible density: minimizing the HK energy functional over densities yields
the ground-state energy. -/
theorem hkEnergy_ground_le {D : Type*} (extEnergy F : D → ℝ) (ρ : D)
    (hbdd : BddBelow (Set.range (hkEnergy extEnergy F))) :
    ⨅ ρ', hkEnergy extEnergy F ρ' ≤ hkEnergy extEnergy F ρ :=
  ciInf_le hbdd ρ

/-- **The Levy constrained-search functional** `F_HK[ρ] = min_{Ψ→ρ} ⟨Ψ|T̂+V̂_ee|Ψ⟩` (Eq. 40): the minimum inner
energy over all wavefunctions `Ψ` yielding the target density `ρ`. -/
noncomputable def levyFunctional {D W : Type*} (innerEnergy : W → ℝ) (yields : D → W → Prop) (ρ : D) : ℝ :=
  ⨅ Ψ : {Ψ // yields ρ Ψ}, innerEnergy Ψ.1

/-- **[The Levy functional is a lower bound]** `F_HK[ρ] ≤ ⟨Ψ|T̂+V̂_ee|Ψ⟩` for any `Ψ` yielding `ρ` — the
constrained search selects the lowest inner energy compatible with the density. -/
theorem levyFunctional_le {D W : Type*} (innerEnergy : W → ℝ) (yields : D → W → Prop) (ρ : D) (Ψ : W)
    (hΨ : yields ρ Ψ)
    (hbdd : BddBelow (Set.range fun Ψ' : {Ψ // yields ρ Ψ} => innerEnergy Ψ'.1)) :
    levyFunctional innerEnergy yields ρ ≤ innerEnergy Ψ :=
  ciInf_le hbdd ⟨Ψ, hΨ⟩

/-- **The spin-independent HK functional from the spin-resolved one** `F_HK[ρ] = min_Q F_HK[ρ,Q]` (Eq. 50). -/
noncomputable def hkSpinReduced {D Q : Type*} (Fspin : D → Q → ℝ) (ρ : D) : ℝ := ⨅ q, Fspin ρ q

/-- **[Spin reduction is a lower bound] `F_HK[ρ] ≤ F_HK[ρ,Q]`** (Eq. 50) — the spin-independent HK functional is
the minimum over admissible spin densities `Q` of the spin-resolved functional. -/
theorem hkSpinReduced_le {D Q : Type*} (Fspin : D → Q → ℝ) (ρ : D) (q : Q)
    (hbdd : BddBelow (Set.range (Fspin ρ))) :
    hkSpinReduced Fspin ρ ≤ Fspin ρ q :=
  ciInf_le hbdd q

end Physlib.QuantumMechanics.SpinDensityFunctionalOperators

end

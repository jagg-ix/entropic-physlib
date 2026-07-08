/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Symplectically adjoint maps and the pure-state complex structure (Verch 1996)

Formalizes the **symplectic-geometry kernel** of *R. Verch, "Continuity of symplectically adjoint maps and the
algebraic structure of Hadamard vacuum representations for quantum fields on curved spacetime", Rev. Math.
Phys. (arXiv:funct-an/9609004)*. There a classical linear field is a symplectic space `(S, σ)` whose temporal
evolution is by **symplectomorphisms** (`σ(Tφ,Tψ)=σ(φ,ψ)`), and a quasifree state's polarizator `R_μ`
(`σ(x,y)=2μ(x,R_μy)`, `R_μ*=−R_μ`) is a **complex structure** `R_μ²=−1` exactly when the state is *pure*
(Eq. 2.4). The heavy functional-analytic content (the `μ_s`-interpolation, GNS, von Neumann type analysis)
needs C*-algebra infrastructure; the symplectic-linear kernel is formalized here, and it connects directly to
the TFD Bogoliubov work:

* a **symplectomorphism** of the `2×2` symplectic space is exactly a **det-1 Bogoliubov** (`Sp(2)=SL(2)`), so
  the boson `thermoBogoliubov` and fermion `fermiBogoliubov` (both `det=1`) *are* symplectomorphisms;
* a symplectomorphism `T` and its inverse `T⁻¹` are **symplectically adjoint** (`Tᵀσ = σT⁻¹`) — Verch's
  `(T,T⁻¹)` example, realized by `U_B(θ)` and `U_B(−θ)`;
* the **pure-state complex structure** `R²=−1` is the symplectic form `J` itself — and `J = −`(the Celeghini
  fermion su(2) generator), tying Verch's purity condition to the fermion Bogoliubov generator.

* **§A — the symplectic form** (`sympForm`, `sympForm_sq`, `sympForm_antisymm`). `J=[[0,1],[-1,0]]`, `J²=−1`,
  `Jᵀ=−J`.
* **§B — symplectomorphisms = `SL(2)`** (`Symplectomorphism`, `symplectic_det_identity`,
  `det_one_symplectomorphism`). `MᵀJM = (det M)·J`, so `MᵀJM=J ⟺ det M = 1`.
* **§C — Bogoliubov symplectomorphisms and adjoint pairs** (`thermoBogoliubov_symplectomorphism`,
  `fermiBogoliubov_symplectomorphism`, `symplectic_adjoint_pair`, `thermoBogoliubov_adjoint_pair`).
* **§D — the pure-state complex structure** (`sympForm_eq_neg_fermiGen`). Eq. 2.4 `R²=−1`: the symplectic form
  is minus the fermion generator, both squaring to `−1`.

## References

* R. Verch, arXiv:funct-an/9609004 (the symplectic space `(S,σ)`, symplectically adjoint maps, the polarizator
  `R_μ`, pure scalar products `pu(S,σ)` with `R_μ²=−1`, Eqs. 2.1–2.4).
* Repo dependencies: `ThermoFieldDynamics.TFDImaginaryPart.thermoBogoliubov`/`ThermoFieldDynamics.TFDBogoliubovHopf.fermiBogoliubov` (the det-1 Bogoliubov
  symplectomorphisms); `ThermoFieldDynamics.TFDBogoliubovHopf.fermiBogoliubovGenerator` (the complex structure `J²=−1`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf

/-! ## §A — the symplectic form (Verch §2) -/

/-- **The `2×2` symplectic form** `J = [[0,1],[-1,0]]` — the canonical anti-symmetric, non-degenerate bilinear
form `σ(x,y) = xᵀJy`. -/
def sympForm : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- **[Pure-state complex structure] `J² = −1`** — the symplectic form squares to `−1`, the polarizator
condition `R_μ² = −1` of a *pure* quasifree state (Verch Eq. 2.4). -/
theorem sympForm_sq : sympForm * sympForm = -1 := by
  rw [sympForm, Matrix.mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **The symplectic form is anti-symmetric** `Jᵀ = −J`. -/
theorem sympForm_antisymm : sympFormᵀ = -sympForm := by
  rw [sympForm]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ## §B — symplectomorphisms = `SL(2)` -/

/-- **A symplectomorphism** `MᵀJM = J` — a linear map preserving the symplectic form `σ(Mφ,Mψ)=σ(φ,ψ)`. -/
def Symplectomorphism (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop := Mᵀ * sympForm * M = sympForm

/-- **[`Sp(2)=SL(2)`] `MᵀJM = (det M)·J`** — for `2×2` matrices the symplectic transform scales `J` by the
determinant. -/
theorem symplectic_det_identity (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Mᵀ * sympForm * M = M.det • sympForm := by
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sympForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring

/-- **`det M = 1 ⟹ M` is a symplectomorphism** — the determinant-one condition is `SL(2)=Sp(2,ℝ)`. -/
theorem det_one_symplectomorphism (M : Matrix (Fin 2) (Fin 2) ℝ) (h : M.det = 1) :
    Symplectomorphism M := by
  rw [Symplectomorphism, symplectic_det_identity, h, one_smul]

/-! ## §C — Bogoliubov symplectomorphisms and symplectically adjoint pairs -/

/-- **The boson Bogoliubov is a symplectomorphism** — `thermoBogoliubov θ` has `det=1`
(`thermoBogoliubov_det`), so the thermal/temporal evolution preserves the symplectic form. -/
theorem thermoBogoliubov_symplectomorphism (θ : ℝ) : Symplectomorphism (thermoBogoliubov θ) :=
  det_one_symplectomorphism _ (thermoBogoliubov_det θ)

/-- **The fermion Bogoliubov is a symplectomorphism** — `fermiBogoliubov θ` has `det=1`. -/
theorem fermiBogoliubov_symplectomorphism (θ : ℝ) : Symplectomorphism (fermiBogoliubov θ) :=
  det_one_symplectomorphism _ (fermiBogoliubov_det θ)

/-- **[Verch's `(T,T⁻¹)` example] A symplectomorphism and its inverse are symplectically adjoint** `Mᵀσ = σM⁻¹`
— `σ(Mφ,ψ) = σ(φ, M⁻¹ψ)`. -/
theorem symplectic_adjoint_pair (M Mi : Matrix (Fin 2) (Fin 2) ℝ)
    (hsymp : Symplectomorphism M) (hinv : M * Mi = 1) :
    Mᵀ * sympForm = sympForm * Mi := by
  rw [Symplectomorphism] at hsymp
  calc Mᵀ * sympForm = Mᵀ * sympForm * (M * Mi) := by rw [hinv, mul_one]
    _ = Mᵀ * sympForm * M * Mi := by rw [← mul_assoc]
    _ = sympForm * Mi := by rw [hsymp]

/-- **The boson Bogoliubov pair `(U_B(θ), U_B(−θ))` is symplectically adjoint** — its inverse is the
reversed boost (`thermoBogoliubov_neg`), realizing Verch's `(T,T⁻¹)`. -/
theorem thermoBogoliubov_adjoint_pair (θ : ℝ) :
    (thermoBogoliubov θ)ᵀ * sympForm = sympForm * thermoBogoliubov (-θ) :=
  symplectic_adjoint_pair _ _ (thermoBogoliubov_symplectomorphism θ) (thermoBogoliubov_neg θ)

/-! ## §D — the pure-state complex structure (Eq. 2.4) -/

/-- **The symplectic form is minus the fermion su(2) generator** `J = −J_F` — Verch's pure-state polarizator
`R²=−1` (the symplectic form `J`, `sympForm_sq`) is exactly minus the Celeghini fermion Bogoliubov generator
`fermiBogoliubovGenerator` (`J_F²=−1`, `fermiBogoliubovGenerator_sq`): the complex structure of a pure
quasifree state is the fermion Bogoliubov generator. -/
theorem sympForm_eq_neg_fermiGen : sympForm = -fermiBogoliubovGenerator := by
  rw [sympForm, fermiBogoliubovGenerator]; ext i j; fin_cases i <;> fin_cases j <;> simp

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard

end

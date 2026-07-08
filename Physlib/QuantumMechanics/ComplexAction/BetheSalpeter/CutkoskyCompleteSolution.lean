/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution

/-!
# Completing the Wick–Cutkosky solution: degeneracy and the unequal-mass boost (Cutkosky 1954)

This completes the algebraic core of `BetheSalpeter.CutkoskyBetheSalpeterSolution` with the remaining formalizable
content of Cutkosky 1954: the full eigenvalue `λ_κ = (n+κ)(n+κ+1)` with its O(4) degeneracy
(Appendices A, B), and the **unequal-mass similarity transformation** (Sec. IV), which is a Lorentz
boost.

## The eigenvalue and its degeneracy (Appendices A, B)

The zero-energy eigenvalues are `λ_κ = (n+κ)(n+κ+1) = N(N+1)`, `N = n+κ`
(`cutkoskyEigenvalueNodes`, from the Gegenbauer value `C_{N-1}¹(1) = ½N(N+1)`, Eq. A-3). They depend
only on `N = n+κ`, *not* on the split into the orbital index `n` and the node number `κ`
(`cutkoskyEigenvalueNodes_degenerate`) — the O(4) degeneracy of the nonrelativistic hydrogen atom.

## The unequal-mass similarity transformation is a Lorentz boost (Sec. IV)

For unequal masses `m_a = 1+Δ`, `m_b = 1−Δ` (asymmetry `Δ = (M−1)/(M+1)`, `massAsymmetry`,
`|Δ| < 1`), Cutkosky's Eq. 33 maps the relative-time variable by the **Möbius transformation**

  `z̃ = (z − Δ)/(1 − Δz)`   (`cutkoskyMobius`),

and the eigenvalue/energy by `λ̃ = λ/(1−Δ²)` (`effectiveCoupling`),
`η̃² = (η²−Δ²)/(1−Δ²)` (`effectiveEnergySq`), reducing the unequal-mass problem to the equal-mass
one (`λ̃` depends only on `η̃²`). The key recognition: this Möbius transformation is the
**relativistic velocity subtraction** — `z̃ = tanh(ζ − δ)` for `z = tanh ζ`, `Δ = tanh δ`
(`cutkoskyMobius_tanh`) — i.e. a **Lorentz boost** by the rapidity `δ` of the mass asymmetry, the
same hyperbolic structure as the bosonic Bogoliubov diagonalization and the velocity-addition law of
this development. The mass asymmetry `Δ` is the boost velocity.

## Main results

* `cutkoskyEigenvalueNodes`, `_eq`, `_degenerate` — `λ_κ = (n+κ)(n+κ+1) = N(N+1)`, O(4) degenerate.
* `massAsymmetry`, `massAsymmetry_lt_one` — `Δ = (M−1)/(M+1)`, `|Δ| < 1`.
* `cutkoskyMobius`, `cutkoskyMobius_eq_velocityAdd`, `cutkoskyMobius_tanh` — the similarity map is the
  Lorentz boost (velocity subtraction).
* `effectiveCoupling`, `effectiveEnergySq`, `_equal_mass` — the boosted coupling/energy.
* `cutkosky_complete_summary` — the bundled statement.

## Not formalized (analytic, out of scope)

The integral equations (Eqs. 15, 30, 33) and the ODEs (Eqs. 17, 31, 37, 39) *solutions*, the
Gegenbauer eigenfunctions, the η→1 / Δ→1 asymptotics (Eqs. B-6, C-1), the Goldstein Dirac limit
(Eq. 38), and Figs. 1–2 are not formalized — the differential/integral-equation analysis remains the
human-audited part.

## References

* R. E. Cutkosky, Phys. Rev. **96** (1954) 1135. doi:10.1103/PhysRev.96.1135.
* This development: `BetheSalpeter.CutkoskyBetheSalpeterSolution`, `Rapidity.PoincarePolarMinkowskiInterval` (the boost /
  velocity addition).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution
open Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval

namespace Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyCompleteSolution

/-! ## §A — the eigenvalue `λ_κ = (n+κ)(n+κ+1)` and its O(4) degeneracy (Appendices A, B) -/

/-- **The zero-energy eigenvalue** `λ_κ = (n+κ)(n+κ+1)` (`N = n+κ`, Cutkosky Appendices A, B). -/
def cutkoskyEigenvalueNodes (n κ : ℕ) : ℝ := cutkoskyEigenvalue (n + κ)

/-- **`λ_κ = (n+κ)(n+κ+1)`** explicitly. -/
theorem cutkoskyEigenvalueNodes_eq (n κ : ℕ) :
    cutkoskyEigenvalueNodes n κ = ((n + κ : ℝ)) * ((n + κ : ℝ) + 1) := by
  unfold cutkoskyEigenvalueNodes cutkoskyEigenvalue
  push_cast
  ring

/-- **The O(4) degeneracy**: the eigenvalue depends only on `N = n+κ`, not on the split into the
orbital index `n` and the node number `κ` (the nonrelativistic-hydrogen degeneracy). -/
theorem cutkoskyEigenvalueNodes_degenerate (n κ n' κ' : ℕ) (h : n + κ = n' + κ') :
    cutkoskyEigenvalueNodes n κ = cutkoskyEigenvalueNodes n' κ' := by
  unfold cutkoskyEigenvalueNodes
  rw [h]

/-! ## §B — the mass asymmetry and the boosted (effective) coupling/energy (Sec. IV) -/

/-- **The mass asymmetry** `Δ = (M−1)/(M+1)` (`M = m_a/m_b`; `m_a = 1+Δ`, `m_b = 1−Δ`). -/
def massAsymmetry (M : ℝ) : ℝ := (M - 1) / (M + 1)

/-- **The mass asymmetry is sub-luminal** `|Δ| < 1` (for `M > 0`): it is a boost velocity. -/
theorem massAsymmetry_lt_one (M : ℝ) (hM : 0 < M) : |massAsymmetry M| < 1 := by
  unfold massAsymmetry
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < M + 1),
    div_lt_one (by linarith : (0 : ℝ) < M + 1), abs_lt]
  constructor <;> linarith

/-- **The boosted (effective) coupling** `λ̃ = λ/(1−Δ²)` (Cutkosky Eq. 34). -/
def effectiveCoupling (lam Δ : ℝ) : ℝ := lam / (1 - Δ ^ 2)

/-- **The boosted (effective) energy** `η̃² = (η²−Δ²)/(1−Δ²)` (Cutkosky Eq. 33). -/
def effectiveEnergySq (η Δ : ℝ) : ℝ := (η ^ 2 - Δ ^ 2) / (1 - Δ ^ 2)

/-- **Equal-mass reduction** `Δ = 0 ⟹ λ̃ = λ`. -/
theorem effectiveCoupling_equal_mass (lam : ℝ) : effectiveCoupling lam 0 = lam := by
  simp [effectiveCoupling]

/-- **Equal-mass reduction** `Δ = 0 ⟹ η̃² = η²`. -/
theorem effectiveEnergySq_equal_mass (η : ℝ) : effectiveEnergySq η 0 = η ^ 2 := by
  simp [effectiveEnergySq]

/-! ## §C — the similarity transformation is a Lorentz boost (velocity subtraction) -/

/-- **The Cutkosky similarity Möbius transformation** `z̃ = (z − Δ)/(1 − Δz)` (Eq. 33). -/
def cutkoskyMobius (z Δ : ℝ) : ℝ := (z - Δ) / (1 - Δ * z)

/-- **The similarity map is the relativistic velocity subtraction** `z̃ = (z + (−Δ))/(1 + z(−Δ))` —
the velocity-addition law with velocity `−Δ`. -/
theorem cutkoskyMobius_eq_velocityAdd (z Δ : ℝ) :
    cutkoskyMobius z Δ = (z + (-Δ)) / (1 + z * (-Δ)) := by
  unfold cutkoskyMobius
  ring

/-- **The similarity transformation is a Lorentz boost** `z̃ = tanh(ζ − δ)` for `z = tanh ζ`,
`Δ = tanh δ`: Cutkosky's unequal-mass map is the boost by the rapidity `δ` of the mass asymmetry —
the same hyperbolic structure as the Bogoliubov diagonalization and the velocity-addition law. -/
theorem cutkoskyMobius_tanh (ζ δ : ℝ) :
    cutkoskyMobius (Real.tanh ζ) (Real.tanh δ) = Real.tanh (ζ - δ) := by
  unfold cutkoskyMobius
  rw [sub_eq_add_neg ζ δ, tanh_add, Real.tanh_neg]
  ring

/-! ## §D — the bundled completion -/

/-- **The completed Wick–Cutkosky algebraic core.**

* the eigenvalue is `λ_κ = (n+κ)(n+κ+1)`, degenerate in the split of `N = n+κ` (O(4) hydrogen);
* the mass asymmetry `Δ = (M−1)/(M+1)` is sub-luminal `|Δ| < 1`;
* the unequal-mass similarity map `z̃ = (z−Δ)/(1−Δz)` is the Lorentz boost `tanh(ζ−δ)`, with the
  equal-mass case `Δ = 0` recovering `λ̃ = λ`. -/
theorem cutkosky_complete_summary (n κ : ℕ) (M : ℝ) (hM : 0 < M) (ζ δ lam : ℝ) :
    cutkoskyEigenvalueNodes n κ = ((n + κ : ℝ)) * ((n + κ : ℝ) + 1)
      ∧ |massAsymmetry M| < 1
      ∧ cutkoskyMobius (Real.tanh ζ) (Real.tanh δ) = Real.tanh (ζ - δ)
      ∧ effectiveCoupling lam 0 = lam :=
  ⟨cutkoskyEigenvalueNodes_eq n κ, massAsymmetry_lt_one M hM,
   cutkoskyMobius_tanh ζ δ, effectiveCoupling_equal_mass lam⟩

end Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyCompleteSolution

end

end

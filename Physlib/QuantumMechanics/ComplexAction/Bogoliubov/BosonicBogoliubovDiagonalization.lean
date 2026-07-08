/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes

/-!
# Bosonic Bogoliubov diagonalization (Nam–Napiórkowski–Solovej) as the Lorentz boost

This file formalizes the **single-mode core** of P. T. Nam, M. Napiórkowski, J. P. Solovej,
*Diagonalization of bosonic quadratic Hamiltonians by Bogoliubov transformations*, J. Funct. Anal.
270 (2016) 4340–4368 — the commutative (`dim ℌ = 2`, Bogoliubov 1947) case — and links it to the
hyperbolic / Minkowski / complex-oscillator formalization of this development.

## The bosonic symplectic structure is Minkowski (Nam–Napiórkowski–Solovej Eq. 9)

The bosonic generalized operators obey the CCR `[A(F₁), A*(F₂)] = ⟨F₁, S F₂⟩` with the **symplectic
matrix**

  `S = diag(1, −1)`   (`symplecticS`),

which the authors call "the bosonic analogue to the identity in the fermionic case". `S` is the
**Minkowski metric**: `⟨(t,x), S (t,x)⟩ = t² − x²` (`symplecticS_quadratic_form`,
`= lorentzianForm`). A Bogoliubov transformation `𝒱` satisfies `𝒱ᵀ S 𝒱 = S` (Eq. 11), i.e. it
**preserves the Minkowski form** — the operator `SO(1,1)`. For the single real mode `𝒱 = [[u,v],[v,u]]`,
this is `u² − v² = 1` (`bosonicBogoliubov_preserves_S_iff`, Eq. 13 `U*U − V*V = 1`), the **hyperbolic**
normalization — *not* the fermionic Euclidean `u² + v² = 1`. With `u = cosh θ`, `v = sinh θ` the
transformation is exactly the **Lorentz boost** (`bosonicBogoliubov_mulVec_eq_lorentzBoost`).

## The commutative diagonalization (Nam–Napiórkowski–Solovej §1.3 example)

For `𝔸 = [[h,k],[k,h]]` (`h` = one-body energy, `k` = pairing), with `G := k/h` (`pairingRatio`):

* `𝔸 > 0 ⟺ |G| < 1` (`quadraticHamiltonian_pos_iff`, `pairingRatio_abs_lt_one_iff`) — the
  **timelike** / sub-luminal condition `|k| < h`;
* the diagonalized frequency is `ξ = √(h² − k²)` (`diagonalizedFrequency`), the **boost-invariant**
  `ξ² = lorentzianForm(h + ik)` (`diagonalizedFrequency_eq_lorentzianForm`) — the bosonic analogue of
  the rest mass / gap `√(E² − ξ²)`;
* the diagonalization **is a boost**: `(h, k) = (ξ cosh θ, ξ sinh θ)` for a unique rapidity `θ`
  (`exists_diagonalizing_rapidity`), with `G = k/h = tanh θ`.

So the Nam–Napiórkowski–Solovej bosonic Bogoliubov transformation is the Lorentz boost of this
development, the diagonalized frequency is the Minkowski invariant, and `𝔸 > 0` is the timelike
(harmonic-oscillator) regime of `ComplexOscillator.CausalRegimes`.

## Main results

* `symplecticS`, `symplecticS_quadratic_form` — the Minkowski symplectic metric.
* `bosonicBogoliubov`, `bosonicBogoliubov_S_form`, `bosonicBogoliubov_preserves_S_iff` — `𝒱ᵀ S 𝒱 = S
  ⟺ u² − v² = 1`.
* `bosonicBogoliubov_mulVec_eq_lorentzBoost`, `bosonicBogoliubov_cosh_sinh_preserves_S` — `𝒱` = boost.
* `quadraticHamiltonian_pos_iff`, `pairingRatio_abs_lt_one_iff` — `𝔸 > 0 ⟺ |G| < 1` (timelike).
* `diagonalizedFrequency`, `diagonalizedFrequency_eq_lorentzianForm`, `exists_diagonalizing_rapidity`
  — `ξ = √(h²−k²)` is the boost-invariant; diagonalization = boost.
* `bosonicBogoliubov_no_pairing` — `k = 0` (no squeezing) is the reversible/trivial fiber.

## Equation correspondence (Nam–Napiórkowski–Solovej 2016)

| This file | Paper object | Equation |
|---|---|---|
| `symplecticS` `S = diag(1, −1)` | symplectic matrix `S` | Eq. (9) |
| (CCR `[A(F₁), A*(F₂)] = ⟨F₁, S F₂⟩`, motivation) | generalized CCR | Eq. (8) |
| `bosonicBogoliubov` `𝒱 = [[u, v], [v, u]]` | `𝒱 = [[U, J*VJ*], [V, JUJ*]]` | Eq. (12) |
| `bosonicBogoliubov_preserves_S_iff` | `𝒱*S𝒱 = S` ; `U*U − V*V = 1` | Eqs. (11), (13) |
| `quadraticHamiltonian` `𝔸 = [[h, k], [k, h]]` | `𝔸 = [[h, k*], [k, JhJ*]]` (commutative) | Eq. (16), §1.3 |
| `pairingRatio` `G = k/h` | `G := |k| h⁻¹` | §1.3 |
| `quadraticHamiltonian_pos_iff` | `𝔸 > 0 ⟺ −1 < G < 1` | §1.3 |
| `diagonalizedFrequency` `ξ = √(h²−k²)` | `ξ = h√(1−G²) = √(h²−k²) > 0` | §1.3 (after Eq. (18)) |
| `exists_diagonalizing_rapidity` | `𝒱𝔸𝒱* = diag(ξ, ξ)` | §1.3 |

Shale's implementability condition `‖V‖²_HS = Tr(V*V) < ∞` (Eq. (14)), the operator-norm estimate
`‖𝒱‖ ∼ (1 − ‖G‖)^{−1/4}` (Eq. (19)–(20)), and the ground-state energy `inf σ(ℍ) ∼ −‖k h^{−1/2}‖²_HS`
(Eq. (21)) concern infinite-dimensional Fock-space implementability and are outside this single-mode
(finite-dimensional) scope.

## References

* P. T. Nam, M. Napiórkowski, J. P. Solovej, *Diagonalization of bosonic quadratic Hamiltonians by
  Bogoliubov transformations*, J. Funct. Anal. **270** (11) (2016) 4340–4368.
  doi:10.1016/j.jfa.2015.12.007.
* N. N. Bogoliubov, *On the theory of superfluidity*, J. Phys. (USSR) **11** (1947) 23–32 — the
  `dim ℌ = 2` case formalized here (ref. [4] therein).
* D. Shale, *Linear symmetries of free boson fields*, Trans. Amer. Math. Soc. **103** (1962)
  149–167. doi:10.1090/S0002-9947-1962-0137504-6 — Shale's condition, Eq. (14) (ref. [23] therein).
* This development: `ComplexOscillator.CausalRegimes`, `Rapidity.PoincarePolarMinkowskiInterval`,
  `TimeOperator.HyperbolicPoincareLorentzMisra`. Mathlib: `Real.arsinh`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization

/-! ## §A — the bosonic symplectic metric `S = diag(1, −1)` (the Minkowski signature) -/

/-- **The bosonic symplectic matrix** `S = diag(1, −1)` (Nam–Napiórkowski–Solovej Eq. 9) — the
"bosonic analogue to the identity in the fermionic case", the Minkowski metric. -/
def symplecticS : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- **`S` is the Minkowski quadratic form** `⟨(t,x), S(t,x)⟩ = t² − x²`. -/
theorem symplecticS_quadratic_form (t x : ℝ) :
    ![t, x] ⬝ᵥ (symplecticS *ᵥ ![t, x]) = t ^ 2 - x ^ 2 := by
  simp [symplecticS, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  ring

/-! ## §B — the single-mode bosonic Bogoliubov transformation `𝒱ᵀ S 𝒱 = S ⟺ u² − v² = 1` -/

/-- **The single-mode bosonic Bogoliubov transformation** `𝒱 = [[u, v], [v, u]]`
(Nam–Napiórkowski–Solovej Eq. 12, real commutative case). -/
def bosonicBogoliubov (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![u, v; v, u]

/-- **`𝒱ᵀ S 𝒱 = (u² − v²) · S`**: the Bogoliubov transformation scales the Minkowski metric by
`u² − v²`. -/
theorem bosonicBogoliubov_S_form (u v : ℝ) :
    (bosonicBogoliubov u v)ᵀ * symplecticS * bosonicBogoliubov u v = (u ^ 2 - v ^ 2) • symplecticS := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bosonicBogoliubov, symplecticS, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] <;> ring

/-- **The bosonic Bogoliubov condition** `𝒱ᵀ S 𝒱 = S ⟺ u² − v² = 1` (Nam–Napiórkowski–Solovej
Eq. 11/13, `U*U − V*V = 1`): the **hyperbolic** normalization, preserving the Minkowski metric. -/
theorem bosonicBogoliubov_preserves_S_iff (u v : ℝ) :
    (bosonicBogoliubov u v)ᵀ * symplecticS * bosonicBogoliubov u v = symplecticS
      ↔ u ^ 2 - v ^ 2 = 1 := by
  rw [bosonicBogoliubov_S_form]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simpa [symplecticS, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.head_cons] using h00
  · intro h; rw [h, one_smul]

/-- **The Bogoliubov transformation is the Lorentz boost**: `𝒱 = [[cosh θ, sinh θ], [sinh θ, cosh
θ]]` acts on `(t, x)` exactly as `lorentzBoost θ`. -/
theorem bosonicBogoliubov_mulVec_eq_lorentzBoost (θ t x : ℝ) :
    bosonicBogoliubov (Real.cosh θ) (Real.sinh θ) *ᵥ ![t, x]
      = ![(lorentzBoost θ t x).1, (lorentzBoost θ t x).2] := by
  unfold bosonicBogoliubov lorentzBoost
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

/-- **The boost is a bosonic Bogoliubov transformation** (`cosh² θ − sinh² θ = 1`). -/
theorem bosonicBogoliubov_cosh_sinh_preserves_S (θ : ℝ) :
    (bosonicBogoliubov (Real.cosh θ) (Real.sinh θ))ᵀ * symplecticS
        * bosonicBogoliubov (Real.cosh θ) (Real.sinh θ) = symplecticS :=
  (bosonicBogoliubov_preserves_S_iff _ _).mpr (Real.cosh_sq_sub_sinh_sq θ)

/-! ## §C — the commutative diagonalization: `𝔸 > 0 ⟺ |G| < 1`, frequency `ξ = √(h² − k²)` -/

/-- **The single-mode quadratic Hamiltonian** `𝔸 = [[h, k], [k, h]]` (`h` energy, `k` pairing). -/
def quadraticHamiltonian (h k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![h, k; k, h]

/-- **The eigenvalues of `𝔸` are `h ± k`** (eigenvectors `(1, ±1)`): so `𝔸 > 0 ⟺ h + k > 0 ∧
h − k > 0 ⟺ |k| < h`. -/
theorem quadraticHamiltonian_pos_iff (h k : ℝ) :
    (0 < h + k ∧ 0 < h - k) ↔ |k| < h := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **The pairing ratio** `G = k/h` (Nam–Napiórkowski–Solovej §1.3): the bosonic "velocity". -/
def pairingRatio (h k : ℝ) : ℝ := k / h

/-- **`|G| < 1 ⟺ |k| < h`** (`𝔸 > 0`): the timelike / sub-luminal condition. -/
theorem pairingRatio_abs_lt_one_iff (h k : ℝ) (hh : 0 < h) :
    |pairingRatio h k| < 1 ↔ |k| < h := by
  unfold pairingRatio
  rw [abs_div, abs_of_pos hh, div_lt_one hh]

/-- **The diagonalized frequency** `ξ = √(h² − k²)` (Nam–Napiórkowski–Solovej: `ξ = h√(1−G²) =
√(h²−k²)`) — the bosonic analogue of the rest mass / gap. -/
def diagonalizedFrequency (h k : ℝ) : ℝ := Real.sqrt (h ^ 2 - k ^ 2)

/-- **`ξ² = h² − k²`** (for `|k| ≤ h`). -/
theorem diagonalizedFrequency_sq (h k : ℝ) (hk : |k| ≤ h) :
    diagonalizedFrequency h k ^ 2 = h ^ 2 - k ^ 2 := by
  unfold diagonalizedFrequency
  rw [Real.sq_sqrt]
  nlinarith [sq_abs k, abs_nonneg k, hk]

/-- **The diagonalized frequency is the Minkowski (boost) invariant** `ξ² = lorentzianForm(h + ik)`:
the diagonalization preserves it — the bosonic invariant mass. -/
theorem diagonalizedFrequency_eq_lorentzianForm (h k : ℝ) (hk : |k| ≤ h) :
    diagonalizedFrequency h k ^ 2 = lorentzianForm ((h : ℂ) + (k : ℂ) * Complex.I) := by
  rw [diagonalizedFrequency_sq h k hk, lorentzianForm_ofReal_add_mul_I]

/-- **The diagonalization is a Lorentz boost** of the rest frame: for `0 < h`, `|k| < h` there is a
rapidity `θ` with `k = ξ sinh θ` and `h = ξ cosh θ` (`ξ = √(h²−k²)`). So `(h, k)` is the boost of the
diagonal `(ξ, 0)`, and `G = k/h = tanh θ`. -/
theorem exists_diagonalizing_rapidity (h k : ℝ) (hh : 0 < h) (hk : |k| < h) :
    ∃ θ : ℝ, k = diagonalizedFrequency h k * Real.sinh θ
      ∧ h = diagonalizedFrequency h k * Real.cosh θ := by
  have hξ : 0 < diagonalizedFrequency h k := by
    unfold diagonalizedFrequency
    apply Real.sqrt_pos.mpr
    nlinarith [sq_abs k, abs_nonneg k, hk]
  have hξne : diagonalizedFrequency h k ≠ 0 := hξ.ne'
  refine ⟨Real.arsinh (k / diagonalizedFrequency h k), ?_, ?_⟩
  · rw [Real.sinh_arsinh]; field_simp
  · have hsink : diagonalizedFrequency h k
        * Real.sinh (Real.arsinh (k / diagonalizedFrequency h k)) = k := by
      rw [Real.sinh_arsinh]; field_simp
    have hcs : Real.cosh (Real.arsinh (k / diagonalizedFrequency h k)) ^ 2
        = 1 + Real.sinh (Real.arsinh (k / diagonalizedFrequency h k)) ^ 2 := by
      have := Real.cosh_sq_sub_sinh_sq (Real.arsinh (k / diagonalizedFrequency h k)); linarith
    have key : h ^ 2
        = (diagonalizedFrequency h k * Real.cosh (Real.arsinh (k / diagonalizedFrequency h k))) ^ 2 := by
      rw [mul_pow, hcs, mul_add, mul_one,
        show diagonalizedFrequency h k ^ 2
              * Real.sinh (Real.arsinh (k / diagonalizedFrequency h k)) ^ 2
            = (diagonalizedFrequency h k
                * Real.sinh (Real.arsinh (k / diagonalizedFrequency h k))) ^ 2 by ring,
        hsink, diagonalizedFrequency_sq h k hk.le]
      ring
    calc h = Real.sqrt (h ^ 2) := (Real.sqrt_sq hh.le).symm
      _ = Real.sqrt ((diagonalizedFrequency h k
            * Real.cosh (Real.arsinh (k / diagonalizedFrequency h k))) ^ 2) := by rw [key]
      _ = diagonalizedFrequency h k * Real.cosh (Real.arsinh (k / diagonalizedFrequency h k)) :=
          Real.sqrt_sq (mul_nonneg hξ.le (Real.cosh_pos _).le)

/-! ## §D — the reversible (no-pairing) fiber and the bosonic vs fermionic signature -/

/-- **No pairing `k = 0` is the reversible / trivial fiber**: `𝔸 = h · 1` is already diagonal
(no squeezing, `G = 0`, `ξ = |h|`), the bosonic Bogoliubov transformation is the identity. The
pairing `k` (the off-diagonal) is the squeezing that generates mode entanglement / entropic time. -/
theorem bosonicBogoliubov_no_pairing (h : ℝ) :
    quadraticHamiltonian h 0 = h • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold quadraticHamiltonian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

/-- **Bosonic vs fermionic signature.** The bosonic Bogoliubov transformation preserves the
**Minkowski** metric `S = diag(1,−1)` with `u² − v² = 1` (hyperbolic, the boost); the fermionic case
uses the **identity** metric, and a rotation preserves the Euclidean form `t² + x²`
(`rotation_preserves_euclidean`). The signature of `S` is what distinguishes the two. -/
theorem bosonic_minkowski_vs_fermionic_euclidean (u v θ E ξ : ℝ) :
    ((bosonicBogoliubov u v)ᵀ * symplecticS * bosonicBogoliubov u v = symplecticS ↔ u ^ 2 - v ^ 2 = 1)
      ∧ (euclidRotation θ E ξ).1 ^ 2 + (euclidRotation θ E ξ).2 ^ 2 = E ^ 2 + ξ ^ 2 :=
  ⟨bosonicBogoliubov_preserves_S_iff u v, rotation_preserves_euclidean θ E ξ⟩

/-! ## §E — the bundled link -/

/-- **The Nam–Napiórkowski–Solovej bosonic Bogoliubov diagonalization is the Lorentz boost.** For
`0 < h`, `|k| < h` (`𝔸 = [[h,k],[k,h]] > 0`):

* the Bogoliubov transformation preserves the Minkowski metric, `𝒱ᵀ S 𝒱 = S ⟺ u² − v² = 1`;
* `𝔸 > 0 ⟺ |G| < 1` (`G = k/h`, the timelike condition);
* the diagonalized frequency `ξ = √(h² − k²)` is the Minkowski (boost) invariant
  `ξ² = lorentzianForm(h + ik)`;
* the diagonalization is a boost: `(h, k) = (ξ cosh θ, ξ sinh θ)` for a rapidity `θ`. -/
theorem bosonic_bogoliubov_is_boost (h k : ℝ) (hh : 0 < h) (hk : |k| < h) :
    (∀ u v : ℝ, (bosonicBogoliubov u v)ᵀ * symplecticS * bosonicBogoliubov u v = symplecticS
        ↔ u ^ 2 - v ^ 2 = 1)
      ∧ (|pairingRatio h k| < 1 ↔ |k| < h)
      ∧ diagonalizedFrequency h k ^ 2 = lorentzianForm ((h : ℂ) + (k : ℂ) * Complex.I)
      ∧ ∃ θ : ℝ, k = diagonalizedFrequency h k * Real.sinh θ
          ∧ h = diagonalizedFrequency h k * Real.cosh θ :=
  ⟨bosonicBogoliubov_preserves_S_iff, pairingRatio_abs_lt_one_iff h k hh,
   diagonalizedFrequency_eq_lorentzianForm h k hk.le, exists_diagonalizing_rapidity h k hh hk⟩

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization

end

end

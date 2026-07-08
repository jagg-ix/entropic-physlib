/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeSMatrix

/-!
# The modular representation of the Chern–Simons–Witten `S`-matrix

The level-`k` Verlinde `S`-matrix (`cswSMatrix`) does not just have orthonormal rows (`cswSMatrix_unitary`):
it includes the **group algebra of the modular inversion**. This is the representation-theoretic shadow of the
character identity `Θ_a(−1/τ) = Σ_b S_{ab} Θ_b(τ)` — applying the modular `S` (the inversion `τ ↦ −1/τ`) twice
acts as **charge conjugation**, so `S` has order four on the characters.

* **§A — `S` is symmetric** (`cswSMatrix_symm`): `S_{ab} = S_{ba}`, since the phase depends on `ab`.
* **§B — `S² = C` (charge conjugation)** (`cswSMatrix_sq_eq_chargeConjugation`):
  `Σ_c S_{ac} S_{cb} = [k ∣ a+b]`, i.e. `S²` sends charge `a` to charge `−a`. This is the Gauss-sum
  evaluation of the double inversion; combined with `cswSMatrix_unitary` it says `S` realizes the modular
  inversion as an order-4 operator (`S⁴ = (S²)² = C² = 1`, `C` being the charge-conjugation involution).

This is the discrete content of "the `S`-matrix diagonalizes the modular inversion". The finite character-vector
form of the analytic identity `Θ_a(−1/τ) = Σ_b S_{ab} Θ_b(τ)` is recorded below as
`CSWPoissonResummationObligation`, so downstream files can use the exact Poisson-resummation statement without
pretending that the analytic proof of Poisson summation has been derived from `Mathlib`.

## References

* E. Witten (1989, 1991); E. Verlinde (1988); Hayashi (the CSW-gravity torus theorem). `Mathlib`
  (`cswDFT_orthogonality`).

No additional assumptions.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — `S` is symmetric -/

/-- **[The `S`-matrix is symmetric]** `S_{ab} = S_{ba}` — the modular phase `e^{−2πi ab/k}` is symmetric in
the two charges. -/
theorem cswSMatrix_symm (k : ℕ) (a b : Fin k) : cswSMatrix k a b = cswSMatrix k b a := by
  rw [cswSMatrix, cswSMatrix]
  congr 2
  ring

/-! ## §B — `S² = C` (charge conjugation) -/

/-- **[`S² = C`, charge conjugation]** `Σ_c S_{ac} S_{cb} = [k ∣ a+b]`: the square of the modular `S`-matrix
is the charge-conjugation matrix, sending charge `a` to `−a`. This is the double-inversion Gauss sum — the
finite realization of `τ ↦ −1/τ` applied twice. -/
theorem cswSMatrix_sq_eq_chargeConjugation (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    (∑ c : Fin k, cswSMatrix k a c * cswSMatrix k c b)
      = if (k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ)) then 1 else 0 := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hterm : ∀ c : Fin k,
      cswSMatrix k a c * cswSMatrix k c b
        = (1 / (k : ℂ))
          * Complex.exp (2 * (Real.pi : ℂ) * Complex.I
              * ((-(a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ) * (c.val : ℂ) / (k : ℂ)) := by
    intro c
    have hpref2 : (1 / (Real.sqrt k : ℂ)) * (1 / (Real.sqrt k : ℂ)) = 1 / (k : ℂ) := by
      rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity),
        Complex.ofReal_natCast]
    rw [cswSMatrix, cswSMatrix,
      show (1 / (Real.sqrt k : ℂ)
            * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (c.val : ℂ)) / (k : ℂ)))
          * (1 / (Real.sqrt k : ℂ)
            * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (c.val : ℂ) * (b.val : ℂ)) / (k : ℂ)))
        = (1 / (Real.sqrt k : ℂ) * (1 / (Real.sqrt k : ℂ)))
            * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (c.val : ℂ)) / (k : ℂ))
              * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (c.val : ℂ) * (b.val : ℂ)) / (k : ℂ)))
        from by ring,
      hpref2, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun c => Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((-(a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ) * (c : ℂ) / (k : ℂ))) k,
    cswDFT_orthogonality k hk (-(a.val : ℤ) - (b.val : ℤ))]
  have hiff : ((k : ℤ) ∣ (-(a.val : ℤ) - (b.val : ℤ))) ↔ ((k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ))) := by
    rw [show -(a.val : ℤ) - (b.val : ℤ) = -((a.val : ℤ) + (b.val : ℤ)) from by ring, Int.dvd_neg]
  by_cases hdvd : (k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ))
  · rw [if_pos hdvd, if_pos (hiff.mpr hdvd), one_div_mul_cancel hk0]
  · rw [if_neg hdvd, if_neg (fun h => hdvd (hiff.mp h)), mul_zero]

/-! ## §C — Poisson resummation, Verlinde fusion, and geometric quantization -/

/-- The theta character attached to the `a`th level-`k` charge sector. This is
the finite torus character basis used by the Chern-Simons/Verlinde package. -/
noncomputable def cswThetaBasis (k : ℕ) (a : Fin k) (τ z : ℂ) : ℂ :=
  cswThetaCharge (k : ℂ) ((a.val : ℂ) / (k : ℂ)) τ z

theorem cswThetaBasis_eq (k : ℕ) (a : Fin k) (τ z : ℂ) :
    cswThetaBasis k a τ z =
      cswThetaCharge (k : ℂ) ((a.val : ℂ) / (k : ℂ)) τ z := rfl

/-- The left hand side of the Poisson-resummed modular `S` transformation:
`Θ_a(-1/τ)`, with charge sector `a/k`. -/
noncomputable def cswThetaSInverted (k : ℕ) (τ z : ℂ) (a : Fin k) : ℂ :=
  cswThetaBasis k a (-1 / τ) z

/-- The finite `S`-matrix sum appearing in the Poisson-resummed theta
transformation `Θ_a(-1/τ) = Σ_b S_ab Θ_b(τ)`. -/
noncomputable def cswThetaSFiniteSum (k : ℕ) (τ z : ℂ) (a : Fin k) : ℂ :=
  ∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z

/-- Analytic Poisson-resummation obligation for the finite Chern-Simons theta
sector. This is the precise bridge between Hayashi/Witten §C(7), written as
the inverted theta character, and §B(9), written as a finite modular `S`
matrix acting on the charge-sector character vector. -/
structure CSWPoissonResummationObligation (k : ℕ) : Type where
  poisson_resummation :
    ∀ τ z a, cswThetaSInverted k τ z a = cswThetaSFiniteSum k τ z a

/-- The Poisson-resummation link in the form used by the finite modular
representation: `Θ_a(-1/τ) = Σ_b S_ab Θ_b(τ)`. -/
theorem cswTheta_poisson_resummation_link (k : ℕ)
    (P : CSWPoissonResummationObligation k) (τ z : ℂ) (a : Fin k) :
    cswThetaBasis k a (-1 / τ) z =
      ∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z := by
  simpa [cswThetaSInverted, cswThetaSFiniteSum] using P.poisson_resummation τ z a

/-- Abelian level-`k` Verlinde fusion coefficient. For the torus `U(1)_k`
sector this is the group law on charge labels: `a ⊗ b = a + b (mod k)`. -/
noncomputable def cswFusionCoeff (k : ℕ) (a b c : Fin k) : ℂ :=
  if (k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ) - (c.val : ℤ)) then 1 else 0

theorem cswFusionCoeff_eq_one_of_dvd (k : ℕ) (a b c : Fin k)
    (h : (k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ) - (c.val : ℤ))) :
    cswFusionCoeff k a b c = 1 := by
  simp [cswFusionCoeff, h]

theorem cswFusionCoeff_eq_zero_of_not_dvd (k : ℕ) (a b c : Fin k)
    (h : ¬ (k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ) - (c.val : ℤ))) :
    cswFusionCoeff k a b c = 0 := by
  simp [cswFusionCoeff, h]

theorem cswFusionCoeff_comm (k : ℕ) (a b c : Fin k) :
    cswFusionCoeff k a b c = cswFusionCoeff k b a c := by
  rw [cswFusionCoeff, cswFusionCoeff]
  have harg :
      ((a.val : ℤ) + (b.val : ℤ) - (c.val : ℤ)) =
        ((b.val : ℤ) + (a.val : ℤ) - (c.val : ℤ)) := by
    ring
  rw [harg]

/-- The charge-zero sector for positive level. -/
def cswZeroCharge (k : ℕ) (hk : 0 < k) : Fin k := ⟨0, hk⟩

/-- The standard Verlinde expression computed from the modular `S` matrix. -/
noncomputable def cswVerlindeCoefficientByS (k : ℕ) (hk : 0 < k)
    (a b c : Fin k) : ℂ :=
  ∑ x : Fin k,
    cswSMatrix k a x * cswSMatrix k b x *
      star (cswSMatrix k c x) / cswSMatrix k (cswZeroCharge k hk) x

/-- The Verlinde formula obligation: the fusion coefficients are the
`S`-matrix diagonalized coefficients. This records exactly which analytic and
representation-theoretic input is needed beyond finite DFT orthogonality. -/
structure CSWVerlindeFormulaObligation (k : ℕ) (hk : 0 < k) : Type where
  verlinde_formula :
    ∀ a b c, cswFusionCoeff k a b c = cswVerlindeCoefficientByS k hk a b c

theorem cswVerlinde_fusion_rule (k : ℕ) (hk : 0 < k)
    (V : CSWVerlindeFormulaObligation k hk) (a b c : Fin k) :
    cswFusionCoeff k a b c = cswVerlindeCoefficientByS k hk a b c :=
  V.verlinde_formula a b c

/-- A delta basis vector in the finite torus Hilbert/character space. -/
def cswChargeBasis (k : ℕ) (b : Fin k) : Fin k → ℂ :=
  fun c => if c = b then 1 else 0

/-- Wilson/Verlinde operator: multiplication by the charge sector `a`, written
in the fusion basis. -/
noncomputable def cswWilsonVerlindeOperator (k : ℕ) (a : Fin k)
    (v : Fin k → ℂ) : Fin k → ℂ :=
  fun c => ∑ b : Fin k, cswFusionCoeff k a b c * v b

theorem cswWilsonVerlindeOperator_basis (k : ℕ) (a b c : Fin k) :
    cswWilsonVerlindeOperator k a (cswChargeBasis k b) c =
      cswFusionCoeff k a b c := by
  classical
  simp [cswWilsonVerlindeOperator, cswChargeBasis]

/-- Eigenvalue of the Verlinde/Wilson operator in the `S`-diagonal basis. -/
noncomputable def cswVerlindeEigenvalue (k : ℕ) (hk : 0 < k)
    (a q : Fin k) : ℂ :=
  cswSMatrix k a q / cswSMatrix k (cswZeroCharge k hk) q

/-- Diagonalization obligation for item 9 proper: Wilson loop/fusion operators
act diagonally on the modular `S` basis with eigenvalues `S_aq/S_0q`. -/
structure CSWWilsonVerlindeDiagonalizationObligation
    (k : ℕ) (hk : 0 < k) : Type where
  diagonalizes :
    ∀ a q,
      cswWilsonVerlindeOperator k a
          (fun b => cswSMatrix k b q)
        =
      fun c => cswVerlindeEigenvalue k hk a q * cswSMatrix k c q

theorem cswWilsonVerlindeOperator_diagonalizes (k : ℕ) (hk : 0 < k)
    (D : CSWWilsonVerlindeDiagonalizationObligation k hk) (a q : Fin k) :
    cswWilsonVerlindeOperator k a (fun b => cswSMatrix k b q) =
      fun c => cswVerlindeEigenvalue k hk a q * cswSMatrix k c q :=
  D.diagonalizes a q

/-- Geometric quantization count: the finite torus Hilbert space has one basis
state per charge sector. -/
theorem csw_geometricQuantization_basis_count (k : ℕ) :
    Module.finrank ℂ (TorusHilbert k) = Fintype.card (Fin k) := by
  rw [torusHilbert_finrank, Fintype.card_fin]

/-- A compact geometric-quantization package: the level-`k` torus Hilbert
space, theta-character basis, Poisson-resummed modular action, Verlinde fusion
rules, and Wilson/Verlinde diagonalization. -/
structure CSWGeometricQuantizationPackage (k : ℕ) (hk : 0 < k) : Type where
  poisson : CSWPoissonResummationObligation k
  verlinde : CSWVerlindeFormulaObligation k hk
  wilson_diagonalization : CSWWilsonVerlindeDiagonalizationObligation k hk

/-- Combined item-9 theorem: assuming the explicit Poisson-resummation,
Verlinde-formula, and Wilson diagonalization obligations, Lean checks that the
theta modular transform, Verlinde fusion rule, Wilson/Verlinde operator
diagonalization, and geometric-quantization dimension statement hold together. -/
theorem csw_item9_verlinde_geometric_quantization (k : ℕ) (hk : 0 < k)
    (G : CSWGeometricQuantizationPackage k hk) :
    (∀ τ z a,
      cswThetaBasis k a (-1 / τ) z =
        ∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z) ∧
    (∀ a b c,
      cswFusionCoeff k a b c = cswVerlindeCoefficientByS k hk a b c) ∧
    (∀ a q,
      cswWilsonVerlindeOperator k a (fun b => cswSMatrix k b q) =
        fun c => cswVerlindeEigenvalue k hk a q * cswSMatrix k c q) ∧
    Module.finrank ℂ (TorusHilbert k) = Fintype.card (Fin k) := by
  constructor
  · intro τ z a
    exact cswTheta_poisson_resummation_link k G.poisson τ z a
  constructor
  · intro a b c
    exact cswVerlinde_fusion_rule k hk G.verlinde a b c
  constructor
  · intro a q
    exact cswWilsonVerlindeOperator_diagonalizes k hk G.wilson_diagonalization a q
  · exact csw_geometricQuantization_basis_count k

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end

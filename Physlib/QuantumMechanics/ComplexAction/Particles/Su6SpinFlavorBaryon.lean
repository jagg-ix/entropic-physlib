/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Nat.Choose.Basic
public import Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir
meta import Zil

/-!
# The colour-singlet baryon and the `SU(6)` spin-flavour `56`

The physical-baryon layer in two namespaces (each formerly its own module):

* **Part I — `ColorSingletBaryon`.** The defining fact of the strong sector: the baryon colour
  wavefunction `ε_{abc} q₁^a q₂^b q₃^c = det ![q₁,q₂,q₃]` (`baryonColor`) is `SU(3)`- (indeed
  `SL(3,ℂ)`-) invariant (`baryonColor_su3_invariant` — the singlet), totally antisymmetric under
  quark exchange (`baryonColor_antisymm` — the `S₃` sign representation), and vanishes when two
  quarks share a colour (`baryonColor_pauli` — colour Pauli exclusion). The meson side: the
  `q ⊗ q̄` colour matrix splits into the trace singlet (`mesonSinglet`) and the traceless octet
  (`mesonOctet_traceless`) — `3 ⊗ 3̄ = 1 ⊕ 8`.
* **Part II — `Su6SpinFlavorBaryon`.** The eightfold way from the Pauli principle: three quark
  spins `2⊗2⊗2 = 4⊕2⊕2` (`spin_decomp`), the totally symmetric spin-flavour
  `Sym³(ℂ⁶) = C(8,3) = 56` (`su6_56_sym`) branching as `56 = (10,4) ⊕ (8,2) = 40 + 16`
  (`su6_56_split` via `weylDim3`), and the total antisymmetry of the baryon amplitude — symmetric
  spin-flavour times the antisymmetric colour singlet (`baryon_totally_antisymmetric`, consuming
  `baryonColor_antisymm`).

**Honest layering.** Exact: the `SU(3)` invariance (`det_mul`, `SpecialLinearGroup.det_coe`),
antisymmetry (`det_permute`), colour Pauli (`det_zero_of_row_eq`), the trace/traceless split, the
spin/spin-flavour dimensions, and the `56` branching. Interpretive: the identification of `det`
with the `⋀³(ℂ³)` singlet of `3⊗3⊗3`, and of the `56` sub-multiplets with the physical octet
`(p,n,Λ,Σ,Ξ)` and decuplet `(Δ,Σ*,Ξ*,Ω)`.

## References

* Colour `SU(3)` and the eightfold way; the `ε_{abc}` baryon singlet; `SU(6)` spin-flavour symmetry,
  `56 = (8,½) ⊕ (10,3/2)`. Companion to `Particles.StrongInteractionColorOctet` (triality,
  confinement), `Particles.HadronChargeIntegrality` (`3∣n ⟺` integer charge), and
  `PermutationSignAntisymmetrizer` (`det = sign`); built on `Particles.Su3WeylDimensionCasimir`
  (including its `Su3TensorDecomposition` part).


-/

set_option autoImplicit false

open scoped BigOperators

open Matrix

noncomputable section

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon


/-- The **baryon colour wavefunction** `ε_{abc} q₁^a q₂^b q₃^c = det ![q₁, q₂, q₃]`: the totally antisymmetric
combination of the three quark colour vectors. -/
def baryonColor (q₁ q₂ q₃ : Fin 3 → ℂ) : ℂ := (Matrix.of ![q₁, q₂, q₃]).det

/-- **The baryon is a colour singlet** — invariant under a common `SU(3)` colour rotation `q ↦ U ·ᵥ q` of all
three quarks: `det` is unchanged because `det U = 1`. This is the defining property of confinement (the only
observed free colour states are singlets). -/
lemma baryonColor_su3_invariant (U : Matrix.SpecialLinearGroup (Fin 3) ℂ) (q₁ q₂ q₃ : Fin 3 → ℂ) :
    baryonColor ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ q₁) ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ q₂)
        ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ q₃) = baryonColor q₁ q₂ q₃ := by
  have hM : Matrix.of ![(U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ q₁, (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ q₂,
        (U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ q₃]
      = Matrix.of ![q₁, q₂, q₃] * (U : Matrix (Fin 3) (Fin 3) ℂ)ᵀ := by
    ext i j
    fin_cases i <;>
      simp [Matrix.mul_apply, Matrix.mulVec, Matrix.of_apply, Matrix.transpose_apply,
        dotProduct, mul_comm]
  rw [baryonColor, baryonColor, hM, Matrix.det_mul, Matrix.det_transpose,
    Matrix.SpecialLinearGroup.det_coe, mul_one]

/-- **Quark exchange flips the sign** `baryonColor q₂ q₁ q₃ = − baryonColor q₁ q₂ q₃`: the colour wavefunction
is totally antisymmetric — the `S₃` sign representation, the `sign(p)` coefficient of the Slater antisymmetrizer
(`PermutationSignAntisymmetrizer.antisymmetrizer_coeff_eq_permMatrix_det`). -/
lemma baryonColor_antisymm (q₁ q₂ q₃ : Fin 3 → ℂ) :
    baryonColor q₂ q₁ q₃ = - baryonColor q₁ q₂ q₃ := by
  have h : Matrix.of ![q₂, q₁, q₃]
      = (Matrix.of ![q₁, q₂, q₃] : Matrix (Fin 3) (Fin 3) ℂ).submatrix (Equiv.swap 0 1) id := by
    ext i j
    fin_cases i <;>
      simp [Matrix.submatrix_apply, Matrix.of_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
        show (Equiv.swap (0 : Fin 3) 1) 2 = 2 from by decide]
  rw [baryonColor, baryonColor, h, Matrix.det_permute, Equiv.Perm.sign_swap (by decide)]
  simp

/-- **Colour Pauli exclusion** `baryonColor q₁ q₁ q₃ = 0`: two quarks of the same colour give a vanishing
singlet — the three colours in a baryon must all differ (`ε_{abc}` needs distinct indices). -/
lemma baryonColor_pauli (q₁ q₃ : Fin 3 → ℂ) : baryonColor q₁ q₁ q₃ = 0 := by
  rw [baryonColor]
  exact Matrix.det_zero_of_row_eq (by decide : (0 : Fin 3) ≠ 1) (by funext k; simp [Matrix.of_apply])


/-- The **meson colour matrix** `q ⊗ q̄` on colour ⊗ anticolour. -/
def mesonColorMatrix (q qbar : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of (fun a b => q a * qbar b)

/-- The **meson colour singlet** `Σ_a q^a q̄_a` — the `δ_{ab}` (trace) contraction, the `1` in `3 ⊗ 3̄`. -/
def mesonSinglet (q qbar : Fin 3 → ℂ) : ℂ := Matrix.trace (mesonColorMatrix q qbar)

/-- **The singlet is the colour trace** `mesonSinglet = Σ_a q^a q̄_a`. -/
lemma mesonSinglet_eq (q qbar : Fin 3 → ℂ) : mesonSinglet q qbar = ∑ a, q a * qbar a := by
  simp [mesonSinglet, mesonColorMatrix, Matrix.trace, Matrix.diag, Matrix.of_apply]

/-- **The octet is the traceless part** `tr(M − (tr M / 3)·I) = 0`: any colour matrix splits as the singlet
(trace) plus the traceless octet, `3 ⊗ 3̄ = 1 ⊕ 8` — the same trivial ⊕ traceless split as the standard
representation. -/
lemma mesonOctet_traceless (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace (M - (Matrix.trace M / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  norm_num

end Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon

/-! ## Part II — the baryon `SU(6)` spin-flavour `56` and the Pauli principle -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.Su6SpinFlavorBaryon

open Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir
open Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon


/-- **Three quark spins** `2 ⊗ 2 ⊗ 2 = 4 ⊕ 2 ⊕ 2` (`8 = 4 + 2 + 2`): spin 3/2 (the symmetric `4`) plus two
mixed spin-1/2 (`2`). -/
lemma spin_decomp : 2 ^ 3 = 4 + 2 + 2 := by decide

/-- **The symmetric spin-3/2** `Sym³(ℂ²) = C(4,3) = 4` — the totally symmetric three-spin state. -/
lemma spin32_sym : Nat.choose 4 3 = 4 := by decide


/-- The **quark spin-flavour dimension** `3 · 2 = 6`: three light flavours times two spin states. -/
lemma quark_spinflavour_dim : 3 * 2 = 6 := by decide

/-- **The baryon spin-flavour `56`** `Sym³(ℂ⁶) = C(8,3) = 56`: the totally symmetric three-quark spin-flavour
multiplet — the `SU(6)` `56`, forced symmetric by antisymmetric colour and symmetric space. -/
lemma su6_56_sym : Nat.choose 8 3 = 56 := by decide


/-- **The `56` branches into decuplet ⊕ octet** `56 = 10·4 + 8·2 = 40 + 16`: the flavour decuplet (`weylDim3 3 0
= 10`) with spin 3/2 (`4`), plus the flavour octet (`weylDim3 1 1 = 8`) with spin 1/2 (`2`). -/
lemma su6_56_split : Nat.choose 8 3 = weylDim3 3 0 * 4 + weylDim3 1 1 * 2 := by decide


/-- **The baryon is a fermion (Pauli)** — swapping two quarks flips the sign of the total amplitude. With a
**symmetric** spin-flavour-space amplitude `ψ` (unchanged under the swap) and the **antisymmetric** colour
singlet, the total baryon amplitude `colour × ψ` is antisymmetric:
`baryonColor q₂ q₁ q₃ · ψ = − (baryonColor q₁ q₂ q₃ · ψ)` — via `ColorSingletBaryon.baryonColor_antisymm`. So
antisymmetric colour × symmetric spin-flavour ⇒ totally antisymmetric, the eightfold-way `56`. -/
lemma baryon_totally_antisymmetric (q₁ q₂ q₃ : Fin 3 → ℂ) (ψ : ℂ) :
    baryonColor q₂ q₁ q₃ * ψ = - (baryonColor q₁ q₂ q₃ * ψ) := by
  rw [baryonColor_antisymm]; ring

end Physlib.QuantumMechanics.ComplexAction.Particles.Su6SpinFlavorBaryon

end

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon.baryonColor_su3_invariant where
  formalizes @ "claim:baryon-colour-singlet-is-the-sl3c-invariant-epsilon-determinant",
  supported_by @ "paper:gell-mann-1964-eightfold-way"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon.baryonColor_antisymm where
  supported_by @ "lean:Space.needs",
  formalizes @ "claim:baryon-colour-wavefunction-is-totally-antisymmetric-s3-sign-representation",
  requires @ "claim:baryon-colour-singlet-is-the-sl3c-invariant-epsilon-determinant"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.Su6SpinFlavorBaryon.su6_56_split where
  formalizes @ "claim:su6-fifty-six-branches-into-spin-half-octet-and-spin-three-half-decuplet",
  supported_by @ "paper:gursey-radicati-1964-su6-spin-flavour"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.Su6SpinFlavorBaryon.baryon_totally_antisymmetric where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon.baryonColor_antisymm",
  formalizes @ "claim:antisymmetric-colour-times-symmetric-spin-flavour-makes-the-baryon-a-fermion",
  requires @ "claim:baryon-colour-wavefunction-is-totally-antisymmetric-s3-sign-representation",
  requires @ "claim:su6-fifty-six-branches-into-spin-half-octet-and-spin-three-half-decuplet",
  caveat @ "claim:eightfold-way-multiplet-identification-with-physical-baryons-is-interpretive"

zil_file_contract physlib.su6SpinFlavorBaryon where
  promises "The colour-singlet baryon and the SU(6) fifty-six from the Pauli principle: the epsilon determinant is SL(3,C)-invariant and totally antisymmetric, the symmetric spin-flavour fifty-six branches into the spin-half octet and spin-three-half decuplet, and antisymmetric colour times symmetric spin-flavour makes the baryon a fermion."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon.baryonColor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.weylDim3"]
  forbids_substitutes ["the identification of the fifty-six sub-multiplets with the physical octet and decuplet, which is interpretive"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon.baryonColor_su3_invariant,
    Physlib.QuantumMechanics.ComplexAction.Particles.ColorSingletBaryon.baryonColor_antisymm,
    Physlib.QuantumMechanics.ComplexAction.Particles.Su6SpinFlavorBaryon.su6_56_split,
    Physlib.QuantumMechanics.ComplexAction.Particles.Su6SpinFlavorBaryon.baryon_totally_antisymmetric]

/- ZIL-END -/

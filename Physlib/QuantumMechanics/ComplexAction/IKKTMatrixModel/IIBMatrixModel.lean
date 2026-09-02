/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Complex.Basic
meta import Zil

/-!
# The IIB matrix model: scaling, coupling absorption, and translation symmetry (Iso–Kawai)

Formalizes the exact/algebraic structure of the bosonic part of the type IIB matrix-model action of
S. Iso, H. Kawai, *Space-Time and Matter in IIB Matrix Model — gauge symmetry and diffeomorphism*
(hep-th/9903217). The action (Eq. 1.1) is `S = −(1/g²) Tr(¼[A_μ,A_ν][A^μ,A^ν] + …)`; its bosonic potential is
`B(A) = ¼ Σ_{μν} Tr([A_μ,A_ν]²)`.

* **§A — the matrix commutator** `[X,Y] = XY − YX`: bilinear, scales as `[cX,cY] = c²[X,Y]`
  (`iibComm_smul₂`), and is **invariant under identity shifts** `[X + c·1, Y + d·1] = [X,Y]`
  (`iibComm_add_smul_one`).
* **§B — quartic homogeneity** (`iibBosonic_smul`): `B(cA) = c⁴ B(A)`.
* **§C — translation symmetry** (Eq. 1.3) (`iibBosonic_translation_invariant`): `B(A_μ + c_μ·1) = B(A_μ)` —
  the extra bosonic symmetry `δA_μ = c_μ·1` that becomes a space-time translation.
* **§D — coupling absorption** (Eq. 1.7) (`iibBosonicAction_coupling_absorbed`): under `A_μ → √g · A_μ` the
  bosonic action `−(1/g²) B(A)` becomes `−B(A)` — the coupling `g` is absorbed, so the model has **no free
  parameters**.

## References

* S. Iso, H. Kawai (1999), hep-th/9903217 (KEK-TH-617), Eqs. (1.1), (1.3), (1.7).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel

variable {N : ℕ}


/-- The matrix commutator `[X,Y] = XY − YX`. -/
def iibComm (X Y : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := X * Y - Y * X

/-- **[`[cX,cY] = c²[X,Y]`]** — the commutator is quadratically homogeneous under common scaling. -/
lemma iibComm_smul₂ (c : ℂ) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    iibComm (c • X) (c • Y) = c ^ 2 • iibComm X Y := by
  simp only [iibComm, smul_mul_smul_comm, ← smul_sub, sq]

/-- **[`[X, d·1] = 0`]** — every matrix commutes with a multiple of the identity. -/
lemma iibComm_smul_one_right (X : Matrix (Fin N) (Fin N) ℂ) (d : ℂ) : iibComm X (d • 1) = 0 := by
  simp [iibComm]

/-- **[`[c·1, Y] = 0`]**. -/
lemma iibComm_smul_one_left (Y : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) : iibComm (c • 1) Y = 0 := by
  simp [iibComm]

lemma iibComm_add_left (X X' Y : Matrix (Fin N) (Fin N) ℂ) :
    iibComm (X + X') Y = iibComm X Y + iibComm X' Y := by
  simp only [iibComm, add_mul, mul_add]; abel

lemma iibComm_add_right (X Y Y' : Matrix (Fin N) (Fin N) ℂ) :
    iibComm X (Y + Y') = iibComm X Y + iibComm X Y' := by
  simp only [iibComm, add_mul, mul_add]; abel

/-- **[Identity-shift invariance] `[X + c·1, Y + d·1] = [X,Y]`** — the commutator only sees the traceless
(non-identity) parts; this is the algebraic heart of the translation symmetry `δA_μ = c_μ·1`. -/
lemma iibComm_add_smul_one (X Y : Matrix (Fin N) (Fin N) ℂ) (c d : ℂ) :
    iibComm (X + c • 1) (Y + d • 1) = iibComm X Y := by
  rw [iibComm_add_left, iibComm_add_right, iibComm_add_right, iibComm_smul_one_left,
    iibComm_smul_one_right, iibComm_smul_one_right, add_zero, add_zero, add_zero]


/-- **The IIB bosonic potential** `B(A) = ¼ Σ_{μν} Tr([A_μ,A_ν][A_μ,A_ν])` (Eq. 1.1, the `[A,A]²` term). -/
noncomputable def iibBosonic {d : ℕ} (A : Fin d → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  (1 / 4) * ∑ μ : Fin d, ∑ ν : Fin d, Matrix.trace (iibComm (A μ) (A ν) * iibComm (A μ) (A ν))

/-- **[Quartic homogeneity] `B(cA) = c⁴ B(A)`.** -/
lemma iibBosonic_smul {d : ℕ} (c : ℂ) (A : Fin d → Matrix (Fin N) (Fin N) ℂ) :
    iibBosonic (fun μ => c • A μ) = c ^ 4 * iibBosonic A := by
  unfold iibBosonic
  rw [show (c : ℂ) ^ 4 * ((1 / 4)
      * ∑ μ : Fin d, ∑ ν : Fin d, Matrix.trace (iibComm (A μ) (A ν) * iibComm (A μ) (A ν)))
      = (1 / 4) * (c ^ 4
        * ∑ μ : Fin d, ∑ ν : Fin d, Matrix.trace (iibComm (A μ) (A ν) * iibComm (A μ) (A ν))) from by
      ring]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [iibComm_smul₂, smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  ring

/-- **[Translation symmetry, Eq. 1.3] `B(A_μ + c_μ·1) = B(A_μ)`.** The bosonic action is invariant under the
constant identity shift `δA_μ = c_μ·1` — the extra bosonic symmetry interpreted as a space-time translation
of the emergent coordinates. -/
lemma iibBosonic_translation_invariant {d : ℕ} (A : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (c : Fin d → ℂ) :
    iibBosonic (fun μ => A μ + c μ • 1) = iibBosonic A := by
  unfold iibBosonic
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_)
  rw [iibComm_add_smul_one]


/-- **The bosonic IIB matrix-model action** `S = −(1/g²) B(A)` (Eq. 1.1, bosonic part). -/
noncomputable def iibBosonicAction {d : ℕ} (g : ℝ) (A : Fin d → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  -(1 / (g : ℂ) ^ 2) * iibBosonic A

/-- **[Coupling absorption, Eq. 1.7] `S_g(√g · A) = −B(A)`.** Under the field redefinition `A_μ → √g · A_μ`
the coupling `g` drops out of the bosonic action (`(√g)⁴ = g²` cancels `1/g²`) — the IIB matrix model has no
free parameters. -/
lemma iibBosonicAction_coupling_absorbed {d : ℕ} (g : ℝ) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) ℂ) :
    iibBosonicAction g (fun μ => ((Real.sqrt g : ℝ) : ℂ) • A μ) = -iibBosonic A := by
  have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hsq : ((Real.sqrt g : ℝ) : ℂ) ^ 4 = (g : ℂ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt hg.le]
  rw [iibBosonicAction, iibBosonic_smul, hsq]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibComm_smul_one_right where
  formalizes @ "claim:the-iib-matrix-commutator-with-a-central-scalar-vanishes",
  supported_by @ "paper:ishibashi-kawai-kitazawa-tsuchiya-1997-iib-matrix-model"

zil attach Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibBosonicAction_coupling_absorbed where
  formalizes @ "claim:the-iib-bosonic-action-absorbs-the-coupling-by-rescaling-the-matrices",
  requires @ "claim:the-iib-matrix-commutator-with-a-central-scalar-vanishes",
  supported_by @ "paper:ishibashi-kawai-kitazawa-tsuchiya-1997-iib-matrix-model",
  caveat @ "claim:the-bosonic-sector-only-the-fermionic-and-supersymmetric-completion-is-not-built"

zil_file_contract physlib.iibMatrixModel where
  promises "The IKKT / IIB matrix model bosonic sector: the matrix commutator is a genuine Lie bracket vanishing against the central scalars, and the bosonic action absorbs the coupling by rescaling the matrices, exhibiting the coupling as an overall normalization."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibComm",
    "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibBosonicAction"]
  forbids_substitutes ["the fermionic and supersymmetric completion of the model, not built here",
    "the emergent-spacetime interpretation of the eigenvalue distribution, not formalized"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibComm_smul_one_right,
    Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel.iibBosonicAction_coupling_absorbed]

/- ZIL-END -/

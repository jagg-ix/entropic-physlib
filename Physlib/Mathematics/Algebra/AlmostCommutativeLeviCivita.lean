/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Algebra.AlmostCommutative
public import Mathlib.Tactic.Module

/-!
# The Levi-Civita connection on almost commutative algebras — §3

Continues `Physlib.Mathematics.Algebra.AlmostCommutative` (the §2 foundations of Ngakeu, *Levi-Civita
connection on almost commutative algebras*, IJGMMP 4 (2007) 1075) with §3: the curvature of a `ρ`-linear
connection, metric compatibility, and the Ricci tensor / scalar curvature.

The `ρ`-derivations are an abstract `k`-module `D` with a degree map `deg`, a `ρ`-Lie bracket `br`, and a
connection `nabla`. The metric is the `A`-valued pairing `g : D → D → A` and `act : D → A → A` is the action
of a `ρ`-derivation on the algebra.

* **§A — curvature** (Def. 3.2, Prop. 3.9(a)). `rhoCurvature` `R(X,Y)Z = ∇_X∇_YZ − ρ(|X|,|Y|)∇_Y∇_XZ −
  ∇_{[X,Y]}Z` and `rhoCurvature_rho_antisymm` (`R(X,Y) = −ρ(|X|,|Y|)R(Y,X)`).
* **§B — metric compatibility and the Levi-Civita difference lemmas** (Eqs. 7, 8, Theorem 3.6).
  `IsRhoCompatible`, `IsRhoTorsionFree`, `IsNondegenerate`, and the two difference identities that the
  uniqueness of the Levi-Civita connection rests on (`compat_difference`, `torsionFree_difference`).
* **§C — Ricci tensor and scalar curvature** (Defs 3.12, 3.14, Prop. 3.13). `symmetrizedRicci` `Sym(tr R)`,
  `symmetrizedRicci_rho_symm` (the Ricci tensor is `ρ`-symmetric), and `scalarCurvature`.

**Honest layering.** All exact. The braided-Koszul *existence* of the connection (Eq. 9) and the final
uniqueness sign-chase (from the difference lemmas + nondegeneracy) are the deeper computational content of
Theorem 3.6 and are not carried out here; at `ρ ≡ 1` the whole structure reduces to the ordinary Levi-Civita
setting of `Curvature.LeviCivitaFromMetric`.
-/

@[expose] public section

namespace Physlib.Mathematics.Algebra.AlmostCommutativeLeviCivita

open Physlib.Mathematics.Algebra.AlmostCommutative

variable {G : Type*} [AddCommGroup G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {D : Type*} [AddCommGroup D] [Module k D]


/-- **The curvature of a `ρ`-linear connection** (Ngakeu Def. 3.2)
`R(X,Y)Z = ∇_X∇_YZ − ρ(|X|,|Y|)∇_Y∇_XZ − ∇_{[X,Y]}Z`. -/
def rhoCurvature (ρ : CommutationFactor G k) (deg : D → G) (br nabla : D → D → D) (X Y Z : D) : D :=
  nabla X (nabla Y Z) - ρ.factor (deg X) (deg Y) • nabla Y (nabla X Z) - nabla (br X Y) Z

/-- **[The curvature is `ρ`-antisymmetric] `R(X,Y) = −ρ(|X|,|Y|)R(Y,X)`** (Ngakeu Prop. 3.9(a)) — provided the
bracket is `ρ`-antisymmetric (`[X,Y] = −ρ(|X|,|Y|)[Y,X]`) and the connection is `k`-linear (and odd) in its
first slot. -/
lemma rhoCurvature_rho_antisymm (ρ : CommutationFactor G k) (deg : D → G) (br nabla : D → D → D)
    (hbr : ∀ V W, br V W = -(ρ.factor (deg V) (deg W) • br W V))
    (hlin : ∀ (c : k) (V W : D), nabla (c • V) W = c • nabla V W)
    (hneg : ∀ V W : D, nabla (-V) W = -nabla V W) (X Y Z : D) :
    rhoCurvature ρ deg br nabla X Y Z
      = -(ρ.factor (deg X) (deg Y) • rhoCurvature ρ deg br nabla Y X Z) := by
  have hf : ρ.factor (deg X) (deg Y) * ρ.factor (deg Y) (deg X) = 1 := ρ.factor_mul_symm _ _
  have hbrXY : nabla (br X Y) Z = -(ρ.factor (deg X) (deg Y) • nabla (br Y X) Z) := by
    rw [hbr X Y, hneg, hlin]
  simp only [rhoCurvature, hbrXY, smul_sub, smul_smul, hf, one_smul]
  module


/-- **A metric-compatible connection** (Ngakeu Eq. 8) `X·⟨V,W;g⟩ = ⟨∇_XV,W;g⟩ + ρ(|X|,|V|)⟨V,∇_XW;g⟩`, with
`act X` the action of the `ρ`-derivation `X` on `A` and `g` the `A`-valued metric pairing. -/
def IsRhoCompatible (ρ : CommutationFactor G k) (deg : D → G) (act : D → A → A) (g : D → D → A)
    (nabla : D → D → D) : Prop :=
  ∀ X V W, act X (g V W) = g (nabla X V) W + ρ.factor (deg X) (deg V) • g V (nabla X W)

/-- **A torsion-free connection** (Ngakeu Eq. 7) `[V,W] = ∇_VW − ρ(|V|,|W|)∇_WV`. -/
def IsRhoTorsionFree (ρ : CommutationFactor G k) (deg : D → G) (br nabla : D → D → D) : Prop :=
  ∀ V W, br V W = nabla V W - ρ.factor (deg V) (deg W) • nabla W V

/-- **The metric is nondegenerate** — if `⟨δ,W;g⟩ = 0` for all `W` then `δ = 0`. -/
def IsNondegenerate (g : D → D → A) : Prop := ∀ δ : D, (∀ W, g δ W = 0) → δ = 0

omit [Module k D] in
/-- **[Compatibility difference lemma]** the difference of two metric-compatible connections
`δ(X,V) = ∇_XV − ∇'_XV` satisfies `⟨δ(X,V),W;g⟩ + ρ(|X|,|V|)⟨V,δ(X,W);g⟩ = 0`. This is the first equation the
uniqueness of the Levi-Civita connection rests on. -/
lemma compat_difference (ρ : CommutationFactor G k) (deg : D → G) (act : D → A → A) (g : D → D → A)
    (nabla nabla' : D → D → D)
    (hc : IsRhoCompatible ρ deg act g nabla) (hc' : IsRhoCompatible ρ deg act g nabla')
    (hgL : ∀ (V V' W : D), g (V - V') W = g V W - g V' W)
    (hgR : ∀ (V W W' : D), g V (W - W') = g V W - g V W') (X V W : D) :
    g (nabla X V - nabla' X V) W + ρ.factor (deg X) (deg V) • g V (nabla X W - nabla' X W) = 0 := by
  have key : g (nabla X V) W + ρ.factor (deg X) (deg V) • g V (nabla X W)
      = g (nabla' X V) W + ρ.factor (deg X) (deg V) • g V (nabla' X W) := by
    rw [← hc X V W, ← hc' X V W]
  rw [hgL, hgR, smul_sub, sub_add_sub_comm, key, sub_self]

/-- **[Torsion-free difference lemma]** the difference `δ(V,W) = ∇_VW − ∇'_VW` of two torsion-free connections
is `ρ`-symmetric: `δ(V,W) = ρ(|V|,|W|)δ(W,V)`. -/
lemma torsionFree_difference (ρ : CommutationFactor G k) (deg : D → G) (br nabla nabla' : D → D → D)
    (ht : IsRhoTorsionFree ρ deg br nabla) (ht' : IsRhoTorsionFree ρ deg br nabla') (V W : D) :
    nabla V W - nabla' V W = ρ.factor (deg V) (deg W) • (nabla W V - nabla' W V) := by
  have key : nabla V W - ρ.factor (deg V) (deg W) • nabla W V
      = nabla' V W - ρ.factor (deg V) (deg W) • nabla' W V := by rw [← ht V W, ← ht' V W]
  rw [smul_sub]
  rw [sub_eq_sub_iff_add_eq_add] at key ⊢
  rw [key]; abel


/-- **The symmetrized Ricci tensor** (Ngakeu Def. 3.12) `⟨U,V;Ricci⟩ = ½(⟨U,V;tr R⟩ + ρ(|U|,|V|)⟨V,U;tr R⟩)`,
the symmetrization of the trace `trR` of the curvature. -/
noncomputable def symmetrizedRicci (ρ : CommutationFactor G k) (deg : D → G) (trR : D → D → A)
    (U V : D) : A :=
  (1 / 2 : k) • (trR U V + ρ.factor (deg U) (deg V) • trR V U)

omit [AddCommGroup D] [Module k D] in
/-- **[The Ricci tensor is `ρ`-symmetric] `⟨U,V;Ricci⟩ = ρ(|U|,|V|)⟨V,U;Ricci⟩`** (Ngakeu Prop. 3.13). -/
lemma symmetrizedRicci_rho_symm (ρ : CommutationFactor G k) (deg : D → G) (trR : D → D → A) (U V : D) :
    symmetrizedRicci ρ deg trR U V = ρ.factor (deg U) (deg V) • symmetrizedRicci ρ deg trR V U := by
  simp only [symmetrizedRicci]
  symm
  rw [smul_comm (ρ.factor (deg U) (deg V)) ((1 : k) / 2), smul_add, smul_smul, ρ.factor_mul_symm,
    one_smul, add_comm]

/-- **The scalar curvature** (Ngakeu Def. 3.14) `Scal_g = tr(Ric) = ∑ᵢ ρ(|xᵢ|,|yᵢ|)Rᵢᵢ`, the trace of the
Ricci operator over the (finite) coordinate basis `basis`, with `degX`, `degY` the degrees of the dual bases
and `Rdiag i` the diagonal Ricci component. -/
noncomputable def scalarCurvature {ι : Type*} [Fintype ι] (ρ : CommutationFactor G k)
    (degX degY : ι → G) (Rdiag : ι → A) : A :=
  ∑ i, ρ.factor (degX i) (degY i) • Rdiag i

end Physlib.Mathematics.Algebra.AlmostCommutativeLeviCivita

end

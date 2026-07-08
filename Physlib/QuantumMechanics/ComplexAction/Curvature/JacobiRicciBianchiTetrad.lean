/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
public import Mathlib.Algebra.Lie.Basic

/-!
# The orthonormal-tetrad connection algebra and the Jacobi–Ricci–Bianchi correspondence

Van den Bergh, *On the relation between the Einstein field equations and the Jacobi-Ricci-Bianchi system*
(arXiv:1302.6448). In the extended tetrad formalism the connection one-forms `Γᵃ_b = Γᵃ_bc ωᶜ` and the
commutation coefficients `γᶜ_ab` (`[∂ₐ,∂_b] = γᶜ_ab ∂_c`) of a **rigid orthonormal tetrad** are tied together,
and the **first Bianchi identity is the Jacobi identity** for the frame vector fields.

* **§A — the rigid-tetrad connection algebra.** `TetradConnection` includes the orthonormal/metric-compatible
 antisymmetry `Γ_{(ab)c} = 0` (Eq 7). `commCoeff` is `γᶜ_ab = 2Γᶜ_{[ba]}` (torsion-free, Eq 10),
 `commCoeff_antisymm` its lower-pair antisymmetry (Eq 8), and `koszul` the **Levi-Civita / Koszul formula**
 `Γ_cab = ½(γ_bca + γ_acb − γ_cab)` (Eq 11) — the connection is fixed by the commutation coefficients.
* **§B — first Bianchi ⟺ frame Jacobi.** `cyclicSum` is the common cyclic operator; `firstBianchi_iff_cyclicSum`
 recasts the first Bianchi identity `R_{a[bcd]}=0` (Eq 14, reusing `LeviCivita.BianchiValidation.FirstBianchi`)
 as a cyclic sum, and `frame_jacobi` (Eq 15, Mathlib `lie_jacobi`) is the frame bracket's cyclic
 double-bracket Jacobi — the same `cyclicSum`-vanishing structure. `jacobi_ricci_bianchi_correspondence`
 assembles the two faces.

Proven algebraically: the rigid-tetrad antisymmetry determines the connection from the
commutation coefficients (the Koszul formula), and the first Bianchi identity and the frame Jacobi identity
share one cyclic-sum-vanishing structure. The frame derivatives `∂ₐ`, the Riemann tensor built from `γᶜ_ab`
(Eq 13), and the paper's main integrability theorem (the field equations as integrability conditions of the
JRB system) need frame-derivative PDE machinery not modelled here; this file isolates the algebraic skeleton.

## References

* **Primary source.** N. Van den Bergh, *On the relation between the Einstein field equations and the
 Jacobi–Ricci–Bianchi system*, Class. Quantum Grav. **31** (2014) 145007,
 doi:10.1088/0264-9381/31/14/145007; arXiv:1302.6448v3 [gr-qc] (10 June 2013); PACS 04.20.Jb. — §2
 (Tetrad formalisms), Eqs (6)–(7) rigid orthonormal tetrad (p. 3), (8)–(10) commutation coefficients (p. 3),
 (11) Koszul/Levi-Civita formula (p. 3), (14) first Bianchi `R_{a[bcd]}=0` (p. 3), (15) frame Jacobi
 `[∂_{[a},[∂_b,∂_{c]}]]=0` (p. 3), (16) its commutation-coefficient form (p. 3).
* `Physlib` (`LeviCivita.BianchiValidation.FirstBianchi`); Mathlib (`lie_jacobi`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation (FirstBianchi)

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad

/-! ## §A — the rigid orthonormal-tetrad connection algebra -/

/-- A **rigid orthonormal-tetrad connection**: the (fully lowered) connection coefficients `Γ_abc = Γ_{ab}c`
with the orthonormal/metric-compatibility antisymmetry `Γ_{(ab)c} = 0`, i.e. `Γ_abc = −Γ_bac` (Eq 7 — the
basis is rigid, `dg_ab = 0`). The third index is the form index. -/
structure TetradConnection (ι : Type*) where
  /-- The connection coefficients `Γ_abc` (antisymmetric in the first two, lowered, indices). -/
  Γ : ι → ι → ι → ℝ
  /-- Rigid orthonormal tetrad: `Γ_{(ab)c} = 0`, i.e. `Γ_abc = −Γ_bac` (Eq 7). -/
  rigid : ∀ a b c, Γ a b c = - Γ b a c

variable {ι : Type*} (T : TetradConnection ι)

/-- The **commutation coefficients** `γ_abc = 2Γ_{a[cb]} = Γ_acb − Γ_abc` of the tetrad — the torsion-free
relation between connection and frame bracket `[∂ₐ,∂_b] = γᶜ_ab ∂_c` (Eq 10). -/
def TetradConnection.commCoeff (a b c : ι) : ℝ := T.Γ a c b - T.Γ a b c

/-- **[Commutation coefficients are antisymmetric in the lower pair]** `γ_abc = −γ_acb` — the frame bracket
is antisymmetric, `[∂_b,∂_c] = −[∂_c,∂_b]` (Eq 8). -/
theorem TetradConnection.commCoeff_antisymm (a b c : ι) :
    T.commCoeff a b c = - T.commCoeff a c b := by
  simp only [TetradConnection.commCoeff]; ring

/-- **[The Koszul / Levi-Civita formula for an orthonormal tetrad — arXiv:1302.6448v3, Eq (11), p. 3]**
`Γ_cab = ½(γ_bca + γ_acb − γ_cab)`: for a rigid orthonormal tetrad (Eqs (6)–(7), p. 3) the connection is
completely determined by the commutation coefficients `γ` (Eq (10), p. 3). -/
theorem TetradConnection.koszul (a b c : ι) :
    T.Γ c a b = (T.commCoeff b c a + T.commCoeff a c b - T.commCoeff c a b) / 2 := by
  simp only [TetradConnection.commCoeff]
  have h1 := T.rigid b a c
  have h2 := T.rigid b c a
  have h3 := T.rigid a c b
  linarith

/-! ## §B — the first Bianchi identity is the frame Jacobi identity -/

/-- The **cyclic sum** `f(a,b,c) + f(b,c,a) + f(c,a,b)` — the single operator behind both the first Bianchi
identity and the Jacobi identity. -/
def cyclicSum {α : Type*} {M : Type*} [AddCommMonoid M] (f : α → α → α → M) (a b c : α) : M :=
  f a b c + f b c a + f c a b

/-- **[The first Bianchi identity is a cyclic sum]** `R_{a[bcd]} = 0` (Eq 14) is exactly the vanishing of the
cyclic sum of the Riemann symbols over the last three indices. -/
theorem firstBianchi_iff_cyclicSum {κ : Type*} [Fintype κ] (R : κ → κ → κ → κ → ℝ) :
    FirstBianchi R ↔ ∀ a b c d, cyclicSum (R a) b c d = 0 :=
  Iff.rfl

/-- **[The frame Jacobi identity — arXiv:1302.6448v3, Eq (15), p. 3]** the frame vector fields (elements of
any Lie ring) obey the cyclic double-bracket identity `⁅x,⁅y,z⁆⁆ + ⁅y,⁅z,x⁆⁆ + ⁅z,⁅x,y⁆⁆ = 0` — equivalent
to the first Bianchi identity (Eq (14), p. 3) and its commutation-coefficient form (Eq (16), p. 3); the
integrability condition whose curvature face is the first Bianchi identity. -/
theorem frame_jacobi {L : Type*} [LieRing L] (x y z : L) :
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
  lie_jacobi x y z

/-- **[The Jacobi–Ricci–Bianchi correspondence]** the first Bianchi identity (Eq 14) and the frame Jacobi
identity (Eq 15) are the same cyclic-sum-vanishing structure: `FirstBianchi R` is the cyclic sum of the
Riemann symbols, while the frame bracket satisfies the cyclic double-bracket Jacobi. -/
theorem jacobi_ricci_bianchi_correspondence {κ : Type*} [Fintype κ] (R : κ → κ → κ → κ → ℝ)
    {L : Type*} [LieRing L] :
    (FirstBianchi R ↔ ∀ a b c d, cyclicSum (R a) b c d = 0)
      ∧ (∀ x y z : L, ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0) :=
  ⟨firstBianchi_iff_cyclicSum R, fun x y z => frame_jacobi x y z⟩

end Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.StachelSuperpotentialEinsteinBits
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita

/-!
# Papapetrou–Stachel: torsion vanishes from the field equations, and the tetrad connection

Papapetrou and Stachel (Gen. Relativ. Gravit. 9 (1978) 1075) modify the Palatini Lagrangian by
subtracting `g̃^{λμ} Γ_{λ;μ}` (the covariant divergence of the torsion trace vector), obtaining
`ℒ = g̃^{λμ}(R_{λμ} − Γ_{λ;μ})` (Eq. 2.7). The remarkable property: with only the assumption that the
**metric** is symmetric, varying the connection makes the **torsion vanish as a field equation**,
rather than by fiat. Varying the antisymmetric part of the connection gives (Eq. 2.11) a tensor

  `T_{μνλ} = g_{μμ'} Γ^{μ'}_{[νλ]}`   symmetric in `μ,λ` and antisymmetric in `ν,λ`,

and such a tensor must vanish (Eq. 2.12): `Γ^{μ}_{[νλ]} = 0`. So the affine connection is symmetric
— the Levi-Civita connection — and the field equations reduce to the vacuum Einstein equations
`R_{λμ} = 0` (Eq. 2.14). This is the symmetric-connection premise under which
`StachelSuperpotentialEinsteinBits.stachelSuperpotential_isRiemann` holds.

Section 3 transcribes this to a tetrad `z_m^μ`. The anholonomy object `Ω^l_{mn}` is antisymmetric;
the anholonomic connection coefficients `γ^l_{mn}` (a.c.c.) split as `γ = γ̊ + S` (Eq. 3.7) with the
symmetrized `γ̊^l_{mn} = γ^l_{(mn)} − Ω^l_{mn}` (Eq. 3.9), and the metric-compatible symmetric case
gives the tetrad Ricci-rotation formula (Eq. 5.10): the symmetrized a.c.c. is the **Christoffel first
kind of the tetrad metric plus the anholonomy** — `CliffordFiberLeviCivita.christoffelFirstKind`
extended by `Ω`. In a holonomic (coordinate) basis `Ω = 0` and `γ̊` is exactly the Christoffel first
kind, recovering the coordinate Levi-Civita connection.

* **§A** the torsion vanishes: a rank-three tensor symmetric in the outer pair and antisymmetric in
  the last pair is zero (Eqs. 2.11–2.12) — the connection is symmetric.
* **§B** the a.c.c. decomposition `γ̊ = γ_{(mn)} − Ω` (Eqs. 3.5, 3.7, 3.9).
* **§C** for a constant tetrad metric the Ricci-rotation coefficients are antisymmetric in the metric
  pair (Eq. 3.14b).
* **§D** the symmetrized a.c.c. is `christoffelFirstKind` of the tetrad metric plus anholonomy
  (Eq. 5.10), reducing to `christoffelFirstKind` in a holonomic basis.

## References

* A. Papapetrou, J. Stachel, *A new Lagrangian for the vacuum Einstein equations and its tetrad form*,
  Gen. Relativ. Gravit. 9 (1978) 1075 — Eqs. 2.7–2.14, 3.2–3.14, 5.10.
* J. A. Schouten, *Ricci-Calculus* (Springer, 1954) — the anholonomic connection coefficients.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.PapapetrouStachelTorsionTetrad

@[expose] public section

/-! ## A. The torsion vanishes as a field equation -/

/-- **[A tensor symmetric in the outer pair and antisymmetric in the last pair vanishes, Eqs. 2.11–2.12]**
If `T a b c = T c b a` (symmetric under exchange of the first and third slots) and `T a b c = −T a c b`
(antisymmetric under exchange of the second and third slots), then `T ≡ 0`. This is the Papapetrou–Stachel
mechanism: varying the antisymmetric part of the connection makes the lowered torsion
`T_{μνλ} = g_{μμ'} Γ^{μ'}_{[νλ]}` symmetric in `μ,λ` and antisymmetric in `ν,λ`, forcing it to zero. -/
theorem symm_outer_antisymm_last_vanishes {ι : Type*} (T : ι → ι → ι → ℝ)
    (hsym : ∀ a b c, T a b c = T c b a) (hanti : ∀ a b c, T a b c = -T a c b) (a b c : ι) :
    T a b c = 0 := by
  have e1 := hsym a b c
  have e2 := hanti c b a
  have e3 := hsym c a b
  have e4 := hanti b a c
  have e5 := hsym b c a
  have e6 := hanti a b c
  linarith

/-- **[The Papapetrou–Stachel torsion vanishes] `Γ^{μ}_{[νλ]} = 0` (Eq. 2.12).** With the metric
symmetric, the field equation from varying the antisymmetric connection (Eq. 2.11) makes the lowered
torsion symmetric in the outer pair and antisymmetric in the last pair, so the torsion vanishes and the
connection is symmetric — the premise for the Levi-Civita connection and for
`StachelSuperpotentialEinsteinBits.stachelSuperpotential_isRiemann`. -/
theorem torsion_vanishes {ι : Type*} (torsion : ι → ι → ι → ℝ)
    (hsym : ∀ μ ν κ, torsion μ ν κ = torsion κ ν μ)
    (hanti : ∀ μ ν κ, torsion μ ν κ = -torsion μ κ ν) (μ ν κ : ι) :
    torsion μ ν κ = 0 :=
  symm_outer_antisymm_last_vanishes torsion hsym hanti μ ν κ

/-! ## B. The anholonomic connection coefficient decomposition -/

/-- **[The symmetrized a.c.c. is the symmetric part minus the anholonomy, Eq. 3.9]**
`γ̊^l_{mn} = γ^l_{(mn)} − Ω^l_{mn}`. The anholonomy `Ω` and torsion projection `S` are antisymmetric in
`m,n`; from the antisymmetric-part relation `γ^l_{[mn]} = S^l_{mn} − Ω^l_{mn}` (Eq. 3.5), the
symmetrized coefficient `γ̊ = γ − S` (Eq. 3.7) equals the symmetric part of `γ` minus the anholonomy. -/
theorem symmetrizedAcc_eq_symPart_sub_anholonomy {ι : Type*}
    (γ Ω S : ι → ι → ι → ℝ)
    (hacc : ∀ l m n, (γ l m n - γ l n m) / 2 = S l m n - Ω l m n)
    (l m n : ι) :
    γ l m n - S l m n = (γ l m n + γ l n m) / 2 - Ω l m n := by
  have h := hacc l m n
  linarith

/-! ## C. Ricci-rotation coefficients of a constant tetrad metric are antisymmetric -/

/-- **[Constant tetrad metric ⟹ antisymmetric rotation coefficients, Eq. 3.14b]** metric compatibility
of a symmetric tetrad metric gives `η_{lm,n} = γ_{lnm} + γ_{mnl}` (`hcompat`, `dη l m n = η_{lm,n}`).
For a constant tetrad metric — an orthonormal (Minkowski) tetrad, `η_{lm,n} = 0` — this forces
`γ_{lnm} = −γ_{mnl}`: the Ricci-rotation coefficients are antisymmetric in the metric-index pair. -/
theorem rotationCoeff_antisymm_of_const_metric {ι : Type*} (dη γ : ι → ι → ι → ℝ)
    (hcompat : ∀ l m n, dη l m n = γ l n m + γ m n l)
    (hconst : ∀ l m n, dη l m n = 0) (l m n : ι) :
    γ l n m = -γ m n l := by
  have h := hcompat l m n
  rw [hconst l m n] at h
  linarith

/-! ## D. The symmetrized a.c.c. is `christoffelFirstKind` plus anholonomy -/

/-- **The Papapetrou–Stachel symmetrized a.c.c., Eq. 5.10.**
`γ̊_{lmn} = ½(η_{lm,n} + η_{ln,m} − η_{mn,l}) + Ω_{mnl} + Ω_{nml} + Ω_{lmn}`, with `dη n l m = η_{lm,n}`
the tetrad-metric derivative and `Ω` the (lowered) anholonomy. -/
noncomputable def symmetrizedAcc {d : ℕ} (dη Ω : Fin d → Fin d → Fin d → ℝ) (l m n : Fin d) : ℝ :=
  (dη n l m + dη m l n - dη l m n) / 2 + Ω m n l + Ω n m l + Ω l m n

/-- **[The symmetrized a.c.c. is the Christoffel first kind plus anholonomy, Eq. 5.10]** for a
symmetric tetrad metric (`dη a b c = dη a c b`), the first three terms of `symmetrizedAcc` are exactly
`CliffordFiberLeviCivita.christoffelFirstKind` of the tetrad metric, so
`γ̊_{lmn} = christoffelFirstKind dη l n m + Ω_{mnl} + Ω_{nml} + Ω_{lmn}`. The tetrad connection is the
coordinate Christoffel formula corrected by the anholonomy. -/
theorem symmetrizedAcc_eq_christoffelFirstKind_add_anholonomy {d : ℕ}
    (dη Ω : Fin d → Fin d → Fin d → ℝ) (hsym : ∀ a b c, dη a b c = dη a c b) (l m n : Fin d) :
    symmetrizedAcc dη Ω l m n
      = christoffelFirstKind dη l n m + (Ω m n l + Ω n m l + Ω l m n) := by
  simp only [symmetrizedAcc, christoffelFirstKind]
  rw [hsym n l m, hsym m l n, hsym l m n]
  ring

/-- **[Holonomic limit: the a.c.c. is the Christoffel first kind, Eq. 5.10 with `Ω = 0`]** in a
coordinate (holonomic) basis the anholonomy vanishes and the symmetrized a.c.c. is exactly the
Christoffel first kind of the tetrad metric — the tetrad connection reduces to the coordinate
Levi-Civita connection (`Curvature.LeviCivitaFromMetric`). -/
theorem symmetrizedAcc_holonomic {d : ℕ} (dη : Fin d → Fin d → Fin d → ℝ)
    (hsym : ∀ a b c, dη a b c = dη a c b) (l m n : Fin d) :
    symmetrizedAcc dη 0 l m n = christoffelFirstKind dη l n m := by
  rw [symmetrizedAcc_eq_christoffelFirstKind_add_anholonomy dη 0 hsym]
  simp

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.PapapetrouStachelTorsionTetrad

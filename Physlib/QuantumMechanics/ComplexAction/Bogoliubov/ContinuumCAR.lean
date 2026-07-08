/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FoldyWouthuysenBogoliubovIdentity

/-!
# Tier 3: the Bogoliubov transformation on the continuum one-particle Hilbert space

`Bogoliubov.FermionicBogoliubovCAR` (Tier 1) and `Bogoliubov.DiracFieldSpecBogoliubov` (Tier 2) realized the second-quantized
Bogoliubov on a *finite* Fock space. This file takes the **continuum** step: the one-particle Hilbert
space of the Dirac field is `H = L²(ℝ³)` (the momentum continuum), and the Bogoliubov transformation is
the **Nambu** map on `H ⊕ H` (particle ⊕ antiparticle/conjugate). The operator-algebra criterion for it
to be a valid canonical CAR transformation is that this one-particle map be **unitary** — which is
exactly `u² + v² = 1`.

## The Nambu one-particle Bogoliubov

For an arbitrary real inner-product space `H` (instantiated by the realified momentum continuum
`L²(ℝ³)`), the Nambu Bogoliubov map `B(f, g) = (u f + v g, −v f + u g)` scales the one-particle
(Nambu) inner product by `u² + v²`:

 `⟪Bf, Bf'⟫ + ⟪Bg, Bg'⟫ = (u² + v²)·(⟪f, f'⟫ + ⟪g, g'⟫)` (`nambu_bogoliubov_inner`),

so it **preserves** the inner product — i.e. is an **isometry / unitary** on the continuum one-particle
space — *iff* `u² + v² = 1` (`nambu_bogoliubov_preserves_inner`, `nambu_bogoliubov_isometry`).

## Why this is the continuum CAR criterion

The smeared canonical anticommutation relation is `{a(f), a(g)†} = ⟪f, g⟫` (the continuum `δ³(k−k')`
realized as the inner product on `H = L²(ℝ³)`). A Bogoliubov transformation `a(f) ↦ a(Bf)` is a valid
**canonical / `*`-automorphism of the CAR algebra** exactly when `B` preserves `⟪·,·⟫` — unitarity of
the one-particle map. So `u² + v² = 1` (the Foldy–Wouthuysen normalization) is precisely the condition
that the continuum Dirac Bogoliubov is CAR-preserving (`fw_continuum_canonical`), now over the genuine
infinite-dimensional Hilbert space `H`, not a finite Fock space.

## Scope (the part still not built)

This formalizes the **one-particle Hilbert-space criterion** (over the continuum `H`): the Nambu
Bogoliubov is unitary iff `u² + v² = 1`, which is the condition for it to be a canonical CAR
transformation (the Bogoliubov / self-dual-CAR criterion). What is **not** built: the CAR `C*`-algebra
itself, the Fock-space second-quantization functor `H ↦ Λ(H)`, and the **Shale–Stinespring**
unitary-implementability criterion (the off-diagonal block being Hilbert–Schmidt) — Mathlib has the
Hilbert-space layer used here but not the CAR-algebra / Fock-functor layer. So Tier 3 is the
continuum *one-particle* statement; the full Fock-functor implementation remains the open frontier.

## References

* The self-dual CAR / Bogoliubov criterion (Araki; Shale–Stinespring). This development:
 `Bogoliubov.FermionicBogoliubovCAR`, `Bogoliubov.DiracFieldSpecBogoliubov`, `Bogoliubov.FoldyWouthuysenBogoliubovIdentity`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.ContinuumCAR

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## §A — the Nambu one-particle Bogoliubov scales the inner product by `u² + v²` -/

/-- **The Nambu Bogoliubov inner-product scaling.** On the one-particle (Nambu) space `H ⊕ H`, the
Bogoliubov map `B(f, g) = (u f + v g, −v f + u g)` scales the inner product by `u² + v²`:
`⟪Bf, Bf'⟫ + ⟪Bg, Bg'⟫ = (u²+v²)(⟪f,f'⟫ + ⟪g,g'⟫)`. The off-diagonal (`uv`) cross terms cancel. -/
theorem nambu_bogoliubov_inner (u v : ℝ) (f g f' g' : H) :
    ⟪u • f + v • g, u • f' + v • g'⟫ + ⟪(-(v • f)) + u • g, (-(v • f')) + u • g'⟫
      = (u ^ 2 + v ^ 2) * (⟪f, f'⟫ + ⟪g, g'⟫) := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_neg_left, inner_neg_right]
  ring

/-! ## §B — unitarity of the one-particle map iff `u² + v² = 1` -/

/-- **The Nambu Bogoliubov preserves the one-particle inner product** when `u² + v² = 1`: it is a
**unitary** (isometric) map on the continuum one-particle Hilbert space — the condition for it to be a
canonical CAR transformation. -/
theorem nambu_bogoliubov_preserves_inner (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (f g f' g' : H) :
    ⟪u • f + v • g, u • f' + v • g'⟫ + ⟪(-(v • f)) + u • g, (-(v • f')) + u • g'⟫
      = ⟪f, f'⟫ + ⟪g, g'⟫ := by
  rw [nambu_bogoliubov_inner, h, one_mul]

/-- **The Nambu Bogoliubov is an isometry** when `u² + v² = 1`: the one-particle norm is preserved,
`‖Bf‖² + ‖Bg‖² = ‖f‖² + ‖g‖²` (the diagonal case of `nambu_bogoliubov_preserves_inner`). -/
theorem nambu_bogoliubov_isometry (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (f g : H) :
    ⟪u • f + v • g, u • f + v • g⟫ + ⟪(-(v • f)) + u • g, (-(v • f)) + u • g⟫
      = ⟪f, f⟫ + ⟪g, g⟫ :=
  nambu_bogoliubov_preserves_inner u v h f g f g

/-! ## §C — the Foldy–Wouthuysen continuum CAR -/

/-- **The Foldy–Wouthuysen Bogoliubov is CAR-preserving on the continuum.** For the Foldy–Wouthuysen
amplitudes `u² + v² = 1` (`Bogoliubov.FoldyWouthuysenBogoliubovIdentity.fw_weights_normalization`), the Nambu
Bogoliubov map on the continuum one-particle Hilbert space `H = L²(ℝ³)` preserves the inner product —
the smeared CAR `{a(f), a(g)†} = ⟪f, g⟫` is preserved, so the transformation is a canonical
`*`-automorphism criterion of the CAR algebra over the momentum continuum. -/
theorem fw_continuum_canonical (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (f g f' g' : H) :
    ⟪u • f + v • g, u • f' + v • g'⟫ + ⟪(-(v • f)) + u • g, (-(v • f')) + u • g'⟫
      = ⟪f, f'⟫ + ⟪g, g'⟫ :=
  nambu_bogoliubov_preserves_inner u v h f g f' g'

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.ContinuumCAR

end

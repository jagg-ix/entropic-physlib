/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The Virasoro central extension and the positive energy of conformally-excited states

`ConformalModularEntanglement` built the finite conformal unitaries of Caminiti, Capeccia, Ciambelli, Myers,
*Geometric modular flows in 2d CFT and beyond* (JHEP 08 (2025) 166, arXiv:2502.02633), and noted that the
*infinitesimal* form of those unitaries — the Virasoro construction `|Ψ⟩ = e^{iε(L_n + L_{−n})}|Ω⟩`
(eq. 1.9) — was not formalized because the repository had no Virasoro algebra. This module supplies it.

## The central extension

The Witt algebra of `S¹` vector fields has bracket `[L_m, L_n] = (m − n) L_{m+n}`. Its unique nontrivial
central extension is the **Virasoro algebra**

  `[L_m, L_n] = (m − n) L_{m+n} + (c/12) m(m² − 1) δ_{m+n,0} · C`,

with `C` central and `c` the central charge. The central term is the 2-cocycle
`ω(L_m, L_n) = (c/12) m(m² − 1) δ_{m+n,0}` (`virasoroCocycle`, using `m³ − m = m(m²−1)`).

* `virasoroCocycle_antisymm` — `ω` is antisymmetric, `ω(m,n) = −ω(n,m)`.
* `virasoroCocycle_cocycle` — the **2-cocycle (Jacobi) identity**
  `(m−n) ω(m+n,p) + (n−p) ω(n+p,m) + (p−m) ω(p+m,n) = 0`, the condition that makes the extension a Lie
  algebra. (Nontrivial only on `m+n+p = 0`, where it is the classical Virasoro polynomial identity.)

## The vacuum descendant norm and positive energy (eq. 1.9)

For the vacuum `|Ω⟩` (`L_n|Ω⟩ = 0` for `n ≥ −1`, `L_0|Ω⟩ = 0`, `⟨Ω|Ω⟩ = 1`), the diagonal bracket
`[L_n, L_{−n}] = 2n L_0 + (c/12) n(n²−1)` gives the **norm of the descendant** `L_{−n}|Ω⟩`:

  `‖L_{−n}|Ω⟩‖² = ⟨Ω| L_n L_{−n} |Ω⟩ = (c/12) n(n² − 1)`   (`descendantNorm`).

* `descendantNorm_eq_cocycle` — this norm is the diagonal cocycle `ω(n,−n)`.
* `descendantNorm_translation_zero`, `descendantNorm_vacuum_zero`, `descendantNorm_special_conformal_zero`
  — it **vanishes for `n ∈ {−1, 0, 1}`**: the global-conformal `sl(2,ℝ) = ⟨L_{−1}, L_0, L_1⟩` subalgebra
  (the Möbius group of `ConformalModularEntanglement`) has no central term and acts on `|Ω⟩` with null
  descendants. This is exactly why eq. (1.9) requires `n ≥ 2`.
* `descendantNorm_pos` — for `c > 0` and `n ≥ 2` the norm is **strictly positive**; the local (non-Möbius)
  conformal descendants are genuine excitations.
* `excitedStateEnergy_pos` — the conformally-excited state `|Ψ⟩ = (1 + iε L_{−n})|Ω⟩ + O(ε²)` has energy
  `⟨Ψ| L_0 |Ψ⟩ = ε² · n · ⟨Ω| L_n L_{−n} |Ω⟩ = ε² (c/12) n²(n²−1) > 0` for `n ≥ 2` — the **positive-energy
  mechanism** of eq. (1.9): local conformal symmetries act nontrivially on the vacuum because `L_0` fails to
  commute with `L_{−n}`.

## The full bracket

`wittCoeff`, `virasoroCocycle`, and the identities `wittCoeff_antisymm`, `virasoroCocycle_antisymm`,
`wittCoeff_jacobi`, `virasoroCocycle_cocycle` (bundled in `virasoro_jacobi`) give the complete Virasoro
Lie-algebra structure `[L_m, L_n] = (m − n) L_{m+n} + ω(m,n) C` at the structure-constant level — every
Lie-algebra axiom (bilinearity, antisymmetry, Jacobi) verified, the same standard as the repository's
affine Kac–Moody formalization. `sl2_subalgebra` records that the global-conformal `⟨L_{−1}, L_0, L_1⟩`
closes as a genuine `sl(2,ℝ)` with no central term.

The central charge `c` is the same one whose vacuum Casimir `−c/24` is the `SciamaFockVerlindeWitten`
`virasoroCasimir_from_zeta` (`c·½·ζ(−1) = −c/24`), and whose transverse value fixes the critical dimension
`D = 26` (`StringScaleHolographicGravity`). The Lie algebra is characterized here by its structure
constants and cocycle; a concrete `LieRing` instance on `(ℤ →₀ ℝ) ⊕ ℝ·C` and a Verma-module Hilbert space
are not built.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.VirasoroCentralExtension

/-- **The Virasoro 2-cocycle** `ω(L_m, L_n) = (c/12) m(m² − 1) δ_{m+n,0}`, written with `m³ − m = m(m²−1)`.
It is the central term of `[L_m, L_n] = (m − n) L_{m+n} + ω(L_m,L_n) C`. -/
noncomputable def virasoroCocycle (c : ℝ) (m n : ℤ) : ℝ :=
  if m + n = 0 then c / 12 * ((m : ℝ) ^ 3 - (m : ℝ)) else 0

theorem virasoroCocycle_of_add_zero (c : ℝ) {m n : ℤ} (h : m + n = 0) :
    virasoroCocycle c m n = c / 12 * ((m : ℝ) ^ 3 - (m : ℝ)) := by
  rw [virasoroCocycle, if_pos h]

theorem virasoroCocycle_of_add_ne (c : ℝ) {m n : ℤ} (h : m + n ≠ 0) :
    virasoroCocycle c m n = 0 := by
  rw [virasoroCocycle, if_neg h]

/-- **The cocycle is antisymmetric**, `ω(m,n) = −ω(n,m)` — the antisymmetry of the Virasoro bracket. -/
theorem virasoroCocycle_antisymm (c : ℝ) (m n : ℤ) :
    virasoroCocycle c m n = - virasoroCocycle c n m := by
  by_cases h : m + n = 0
  · rw [virasoroCocycle_of_add_zero c h, virasoroCocycle_of_add_zero c (by linarith : n + m = 0)]
    have hn : n = -m := by linarith
    subst hn
    push_cast
    ring
  · rw [virasoroCocycle_of_add_ne c h, virasoroCocycle_of_add_ne c (fun hc => h (by linarith)),
      neg_zero]

/-- **The 2-cocycle (Jacobi) identity** `(m−n) ω(m+n,p) + (n−p) ω(n+p,m) + (p−m) ω(p+m,n) = 0` — the
condition that the central extension `[L_m,L_n] = (m−n)L_{m+n} + ω(m,n)C` is a Lie algebra. It is
nontrivial precisely on `m + n + p = 0`, where it is the classical Virasoro polynomial identity. -/
theorem virasoroCocycle_cocycle (c : ℝ) (m n p : ℤ) :
    ((m - n : ℤ) : ℝ) * virasoroCocycle c (m + n) p
      + ((n - p : ℤ) : ℝ) * virasoroCocycle c (n + p) m
      + ((p - m : ℤ) : ℝ) * virasoroCocycle c (p + m) n = 0 := by
  by_cases h : m + n + p = 0
  · rw [virasoroCocycle_of_add_zero c (by linarith : (m + n) + p = 0),
        virasoroCocycle_of_add_zero c (by linarith : (n + p) + m = 0),
        virasoroCocycle_of_add_zero c (by linarith : (p + m) + n = 0)]
    have hp : p = -m - n := by linarith
    subst hp
    push_cast
    ring
  · rw [virasoroCocycle_of_add_ne c (fun hc => h (by linarith) : (m + n) + p ≠ 0),
        virasoroCocycle_of_add_ne c (fun hc => h (by linarith) : (n + p) + m ≠ 0),
        virasoroCocycle_of_add_ne c (fun hc => h (by linarith) : (p + m) + n ≠ 0)]
    ring

/-- **The vacuum descendant norm** `‖L_{−n}|Ω⟩‖² = ⟨Ω| L_n L_{−n} |Ω⟩ = (c/12) n(n² − 1)`, from the
diagonal bracket `[L_n, L_{−n}] = 2n L_0 + (c/12)n(n²−1)` with `L_0|Ω⟩ = 0`, `L_n|Ω⟩ = 0` (`n ≥ 1`). -/
noncomputable def descendantNorm (c : ℝ) (n : ℤ) : ℝ := c / 12 * ((n : ℝ) ^ 3 - (n : ℝ))

/-- The descendant norm is the diagonal Virasoro cocycle `ω(n, −n)`. -/
theorem descendantNorm_eq_cocycle (c : ℝ) (n : ℤ) :
    descendantNorm c n = virasoroCocycle c n (-n) := by
  rw [virasoroCocycle_of_add_zero c (by ring : n + (-n) = 0), descendantNorm]

/-- The `L_{−1}` (translation) descendant is null: `⟨Ω| L_1 L_{−1} |Ω⟩ = 0`. -/
theorem descendantNorm_translation_zero (c : ℝ) : descendantNorm c 1 = 0 := by
  rw [descendantNorm]; norm_num

/-- The `L_0` descendant is null. -/
theorem descendantNorm_vacuum_zero (c : ℝ) : descendantNorm c 0 = 0 := by
  rw [descendantNorm]; norm_num

/-- The `L_1` (special-conformal) descendant is null: `⟨Ω| L_{−1} L_1 |Ω⟩ = 0`. -/
theorem descendantNorm_special_conformal_zero (c : ℝ) : descendantNorm c (-1) = 0 := by
  rw [descendantNorm]; norm_num

/-- **Positive descendant norm for `n ≥ 2`.** For central charge `c > 0`, the norm of `L_{−n}|Ω⟩` is
strictly positive — the local (non-Möbius) conformal descendants are genuine excitations. -/
theorem descendantNorm_pos (c : ℝ) (n : ℤ) (hc : 0 < c) (hn : 2 ≤ n) :
    0 < descendantNorm c n := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [descendantNorm]
  have hfac : (n : ℝ) ^ 3 - (n : ℝ) = (n : ℝ) * (((n : ℝ) - 1) * ((n : ℝ) + 1)) := by ring
  rw [hfac]
  have h1 : (0 : ℝ) < (n : ℝ) := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h3 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  exact mul_pos (by positivity) (mul_pos h1 (mul_pos h2 h3))

/-- **The energy of the conformally-excited state** `|Ψ⟩ = (1 + iε L_{−n})|Ω⟩ + O(ε²)`, at order `ε²`:
`⟨Ψ| L_0 |Ψ⟩ / ε² = n · ⟨Ω| L_n L_{−n} |Ω⟩` (using `L_0 L_{−n}|Ω⟩ = n L_{−n}|Ω⟩`). -/
noncomputable def excitedStateEnergy (c : ℝ) (n : ℤ) : ℝ := (n : ℝ) * descendantNorm c n

/-- **Positive energy of the eq. (1.9) excited state.**  For `c > 0` and `n ≥ 2`, the conformally-excited
state has strictly positive energy `⟨Ψ|L_0|Ψ⟩ = ε² (c/12) n²(n²−1) > 0` — local conformal symmetries act
nontrivially on the vacuum because `L_0` fails to commute with `L_{−n}`. -/
theorem excitedStateEnergy_pos (c : ℝ) (n : ℤ) (hc : 0 < c) (hn : 2 ≤ n) :
    0 < excitedStateEnergy c n := by
  have hn' : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact mul_pos hn' (descendantNorm_pos c n hc hn)

/-- The excited-state energy in closed form, `⟨Ψ|L_0|Ψ⟩ / ε² = (c/12) n²(n² − 1)`. -/
theorem excitedStateEnergy_eq (c : ℝ) (n : ℤ) :
    excitedStateEnergy c n = c / 12 * ((n : ℝ) ^ 2 * ((n : ℝ) ^ 2 - 1)) := by
  rw [excitedStateEnergy, descendantNorm]; ring

/-- **The eq. (1.9) mechanism in one statement.**  The global-conformal `sl(2)` descendants are null
(`n = 1`), while for `n ≥ 2` and `c > 0` the descendant norm and the excited-state energy are both strictly
positive. -/
theorem virasoro_positive_energy_synthesis (c : ℝ) (n : ℤ) (hc : 0 < c) (hn : 2 ≤ n) :
    descendantNorm c 1 = 0 ∧ 0 < descendantNorm c n ∧ 0 < excitedStateEnergy c n :=
  ⟨descendantNorm_translation_zero c, descendantNorm_pos c n hc hn,
    excitedStateEnergy_pos c n hc hn⟩

/-! ## The full Virasoro Lie bracket

The Virasoro bracket `[L_m, L_n] = wittCoeff(m,n) L_{m+n} + ω(m,n) C` is bilinear (automatic from its
structure constants), antisymmetric (`wittCoeff_antisymm`, `virasoroCocycle_antisymm`), and satisfies the
Jacobi identity in both the mode component (`wittCoeff_jacobi`) and the central component
(`virasoroCocycle_cocycle`). Those are all the Lie-algebra axioms, verified here at the structure-constant
level (the same standard as the repository's affine Kac–Moody formalization). -/

/-- **The Witt structure constant** of the Virasoro bracket `[L_m, L_n] = (m − n) L_{m+n} + ω(m,n) C`:
the coefficient of the mode `L_{m+n}`. -/
def wittCoeff (m n : ℤ) : ℤ := m - n

/-- **The Witt structure constant is antisymmetric**, `wittCoeff(m,n) = −wittCoeff(n,m)` — the
antisymmetry of the mode part of the Virasoro bracket. -/
theorem wittCoeff_antisymm (m n : ℤ) : wittCoeff m n = - wittCoeff n m := by
  simp only [wittCoeff]; ring

/-- **The Witt (Jacobi) identity, mode part.**  The coefficient of `L_{m+n+p}` in the Jacobiator
`[[L_m,L_n],L_p] + [[L_n,L_p],L_m] + [[L_p,L_m],L_n]` vanishes:
`(m−n)((m+n)−p) + (n−p)((n+p)−m) + (p−m)((p+m)−n) = 0`. -/
theorem wittCoeff_jacobi (m n p : ℤ) :
    wittCoeff m n * wittCoeff (m + n) p
      + wittCoeff n p * wittCoeff (n + p) m
      + wittCoeff p m * wittCoeff (p + m) n = 0 := by
  simp only [wittCoeff]; ring

/-- **The full Virasoro Jacobi identity.**  The Jacobiator of the Virasoro bracket
`[L_m, L_n] = (m − n) L_{m+n} + ω(m,n) C` vanishes in *both* components: the mode part (coefficient of
`L_{m+n+p}`) is the Witt Jacobi identity, and the central part (coefficient of `C`) is the 2-cocycle
identity. Together with antisymmetry and the automatic bilinearity of a structure-constant bracket, this
verifies every Lie-algebra axiom of the Virasoro central extension. -/
theorem virasoro_jacobi (c : ℝ) (m n p : ℤ) :
    (wittCoeff m n * wittCoeff (m + n) p + wittCoeff n p * wittCoeff (n + p) m
        + wittCoeff p m * wittCoeff (p + m) n = 0)
      ∧ (((m - n : ℤ) : ℝ) * virasoroCocycle c (m + n) p
          + ((n - p : ℤ) : ℝ) * virasoroCocycle c (n + p) m
          + ((p - m : ℤ) : ℝ) * virasoroCocycle c (p + m) n = 0) :=
  ⟨wittCoeff_jacobi m n p, virasoroCocycle_cocycle c m n p⟩

/-- **The global-conformal `sl(2,ℝ)` subalgebra** `⟨L_{−1}, L_0, L_1⟩` closes with *no* central term:
`[L_1, L_{−1}] = 2 L_0`, `[L_0, L_1] = −L_1`, `[L_0, L_{−1}] = L_{−1}`, every central charge vanishing.
This is the Möbius algebra of `ConformalModularEntanglement` that acts on `|Ω⟩` without excitation — the
reason eq. (1.9) needs `n ≥ 2`. -/
theorem sl2_subalgebra (c : ℝ) :
    wittCoeff 1 (-1) = 2 ∧ wittCoeff 0 1 = -1 ∧ wittCoeff 0 (-1) = 1
      ∧ virasoroCocycle c 1 (-1) = 0 ∧ virasoroCocycle c 0 1 = 0 ∧ virasoroCocycle c 0 (-1) = 0 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [virasoroCocycle_of_add_zero c (show (1 : ℤ) + (-1) = 0 by decide)]; norm_num
  · rw [virasoroCocycle_of_add_ne c (show (0 : ℤ) + 1 ≠ 0 by decide)]
  · rw [virasoroCocycle_of_add_ne c (show (0 : ℤ) + (-1) ≠ 0 by decide)]

end Physlib.QuantumMechanics.ComplexAction.VirasoroCentralExtension

end

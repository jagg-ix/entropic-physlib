/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift

/-!
# The Lamb shift is the density at the origin: why it is an S-state, `1/n³` effect

Grounds the **Bethe Lamb shift** (`Electromagnetic.CovariantMaxwellLambShift.betheLambShift`, the `α⁵/n³` radiative
splitting of the `2S₁⁄₂`–`2P₁⁄₂` hydrogen levels) in its physical origin — the **electron probability
density at the nucleus** `|ψ_{nS}(0)|²`.

In the Bethe/Welton picture the leading self-energy shift of a level is proportional to `⟨∇²V⟩`, and for
the Coulomb potential `∇²(1/r) = −4π δ³(r)`, so the shift is proportional to the density at the origin
`|ψ(0)|²`. For hydrogen,

  `|ψ_{nS}(0)|² = Z³ / (π n³ a₀³)`   (`sStateDensityAtOrigin`),

which is **nonzero only for `S` states** (`l = 0`): for `l ≥ 1` the wavefunction vanishes at the origin
(`densityAtOrigin_eq_zero_of_l_pos`). This is the exact reason the Lamb shift acts only on the `l = 0`
state (the `lambTerm`'s `if l = 0` selection) and scales as `1/n³`:

  the Bethe Lamb shift is **proportional to the density at the origin** across the principal quantum
  number `n` — `ΔE_n / ΔE_m = |ψ_{nS}(0)|² / |ψ_{mS}(0)|² = (m/n)³`
  (`betheLambShift_proportional_to_density`).

So the `2S₁⁄₂`–`2P₁⁄₂` splitting is the self-energy of the only state with support at the nucleus.

* **§A — the density at the origin** (`sStateDensityAtOrigin`, `sStateDensityAtOrigin_pos`,
  `densityAtOrigin`, `densityAtOrigin_eq_zero_of_l_pos`, `densityAtOrigin_s_state`).
* **§B — the Bethe Lamb shift is proportional to it** (`betheLambShift_proportional_to_density`).
* **§C — the assembly** (`lambShift_is_origin_density`).

## References

* H. A. Bethe, Phys. Rev. 72 (1947) 339; T. A. Welton, Phys. Rev. 74 (1948) 1157 (the `⟨∇²V⟩ ∝ |ψ(0)|²`
  picture). Hydrogen density at the nucleus `|ψ_{nS}(0)|² = Z³/(π n³ a₀³)`. Repo carrier:
  `Electromagnetic.CovariantMaxwellLambShift` (`betheLambShift`, `lambTerm`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LambShiftOriginDensity

open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift


/-- **The hydrogen `S`-state density at the nucleus** `|ψ_{nS}(0)|² = Z³ / (π n³ a₀³)` — the probability
density at the origin of the `nS` state (nuclear charge `Z`, Bohr radius `a₀`). -/
noncomputable def sStateDensityAtOrigin (n : ℕ) (Z a₀ : ℝ) : ℝ := Z ^ 3 / (Real.pi * (n : ℝ) ^ 3 * a₀ ^ 3)

/-- **The `S`-state density at the origin is positive** for `Z, a₀ > 0`, `n > 0`. -/
lemma sStateDensityAtOrigin_pos (n : ℕ) (Z a₀ : ℝ) (hZ : 0 < Z) (ha : 0 < a₀) (hn : 0 < n) :
    0 < sStateDensityAtOrigin n Z a₀ := by
  unfold sStateDensityAtOrigin
  have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  positivity

/-- **The density at the origin of an `(n, l)` state** — `|ψ_{nl}(0)|²`, equal to the `S`-state value for
`l = 0` and `0` for `l ≥ 1` (the wavefunction vanishes at the origin away from `S`). -/
noncomputable def densityAtOrigin (n l : ℕ) (Z a₀ : ℝ) : ℝ :=
  if l = 0 then sStateDensityAtOrigin n Z a₀ else 0

/-- **[Only `S` states reach the nucleus] `|ψ_{nl}(0)|² = 0` for `l ≥ 1`.** The exact reason the Lamb
shift acts only on the `l = 0` state. -/
lemma densityAtOrigin_eq_zero_of_l_pos (n l : ℕ) (Z a₀ : ℝ) (hl : 0 < l) :
    densityAtOrigin n l Z a₀ = 0 := by
  unfold densityAtOrigin; rw [if_neg hl.ne']

/-- **[`S`-state density] `|ψ_{n0}(0)|² = Z³/(π n³ a₀³)`.** -/
lemma densityAtOrigin_s_state (n : ℕ) (Z a₀ : ℝ) :
    densityAtOrigin n 0 Z a₀ = sStateDensityAtOrigin n Z a₀ := by
  unfold densityAtOrigin; rw [if_pos rfl]


/-- **[The Bethe Lamb shift is proportional to the density at the origin] `ΔE_n / ΔE_m = |ψ_{nS}(0)|² /
|ψ_{mS}(0)|² = (m/n)³`.** Stated as a cross-multiplied identity (no division): the Bethe Lamb shift and
the `S`-state density at the origin have the *same* `n`-dependence — the shift is proportional to the
electron density at the nucleus. -/
lemma betheLambShift_proportional_to_density (α L Z a₀ : ℝ) (n m : ℕ) :
    betheLambShift α L n * sStateDensityAtOrigin m Z a₀
      = betheLambShift α L m * sStateDensityAtOrigin n Z a₀ := by
  unfold betheLambShift sStateDensityAtOrigin; ring


/-- **[The Lamb shift is the density at the origin, assembled].** The Bethe Lamb shift acts only on the
`l = 0` state because the density at the origin `|ψ_{nl}(0)|²` vanishes for `l ≥ 1`
(`densityAtOrigin_eq_zero_of_l_pos`); it scales as `1/n³` because that is the `1/n³` law of the `S`-state
density `|ψ_{nS}(0)|² = Z³/(π n³ a₀³)`; and the shift is proportional to that density across `n`
(`betheLambShift_proportional_to_density`). The `2S₁⁄₂`–`2P₁⁄₂` splitting is the self-energy of the only
level with support at the nucleus. -/
lemma lambShift_is_origin_density (α L Z a₀ : ℝ) (n m l : ℕ) (hl : 0 < l) :
    densityAtOrigin n l Z a₀ = 0
      ∧ densityAtOrigin n 0 Z a₀ = sStateDensityAtOrigin n Z a₀
      ∧ betheLambShift α L n * sStateDensityAtOrigin m Z a₀
          = betheLambShift α L m * sStateDensityAtOrigin n Z a₀ :=
  ⟨densityAtOrigin_eq_zero_of_l_pos n l Z a₀ hl, densityAtOrigin_s_state n Z a₀,
    betheLambShift_proportional_to_density α L Z a₀ n m⟩

end Physlib.QuantumMechanics.ComplexAction.LambShiftOriginDensity

end

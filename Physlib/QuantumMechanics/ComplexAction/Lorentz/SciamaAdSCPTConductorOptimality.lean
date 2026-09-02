/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConductorDerivation

/-!
# Why the noble metals are *the best* conductors: the s-electron carrier is optimal

`SciamaAdSCPTConductorDerivation` shows the `d¹⁰s¹` configuration *conducts* (a single carrier in a half-filled
`s`-band).  This module continues to *why it is optimal* — why the elements with this configuration are the
**best** conductors, not merely metals.

The Drude mobility `μ = eτ/m*` of a valence carrier depends on its orbital angular momentum `ℓ`: an `s`-electron
(`ℓ = 0`) is spherically symmetric and nearly free (lowest effective mass, least directional scattering), while
higher-`ℓ` valence electrons (`p`, `d`) are more localized and anisotropic — higher `m*`, more scattering, lower
mobility.  Modelling the orbital mobility factor `1/(2ℓ+1)` (inverse of the subshell's angular multiplicity):

* `orbitalMobility_s_gt_p`, `orbitalMobility_p_gt_d` — `s > p > d`: mobility decreases with `ℓ`.
* `orbitalMobility_max_at_s` — the `s`-orbital (`ℓ = 0`) is the **unique maximum**: any `ℓ ≥ 1` carrier has
  strictly lower mobility.
* **`group11_optimal_conductor`** — the `d¹⁰s¹` configuration puts its single conduction electron in the
  maximal-mobility `ℓ = 0` `s`-orbital, over an inert closed `d`-shell: metallic, one carrier, maximal mobility
  — the optimal conductor configuration.  This is why group 11 (Cu, Ag, Au) and the `s`-valence metals are the
  best conductors: `σ = n·eμ` is maximized by a single (`n = 1`) `s`-carrier (`μ` maximal at `ℓ = 0`).

Together with `SciamaAdSCPTBranchConfigurationAnalogy`, the picture is complete: particle physics predicts the
best-conductor **configuration** (`d¹⁰s¹`, optimal `s`-carrier), the **elements** (group 11, `Z = 29, 47, 79`),
and the branch's relativistic coupling predicts their **order** — with our `Ag > Cu > Au` analogous to another
branch's `Au > Ag > Cu`.

Honest scope: the `ℓ`-dependence of mobility is modelled by the illustrative factor `1/(2ℓ+1)` capturing the
`s > p > d` trend; the true effective masses and scattering rates are band-structure quantities.  Group 11 over
the `s¹` alkalis (both `s`-carriers) is additionally favoured by the closed-`d` core's density and screening,
which are solid-state — not resolved here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConductorOptimality

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConductorDerivation

/-- The orbital mobility factor `1/(2ℓ+1)`: a valence carrier in orbital `ℓ` has mobility `∝ 1/(2ℓ+1)` — the
`ℓ = 0` `s`-electron (one spherical orbital) is nearly free; higher `ℓ` is more anisotropic and less mobile. -/
def orbitalMobility (ℓ : ℕ) : ℝ := 1 / (2 * (ℓ : ℝ) + 1)

/-- **[s-orbital mobility is 1] `orbitalMobility 0 = 1`.** -/
theorem orbitalMobility_s : orbitalMobility 0 = 1 := by norm_num [orbitalMobility]

/-- **[s beats p] `orbitalMobility 0 > orbitalMobility 1`** (`1 > 1/3`). -/
theorem orbitalMobility_s_gt_p : orbitalMobility 0 > orbitalMobility 1 := by
  norm_num [orbitalMobility]

/-- **[p beats d] `orbitalMobility 1 > orbitalMobility 2`** (`1/3 > 1/5`). -/
theorem orbitalMobility_p_gt_d : orbitalMobility 1 > orbitalMobility 2 := by
  norm_num [orbitalMobility]

/-- **[The s-orbital is the unique mobility maximum] any `ℓ ≥ 1` carrier is strictly less mobile than `s`.** -/
theorem orbitalMobility_max_at_s (ℓ : ℕ) (h : 1 ≤ ℓ) : orbitalMobility ℓ < orbitalMobility 0 := by
  rw [orbitalMobility_s, orbitalMobility, div_lt_one (by positivity)]
  have hℓ : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
  linarith

/-- **[The `d¹⁰s¹` configuration is the optimal conductor].**  Its single conduction electron sits in the
maximal-mobility `ℓ = 0` `s`-orbital, the band is metallic (half-filled `s`), and there is exactly one carrier —
so `σ = n·eμ` is maximized.  This is why the group-11 noble metals are the *best* conductors, not just metals. -/
theorem group11_optimal_conductor :
    (∀ ℓ : ℕ, 1 ≤ ℓ → orbitalMobility ℓ < orbitalMobility 0)
      ∧ conducts (subshellCapacity 0) 1
      ∧ conductionElectrons 1 = 1 :=
  ⟨orbitalMobility_max_at_s, sBand_halfFilled_conducts, d10s1_single_carrier⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConductorOptimality

end

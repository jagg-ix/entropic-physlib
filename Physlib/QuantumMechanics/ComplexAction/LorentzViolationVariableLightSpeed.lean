/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic

/-!
# A variable-light-speed Lorentz-violation model: the exact `k`-generalized structure

The exact structural core of Hu & Hu, *Correction to the quantum relation of photons in the Doppler effect
based on a special Lorentz violation model* (arXiv:2503.03522, 2025): the Lorentz transformation with the light
speed `c` replaced by an **invariant speed** `k`, and the resulting modified mass shell `E² = p²k² + E₀²`. The
invariant `k` plays the role `c` has in special relativity, while the *light* speed becomes a separate,
observer-dependent quantity — the mechanism by which the model keeps particle energies finite as `v → c`.

Only the exact, `k`-parametric identities are formalized (valid for every `k` with `k² > v²`); the paper's
*fitted* correction coefficient `n(v,c)` (its Eq. 8, carrying the empirical parameter `Q`) is a phenomenological
ansatz and is deliberately not formalized. Setting `k = c` recovers ordinary special relativity.

* **§A — the `k`-interval invariance.** The boost `t' = γ(t − vx/k²)`, `x' = γ(x − vt)` with `γ² = k²/(k²−v²)`
  preserves the modified interval: **`kInterval_invariant`** (`k²t'² − x'² = k²t² − x²`). This generalizes the
  Minkowski interval `c²t² − x²` (the Nagao–Nielsen cone / `PoincareCasimirMassShell` metric) with `c ↦ k`.
* **§B — the modified mass shell.** With `E = γm₀k²`, `p = γm₀v`, `E₀ = m₀k²`: **`modified_mass_shell`**
  (`E² = p²k² + E₀²`) — the `k`-generalization of `E² = p²c² + (m₀c²)²`.
* **§C — reduction to special relativity.** `lorentz_recovered` (at `k = c`, the modified mass shell is exactly
  the standard `E² = (pc)² + (m₀c²)²`).

**Honest layering.** Everything is an exact algebraic identity in the free parameters, holding for any `k` with
`γ² = k²/(k²−v²)` (encoded as the hypothesis `hγ : γ²(k²−v²) = k²`). The physical interpretation (invariant
speed, variable light speed, finite energy at `v→c`) is the model's reading; the fitted `n(v,c)` and the
Doppler/Compton applications built on it are not formalized here.

## References

* J. Hu & H. Hu, arXiv:2503.03522 (2025), Eqs. 1–2. Generalizes the Minkowski mass shell of
  `ComplexAction`/`Relativity` (`c ↦ k`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed


/-- **The `k`-boost preserves the modified interval** `k²t'² − x'² = k²t² − x²`, where `t' = γ(t − vx/k²)`,
`x' = γ(x − vt)` and `γ² = k²/(k²−v²)` (encoded as `hγ`). Replacing `k` with the light speed `c` gives the
ordinary Minkowski interval. -/
lemma kInterval_invariant (v k γ t x : ℝ) (hk : k ≠ 0) (hγ : γ ^ 2 * (k ^ 2 - v ^ 2) = k ^ 2) :
    k ^ 2 * (γ * (t - v * x / k ^ 2)) ^ 2 - (γ * (x - v * t)) ^ 2 = k ^ 2 * t ^ 2 - x ^ 2 := by
  have hk2 : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hk
  have key : k ^ 2 * (γ * (t - v * x / k ^ 2)) ^ 2 - (γ * (x - v * t)) ^ 2
      = γ ^ 2 * (k ^ 2 - v ^ 2) * (k ^ 2 * t ^ 2 - x ^ 2) / k ^ 2 := by
    field_simp
    ring
  rw [key, hγ]
  field_simp


/-- **The modified mass shell** `E² = p²k² + E₀²`, with `E = γm₀k²`, `p = γm₀v`, `E₀ = m₀k²` and
`γ² = k²/(k²−v²)`. This is the `k`-generalization of the relativistic mass shell `E² = p²c² + (m₀c²)²`. -/
lemma modified_mass_shell (m₀ v k γ : ℝ) (hγ : γ ^ 2 * (k ^ 2 - v ^ 2) = k ^ 2) :
    (γ * m₀ * k ^ 2) ^ 2 = (γ * m₀ * v) ^ 2 * k ^ 2 + (m₀ * k ^ 2) ^ 2 := by
  linear_combination (m₀ ^ 2 * k ^ 2) * hγ


/-- **Special relativity is recovered at `k = c`** — the modified mass shell becomes the ordinary
`E² = (pc)² + (m₀c²)²` with rest energy `E₀ = m₀c²`. -/
lemma lorentz_recovered (m₀ v c γ : ℝ) (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2) :
    (γ * m₀ * c ^ 2) ^ 2 = (γ * m₀ * v) ^ 2 * c ^ 2 + (m₀ * c ^ 2) ^ 2 :=
  modified_mass_shell m₀ v c γ hγ

/-- **The rest energy at `k = c` is `E₀ = m₀c²`** — Einstein's relation, the `v = 0` case of the mass shell
(`γ = 1`). -/
lemma rest_energy_mc2 (m₀ c : ℝ) :
    (1 * m₀ * c ^ 2) ^ 2 = (1 * m₀ * 0) ^ 2 * c ^ 2 + (m₀ * c ^ 2) ^ 2 := by
  ring

end Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed

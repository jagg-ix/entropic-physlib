/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic

/-!
# Variable-light-speed model: aberration and the invariant-speed velocity law

The remaining exact identities of Hu & Hu (arXiv:2503.03522, 2025) — the relativistic **aberration of light**
(Eq. 21) and the **velocity-composition law** of the `k`-transformation, showing that the invariant speed of the
model is `k` (not the light speed `c`). As before only the exact `k`-parametric structure is formalized, never
the fitted correction coefficient `n(v,c)`.

* **§A — the invariant speed `k`.** `kVelocityComposition u v k = (u−v)/(1 − vu/k²)` and `invariant_speed_k`
  (`kVelocityComposition k v k = k`): a signal at the invariant speed `k` stays at `k` in every frame — the role
  `c` plays in special relativity, now taken by `k` while the light speed becomes observer-dependent.
* **§B — aberration of light.** With `cos θ' = (cos θ − β)/(1 − β cos θ)`, `sin θ' = sin θ /(γ(1 − β cos θ))`
  (`β = v/k`, `γ² = 1/(1−β²)`): **`aberration_unit_circle`** — `cos²θ' + sin²θ' = 1`, so it is a genuine angle
  transformation. This is the `k`-form of relativistic aberration, reducing to the standard formula at `k = c`.

**Honest layering.** Both are exact algebraic identities (the invariant-speed fixed point and the
unit-circle preservation) in the free parameters, with `γ` encoded by `hγ : γ²(1−β²) = 1`. The fitted `n(v,c)`
and the Doppler/Compton/synchrotron applications are not formalized.

## References

* J. Hu & H. Hu, arXiv:2503.03522 (2025), Eqs. 1 and 21. Companion of
  `ComplexAction.LorentzViolationVariableLightSpeed`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LorentzViolationAberrationVelocity


/-- The **velocity-composition law** of the `k`-transformation: a velocity `u` in one frame is `(u − v)/(1 −
vu/k²)` in a frame moving at `v`. -/
noncomputable def kVelocityComposition (u v k : ℝ) : ℝ := (u - v) / (1 - v * u / k ^ 2)

/-- **`k` is the invariant speed** `kVelocityComposition k v k = k` — a signal at speed `k` is measured at `k`
in every frame, exactly as `c` is invariant in special relativity. (The light speed `c ≠ k` is *not* invariant,
becoming the observer-dependent `nc`.) -/
lemma invariant_speed_k (v k : ℝ) (hk : k ≠ 0) (hkv : k - v ≠ 0) :
    kVelocityComposition k v k = k := by
  unfold kVelocityComposition
  have hd : (1 - v * k / k ^ 2) ≠ 0 := by
    have e : 1 - v * k / k ^ 2 = (k - v) / k := by field_simp
    rw [e]; exact div_ne_zero hkv hk
  rw [div_eq_iff hd]
  field_simp


/-- **Relativistic aberration is a genuine angle transformation** `cos²θ' + sin²θ' = 1`, where
`cos θ' = (cos θ − β)/(1 − β cos θ)` and `sin θ' = sin θ/(γ(1 − β cos θ))` with `β = v/k` and `γ² = 1/(1−β²)`.
This is the `k`-generalized aberration of light; at `k = c` it is the ordinary relativistic aberration. -/
lemma aberration_unit_circle (cθ sθ β γ : ℝ) (hc : cθ ^ 2 + sθ ^ 2 = 1)
    (hγ : γ ^ 2 * (1 - β ^ 2) = 1) (hd : 1 - β * cθ ≠ 0) :
    ((cθ - β) / (1 - β * cθ)) ^ 2 + (sθ / (γ * (1 - β * cθ))) ^ 2 = 1 := by
  have hγ0 : γ ≠ 0 := by rintro rfl; norm_num at hγ
  have key : (cθ - β) ^ 2 * γ ^ 2 + sθ ^ 2 = γ ^ 2 * (1 - β * cθ) ^ 2 := by
    linear_combination (cθ ^ 2 - 1) * hγ + hc
  have expand : ((cθ - β) / (1 - β * cθ)) ^ 2 + (sθ / (γ * (1 - β * cθ))) ^ 2
      = ((cθ - β) ^ 2 * γ ^ 2 + sθ ^ 2) / (γ ^ 2 * (1 - β * cθ) ^ 2) := by
    field_simp
  rw [expand, key]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.LorentzViolationAberrationVelocity

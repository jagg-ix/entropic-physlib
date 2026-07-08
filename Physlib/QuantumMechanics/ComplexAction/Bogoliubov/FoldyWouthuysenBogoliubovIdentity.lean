/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.FoldyWouthuysenExact
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

/-!
# Beyond operational correspondence: the Foldy–Wouthuysen rotation *is* a Bogoliubov transformation

`EntropicTime.HelicityEntropicComplexMomentum` proved the *operational* correspondence — the helicity momentum
`|p|` equals the Bogoliubov off-diagonal `ξ`, sharing the dispersion. This file goes **beyond** it: the
exact Foldy–Wouthuysen rotation `W = (E+m)·1 + β(α·p)` (`Dirac.FoldyWouthuysenExact`) is *literally* a
Bogoliubov transformation — its normalized coefficients **are** `bogoliubovU2`, `bogoliubovV2`.

## The Foldy–Wouthuysen weights are the Bogoliubov coefficients

The matrix fact `W·W̄ = ((E+m)²+|p|²)·1` (`fwOperator_modulus`) is, on shell (`E² = m²+|p|²`), the
**fermionic Bogoliubov normalization** `(E+m)²+|p|² = 2E(E+m)` (`fw_modulus_normalization`). So the
normalized rotation `U = W/√(2E(E+m))` has squared coefficients

 `u² = (E+m)²/(2E(E+m)) = (E+m)/(2E) = bogoliubovU2 m |p|` (`fw_upperWeight_eq_bogoliubovU2`),
 `v² = |p|²/(2E(E+m)) = (E−m)/(2E) = bogoliubovV2 m |p|` (`fw_lowerWeight_eq_bogoliubovV2`),

with `u² + v² = 1` (fermionic) and `u² − v² = m/E`. So the Foldy–Wouthuysen rotation **is** the
Bogoliubov transformation `bogoliubov(ξ = m, Δ = |p|)`, and `fw_intertwine` (`W H = Eβ W`) is its
diagonalization. The lower (antiparticle) weight `v²` is the Bogoliubov quasiparticle occupation, and
its binary entropy is the entropic time (`fw_entropicTime`).

## The dual conventions

This Bogoliubov uses `ξ = m` (rest mass, diagonal), `Δ = |p|` (momentum, off-diagonal) — so
`v² = (1 − m/E)/2` vanishes at **rest** (`|p| = 0`): the *quasiparticle/Foldy–Wouthuysen* angle. The
entropic *proper-time* link (`EntropicTime.HelicityEntropicComplexMomentum`) used the **dual** assignment
`ξ = |p|`, `Δ = m`, with `v² = (1 − |p|/E)/2` vanishing at **massless**. They are the `ξ ↔ Δ` duality —
two distinct mixing angles; "beyond operational" sharpens the Foldy–Wouthuysen one (`ξ = m`).

## Scope (the genuine remaining gap)

What is proved: the Foldy–Wouthuysen rotation equals the single-particle Bogoliubov transformation —
the coefficient identity, the normalization, the diagonalization, and the helicity as conserved label
(`helicity_commutes_energy`). What is **not** (and cannot be at the finite-matrix level): the
*second-quantized* statement that the Dirac field's particle/antiparticle operators are the
Bogoliubov-transformed vacuum operators — that is the Bogoliubov automorphism of the CAR algebra on
Fock space (infinite-dimensional), the real frontier beyond this matrix identification.

## References

* This development: `Dirac.FoldyWouthuysenExact`, `Bogoliubov.Transformation`, `Bogoliubov.EntropicTime`,
 `EntropicTime.HelicityEntropicComplexMomentum`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FoldyWouthuysenBogoliubovIdentity

/-! ## §A — the dispersion and the Bogoliubov normalization -/

/-- **`E² = m² + Δ²`** for the Bogoliubov energy (`Δ = |p|` the momentum, `m` the rest mass). -/
theorem bogoliubovEnergy_sq (m Δ : ℝ) : bogoliubovEnergy m Δ ^ 2 = m ^ 2 + Δ ^ 2 := by
  rw [bogoliubovEnergy, Real.sq_sqrt (by positivity)]

/-- **The Foldy–Wouthuysen modulus is the fermionic Bogoliubov normalization** `(E+m)²+|p|² =
2E(E+m)`: the matrix fact `W·W̄ = ((E+m)²+|p|²)·1` (`fwOperator_modulus`) is `u²+v² = 1` in disguise. -/
theorem fw_modulus_normalization (m Δ : ℝ) :
    (bogoliubovEnergy m Δ + m) ^ 2 + Δ ^ 2 = 2 * bogoliubovEnergy m Δ * (bogoliubovEnergy m Δ + m) := by
  have hE2 := bogoliubovEnergy_sq m Δ
  linear_combination -hE2

/-! ## §B — the Foldy–Wouthuysen weights are the Bogoliubov coefficients -/

/-- **The Foldy–Wouthuysen lower (antiparticle) weight is the Bogoliubov occupation**
`v² = |p|²/(2E(E+m)) = bogoliubovV2 m |p|`. The Foldy–Wouthuysen small component is the Bogoliubov
quasiparticle occupation. -/
theorem fw_lowerWeight_eq_bogoliubovV2 (m Δ : ℝ) (hm : 0 < m) :
    Δ ^ 2 / (2 * bogoliubovEnergy m Δ * (bogoliubovEnergy m Δ + m)) = bogoliubovV2 m Δ := by
  have hE2 := bogoliubovEnergy_sq m Δ
  have hEpos : 0 < bogoliubovEnergy m Δ := by
    rw [bogoliubovEnergy]
    exact Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (pow_pos hm 2) (sq_nonneg Δ))
  have hE : bogoliubovEnergy m Δ ≠ 0 := hEpos.ne'
  have hEm : bogoliubovEnergy m Δ + m ≠ 0 := by linarith
  have key : Δ ^ 2 = (bogoliubovEnergy m Δ - m) * (bogoliubovEnergy m Δ + m) := by
    linear_combination -hE2
  rw [bogoliubovV2, key]
  field_simp

/-- **The Foldy–Wouthuysen upper (particle) weight is the Bogoliubov coherence factor**
`u² = (E+m)²/(2E(E+m)) = bogoliubovU2 m |p|`. -/
theorem fw_upperWeight_eq_bogoliubovU2 (m Δ : ℝ) (hm : 0 < m) :
    (bogoliubovEnergy m Δ + m) ^ 2 / (2 * bogoliubovEnergy m Δ * (bogoliubovEnergy m Δ + m))
      = bogoliubovU2 m Δ := by
  have hEpos : 0 < bogoliubovEnergy m Δ := by
    rw [bogoliubovEnergy]
    exact Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (pow_pos hm 2) (sq_nonneg Δ))
  have hE : bogoliubovEnergy m Δ ≠ 0 := hEpos.ne'
  have hEm : bogoliubovEnergy m Δ + m ≠ 0 := by linarith
  rw [bogoliubovU2]
  field_simp

/-- **The Foldy–Wouthuysen weights satisfy the fermionic normalization** `u² + v² = 1` — the matrix
`W·W̄` normalization is the Bogoliubov `u²+v²=1`. -/
theorem fw_weights_normalization (m Δ : ℝ) : bogoliubovU2 m Δ + bogoliubovV2 m Δ = 1 :=
  bogoliubov_normalization m Δ

/-- **The Foldy–Wouthuysen coherence difference** `u² − v² = m/E` (the Foldy–Wouthuysen `cos θ`). -/
theorem fw_weights_diff (m Δ : ℝ) :
    bogoliubovU2 m Δ - bogoliubovV2 m Δ = m / bogoliubovEnergy m Δ :=
  bogoliubov_uv_diff m Δ

/-! ## §C — the entropic time of the Foldy–Wouthuysen quasiparticle -/

/-- **The Foldy–Wouthuysen entropic time is the binary entropy of the antiparticle admixture**
`τ_ent = binEntropy(v²)`: the entropic time of the Foldy–Wouthuysen quasiparticle is the binary
entropy of its Bogoliubov occupation `v²`. -/
theorem fw_entropicTime (m Δ : ℝ) :
    bogoliubovEntropicTime m Δ = Real.binEntropy (bogoliubovV2 m Δ) := rfl

/-! ## §D — the Foldy–Wouthuysen rotation is the Bogoliubov transformation (bundled) -/

/-- **Beyond operational correspondence: the Foldy–Wouthuysen rotation is the Bogoliubov
transformation.** For a physical mass `m > 0` and momentum `Δ = |p|`:

* the matrix modulus `(E+m)²+|p|²` is the fermionic normalization `2E(E+m)` (so `W/√(2E(E+m))` is
  unitary);
* the normalized upper/lower weights are exactly `bogoliubovU2 m |p|`, `bogoliubovV2 m |p|`, with
  `u² + v² = 1`;
* the antiparticle-admixture entropy is the entropic time `binEntropy(v²)`.

So the Foldy–Wouthuysen rotation is `bogoliubov(ξ = m, Δ = |p|)` — not merely sharing `|p|`, but the
same single-particle transformation (its diagonalization is `fw_intertwine`). -/
theorem foldyWouthuysen_is_bogoliubov (m Δ : ℝ) (hm : 0 < m) :
    (bogoliubovEnergy m Δ + m) ^ 2 + Δ ^ 2 = 2 * bogoliubovEnergy m Δ * (bogoliubovEnergy m Δ + m)
      ∧ Δ ^ 2 / (2 * bogoliubovEnergy m Δ * (bogoliubovEnergy m Δ + m)) = bogoliubovV2 m Δ
      ∧ (bogoliubovEnergy m Δ + m) ^ 2 / (2 * bogoliubovEnergy m Δ * (bogoliubovEnergy m Δ + m))
        = bogoliubovU2 m Δ
      ∧ bogoliubovU2 m Δ + bogoliubovV2 m Δ = 1 :=
  ⟨fw_modulus_normalization m Δ, fw_lowerWeight_eq_bogoliubovV2 m Δ hm,
   fw_upperWeight_eq_bogoliubovU2 m Δ hm, fw_weights_normalization m Δ⟩

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FoldyWouthuysenBogoliubovIdentity

end

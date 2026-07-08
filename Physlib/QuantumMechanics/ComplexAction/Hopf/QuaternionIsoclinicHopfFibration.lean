/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# SO(4) isoclinic rotations and the Hopf fibration `S³ → S²` (quaternions)

The fermion-as-spinor picture rests on two pieces of quaternion geometry that `gemdec22-2025.md`
(Lück–Warrington icosians, "two counter-rotating 3-spheres") invokes but never makes precise. This file
formalizes both over Mathlib's quaternion algebra `ℍ[ℝ]`, where the unit quaternions are the 3-sphere `S³`.

* **§A — isoclinic decomposition of SO(4).** Left and right multiplication by a *unit* quaternion are
 isometries of `ℍ[ℝ]` (`leftMul_normSq`, `rightMul_normSq`), and they **commute**
 (`isoclinic_commute`, = associativity). This is the splitting `SO(4) ⊇ SU(2)_L × SU(2)_R`: every
 isoclinic rotation is `x ↦ p·x` (left) or `x ↦ x·q` (right), and the two families commute.

* **§B — the two-sided map and the `(SU(2)×SU(2))/±1` double cover.** `so4Map p q x = p·x·q̄` (with
 `q̄ = q⁻¹` on `S³`) is an isometry (`so4Map_normSq`), composes as a homomorphism (`so4Map_comp`), and crucially
 `so4Map (-p) (-q) = so4Map p q` (`so4Map_neg_neg`): the pair `(p,q)` and `(-p,-q)` give the *same*
 rotation — the `±1` kernel of `SU(2)×SU(2) ↠ SO(4)`.

* **§C — the Hopf fibration `S³ → S²`.** `hopf q = q·i·q̄` conjugates the imaginary unit. The image is a
 *unit* quaternion (`hopf_normSq`, lands on a sphere) that is *purely imaginary* (`hopf_re_zero`, lands
 on `S² ⊂ ℑℍ`). It is invariant under the antipode `hopf (-q) = hopf q` (`hopf_neg`, the `SU(2) → SO(3)`
 double cover — the fermion `2π ↦ −1`) and under the `S¹` stabilizer of `i`
 (`hopf_fiber`: `hopf (q·(cos θ + i sin θ)) = hopf q`), so the fibers are circles.

**Why this is the spinor double cover.** `hopf_neg` is the same `q ~ −q` identification that gives the
`SL(2,ℂ) → SO⁺(1,3)` rapidity-doubling of `Hopf.SL2CDoubleCover` and the `ribbonTwist ½ = −1` fermion
exchange sign of `Hopf.ChargeConjugationRibbonTwist`: a spinor needs a `4π` turn (`q → q`, two sheets) to
return, its `2π` turn landing on `−q`. `so4Map_neg_neg` is the 4-dimensional version of the same `±1`.

**Left vs right fiber.** This `hopf` is invariant under the *right* `U(1)` (`hopf_fiber`, `q ↦ q·e^{iθ}`),
so it quotients `S³` by right cosets — the `SU(2)_R` factor of §A. The ℂ²/Pauli realization
`Hopf.FibrationSpinorMap` instead quotients by the *left* global phase `χ ↦ uχ` (`SU(2)_L`); the two are the
mirror (left/right) Hopf fibrations. `Hopf.QuaternionHopfDualSphere` runs these direction vectors through
the `Hopf.DualSphereFiberDecomposition` cross-sphere alignment and finds it `≡ 1` (a rigid orthonormal frame).

Everything here is proven quaternion algebra: isometry from multiplicativity of
`normSq`, commuting isoclinic families from associativity, the Hopf image on `S²` from `star`-antisymmetry,
and the circle fibers from the `i`-stabilizer. The *identification* of these objects with fermions/SO(4)
gauge structure is the model reading; the geometry is unconditional.

## References

* Quaternion realization of `SO(4) = (SU(2)×SU(2))/±1` and the Hopf map `S³ → S²`. `Physlib`
 (`Hopf.SL2CDoubleCover`, `Hopf.ChargeConjugationRibbonTwist.ribbonTwist`).

No additional assumptions.
-/

set_option autoImplicit false

open Quaternion Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration

/-! ## §A — isoclinic rotations: left/right unit-quaternion multiplication -/

/-- **[Left isoclinic rotation is an isometry]** for a *unit* quaternion `p` (`normSq p = 1`), left
multiplication `x ↦ p·x` preserves `normSq` — an element of `SO(4)` (the left factor `SU(2)_L`). -/
theorem leftMul_normSq (p x : ℍ[ℝ]) (hp : normSq p = 1) : normSq (p * x) = normSq x := by
  rw [map_mul, hp, one_mul]

/-- **[Right isoclinic rotation is an isometry]** for a *unit* quaternion `q`, right multiplication
`x ↦ x·q` preserves `normSq` — the right factor `SU(2)_R`. -/
theorem rightMul_normSq (q x : ℍ[ℝ]) (hq : normSq q = 1) : normSq (x * q) = normSq x := by
  rw [map_mul, hq, mul_one]

/-- **[Left and right isoclinic rotations commute]** `p·(x·q) = (p·x)·q` — the two isoclinic families
commute, the algebraic heart of the splitting `SU(2)_L × SU(2)_R → SO(4)` ("two counter-rotating
3-spheres"). -/
theorem isoclinic_commute (p q x : ℍ[ℝ]) : p * (x * q) = (p * x) * q := (mul_assoc p x q).symm

/-! ## §B — the two-sided map `p·x·q̄` and the `(SU(2)×SU(2))/±1` double cover -/

/-- **The generic SO(4) rotation** `x ↦ p·x·q̄` for unit quaternions `p, q` (on `S³` the conjugate `q̄`
is the inverse `q⁻¹`, so this is the standard `p·x·q⁻¹`). -/
def so4Map (p q x : ℍ[ℝ]) : ℍ[ℝ] := p * x * star q

/-- **[The two-sided map is an isometry]** `normSq (p·x·q̄) = normSq x` for unit `p, q` — so
`so4Map p q ∈ SO(4)`. -/
theorem so4Map_normSq (p q x : ℍ[ℝ]) (hp : normSq p = 1) (hq : normSq q = 1) :
    normSq (so4Map p q x) = normSq x := by
  simp only [so4Map, map_mul, normSq_star, hp, hq, one_mul, mul_one]

/-- **[Identity rotation]** `so4Map 1 1 = id`. -/
theorem so4Map_one (x : ℍ[ℝ]) : so4Map 1 1 x = x := by
  simp only [so4Map, star_one, one_mul, mul_one]

/-- **[Composition is a homomorphism]** `so4Map p₂ q₂ ∘ so4Map p₁ q₁ = so4Map (p₂·p₁) (q₂·q₁)` — the
group homomorphism `SU(2)×SU(2) → SO(4)`. -/
theorem so4Map_comp (p₁ q₁ p₂ q₂ x : ℍ[ℝ]) :
    so4Map p₂ q₂ (so4Map p₁ q₁ x) = so4Map (p₂ * p₁) (q₂ * q₁) x := by
  simp only [so4Map, star_mul]; noncomm_ring

/-- **[The `±1` kernel — the double cover]** `so4Map (-p) (-q) = so4Map p q`: the pairs `(p,q)` and
`(-p,-q)` induce the *same* `SO(4)` rotation. This is the kernel `{±(1,1)}` of `SU(2)×SU(2) ↠ SO(4)`,
the 4D analogue of the spinor double cover. -/
theorem so4Map_neg_neg (p q x : ℍ[ℝ]) : so4Map (-p) (-q) x = so4Map p q x := by
  simp only [so4Map]
  ext <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

/-! ## §C — the Hopf fibration `S³ → S²` -/

/-- The imaginary unit `i = (0,1,0,0)` — a fixed point of `S² ⊂ ℑℍ`. -/
def imagUnit : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

@[simp] theorem normSq_imagUnit : normSq imagUnit = 1 := by
  simp only [imagUnit, Quaternion.normSq_def']; norm_num

theorem star_imagUnit : star imagUnit = -imagUnit := by
  ext <;> simp [imagUnit]

/-- **The Hopf map** `S³ → S²`: conjugate the imaginary unit, `hopf q = q·i·q̄`. -/
def hopf (q : ℍ[ℝ]) : ℍ[ℝ] := q * imagUnit * star q

/-- **[The Hopf image is anti-self-conjugate]** `star (hopf q) = -hopf q` — `hopf q` is purely imaginary
(no real part), the key step placing it on `S² ⊂ ℑℍ`. -/
theorem star_hopf (q : ℍ[ℝ]) : star (hopf q) = - hopf q := by
  simp only [hopf, imagUnit]
  ext <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

/-- **[The Hopf image lies in `ℑℍ`]** `(hopf q).re = 0`: the image is a purely imaginary quaternion, a
point of the 2-sphere `S²`. -/
theorem hopf_re_zero (q : ℍ[ℝ]) : (hopf q).re = 0 :=
  QuaternionAlgebra.star_eq_neg.mp (star_hopf q)

/-- **[The Hopf image lies on the unit sphere]** `normSq (hopf q) = 1` for `q ∈ S³` (`normSq q = 1`):
together with `hopf_re_zero`, the image is on the *unit* 2-sphere `S²`. -/
theorem hopf_normSq (q : ℍ[ℝ]) (hq : normSq q = 1) : normSq (hopf q) = 1 := by
  simp only [hopf, map_mul, normSq_imagUnit, normSq_star, hq, one_mul, mul_one]

/-- **[Antipodal invariance — the `SU(2) → SO(3)` double cover]** `hopf (-q) = hopf q`: the two
antipodal preimages `±q ∈ S³` map to the *same* point of `S²`. This is the spinor double cover —
the fermion's `2π` rotation lands on `−q`, only `4π` returns to `q`. -/
theorem hopf_neg (q : ℍ[ℝ]) : hopf (-q) = hopf q := by
  simp only [hopf, imagUnit]
  ext <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

/-- The `S¹` fiber circle `cos θ + i sin θ` — the stabilizer of `i` inside `S³`. -/
def fiberCircle (θ : ℝ) : ℍ[ℝ] := ⟨Real.cos θ, Real.sin θ, 0, 0⟩

@[simp] theorem normSq_fiberCircle (θ : ℝ) : normSq (fiberCircle θ) = 1 := by
  simp only [fiberCircle, Quaternion.normSq_def']
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **[The fiber circle commutes with `i`]** `(cos θ + i sin θ)·i = i·(cos θ + i sin θ)` — `fiberCircle θ`
lies in the commutative subalgebra `ℝ[i]`. -/
theorem fiberCircle_comm (θ : ℝ) : fiberCircle θ * imagUnit = imagUnit * fiberCircle θ := by
  ext <;>
    simp [fiberCircle, imagUnit, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

/-- **[The fiber circle stabilizes `i`]** `u·i·ū = i` for `u = fiberCircle θ` — conjugation by a fiber
element fixes the imaginary axis. -/
theorem fiber_fixes_imagUnit (θ : ℝ) :
    fiberCircle θ * imagUnit * star (fiberCircle θ) = imagUnit := by
  have hstar : fiberCircle θ * star (fiberCircle θ) = 1 := by
    rw [mul_star_eq_coe, ← Quaternion.normSq_def, normSq_fiberCircle, Quaternion.coe_one]
  calc fiberCircle θ * imagUnit * star (fiberCircle θ)
      = imagUnit * (fiberCircle θ * star (fiberCircle θ)) := by rw [fiberCircle_comm]; noncomm_ring
    _ = imagUnit := by rw [hstar, mul_one]

/-- **[The Hopf fibers are circles]** `hopf (q·(cos θ + i sin θ)) = hopf q`: multiplying `q` on the right
by the `S¹` stabilizer of `i` leaves the Hopf image unchanged. So the preimage of each `S²` point is a
great circle `S¹` — the fibration `S¹ ↪ S³ → S²`. -/
theorem hopf_fiber (q : ℍ[ℝ]) (θ : ℝ) : hopf (q * fiberCircle θ) = hopf q := by
  have hf := fiber_fixes_imagUnit θ
  simp only [hopf, star_mul]
  calc q * fiberCircle θ * imagUnit * (star (fiberCircle θ) * star q)
      = q * (fiberCircle θ * imagUnit * star (fiberCircle θ)) * star q := by noncomm_ring
    _ = q * imagUnit * star q := by rw [hf]

end Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration

end

end

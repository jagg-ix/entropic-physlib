/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric
public import Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# Inspecting the Schwarzschild horizon through scale dilation and the SL(2,ℂ) Möbius boundary

Reads the Schwarzschild horizon of `SchwarzschildInteriorFoliationMetric` — the 2-sphere `r = R_g = 2GM/c²`
of area `A = 4πR_g²` (Barletta's angular block `a² = r²`) carrying the Bekenstein–Hawking entropy of the
ER=EPR bridge — against two other structures already in the repository: the **scale-dilation log metric**
(`EntropicTime.ScaleDilationLogMetric`, radial dilations `r ↦ μr` with `scaleDistance r r' = |log(r/r')|`) and
the **SL(2,ℂ) Möbius action** on the boundary Riemann sphere (`RiemannSphereBlochSL2CLinks.sl2c_onePoint_mobius`,
the celestial-sphere conformal group). Five connections:

* **§A — horizon area and radius-based entropy are scale-covariant.** `horizonArea_dilation` and
  `horizonBhEntropy_dilation` prove `A(μR) = μ²·A(R)` and `S(μR) = μ²·S(R)` with the physical constants
  fixed. A positive radial dilation has `scaleDistance (μR) R = |log μ|`.
* **§B — one-bit entropy matches one factor-2 scale step.** `erEpr_entropy_eq_scaleDistance`:
  the wormhole entropy `S_BH = k_B ln 2` (Dai–Minic–Stojkovic–Fu Eq. 10) equals `k_B · scaleDistance 2 1` —
  an exact numerical identity with the length of one binary scale step. It does not assert that
  entanglement dynamically doubles a physical horizon.
* **§C — the dilation is a diagonal SL(2,ℂ) Möbius map of the horizon sphere.** `dilationSL2C` is the SL(2,ℂ)
  element `diag(√μ, 1/√μ)`. It acts on finite coordinates by `w ↦ μw` and fixes infinity, hence acts on the
  whole Riemann sphere. The positive scale group is represented by a diagonal subgroup of celestial
  `SL(2,ℂ)`.
* **§D — positive scales form a represented group.** `scaleDilationSL2CHom` bundles the diagonal boosts as a
  homomorphism from the multiplicative positive reals into `SL(2,ℂ)`, with explicit identity, inverse, and
  composed Möbius-action laws.
* **§E — multi-bit entropy is a scale ladder, not a mass theorem.** `nBitErEprEntropy n k_B = k_B n log 2`
  equals `k_B·scaleDistance(2ⁿ,1)`. This is an information/scale identity; no generalized `n`-bit
  Schwarzschild mass is postulated.

Reuses (GREP-first) `SchwarzschildInteriorFoliationMetric` (`bhEntropy`, `erEpr_wormholeMass`),
`Thermodynamics.sphereArea`, `EntropicTime.ScaleDilationLogMetric` (`scaleDistance`, `scaleDistance_two_one`),
`RiemannSphereBlochSL2CLinks` (`sl2c_onePoint_mobius`).

## References

* D.-C. Dai, D. Minic, D. Stojkovic, C. Fu, Phys. Rev. D 102 (2020) 066004 (ER=EPR entropy–energy test);
  E. Barletta, S. Dragomir, M. Magliaro, Class. Quantum Grav. 31 (2014) 205012 (foliated Schwarzschild).
-/

set_option autoImplicit false

open Matrix
open scoped MatrixGroups
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
open Physlib.Thermodynamics

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius

/-! ### §A The horizon area is scale-covariant -/

/-- **[The horizon area scales as `μ²` under a radial dilation] `A(μR) = μ²·A(R)`.** The horizon 2-sphere area
`A = 4πR²` (`Thermodynamics.sphereArea`) is not scale-invariant: dilating the Schwarzschild radius `R_g ↦ μR_g`
multiplies the area — and hence the Bekenstein–Hawking entropy — by `μ²`. -/
theorem horizonArea_dilation (μ R : ℝ) : sphereArea (μ * R) = μ ^ 2 * sphereArea R := by
  simp only [sphereArea]; ring

/-- Bekenstein–Hawking entropy expressed directly in terms of a spherical horizon radius,
with `G`, `c`, `ℏ`, and `kB` treated as fixed parameters. -/
noncomputable def horizonBhEntropy (R G c ℏ kB : ℝ) : ℝ :=
  kB * c ^ 3 * sphereArea R / (4 * G * ℏ)

/-- **[Radius-based Bekenstein–Hawking entropy is scale-covariant]**
`S(μR) = μ² S(R)`. Unlike the area-only statement, this theorem explicitly carries
the entropy formula and keeps all physical constants fixed. -/
/- ZIL-BEGIN -/
@[zil_claim physlib.schwarzschild.horizonEntropyScaleCovariant,
  zil_concept physics.schwarzschildHorizon, zil_level domain_model, zil_export]
/- ZIL-END -/
theorem horizonBhEntropy_dilation (μ R G c ℏ kB : ℝ) :
    horizonBhEntropy (μ * R) G c ℏ kB = μ ^ 2 * horizonBhEntropy R G c ℏ kB := by
  unfold horizonBhEntropy
  rw [horizonArea_dilation]
  ring

/-- The mass-based entropy agrees with the radius-based expression at the
Schwarzschild radius. -/
/- ZIL-BEGIN -/
@[zil_claim physlib.schwarzschild.massRadiusEntropyAgreement,
  zil_concept physics.schwarzschildHorizon, zil_requires assumptions.lightSpeedNonzero,
  zil_level domain_model, zil_export]
/- ZIL-END -/
theorem bhEntropy_eq_horizonBhEntropy (M G c ℏ kB : ℝ) (hc : c ≠ 0) :
    bhEntropy M G c ℏ kB =
      horizonBhEntropy (Physlib.Relativity.SemiClassical.schwarzschildRadius M G c)
        G c ℏ kB := by
  unfold bhEntropy horizonBhEntropy
  rw [schwarzschildArea_eq_sphereArea M G c hc]

/-- **[The scale-distance of a radial dilation] `scaleDistance (μR) R = |log μ|`** (for `R ≠ 0`) — a dilation
`R_g ↦ μR_g` sits at log-distance `|log μ|` in the scale metric, independently of the base radius. -/
theorem horizon_scaleDistance (μ R : ℝ) (hR : R ≠ 0) :
    scaleDistance (μ * R) R = |Real.log μ| := by
  rw [scaleDistance, mul_div_assoc, div_self hR, mul_one]

/-- The physical positive-scale specialization of `horizon_scaleDistance`. Using bundled
positive reals rules out sign-changing or zero “dilations” at the statement boundary. -/
theorem horizon_scaleDistance_pos (μ R : {x : ℝ // 0 < x}) :
    scaleDistance (μ.1 * R.1) R.1 = |Real.log μ.1| :=
  horizon_scaleDistance μ.1 R.1 R.2.ne'

/-! ### §B One-bit ER=EPR entropy matches one factor-2 scale step -/

/-- **[The ER=EPR one-bit entropy is `k_B` times a factor-2 scale-distance]
`S_BH = k_B · scaleDistance 2 1`.** The wormhole whose Bekenstein–Hawking entropy is one bit of entanglement
(`erEpr_wormholeMass`, `S_BH = k_B ln 2`) has entropy exactly `k_B` times the scale-distance of a factor-2
dilation (`scaleDistance 2 1 = ln 2`). This is an equality of values; it does not identify the
entanglement operation with a physical rescaling of the horizon. -/
/- ZIL-BEGIN -/
@[zil_claim physlib.schwarzschild.oneBitEntropyScaleIdentity,
  zil_concept physics.erEprScaleIdentity, zil_requires assumptions.positivePhysicalConstants,
  zil_level bridge_theorem, zil_export]
/- ZIL-END -/
theorem erEpr_entropy_eq_scaleDistance (G c ℏ kB : ℝ) (hG : 0 < G) (hc : 0 < c) (hℏ : 0 < ℏ) :
    bhEntropy (Real.sqrt (ℏ * c * Real.log 2 / (4 * Real.pi * G))) G c ℏ kB
      = kB * scaleDistance 2 1 := by
  rw [erEpr_wormholeMass G c ℏ kB hG hc hℏ, scaleDistance_two_one]

/-! ### §C The dilation is a diagonal SL(2,ℂ) Möbius map of the horizon sphere -/

/-- **[The scale dilation as a diagonal SL(2,ℂ) element] `diag(√μ, 1/√μ)`** — the boost of the celestial
SL(2,ℂ) whose Möbius action rescales the horizon boundary sphere by `μ`. -/
noncomputable def dilationSL2C (μ : ℝ) (hμ : 0 < μ) : SL(2, ℂ) :=
  ⟨!![(Real.sqrt μ : ℂ), 0; 0, (Real.sqrt μ : ℂ)⁻¹], by
    have h : (Real.sqrt μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hμ).ne'
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_inv_cancel₀ h]⟩

/-- **[The dilation acts on finite Riemann-sphere coordinates by `w ↦ μw`]
`diag(√μ, 1/√μ) • w = μw`.** The diagonal
SL(2,ℂ) element `dilationSL2C μ` implements, through the boundary Möbius action (`sl2c_onePoint_mobius`), the
scale dilation `w ↦ μw` for every finite `w : ℂ` in the horizon sphere `OnePoint ℂ`.
The separate theorem `dilationSL2C_mobius_infty` proves that the remaining point is fixed. -/
theorem dilationSL2C_mobius (μ : ℝ) (hμ : 0 < μ) (w : ℂ) :
    (dilationSL2C μ hμ).toGL • (w : OnePoint ℂ) = ((μ * w : ℂ) : OnePoint ℂ) := by
  have h : (Real.sqrt μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hμ).ne'
  have hentry : ∀ i j, (dilationSL2C μ hμ : Matrix (Fin 2) (Fin 2) ℂ) i j
      = !![(Real.sqrt μ : ℂ), 0; 0, (Real.sqrt μ : ℂ)⁻¹] i j := fun _ _ => rfl
  have hk : (dilationSL2C μ hμ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * w
      + (dilationSL2C μ hμ : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
    rw [hentry, hentry]
    simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, zero_mul, zero_add]
    exact inv_ne_zero h
  rw [sl2c_onePoint_mobius (dilationSL2C μ hμ) w hk]
  congr 1
  rw [hentry, hentry, hentry, hentry]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero,
    zero_mul, zero_add]
  rw [div_eq_mul_inv, inv_inv, show (Real.sqrt μ : ℂ) * w * (Real.sqrt μ : ℂ)
        = ((Real.sqrt μ : ℂ) * (Real.sqrt μ : ℂ)) * w from by ring,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hμ.le]

/-- **[The diagonal dilation fixes the point at infinity]**. Together with
`dilationSL2C_mobius`, this covers every point of `OnePoint ℂ`, not only finite coordinates. -/
theorem dilationSL2C_mobius_infty (μ : ℝ) (hμ : 0 < μ) :
    (dilationSL2C μ hμ).toGL • (OnePoint.infty : OnePoint ℂ) = OnePoint.infty := by
  rw [OnePoint.smul_infty_eq_self_iff]
  rfl

/-! ### §D The positive scale group as a subgroup of SL(2,ℂ) -/

set_option linter.unusedSimpArgs false in
/-- **[The dilations compose] `diag(√μ,1/√μ) · diag(√ν,1/√ν) = diag(√(μν),1/√(μν))`.** The map
`μ ↦ dilationSL2C μ` is a homomorphism from the multiplicative scale group `(ℝ₊, ×)` into `SL(2,ℂ)`, so the
radial dilations of the horizon are genuinely the diagonal (boost) one-parameter subgroup of the celestial
SL(2,ℂ) — and their Möbius actions compose as `w ↦ μw ↦ μνw`. -/
theorem dilationSL2C_mul (μ ν : ℝ) (hμ : 0 < μ) (hν : 0 < ν) :
    dilationSL2C μ hμ * dilationSL2C ν hν = dilationSL2C (μ * ν) (mul_pos hμ hν) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  have hμν : (Real.sqrt (μ * ν) : ℂ) = (Real.sqrt μ : ℂ) * (Real.sqrt ν : ℂ) := by
    rw [← Complex.ofReal_mul, Real.sqrt_mul hμ.le]
  fin_cases i <;> fin_cases j <;>
    simp only [dilationSL2C, Matrix.SpecialLinearGroup.coe_mk, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, mul_zero, zero_mul, add_zero, zero_add, hμν, mul_inv]

/-- The multiplicative group of strictly positive real scale factors. This is kept
separate from `ScaleLine`, whose primary bundled structure is its log metric. -/
abbrev PositiveScale := {μ : ℝ // 0 < μ}

/-- **[The positive scale group represented in `SL(2,ℂ)`]**. Each positive scale
`PositiveScale = {μ : ℝ // 0 < μ}` is sent to the diagonal boost
`diag(√μ, 1/√μ)`. The multiplication proof above packages this as a genuine group
homomorphism, rather than only a pointwise family of matrices. -/
noncomputable def scaleDilationSL2CHom : PositiveScale →* SL(2, ℂ) where
  toFun μ := dilationSL2C μ.1 μ.2
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [dilationSL2C, Matrix.of_apply]
  map_mul' μ ν := (dilationSL2C_mul μ.1 ν.1 μ.2 ν.2).symm

/-- **The diagonal positive-dilation subgroup of `SL(2,ℂ)`**, defined as the range of
`scaleDilationSL2CHom`. Closure under identity, multiplication, and inverse is therefore
part of the bundled `Subgroup` structure. -/
noncomputable def scaleDilationSL2CSubgroup : Subgroup (SL(2, ℂ)) :=
  MonoidHom.range scaleDilationSL2CHom

@[simp]
theorem scaleDilationSL2CHom_apply (μ : PositiveScale) :
    scaleDilationSL2CHom μ = dilationSL2C μ.1 μ.2 := rfl

/-- **[The unit scale is the identity boost]**. -/
@[simp]
theorem scaleDilationSL2CHom_one :
    scaleDilationSL2CHom (1 : PositiveScale) = 1 :=
  map_one scaleDilationSL2CHom

/-- **[Reciprocal scaling is the inverse boost]**. Expansion by `μ` and contraction by
`μ⁻¹` are inverse elements of the celestial `SL(2,ℂ)` subgroup. -/
@[simp]
theorem scaleDilationSL2CHom_inv (μ : PositiveScale) :
    scaleDilationSL2CHom μ⁻¹ = (scaleDilationSL2CHom μ)⁻¹ :=
  map_inv scaleDilationSL2CHom μ

/-- **[The represented Möbius actions compose]**. Multiplication in the bundled positive
scale group becomes successive dilation of every finite point of the celestial sphere. -/
/- ZIL-BEGIN -/
@[zil_claim physlib.schwarzschild.positiveScaleMobiusComposition,
  zil_concept mathematics.positiveScaleSL2C, zil_level structural, zil_export]
/- ZIL-END -/
theorem scaleDilationSL2CHom_mul_mobius (μ ν : PositiveScale) (w : ℂ) :
    (scaleDilationSL2CHom (μ * ν)).toGL • (w : OnePoint ℂ)
      = ((μ.1 * (ν.1 * w) : ℂ) : OnePoint ℂ) := by
  change (dilationSL2C (μ.1 * ν.1) (mul_pos μ.2 ν.2)).toGL • (w : OnePoint ℂ)
    = ((μ.1 * (ν.1 * w) : ℂ) : OnePoint ℂ)
  rw [dilationSL2C_mobius (μ.1 * ν.1) (mul_pos μ.2 ν.2)]
  congr 1
  rw [Complex.ofReal_mul]
  ring

/-! ### §E Multi-bit ER=EPR entanglement is a ladder of factor-2 dilations -/

/-- **The entropy assigned to `n` independent bits**, `Sₙ = k_B n log 2`. This is an
information-theoretic definition. It does not assert the existence of a Schwarzschild solution
or a generalized `n`-bit wormhole mass. Such a mass law would require separate physical input
and a separate theorem connecting it to `bhEntropy`. -/
noncomputable def nBitErEprEntropy (n : ℕ) (kB : ℝ) : ℝ :=
  kB * (n : ℝ) * Real.log 2

/-- **[`n`-bit entropy is the length of `n` binary scale steps]**
`Sₙ = k_B·scaleDistance(2ⁿ,1)`. This proves an exact identity between the explicitly
defined information entropy and the block-spin scale ladder. It deliberately makes no
generalized mass claim. -/
/- ZIL-BEGIN -/
@[zil_claim physlib.schwarzschild.nBitEntropyScaleLadder,
  zil_concept physics.informationScaleIdentity, zil_level bridge_theorem, zil_export]
/- ZIL-END -/
theorem erEpr_nbit_entropy_eq_scaleDistance (n : ℕ) (kB : ℝ) :
    nBitErEprEntropy n kB = kB * scaleDistance (2 ^ n) 1 := by
  have h := blockspin_ladder n 1 one_pos
  rw [mul_one] at h
  rw [h]
  unfold nBitErEprEntropy
  ring

/-- The same result in the arithmetic form `Sₙ = k_B n log 2`, exposed separately
from the geometric scale-distance theorem. -/
theorem nBitErEprEntropy_eq (n : ℕ) (kB : ℝ) :
    nBitErEprEntropy n kB = kB * ((n : ℝ) * Real.log 2) := by
  unfold nBitErEprEntropy
  ring

/-! ### §F Conservative synthesis of the proved one-bit identities -/

/-- The formally closed one-bit package: the selected mass has entropy equal to one
binary scale step, and the corresponding factor-2 diagonal element acts by `w ↦ 2w`
on finite coordinates while fixing infinity. This conjunction composes the proved
equalities without asserting a dynamical map from entanglement to horizon dilation. -/
/- ZIL-BEGIN -/
@[zil_claim physlib.schwarzschild.oneBitEntropyScaleMobiusSynthesis,
  zil_concept physics.schwarzschildHorizon, zil_requires assumptions.positivePhysicalConstants,
  zil_level bridge_theorem, zil_export]
/- ZIL-END -/
theorem oneBitEntropy_scale_mobius_synthesis
    (G c ℏ kB : ℝ) (hG : 0 < G) (hc : 0 < c) (hℏ : 0 < ℏ) :
    bhEntropy (Real.sqrt (ℏ * c * Real.log 2 / (4 * Real.pi * G))) G c ℏ kB
        = kB * scaleDistance 2 1
      ∧ (∀ w : ℂ,
        (dilationSL2C 2 (by norm_num)).toGL • (w : OnePoint ℂ)
          = ((2 * w : ℂ) : OnePoint ℂ))
      ∧ (dilationSL2C 2 (by norm_num)).toGL •
          (OnePoint.infty : OnePoint ℂ) = OnePoint.infty := by
  exact ⟨erEpr_entropy_eq_scaleDistance G c ℏ kB hG hc hℏ,
    dilationSL2C_mobius 2 (by norm_num), dilationSL2C_mobius_infty 2 (by norm_num)⟩

/-! ### §G The complete typed Schwarzschild-horizon chain -/

/-- **[The complete formal chain]** from Barletta's angular radius through the
one-bit entropy and the celestial Möbius dilation.

The theorem retains every intermediate equality with its own type:

1. Barletta's transverse function satisfies `a(r_B) = r_B`;
2. the Barletta horizon coordinate `r_B = 2GM₁/c²` is the Schwarzschild radius `R_g`;
3. the Schwarzschild area is the sphere area at `R_g`;
4. that sphere area is `4π a(r_B)²`;
5. the mass- and radius-based Bekenstein–Hawking entropy formulas agree;
6. at the selected mass `M₁`, the entropy is `k_B log 2`;
7. this equals `k_B·scaleDistance(2,1)`;
8. the corresponding diagonal `SL(2,ℂ)` element acts by `w ↦ 2w` on finite
   points and fixes infinity.

The last two facts share the factor `2`, but the theorem deliberately asserts no
causal or dynamical identification between entanglement and horizon rescaling. -/
/-
@zil target=self
self#formalizes@claim:schwarzschild-one-bit-entire-chain.
self#requires@assumption:positive-physical-constants.
self#supported_by@paper:dai-minic-stojkovic-fu-2020.
self#supported_by@paper:barletta-dragomir-magliaro-2014.
self#caveat@claim:no-dynamical-entanglement-to-horizon-dilation.
self#requires_check@check:lean_compile.
@endzil
-/
/- ZIL-BEGIN -/
@[zil_claim physlib.schwarzschild.oneBitEntireChain,
  zil_concept physics.schwarzschildHorizon, zil_requires assumptions.positivePhysicalConstants,
  zil_level bridge_theorem, zil_export]
/- ZIL-END -/
theorem schwarzschildHorizon_oneBit_entire_chain
    (G c ℏ kB : ℝ) (hG : 0 < G) (hc : 0 < c) (hℏ : 0 < ℏ) :
    let M₁ := Real.sqrt (ℏ * c * Real.log 2 / (4 * Real.pi * G))
    let rB := 2 * (G * M₁ / c ^ 2)
    let Rg := Physlib.Relativity.SemiClassical.schwarzschildRadius M₁ G c
    barlettaA rB = rB
      ∧ rB = Rg
      ∧ Physlib.Relativity.SemiClassical.schwarzschildArea M₁ G c = sphereArea Rg
      ∧ sphereArea Rg = 4 * Real.pi * (barlettaA rB) ^ 2
      ∧ bhEntropy M₁ G c ℏ kB = horizonBhEntropy Rg G c ℏ kB
      ∧ bhEntropy M₁ G c ℏ kB = kB * Real.log 2
      ∧ kB * Real.log 2 = kB * scaleDistance 2 1
      ∧ (∀ w : ℂ,
        (dilationSL2C 2 (by norm_num)).toGL • (w : OnePoint ℂ)
          = ((2 * w : ℂ) : OnePoint ℂ))
      ∧ (dilationSL2C 2 (by norm_num)).toGL •
          (OnePoint.infty : OnePoint ℂ) = OnePoint.infty := by
  dsimp only
  have hr :=
    barlettaHorizonRadius_eq_schwarzschildRadius
      (Real.sqrt (ℏ * c * Real.log 2 / (4 * Real.pi * G))) G c
  refine ⟨rfl, hr, schwarzschildArea_eq_sphereArea _ G c hc.ne', ?_,
    bhEntropy_eq_horizonBhEntropy _ G c ℏ kB hc.ne',
    erEpr_wormholeMass G c ℏ kB hG hc hℏ, ?_,
    dilationSL2C_mobius 2 (by norm_num), dilationSL2C_mobius_infty 2 (by norm_num)⟩
  · rw [← hr]
    simp only [sphereArea, barlettaA]
  · rw [scaleDistance_two_one]

/-- **[The independently fixed inference-variance coupling enters the entire
one-bit Schwarzschild horizon chain].**  A `G`-free Compton-cell tiling fixes
`G = ℏcσ₀⁴`; the existing horizon theorem then transports that same coupling
through Schwarzschild radius and area, Bekenstein--Hawking entropy, the one-bit
scale distance, and the diagonal `SL(2,ℂ)` Möbius action.

The inference screen used to determine `G` and the one-bit Schwarzschild horizon
are not identified geometrically.  Nor does this theorem determine `σ₀` from data
or convert the ER=EPR inversion into an independent mass prediction. -/
theorem comptonCellInference_schwarzschildHorizon_oneBit_entire_chain
    (c ℏ kB σ₀ η : ℝ)
    (hc : 0 < c) (hℏ : 0 < ℏ) (hσ : 0 < σ₀) (hη : 0 < η) :
    let m := inferenceMass σ₀
    let RI := entropicProperDistance m c ℏ η
    let N := comptonCellBits m c ℏ η
    let G := ℏ * c * σ₀ ^ 4
    let M₁ := Real.sqrt (ℏ * c * Real.log 2 / (4 * Real.pi * G))
    let rB := 2 * (G * M₁ / c ^ 2)
    let Rg := Physlib.Relativity.SemiClassical.schwarzschildRadius M₁ G c
    G = sphereArea RI * c ^ 3 / (ℏ * N)
      ∧ barlettaA rB = rB
      ∧ rB = Rg
      ∧ Physlib.Relativity.SemiClassical.schwarzschildArea M₁ G c = sphereArea Rg
      ∧ sphereArea Rg = 4 * Real.pi * (barlettaA rB) ^ 2
      ∧ bhEntropy M₁ G c ℏ kB = horizonBhEntropy Rg G c ℏ kB
      ∧ bhEntropy M₁ G c ℏ kB = kB * Real.log 2
      ∧ kB * Real.log 2 = kB * scaleDistance 2 1
      ∧ (∀ w : ℂ,
        (dilationSL2C 2 (by norm_num)).toGL • (w : OnePoint ℂ) =
          ((2 * w : ℂ) : OnePoint ℂ))
      ∧ (dilationSL2C 2 (by norm_num)).toGL •
          (OnePoint.infty : OnePoint ℂ) = OnePoint.infty := by
  dsimp only
  have hG : 0 < ℏ * c * σ₀ ^ 4 := by positivity
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    ne_of_gt (Real.log_pos (schmidtNumber_gt_one η hη))
  have hArea :=
    (newtonG_from_positionVariance σ₀ c ℏ η hσ.ne' hc.ne' hℏ.ne' hlog).symm
  exact ⟨hArea,
    schwarzschildHorizon_oneBit_entire_chain
      (ℏ * c * σ₀ ^ 4) c ℏ kB hG hc hℏ⟩

/- ZIL-BEGIN -/
#zil_validate_embedded schwarzschildHorizon_oneBit_entire_chain where
  no_sorry, claim_linked, requirement_linked, type_fingerprint "lean-hash:333771888"

/-! ### §H Formalization-accountability contract -/

zil_theorem_intent schwarzschildHorizon_oneBit_entire_chain where
  at_level bridge_theorem
  must_mention [
    barlettaA,
    Physlib.Relativity.SemiClassical.schwarzschildRadius,
    Physlib.Relativity.SemiClassical.schwarzschildArea,
    sphereArea,
    bhEntropy,
    horizonBhEntropy,
    scaleDistance,
    dilationSL2C
  ]

zil_theorem_intent comptonCellInference_schwarzschildHorizon_oneBit_entire_chain where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCellBits,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.inferenceMass,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    bhEntropy,
    horizonBhEntropy,
    scaleDistance,
    dilationSL2C
  ]

zil_file_contract physlib.schwarzschildHorizonScaleMobius where
  promises "formalization:schwarzschild-horizon-scale-mobius-chain"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric.barlettaA",
    "lean:Physlib.Relativity.SemiClassical.schwarzschildRadius",
    "lean:Physlib.Relativity.SemiClassical.schwarzschildArea",
    "lean:Physlib.Thermodynamics.sphereArea",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric.bhEntropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.horizonBhEntropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.scaleDistance",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.dilationSL2C",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.schwarzschildHorizon_oneBit_entire_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.comptonCellInference_schwarzschildHorizon_oneBit_entire_chain"
  ]
  forbids_substitutes [
    "a prose-only Schwarzschild/entropy/Mobius connection",
    "a generalized n-bit physical mass theorem",
    "a dynamical identification of entanglement with horizon dilation"
  ]
  witnessed_by [schwarzschildHorizon_oneBit_entire_chain,
    comptonCellInference_schwarzschildHorizon_oneBit_entire_chain]

#zil_formalization_lint physlib.schwarzschildHorizonScaleMobius

/-! ### §I Native ZIL claim graph -/

zil attach horizonBhEntropy_dilation where
  formalizes @ "claim:horizon-entropy-scale-covariance",
  supported_by @ "definition:bekenstein-hawking-entropy"

zil attach bhEntropy_eq_horizonBhEntropy where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric.schwarzschildArea_eq_sphereArea",
  formalizes @ "claim:mass-radius-entropy-agreement",
  requires @ "assumption:light-speed-nonzero"

zil attach erEpr_entropy_eq_scaleDistance where
  formalizes @ "claim:one-bit-entropy-scale-identity",
  requires @ "assumption:positive-physical-constants",
  supported_by @ "paper:dai-minic-stojkovic-fu-2020",
  caveat @ "claim:value-identity-not-dynamical-dilation"

zil attach scaleDilationSL2CHom_mul_mobius where
  formalizes @ "claim:positive-scale-mobius-composition",
  requires @ "structure:positive-scale-group",
  supported_by @ "definition:scale-dilation-sl2c-hom"

zil attach erEpr_nbit_entropy_eq_scaleDistance where
  supported_by @ "lean:ScaleLine.blockspin_ladder",
  formalizes @ "claim:n-bit-entropy-scale-ladder",
  requires @ "definition:n-bit-er-epr-entropy",
  caveat @ "claim:no-generalized-n-bit-mass-law"

zil attach oneBitEntropy_scale_mobius_synthesis where
  supported_by @ "lean:erEpr_entropy_eq_scaleDistance",
  formalizes @ "claim:one-bit-entropy-scale-mobius-synthesis",
  requires @ "claim:one-bit-entropy-scale-identity",
  requires @ "claim:positive-scale-mobius-composition",
  caveat @ "claim:no-dynamical-entanglement-to-horizon-dilation"

zil attach schwarzschildHorizon_oneBit_entire_chain where
  formalizes @ "claim:schwarzschild-one-bit-entire-chain",
  requires @ "claim:barletta-horizon-radius",
  requires @ "claim:schwarzschild-area-sphere-area",
  requires @ "claim:mass-radius-entropy-agreement",
  requires @ "claim:one-bit-entropy-scale-identity",
  requires @ "claim:positive-scale-mobius-composition",
  supported_by @ "paper:dai-minic-stojkovic-fu-2020",
  supported_by @ "paper:barletta-dragomir-magliaro-2014",
  caveat @ "claim:no-dynamical-entanglement-to-horizon-dilation"

zil attach comptonCellInference_schwarzschildHorizon_oneBit_entire_chain where
  formalizes @ "claim:independent-compton-cell-inference-coupling-drives-the-one-bit-schwarzschild-entropy-scale-and-mobius-chain",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.schwarzschildHorizon_oneBit_entire_chain",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  caveat @ "claim:the-inference-screen-that-fixes-G-is-not-identified-with-the-one-bit-schwarzschild-horizon",
  caveat @ "claim:the-er-epr-one-bit-mass-remains-an-inversion-not-an-independent-mass-prediction",
  caveat @ "epistemic:sigma0-must-be-fixed-independently-rather-than-fitted-to-the-measured-G"

zil_rule schwarzschildClaimRequirement:
  ?claim # requires_claim @ ?requirement IF
  ?declaration # formalizes @ ?claim AND
  ?declaration # requires @ ?requirement

zil_rule schwarzschildClaimEvidence:
  ?claim # supported_by @ ?source IF
  ?declaration # formalizes @ ?claim AND
  ?declaration # supported_by @ ?source

zil_rule schwarzschildClaimCaveat:
  ?claim # has_caveat @ ?caveat IF
  ?declaration # formalizes @ ?claim AND
  ?declaration # caveat @ ?caveat
/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius

end

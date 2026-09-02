/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexSaddleEntropicWeight
public import Physlib.Thermodynamics.HolographicPrinciple
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Lorentzian condition: nucleation saddles on the imaginary-`K` contour

Formalizes the saddle-point core of Bousso–Hawking, *Lorentzian Condition in Quantum
Gravity* (arXiv:hep-th/9807148), on the repository's complex-saddle carriers: the wave
function of the universe in the extrinsic-curvature representation, `Ψ(K) = e^{−I(K)}`,
with the **Lorentzian condition** — `K` purely imaginary — implemented as the
imaginary-`K` contour of a single complex saddle action:

* `deSitterSaddleAction` (Eq. (2.11)) and `nariaiSaddleAction` (Eq. (3.17)), one `cpow`
  expression each; on the real (Euclidean) axis both are real
  (`deSitterSaddleAction_euclidean`, `nariaiSaddleAction_euclidean`), recovering the
  paper's real-`K` branch and `Ψ(0) = exp(3π/2Λ)` (Eq. (2.13));
* `deSitterSaddleAction_lorentzian_re`, `nariaiSaddleAction_lorentzian_re` — **the
  Lorentzian condition theorem**: up the imaginary-`K` axis (`K = ik`, `k² < 1`) the
  real part of the action is *constant* (`−3π/2Λ`, resp. `−π/Λ`) — only the phase
  varies: the amplitude stays at its `K = 0` (half-instanton) value while the wave
  function oscillates, the paper's criterion for a Lorentzian geometry near `Σ`;
* `deSitter_amplitude_constant`, `nariai_amplitude_constant` — `‖e^{−I}‖` along the
  contour, by the existing saddle-weight lemma
  `ComplexSaddleEntropicWeight.cexp_neg_modulus_eq_exp_neg_re`: the probability measure
  depends only on `Re I`, which stems from the Euclidean sector;
* `nariai_pair_creation_rate` (Eq. (3.19)) — `Γ_N = |Ψ_N|²/|Ψ_dS|² = exp(−π/Λ)` for
  *any* pair of points on the two Lorentzian contours: the rate is contour-independent
  because both amplitudes are;
* `pair_creation_rate_eq_entropy_deficit` — the modern reading, welded to the
  Bekenstein–Hawking modules: in Planck units the rate is `exp(S_Nariai − S_dS)` with
  `S_dS = 3π/Λ` the de Sitter horizon entropy and `S_N = 2·(π/Λ)` the two Nariai
  horizons, both carried by `microstateEntropy (holographicBits …)` — black-hole pair
  creation is suppressed by exactly the horizon-entropy deficit;
* `scaleFactor_hasDerivAt`, `nucleation_surface` (Eqs. (2.9)–(2.10)) — the Euclidean
  four-sphere profile `a(τ̂) = R₀ sin(τ̂/R₀)` has `ȧ = cos(τ̂/R₀)`, and at the equator
  `τ̂ = (π/2)R₀` the slice is the maximal three-sphere `a = R₀` with `K = ȧ/a = 0`:
  the joining surface to the Lorentzian branch is exactly the `K = 0` point where the
  two contour branches of §A meet.  (`K = ȧ/a` is the Euclidean face of
  `Cosmology.hubbleConstant = ∂ₜa/a`.)

**Honest layering.**  Exact algebra of the saddle actions on the two axes where
`1 + K²` is a positive real, so the `cpow` is single-valued — the paper's own contours;
the general complex-`K` branch structure, the minisuperspace path integral behind
Eq. (1.4), the Laplace transform (1.3), and the §4 sub-maximal (conical-deficit)
instantons are not formalized.  Prefactors are neglected as in the paper.

## References

* R. Bousso and S. W. Hawking, *Lorentzian Condition in Quantum Gravity*,
  arXiv:hep-th/9807148.  Eqs. (2.9)–(2.13), (3.17)–(3.19).
* Carrier reuse: `ComplexSaddleEntropicWeight` (`cexp_neg_modulus_eq_exp_neg_re`),
  `Thermodynamics.HolographicScreenEntropy` / `HorizonCell.CellBondDimension`
  (`microstateEntropy`, `holographicBits`), `VerlindeNewtonGravity` (`sphereArea`),
  `Cosmology.FLRW.Basic` (`hubbleConstant`, cited).
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComplexSaddleEntropicWeight
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LorentzianConditionNucleation

/-! ## §A — the two saddle actions and their Euclidean (real) branches -/

/-- **The de Sitter saddle action** `I_dS(K)` (Eq. (2.11)): the Euclidean action of the
complex four-sphere solution bounded by a round three-sphere of extrinsic curvature `K`. -/
noncomputable def deSitterSaddleAction (Λ : ℝ) (K : ℂ) : ℂ :=
  -((3 * Real.pi / (2 * Λ) : ℝ) : ℂ) *
    (1 - (3 + 2 * K ^ 2) * K / (2 * (1 + K ^ 2) ^ ((3 : ℂ) / 2)))

/-- **The Nariai saddle action** `I_N(K)` (Eq. (3.17)): the `S² × S²` instanton bounded
by an `S¹ × S²` slice of extrinsic curvature `K`. -/
noncomputable def nariaiSaddleAction (Λ : ℝ) (K : ℂ) : ℂ :=
  -((Real.pi / Λ : ℝ) : ℂ) * (1 - K / (1 + K ^ 2) ^ ((1 : ℂ) / 2))

/-- On the real (Euclidean) axis the de Sitter action is real, and equals the paper's
Eq. (2.11) with the real `3/2`-power. -/
theorem deSitterSaddleAction_euclidean (Λ K : ℝ) :
    deSitterSaddleAction Λ (K : ℂ) =
      ((-(3 * Real.pi / (2 * Λ)) *
        (1 - (3 + 2 * K ^ 2) * K / (2 * (1 + K ^ 2) ^ ((3 : ℝ) / 2)))) : ℝ) := by
  unfold deSitterSaddleAction
  have h1 : ((1 : ℂ) + (K : ℂ) ^ 2) = ((1 + K ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, show ((3 : ℂ) / 2) = (((3 : ℝ) / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity) ((3 : ℝ) / 2)]
  push_cast
  ring

/-- On the real axis the Nariai action is real (Eq. (3.17) with the real square root). -/
theorem nariaiSaddleAction_euclidean (Λ K : ℝ) :
    nariaiSaddleAction Λ (K : ℂ) =
      ((-(Real.pi / Λ) * (1 - K / (1 + K ^ 2) ^ ((1 : ℝ) / 2))) : ℝ) := by
  unfold nariaiSaddleAction
  have h1 : ((1 : ℂ) + (K : ℂ) ^ 2) = ((1 + K ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity) ((1 : ℝ) / 2)]
  push_cast
  ring

/-- **The half-instanton value** `Ψ(0) = exp(3π/2Λ)` (Eq. (2.13)): at `K = 0` the saddle
is half the Euclidean four-sphere. -/
theorem deSitterSaddleAction_zero (Λ : ℝ) :
    deSitterSaddleAction Λ 0 = ((-(3 * Real.pi / (2 * Λ)) : ℝ) : ℂ) := by
  have h := deSitterSaddleAction_euclidean Λ 0
  simpa using h

/-! ## §B — the Lorentzian condition: constant amplitude up the imaginary-`K` axis -/

/-- **The Lorentzian condition, de Sitter** — up the imaginary-`K` axis (`K = ik`,
`k² < 1`) only the imaginary part of Eq. (2.11) changes: the real part is the constant
`−3π/(2Λ)`, the `K = 0` half-instanton value.  The amplitude of the wave function is
frozen while its phase varies — the mark of a Lorentzian geometry near `Σ`. -/
theorem deSitterSaddleAction_lorentzian_re (Λ k : ℝ) (hk : k ^ 2 < 1) :
    (deSitterSaddleAction Λ (Complex.I * k)).re = -(3 * Real.pi / (2 * Λ)) := by
  unfold deSitterSaddleAction
  have h1 : ((1 : ℂ) + (Complex.I * k) ^ 2) = ((1 - k ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  rw [h1, show ((3 : ℂ) / 2) = (((3 : ℝ) / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by linarith) ((3 : ℝ) / 2)]
  have h2 : (3 + 2 * (Complex.I * k) ^ 2) * (Complex.I * k) /
        (2 * ((((1 - k ^ 2) ^ ((3 : ℝ) / 2) : ℝ)) : ℂ)) =
      Complex.I * (((3 - 2 * k ^ 2) * k / (2 * (1 - k ^ 2) ^ ((3 : ℝ) / 2)) : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [h2]
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The Lorentzian condition, Nariai** — the real part of Eq. (3.17) along the
imaginary-`K` contour is the constant `−π/Λ`. -/
theorem nariaiSaddleAction_lorentzian_re (Λ k : ℝ) (hk : k ^ 2 < 1) :
    (nariaiSaddleAction Λ (Complex.I * k)).re = -(Real.pi / Λ) := by
  unfold nariaiSaddleAction
  have h1 : ((1 : ℂ) + (Complex.I * k) ^ 2) = ((1 - k ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  rw [h1, show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by linarith) ((1 : ℝ) / 2)]
  have h2 : (Complex.I * k) / ((((1 - k ^ 2) ^ ((1 : ℝ) / 2) : ℝ)) : ℂ) =
      Complex.I * ((k / (1 - k ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h2]
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The de Sitter amplitude is frozen along the Lorentzian contour** — by the
saddle-weight lemma, `‖e^{−I}‖ = e^{−Re I}` depends only on the Euclidean sector, and
`Re I` is constant: the amplitude keeps its `K = 0` value `exp(3π/2Λ)` (Eq. (2.13)) at
every point of the contour. -/
theorem deSitter_amplitude_constant (Λ k : ℝ) (hk : k ^ 2 < 1) :
    ‖Complex.exp (-(deSitterSaddleAction Λ (Complex.I * k)))‖ =
      Real.exp (3 * Real.pi / (2 * Λ)) := by
  rw [cexp_neg_modulus_eq_exp_neg_re _ 1 one_ne_zero,
    deSitterSaddleAction_lorentzian_re Λ k hk, neg_neg]

/-- **The Nariai amplitude is frozen along its Lorentzian contour** at `exp(π/Λ)`. -/
theorem nariai_amplitude_constant (Λ k : ℝ) (hk : k ^ 2 < 1) :
    ‖Complex.exp (-(nariaiSaddleAction Λ (Complex.I * k)))‖ = Real.exp (Real.pi / Λ) := by
  rw [cexp_neg_modulus_eq_exp_neg_re _ 1 one_ne_zero,
    nariaiSaddleAction_lorentzian_re Λ k hk, neg_neg]

/-! ## §C — the pair creation rate and its entropy-deficit form -/

/-- **The Nariai pair creation rate** (Eq. (3.19)):
`Γ_N = Ψ*_N Ψ_N / Ψ*_dS Ψ_dS = exp(−π/Λ)` — for *any* pair of points on the two
Lorentzian contours, because both amplitudes are contour-constant: the probability
measure depends only on the real, Euclidean part of the saddle actions. -/
theorem nariai_pair_creation_rate (Λ k₁ k₂ : ℝ) (h₁ : k₁ ^ 2 < 1) (h₂ : k₂ ^ 2 < 1) :
    ‖Complex.exp (-(nariaiSaddleAction Λ (Complex.I * k₁)))‖ ^ 2 /
      ‖Complex.exp (-(deSitterSaddleAction Λ (Complex.I * k₂)))‖ ^ 2 =
      Real.exp (-Real.pi / Λ) := by
  rw [nariai_amplitude_constant Λ k₁ h₁, deSitter_amplitude_constant Λ k₂ h₂,
    sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

/-- **The rate is the horizon-entropy deficit** — the weld to the Bekenstein–Hawking
modules: in Planck units (`G = ℏ = c = 1`) the de Sitter horizon `R = √(3/Λ)` carries
`S_dS = 3π/Λ` and the two Nariai horizons `R = 1/√Λ` carry `S_N = 2·(π/Λ)`, both as
`microstateEntropy (holographicBits …)`; the pair creation rate `exp(−π/Λ)` is exactly
`exp(S_N − S_dS)` — nucleating the black-hole pair costs the entropy the horizons
lose. -/
theorem pair_creation_rate_eq_entropy_deficit (Λ : ℝ) (hΛ : 0 < Λ) :
    Real.exp (-Real.pi / Λ) =
      Real.exp
        (2 * microstateEntropy (holographicBits (sphereArea (1 / Real.sqrt Λ)) 1 1 1)
          - microstateEntropy (holographicBits (sphereArea (Real.sqrt (3 / Λ))) 1 1 1)) := by
  congr 1
  rw [microstateEntropy_eq_quarter, microstateEntropy_eq_quarter]
  unfold holographicBits sphereArea
  rw [div_pow, one_pow, Real.sq_sqrt hΛ.le, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 3 / Λ)]
  ring

/-! ## §D — the Euclidean four-sphere profile and the nucleation surface -/

/-- **The scale factor of the Euclidean four-sphere** `a(τ̂) = R₀ sin(τ̂/R₀)`
(Eq. (2.9)) has `ȧ(τ̂) = cos(τ̂/R₀)` — the numerator of `K = ȧ/a` (Eq. (2.10), the
Euclidean face of `Cosmology.hubbleConstant`). -/
theorem scaleFactor_hasDerivAt (R₀ τ : ℝ) (hR : R₀ ≠ 0) :
    HasDerivAt (fun t : ℝ => R₀ * Real.sin (t / R₀)) (Real.cos (τ / R₀)) τ := by
  have hs : HasDerivAt (fun t : ℝ => t / R₀) (1 / R₀) τ := (hasDerivAt_id τ).div_const R₀
  have hval : Real.cos (τ / R₀) = R₀ * (Real.cos (τ / R₀) * (1 / R₀)) := by
    field_simp
  rw [hval]
  exact ((Real.hasDerivAt_sin (τ / R₀)).comp τ hs).const_mul R₀

/-- **The nucleation surface is the equator** — at `τ̂ = (π/2)·R₀` the slice is the
maximal three-sphere `a = R₀` and the expansion rate vanishes: `K = ȧ/a = 0`, exactly
the `K = 0` point where the Euclidean branch (§A) hands over to the Lorentzian contour
(§B) with amplitude `exp(3π/2Λ)`. -/
theorem nucleation_surface (R₀ : ℝ) (hR : 0 < R₀) :
    R₀ * Real.sin (Real.pi / 2 * R₀ / R₀) = R₀ ∧
    deriv (fun t : ℝ => R₀ * Real.sin (t / R₀)) (Real.pi / 2 * R₀) = 0 := by
  constructor
  · rw [mul_div_assoc, div_self hR.ne', mul_one, Real.sin_pi_div_two, mul_one]
  · rw [(scaleFactor_hasDerivAt R₀ (Real.pi / 2 * R₀) hR.ne').deriv,
      mul_div_assoc, div_self hR.ne', mul_one, Real.cos_pi_div_two]

/-! ## §E — Sabir complex `SU(2)` Yang–Mills–Higgs bounce: the conjugate-pair complex Euclidean action

Sabir and Ajithkumar, *Complex `SU(2)` Yang–Mills–Higgs configurations with finite, complex
Euclidean actions* (J. Phys. G: Nucl. Phys. **9** (1983) 1469), exhibit a pair of exact,
complex-conjugate solutions of the Prasad–Sommerfield `SU(2)` Yang–Mills–Higgs system whose
Euclidean actions are finite and complex.  Like the Bousso–Hawking nucleation saddle of §A–§C
this is a de Sitter **bounce** (vacuum `A = 0`, `φ = 0` at infinity, Coleman 1979) whose
path-integral weight `e^{−S}` has modulus fixed by the real part of the complex action — reusing
the same `cexp_neg_modulus_eq_exp_neg_re` as the Lorentzian-condition amplitudes above. -/

/-- **The `(4a)` source** `K(K² − 1 + H²)` of the Julia–Zee reduced Yang–Mills equation
(Sabir Eq. (4a)). -/
def juliaZeeSourceK (K H : ℝ) : ℝ := K * (K ^ 2 - 1 + H ^ 2)

/-- **The `(4b)` source** `2HK²` of the Higgs reduced equation (Sabir Eq. (4b)). -/
def juliaZeeSourceH (K H : ℝ) : ℝ := 2 * H * K ^ 2

/-- **The single reduced source** `2K²(K − 1)` (Sabir Eq. (8)). -/
def reducedSource (K : ℝ) : ℝ := 2 * K ^ 2 * (K - 1)

/-- **The substitution `K = 1 − H` collapses the gauge equation** — with `H = 1 − K` the
`(4a)` source becomes exactly the single reduced source `2K²(K − 1)` (Sabir Eq. (7) → (8)). -/
theorem juliaZee_reduction_K (K : ℝ) : juliaZeeSourceK K (1 - K) = reducedSource K := by
  unfold juliaZeeSourceK reducedSource; ring

/-- **`K = 1 − H` collapses the Higgs equation too** — the `(4b)` source at `H = 1 − K` is
minus the reduced source; together with `∇²H = −∇²K` this reproduces the same Eq. (8), so a
single non-linear equation governs both fields. -/
theorem juliaZee_reduction_H (K : ℝ) : juliaZeeSourceH K (1 - K) = -reducedSource K := by
  unfold juliaZeeSourceH reducedSource; ring

/-- **The two reduced sources are consistent under `K = 1 − H`** — their sum vanishes, the
algebraic content of Sabir Eq. (7): the gauge and Higgs equations coincide. -/
theorem juliaZee_reduction_consistent (K : ℝ) :
    juliaZeeSourceK K (1 - K) + juliaZeeSourceH K (1 - K) = 0 := by
  rw [juliaZee_reduction_K, juliaZee_reduction_H]; ring

/-- **The complex coupling `a`** of the trial solution (Sabir Eq. (10)),
`a = −⅛(1 + ε i√8)` for the sign `ε = ±1`. -/
noncomputable def sabirA (ε : ℝ) : ℂ :=
  -(1 / 8) * (1 + (ε : ℂ) * Complex.I * (Real.sqrt 8 : ℂ))

/-- **The complex coupling `b`** of the trial solution (Sabir Eq. (10)),
`b = −⅛(7 − 2ε i√8)` — the `∓` of the paper paired with `a`'s `±`. -/
noncomputable def sabirB (ε : ℝ) : ℂ :=
  -(1 / 8) * (7 - 2 * (ε : ℂ) * Complex.I * (Real.sqrt 8 : ℂ))

/-- **`a` conjugates to the opposite-sign root** `ā(ε) = a(−ε)`: the two Eq. (10) choices are
complex conjugates. -/
theorem sabirA_conj (ε : ℝ) : (starRingEnd ℂ) (sabirA ε) = sabirA (-ε) := by
  simp only [sabirA, map_neg, map_mul, map_add, map_one, map_div₀, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- **`b` conjugates to the opposite-sign root** `b̄(ε) = b(−ε)`. -/
theorem sabirB_conj (ε : ℝ) : (starRingEnd ℂ) (sabirB ε) = sabirB (-ε) := by
  simp only [sabirB, map_neg, map_mul, map_add, map_sub, map_one, map_div₀, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- **The coupling difference `a − b`** (the `8π²(a−b)²` prefactor of the action integral,
Sabir Eq. (12)) is `(6 − 3ε i√8)/8`. -/
theorem sabirA_sub_sabirB (ε : ℝ) :
    sabirA ε - sabirB ε = (6 - 3 * (ε : ℂ) * Complex.I * (Real.sqrt 8 : ℂ)) / 8 := by
  unfold sabirA sabirB; ring

/-- **The trial gauge profile** `K(r, t)` (Sabir Eq. (9)):
`K = (4a r² + (1 + r² + t²)²)/(4b r² + (1 + r² + t²)²)`. -/
noncomputable def sabirTrialK (a b : ℂ) (r t : ℝ) : ℂ :=
  (4 * a * (r : ℂ) ^ 2 + ((1 + r ^ 2 + t ^ 2 : ℝ) : ℂ) ^ 2) /
    (4 * b * (r : ℂ) ^ 2 + ((1 + r ^ 2 + t ^ 2 : ℝ) : ℂ) ^ 2)

/-- **Regularity at the origin** `K → 1` as `r → 0` (Sabir Eq. (5)): the `r²` terms drop and
numerator equals denominator. -/
theorem sabirTrialK_regular (a b : ℂ) (t : ℝ) : sabirTrialK a b 0 t = 1 := by
  have hpos : (0 : ℝ) < 1 + (0 : ℝ) ^ 2 + t ^ 2 := by positivity
  have hnz : ((1 + (0 : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hpos.ne')
  unfold sabirTrialK
  rw [Complex.ofReal_zero,
    show (4 * a * (0 : ℂ) ^ 2 + ((1 + (0 : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) ^ 2)
        = ((1 + (0 : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) ^ 2 by ring,
    show (4 * b * (0 : ℂ) ^ 2 + ((1 + (0 : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) ^ 2)
        = ((1 + (0 : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) ^ 2 by ring]
  exact div_self hnz

/-- **The Higgs profile vanishes at the origin** `H = 1 − K → 0` as `r → 0` (Sabir Eq. (5)),
consistent with the substitution `K = 1 − H`. -/
theorem sabirTrialH_regular (a b : ℂ) (t : ℝ) : 1 - sabirTrialK a b 0 t = 0 := by
  rw [sabirTrialK_regular]; ring

/-- **The action integrand** of Sabir Eq. (12):
`8π²(a−b)² · ρ²/(bρ²+1)⁴ · [10 + 2(2a+b−3)ρ² + ⅓(3a²+b²+2ab)ρ⁴]`, whose `∫₀¹ dρ` is the
finite complex action. -/
noncomputable def sabirActionIntegrand (a b : ℂ) (ρ : ℝ) : ℂ :=
  8 * ((Real.pi : ℝ) : ℂ) ^ 2 * (a - b) ^ 2 *
    ((ρ : ℂ) ^ 2 / (b * (ρ : ℂ) ^ 2 + 1) ^ 4) *
    (10 + 2 * (2 * a + b - 3) * (ρ : ℂ) ^ 2 +
      (1 / 3) * (3 * a ^ 2 + b ^ 2 + 2 * a * b) * (ρ : ℂ) ^ 4)

/-- **The action integrand is conjugation-covariant** — under `(a, b) ↦ (ā, b̄)` (with real
`ρ`) the integrand conjugates, so the two Eq. (10) solutions have complex-conjugate actions
(Sabir Eq. (12): `S ≈ −8π²(6.545 ± 9.89i)`). -/
theorem sabirActionIntegrand_conj (a b : ℂ) (ρ : ℝ) :
    (starRingEnd ℂ) (sabirActionIntegrand a b ρ) =
      sabirActionIntegrand ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) ρ := by
  simp only [sabirActionIntegrand, map_mul, map_add, map_sub, map_div₀, map_pow, map_one,
    map_ofNat, Complex.conj_ofReal]

/-- **The conjugate-pair actions carry the same bounce weight** — for any complex action `S`
its conjugate `S̄` gives the identical path-integral modulus `‖e^{−S}‖ = ‖e^{−S̄}‖`, because the
weight depends only on `Re S` (reusing `cexp_neg_modulus_eq_exp_neg_re`).  Sabir's
complex-conjugate solution pair therefore contributes with equal magnitude to the bounce, the
condition for both to be kept in the complex saddle-point sum. -/
theorem sabir_conjugate_action_same_weight (S : ℂ) :
    ‖Complex.exp (-S)‖ = ‖Complex.exp (-((starRingEnd ℂ) S))‖ := by
  rw [cexp_neg_modulus_eq_exp_neg_re S 1 one_ne_zero,
    cexp_neg_modulus_eq_exp_neg_re ((starRingEnd ℂ) S) 1 one_ne_zero, Complex.conj_re]

end Physlib.QuantumMechanics.ComplexAction.LorentzianConditionNucleation

end

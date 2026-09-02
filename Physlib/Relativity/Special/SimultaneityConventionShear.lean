/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Conventionality of simultaneity: synchrony shears and the tippe-top trajectory

Formalizes the exact kinematic core of Ghosal–Raychaudhuri–Chowdhury–Sarker,
*Conventionality of Simultaneity and the Tippe Top Paradox in Relativity*, Found. Phys.
Lett. **16** (2003) 549 (Eqs. (1)–(17)), on the repository's boost carriers:

* `spinning_coordinate`, `trajectory_ellipse`, `table_time_phase` (Eqs. (1)–(8)) — for
  *any* linear frame map `x⁰ = ax + bt`, `t⁰ = gx + ht`, the top's table-frame circle
  becomes the ellipse `a²x_s² + y_s² = R²` in spinning coordinates (`x_s = x⁰/a`), and
  the table time acquires the phase `t⁰ = g·x_s + (h − gb/a)·t`: the paper's **type I**
  distortion is carried entirely by the entry `a`, its **type II** (bow-shaped chains,
  "relativity of simultaneity") entirely by the entry `g`;
* the four frame maps as unimodular `2×2` matrices — `lorentzFrame` (Eqs. (9)–(10)),
  `tangherliniFrame` (Eq. (14)), `galileanFrame` (Eq. (15)), `zaharFrame`
  (Eqs. (16)–(17)) — all of determinant one (`*_det`);
* `synchronyShear` with `synchronyShear_mul` — resynchronizing distant clocks is the
  **parabolic** one-parameter family `[[1,0],[κ,1]]` (`t ↦ t + κx`, space untouched:
  `synchronyShear_fixes_space`), the third conjugacy class alongside the elliptic
  (`middleRotation`) and hyperbolic (`middleBoost`, `thermoBogoliubov`) subgroups of
  the repository's `SL(2)` decomposition modules;
* **the conventionality theorems**: `tangherlini_eq_lorentz_shear` — the Tangherlini
  map *is* the Lorentz boost times a synchrony shear, and its time row is
  `x`-independent (`tangherlini_absolute_simultaneity`): the type II effect is pure
  convention, removable by resynchronization; `zahar_eq_galilean_shear` and
  `zahar_manufactures_phase` — conversely, Einstein synchrony imported into the
  *Galilean* world (the Zahar map) manufactures a nonzero phase entry where no paradox
  can exist: the paper's refutation of resolving the tippe-top paradox by the lack of
  clock synchrony;
* `lorentz_ellipse` (Eq. (13)) and `tangherlini_ellipse` — the same top appears
  γ-contracted under Einstein synchrony and γ-elongated under absolute synchrony: even
  the type I "geometry" of the moving top is convention-laden;
* `lorentzFrame_eq_thermoBogoliubov` — the weld: at `c = 1` and rapidity
  parametrization (`γ = cosh η`, `β = tanh η`), the paper's Lorentz matrix *is* the
  repository's `thermoBogoliubov (−η)` (`ThermoFieldDynamics.TFDImaginaryPart`, the
  boost of the complex-delta contour arc), inheriting its unimodularity and Minkowski
  preservation (`thermoBogoliubov_det`, `rapidityBoost_preserves_minkowski`);
* the **entropic-distance welds** (§F): `boost_velocity_eq_vacuumBell_decay` — the
  rocket whose speed is the vacuum Bell decay `β = e^{−r/λ_C}` at the entropic proper
  distance (`EntropicProperDistance.entropicProperDistance_vacuumBell`) implements
  exactly the Bogoliubov boost of the entanglement rapidity;
  `tangherlini_resync_eq_vacuumBell` — the synchrony-shear parameter at that velocity
  is the same Bell decay: conventionality of simultaneity graded by entanglement;
  `tippeTop_ellipse_entanglement` — the top's type I ellipse coefficient satisfies
  `γ²(K² − 1) = K²` (`boost_sq_schmidt_relation`): the distortion is a function of the
  Schmidt number `K = e^{r/λ_C}` alone.

**Honest layering.**  Exact linear algebra and trigonometry; entropies of opinion none.
The paper's §§5–7 — the pseudo-standard synchrony (Eq. (18)), the detailed re-analysis
of the Basu et al. resolution, and the physical invariance of the tipping condition —
are its discursive layer, cited not formalized.  The tippe top's actual rigid-body
dynamics (moments of inertia, tipping regime) is not modelled; only the kinematics of
its particle orbits, which is where the paper's mathematics lives.

## References

* S. K. Ghosal, B. Raychaudhuri, A. K. Chowdhury, M. Sarker, *Conventionality of
  simultaneity and the tippe top paradox in relativity*, Found. Phys. Lett. **16**
  (2003) 549–560.  Eqs. (1)–(17).
* Carrier reuse: `ThermoFieldDynamics.TFDImaginaryPart` (`thermoBogoliubov`,
  `thermoBogoliubov_det`), `Lorentz.StandardLorentzBoost`
  (`rapidityBoost_preserves_minkowski`, cited), `CartanDecompositionDoubleCovers` /
  `CartanDecompositionLorentzGroup` (the elliptic and hyperbolic subgroup families the
  parabolic shear completes).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

@[expose] public section

namespace Physlib.Relativity.Special.SimultaneityConventionShear

/-! ## §A — the general frame map and the spinning trajectory (Eqs. (1)–(8)) -/

/-- **The spinning coordinate is `x⁰/a`** (Eqs. (2), (5)): subtracting the drift of the
table origin from the rocket coordinate leaves exactly the table coordinate rescaled by
the entry `a` — the algebraic seed of both non-rigidity types. -/
theorem spinning_coordinate (a b x t x0 : ℝ) (ha : a ≠ 0)
    (hx0 : x0 = a * x + b * t) :
    x + (b / a) * t = x0 / a := by
  rw [hx0]
  field_simp

/-- **The trajectory ellipse** (Eqs. (1), (8)): a particle of the top on the table-frame
circle of radius `R` traces, in the spinning coordinates of *any* linear frame map, the
ellipse `a²x_s² + y_s² = R²` — the type I distortion, governed only by `a`. -/
theorem trajectory_ellipse (a b x t x0 t0 y R ω : ℝ) (ha : a ≠ 0)
    (horbit : x0 = R * Real.cos (ω * t0)) (hy : y = R * Real.sin (ω * t0))
    (hx0 : x0 = a * x + b * t) :
    a ^ 2 * (x + (b / a) * t) ^ 2 + y ^ 2 = R ^ 2 := by
  rw [spinning_coordinate a b x t x0 ha hx0, horbit, hy]
  have h := Real.sin_sq_add_cos_sq (ω * t0)
  field_simp
  nlinarith [h]

/-- **The table time acquires the phase `g·x_s`** (Eqs. (6)–(7)): in spinning
coordinates the table time is `t⁰ = g·x_s + (h − gb/a)·t` — the type II effect
(bow-shaped particle chains, "relativity of simultaneity") is governed only by `g`. -/
theorem table_time_phase (a b g h x t t0 : ℝ) (ha : a ≠ 0)
    (ht0 : t0 = g * x + h * t) :
    t0 = g * (x + (b / a) * t) + (h - g * b / a) * t := by
  rw [ht0]
  field_simp
  ring

/-! ## §B — the four frame maps and the synchrony shear (Eqs. (9)–(17)) -/

/-- **The Lorentz map** (Eqs. (9)–(10)): `T = γ[[1, −βc], [−β/c, 1]]`, sending rocket
coordinates `(x, t)` to table coordinates `(x⁰, t⁰)`. -/
noncomputable def lorentzFrame (β c γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![γ, -(γ * β * c); -(γ * β / c), γ]

/-- **The Tangherlini map** (Eq. (14), inverted to the Eq. (2) direction): absolute
synchrony — the time row has no space component. -/
noncomputable def tangherliniFrame (β c γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![γ⁻¹, -(γ * β * c); 0, γ]

/-- **The Galilean map** (Eq. (15)). -/
noncomputable def galileanFrame (β c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -(β * c); 0, 1]

/-- **The Zahar map** (Eqs. (16)–(17)): Einstein synchrony imported into the Galilean
world. -/
noncomputable def zaharFrame (β c γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![γ ^ 2, -(β * c); -(γ ^ 2 * β / c), 1]

/-- **The synchrony shear**: resynchronizing the distant clocks of the rocket frame,
`(x, t) ↦ (x, t + κx)` — the parabolic one-parameter family of the `(1+1)` kinematics,
alongside the elliptic (`middleRotation`) and hyperbolic (`middleBoost`,
`thermoBogoliubov`) families. -/
noncomputable def synchronyShear (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; κ, 1]

/-- The shears form a one-parameter subgroup: `S(κ₁)·S(κ₂) = S(κ₁+κ₂)`. -/
theorem synchronyShear_mul (κ₁ κ₂ : ℝ) :
    synchronyShear κ₁ * synchronyShear κ₂ = synchronyShear (κ₁ + κ₂) := by
  unfold synchronyShear
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A resynchronization never moves an event in space: the `x`-row of the shear is
`(1, 0)` — only the time label changes. -/
theorem synchronyShear_fixes_space (κ x t : ℝ) :
    (synchronyShear κ).mulVec ![x, t] 0 = x := by
  simp [synchronyShear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- All four frame maps and the shear are unimodular (`γ²(1−β²) = 1` for the three
`γ`-dependent ones). -/
theorem frames_unimodular (β c γ : ℝ) (hc : c ≠ 0) (hγ : γ ^ 2 * (1 - β ^ 2) = 1) :
    (lorentzFrame β c γ).det = 1 ∧ (tangherliniFrame β c γ).det = 1 ∧
    (galileanFrame β c).det = 1 ∧ (zaharFrame β c γ).det = 1 ∧
    ∀ κ, (synchronyShear κ).det = 1 := by
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h] at hγ
    norm_num at hγ
  refine ⟨?_, ?_, ?_, ?_, fun κ => ?_⟩
  · simp only [lorentzFrame]
    rw [Matrix.det_fin_two_of]
    linear_combination hγ - γ ^ 2 * β ^ 2 * (mul_inv_cancel₀ hc)
  · simp only [tangherliniFrame]
    rw [Matrix.det_fin_two_of]
    linear_combination mul_inv_cancel₀ hγ0
  · simp only [galileanFrame]
    rw [Matrix.det_fin_two_of]
    ring
  · simp only [zaharFrame]
    rw [Matrix.det_fin_two_of]
    linear_combination hγ - γ ^ 2 * β ^ 2 * (mul_inv_cancel₀ hc)
  · simp only [synchronyShear]
    rw [Matrix.det_fin_two_of]
    ring

/-! ## §C — conventionality: the frames differ by pure resynchronization -/

/-- **The Tangherlini map is the Lorentz boost times a synchrony shear**: absolute
synchrony in the relativistic world is Einstein synchrony resynchronized by
`κ = β/c` — the two describe the same world. -/
theorem tangherlini_eq_lorentz_shear (β c γ : ℝ) (hc : c ≠ 0)
    (hγ : γ ^ 2 * (1 - β ^ 2) = 1) :
    tangherliniFrame β c γ = lorentzFrame β c γ * synchronyShear (β / c) := by
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h] at hγ
    norm_num at hγ
  unfold tangherliniFrame lorentzFrame synchronyShear
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-γ⁻¹) * hγ + γ * (1 - β ^ 2) * (mul_inv_cancel₀ hγ0)
      + γ * β ^ 2 * (mul_inv_cancel₀ hc)
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Absolute simultaneity under the Tangherlini map**: events at the same rocket time
get the same table time, whatever their separation — the time row is `x`-independent,
so the type II effect (`g = 0`) is absent. -/
theorem tangherlini_absolute_simultaneity (β c γ x₁ x₂ t : ℝ) :
    (tangherliniFrame β c γ).mulVec ![x₁, t] 1 =
      (tangherliniFrame β c γ).mulVec ![x₂, t] 1 := by
  simp [tangherliniFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The Zahar map is the Galilean map times a synchrony shear** (`κ = −γ²β/c`):
Einstein synchrony can be imported into the Galilean world by pure resynchronization. -/
theorem zahar_eq_galilean_shear (β c γ : ℝ) (hc : c ≠ 0)
    (hγ : γ ^ 2 * (1 - β ^ 2) = 1) :
    zaharFrame β c γ = galileanFrame β c * synchronyShear (-(γ ^ 2 * β / c)) := by
  unfold zaharFrame galileanFrame synchronyShear
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hγ - γ ^ 2 * β ^ 2 * (mul_inv_cancel₀ hc)
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The Galilean world manufactures the "relativistic" phase**: the Zahar map has a
nonzero time–space entry, so the bow-shaped chains (type II) appear in a world where
the tippe top cannot possibly be paradoxical — the lack of clock synchrony cannot be
what resolves the paradox (the paper's thesis). -/
theorem zahar_manufactures_phase (β c γ : ℝ) (hβ : β ≠ 0) (hc : c ≠ 0) (hγ0 : γ ≠ 0) :
    zaharFrame β c γ 1 0 ≠ 0 := by
  show -(γ ^ 2 * β / c) ≠ 0
  exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (pow_ne_zero 2 hγ0) hβ) hc)

/-! ## §D — the ellipse under the two synchronies: type I is convention-laden too -/

/-- **Lorentz contraction of the orbit** (Eq. (13)): under the Lorentz map the circle
becomes `γ²x_s² + y_s² = R²` — the semi-axis along the boost is `R/γ`. -/
theorem lorentz_ellipse (β c γ x t x0 t0 y R ω : ℝ) (hγ0 : γ ≠ 0)
    (horbit : x0 = R * Real.cos (ω * t0)) (hy : y = R * Real.sin (ω * t0))
    (hx0 : x0 = γ * x + -(γ * β * c) * t) :
    γ ^ 2 * (x + (-(γ * β * c) / γ) * t) ^ 2 + y ^ 2 = R ^ 2 :=
  trajectory_ellipse γ (-(γ * β * c)) x t x0 t0 y R ω hγ0 horbit hy hx0

/-- **Elongation under absolute synchrony**: under the Tangherlini map the same top
traces `γ⁻²x_s² + y_s² = R²` — semi-axis `γR` along the boost.  Together with
`lorentz_ellipse`: even the type I geometry of the moving top depends on the synchrony
convention. -/
theorem tangherlini_ellipse (β c γ x t x0 t0 y R ω : ℝ) (hγ0 : γ ≠ 0)
    (horbit : x0 = R * Real.cos (ω * t0)) (hy : y = R * Real.sin (ω * t0))
    (hx0 : x0 = γ⁻¹ * x + -(γ * β * c) * t) :
    (γ⁻¹) ^ 2 * (x + (-(γ * β * c) / γ⁻¹) * t) ^ 2 + y ^ 2 = R ^ 2 :=
  trajectory_ellipse γ⁻¹ (-(γ * β * c)) x t x0 t0 y R ω (inv_ne_zero hγ0) horbit hy hx0

/-! ## §E — the weld: the paper's boost is the repository's boost -/

/-- **The Lorentz map is `thermoBogoliubov` at negative rapidity**: at `c = 1` with
`γ = cosh η`, `β = tanh η`, the paper's matrix (Eq. (10)) is the TFD Bogoliubov boost
of the complex-delta contour arc — Ghosal's kinematics inherits `thermoBogoliubov_det`
and `rapidityBoost_preserves_minkowski`. -/
theorem lorentzFrame_eq_thermoBogoliubov (η : ℝ) :
    lorentzFrame (Real.tanh η) 1 (Real.cosh η) = thermoBogoliubov (-η) := by
  unfold lorentzFrame thermoBogoliubov
  have hcosh : Real.cosh η ≠ 0 := (Real.cosh_pos η).ne'
  have htanh : Real.cosh η * Real.tanh η = Real.sinh η := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Real.cosh_neg]
  · simp [Real.sinh_neg, mul_one]
    linear_combination htanh
  · simp [Real.sinh_neg, div_one]
    linear_combination htanh
  · simp [Real.cosh_neg]

/-! ## §F — the weld to the entropic proper distance: the rocket's speed is the Bell decay

The Ghosal kinematics and the Compton-clock entanglement arc live on the same rapidity
`η`: the boost velocity is `β = tanh η`, and by
`EntropicProperDistance.entropicProperDistance_vacuumBell` that is exactly the vacuum
Bell decay `e^{−r/λ_C}` at the entropic proper distance `r = λ_C log K`
(`K = schmidtNumber η = coth η`).  The tippe top's frame kinematics is therefore fixed
by the entanglement of the two regions. -/

/-- `γ²(1 − tanh²) = 1` — the rapidity parametrization satisfies the unimodularity
hypothesis of the frame theorems. -/
lemma rapidity_gamma_identity (η : ℝ) :
    Real.cosh η ^ 2 * (1 - Real.tanh η ^ 2) = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh η ≠ 0 := (Real.cosh_pos η).ne'
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq η]

/-- **The rocket's speed is the vacuum Bell decay at the entropic distance**: the frame
whose velocity is `β = e^{−r/λ_C}` — the Reeh–Schlieder suppression at the entropic
proper separation — implements exactly the Bogoliubov boost `thermoBogoliubov (−η)` of
the entanglement rapidity: Ghosal's tippe-top kinematics is set by the entanglement of
the regions. -/
theorem boost_velocity_eq_vacuumBell_decay (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    lorentzFrame (Real.exp (-(entropicProperDistance m c ħ η / comptonWavelength m c ħ)))
        1 (Real.cosh η) = thermoBogoliubov (-η) := by
  rw [entropicProperDistance_vacuumBell m c ħ η hη hlam]
  exact lorentzFrame_eq_thermoBogoliubov η

/-- **The resynchronization gauge is the Bell decay**: at the entanglement velocity the
Tangherlini frame differs from the Lorentz frame by the synchrony shear whose parameter
`κ = e^{−r/λ_C}` is again the vacuum Bell suppression — the conventionality of
simultaneity is graded by the entanglement of the separated regions. -/
theorem tangherlini_resync_eq_vacuumBell (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    tangherliniFrame (Real.exp (-(entropicProperDistance m c ħ η / comptonWavelength m c ħ)))
        1 (Real.cosh η) =
      lorentzFrame (Real.exp (-(entropicProperDistance m c ħ η / comptonWavelength m c ħ)))
        1 (Real.cosh η) *
      synchronyShear
        (Real.exp (-(entropicProperDistance m c ħ η / comptonWavelength m c ħ))) := by
  rw [entropicProperDistance_vacuumBell m c ħ η hη hlam]
  have h := tangherlini_eq_lorentz_shear (Real.tanh η) 1 (Real.cosh η) one_ne_zero
    (rapidity_gamma_identity η)
  rwa [div_one] at h

/-- **The tippe-top ellipse is pinned by the Schmidt number**: seen from the
entanglement-rapidity rocket, the top's circle becomes the ellipse with coefficient
`γ² = cosh²η`, and that coefficient satisfies `γ²(K² − 1) = K²`
(`boost_sq_schmidt_relation`) — the type I distortion of the top is a definite function
of the entanglement `K = e^{r/λ_C}` alone. -/
theorem tippeTop_ellipse_entanglement (η x t x0 t0 y R ω : ℝ) (hη : 0 < η)
    (horbit : x0 = R * Real.cos (ω * t0)) (hy : y = R * Real.sin (ω * t0))
    (hx0 : x0 = Real.cosh η * x + -(Real.cosh η * Real.tanh η * 1) * t) :
    Real.cosh η ^ 2 *
        (x + (-(Real.cosh η * Real.tanh η * 1) / Real.cosh η) * t) ^ 2 + y ^ 2 = R ^ 2 ∧
    Real.cosh η ^ 2 * (schmidtNumber η ^ 2 - 1) = schmidtNumber η ^ 2 :=
  ⟨lorentz_ellipse (Real.tanh η) 1 (Real.cosh η) x t x0 t0 y R ω
      (Real.cosh_pos η).ne' horbit hy hx0,
    boost_sq_schmidt_relation η hη⟩

/-! ## §G — the approximate Lorentz transformation (Eqs. (23)–(26)):
the `β² ≪ 1` limit of `LT` is *not* `GT` -/

/-- **The approximate Lorentz map** (Eq. (23)): the `γ ≅ 1` limit of the Lorentz map —
Einstein synchrony survives the nonrelativistic limit. -/
noncomputable def approxLorentzFrame (β c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -(β * c); -(β / c), 1]

/-- The approximate Lorentz map is *not* unimodular: `det = 1 − β²` — the truncation
breaks the group property at `O(β²)`. -/
theorem approxLorentzFrame_det (β c : ℝ) (hc : c ≠ 0) :
    (approxLorentzFrame β c).det = 1 - β ^ 2 := by
  simp only [approxLorentzFrame]
  rw [Matrix.det_fin_two_of]
  field_simp

/-- **No contraction in the approximate map** (Eq. (26)): the top's orbit stays a
*circle* (`a = 1`), even though the phase survives. -/
theorem alt_circle (β c x t x0 t0 y R ω : ℝ)
    (horbit : x0 = R * Real.cos (ω * t0)) (hy : y = R * Real.sin (ω * t0))
    (hx0 : x0 = x + -(β * c) * t) :
    (x + -(β * c) * t) ^ 2 + y ^ 2 = R ^ 2 := by
  have h := trajectory_ellipse 1 (-(β * c)) x t x0 t0 y R ω one_ne_zero horbit hy
    (by linarith [hx0])
  simpa using h

/-- **The phase survives the nonrelativistic limit** (Eqs. (24)–(25)): the approximate
map keeps a nonzero time–space entry — type II non-rigidity, with *no* type I: the
bow-shaped chains are a pure synchrony artefact present already at `O(β)`. -/
theorem alt_phase_survives (β c : ℝ) (hβ : β ≠ 0) (hc : c ≠ 0) :
    approxLorentzFrame β c 1 0 ≠ 0 := by
  show -(β / c) ≠ 0
  exact neg_ne_zero.mpr (div_ne_zero hβ hc)

/-- **The Zahar map exceeds the approximate Lorentz map exactly at `O(γ²−1)`**: an
exact decomposition — `ZT = ALT + (γ²−1)·[[1,0],[−β/c,0]]` — so the two agree as
`γ → 1`: the Zahar world *is* Einstein synchrony in the Galilean world. -/
theorem zahar_eq_alt_plus_gamma_correction (β c γ : ℝ) :
    zaharFrame β c γ =
      approxLorentzFrame β c + (γ ^ 2 - 1) • !![(1 : ℝ), 0; -(β / c), 0] := by
  unfold zaharFrame approxLorentzFrame
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.add_apply]
      all_goals ring

/-! ## §H — the spinning map `B` (Eqs. (27)–(29)): the rigidity criterion -/

/-- **The spinning map** (Eq. (28)): the matrix `B` with `x⁰ = B·x_s` — the whole
distortion of the top, type I in the `(0,0)` entry, type II in the `(1,0)` entry. -/
noncomputable def spinningMap (a b g h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 0; g, h - g * b / a]

/-- **`x⁰ = B·x_s`** (Eq. (27)): the spinning map carries the spinning coordinates to
the table coordinates — `spinning_coordinate` and `table_time_phase` as one matrix
statement. -/
theorem spinningMap_mulVec (a b g h x t x0 t0 : ℝ) (ha : a ≠ 0)
    (hx0 : x0 = a * x + b * t) (ht0 : t0 = g * x + h * t) :
    (spinningMap a b g h).mulVec ![x + (b / a) * t, t] = ![x0, t0] := by
  funext i
  fin_cases i
  · simp [spinningMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hx0]
    field_simp
  · simp [spinningMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [ht0]
    field_simp
    all_goals ring

/-- **For the Galilean map, `B = 1`** (Eq. (29)): the spinning coordinates *are* the
table coordinates — no distortion of any type. -/
theorem spinningMap_galilean_eq_one (β c : ℝ) :
    spinningMap 1 (-(β * c)) 0 1 = 1 := by
  unfold spinningMap
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The rigidity criterion**: the top appears undistorted (`B = 1`) *iff* both
non-rigidity entries vanish — `a = 1` (no type I) and `g = 0` (no type II) and the
time scale is trivial. -/
theorem spinningMap_eq_one_iff (a b g h : ℝ) (ha : a ≠ 0) :
    spinningMap a b g h = 1 ↔ a = 1 ∧ g = 0 ∧ h = 1 := by
  constructor
  · intro heq
    have h00 : spinningMap a b g h 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
      rw [heq]
    have h10 : spinningMap a b g h 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
      rw [heq]
    have h11 : spinningMap a b g h 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
      rw [heq]
    simp [spinningMap] at h00 h10 h11
    refine ⟨h00, h10, ?_⟩
    rw [h10] at h11
    simpa using h11
  · rintro ⟨rfl, rfl, rfl⟩
    unfold spinningMap
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-! ## §I — the explicit Tangherlini orbit (Eqs. (30)–(33)): no transcendental
equation -/

/-- **The Tangherlini orbit is explicit** (Eq. (31)): under absolute synchrony the
spinning coordinate is `x_s = γ·R·cos(ωγt)` — an explicit function of the rocket time,
with no implicit `x_s` in the phase (`g = 0`): the transcendental equation of §6 never
arises, and no speed constraint appears. -/
theorem tangherlini_explicit_orbit (β c γ x t x0 t0 R ω : ℝ) (hγ0 : γ ≠ 0)
    (horbit : x0 = R * Real.cos (ω * t0)) (ht0 : t0 = γ * t)
    (hx0 : x0 = γ⁻¹ * x + -(γ * β * c) * t) :
    x + (-(γ * β * c) / γ⁻¹) * t = γ * (R * Real.cos (ω * (γ * t))) := by
  rw [spinning_coordinate γ⁻¹ (-(γ * β * c)) x t x0 (inv_ne_zero hγ0) hx0, horbit, ← ht0]
  field_simp

/-! ## §J — the transcendental equation and the light-speed bound (Eqs. (34)–(36)) -/

/-- **The implicit-orbit map** (Eq. (34)): the right-hand side of `x_s = f(x_s)`
(Eq. (6)) — amplitude `A = R/a`, external phase `φ`, feedback `g`. -/
noncomputable def implicitOrbit (A ω φ g : ℝ) : ℝ → ℝ :=
  fun xs => A * Real.cos (ω * (φ + g * xs))

/-- The implicit-orbit map is differentiable with derivative
`−A·sin(ω(φ+gx_s))·ωg`. -/
theorem implicitOrbit_hasDerivAt (A ω φ g xs : ℝ) :
    HasDerivAt (implicitOrbit A ω φ g)
      (A * (-Real.sin (ω * (φ + g * xs)) * (ω * g))) xs := by
  have hu : HasDerivAt (fun x : ℝ => ω * (φ + g * x)) (ω * g) xs := by
    simpa using (((hasDerivAt_id xs).const_mul g).const_add φ).const_mul ω
  exact ((Real.hasDerivAt_cos (ω * (φ + g * xs))).comp xs hu).const_mul A

/-- **The iteration bound** (Eq. (35)): the derivative of the implicit-orbit map never
exceeds `|A|·|ω|·|g|` — the map contracts whenever the amplitude–feedback product is
below one. -/
theorem implicitOrbit_deriv_bound (A ω φ g xs : ℝ) :
    |A * (-Real.sin (ω * (φ + g * xs)) * (ω * g))| ≤ |A| * (|ω| * |g|) := by
  have hsin := Real.abs_sin_le_one (ω * (φ + g * xs))
  calc |A * (-Real.sin (ω * (φ + g * xs)) * (ω * g))|
      = |A| * (|Real.sin (ω * (φ + g * xs))| * (|ω| * |g|)) := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul]
    _ ≤ |A| * (1 * (|ω| * |g|)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsin (by positivity)) (abs_nonneg A)
    _ = |A| * (|ω| * |g|) := by rw [one_mul]

/-- **The light-speed bound** (Eq. (36)): for the Lorentz map (`A = R/γ`,
`g = −γβ/c`) the contraction bound is `ωRβ/c` — the `γ`'s cancel — so `ωR < c` (no
particle of the top faster than light) makes the implicit orbit equation an iteration
contraction, for *every* rocket speed `β < 1`. -/
theorem lorentz_iteration_light_bound (β c γ R ω : ℝ)
    (hc : 0 < c) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hR : 0 ≤ R) (hω : 0 ≤ ω)
    (hγ0 : γ ≠ 0) (hlight : ω * R < c) :
    |R / γ| * (|ω| * |-(γ * β / c)|) < 1 := by
  have hγabs : |γ| ≠ 0 := (abs_pos.mpr hγ0).ne'
  have hval : |R / γ| * (|ω| * |-(γ * β / c)|) = ω * R * β / c := by
    rw [abs_div, abs_neg, abs_div, abs_mul, abs_of_nonneg hR, abs_of_nonneg hω,
      abs_of_nonneg hβ0, abs_of_pos hc]
    field_simp
  rw [hval, div_lt_one hc]
  nlinarith [hlight, mul_nonneg hω hR,
    mul_nonneg (mul_nonneg hω hR) (sub_nonneg.mpr hβ1.le)]

end Physlib.Relativity.Special.SimultaneityConventionShear

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicMacroscopicLadder
public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde
public import Physlib.Units.PlanckUnitsInformation
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The area of the one-region entanglement screen

The one-region model of the entangled pair has a *size*: the entropic proper distance
`r = λ_C·log K` (`EntropicProperDistance`, `K = coth η` the Schmidt number) — one region
whose radius is set by its entanglement, `r = λ_C·log 2` for the Bell pair
(`EntropicMacroscopicLadder.bellMarginal_radius`). This module closes that radius into a
**screen** and derives the equation for its area, welding the one-region arc to the
holographic layer (`VerlindeNewtonGravity`) and the Planck ledger
(`Units.PlanckUnitsInformation`).

## The area equation and its three faces

* `entanglementScreenArea` — **the equation**:
  `A(η) = 4π·λ_C²·(log K)²` — the area of the sphere at the one-region radius is the
  Compton area `λ_C²` times the *squared* entanglement entropy (in nats).
* `entanglementScreen_holographicBits` — the holographic face: the Verlinde bit count of
  that screen is
  `N = A·c³/(Gℏ) = 4π·(ℏc/G)·(log K)²/m² = 4π·(m_P/m)²·(log K)²` —
  squared Planck-to-particle mass ratio times squared entanglement nats. The conversion
  uses the two factorizations of `ℏ/c` — `λ_C·m = ℏ/c = ℓ_P·m_P`
  (`PlanckUnitsInformation.planckPairs_infoFree`) — so `λ_C/ℓ_P = m_P/m`.
* `schwarzschildCompton_geometricMean` — the horizon face: for *every* mass,
  `r_s·λ_C = 2Gℏ/c³ = 2ℓ_P²` — the Schwarzschild radius and the Compton wavelength have
  the Planck area as (half) their geometric mean; hence the equivalent form
  `entanglementScreenBits_perSchwarzschild`: `N = 8π·λ_C·(log K)²/r_s` — the bit count
  measures the screen against the particle's own horizon scale.

Bell endpoints on the `QuantumInfo` carrier (`K = 2` via the computed marginal):
`bellScreenArea` (`A = 4π·λ_C²·(log 2)²`) and `bellScreenBits`
(`N = 4π·(ℏc/G)·(log 2)²/m²`).

## The stack face and the flat point

Radii add under the state product (`EntropicMacroscopicLadder.entropicRadius_add`), so
`n` Bell pairs give a screen of area `4π·λ_C²·(n·log 2)²` (`bellStackScreenArea`) with
bit capacity quadratic in `n` (`bellStackScreenBits`) — while the entanglement content
`n·log 2` is linear. `stackScreen_holographic_headroom` proves the resulting bound: for
any sub-Planckian mass and `n ≥ 1`, content ≤ capacity (margin `4π·(m_P/m)²·n·log 2 >
1`) — the entanglement stack always respects the holographic bound of its own screen.
And the screen carries no curvature: `chordLength_iff_flat` (chord = geodesic **iff**
`K = 0`, from the Szabados triangle length) plus `oneRegion_flat_normal_point` — when
chord and geodesic across the pair both equal the entropic proper distance (the
graph-transport identification), the recovered sectional curvature vanishes, so the
area formula is exact flat-sphere geometry (Pillar 5).

## The `[I]` typing: which face is information-balanced

`GravitationalCouplingDimensions` forced counts-in-Compton-units to carry `I𝓭` (nats),
so the typed one-region radius is `[r] = L·I𝓭` and the entanglement face of the area
equation carries `[A] = L²·I𝓭²` — **two nats, one per radius factor** — while the
holographic face `N·ℓ_P²` is a pure area (`PlanckUnitsInformation.holographicCount_isBits`:
`[A/ℓ_P²] = I𝓭` with the informed Planck area). `entanglementArea_carries_two_bits`
records the defect and its SI-invisibility: under `forgetInfo` the two faces collide —
5-base analysis cannot distinguish the entanglement area from a geometric area; only the
`[I]` axis shows that the quadratic-in-entropy face is nat-weighted and the linear
holographic count is the balanced form.

## References

* Carriers: `ComptonClock.EntropicProperDistance` (`r = λ_C·log K`),
  `ComptonClock.EntropicMacroscopicLadder` (`bellMarginal_radius`),
  `Thermodynamics.VerlindeNewtonGravity` (`sphereArea`, `holographicBits`),
  `Relativity.SemiClassical.SchwarzschildVerlinde` (`schwarzschildRadius`),
  `Units.PlanckUnitsInformation` (informed Planck area, half-bit grading),
  `Units.GravitationalCouplingDimensions` (forced `I𝓭`-typings).
* E. Verlinde, JHEP 04 (2011) 029 — `N = Ac³/(Gℏ)`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.SzabadosCurvedSpacetime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicMacroscopicLadder
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.Thermodynamics
open Physlib.Relativity.SemiClassical
open Dimension.LTMCTI Physlib.Units.InformationDimensionCollision
open Physlib.Units.GravitationalCouplingDimensions

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

/-! ## §A — the area equation -/

/-- **The area of the one-region entanglement screen**:
`A(η) = 4π·λ_C²·(log K)²` — the sphere at the entropic proper radius `r = λ_C·log K`
has the Compton area times the squared entanglement entropy (in nats). The size of the
one region is quadratic in its entanglement. -/
theorem entanglementScreenArea (m c ħ η : ℝ) :
    sphereArea (entropicProperDistance m c ħ η)
      = 4 * Real.pi * comptonWavelength m c ħ ^ 2
          * Real.log (schmidtNumber η) ^ 2 := by
  unfold sphereArea entropicProperDistance
  ring

/-! ## §B — the holographic face: bits on the screen -/

/-- **The holographic bit count of the entanglement screen**:
`N = A·c³/(Gℏ) = 4π·(ℏc/G)·(log K)²/m²` — since `ℏc/G = m_P²` (the squared Planck mass
of `PlanckUnitsInformation`), this is `N = 4π·(m_P/m)²·(log K)²`: squared
Planck-to-particle mass ratio times squared entanglement nats. The mass ratio enters
through the two factorizations of `ℏ/c` — `λ_C·m = ℏ/c = ℓ_P·m_P`
(`planckPairs_infoFree`), i.e. `λ_C/ℓ_P = m_P/m`. -/
theorem entanglementScreen_holographicBits (m c ħ G η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) :
    holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c
      = 4 * Real.pi * (ħ * c / G) * Real.log (schmidtNumber η) ^ 2 / m ^ 2 := by
  unfold holographicBits sphereArea entropicProperDistance comptonWavelength
  field_simp

/-! ## §C — the horizon face: the Planck area as geometric mean -/

/-- **The Schwarzschild–Compton geometric mean is the Planck area, for every mass**:
`r_s·λ_C = (2Gm/c²)·(ℏ/(mc)) = 2·Gℏ/c³ = 2ℓ_P²` — the mass cancels: any particle's
horizon scale times its quantum scale is twice the Planck area. This is the ℝ-level
face of `informedPlanckArea_eq`: the Planck area sits between gravity's length and
quantum mechanics' length as their mass-independent mean. -/
theorem schwarzschildCompton_geometricMean (m G c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    schwarzschildRadius m G c * comptonWavelength m c ħ = 2 * (G * ħ / c ^ 3) := by
  unfold schwarzschildRadius comptonWavelength
  field_simp

/-- **The bit count measured against the particle's own horizon**:
`N = 8π·λ_C·(log K)²/r_s` — eliminating `G` through the geometric mean, the
entanglement screen's bit count is the Compton wavelength per Schwarzschild radius,
times `8π` squared nats. -/
theorem entanglementScreenBits_perSchwarzschild (m c ħ G η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) :
    holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c
      = 8 * Real.pi * comptonWavelength m c ħ * Real.log (schmidtNumber η) ^ 2
          / schwarzschildRadius m G c := by
  unfold holographicBits sphereArea entropicProperDistance comptonWavelength
    schwarzschildRadius
  field_simp
  ring

/-! ## §D — Bell endpoints on the `QuantumInfo` carrier -/

/-- **The Bell screen area**: for the Bell marginal (Schmidt number `2` via the computed
`collisionWeight = 1/2`), the one-region screen has area `A = 4π·λ_C²·(log 2)²`. -/
theorem bellScreenArea (m c ħ : ℝ) :
    sphereArea (entropicRadius m c ħ ((MState.pure bellPhiPlus).traceRight))
      = 4 * Real.pi * comptonWavelength m c ħ ^ 2 * Real.log 2 ^ 2 := by
  rw [bellMarginal_radius]
  unfold sphereArea
  ring

/-- **The Bell screen bit count**: `N = 4π·(ℏc/G)·(log 2)²/m² = 4π·(m_P/m)²·(log 2)²` —
one Bell pair's screen, counted in holographic bits. -/
theorem bellScreenBits (m c ħ G : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) :
    holographicBits
        (sphereArea (entropicRadius m c ħ ((MState.pure bellPhiPlus).traceRight))) G ħ c
      = 4 * Real.pi * (ħ * c / G) * Real.log 2 ^ 2 / m ^ 2 := by
  rw [bellMarginal_radius]
  unfold holographicBits sphereArea comptonWavelength
  field_simp

/-! ## §E — the `[I]` typing of the area equation -/

/-- **The entanglement face of the area equation carries two nats.** With the forced
typing of Compton-unit counts as nats (`GravitationalCouplingDimensions`), the
one-region radius is `[r] = L·I𝓭` and its screen `[A] = (L·I𝓭)² = L²·I𝓭²` — one nat
per radius factor. The defect is invisible to the 5-base projection (`forgetInfo`
collides it with the pure area) yet dimensionally real: only the `[I]` axis
distinguishes the quadratic-in-entropy entanglement area from a geometric area — whose
information-balanced form is the holographic face `N·ℓ_P²`
(`PlanckUnitsInformation.holographicCount_isBits`). -/
theorem entanglementArea_carries_two_bits :
    (L𝓭 * I𝓭) ^ (2 : ℚ) = area_dim * I𝓭 ^ (2 : ℚ)
    ∧ forgetInfo ((L𝓭 * I𝓭) ^ (2 : ℚ)) = forgetInfo area_dim
    ∧ (L𝓭 * I𝓭) ^ (2 : ℚ) ≠ area_dim := by
  refine ⟨by ext b <;> cases b <;> norm_num [area_dim], by ext b <;> cases b <;> norm_num [area_dim], fun h => ?_⟩
  have hinformation := congrArg (fun d => d.exponent .information) h
  simp [area_dim] at hinformation

/-! ## §F — the stack face: macroscopic screens from added radii -/

/-- **The stack screen area**: `n` independent Bell pairs add their radii
(`EntropicMacroscopicLadder.entropicRadius_add`, `bellStack_radius`), so the stack's
screen has area `A(n) = 4π·λ_C²·(n·log 2)²` — **quadratic** in the pair count, while
the stack's entanglement entropy `n·log 2` is linear. -/
theorem bellStackScreenArea (m c ħ : ℝ) (n : ℕ) :
    sphereArea ((n : ℝ) * (comptonWavelength m c ħ * Real.log 2))
      = 4 * Real.pi * comptonWavelength m c ħ ^ 2 * ((n : ℝ) * Real.log 2) ^ 2 := by
  unfold sphereArea
  ring

/-- **The stack screen bit count**: `N(n) = 4π·(ℏc/G)·(n·log 2)²/m²
= 4π·(m_P/m)²·(n·log 2)²` — the holographic capacity of the stack's screen grows with
the *square* of the pair count. -/
theorem bellStackScreenBits (m c ħ G : ℝ) (n : ℕ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) :
    holographicBits (sphereArea ((n : ℝ) * (comptonWavelength m c ħ * Real.log 2))) G ħ c
      = 4 * Real.pi * (ħ * c / G) * ((n : ℝ) * Real.log 2) ^ 2 / m ^ 2 := by
  unfold holographicBits sphereArea comptonWavelength
  field_simp

/-- **Sub-Planckian stacks never saturate their own screen**: for any mass at or below
the Planck mass (`m² ≤ ℏc/G`) and any `n ≥ 1`, the stack's entanglement content
`n·log 2` nats stays below the holographic capacity `N(n)` of its screen — the
Bekenstein/holographic bound is respected with room to spare, because capacity grows
quadratically (`bellStackScreenBits`) while content grows linearly. The margin is the
factor `4π·(m_P/m)²·n·log 2 ≥ 4π·log 2 > 1`. -/
theorem stackScreen_holographic_headroom (m c ħ G : ℝ) (n : ℕ)
    (hm : 0 < m) (hn : 1 ≤ n) (hplanck : m ^ 2 ≤ ħ * c / G) :
    (n : ℝ) * Real.log 2
      ≤ 4 * Real.pi * (ħ * c / G) * ((n : ℝ) * Real.log 2) ^ 2 / m ^ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hA : 0 < (n : ℝ) * Real.log 2 := by nlinarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hB : 0 < ħ * c / G := lt_of_lt_of_le hm2 hplanck
  have h1 : (1 : ℝ) ≤ 4 * Real.pi * ((n : ℝ) * Real.log 2) := by
    nlinarith [Real.pi_gt_three, Real.log_two_gt_d9]
  rw [le_div_iff₀ hm2]
  calc (n : ℝ) * Real.log 2 * m ^ 2
      ≤ (n : ℝ) * Real.log 2 * (ħ * c / G) :=
        mul_le_mul_of_nonneg_left hplanck hA.le
    _ = 1 * ((n : ℝ) * Real.log 2 * (ħ * c / G)) := by ring
    _ ≤ (4 * Real.pi * ((n : ℝ) * Real.log 2))
          * ((n : ℝ) * Real.log 2 * (ħ * c / G)) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hA.le hB.le)
    _ = 4 * Real.pi * (ħ * c / G) * ((n : ℝ) * Real.log 2) ^ 2 := by ring

/-! ## §G — the flat normal point: the screen carries no curvature -/

/-- **Chord equals geodesic iff flat**: the Szabados geodesic-triangle length
`L = tw(1 − t²K/6)` equals the flat chord value `t·w` **iff** the sectional curvature
vanishes — the identification locus (where chord and geodesic coincide) is exactly the
flat locus of the emergent spacetime. -/
theorem chordLength_iff_flat (t w K : ℝ) (ht : t ≠ 0) (hw : w ≠ 0) :
    sectionalGeodesicLength t w K = t * w ↔ K = 0 := by
  unfold sectionalGeodesicLength
  constructor
  · intro h
    have h2 : (t ^ 3 * w) * K = 0 := by linear_combination (-6 : ℝ) * h
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (pow_ne_zero 3 ht) hw)
  · rintro rfl
    ring

/-- **The one-region screen sits at a flat Riemann-normal point** (Pillar 5): if both
the geodesic length and the flat chord `t·w` across the pair equal the entropic proper
distance `r = λ_C·log K` — the graph-transport identification making chord and geodesic
coincide — then the Szabados sectional curvature recovered from those distances is
**zero**. The screen of `entanglementScreenArea` is a sphere in flat emergent
spacetime: its area formula carries no curvature correction. -/
theorem oneRegion_flat_normal_point (m c ħ η t w K : ℝ) (ht : t ≠ 0) (hw : w ≠ 0)
    (hgeo : sectionalGeodesicLength t w K = entropicProperDistance m c ħ η)
    (hchord : t * w = entropicProperDistance m c ħ η) :
    K = 0 :=
  (chordLength_iff_flat t w K ht hw).mp (hgeo.trans hchord.symm)

/-! ## §H — the explicit Bell rapidity: the two radius routes agree -/

/-- **The Bell rapidity is `log √3`**: `schmidtNumber (log √3) = coth (log √3) = 2` —
the explicit rapidity at which the Schmidt number takes the Bell value. This is the
witness that instantiates the conditional Bell-boost theorems
(`SchmidtFixedPointClockBridges.bell_boost*`, hypothesis `schmidtNumber η = 2`)
non-vacuously. -/
theorem bellRapidity_schmidtNumber_two :
    schmidtNumber (Real.log (Real.sqrt 3)) = 2 := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hinv : (Real.sqrt 3)⁻¹ * Real.sqrt 3 = 1 := inv_mul_cancel₀ (ne_of_gt hs)
  have hkey : (Real.sqrt 3 - (Real.sqrt 3)⁻¹) * Real.sqrt 3 = 2 := by
    rw [sub_mul, hinv]
    nlinarith [hsq]
  have hden : 0 < Real.sqrt 3 - (Real.sqrt 3)⁻¹ := by nlinarith [hkey, hs]
  unfold schmidtNumber
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_log hs, Real.exp_neg, Real.exp_log hs]
  rw [div_div_div_cancel_right₀, div_eq_iff (ne_of_gt hden)]
  · nlinarith [hkey, hinv]
  · norm_num

/-- **The Bell rapidity is positive and realizes the collision datum**:
`0 < log √3` and `schmidtNumber (log √3) = (collisionWeight ρ_Bell)⁻¹ = 2` — the
hypotheses of `bell_boost_sq`/`bell_boost`/`bell_deBroglie_clock` are satisfiable, with
the explicit witness `η = log √3`. -/
theorem bellRapidity_realizes_collision :
    0 < Real.log (Real.sqrt 3)
    ∧ schmidtNumber (Real.log (Real.sqrt 3))
        = (collisionWeight ((MState.pure bellPhiPlus).traceRight))⁻¹ := by
  refine ⟨Real.log_pos ?_, ?_⟩
  · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),
      Real.sqrt_nonneg (3 : ℝ)]
  · rw [bellRapidity_schmidtNumber_two, collisionWeight_bellMarginal]
    norm_num

/-- **The two radius routes agree at the Bell point**: the rapidity route
`entropicProperDistance` at `η = log √3` (Schmidt dictionary, `K = coth η`) and the
state route `entropicRadius` on the computed Bell marginal (`QuantumInfo` collision
weight) give the *same* proper radius `λ_C·log 2` — so `bellScreenArea` and
`entanglementScreenArea` at the Bell rapidity are the same screen. -/
theorem bell_radius_routes_agree (m c ħ : ℝ) :
    entropicProperDistance m c ħ (Real.log (Real.sqrt 3))
      = entropicRadius m c ħ ((MState.pure bellPhiPlus).traceRight) := by
  unfold entropicProperDistance
  rw [bellRapidity_schmidtNumber_two, bellMarginal_radius]


/-! ## §J — isolating the fine-structure constant from the screen

The Planck system pairs each constant with a ratio: `α = e²/(4πε₀ℏc)` is the *squared
charge-to-Planck-charge ratio* (`q_P² = 4πε₀ℏc`), and the gravitational coupling
`α_G = Gm²/(ℏc)` is the *squared particle-to-Planck mass ratio* (`m_P² = ℏc/G`). Their quotient
kills `ℏc`: `α/α_G = e²/(4πε₀Gm²)`, the electromagnetic-to-gravitational force ratio — so `α` is
the force ratio evaluated *at the Planck mass*. Feeding in the screen's holographic bit count
`N = 4π(m_P/m)²(log K)²` (the entropic route to Newton's `G` of §B and
`VerlindeNewtonGravity`), `ℏc` is eliminated in favor of measurable ratios and the fine-structure
constant is **isolated**:

  `α = (e/m)²·(log K)²/(ε₀·G·N)`

— squared charge-to-mass ratio times squared entanglement nats over `ε₀·G·(bit count)`; read the
other way, the same identity *derives Newton's constant* from `α`, the charge-to-mass ratio and
the screen count: `G = (e/m)²·(log K)²/(ε₀·α·N)`. -/

/-- **The fine-structure constant** `α = e²/(4πε₀ℏc)`. -/
noncomputable def fineStructure (e eps0 ħ c : ℝ) : ℝ := e ^ 2 / (4 * Real.pi * eps0 * ħ * c)

/-- **The squared Planck charge** `q_P² = 4πε₀ℏc`. -/
noncomputable def planckChargeSq (eps0 ħ c : ℝ) : ℝ := 4 * Real.pi * eps0 * ħ * c

/-- **The squared Planck mass** `m_P² = ℏc/G` — the mass whose gravitational coupling is one. -/
noncomputable def planckMassSq (G ħ c : ℝ) : ℝ := ħ * c / G

/-- **The gravitational coupling** `α_G = Gm²/(ℏc)` — gravity's fine-structure constant. -/
noncomputable def gravitationalCoupling (G m ħ c : ℝ) : ℝ := G * m ^ 2 / (ħ * c)

/-- **[`α` is the squared charge ratio]** `α·q_P² = e²`: the fine-structure constant measures the
elementary charge against the Planck charge. -/
theorem fineStructure_mul_planckChargeSq (e eps0 ħ c : ℝ)
    (heps : eps0 ≠ 0) (hħ : ħ ≠ 0) (hc : c ≠ 0) :
    fineStructure e eps0 ħ c * planckChargeSq eps0 ħ c = e ^ 2 := by
  unfold fineStructure planckChargeSq
  have hπ := Real.pi_ne_zero
  field_simp

/-- **[`α_G` is the squared mass ratio]** `α_G·m_P² = m²`: the gravitational coupling measures
the particle mass against the Planck mass. -/
theorem gravitationalCoupling_mul_planckMassSq (G m ħ c : ℝ) (hG : G ≠ 0)
    (hħ : ħ ≠ 0) (hc : c ≠ 0) :
    gravitationalCoupling G m ħ c * planckMassSq G ħ c = m ^ 2 := by
  unfold gravitationalCoupling planckMassSq
  field_simp

/-- **[The coupling quotient is the force ratio]** `α/α_G = e²/(4πε₀Gm²)`: `ℏc` cancels and the
quotient of the two fine-structure constants is the Coulomb-to-Newton force ratio for a particle
of charge `e` and mass `m` — pure ratio data, no quantum of action left. -/
theorem fineStructure_div_gravitationalCoupling (e eps0 G m ħ c : ℝ)
    (heps : eps0 ≠ 0) (hG : G ≠ 0) (hm : m ≠ 0) (hħ : ħ ≠ 0) (hc : c ≠ 0) :
    fineStructure e eps0 ħ c / gravitationalCoupling G m ħ c
      = e ^ 2 / (4 * Real.pi * eps0 * G * m ^ 2) := by
  unfold fineStructure gravitationalCoupling
  have hπ := Real.pi_ne_zero
  field_simp

/-- **[`α` is the force ratio at the Planck mass]** `α = e²/(4πε₀·G·m_P²)`: substituting
`G·m_P² = ℏc` — the Planck-mass definition, i.e. the `G`-equation — expresses the fine-structure
constant with no explicit `ℏ`: electromagnetism against gravity at the Planck scale. -/
theorem fineStructure_at_planckMass (e eps0 G ħ c : ℝ) (hG : G ≠ 0) :
    fineStructure e eps0 ħ c
      = e ^ 2 / (4 * Real.pi * eps0 * G * planckMassSq G ħ c) := by
  unfold fineStructure planckMassSq
  rw [show 4 * Real.pi * eps0 * G * (ħ * c / G) = 4 * Real.pi * eps0 * (G * (ħ * c / G))
      from by ring,
    mul_div_cancel₀ _ hG]
  ring_nf

/-- **[The fine-structure constant isolated from the screen]**
`α = (e/m)²·(log K)²/(ε₀·G·N)` with `N` the holographic bit count of the one-region
entanglement screen: the charge-to-mass ratio and the squared entanglement nats, divided by
`ε₀·G` times the bit count — `ℏ` and `c` eliminated through the entropic `G`-equation of §B. -/
theorem fineStructure_from_screenBits (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η) :
    fineStructure e eps0 ħ c
      = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2
        / (eps0 * G
            * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [entanglementScreen_holographicBits m c ħ G η hm hc hħ hG]
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hπ := Real.pi_ne_zero
  unfold fineStructure
  field_simp

/-- **[Newton's constant derived from `α` and the screen]**
`G = (e/m)²·(log K)²/(ε₀·α·N)`: the same identity read backwards — the entropic bit count, the
fine-structure constant and the charge-to-mass ratio fix Newton's constant. -/
theorem newtonG_from_screenBits (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η)
    (he : e ≠ 0) :
    G = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2
        / (eps0 * fineStructure e eps0 ħ c
            * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [entanglementScreen_holographicBits m c ħ G η hm hc hħ hG]
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hπ := Real.pi_ne_zero
  unfold fineStructure
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

end

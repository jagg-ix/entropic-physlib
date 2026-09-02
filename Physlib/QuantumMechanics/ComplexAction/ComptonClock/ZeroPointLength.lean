/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.Thermodynamics.VerlindeEntropicForce

/-!
# The zero-point length of spacetime and the equivalence principle at Planck scales

Padmanabhan (*Principle of Equivalence at Planck scales, QG in locally inertial frames and the
zero-point-length of spacetime*, arXiv:2005.09677) argues that the dominant quantum-gravity effect at
mesoscopic scales is a **zero-point length** `L ~ L_P`: the squared geodesic interval is shifted
`σ² → σ² + L²`, so that the effective path length `ℓ ↦ √(ℓ² + L²)` (Eq. 8) and the path-integral
amplitude becomes `exp[−m(σ + L²/σ)]` (Eq. 13). The Planck length emerges as the geometric mean of the
Compton wavelength `λ_c = ℏ/mc` and the gravitational (Schwarzschild) radius `λ_g = Gm/c²`,
`L_P = √(λ_c λ_g)`, and the mass drops out — `λ_c λ_g = Gℏ/c³`. The self-dual form `σ + L²/σ` and its
universal (mass-independent) geometric interpretation both hinge on the **principle of equivalence**
`m_i = m_g` (Eq. 14).

This module formalizes that algebraic structure and sharpens it into the minimal-length statements the
picture implies. It reuses `ComptonClock.FrequencyTrinity.comptonWavelength`.

* **§A Length hierarchy (Eq. 1).** `gravitationalLength = Gm/c²`, `planckLengthSq = Gℏ/c³`,
  `planckLength = √(Gℏ/c³)`. `compton_grav_product_eq_planckSq` — the mass cancels,
  `λ_c λ_g = L_P²`; `planckLength_eq_geometricMean` — `L_P = √(λ_c λ_g)`; and `length_hierarchy` —
  `λ_g < L_P < λ_c` for `m < m_pl` (`λ_g < λ_c`), the ordering (1).
* **§B Self-dual QG path length (Eq. 13).** `qgPathLength L σ = σ + L²/σ`; `qgPathLength_duality` — the
  path-integral duality invariance under `σ → L²/σ`; `qgPathLength_self_dual` — its fixed point `σ = L`
  gives `2L`; **`qgPathLength_ge_two_L`** *(extension)* — `σ + L²/σ ≥ 2L`, so the amplitude is maximal at
  the self-dual point and the effective path length is bounded below by `2L`.
* **§C The zero-point length as a minimal length (Eq. 8).** `qgInterval L ℓ = √(ℓ² + L²)`;
  `qgInterval_sq` — `σ² + L²`; **`qgInterval_ge_L`** *(extension)* — `√(ℓ² + L²) ≥ |L|`, with equality at
  `ℓ = 0` (`qgInterval_at_zero`): the geodesic interval can never fall below the zero-point length, the
  rigorous minimal-length content of the `σ² → σ² + L²` postulate.
* **§D Heat-kernel form (Eq. 9/23).** `heat_zeroPoint_shift` — the `L²/4s` factor in the Schwinger
  proper-time propagator is exactly the exponent shift `σ²/4s + L²/4s = (√(σ²+L²))²/4s`, i.e.
  `σ² → σ² + L²` to leading order.
* **§E Equivalence principle (Eq. 14).** `eepPathCoefficient m_i m_g = m_g/m_i` — the coefficient of
  `L²/σ` in the exponent; `eepPathCoefficient_eq_one_iff` — it equals `1` (the universal, geometric,
  matter-independent `σ + L²/σ`) **iff** `m_i = m_g`, the principle of equivalence.

## Honest scope

Formalized: the length-scale algebra, the path-length/interval duality and minimal-length bounds, the
heat-kernel exponent shift, and the EEP coefficient. The analytic identities of the paper — the free
propagator `G_QG(p²) = mL/√(p²+m²) K₁[L√(p²+m²)]` (Eqs. 10/11, modified Bessel `K₁`), the Bessel
integral `∫ 2K J₀(KL) e^{−sK²} dK = ½ e^{−L²/4s}` (Eq. 25), and the mass-integral relation (Eqs. 15/30)
— are cited, not evaluated. `L` is taken `= O(1) L_P` throughout, as in the paper.

## References

* T. Padmanabhan, *Principle of Equivalence at Planck scales, QG in locally inertial frames and the
  zero-point-length of spacetime*, arXiv:2005.09677 (Eqs. 1, 8, 9, 13, 14, 23).
* `ComptonClock.FrequencyTrinity` (`comptonWavelength = ℏ/mc`); the entropic/calibrated proper-distance
  arc (`ComptonClock.EntropicProperDistance`, `ComptonClock.CalibratedDistance`).
-/

set_option autoImplicit false

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength

/-! ## A. The length hierarchy `λ_g < L_P < λ_c` (Eq. 1) -/

/-- **The gravitational (Schwarzschild) length** `λ_g = Gm/c²` (Padmanabhan §2), the Schwarzschild radius
up to the `O(1)` factor of two. -/
noncomputable def gravitationalLength (m G c : ℝ) : ℝ := G * m / c ^ 2

/-- **The Planck length squared** `L_P² = Gℏ/c³` — the zero-point area `L² ~ L_P²`. -/
noncomputable def planckLengthSq (G ħ c : ℝ) : ℝ := G * ħ / c ^ 3

/-- **The Planck length** `L_P = √(Gℏ/c³)`. -/
noncomputable def planckLength (G ħ c : ℝ) : ℝ := Real.sqrt (planckLengthSq G ħ c)

/-- The Planck length is non-negative. -/
theorem planckLength_nonneg (G ħ c : ℝ) : 0 ≤ planckLength G ħ c := Real.sqrt_nonneg _

/-- **The mass cancels: `λ_c λ_g = L_P²`.** The product of the Compton wavelength `ℏ/mc` and the
gravitational radius `Gm/c²` is `Gℏ/c³ = L_P²`, independent of the particle mass — the key fact making the
zero-point length universal (Padmanabhan §2.3). -/
theorem compton_grav_product_eq_planckSq (m G ħ c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    comptonWavelength m c ħ * gravitationalLength m G c = planckLengthSq G ħ c := by
  unfold comptonWavelength gravitationalLength planckLengthSq
  field_simp

/-- **The Planck product is `ℏ/c`, and `G` cancels**: `ℓ_P² · m_P² = (ℏ/c)²`, where
`m_P² = ℏc/G` (`EntanglementScreenArea.planckMassSq`).  Newton's constant appears once in
each factor and drops out, so the reduced Compton wavelength of the Planck mass *is* the
Planck length.

Under the holographic typing (`[G] = L³M⁻¹T⁻²I⁻¹`) this is the identity in which the
information charge cancels exactly: `ℓ_P` carries `I^{-1/2}` and `m_P` carries `I^{+1/2}`,
so the product is nat-free.  The half-nats are opposite in sign because `G` sits in the
denominator of one and the numerator of the other. -/
theorem planckLengthSq_mul_planckMassSq (G ħ c : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) :
    planckLengthSq G ħ c * (ħ * c / G) = (ħ / c) ^ 2 := by
  unfold planckLengthSq
  field_simp

/-- **The Planck length is the geometric mean** `L_P = √(λ_c λ_g)` (Padmanabhan §2). -/
theorem planckLength_eq_geometricMean (m G ħ c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    planckLength G ħ c = Real.sqrt (comptonWavelength m c ħ * gravitationalLength m G c) := by
  unfold planckLength; rw [compton_grav_product_eq_planckSq m G ħ c hm hc]

/-- The geometric mean of two positive reals lies strictly between them: `0 < a < b ⟹ a < √(ab) < b`. -/
theorem geometricMean_between {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    a < Real.sqrt (a * b) ∧ Real.sqrt (a * b) < b := by
  have hb : 0 < b := ha.trans hab
  refine ⟨(Real.lt_sqrt ha.le).mpr ?_, (Real.sqrt_lt' hb).mpr ?_⟩
  · nlinarith
  · nlinarith

/-- **The length hierarchy `λ_g < L_P < λ_c` (Eq. 1).** For a sub-Planckian particle (`λ_g < λ_c`, i.e.
`m < m_pl`), the Planck length — the geometric mean of the gravitational radius and the Compton
wavelength — lies strictly between them. -/
theorem length_hierarchy (m G ħ c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0)
    (hg : 0 < gravitationalLength m G c)
    (hgc : gravitationalLength m G c < comptonWavelength m c ħ) :
    gravitationalLength m G c < planckLength G ħ c ∧
      planckLength G ħ c < comptonWavelength m c ħ := by
  have hp : planckLength G ħ c
      = Real.sqrt (gravitationalLength m G c * comptonWavelength m c ħ) := by
    unfold planckLength
    rw [← compton_grav_product_eq_planckSq m G ħ c hm hc, mul_comm]
  rw [hp]; exact geometricMean_between hg hgc

/-! ## B. The self-dual QG path length `σ + L²/σ` (Eq. 13) -/

/-- **The quantum-gravity path length** `σ + L²/σ` (Padmanabhan Eq. 13): the argument of the modified
path-integral amplitude `exp[−m(σ + L²/σ)]`, combining the Compton suppression `σ/λ_c` and the
self-gravity suppression `λ_g/σ` with `λ_c λ_g = L²`. -/
noncomputable def qgPathLength (L σ : ℝ) : ℝ := σ + L ^ 2 / σ

/-- **Path-integral duality** (Padmanabhan Eq. 13): the QG path length is invariant under the duality
transformation `σ → L²/σ`, so the amplitude `exp[−m(σ + L²/σ)]` is self-dual. -/
theorem qgPathLength_duality (L σ : ℝ) (hσ : σ ≠ 0) (hL : L ≠ 0) :
    qgPathLength L (L ^ 2 / σ) = qgPathLength L σ := by
  unfold qgPathLength; field_simp; ring

/-- **The self-dual fixed point** `σ = L`: the duality `σ → L²/σ` fixes `σ = L`, where the path length
attains `2L`. -/
theorem qgPathLength_self_dual (L : ℝ) : qgPathLength L L = 2 * L := by
  unfold qgPathLength
  rcases eq_or_ne L 0 with h | h
  · simp [h]
  · rw [pow_two, mul_div_assoc, div_self h, mul_one, two_mul]

/-- **[extension] The QG path length is bounded below by `2L`** `σ + L²/σ ≥ 2L` for `σ > 0`, with
equality exactly at the self-dual point `σ = L`. So the amplitude `exp[−m(σ + L²/σ)]` is *maximal* at
`σ = L`, and the effective path length can never fall below twice the zero-point length — the
minimal-length content of the duality (AM–GM, sharpening Eq. 13). -/
theorem qgPathLength_ge_two_L (L σ : ℝ) (hσ : 0 < σ) : 2 * L ≤ qgPathLength L σ := by
  unfold qgPathLength
  rw [show σ + L ^ 2 / σ = (σ ^ 2 + L ^ 2) / σ by field_simp, le_div_iff₀ hσ]
  nlinarith [sq_nonneg (σ - L)]

/-! ## C. The zero-point length as a minimal geodesic interval (Eq. 8) -/

/-- **The QG geodesic interval** `√(ℓ² + L²)` (Padmanabhan Eq. 8): the replacement `ℓ → √(ℓ² + L²)`
implementing the zero-point-length shift `σ² → σ² + L²`. -/
noncomputable def qgInterval (L ℓ : ℝ) : ℝ := Real.sqrt (ℓ ^ 2 + L ^ 2)

/-- **The squared interval is `σ² + L²`** — the zero-point-length postulate `σ² → σ² + L²`. -/
theorem qgInterval_sq (L ℓ : ℝ) : (qgInterval L ℓ) ^ 2 = ℓ ^ 2 + L ^ 2 := by
  unfold qgInterval; exact Real.sq_sqrt (by positivity)

/-- **[extension] The zero-point length is a minimal length** `√(ℓ² + L²) ≥ |L|`: the QG geodesic
interval can never fall below the zero-point length `L`, whatever the coordinate separation `ℓ`. This is
the rigorous minimal-length statement implicit in the `σ² → σ² + L²` postulate (Eq. 8). -/
theorem qgInterval_ge_L (L ℓ : ℝ) : |L| ≤ qgInterval L ℓ := by
  unfold qgInterval
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ℓ])

/-- **The minimum is attained at `ℓ = 0`** `√(0 + L²) = |L|`: even a path of zero coordinate length has
geodesic interval `L` — the defining feature of the zero-point length. -/
theorem qgInterval_at_zero (L : ℝ) : qgInterval L 0 = |L| := by
  unfold qgInterval; rw [show (0 : ℝ) ^ 2 + L ^ 2 = L ^ 2 by ring, Real.sqrt_sq_eq_abs]

/-! ## D. The heat-kernel form of the zero-point length (Eq. 9/23) -/

/-- **The `L²/4s` factor is the exponent shift `σ² → σ² + L²`** (Padmanabhan Eq. 9/23). The QG heat
kernel carries `exp(−m²s − L²/4s)`; on the leading heat-kernel behaviour `K_std ~ s⁻² exp(−σ²/4s)` this
adds `L²/4s` to the exponent, `σ²/4s + L²/4s = (√(σ²+L²))²/4s` — exactly `σ² → σ² + L²`. -/
theorem heat_zeroPoint_shift (L σ s : ℝ) :
    σ ^ 2 / (4 * s) + L ^ 2 / (4 * s) = (qgInterval L σ) ^ 2 / (4 * s) := by
  rw [qgInterval_sq]; ring

/-! ## E. The equivalence-principle constraint (Eq. 14) -/

/-- **The equivalence-principle coefficient** `m_g/m_i` (Padmanabhan Eq. 14): the coefficient of `L²/σ`
in the exponent `(1/λ_c)[σ + (m_g/m_i)(L²/σ)]` when the inertial and gravitational masses differ. -/
noncomputable def eepPathCoefficient (mi mg : ℝ) : ℝ := mg / mi

/-- **The universal geometric form requires the equivalence principle** (Padmanabhan Eq. 14). The
coefficient of `L²/σ` equals `1` — giving the mass-independent, purely geometric path length `σ + L²/σ`
and hence a universal zero-point length — **iff** the inertial and gravitational masses coincide,
`m_i = m_g`. The zero-point-length duality is tied to the principle of equivalence. -/
theorem eepPathCoefficient_eq_one_iff (mi mg : ℝ) (hmi : mi ≠ 0) :
    eepPathCoefficient mi mg = 1 ↔ mi = mg := by
  unfold eepPathCoefficient
  rw [div_eq_one_iff_eq hmi]; exact eq_comm


/-- Link found by `#zil_link`: `comptonTemperature` is `gravitationalLength` under `the same names` with conversion `kB^-1 · c^4 · G^-1` and prescription `× 1/2 · π^-1`. -/
theorem comptonTemperature_eq_gravitationalLength_scaled (m c kB G : ℝ) (hG : G ≠ 0)
    (hc : c ≠ 0) :
    Physlib.Thermodynamics.comptonTemperature m c kB
      = ((1 / 2 : ℝ) * c ^ 4 / (kB * G * Real.pi)) * Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.gravitationalLength m G c := by
  unfold Physlib.Thermodynamics.comptonTemperature Physlib.Thermodynamics.deBroglieTemperature
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.gravitationalLength
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength

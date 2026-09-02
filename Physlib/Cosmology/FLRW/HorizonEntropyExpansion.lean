/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.HubbleEvolution
public import Physlib.Cosmology.FLRW.Distances
public import Physlib.Thermodynamics.HolographicPrinciple
public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Physlib.Thermodynamics.VerlindeWeakEquivalence
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength

/-!
# Cosmic entropy increase ⟺ universe expansion

The requested equivalence, made exact on existing definitions: the Bekenstein–Hawking
entropy of the Hubble horizon *increases if and only if the universe expands*.

The Hubble sphere `R_H = c/H` has the holographic screen entropy
`S_H = S_BH(4πR_H²) = πc⁵/(GℏH²)` (`horizonEntropy_closed_form`, composed from the
existing `sphereArea`/`holographicBits`/`microstateEntropy` dictionary — Gibbons &
Hawking 1977).  Differentiating along cosmic time and substituting the Friedmann
`Ḣ` equation (`deriv_hubbleConstant_eq_friedmann`, flat `k = 0`, the `Λ`-terms
cancel) gives the entropy production rate

  `Ṡ_H = 8π²c⁵·(ρ + p/c²) / (ℏ·H³)`   (`horizonEntropy_production`),

in which Newton's constant *cancels* — horizon-entropy production is fixed by
matter and `ℏ` alone.  Hence, pointwise in cosmic time:

* **the equivalence** (`horizonEntropy_increase_iff_expansion`): under the strict
  null energy condition `ρ + p/c² > 0`, `Ṡ_H > 0 ↔ H > 0` — *cosmic entropy
  increase is expansion*, each side characterizing the other;
* **the dual equivalence** (`horizonEntropy_increase_iff_nec`): in an expanding
  universe, `Ṡ_H > 0 ↔ ρ + p/c² > 0` — the second law at the horizon *is* the
  null energy condition (the horizon face of the GSL, Davies 1987);
* **the arrow flips with the expansion**
  (`horizonEntropy_decreasing_of_contraction`): in a contracting phase `Ṡ_H < 0` —
  a bounce cosmology has opposing horizon-entropy arrows on its two sides,
  the cosmological face of the two-sided opposing arrows of
  `TimeSymmetricMarkovArrows` (there `sgn t`, here `sgn H`).

The Birkhoff weld (previous module): the Hubble sphere is exactly its own
Schwarzschild radius — `hubbleSphere_schwarzschild`: with the flat first Friedmann
equation, `r_s(M_H) = R_H` for the Misner–Sharp-type mass `M_H = (4π/3)ρR_H³`
enclosed by the horizon.  The screen whose entropy the equivalence tracks is a
marginally trapped Schwarzschild screen, the same `schwarzschildRadius` whose
exterior `BirkhoffMonopoleNonRadiation` froze: at `ℓ = 0` nothing radiates
*through* the horizon; what grows is the horizon's own area, and it grows exactly
when space expands.

**§D — the Clausius face.** With the Gibbons–Hawking temperature `T = ℏH/(2π)`
(`gibbonsHawkingTemperature`), the production rate is exactly the Clausius
relation at the horizon: `T·Ṡ_H = A_H·(ρc² + p)·c`
(`clausius_at_hubble_horizon`) — the energy flux through the horizon area at
speed `c`; read right-to-left, the Jacobson/Cai–Kim thermodynamic derivation of
the Friedmann equation.

**§E — Bianchi and the `k ≠ 0` apparent horizon.** The continuity equation
`ρ̇ = −3H(ρ + p/c²)` is *derived* from the two Friedmann equations
(`FriedmannEquation.continuity_from_friedmann`, now upstream in `HubbleEvolution`;
the sum/product/chain rules live in the `Time` API, `Time.deriv_add` etc.).
For any spatial curvature the first Friedmann equation turns the
apparent-horizon entropy into pure inverse energy density, `S_A = 3c⁵/(8G²ℏρ)`
(`apparentHorizonEntropy_inverse_density` — even `π` cancels), whence
`Ṡ_A = 9c⁵(ρ + p/c²)/(8G²ℏρ²)·H` (`apparentHorizonEntropy_production`) and the
equivalence extends to all three FLRW geometries:
`apparentHorizonEntropy_increase_iff_expansion` — under the strict NEC,
`0 < Ṡ_A ↔ 0 < H`, with the flat case the `k = 0` face.

Honest layering: the identification of `A/4ℓ_P²` as *the* thermodynamic entropy of
the cosmological horizon is the quoted semiclassical input provided by the existing
screen dictionary (the Gibbons–Hawking temperature enters §D as a definition, not
a derivation); the `k ≠ 0` arc fixes `Λ = 0`; the total (horizon + matter) GSL
budget is not formalized.

## References

* G. W. Gibbons, S. W. Hawking, Phys. Rev. D 15 (1977) 2738 (cosmological horizon
  entropy).
* P. C. W. Davies, Class. Quantum Grav. 4 (1987) L225 (cosmological horizon second
  law ⟺ energy conditions).
* T. Jacobson, Phys. Rev. Lett. 75 (1995) 1260; R.-G. Cai, S. P. Kim, JHEP 0502
  (2005) 050 (Friedmann equations from `δQ = T dS` at the apparent horizon).
* Repo modules used: `Cosmology.FLRW.Basic`/`HubbleEvolution` (`hubbleConstant`,
  `FirstOrderFriedmann`, `SecondOrderFriedmann`, `deriv_hubbleConstant_eq_friedmann`),
  `Thermodynamics.HolographicScreenEntropy` (`microstateEntropy ∘ holographicBits`
  dictionary), `Thermodynamics` (`sphereArea`, `holographicBits`),
  `SemiClassical.SchwarzschildVerlinde` (`schwarzschildRadius`),
  `SecondLaw.TimeSymmetricMarkovArrows` (the opposing-arrows shape).


-/

set_option autoImplicit false

@[expose] public section

namespace Cosmology.FLRW.HorizonEntropyExpansion

open Time
open Cosmology.FLRW.FriedmannEquation
open Cosmology.FLRW.Distances
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.Relativity.SemiClassical


/-- **The Hubble-horizon entropy** — the holographic screen entropy of the Hubble
sphere: `microstateEntropy` of the `holographicBits` of the `sphereArea` at the
Hubble radius, the existing Bekenstein–Hawking dictionary evaluated on the
cosmological horizon (Gibbons–Hawking). -/
noncomputable def horizonEntropy (G ℏ c H : ℝ) : ℝ :=
  microstateEntropy (holographicBits (sphereArea (hubbleRadius c H)) G ℏ c)

/-! ## §A — closed form and the Schwarzschild weld -/

/-- **[Closed form] `S_H = πc⁵/(GℏH²)`** — unconditionally (the division-by-zero
conventions of every factor agree). -/
theorem horizonEntropy_closed_form (G ℏ c H : ℝ) :
    horizonEntropy G ℏ c H = Real.pi * c ^ 5 / (G * ℏ * H ^ 2) := by
  unfold horizonEntropy hubbleRadius
  rw [microstateEntropy_eq_quarter, holographicBits_def]
  unfold sphereArea
  ring

/-- **[The Hubble sphere is its own Schwarzschild radius]** with the flat
(`k = 0`, `Λ = 0`) first Friedmann equation, the mass `M_H = (4π/3)ρR_H³` enclosed
by the Hubble sphere has `schwarzschildRadius M_H = R_H` exactly: the cosmological
horizon is a marginal Schwarzschild screen — the same one-parameter exterior that
Birkhoff freezes (`BirkhoffMonopoleNonRadiation`), now with the whole universe
inside it. -/
theorem hubbleSphere_schwarzschild (a ρ : Time → ℝ) (G c : ℝ) (t : Time)
    (hfirst : FirstOrderFriedmann a ρ 0 0 G c t)
    (hH0 : hubbleConstant a t ≠ 0) (hc : c ≠ 0) :
    schwarzschildRadius
        (4 * Real.pi / 3 * ρ t * (hubbleRadius c (hubbleConstant a t)) ^ 3) G c
      = hubbleRadius c (hubbleConstant a t) := by
  have hH2 : (hubbleConstant a t) ^ 2 = 8 * Real.pi * G / 3 * ρ t := by
    have h := hfirst
    unfold FirstOrderFriedmann at h
    simpa [hubbleConstant] using h
  unfold schwarzschildRadius hubbleRadius
  field_simp
  linear_combination (-3 : ℝ) * hH2

/-! ## §B — the entropy production rate -/

/-- **[The chain rule] `Ṡ_H = −2πc⁵·Ḣ/(GℏH³)`** — the horizon entropy responds to
the *change* of the Hubble rate, through the cube of `H`. -/
theorem deriv_horizonEntropy (a : Time → ℝ) (G ℏ c : ℝ) (t : Time)
    (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hH0 : hubbleConstant a t ≠ 0) :
    ∂ₜ (fun s => horizonEntropy G ℏ c (hubbleConstant a s)) t
      = -2 * Real.pi * c ^ 5 / (G * ℏ) * ∂ₜ (hubbleConstant a) t
          / (hubbleConstant a t) ^ 3 := by
  have hfun : (fun s => horizonEntropy G ℏ c (hubbleConstant a s))
      = fun s => (Real.pi * c ^ 5 / (G * ℏ) / hubbleConstant a s)
          / hubbleConstant a s := by
    funext s
    rw [horizonEntropy_closed_form]
    ring
  have hK : DifferentiableAt ℝ (fun _ : Time => Real.pi * c ^ 5 / (G * ℏ)) t :=
    differentiableAt_const _
  have hc1 : DifferentiableAt ℝ
      (fun s => Real.pi * c ^ 5 / (G * ℏ) / hubbleConstant a s) t :=
    (hH.fun_inv hH0).const_mul _
  rw [hfun, Time.deriv_div hc1 hH hH0, Time.deriv_div hK hH hH0]
  simp only [Time.deriv_const, zero_mul, zero_sub]
  field_simp
  ring

/-- **[The Friedmann production rate] `Ṡ_H = 8π²c⁵(ρ + p/c²)/(ℏH³)`** — substituting
the flat-`k` Friedmann `Ḣ` equation.  Newton's constant *cancels*: the horizon
produces entropy at a rate fixed by the matter content and `ℏ` alone, and the
cosmological constant drops out with the `Λ`-cancellation already inside
`deriv_hubbleConstant_eq_friedmann`. -/
theorem horizonEntropy_production (a ρ p : Time → ℝ) (Λ G ℏ c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hH0 : hubbleConstant a t ≠ 0)
    (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0)
    (hfirst : FirstOrderFriedmann a ρ 0 Λ G c t)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    ∂ₜ (fun s => horizonEntropy G ℏ c (hubbleConstant a s)) t
      = 8 * Real.pi ^ 2 * c ^ 5 * (ρ t + p t / c ^ 2)
          / (ℏ * (hubbleConstant a t) ^ 3) := by
  rw [deriv_horizonEntropy a G ℏ c t hH hH0,
    deriv_hubbleConstant_eq_friedmann ha hd_a haz hfirst hsecond]
  simp only [zero_mul, zero_div, add_zero]
  field_simp
  ring

/-! ## §C — the equivalences -/

/-- **[THE EQUIVALENCE: cosmic entropy increase ⟺ expansion.]** Under the strict
null energy condition `ρ + p/c² > 0`, the Hubble-horizon entropy increases *if and
only if* the universe expands:

  `0 < Ṡ_H  ↔  0 < H`.

Both directions follow from one sign: `Ṡ_H = 8π²c⁵(ρ + p/c²)/(ℏH³)` is positive
exactly when `H³` is.  Entropy increase at the cosmological horizon is not merely
*compatible* with expansion — pointwise in cosmic time, each is a complete
characterization of the other. -/
theorem horizonEntropy_increase_iff_expansion (a ρ p : Time → ℝ) (Λ G ℏ c : ℝ)
    (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hH0 : hubbleConstant a t ≠ 0)
    (hG : G ≠ 0) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hnec : 0 < ρ t + p t / c ^ 2)
    (hfirst : FirstOrderFriedmann a ρ 0 Λ G c t)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    0 < ∂ₜ (fun s => horizonEntropy G ℏ c (hubbleConstant a s)) t
      ↔ 0 < hubbleConstant a t := by
  rw [horizonEntropy_production a ρ p Λ G ℏ c t ha hd_a haz hH hH0 hG hℏ.ne' hc.ne'
    hfirst hsecond]
  have hN : 0 < 8 * Real.pi ^ 2 * c ^ 5 * (ρ t + p t / c ^ 2) :=
    mul_pos (by positivity) hnec
  rw [div_pos_iff]
  constructor
  · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · rcases mul_pos_iff.mp h2 with ⟨-, h3⟩ | ⟨hneg, -⟩
      · nlinarith [h3, sq_nonneg (hubbleConstant a t)]
      · linarith
    · linarith
  · intro h
    exact Or.inl ⟨hN, mul_pos hℏ (pow_pos h 3)⟩

/-- **[The dual equivalence: entropy increase ⟺ null energy condition.]** In an
expanding universe, the horizon entropy increases *if and only if* the matter
satisfies the strict null energy condition:

  `0 < Ṡ_H  ↔  0 < ρ + p/c²`.

The second law at the cosmological horizon *is* the null energy condition — the
horizon face of the generalized second law (Davies): phantom matter
(`ρ + p/c² < 0`) is exactly what would shrink the horizon while space expands. -/
theorem horizonEntropy_increase_iff_nec (a ρ p : Time → ℝ) (Λ G ℏ c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hG : G ≠ 0) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hexp : 0 < hubbleConstant a t)
    (hfirst : FirstOrderFriedmann a ρ 0 Λ G c t)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    0 < ∂ₜ (fun s => horizonEntropy G ℏ c (hubbleConstant a s)) t
      ↔ 0 < ρ t + p t / c ^ 2 := by
  rw [horizonEntropy_production a ρ p Λ G ℏ c t ha hd_a haz hH hexp.ne' hG hℏ.ne'
    hc.ne' hfirst hsecond]
  have hD : 0 < ℏ * (hubbleConstant a t) ^ 3 := mul_pos hℏ (pow_pos hexp 3)
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · rcases mul_pos_iff.mp h1 with ⟨-, hX⟩ | ⟨hK, -⟩
      · exact hX
      · have : (0 : ℝ) < 8 * Real.pi ^ 2 * c ^ 5 := by positivity
        linarith
    · linarith
  · intro h
    exact Or.inl ⟨mul_pos (by positivity) h, hD⟩

/-- **[The entropy arrow flips with the expansion.]** In a contracting phase
(`H < 0`, same null energy condition), the horizon entropy *decreases* — the
cosmological face of the opposing two-sided arrows of `TimeSymmetricMarkovArrows`:
a bounce has `Ṡ_H < 0` before and `Ṡ_H > 0` after, the entropy arrow tracking
`sgn H` as the relaxation arrow there tracked `sgn t`. -/
theorem horizonEntropy_decreasing_of_contraction (a ρ p : Time → ℝ) (Λ G ℏ c : ℝ)
    (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hG : G ≠ 0) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hnec : 0 < ρ t + p t / c ^ 2)
    (hcon : hubbleConstant a t < 0)
    (hfirst : FirstOrderFriedmann a ρ 0 Λ G c t)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    ∂ₜ (fun s => horizonEntropy G ℏ c (hubbleConstant a s)) t < 0 := by
  rw [horizonEntropy_production a ρ p Λ G ℏ c t ha hd_a haz hH hcon.ne hG hℏ.ne'
    hc.ne' hfirst hsecond]
  have hN : 0 < 8 * Real.pi ^ 2 * c ^ 5 * (ρ t + p t / c ^ 2) :=
    mul_pos (by positivity) hnec
  have hsq : 0 < (hubbleConstant a t) ^ 2 := by nlinarith [hcon]
  have hD : ℏ * (hubbleConstant a t) ^ 3 < 0 :=
    mul_neg_of_pos_of_neg hℏ (by nlinarith [hcon, hsq])
  exact div_neg_of_pos_of_neg hN hD

/-! ## §D — the Gibbons–Hawking Clausius relation -/

/-- **The Gibbons–Hawking temperature** `T = ℏH/(2π)` (`k_B ≡ 1`, matching the
nat-counted screen entropy) — the horizon temperature seen by the comoving
observer. -/
noncomputable def gibbonsHawkingTemperature (ℏ H : ℝ) : ℝ :=
  ℏ * H / (2 * Real.pi)

/-- **The Gibbons–Hawking temperature with its constants restored** `T_GH = ℏH/(2π k_B)` —
the SI form of `gibbonsHawkingTemperature` (which carries the energy convention `k_B ≡ 1`;
`gibbonsHawkingTemperatureSI_kB_eq` records the conversion).  This is the form on the same
carrier conventions as `Thermodynamics.unruhTemperature`, so the de Sitter weld
`unruh_eq_gibbonsHawkingSI_iff` can be stated. -/
noncomputable def gibbonsHawkingTemperatureSI (ℏ H kB : ℝ) : ℝ :=
  Physlib.Thermodynamics.deBroglieTemperature (ℏ * H) kB

/-- The energy-convention form is `k_B` times the SI form. -/
theorem gibbonsHawkingTemperatureSI_kB_eq {ℏ H kB : ℝ} (hkB : kB ≠ 0) :
    kB * gibbonsHawkingTemperatureSI ℏ H kB = gibbonsHawkingTemperature ℏ H := by
  unfold gibbonsHawkingTemperatureSI Physlib.Thermodynamics.deBroglieTemperature
    gibbonsHawkingTemperature
  field_simp

/-- **The de Sitter weld: the Unruh temperature equals the Gibbons–Hawking temperature exactly
at `a = c·H`** — cosmic expansion read as an acceleration, the de Sitter face of the
equivalence-principle triangle (`unruh_eq_gravityTemperature_iff`: `a = GM/R²`;
`unruhTemperature_eq_hawkingTemperature`: `a = κ`; here: `a = cH`).  `G`-free, hence invariant
under either `G`-typing.  An algebraic identity of carriers, not an independent derivation of
de Sitter thermality. -/
theorem unruh_eq_gibbonsHawkingSI_iff {ℏ kB c H a : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) :
    Physlib.Thermodynamics.unruhTemperature ℏ kB c a = gibbonsHawkingTemperatureSI ℏ H kB
      ↔ a = c * H := by
  have hE : ℏ * H * c / ℏ = c * H := by
    field_simp
  rw [gibbonsHawkingTemperatureSI,
    Physlib.Thermodynamics.unruh_eq_deBroglieTemperature_iff hℏ hkB hc, hE]

/-- **The temperature triangle closes: the Compton temperature equals the Gibbons–Hawking
temperature exactly at `mc² = ℏH`** — the mass whose rest energy is the Hubble energy, de
Sitter's own mass scale `m = ℏH/c²` (Wesson's minimum mass quantum, ~10⁻⁶⁹ kg at the present
epoch).  This is precisely the composition of the two welds through the shared Unruh carrier —
eliminating `a` between `a = c·H` (`unruh_eq_gibbonsHawkingSI_iff`) and `a = mc³/ℏ`
(`unruh_eq_comptonTemperature_iff`) — so the three pairwise constraints among
`unruhTemperature`, `comptonTemperature`, `gibbonsHawkingTemperatureSI` form a *consistent*
triangle, not three independent claims.  `G`-free, hence typing-invariant. -/
theorem comptonTemperature_eq_gibbonsHawkingSI_iff {ℏ kB c H m : ℝ} (hkB : 0 < kB) :
    Physlib.Thermodynamics.comptonTemperature m c kB = gibbonsHawkingTemperatureSI ℏ H kB
      ↔ m * c ^ 2 = ℏ * H := by
  rw [gibbonsHawkingTemperatureSI, Physlib.Thermodynamics.comptonTemperature]
  exact Physlib.Thermodynamics.deBroglieTemperature_inj hkB

/-- **The de Broglie temperature equals the Gibbons–Hawking temperature exactly at `E = ℏ·H`**
— the carrier energy is the Hubble energy, the general-`E` form of
`comptonTemperature_eq_gibbonsHawkingSI_iff` (its instance at `E = mc²`).  Reported by
`#zil_groupoid_report` as an underived composite with proven flanks through the Unruh carrier;
since `gibbonsHawkingTemperatureSI` *is* the de Broglie converter at `E = ℏH`, the direct proof
is the converter's injectivity itself.  `G`-free, hence typing-invariant. -/
theorem deBroglie_eq_gibbonsHawkingSI_iff {ℏ kB E H : ℝ} (hkB : 0 < kB) :
    Physlib.Thermodynamics.deBroglieTemperature E kB = gibbonsHawkingTemperatureSI ℏ H kB
      ↔ E = ℏ * H := by
  rw [gibbonsHawkingTemperatureSI]
  exact Physlib.Thermodynamics.deBroglieTemperature_inj hkB

/-- **The Hawking temperature equals the Gibbons–Hawking temperature exactly at `κ = c·H`** —
the de Sitter horizon's surface gravity (Gibbons–Hawking 1977: the cosmological horizon is a
Killing horizon with `κ = H` in `c = 1` units).  Reported by `#zil_unify_diagram` as an
underived composite with both flanks proven through the Unruh carrier, and proven here *as*
that composition.  With it the four temperatures {Unruh, Compton, Gibbons–Hawking, Hawking}
form a complete proven diagram (WEP depth gate §12). -/
theorem hawking_eq_gibbonsHawkingSI_iff {ℏ kB c H κ : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) :
    hawkingTemperature ℏ κ c kB = gibbonsHawkingTemperatureSI ℏ H kB ↔ κ = c * H := by
  rw [← Physlib.Thermodynamics.unruhTemperature_eq_hawkingTemperature]
  exact unruh_eq_gibbonsHawkingSI_iff hℏ hkB hc

/-- **The Verlinde screen temperature equals the Gibbons–Hawking temperature exactly at
`GM/R² = c·H`** — the radius at which the Newtonian surface gravity equals the de Sitter
acceleration `cH` (the acceleration scale of the observed a₀ ∼ cH₀ coincidence).  Reported by
`#zil_unify_diagram` as an underived composite with both flanks proven through the Unruh
carrier, and proven here *as* that composition.  Carries `G`: exactly one nat off under the
holographic typing (WEP depth gate §13). -/
theorem gravity_eq_gibbonsHawkingSI_iff {M G ℏ kB c H R : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) :
    Physlib.Thermodynamics.verlindeGravityTemperature M G ℏ c R kB
      = gibbonsHawkingTemperatureSI ℏ H kB ↔ G * M / R ^ 2 = c * H := by
  rw [← (Physlib.Thermodynamics.unruh_eq_gravityTemperature_iff hℏ hkB hc hR).mpr rfl]
  exact unruh_eq_gibbonsHawkingSI_iff hℏ hkB hc

/-- **The Yukawa-range face of the de Sitter triangle**: the Compton wavelength — the
screening range of a Yukawa mediator of mass `m` (`Yukawa.ScreenedPotential`,
`reducedYukawa_compton_screening`) — equals the Hubble radius exactly at `ℏH = mc²`: the
*same* constraint as the temperature face (`comptonTemperature_eq_gibbonsHawkingSI_iff`),
here with coefficient exactly one.  The observational reading is counterfactual and
bound-shaped only: a mediator *of* the §11 mass `ℏH/c²` *would* have range equal to the
horizon — graviton-mass bounds are Yukawa-range bounds.  The derived static kernel is the
zero-screening face `1/r`, and that kernel excludes every nonzero screening mass from a
single-radius match (`EntropicNewtonConstantConvergence.newtonPotential_eq_massless_yukawa`,
`Yukawa.ScreenedPotential.yukawaPotential_screeningMass_unique`): within the screened
family, `M = 0` is derived, not chosen. -/
theorem comptonWavelength_eq_hubbleRadius_iff {m c ħ H : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) (hH : 0 < H) :
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength m c ħ = hubbleRadius c H ↔ ħ * H = m * c ^ 2 := by
  unfold Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength hubbleRadius
  rw [div_eq_div_iff (by positivity) hH.ne']
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- **[Clausius at the horizon] `T·Ṡ_H = A_H·(ρc² + p)·c`** — the Cai–Kim identity:
the Gibbons–Hawking temperature times the entropy production rate equals the
energy flux through the horizon (energy density `ρc²` plus pressure work `p`,
crossing the horizon area at speed `c`).  Read right-to-left this is the
thermodynamic derivation of the Friedmann equation from `δQ = T dS`
(Jacobson 1995; Cai–Kim 2005); here, with the Friedmann equations as input, it is
an exact identity — `ℏ` cancels between temperature and entropy, `G` is already
gone. -/
theorem clausius_at_hubble_horizon (a ρ p : Time → ℝ) (Λ G ℏ c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hH0 : hubbleConstant a t ≠ 0)
    (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0)
    (hfirst : FirstOrderFriedmann a ρ 0 Λ G c t)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    gibbonsHawkingTemperature ℏ (hubbleConstant a t)
        * ∂ₜ (fun s => horizonEntropy G ℏ c (hubbleConstant a s)) t
      = sphereArea (hubbleRadius c (hubbleConstant a t)) * (ρ t * c ^ 2 + p t) * c := by
  rw [horizonEntropy_production a ρ p Λ G ℏ c t ha hd_a haz hH hH0 hG hℏ hc
    hfirst hsecond]
  unfold gibbonsHawkingTemperature sphereArea hubbleRadius
  field_simp
  ring

/-! ## §E — the `k ≠ 0` apparent horizon (continuity now upstream in
`HubbleEvolution.continuity_from_friedmann`; sum/product/chain rules in the
`Time` API) -/

/-- **[The apparent-horizon entropy is inverse energy density]
`S_A = 3c⁵/(8G²ℏρ)`** — for *any* spatial curvature `k`, the first Friedmann
equation (`Λ = 0`) turns the apparent-horizon radius `R_A = c/√(H² + kc²/a²)` into
`R_A² = 3c²/(8πGρ)`, so the horizon entropy is a pure function of the total energy
density (even `π` cancels): expansion dilutes `ρ`, and *that* is what grows the
horizon. -/
theorem apparentHorizonEntropy_inverse_density (a ρ : Time → ℝ) (k G ℏ c : ℝ)
    (t : Time)
    (hfirst : FirstOrderFriedmann a ρ k 0 G c t)
    (hρ : 0 < ρ t) (hG : 0 < G) (hℏ : ℏ ≠ 0) :
    horizonEntropy G ℏ c
        (Real.sqrt ((hubbleConstant a t) ^ 2 + k * c ^ 2 / (a t) ^ 2))
      = 3 * c ^ 5 / (8 * G ^ 2 * ℏ * ρ t) := by
  have harg : (hubbleConstant a t) ^ 2 + k * c ^ 2 / (a t) ^ 2
      = 8 * Real.pi * G / 3 * ρ t := by
    have h := hfirst
    unfold FirstOrderFriedmann at h
    simp only [hubbleConstant]
    linear_combination h
  rw [horizonEntropy_closed_form, harg,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ 8 * Real.pi * G / 3 * ρ t)]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **[The apparent-horizon entropy production, any `k`]
`Ṡ_A = 9c⁵·H·(ρ + p/c²)/(8G²ℏρ²)`** — differentiating the inverse-density form and
substituting the continuity equation: the curvature never reappears, and the rate
is again `G`-free up to the `G²` from the density normalization. -/
theorem apparentHorizonEntropy_production (a ρ p : Time → ℝ) (k G ℏ c : ℝ)
    (t : Time)
    (hfirstAll : ∀ s, FirstOrderFriedmann a ρ k 0 G c s)
    (hρAll : ∀ s, 0 < ρ s) (hG : 0 < G) (hℏ : ℏ ≠ 0)
    (hρd : DifferentiableAt ℝ ρ t)
    (hcont : ∂ₜ ρ t = -3 * hubbleConstant a t * (ρ t + p t / c ^ 2)) :
    ∂ₜ (fun s => horizonEntropy G ℏ c
        (Real.sqrt ((hubbleConstant a s) ^ 2 + k * c ^ 2 / (a s) ^ 2))) t
      = 9 * c ^ 5 * (ρ t + p t / c ^ 2) / (8 * G ^ 2 * ℏ * (ρ t) ^ 2)
          * hubbleConstant a t := by
  have hfun : (fun s => horizonEntropy G ℏ c
      (Real.sqrt ((hubbleConstant a s) ^ 2 + k * c ^ 2 / (a s) ^ 2)))
      = fun s => 3 * c ^ 5 / (8 * G ^ 2 * ℏ) / ρ s := by
    funext s
    rw [apparentHorizonEntropy_inverse_density a ρ k G ℏ c s (hfirstAll s)
      (hρAll s) hG hℏ]
    ring
  rw [hfun, Time.deriv_div (differentiableAt_const _) hρd (hρAll t).ne', hcont]
  simp only [Time.deriv_const]
  field_simp
  ring

/-- **[THE EQUIVALENCE AT ANY CURVATURE: entropy increase ⟺ expansion.]** For all
three FLRW spatial geometries (`k` arbitrary, `Λ = 0`), under the strict null
energy condition, the apparent-horizon entropy increases *if and only if* the
universe expands:

  `0 < Ṡ_A  ↔  0 < H`.

The `k = 0` equivalence (`horizonEntropy_increase_iff_expansion`) is the flat face
of this one; the continuity equation that fixes the sign is itself *derived* from
the Friedmann pair (`continuity_from_friedmann`), so the only physical inputs are
the Einstein equations on FLRW, the null energy condition, and the holographic
screen dictionary. -/
theorem apparentHorizonEntropy_increase_iff_expansion (a ρ p : Time → ℝ)
    (k G ℏ c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hρAll : ∀ s, 0 < ρ s) (hρd : DifferentiableAt ℝ ρ t)
    (hnec : 0 < ρ t + p t / c ^ 2)
    (hfirstAll : ∀ s, FirstOrderFriedmann a ρ k 0 G c s)
    (hsecond : SecondOrderFriedmann a ρ p 0 G c t) :
    0 < ∂ₜ (fun s => horizonEntropy G ℏ c
        (Real.sqrt ((hubbleConstant a s) ^ 2 + k * c ^ 2 / (a s) ^ 2))) t
      ↔ 0 < hubbleConstant a t := by
  have hcont := continuity_from_friedmann a ρ p k 0 G c t ha hd_a haz hH hG.ne'
    hc.ne' hfirstAll hsecond
  rw [apparentHorizonEntropy_production a ρ p k G ℏ c t hfirstAll hρAll hG hℏ.ne'
    hρd hcont]
  have hC : 0 < 9 * c ^ 5 * (ρ t + p t / c ^ 2) / (8 * G ^ 2 * ℏ * (ρ t) ^ 2) :=
    div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hc 5)) hnec)
      (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hG 2)) hℏ)
        (pow_pos (hρAll t) 2))
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨-, hHpos⟩ | ⟨hneg, -⟩
    · exact hHpos
    · linarith
  · intro h
    exact mul_pos hC h

/-! ## §F — the length-scale pentagon welds

The five length carriers — `schwarzschildRadius` (gravity's horizon scale),
`gravitationalLength` (its unit-mass half), `comptonWavelength` (the quantum scale),
`planckLength` (their geometric mean), `hubbleRadius` (the cosmological scale) — form a
pentagon in the bridge groupoid.  `#zil_groupoid_report` found four of its ten edges
homogeneous but unproven; the four welds below close them.  Guarded by
`Physlib.Meta.LengthPentagonGate`. -/

section LengthScaleWelds

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength

/-- **The Schwarzschild radius is twice the gravitational length**, `r_s = 2·λ_g` — the
same `GM/c²` seen by the horizon (factor 2) and by the zero-point-length construction
(factor 1).  Reported by `#zil_groupoid_report` as an underived composite of the length
pentagon; the direct proof is definitional. -/
theorem schwarzschildRadius_eq_two_gravitationalLength (M G c : ℝ) :
    schwarzschildRadius M G c = 2 * gravitationalLength M G c := by
  unfold schwarzschildRadius gravitationalLength
  ring

/-- **`r_s · λ_C = 2 ℓ_P²` with the Planck length by name** — the mass-independent
geometric-mean identity (`EntanglementScreenArea.schwarzschildCompton_geometricMean`)
restated against `planckLength` itself, closing the Schwarzschild–Planck edge of the
length pentagon: gravity's length times quantum mechanics' length is twice the Planck
area, for every mass. -/
theorem schwarzschildCompton_eq_two_planckLength_sq {M G c ħ : ℝ}
    (hM : M ≠ 0) (hc : 0 < c) (hG : 0 ≤ G) (hħ : 0 ≤ ħ) :
    schwarzschildRadius M G c *
        Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength
          M c ħ
      = 2 * planckLength G ħ c ^ 2 := by
  have hsq : planckLength G ħ c ^ 2 = planckLengthSq G ħ c := by
    unfold planckLength
    exact Real.sq_sqrt (by unfold planckLengthSq; positivity)
  rw [hsq]
  unfold schwarzschildRadius planckLengthSq
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength
  field_simp

/-- **The gravitational length reaches the Hubble radius exactly at `GmH = c³`** — the
mass whose `λ_g` spans the Hubble sphere is `m = c³/(GH)`, the Hoyle–Carvalho mass of
the observable universe (twice the Hubble-sphere Schwarzschild mass of
`hubbleSphere_schwarzschild`).  Closes the gravitational–Hubble edge of the length
pentagon. -/
theorem gravitationalLength_eq_hubbleRadius_iff {m G c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    gravitationalLength m G c = hubbleRadius c H ↔ G * m * H = c ^ 3 := by
  unfold gravitationalLength hubbleRadius
  rw [div_eq_div_iff (by positivity) hH.ne']
  constructor <;> intro h <;> linear_combination h

/-- **The Planck length reaches the Hubble radius exactly at `GħH² = c⁵`** — equivalently
`E_P = ħH` at Planck curvature: the de Sitter face of the quantum-gravity corner, where
the smallest length in the pentagon meets the largest.  Closes the Planck–Hubble edge of
the length pentagon. -/
theorem planckLength_eq_hubbleRadius_iff {G ħ c H : ℝ}
    (hG : 0 ≤ G) (hħ : 0 ≤ ħ) (hc : 0 < c) (hH : 0 < H) :
    planckLength G ħ c = hubbleRadius c H ↔ G * ħ * H ^ 2 = c ^ 5 := by
  have h1 : hubbleRadius c H = Real.sqrt ((c / H) ^ 2) := by
    rw [Real.sqrt_sq (by positivity)]; rfl
  rw [planckLength, h1,
    Real.sqrt_inj (by unfold planckLengthSq; positivity) (by positivity)]
  unfold planckLengthSq
  rw [div_pow, div_eq_div_iff (by positivity) (by positivity)]
  constructor <;> intro h <;> linear_combination h

end LengthScaleWelds

end Cosmology.FLRW.HorizonEntropyExpansion

end

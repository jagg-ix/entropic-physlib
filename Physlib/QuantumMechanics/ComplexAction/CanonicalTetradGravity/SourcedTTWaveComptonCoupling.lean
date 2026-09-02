/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave
public import Physlib.Thermodynamics.GravitationalCouplingSystem
public import Physlib.Units.GravitationalCouplingDimensions

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTTWaveHolographicCoupling -/

/-!
# The sourced TT gravitational wave with the holographic Newton constant

The sourced transverse-traceless wave equation `□h^TT = −(16πG/c⁴)·T^TT`
(`SourcedTransverseTracelessWave`) carries Newton's constant `G` as an input.  In the
holographic/entropic programme `G` is *not* an input: it is reconstructed from a
`G`-free bit count,

`G = A·c³/(N·ℏ)`  (`newtonG_holographic`, the inverse of `holographicBits A G ℏ c = Ac³/(Għ)`),

the area-per-bit form of Newton's constant.  This module re-evaluates the gravitational
wave coupling at that holographic `G`:

* `einsteinTTCoupling_bitForm` — the coupling counted in holographic bits,
  `−16πG/c⁴ = −16π·(A/N)/(ℏc)` (twice the trace-reversed `8π(A/N)/(ℏc)`);
* `newtonG_holographic_holographicBits` — reconstructing `G` from its own bit count
  returns `G`;
* `einsteinTTCoupling_holographicNewton` — the coupling at the holographic constant,
  `−16πA/(Nℏc)`;
* `sourcedTTWave_holographic` — the sourced TT wave field equation
  `□h = −(16π·(Ac³/Nℏ)/c⁴)·T^TT` with the Newton constant counted in holographic bits.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

/-- **The gravitational-wave coupling in holographic bits.**  When the bit count is the
holographic count `N = A c³/(Għ)`, the transverse-traceless coupling `−16πG/c⁴` is
`−16π·(A/N)/(ℏc)` — the radiative source `T^TT` gravitates at `16π` Planck areas-per-bit
over `ℏc`, twice the trace-reversed `8π(A/N)/(ℏc)`. -/
@[zil_level bridge_theorem]
theorem einsteinTTCoupling_bitForm (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hN : N = holographicBits (sphereArea R) G ℏ c) :
    einsteinTTCoupling G c = -(16 * Real.pi * (sphereArea R / N) / (ℏ * c)) := by
  rw [einsteinTTCoupling_eq_neg_two_mul, einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hN]
  ring

/-- **The holographic Newton constant** `G = A·c³/(N·ℏ)`: Newton's constant reconstructed
from the holographic bit count `N` of a screen of area `A`. -/
def newtonG_holographic (A ℏ c N : ℝ) : ℝ := A * c ^ 3 / (N * ℏ)

/-- **Reconstructing `G` from its own holographic bit count returns `G`** — the area-per-bit
Newton constant is the exact inverse of `holographicBits`. -/
@[zil_level physical_theorem]
theorem newtonG_holographic_holographicBits (A G ℏ c : ℝ)
    (hA : A ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) :
    newtonG_holographic A ℏ c (holographicBits A G ℏ c) = G := by
  unfold newtonG_holographic holographicBits
  field_simp

/-- **The gravitational-wave coupling at the holographic Newton constant** is
`−16πA/(N·ℏ·c)`. -/
@[zil_level physical_theorem]
theorem einsteinTTCoupling_holographicNewton (A ℏ c N : ℝ) (hc : c ≠ 0) :
    einsteinTTCoupling (newtonG_holographic A ℏ c N) c = -(16 * Real.pi * A / (N * ℏ * c)) := by
  unfold einsteinTTCoupling newtonG_holographic
  rw [neg_inj]
  field_simp

/-! ## The sourced field equation with the holographic constant -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The sourced transverse-traceless wave equation with the holographic Newton
constant.**  The retarded field `h = −(16π·(Ac³/Nℏ)/c⁴)·G_ret(T^TT)` solves
`□h = −(16π·G_holographic/c⁴)·T^TT` with `G` reconstructed from the holographic bit count —
the gravitational wave sourced by `T^TT` with no `G` input, only a bit count. -/
@[zil_level bridge_theorem]
theorem sourcedTTWave_holographic (box gret : V →ₗ[ℝ] V) (hGreen : ∀ s, box (gret s) = s)
    (A ℏ c N : ℝ) (TTT : V) :
    box (einsteinTTCoupling (newtonG_holographic A ℏ c N) c • gret TTT)
      = einsteinTTCoupling (newtonG_holographic A ℏ c N) c • TTT :=
  sourcedTTWave_retarded_solution box gret hGreen (newtonG_holographic A ℏ c N) c TTT

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

zil attach einsteinTTCoupling_bitForm where
  formalizes @ "claim:the-gravitational-wave-coupling-minus-sixteen-pi-g-over-c-fourth-equals-minus-sixteen-pi-area-per-bit-over-hbar-c-when-the-bit-count-is-the-holographic-count",
  supported_by @ "lean:Physlib.Thermodynamics.GravitationalCouplingSystem.einsteinCoupling_bitForm"

zil attach sourcedTTWave_holographic where
  formalizes @ "claim:the-sourced-transverse-traceless-wave-equation-box-h-equals-minus-sixteen-pi-holographic-g-over-c-fourth-times-t-tt-holds-with-newtons-constant-reconstructed-from-the-holographic-bit-count-no-g-input",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic",
  caveat @ "claim:this-uses-the-area-per-bit-holographic-newton-constant-a-c-cubed-over-n-hbar-and-the-abstract-retarded-green-inverse-not-a-specific-constructed-propagator"

zil attach newtonG_holographic_holographicBits where
  formalizes @ "claim:reconstructing-newtons-constant-from-its-own-holographic-bit-count-returns-g-the-area-per-bit-constant-is-the-inverse-of-holographic-bits"

zil_file_contract physlib.sourcedTTWaveHolographicCoupling where
  promises "The sourced transverse-traceless gravitational wave equation re-evaluated with the holographic Newton constant, which is reconstructed from a G-free bit count as A c cubed over N hbar rather than taken as input. The wave coupling minus sixteen pi G over c fourth equals minus sixteen pi area-per-bit over hbar c when the bit count is holographic, twice the trace-reversed eight pi area-per-bit; reconstructing G from its own holographic bit count returns G; the coupling at the holographic constant is minus sixteen pi A over N hbar c; and the sourced field equation box h equals minus sixteen pi holographic-G over c fourth times T-TT holds with Newton's constant counted in holographic bits and no G input."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic",
    "lean:Physlib.Thermodynamics.holographicBits"
  ]
  forbids_substitutes [
    "reading the area-per-bit holographic Newton constant as an independent measured input",
    "reading the abstract retarded Green inverse as a specific constructed propagator"
  ]
  witnessed_by [
    einsteinTTCoupling_bitForm,
    newtonG_holographic_holographicBits,
    einsteinTTCoupling_holographicNewton,
    sourcedTTWave_holographic
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.sourcedTTWaveHolographicCoupling

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence -/

/-!
# The holographic and Compton forms of Newton's constant agree

The two `G`-free routes to Newton's constant coincide exactly at the Compton-cell tiling:

* the **holographic** form `newtonG_holographic A ℏ c N = A c³/(N ℏ)` (area `A` in `N` cells), and
* the **Compton** form `G = ℏ c/m²` (screen mass `m`),

are equal precisely when the cell area is the squared reduced Compton wavelength `A/N = (ℏ/(mc))²`.  This
links the horizon-reconstruction of `G` (`HolographicNewtonFromBlackHoleHorizon`) to the entropic
Compton-clock coupling `ComptonCellNewtonConstant.countedNewtonG = ℏc/m²`.

A companion result closes the dimensional bookkeeping of the SI spatial-width form
`G_count = ℏ c σx⁴/μ²`: with `[ℏ] = ML²T⁻¹`, `[c] = LT⁻¹`, `[σx] = L`, `[μ] = ML²`, the assembled
expression carries exactly the Newton-constant dimension `L³M⁻¹T⁻²`.

* `newtonG_holographic_eq_comptonNewton` — `A c³/(N ℏ) = ℏc/m²` at `A = N (ℏ/(mc))²`.
* `comptonSpatialNewtonG_dim` — `[ℏ c σx⁴/μ²] = [G]`.

Honest scope: the algebraic equivalence conditional on the Compton-cell area, and the dimensional identity
of the spatial-width coupling; no numerical value of `G` is predicted.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave
open Dimension.LTMCTI
open Physlib.Units.InformationDimensionCollision
open Physlib.Units.GravitationalCouplingDimensions

/-- **The holographic and Compton forms of `G` agree at the Compton-cell tiling.**  When the holographic
cell area equals the squared reduced Compton wavelength `A/N = (ℏ/(mc))²`, the area-per-bit coupling
`A c³/(N ℏ)` equals the Compton coupling `ℏ c/m²` — linking the horizon bit-count reconstruction of `G` to
the entropic Compton-clock coupling. -/
@[zil_level bridge_theorem]
theorem newtonG_holographic_eq_comptonNewton (A ℏ c N m : ℝ)
    (hN : N ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0)
    (hcell : A = N * (ℏ / (m * c)) ^ 2) :
    newtonG_holographic A ℏ c N = ℏ * c / m ^ 2 := by
  unfold newtonG_holographic
  rw [hcell]
  field_simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- **The SI spatial-width coupling `ℏ c σx⁴/μ²` carries the Newton-constant dimension** `L³M⁻¹T⁻²`
(with `[ℏ] = ML²T⁻¹`, `[c] = LT⁻¹`, `[σx] = L`, `[μ] = ML²`) — the assembled dimensional check of the
`G_count = ℏ c σx⁴/μ²` form (the component dimensions `[μ] = ML²`, `[μ/σx²] = M` are established elsewhere;
this witnesses the full headline formula). -/
@[zil_level physical_theorem]
theorem comptonSpatialNewtonG_dim :
    action_dim * velocity_dim * L𝓭 ^ (4 : ℚ) / (M𝓭 * L𝓭 ^ (2 : ℚ)) ^ (2 : ℚ) = newtonConstant_dim := by
  ext b <;> cases b <;> norm_num [action_dim, velocity_dim, newtonConstant_dim]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence

zil attach newtonG_holographic_eq_comptonNewton where
  formalizes @ "claim:the-holographic-area-per-bit-newton-constant-a-c-cubed-over-n-hbar-equals-the-compton-newton-constant-hbar-c-over-m-squared-exactly-when-the-cell-area-is-the-squared-reduced-compton-wavelength-a-over-n-equals-hbar-over-m-c-squared",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic"

zil attach comptonSpatialNewtonG_dim where
  formalizes @ "claim:the-si-spatial-width-coupling-hbar-c-sigma-x-to-the-fourth-over-mu-squared-carries-exactly-the-newton-constant-dimension-length-cubed-over-mass-times-time-squared"

zil_file_contract physlib.holographicComptonNewtonEquivalence where
  promises "The holographic and Compton forms of Newton's constant agree. The two G-free routes to Newton's constant coincide exactly at the Compton-cell tiling: the holographic area-per-bit form, the screen area times c cubed over the bit count times hbar, and the Compton form, hbar c over the screen mass squared, are equal precisely when the cell area is the squared reduced Compton wavelength, the area over bit count equals hbar over m c all squared. This links the horizon bit-count reconstruction of G to the entropic Compton-clock coupling. A companion dimensional result closes the bookkeeping of the SI spatial-width form G equals hbar c sigma-x to the fourth over mu squared: with the standard dimensions of hbar, c, the spatial width, and the mass-length-squared conversion scale, the assembled expression carries exactly the Newton-constant dimension length cubed over mass times time squared. Honest scope: the algebraic equivalence conditional on the Compton-cell area and the dimensional identity of the spatial-width coupling; no numerical value of G is predicted."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic",
    "lean:Physlib.Units.GravitationalCouplingDimensions.newtonConstant_dim"
  ]
  forbids_substitutes [
    "reading the conditional equivalence of the two G forms as a numerical prediction of Newton's constant from no physical input"
  ]
  witnessed_by [
    newtonG_holographic_eq_comptonNewton,
    comptonSpatialNewtonG_dim
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.holographicComptonNewtonEquivalence

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTTWaveComptonCoupling -/

/-!
# The sourced TT gravitational wave and the value `ℏc/m²` of the holographic constant

The holographic Newton constant is **not** constructed from the Compton mass.  It is
constructed from the `G`-free holographic bit count — the area-per-bit form
`G = A·c³/(N·ℏ)` (`SourcedTTWaveHolographicCoupling.newtonG_holographic`), where `A` is the
screen area and `N` the Compton-cell tiling count, both free of `G`.  Its *value* happens
to be `ℏc/m²`, with the Compton mass `m` entering only through the cell area
`A/N = λ_C² = (ℏ/mc)²` — it is a derived value, not a construction input.

This module makes that derivation explicit and evaluates the gravitational wave coupling at
the resulting value:

* `newtonG_holographic_comptonCell` — the holographically-constructed `G = Ac³/(Nℏ)` reduces
  to `ℏc/m²` exactly when the area-per-bit is the Compton cell area `(ℏ/mc)²` (the content of
  `ComptonCellNewtonConstant`);
* `einsteinTTCoupling_compton` / `einsteinTTCoupling_comptonEnergy` — the wave coupling at
  that value, `−16πℏ/(m²c³)` and, through the Compton rest energy `E = mc²`, `−16πℏc/E²`;
* `sourcedTTWave_compton` — the field equation with that value of the coupling.

The unification is at the level of the *value*: the single mass `m` labels the derived value
of the holographically-constructed `G = ℏc/m²`, the relational-clock energy `E = mc²` (the
`E_sys` of the Page–Wootters Leggett–Garg phase), and the wave coupling `−16πℏc/E²`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

/-- **The value `ℏc/m²`** that the holographically-constructed Newton constant takes — a
*derived value*, `m` entering through the Compton cell area `λ_C = ℏ/mc`, not a construction
from the mass. -/
def newtonG_compton (ℏ c m : ℝ) : ℝ := ℏ * c / m ^ 2

/-- **The holographically-constructed `G` reduces to `ℏc/m²`.**  The area-per-bit constant
`G = A·c³/(N·ℏ)` (`newtonG_holographic`, built from a `G`-free screen area and bit count)
equals `ℏc/m²` exactly when the area-per-bit `A/N` is the Compton cell area `(ℏ/mc)²` — so
`ℏc/m²` is the *value* of the holographic construction, not an independent Compton-mass
input. -/
@[zil_level bridge_theorem]
theorem newtonG_holographic_comptonCell (m c ℏ N : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hN : N ≠ 0) :
    newtonG_holographic ((ℏ / (m * c)) ^ 2 * N) ℏ c N = newtonG_compton ℏ c m := by
  unfold newtonG_holographic newtonG_compton
  field_simp

/-- **Compton and position-variance forms of the value agree** — at the Caticha–Cafaro
inference mass `m = 1/σ₀²`, `ℏc/m² = ℏcσ₀⁴` (the value of
`ComptonCellNewtonConstant.newtonG_from_positionVariance`). -/
@[zil_level physical_theorem]
theorem newtonG_compton_inferenceMass (σ₀ ℏ c : ℝ) (hσ : σ₀ ≠ 0) :
    newtonG_compton ℏ c (1 / σ₀ ^ 2) = ℏ * c * σ₀ ^ 4 := by
  unfold newtonG_compton
  field_simp

/-- **The gravitational-wave coupling at the value `ℏc/m²`** is `−16πℏ/(m²c³)`. -/
@[zil_level bridge_theorem]
theorem einsteinTTCoupling_compton (ℏ c m : ℝ) (hc : c ≠ 0) (hm : m ≠ 0) :
    einsteinTTCoupling (newtonG_compton ℏ c m) c = -(16 * Real.pi * ℏ / (m ^ 2 * c ^ 3)) := by
  unfold einsteinTTCoupling newtonG_compton
  rw [neg_inj]
  field_simp

/-- **The gravitational-wave coupling through the Compton clock energy** `E = mc²`:
`−16πℏc/E²`.  The same energy that drives the Page–Wootters Leggett–Garg phase labels the
gravitational-wave coupling. -/
@[zil_level bridge_theorem]
theorem einsteinTTCoupling_comptonEnergy (ℏ c E : ℝ) (hc : c ≠ 0) (hE : E ≠ 0) :
    einsteinTTCoupling (newtonG_compton ℏ c (E / c ^ 2)) c = -(16 * Real.pi * ℏ * c / E ^ 2) := by
  unfold einsteinTTCoupling newtonG_compton
  rw [neg_inj]
  field_simp

/-! ## The sourced field equation at that value -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The sourced transverse-traceless wave equation at the value `ℏc/m²`.**  The retarded
field `h = −(16π·(ℏc/m²)/c⁴)·G_ret(T^TT)` solves `□h = −(16π·(ℏc/m²)/c⁴)·T^TT` — the coupling
carried by the derived value of the holographically-constructed `G`. -/
@[zil_level bridge_theorem]
theorem sourcedTTWave_compton (box gret : V →ₗ[ℝ] V) (hGreen : ∀ s, box (gret s) = s)
    (ℏ c m : ℝ) (TTT : V) :
    box (einsteinTTCoupling (newtonG_compton ℏ c m) c • gret TTT)
      = einsteinTTCoupling (newtonG_compton ℏ c m) c • TTT :=
  sourcedTTWave_retarded_solution box gret hGreen (newtonG_compton ℏ c m) c TTT

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

zil attach newtonG_holographic_comptonCell where
  formalizes @ "claim:the-holographically-constructed-newton-constant-a-c-cubed-over-n-hbar-reduces-to-the-value-hbar-c-over-m-squared-exactly-when-the-area-per-bit-is-the-compton-cell-area-so-hbar-c-over-m-squared-is-a-derived-value-not-a-construction-from-the-compton-mass",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic"

zil attach einsteinTTCoupling_comptonEnergy where
  formalizes @ "claim:the-gravitational-wave-coupling-at-the-value-of-g-through-the-compton-clock-energy-e-equals-m-c-squared-is-minus-sixteen-pi-hbar-c-over-e-squared-the-same-energy-that-drives-the-page-wootters-leggett-garg-phase",
  caveat @ "claim:the-holographic-newton-constant-is-constructed-from-the-g-free-area-per-bit-not-from-the-compton-mass-the-value-hbar-c-over-m-squared-is-derived-with-m-entering-only-through-the-cell-area"

zil attach newtonG_compton_inferenceMass where
  formalizes @ "claim:the-compton-mass-and-position-variance-forms-of-the-derived-value-agree-hbar-c-over-m-squared-equals-hbar-c-sigma-zero-fourth-at-the-inference-mass"

zil_file_contract physlib.sourcedTTWaveComptonCoupling where
  promises "The holographic Newton constant is constructed from the G-free area-per-bit A c cubed over N hbar, not from the Compton mass; its derived value is hbar c over m squared, with m entering only through the Compton cell area. The holographically-constructed constant reduces to hbar c over m squared exactly when the area-per-bit is the Compton cell area, and agrees with the position-variance value hbar c sigma zero to the fourth at the inference mass. The gravitational wave coupling at that value is minus sixteen pi hbar over m squared c cubed, and through the Compton rest energy E equals m c squared it is minus sixteen pi hbar c over E squared; the sourced field equation holds with that coupling. The single mass m labels the derived value of the constructed G, the relational-clock energy E equals m c squared driving the Page-Wootters Leggett-Garg phase, and the wave coupling."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic"
  ]
  forbids_substitutes [
    "presenting the value hbar c over m squared as a construction of the holographic constant from the Compton mass rather than a derived value of the area-per-bit construction",
    "treating the E = m c squared clock-energy identification as a proved cross-module theorem"
  ]
  witnessed_by [
    newtonG_holographic_comptonCell,
    newtonG_compton_inferenceMass,
    einsteinTTCoupling_compton,
    einsteinTTCoupling_comptonEnergy,
    sourcedTTWave_compton
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.sourcedTTWaveComptonCoupling


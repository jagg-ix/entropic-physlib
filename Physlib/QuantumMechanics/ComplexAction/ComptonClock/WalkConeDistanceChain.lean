/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkClockGravityChain
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength

meta import Zil

/-!
# The coin angle sets the length unit, the cone, and the entropic distance

`WalkClockGravityChain` carries the walk's coin angle through to Newton's constant, the
inverse-square law and Jacobson's Einstein coupling.  The *length* side of the same chain is already
in the library too:

* `FrequencyTrinity.comptonWavelength_mul_comptonFrequency` — `λ_C ω_C = c`, so the clock fixes a
  length as well as a rate;
* `NagaoNielsenMassShellCone` — the `(1,1)` Minkowski form `L(q) = (Re q)² − (Im q)²` on the complex
  energy–momentum coordinate `q = E/c + i p`, with `nnLorentzForm_energyMomentum : L(q) = (mc)²` and
  `nnConverges_energyMomentum_iff : L(q) > 0 ↔ mc ≠ 0` — the steepest-descent convergence cone **is**
  the forward mass shell;
* `EntropicProperDistance.entropicProperDistance = λ_C · log K` — proper separation measured in
  Compton wavelengths, with `exp(r/λ_C) = K` making `r/λ_C` a logarithmic *dilation* coordinate.

Since the walk fixes `ω_C = θ/2`, the length unit is

  **`λ_C = 2c/θ`**

and three things follow at once.  The entropic proper distance becomes `r = (2c/θ)·log K`.  The
mass-shell invariant becomes `(mc)² = (ħθ/2c)²`.  And the Nagao–Nielsen cone is **timelike exactly
when the coin angle is nonzero** — a walk with `θ = 0` is massless and sits on the light cone, so the
coin angle is precisely what makes the walk's trajectory timelike.

There is also a clean bridge back to the gravitational side: eliminating `θ` between `λ_C = 2c/θ` and
`G = 4c⁵/(ħθ²)` gives

  **`G = c³ λ_C²/ħ`**,

i.e. `λ_C² = Għ/c³` — the Compton wavelength squared *is* the Planck area, which is the
Compton-cell = Planck-cell matching that `ComptonCellNewtonConstant` records as coinciding at the
Planck mass.  The walk's dial and the gravitational constant are two readings of one length.

§F turns that scope caveat into an equation.  `G = ħc/m²` is not a free identification: it holds for
Newton's own `G` **exactly** when `m² = ħc/G`, i.e. only at the Planck mass
(`comptonCellG_eq_iff_planck_mass`), and correspondingly it pins the dial to `θ² = 4c⁵/(ħG)`
(`coin_angle_planck_rigidity`).  Read forwards the chain computes a coupling from a walk; read
backwards it says *which* walk — and the answer is the Planck-mass one.  So the chain cannot be run
at an electron clock or a top-quark clock and still deliver `G`.  §G measures the miss: the walk's
dial in Planck units squares to the dimensionless gravitational coupling,
`θ²ħG/(4c⁵) = α_G = Gm²/(ħc)`, so `θ/θ_P = √α_G` and the constant a particle-mass walk returns
overshoots `G` by `1/α_G` — about `5.7 × 10⁴⁴` at the electron.

Scope.  As in `WalkClockGravityChain`, the `G = ħc/m²` step is the conditional Compton-cell/screen
identification, and `K = coth η` carries the Schmidt-rapidity parametrization of
`MuonAnomaly.SchmidtRapidityHyperbolicUnification`.  What is added is composition, plus the §F
rigidity that says how narrow the identification's domain is.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkClockGravityChain
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength

/-! ### §A — The coin angle is a length -/

/-- **The walk's length unit.**  From `λ_C ω_C = c` and `ω_C = θ/2`, the Compton wavelength is
`2c/θ`: the same dial that fixes the clock rate fixes the length scale, inversely. -/
theorem comptonWavelength_from_coin_angle {θ m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) (hθ : θ ≠ 0) :
    comptonWavelength m c ħ = 2 * c / θ := by
  have hω : comptonFrequency m c ħ = θ / 2 := by
    rw [walkZitterFrequency_eq_coin_angle] at hcoin; linarith
  have hmul := comptonWavelength_mul_comptonFrequency m c ħ hm hc hħ
  rw [hω] at hmul
  field_simp at hmul ⊢
  linarith [hmul]

/-! ### §B — Newton's constant is the Compton area -/

/-- **`G = c³λ_C²/ħ`.**  Eliminating the coin angle between the length unit and
`WalkClockGravityChain.comptonCellG_eq_from_coin_angle` shows Newton's constant is the squared
Compton wavelength in Planck units — equivalently `λ_C² = Għ/c³`, the Compton-cell = Planck-cell
matching.  The walk's dial and `G` are two readings of one length. -/
theorem comptonCellG_eq_wavelength_area {m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonCellG ħ c m = c ^ 3 * comptonWavelength m c ħ ^ 2 / ħ := by
  unfold comptonCellG comptonWavelength
  field_simp

/-! ### §C — The entropic distance in walk units -/

/-- **The entropic proper distance carried by the coin angle.**  `r = λ_C log K` with `λ_C = 2c/θ`
gives `r = (2c/θ) log K`: the walk sets the unit in which entanglement measures separation, and
`r/λ_C = log K` is the logarithmic dilation coordinate. -/
theorem entropicProperDistance_from_coin_angle {θ m c ħ η : ℝ} (hm : m ≠ 0) (hc : c ≠ 0)
    (hħ : ħ ≠ 0) (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) (hθ : θ ≠ 0) :
    entropicProperDistance m c ħ η = 2 * c / θ * Real.log (schmidtNumber η) := by
  unfold entropicProperDistance
  rw [comptonWavelength_from_coin_angle hm hc hħ hcoin hθ]

/-! ### §D — The Nagao–Nielsen cone: timelike iff the coin turns -/

/-- **The mass-shell invariant from the coin angle.**  With `m = ħω_C/c² = ħθ/(2c²)`, the
Nagao–Nielsen `(1,1)` form on the energy–momentum coordinate evaluates to `(ħθ/2c)²`: the walk's dial
sets the radius of the mass shell. -/
theorem nnLorentzForm_from_coin_angle {θ m c ħ p : ℝ} (hc : c ≠ 0)
    (hmass : m = ħ * θ / (2 * c ^ 2)) :
    nnLorentzForm (energyMomentumComplex m c p) = (ħ * θ / (2 * c)) ^ 2 := by
  rw [nnLorentzForm_energyMomentum m c p hc, hmass]
  field_simp

/-- **The walk is timelike exactly when the coin turns.**  The Nagao–Nielsen convergence cone is the
forward mass shell, and at `m = ħθ/(2c²)` it is entered iff `θ ≠ 0`.  A zero coin angle is a massless
walk sitting on the light cone: the coin angle is what makes the trajectory timelike. -/
theorem nnConverges_iff_coin_angle_ne_zero {θ m c ħ p : ℝ} (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hmass : m = ħ * θ / (2 * c ^ 2)) :
    nnConverges (energyMomentumComplex m c p) ↔ θ ≠ 0 := by
  rw [nnConverges_energyMomentum_iff m c p hc, hmass]
  constructor
  · intro h hθ
    apply h
    rw [hθ]
    ring
  · intro hθ
    have h2 : (2 : ℝ) * c ^ 2 ≠ 0 := by positivity
    have hnum : ħ * θ ≠ 0 := mul_ne_zero hħ hθ
    have hdiv : ħ * θ / (2 * c ^ 2) ≠ 0 := div_ne_zero hnum h2
    exact mul_ne_zero hdiv hc

/-! ### §F — The identification pins the dial: it is a Planck-mass walk or nothing -/

/-- **The Compton-cell mass is the Planck mass of the constant it produces.**  Feeding
`G = ħc/m²` into `planckMassSq G ħ c = ħc/G` returns `m²`: the cell scale the count tiles with is,
by construction, the Planck mass of the coupling that comes out. -/
theorem comptonCellG_planckMassSq {m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    planckMassSq (comptonCellG ħ c m) ħ c = m ^ 2 := by
  unfold planckMassSq comptonCellG
  field_simp

/-- **The Compton wavelength is the Planck length of the same constant.**  `λ_C² = Għ/c³` read the
other way: the cell the count tiles with is the Planck cell of the coupling it produces.  This is the
Compton-cell = Planck-cell matching, stated as an identity rather than a coincidence. -/
theorem comptonCellG_planckLengthSq {m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    planckLengthSq (comptonCellG ħ c m) ħ c = comptonWavelength m c ħ ^ 2 := by
  unfold planckLengthSq comptonCellG comptonWavelength
  field_simp

/-- **When the counted constant is Newton's own.**  `ħc/m² = G` holds exactly when `m² = ħc/G`, i.e.
exactly when the walk's mass is the Planck mass.  There is no other solution: the identification is
an equation for `m`, not a free choice of species. -/
theorem comptonCellG_eq_iff_planck_mass {G m c ħ : ℝ} (hm : m ≠ 0) (hG : G ≠ 0) :
    comptonCellG ħ c m = G ↔ m ^ 2 = planckMassSq G ħ c := by
  unfold comptonCellG planckMassSq
  rw [div_eq_iff (pow_ne_zero 2 hm), eq_div_iff hG]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The coin angle is not a dial once `G` is fixed.**  If the walk's Compton-cell constant is to be
Newton's constant, then the mass is forced to the Planck mass and the coin angle to
`θ² = 4c⁵/(ħG)` — twice the inverse Planck time.  So the chain cannot be run at an electron clock, or
a top-quark clock, and still deliver `G`: the scope caveat carried in the docstrings of
`ComptonCellNewtonConstant` and `WalkClockGravityChain` is this equation.  Read forwards the chain
computes a coupling from a walk; read backwards it says which walk. -/
theorem coin_angle_planck_rigidity {G θ m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hG : G ≠ 0) (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ)
    (hmatch : comptonCellG ħ c m = G) :
    m ^ 2 = planckMassSq G ħ c ∧ θ ^ 2 = 4 * c ^ 5 / (ħ * G) := by
  refine ⟨(comptonCellG_eq_iff_planck_mass hm hG).mp hmatch, ?_⟩
  have hωne : comptonFrequency m c ħ ≠ 0 := by
    unfold comptonFrequency
    exact div_ne_zero (mul_ne_zero hm (pow_ne_zero 2 hc)) hħ
  have hθval : θ = 2 * comptonFrequency m c ħ := coin_angle_eq_two_compton hcoin
  have hθne : θ ≠ 0 := by
    rw [hθval]
    exact mul_ne_zero two_ne_zero hωne
  have hGval : G = 4 * c ^ 5 / (ħ * θ ^ 2) := by
    rw [← hmatch, comptonCellG_eq_from_coin_angle hm hc hħ hcoin]
  rw [hGval]
  field_simp

/-! ### §G — How far a particle-mass walk misses, measured -/

/-- **The Compton-cell constant is the one that makes gravity strong.**  `α_G = Gm²/(ħc)` evaluated at
`G = ħc/m²` is exactly `1`: the cell identification is the statement that the dimensionless
gravitational coupling of the tiling scale is unity, which is another way of saying the scale is the
Planck mass. -/
theorem gravitationalCoupling_comptonCellG_eq_one {m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0)
    (hħ : ħ ≠ 0) :
    gravitationalCoupling (comptonCellG ħ c m) m ħ c = 1 := by
  unfold gravitationalCoupling comptonCellG
  field_simp

/-- **The overshoot factor is `1/α_G`.**  Run the chain at a real particle rather than at the Planck
mass and the constant it returns exceeds Newton's by exactly the inverse dimensionless gravitational
coupling of that particle.  For an electron `α_G ≈ 1.8 × 10⁻⁴⁵`, so the returned constant exceeds
`G` by about `5.7 × 10⁴⁴`; even at the top quark, the heaviest clock the trinity module reaches, the
overshoot is still `5 × 10³³`.  The rigidity of §F is not a marginal restriction. -/
theorem comptonCellG_div_eq_inv_gravitationalCoupling {G m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0)
    (hħ : ħ ≠ 0) (hG : G ≠ 0) :
    comptonCellG ħ c m / G = 1 / gravitationalCoupling G m ħ c := by
  unfold comptonCellG gravitationalCoupling
  field_simp

/-- **The coin angle in Planck units is `√α_G`.**  Substituting `θ = 2mc²/ħ` into `θ²ħG/(4c⁵)` returns
`Gm²/(ħc)`, so the walk's dial, measured against the Planck dial `θ_P² = 4c⁵/(ħG)`, squares to the
dimensionless gravitational coupling.  The §F rigidity is the case `α_G = 1`; every real particle
sits at `θ/θ_P = √α_G ≪ 1`, and the ratio is a pure number the walk can be asked for. -/
theorem coin_angle_sq_eq_gravitationalCoupling {G θ m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0)
    (hħ : ħ ≠ 0) (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) :
    θ ^ 2 * (ħ * G) / (4 * c ^ 5) = gravitationalCoupling G m ħ c := by
  have hθval : θ = 2 * comptonFrequency m c ħ := coin_angle_eq_two_compton hcoin
  unfold gravitationalCoupling
  rw [hθval]
  unfold comptonFrequency
  field_simp
  ring

/-! ### §E — The chain -/

/-- **One dial: rate, length, cone, distance and coupling.**  A walk whose coin angle is matched to a
Compton clock fixes the length unit `λ_C = 2c/θ`, the entropic proper distance `r = (2c/θ) log K`,
Newton's constant as the Compton area `G = c³λ_C²/ħ`, and the Nagao–Nielsen mass shell — which it
enters exactly when `θ ≠ 0`.  Composed with `WalkClockGravityChain` and
`QuantumWalkFrequencyTrinity`, one parameter runs from the discrete walk to the field equation and to
the metric scale on which distances are measured. -/
theorem walk_coin_cone_distance_chain {θ m c ħ η : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) (hθ : θ ≠ 0) :
    comptonWavelength m c ħ = 2 * c / θ
      ∧ entropicProperDistance m c ħ η = 2 * c / θ * Real.log (schmidtNumber η)
      ∧ comptonCellG ħ c m = c ^ 3 * comptonWavelength m c ħ ^ 2 / ħ :=
  ⟨comptonWavelength_from_coin_angle hm hc hħ hcoin hθ,
   entropicProperDistance_from_coin_angle hm hc hħ hcoin hθ,
   comptonCellG_eq_wavelength_area hm hc hħ⟩


/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.comptonWavelength_from_coin_angle where
  formalizes @ "claim:the-quantum-walk-coin-angle-fixes-the-compton-wavelength-as-two-c-over-the-coin-angle-and-therefore-the-entropic-proper-distance-and-the-nagao-nielsen-mass-shell-cone",
  epistemic_status @ "derived-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength_mul_comptonFrequency",
  caveat @ "the-coin-angle-to-compton-clock-matching-is-a-hypothesis-of-the-theorem-taken-from-the-kurzynski-walk-dirac-correspondence-not-something-derived-here"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.comptonCellG_eq_iff_planck_mass where
  formalizes @ "claim:the-compton-cell-newton-constant-equals-newtons-constant-exactly-when-the-tiling-mass-is-the-planck-mass-so-the-identification-is-an-equation-for-the-mass-not-a-free-choice-of-particle-species",
  epistemic_status @ "derived-identity",
  requires @ "claim:tiling-an-entanglement-screen-with-compton-cells-rather-than-planck-cells-yields-a-newton-constant-hbar-c-over-mass-squared-without-circularity",
  caveat @ "this-is-an-algebraic-characterisation-of-when-the-compton-cell-identification-can-hold-it-is-not-evidence-that-the-identification-does-hold"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.coin_angle_planck_rigidity where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.comptonCellG_eq_iff_planck_mass",
  formalizes @ "claim:matching-the-walk-compton-cell-constant-to-newtons-constant-forces-the-quantum-walk-coin-angle-to-four-c-to-the-fifth-over-hbar-g-under-the-square-so-the-coin-angle-is-not-a-free-dial-once-gravity-is-fixed",
  epistemic_status @ "derived-identity",
  requires @ "claim:the-compton-cell-newton-constant-equals-newtons-constant-exactly-when-the-tiling-mass-is-the-planck-mass-so-the-identification-is-an-equation-for-the-mass-not-a-free-choice-of-particle-species",
  caveat @ "read-forwards-the-chain-computes-a-coupling-from-a-walk-read-backwards-it-says-which-walk-and-the-answer-is-the-planck-mass-one-so-the-chain-must-not-be-quoted-as-deriving-newtons-constant-from-an-electron-or-top-quark-clock"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.coin_angle_sq_eq_gravitationalCoupling where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung.coin_angle_eq_two_compton",
  formalizes @ "claim:the-quantum-walk-coin-angle-measured-against-the-planck-coin-angle-squares-to-the-dimensionless-gravitational-coupling-g-m-squared-over-hbar-c-so-a-particle-mass-walk-overshoots-newtons-constant-by-the-inverse-of-that-coupling",
  epistemic_status @ "derived-identity",
  requires @ "claim:matching-the-walk-compton-cell-constant-to-newtons-constant-forces-the-quantum-walk-coin-angle-to-four-c-to-the-fifth-over-hbar-g-under-the-square-so-the-coin-angle-is-not-a-free-dial-once-gravity-is-fixed",
  caveat @ "the-overshoot-factor-is-the-inverse-dimensionless-gravitational-coupling-about-five-point-seven-times-ten-to-the-forty-four-at-the-electron-and-still-five-times-ten-to-the-thirty-three-at-the-top-quark"

zil_file_contract physlib.walkConeDistanceChain where
  promises "The quantum-walk coin angle fixes a length as well as a rate. From the Compton relation lambda times omega equals c and the walk identification omega equals half the coin angle, the reduced Compton wavelength is two c over the coin angle, which carries the entropic proper distance to two c over the coin angle times the log of the Schmidt number and evaluates the Nagao-Nielsen Minkowski form on the complex energy-momentum coordinate to the square of hbar times the coin angle over two c. That form is positive exactly when the coin angle is nonzero, so a walk with zero coin angle is massless and sits on the light cone and the coin angle is precisely what makes the trajectory timelike. Eliminating the coin angle between the length unit and the Compton-cell Newton constant gives Newton's constant as the Compton area, c cubed times the squared Compton wavelength over hbar. The decisive content of this file is the bound on that last step. The Compton-cell constant equals Newton's own constant exactly when the tiling mass squared equals hbar c over G, that is only at the Planck mass, so the identification is an equation for the mass and not a free choice of particle species, and it correspondingly pins the coin angle squared to four c to the fifth over hbar G. The size of the restriction is measured rather than asserted: the coin angle in Planck units squares to the dimensionless gravitational coupling G m squared over hbar c, so a walk run at a real particle returns a constant exceeding Newton's by the inverse of that coupling, about five point seven times ten to the forty-four at the electron and still five times ten to the thirty-three at the top quark. The chain therefore computes a coupling from a walk when read forwards and says which walk when read backwards, and only the Planck-mass walk answers."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength_mul_comptonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung.walkZitterFrequency_eq_coin_angle",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkClockGravityChain.comptonCellG_eq_from_coin_angle",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.gravitationalCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnConverges_energyMomentum_iff"]
  forbids_substitutes ["quoting the coin-angle chain as a derivation of Newton's constant from an electron or top-quark clock when the identification admits only the Planck mass",
    "presenting the Compton-cell Newton constant as an independent measurement of G rather than as the conditional cell-equals-screen-scale identification",
    "reading the Planck-mass rigidity as evidence that the Compton-cell identification holds, when it only characterises when it could hold"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.comptonWavelength_from_coin_angle,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.comptonCellG_eq_wavelength_area,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.nnConverges_iff_coin_angle_ne_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.comptonCellG_eq_iff_planck_mass,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.coin_angle_planck_rigidity,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.coin_angle_sq_eq_gravitationalCoupling]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain

end

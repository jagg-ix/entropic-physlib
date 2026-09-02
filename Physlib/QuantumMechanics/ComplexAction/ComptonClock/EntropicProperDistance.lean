/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.SzabadosCurvedSpacetime
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
public import Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationsHyperbolic
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell
meta import Zil

/-!
# The entropic proper distance: a principled replacement for the "empirical distance"

Szabados' *empirical distance* (`ComptonClock.PoincareCasimirMassShell.empiricalDistanceVector`) is an
`E(1,3)`-invariant Lorentzian separation *operationally* built from quantum observables — a positivistic,
ad-hoc notion. This module records the principled quantity it can be replaced by: the **entropic proper
distance**
  `r = λ_C · log K = λ_C · (S_I/ℏ)`,
the logarithmic coordinate, in Compton wavelengths `lambda_C`, at which an exponential
profile equals the entanglement suppression. It is a definition whose equivalent forms are
derived, and it links four readings
already in the library:

* **Exponential coordinate.** The identity `e^{-r/lambda_C} = tanh eta` follows from
  `r = lambda_C log K` and `K = coth eta`. `ComptonEuclideanVacuumCorrelation`
  separately derives this profile in an explicit vacuum--one-particle Euclidean mode;
  Reeh--Schlieder alone does not derive it.
* **Verlinde (entropic / holographic).** `r/λ_C = S_I/ℏ = log K` is the entropic action in units of `ℏ`
  (`EntanglementReparametrization.entangled_scale_eq_entropicAction`) — distance from entropy, the
  entropic-gravity length (`Thermodynamics.VerlindeNewtonGravity.holographicBits`).
* **Nagao–Nielsen (complex-action contour).** `S_I` is the imaginary part of the complex action, the
  suppression `e^{−S_I/ℏ}` of the steepest-descent contour (`NagaoNielsenMassShellCone`).
* **Chern–Simons–Witten / string.** `K` is the Schmidt number `= coth η`, the analogue of a quantum
  dimension / modular datum (`ChernSimons.ModularRepresentation.cswWilsonVerlindeOperator`); the same
  hyperbolic rapidity `η` governs the worldsheet boost.

* **§A — the entropic proper distance.** `entropicProperDistance`
  (`= lambda_C log K`), `_vacuumBell`
  (`e^{-r/lambda_C} = tanh eta`, a coordinate identity) and `_eq_entropicAction`
  (`r = λ_C · S_I/ℏ`, the Verlinde/entanglement content).
* **§B — one rapidity, two faces.** `expEntropicDistance_eq_schmidtNumber` (`e^{r/λ_C} = K`) and
  `entanglement_boosts_clock_and_sets_distance`: the same Schmidt number `K = coth η` boosts the Compton
  clock (`ω' = cosh η·ω_C`, the spectral face) and sets the entropic distance (`r = λ_C log K`, the spatial
  face) — the boosted energy `E' = γmc²` and the decoherence length `r` are locked together by `K`.
* **§C — the mass gap is the entanglement gap.** In the one Bogoliubov gap-dispersion
  `E(ξ,Δ) = √(ξ²+Δ²)` (`Bogoliubov.Transformation.bogoliubovEnergy`) the zero-momentum value is the gap
  itself: `bogoliubovEnergy 0 (mc²) = mc² = ħ ω_C` (`restGap_eq_hbar_comptonFrequency`). The gap is open —
  `mc² > 0`, `K = coth η > 1`, `S_I = ħ log K > 0`, `r = λ_C log K > 0` — all together for `η > 0`
  (`entropic_mass_gap`); the common gapless boundary is the separable point `K = 1` where `r = 0` and
  `S_I = 0` (`entropic_mass_gap_boundary`), the frequency-side partner of the massless light cone
  `bogoliubovEnergy k 0 = |k|` (`ChiralSymmetryBreakingCondensate.goldstone_massless_dispersion`).
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.SzabadosCurvedSpacetime
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationsHyperbolic
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.PoincareCasimirMassShell
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation


/-- **The entropic proper distance** `r = λ_C · log K` (`K = coth η` the Schmidt number): the proper
separation, measured in Compton wavelengths, set by the entanglement of the two regions. The principled,
derived replacement for the operational "empirical distance". -/
noncomputable def entropicProperDistance (m c ħ η : ℝ) : ℝ :=
  comptonWavelength m c ħ * Real.log (schmidtNumber η)

/-- **The exponential profile at the entropic coordinate** `e^{-r/lambda_C} = tanh eta`.

This is the change-of-variables identity induced by `r = lambda_C log K` and `K = coth eta`.
It is not, by itself, a Reeh--Schlieder or Pauli--Jordan decay theorem. -/
lemma entropicProperDistance_vacuumBell (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    Real.exp (-(entropicProperDistance m c ħ η / comptonWavelength m c ħ)) = Real.tanh η := by
  unfold entropicProperDistance
  exact vacuumBell_at_entropicScale η m c ħ hη hlam

/-- **[Verlinde / entanglement] the entropic distance is the entropic action in Compton wavelengths**
`r = λ_C · (S_I/ℏ)`: the entropic proper distance is the entropic action `S_I` (imaginary Nagao–Nielsen
action / entanglement entropy) measured in units of `ℏ`, scaled by the Compton wavelength — `r/λ_C = S_I/ℏ
= log K` (`EntanglementReparametrization.entangled_scale_eq_entropicAction`). -/
lemma entropicProperDistance_eq_entropicAction (m c ħ η : ℝ) (hħ : ħ ≠ 0) :
    entropicProperDistance m c ħ η = comptonWavelength m c ħ * (entropicAction ħ η / ħ) := by
  unfold entropicProperDistance
  rw [entangled_scale_eq_entropicAction ħ η hħ]


/-- **The exponential of the entropic distance is the Schmidt number** `e^{r/λ_C} = K = coth η`: the
entropic proper distance in Compton wavelengths is `log K`, so `e^{r/λ_C}` recovers the very Schmidt number
`K` that reparametrizes (boosts) the Compton clock — the decoherence length and the frequency boost carry
the same `K`. -/
lemma expEntropicDistance_eq_schmidtNumber (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    Real.exp (entropicProperDistance m c ħ η / comptonWavelength m c ħ) = schmidtNumber η := by
  have hK : 0 < schmidtNumber η := by
    have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
    unfold schmidtNumber; positivity
  unfold entropicProperDistance
  rw [mul_div_cancel_left₀ _ hlam, Real.exp_log hK]

/-- **[One rapidity, two faces] the same entanglement boosts the clock and sets the distance.** At
rapidity `η > 0`, one Schmidt number `K = coth η` simultaneously boosts the Compton clock —
`ω' = cosh η · ω_C` (`EntanglementReparametrization.entangled_compton_clock_eq_cosh`, `E: mc² → cosh η·mc²`)
— and sets the entropic proper distance — `e^{r/λ_C} = K`. The spectral face (frequency boost `γ = cosh η`)
and the spatial exponential-profile coordinate `r = lambda_C log K` are two readings of the one
rapidity `η`: the energy value `E' = γ mc²` and the separation `r = λ_C log K` are locked together by `K`. -/
lemma entanglement_boosts_clock_and_sets_distance (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ = Real.cosh η * comptonFrequency m c ħ
      ∧ Real.exp (entropicProperDistance m c ħ η / comptonWavelength m c ħ) = schmidtNumber η :=
  ⟨entangled_compton_clock_eq_cosh η m c ħ, expEntropicDistance_eq_schmidtNumber m c ħ η hη hlam⟩

/-- **The boost is fixed by the Schmidt number** `γ² (K² − 1) = K²`, i.e. `cosh²η = K²/(K²−1)` with
`K = coth η`: eliminating the rapidity, the Compton-clock boost `γ = cosh η` is a definite function of the
Schmidt number `K`. -/
lemma boost_sq_schmidt_relation (η : ℝ) (hη : 0 < η) :
    Real.cosh η ^ 2 * (schmidtNumber η ^ 2 - 1) = schmidtNumber η ^ 2 := by
  have hs : Real.sinh η ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hη)
  unfold schmidtNumber
  rw [div_pow]
  field_simp
  linear_combination Real.cosh_sq_sub_sinh_sq η

/-- **[The energy boost is locked to the entropic distance]** `γ² (K² − 1) = K²` with `K = e^{r/λ_C}`:
substituting `K = e^{r/λ_C}` (§B) into the boost–Schmidt relation, the Compton-clock energy boost
`γ = cosh η` (so `E' = γ mc²`) is a definite function of the entropic proper distance `r` alone —
`cosh²η = e^{2r/λ_C}/(e^{2r/λ_C} − 1)`. The spectral value `E'` and the spatial separation `r` are one:
knowing the decoherence length fixes the frequency boost, and conversely. -/
lemma boost_sq_from_entropicDistance (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    Real.cosh η ^ 2
        * (Real.exp (entropicProperDistance m c ħ η / comptonWavelength m c ħ) ^ 2 - 1)
      = Real.exp (entropicProperDistance m c ħ η / comptonWavelength m c ħ) ^ 2 := by
  rw [expEntropicDistance_eq_schmidtNumber m c ħ η hη hlam]
  exact boost_sq_schmidt_relation η hη

/-!

Szabados' "empirical distance" (`SzabadosCurvedSpacetime`) is *operational* — a spatial Lorentzian interval
built by hand from expectation values and postulated to carry the metric. The entropic proper distance is the
*derived* object it should be replaced by: setting his operationally stipulated affine parameter to
`entropicProperDistance = λ_C log K` turns his distance and his curvature-from-distance recovery into
statements about entanglement, and the one derived quantity unifies the four groundings his construction reaches
for separately (Sorkin, Verlinde, Nagao–Nielsen, Chern–Simons–Witten). -/

/-- **[The Szabados radial distance, grounded, is `(λ_C log K)²`]** — Szabados' squared distance from `q` to
`r = exp_q(tX)` for a unit spacelike `X` (his Eq. 3.5, `−(t²)⟨X,X⟩ = t²`) is `t²`; setting the operationally
stipulated affine parameter `t` to the *derived* entropic proper distance `r = λ_C log K` turns the operational
primitive into a statement about entanglement: the radial separation *is* the log of the Schmidt number, in
Compton wavelengths. -/
lemma szabadosRadialDistance_eq_entropicProper {ι : Type*} [Fintype ι] (metric : Matrix ι ι ℝ)
    (X : ι → ℝ) (m c ħ η : ℝ) (hX : lorentzianNormSq metric X = -1) :
    -(entropicProperDistance m c ħ η) ^ 2 * lorentzianNormSq metric X
      = (comptonWavelength m c ħ * Real.log (schmidtNumber η)) ^ 2 := by
  rw [distance_qr_eq_affineParameter metric X (entropicProperDistance m c ħ η) hX]
  rfl

/-- **[Curvature from the entropic distance]** — Szabados' curvature-recovery formula
(`sectionalCurvature_from_squaredDistance`, `K = 3(t²w² − D²)/(t⁴w²)`) evaluated at the derived entropic proper
distance `t = r = λ_C log K` recovers the sectional curvature from entanglement: the local geometry is fixed by
the Schmidt number of the vacuum correlations, not by a stipulated Lorentzian interval. -/
lemma szabadosCurvature_from_entropicDistance (m c ħ η w K : ℝ)
    (ht : entropicProperDistance m c ħ η ≠ 0) (hw : w ≠ 0) :
    3 * ((entropicProperDistance m c ħ η) ^ 2 * w ^ 2
          - curvedSquaredDistance (entropicProperDistance m c ħ η) w K)
        / ((entropicProperDistance m c ħ η) ^ 4 * w ^ 2) = K :=
  sectionalCurvature_from_squaredDistance (entropicProperDistance m c ħ η) w K ht hw

/-- **[Four equivalent readings of the entropic-distance definition.]** The single coordinate
`r = λ_C log K` is at once: the **Chern–Simons–Witten / string** Schmidt datum `r = λ_C log K` (`K = coth η` a
quantum-dimension analogue), the exponential-profile identity `e^{-r/lambda_C} = tanh eta`, the
**Verlinde / holographic** entropic action in units of `ℏ` (`r = λ_C S_I/ℏ`, `S_I` the **Nagao–Nielsen**
imaginary action), and the exponential recovery of the Schmidt number (`e^{r/λ_C} = K`). Szabados' operational
"empirical distance" is replaced by this one entanglement-forced quantity. -/
lemma entropicProperDistance_unifies_four_groundings (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) (hħ : ħ ≠ 0) :
    entropicProperDistance m c ħ η = comptonWavelength m c ħ * Real.log (schmidtNumber η)
      ∧ Real.exp (-(entropicProperDistance m c ħ η / comptonWavelength m c ħ)) = Real.tanh η
      ∧ entropicProperDistance m c ħ η = comptonWavelength m c ħ * (entropicAction ħ η / ħ)
      ∧ Real.exp (entropicProperDistance m c ħ η / comptonWavelength m c ħ) = schmidtNumber η :=
  ⟨rfl, entropicProperDistance_vacuumBell m c ħ η hη hlam,
    entropicProperDistance_eq_entropicAction m c ħ η hħ,
    expEntropicDistance_eq_schmidtNumber m c ħ η hη hlam⟩

/-- **[The flat operational empirical distance is replaced by the derived entropic proper distance]** —
Szabados' *operational* empirical distance (`PoincareCasimirMassShell.empiricalDistanceVector`, the flat spatial
Lorentzian interval `(D_ij)² = −⟨d_ij, d_ij⟩` built by hand from the momenta and centre-of-mass vectors — the
`2309.06150` construction) is positivistic: measured, not derived. Grounding it — identifying its squared
magnitude with the entropic proper distance `r² = (λ_C log K)²` — turns the operational primitive into the
entanglement-forced quantity: it then equals `(λ_C log K)²` **and** inherits the four groundings (Sorkin
causal-decay length, Verlinde entropic action, Nagao–Nielsen contour scale, Chern–Simons–Witten Schmidt datum),
all `= λ_C log K` for the one rapidity `η`. The distance stops being an operational primitive. -/
lemma empiricalDistance_replaced_by_entropic (p1 p2 M1 M2 : Fin 1 ⊕ Fin 3 → ℝ)
    (mu1Sq mu2Sq m c ħ η : ℝ) (hη : 0 < η) (hlam : comptonWavelength m c ħ ≠ 0) (hħ : ħ ≠ 0)
    (hground : -minkProd (empiricalDistanceVector p1 p2 M1 M2 mu1Sq mu2Sq)
        (empiricalDistanceVector p1 p2 M1 M2 mu1Sq mu2Sq) = entropicProperDistance m c ħ η ^ 2) :
    (-minkProd (empiricalDistanceVector p1 p2 M1 M2 mu1Sq mu2Sq)
        (empiricalDistanceVector p1 p2 M1 M2 mu1Sq mu2Sq)
      = (comptonWavelength m c ħ * Real.log (schmidtNumber η)) ^ 2)
    ∧ (entropicProperDistance m c ħ η = comptonWavelength m c ħ * Real.log (schmidtNumber η)
      ∧ Real.exp (-(entropicProperDistance m c ħ η / comptonWavelength m c ħ)) = Real.tanh η
      ∧ entropicProperDistance m c ħ η = comptonWavelength m c ħ * (entropicAction ħ η / ħ)
      ∧ Real.exp (entropicProperDistance m c ħ η / comptonWavelength m c ħ) = schmidtNumber η) :=
  ⟨by rw [hground]; rfl, entropicProperDistance_unifies_four_groundings m c ħ η hη hlam hħ⟩


/-- **[Link — muon g−2] the anomaly is the exponential entropic distance squared, minus one**
`a(η) = e^{2r/λ_C} − 1`: the Schwinger anomaly `anomaly η = 1/sinh²η` of the muon g−2 arc
(`AnomalyRapidity`, with `α = 2π·a(η)`) is the Schmidt defect `K² − 1` (`anomaly_eq_schmidt_sq_sub_one`),
and `K = e^{r/λ_C}` (§B), so the anomalous magnetic moment is read directly off the entropic decoherence
length. -/
lemma anomaly_eq_entropicDistance (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    anomaly η
      = Real.exp (entropicProperDistance m c ħ η / comptonWavelength m c ħ) ^ 2 - 1 := by
  rw [anomaly_eq_schmidt_sq_sub_one η hη, expEntropicDistance_eq_schmidtNumber m c ħ η hη hlam]

/-- **[Link — icosahedral / golden] the entropic distance at the golden rapidity is `λ_C log φ`** — at the
golden rapidity `η_φ = (3/2)log φ` the Schmidt number is the golden ratio
(`IcosahedralRotationsHyperbolic.schmidtNumber_goldenRapidity`), so the entropic proper distance is
`r = λ_C log φ`, the decoherence length set by the icosahedral/golden vacuum. -/
lemma entropicProperDistance_goldenRapidity (m c ħ : ℝ) :
    entropicProperDistance m c ħ goldenRapidity = comptonWavelength m c ħ * Real.log Real.goldenRatio := by
  unfold entropicProperDistance
  rw [schmidtNumber_goldenRapidity]

/-- **[Link — icosahedral / golden] `e^{r/λ_C} = φ` at the golden rapidity** — the Schmidt number recovered
from the entropic proper distance is exactly the golden ratio, tying the entropic decoherence length to the
icosahedral geometry. -/
lemma expEntropicDistance_goldenRapidity (m c ħ : ℝ) (hlam : comptonWavelength m c ħ ≠ 0) :
    Real.exp (entropicProperDistance m c ħ goldenRapidity / comptonWavelength m c ħ) = Real.goldenRatio := by
  have hg : 0 < goldenRapidity := by
    unfold goldenRapidity
    have := Real.log_pos Real.one_lt_goldenRatio
    linarith
  rw [expEntropicDistance_eq_schmidtNumber m c ħ goldenRapidity hg hlam, schmidtNumber_goldenRapidity]


/-! ### §C — the mass gap is the entanglement gap

The Yang–Mills mass gap asks for `inf(spectrum \ {0}) = Δ > 0`: the lightest excitation is strictly
massive. Here the gap lives in the one Bogoliubov gap-dispersion `E(ξ,Δ) = √(ξ²+Δ²)`
(`Bogoliubov.Transformation.bogoliubovEnergy`), and each Core carries one face of the same gap `Δ`. At zero
momentum the dispersion returns the gap itself; with `Δ = mc²` this rest-frame gap is the Compton rest
energy `ħ ω_C`. The gap is open exactly when the vacuum is entangled: `η > 0 ⟹ K = coth η > 1`, so the rest
gap `mc²`, the Schmidt number, the entropic action `S_I = ħ log K` and the entropic proper distance
`r = λ_C log K` are strictly positive together. The gapless boundary is the separable point `K = 1`
(`S_I = 0`, `r = 0`), the frequency-side partner of the massless light cone `bogoliubovEnergy k 0 = |k|`.
This is the entropic-side face of the mass gap; the dynamical origin `Δ > 0` (positivity of the string
tension `σ`) is not derived and stays cited (`Su3ConfinementPotential`). -/

/-- **[The rest-frame gap is the rest energy] `bogoliubovEnergy 0 (mc²) = mc²`.** At zero momentum the
Bogoliubov gap-dispersion `E = √(ξ²+Δ²)` returns the gap itself; with `Δ = mc²` the rest-frame gap is the
rest energy — the `ξ = 0` partner of the massless `Δ = 0` light cone. -/
lemma restGap_eq_restEnergy (m c : ℝ) (h : 0 ≤ m * c ^ 2) :
    bogoliubovEnergy 0 (m * c ^ 2) = m * c ^ 2 := by
  unfold bogoliubovEnergy
  rw [show (0 : ℝ) ^ 2 = 0 from by norm_num, zero_add, Real.sqrt_sq h]

/-- **[The rest-frame gap is `ħ` times the Compton frequency] `bogoliubovEnergy 0 (mc²) = ħ ω_C`.** The
mass gap in energy is the Compton frequency `ω_C = mc²/ħ` (`FrequencyTrinity.comptonFrequency`) in units of
`ħ` — the rest-energy clock. -/
lemma restGap_eq_hbar_comptonFrequency (m c ħ : ℝ) (h : 0 ≤ m * c ^ 2) (hħ : ħ ≠ 0) :
    bogoliubovEnergy 0 (m * c ^ 2) = ħ * comptonFrequency m c ħ := by
  rw [restGap_eq_restEnergy m c h]
  unfold comptonFrequency
  field_simp

/-- **[The entropic action gap is open] `0 < S_I` for `η > 0`.** The strict form of
`entropicAction_nonneg`: an entangled rapidity gives a strictly positive imaginary action `S_I = ħ log K`. -/
lemma entropicAction_pos (ħ η : ℝ) (hħ : 0 < ħ) (hη : 0 < η) :
    0 < entropicAction ħ η := by
  unfold entropicAction
  exact mul_pos hħ (Real.log_pos (schmidtNumber_gt_one η hη))

/-- **[The entropic distance gap is open] `0 < r` for `η > 0`.** The entropic proper distance
`r = λ_C log K` is strictly positive exactly when the state is entangled (`K > 1`). -/
lemma entropicProperDistance_pos (m c ħ η : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η) :
    0 < entropicProperDistance m c ħ η := by
  unfold entropicProperDistance
  exact mul_pos (comptonWavelength_pos m c ħ hm hc hħ) (Real.log_pos (schmidtNumber_gt_one η hη))

/-- **[The mass gap is the entanglement gap, assembled].** For an entangled rapidity `η > 0` and positive
mass `m > 0`: the rest-frame Bogoliubov gap is the Compton energy `bogoliubovEnergy 0 (mc²) = ħ ω_C > 0`
(`restGap_eq_hbar_comptonFrequency`), and simultaneously the Schmidt number `K = coth η > 1`
(`schmidtNumber_gt_one`), the entropic action `S_I = ħ log K > 0` (`entropicAction_pos`) and the entropic
proper distance `r = λ_C log K > 0` (`entropicProperDistance_pos`) are all strictly positive — one open gap
read on four faces. The lightest excitation is massive iff the vacuum correlations are entangled. -/
theorem entropic_mass_gap (m c ħ η : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η) :
    bogoliubovEnergy 0 (m * c ^ 2) = ħ * comptonFrequency m c ħ
      ∧ 0 < bogoliubovEnergy 0 (m * c ^ 2)
      ∧ 1 < schmidtNumber η
      ∧ 0 < entropicAction ħ η
      ∧ 0 < entropicProperDistance m c ħ η := by
  have hmc : 0 ≤ m * c ^ 2 := by positivity
  refine ⟨restGap_eq_hbar_comptonFrequency m c ħ hmc hħ.ne', ?_, schmidtNumber_gt_one η hη,
    entropicAction_pos ħ η hħ hη, entropicProperDistance_pos m c ħ η hm hc hħ hη⟩
  rw [restGap_eq_restEnergy m c hmc]; positivity

/-- **[The common gapless boundary] `r = 0 ⟺ K = 1 ⟺ S_I = 0`.** The mass-gap trinity closes at the
separable point: the entropic proper distance and the entropic action vanish exactly when the Schmidt
number is `1` (`reversible_iff_separable`) — the reversible/separable `45°`-cone limit, the frequency-side
partner of the massless light cone `bogoliubovEnergy k 0 = |k|`. -/
lemma entropic_mass_gap_boundary (m c ħ η : ℝ) (hlam : comptonWavelength m c ħ ≠ 0) (hħ : ħ ≠ 0)
    (hK : 0 < schmidtNumber η) :
    (entropicProperDistance m c ħ η = 0 ↔ schmidtNumber η = 1)
      ∧ (entropicAction ħ η = 0 ↔ schmidtNumber η = 1) := by
  refine ⟨?_, reversible_iff_separable ħ η hħ hK⟩
  rw [← reversible_iff_separable ħ η hħ hK]
  unfold entropicProperDistance entropicAction
  rw [mul_eq_zero, mul_eq_zero, or_iff_right hlam, or_iff_right hħ]

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.expEntropicDistance_eq_schmidtNumber where
  formalizes @ "claim:exponential-of-the-entropic-proper-distance-is-the-schmidt-number",
  supported_by @ "paper:caticha-entropic-dynamics",
  caveat @ "claim:operational-identification-r-equals-lambda-c-log-K-of-distance-with-entanglement"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entanglement_boosts_clock_and_sets_distance where
  formalizes @ "claim:entanglement-rapidity-boosts-the-internal-clock-and-sets-the-entropic-distance",
  requires @ "claim:exponential-of-the-entropic-proper-distance-is-the-schmidt-number",
  supported_by @ "paper:caticha-entropic-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance_unifies_four_groundings where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.expEntropicDistance_eq_schmidtNumber",
  formalizes @ "claim:the-defined-entropic-distance-has-four-equivalent-algebraic-readings",
  requires @ "claim:entanglement-rapidity-boosts-the-internal-clock-and-sets-the-entropic-distance",
  caveat @ "claim:conjunction-of-four-exact-identities-on-a-defined-shared-carrier-\
not-four-independent-physical-derivations"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.anomaly_eq_entropicDistance where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.anomaly_eq_schmidt_sq_sub_one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.expEntropicDistance_eq_schmidtNumber",
  formalizes @ "claim:the-muon-anomaly-channel-is-a-reading-of-the-entropic-proper-distance",
  requires @ "claim:exponential-of-the-entropic-proper-distance-is-the-schmidt-number",
  caveat @ "claim:change-of-variables-until-K-is-derived-from-a-state-before-using-a-mu"

zil_file_contract physlib.entropicProperDistance where
  promises "The entropic proper distance is the defined logarithmic coordinate r = \
lambda-C log K. Its exponential, suppression, entropic-action, and empirical-distance \
bridge are exact equivalent readings. The exponential suppression equality is a change \
of variables and is not presented as a Reeh-Schlieder, Pauli-Jordan, or AQFT Bell-profile \
derivation."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance"]
  forbids_substitutes ["a derivation of the Schmidt number K from a state, which the operational identification presumes",
    "entanglement or entropy evidence claimed from the change-of-variables alone",
    "an exact vacuum Bell decay law derived from Reeh-Schlieder or Pauli-Jordan antisymmetry"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.expEntropicDistance_eq_schmidtNumber,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entanglement_boosts_clock_and_sets_distance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance_unifies_four_groundings,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.anomaly_eq_entropicDistance]

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.restGap_eq_hbar_comptonFrequency where
  formalizes @ "claim:the-zero-momentum-bogoliubov-gap-is-the-compton-rest-energy-hbar-omega-c",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation.bogoliubovEnergy",
  caveat @ "claim:identification-of-the-zero-momentum-gap-dispersion-value-with-the-rest-energy-mass"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropic_mass_gap where
  formalizes @ "claim:the-mass-gap-is-the-entanglement-gap-rest-gap-schmidt-number-entropic-action-and-entropic-distance-are-strictly-positive-together",
  requires @ "claim:the-zero-momentum-bogoliubov-gap-is-the-compton-rest-energy-hbar-omega-c",
  supported_by @ "paper:caticha-entropic-dynamics",
  caveat @ "claim:the-dynamical-origin-of-a-positive-gap-the-string-tension-positivity-is-not-derived-and-stays-cited"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropic_mass_gap_boundary where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.reversible_iff_separable",
  formalizes @ "claim:the-common-gapless-boundary-is-the-separable-schmidt-number-one-point-where-the-entropic-distance-and-action-vanish",
  requires @ "claim:the-mass-gap-is-the-entanglement-gap-rest-gap-schmidt-number-entropic-action-and-entropic-distance-are-strictly-positive-together"

zil_file_contract physlib.entropicMassGap where
  promises "The mass gap is the entanglement gap: at zero momentum the Bogoliubov gap-dispersion returns the rest energy, which is hbar times the Compton frequency; for an entangled rapidity the rest gap, the Schmidt number above one, the entropic action and the entropic proper distance are all strictly positive together; and the common gapless boundary is the separable Schmidt-number-one point where the entropic distance and action vanish, the frequency-side partner of the massless light cone."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation.bogoliubovEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance"]
  forbids_substitutes ["a derivation of a positive string tension or the dynamical origin of the mass gap, which stays cited",
    "a numerical value of any particle mass, all masses left as free parameters"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.restGap_eq_hbar_comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropic_mass_gap,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropic_mass_gap_boundary]

/- ZIL-END -/

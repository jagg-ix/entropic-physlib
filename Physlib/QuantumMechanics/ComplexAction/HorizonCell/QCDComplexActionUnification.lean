/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.FiniteBaryonDensityPhaseTransition
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions
public import Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronComplexEinsteinCPTChirality
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties
public import Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential
public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
meta import Zil

/-!
# The QCD sector is the repo's complex action: θ-phase × confinement-damping (PDG 2026 §9)

Binds the four QCD modules (`QCDBetaFunctionAsymptoticFreedom`, `QCDThetaTermStrongCP`, `QCDColorCountingRatioR`,
`ConfinementAreaLawEntropicWeight`) into the rest of the repository, so the QCD content is not a free-floating
island but the gauge face of structure the edifice already carries.

**The central link.** The repository's master path-integral weight is
`complexActionPathIntegralWeight S_R S_I ℏ = e^{(i/ℏ)S_R − (1/ℏ)S_I}` — an *imaginary phase* (from the real action
`S_R`) times a *real damping* (from the imaginary action `S_I`). The two QCD non-perturbative structures are
exactly these two parts:

* the **θ-term is the phase** `e^{iθn}` — a real topological action `S_R = θn` (`theta_is_master_phase`);
* the **confinement area law is the damping** `e^{−σA} = kuikenWeight` — an imaginary action `S_I = σA`, the
  modulus of the master weight (`confinement_is_master_modulus`);
* so the master weight **factorizes** into θ-vacuum phase times confinement damping
  (`qcd_theta_confinement_factorization`): `complexActionPathIntegralWeight (θn) (σA) 1 = thetaWeight · wilsonAreaLaw`.

The θ-term (CP phase, `S_R`) and confinement (entropic damping, `S_I`) are the real- and imaginary-action halves
of one complex action — the same `S = S_R + iS_I` split as the arc's `𝒢 = G + iΛ`.

**The other bindings.**

* **charges** — the R-ratio's quark charges are the repo's `windingCharge`: `2/3 = windingCharge 2`,
  `−1/3 = windingCharge (−1)`, so `R = 2` is built from the `SU(5)`/winding charges
  (`ratioR_uds_via_winding`);
* **color** — the color Casimir `C_A = 3` and the eight gluons `N²−1 = 8` are the octet module's `gluon_count`
  and `colourSpace_decomp` (`casimir_matches_colorOctet`);
* **CPT** — the θ-term's CP-oddness (`n → −n` conjugates the phase) is the C-odd imaginary-Einstein sector
  (`imEinstein_charge_conjugation_odd`); CPT is preserved (`cpt_diracOp_invariant`) — CP-odd but CPT-even
  (`qcd_theta_cp_is_imEinstein_odd`).

* **§A — θ-term = the imaginary-phase part** (`theta_is_master_phase`).
* **§B — confinement = the real-damping modulus** (`confinement_is_master_modulus`).
* **§C — the master weight factorizes** (`qcd_theta_confinement_factorization`).
* **§D — R-ratio charges = winding charges** (`ratioR_uds_via_winding`).
* **§E — Casimir = color octet** (`casimir_matches_colorOctet`).
* **§F — θ-term CP-odd = imaginary-Einstein C-odd** (`qcd_theta_cp_is_imEinstein_odd`).
* **§O — normalized continuum soft-wall pion mode**
  (`softWallPionWavefunction_full_normalization`).
* **§P — derived invariant transverse size**
  (`softWallPionWavefunction_meanZetaSq`): the normalized mode has the exact
  continuum moment `⟨ζ²⟩=1/κ²`.

**Honest layering.** Every statement is an exact identity binding the new QCD defs to existing repo defs
(`complexActionPathIntegralWeight`, `kuikenWeight`, `master_modulus_is_kuiken`, `windingCharge`, `upQuark_charge`,
`downQuark_charge`, `gluon_count`, `imEinstein_charge_conjugation_odd`, `cpt_diracOp_invariant`). No new physics is
asserted; this module only wires the QCD sector into the edifice. ## References

* Particle Data Group, PDG 2026 Review, §9 (θ-term, R-ratio, color factors). Repo carriers:
  `PathIntegral.ComplexActionPathIntegralWeight`, `Winding.QuarkChargeWinding`,
  `Particles.StrongInteractionColorOctet`, `HorizonCell.ElectronComplexEinsteinCPTChirality`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronComplexEinsteinCPTChirality
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.FiniteBaryonDensityPhaseTransition
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions
open Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator
open Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential
open Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification


/-- **[The θ-vacuum weight is the master complex-action phase] `e^{iθn} = complexActionPathIntegralWeight (θn) 0 1`.**
The θ-term is a *real* topological action `S_R = θn` (with no imaginary/dissipative part, `S_I = 0`), so its
θ-vacuum weight is exactly the imaginary-phase factor `e^{(i/ℏ)S_R}` of the repository's master path-integral
weight — a pure CP phase, the `𝒢 = G + iΛ` real-action half. -/
lemma theta_is_master_phase (θ : ℝ) (n : ℤ) :
    thetaWeight θ n = complexActionPathIntegralWeight (θ * n) 0 1 := by
  unfold thetaWeight complexActionPathIntegralWeight
  congr 1
  push_cast
  ring


/-- **[The confinement area law is the master-weight modulus] `e^{−σA} = ‖complexActionPathIntegralWeight S_R (σA) 1‖`.**
The confining Wilson loop is a *real damping* — the modulus `kuikenWeight` of the master path-integral weight
(`master_modulus_is_kuiken`) with **imaginary action** `S_I = σA` (string tension × area). Confinement is the
dissipative `iΛ` imaginary-action half, for any accompanying real action `S_R`. -/
lemma confinement_is_master_modulus (σ A S_R : ℝ) :
    wilsonAreaLaw σ A = ‖complexActionPathIntegralWeight S_R (σ * A) 1‖ := by
  rw [areaLaw_is_kuikenWeight, master_modulus_is_kuiken]


/-- **[The master weight factorizes: θ-phase × confinement-damping]
`complexActionPathIntegralWeight (θn) (σA) 1 = e^{iθn} · e^{−σA}`.** The one complex action `S = θn + i(σA)` splits
into the QCD θ-term (real action → CP phase `thetaWeight`) and confinement (imaginary action → entropic damping
`wilsonAreaLaw`). The two non-perturbative faces of QCD are the imaginary and real parts of a single
complex-action weight of the arc. -/
lemma qcd_theta_confinement_factorization (θ σ A : ℝ) (n : ℤ) :
    complexActionPathIntegralWeight (θ * n) (σ * A) 1
      = thetaWeight θ n * ((wilsonAreaLaw σ A : ℝ) : ℂ) := by
  unfold complexActionPathIntegralWeight thetaWeight wilsonAreaLaw
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring


/-- **[The R-ratio plateau is built from the winding charges] `R = 3·((windingCharge 2)² + 2(windingCharge −1)²) = 2`.**
The color-counting ratio's quark charges are the repository's `windingCharge`: the up-quark `2/3 = windingCharge 2`
and the down-quark `−1/3 = windingCharge (−1)` (`upQuark_charge`, `downQuark_charge`, the `SU(5)`/winding charges).
So the measured plateau `R = 2` is assembled from the same fractional charges the charge-chirality arc carries. -/
lemma ratioR_uds_via_winding :
    ratioR 3 (((windingCharge upWinding : ℚ) : ℝ) ^ 2 + ((windingCharge downWinding : ℚ) : ℝ) ^ 2
      + ((windingCharge downWinding : ℚ) : ℝ) ^ 2) = 2 := by
  rw [upQuark_charge, downQuark_charge]
  unfold ratioR
  push_cast
  norm_num


/-- **[The color Casimir is the octet's gluon count] `C_A = 3`, `N² − 1 = 8`, `3⊗3̄ = 8⊕1`.** The adjoint Casimir
`C_A = N = 3` of the β-function is the `SU(3)` `N`, and the eight gluons `N² − 1 = 8` are the octet module's
`gluon_count`, with the color decomposition `3·3 = 8 + 1` (`colourSpace_decomp`). The QCD color factors are the
existing strong-interaction color octet. -/
lemma casimir_matches_colorOctet :
    QCDBetaFunctionAsymptoticFreedom.casimirAdjoint 3 = 3 ∧ 3 ^ 2 - 1 = 8 ∧ 3 * 3 = 8 + 1 :=
  ⟨rfl, gluon_count, colourSpace_decomp⟩


/-- **[The θ-term is CP-odd like the imaginary-Einstein sector].** The θ-vacuum phase is CP-odd — the topological
flip `n → −n` conjugates it (`thetaWeight_cp`) — exactly as the arc's **imaginary** Einstein sector is C-odd:
`Im 𝒢` flips sign under charge conjugation `m_I → −m_I` (`imEinstein_charge_conjugation_odd`). Both are the C-odd,
imaginary (entropic/`Λ`) half of the complex action, while the real half is C-even. CPT is preserved
(`cpt_diracOp_invariant`): the θ-term is CP-violating but CPT-even, the strong-CP structure on the arc's CPT
frame. -/
lemma qcd_theta_cp_is_imEinstein_odd (θ : ℝ) (n : ℤ) (m_R m_I c : ℝ) :
    thetaWeight θ (-n) = (starRingEnd ℂ) (thetaWeight θ n)
      ∧ (complexEinsteinEnergy m_R (-m_I) c).im = -(complexEinsteinEnergy m_R m_I c).im :=
  ⟨thetaWeight_cp θ n, imEinstein_charge_conjugation_odd m_R m_I c⟩

/-! ## G. AdS radial scale and the QCD renormalization group -/

/-- The one-loop QCD coupling read at the holographic radial coordinate `z`, with
renormalization-group time `t = -log z`. -/
noncomputable def adsRadialRunningCoupling (b0 α0 z : ℝ) : ℝ :=
  QCDBetaFunctionAsymptoticFreedom.runningCoupling b0 α0 (-Real.log z)

/-- Along the standard Poincaré-AdS parametrization `z = exp(-t)`, the holographic
radial coupling is exactly the existing one-loop QCD running coupling at RG time `t`. -/
lemma adsRadialRunningCoupling_exp_neg (b0 α0 t : ℝ) :
    adsRadialRunningCoupling b0 α0 (Real.exp (-t)) =
      QCDBetaFunctionAsymptoticFreedom.runningCoupling b0 α0 t := by
  unfold adsRadialRunningCoupling
  rw [Real.log_exp]
  congr 2
  ring

/-- **Holographic UV/asymptotic-freedom bridge.** As RG time tends to infinity,
the Poincaré radial coordinate approaches the AdS boundary `z = 0`, while the
one-loop QCD coupling evaluated at that radial scale approaches zero. -/
@[zil_level bridge_theorem]
lemma adsBoundary_qcdRunningCoupling_tendsto_zero
    (b0 α0 : ℝ) (hb : 0 < b0) (hα : 0 < α0) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-t)) Filter.atTop (nhds 0)
      ∧ Filter.Tendsto
        (fun t : ℝ => adsRadialRunningCoupling b0 α0 (Real.exp (-t)))
        Filter.atTop (nhds 0) := by
  constructor
  · exact Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
  · simpa only [adsRadialRunningCoupling_exp_neg] using
      QCDBetaFunctionAsymptoticFreedom.runningCoupling_tendsto_zero b0 α0 hb hα

/-! ## H. Finite-density holography as a complex-action damping law -/

/-- The master complex-action weight whose damping slot is the renormalized
D3/D7 finite-density on-shell action. -/
noncomputable def finiteDensityHolographicWeight
    (γN t μ m S_R : ℝ) : ℂ :=
  complexActionPathIntegralWeight S_R (sRen γN t μ m) 1

/-- The grand-potential derivative is minus the holographic baryon density at
every chemical potential, not only at the transition point. -/
lemma grandPotential_hasDerivAt_eq_neg_density (γN t m μ : ℝ) :
    HasDerivAt (fun x => grandPotential γN t x m)
      (-density γN t μ m) μ := by
  unfold grandPotential
  apply (sRen_hasDerivAt γN t m μ).neg.congr_of_eventuallyEq
  filter_upwards [] with x
  rfl

/-- For nonnegative D3/D7 normalization, the finite-density Euclidean on-shell
action produces a genuine complex-action damping factor of modulus at most one. -/
lemma finiteDensityHolographicWeight_norm_le_one
    (γN t μ m S_R : ℝ) (hγN : 0 ≤ γN) :
    ‖finiteDensityHolographicWeight γN t μ m S_R‖ ≤ 1 := by
  unfold finiteDensityHolographicWeight
  rw [master_modulus_is_kuiken]
  exact
    ElectronExclusionEntropyProduction.kuikenWeight_le_one
      1 (sRen γN t μ m) one_pos (sRen_nonneg γN t μ m hγN)

/-- At the second-order threshold `μ = m`, the on-shell action vanishes and the
finite-density complex-action damping restores unit modulus. -/
lemma finiteDensityHolographicWeight_transition
    (γN t m S_R : ℝ) :
    ‖finiteDensityHolographicWeight γN t m m S_R‖ = 1 := by
  unfold finiteDensityHolographicWeight
  rw [master_modulus_is_kuiken, sRen_transition]
  simp [kuikenWeight]

/-- **Finite-density holographic complex-action package.** The exact D3/D7 grand
potential differentiates to minus the baryon density, its Euclidean action gives
a bounded damping modulus, and the continuous threshold `μ = m` restores unit
modulus. -/
@[zil_level bridge_theorem]
lemma finiteDensity_holographic_complexAction_chain
    (γN t m μ S_R : ℝ) (hγN : 0 ≤ γN) :
    HasDerivAt (fun x => grandPotential γN t x m)
        (-density γN t μ m) μ
      ∧ ‖finiteDensityHolographicWeight γN t μ m S_R‖ ≤ 1
      ∧ ‖finiteDensityHolographicWeight γN t m m S_R‖ = 1 :=
  ⟨grandPotential_hasDerivAt_eq_neg_density γN t m μ,
    finiteDensityHolographicWeight_norm_le_one γN t μ m S_R hγN,
    finiteDensityHolographicWeight_transition γN t m S_R⟩

/-! ## I. A controlled conformal-AdS/QCD crossover -/

/-- The positive radius where the magnitude of Maldacena's conformal Coulomb
coefficient balances a QCD string tension. This is a phenomenological UV/IR
matching scale, not an identification of conformal `N = 4` SYM with QCD. -/
noncomputable def adsQcdCrossoverRadius (lam sigma : ℝ) : ℝ :=
  crossoverRadius 1 (maldacenaWilsonCoefficient lam) sigma

/-- The AdS/QCD crossover radius is positive for positive 't Hooft coupling and
positive QCD string tension. -/
lemma adsQcdCrossoverRadius_pos (lam sigma : ℝ)
    (hlam : 0 < lam) (hsigma : 0 < sigma) :
    0 < adsQcdCrossoverRadius lam sigma := by
  exact crossoverRadius_pos 1 (maldacenaWilsonCoefficient lam) sigma
    one_pos (maldacenaWilsonCoefficient_pos lam hlam) hsigma

/-- **AdS/QCD UV–IR balance at the constructed scale.** At the positive matching
radius, the magnitude of Maldacena's conformal `1/L` potential equals the QCD
linear confining potential. -/
@[zil_level bridge_theorem]
lemma maldacena_qcd_balance_at_crossover
    (lam sigma : ℝ) (hlam : 0 < lam) (hsigma : 0 < sigma) :
    -maldacenaQuarkPotential lam (adsQcdCrossoverRadius lam sigma) =
      linearConfiningPotential sigma (adsQcdCrossoverRadius lam sigma) := by
  have hbalance :=
    cornell_terms_balance_at_crossover 1 (maldacenaWilsonCoefficient lam) sigma
      one_pos (maldacenaWilsonCoefficient_pos lam hlam) hsigma
  simpa only [adsQcdCrossoverRadius, maldacenaQuarkPotential,
    linearConfiningPotential, one_mul, neg_div, neg_neg] using hbalance

/-! ## J. Finite-density stability above the holographic threshold -/

/-- **Positive holographic baryon susceptibility.** Above the D3/D7 threshold
`μ ≥ m > 0`, with positive normalization and nonzero string scale, the derivative
of baryon density is strictly positive. -/
@[zil_level bridge_theorem]
lemma finiteDensity_baryonSusceptibility_pos
    (γN t m μ : ℝ) (hγN : 0 < γN) (ht : t ≠ 0)
    (hm : 0 < m) (hμ : m ≤ μ) :
    0 < γN * t ^ 4 * (3 * μ ^ 2 - m ^ 2)
      ∧ HasDerivAt (fun x => density γN t x m)
        (γN * t ^ 4 * (3 * μ ^ 2 - m ^ 2)) μ := by
  have hsq : m * m ≤ μ * μ := mul_self_le_mul_self hm.le hμ
  have hfactor : 0 < 3 * μ ^ 2 - m ^ 2 := by
    nlinarith [hsq, sq_pos_of_pos hm]
  exact ⟨by positivity, density_hasDerivAt γN t m μ⟩

/-! ## K. Dimensional transmutation supplies the trace-anomaly mass scale -/

/-- **QCD scale to trace-anomaly mass chain.** Under the standard dimensional
identification of the positive gluon-condensate scale with `Λ_QCD⁴`, dimensional
transmutation supplies a positive scale, the one-loop trace anomaly is negative,
and its hadron mass-squared is positive. -/
@[zil_level bridge_theorem]
lemma qcdScale_traceAnomaly_hadronMass_chain
    (μ0 α0 N_f gSq : ℝ) (hμ0 : 0 < μ0) (hα0 : 0 < α0)
    (hNf : N_f < 33 / 2) (hgSq : 0 < gSq) :
    1 + betaZeroCoeff N_f * α0 *
        landauPoleTime (betaZeroCoeff N_f) α0 = 0
      ∧ α0⁻¹ + betaZeroCoeff N_f *
        landauPoleTime (betaZeroCoeff N_f) α0 = 0
      ∧ 0 < qcdScale μ0 (betaZeroCoeff N_f) α0
      ∧ traceAnomaly (betaZeroCoeff N_f) gSq
          ((qcdScale μ0 (betaZeroCoeff N_f) α0) ^ 4) < 0
      ∧ 0 < hadronMassSq
          (traceAnomaly (betaZeroCoeff N_f) gSq
            ((qcdScale μ0 (betaZeroCoeff N_f) α0) ^ 4)) := by
  have hb : 0 < betaZeroCoeff N_f := (asymptotic_freedom_iff N_f).mpr hNf
  have htrans := dimensional_transmutation μ0 (betaZeroCoeff N_f) α0
    hμ0 hb.ne' hα0.ne'
  have hscale : 0 < qcdScale μ0 (betaZeroCoeff N_f) α0 :=
    htrans.2.2
  have htrace : traceAnomaly (betaZeroCoeff N_f) gSq
      ((qcdScale μ0 (betaZeroCoeff N_f) α0) ^ 4) < 0 :=
    trace_anomaly_from_asymptotic_freedom N_f gSq
      ((qcdScale μ0 (betaZeroCoeff N_f) α0) ^ 4) hNf hgSq (by positivity)
  exact ⟨htrans.1, htrans.2.1, hscale, htrace, hadronMassSq_pos _ htrace⟩

/-! ## L. Thermal RG and Polyakov deconfinement are distinct monotonicities -/

/-- The finite-temperature Polyakov magnitude is exactly the master complex-action
modulus with the single-quark free energy in the damping slot. -/
lemma polyakovMagnitude_is_master_modulus (T F_q S_R : ℝ) :
    polyakovMagnitude T F_q =
      ‖complexActionPathIntegralWeight S_R F_q T‖ := by
  unfold polyakovMagnitude
  rw [master_modulus_is_kuiken]

/-- **Thermal-flow/deconfinement separation.** At fixed positive momentum,
raising temperature makes the displayed high-temperature beta function more
negative while increasing the Polyakov-loop magnitude. These are simultaneous
but logically distinct statements: the beta-function sign alone neither proves
nor refutes center-symmetry breaking. -/
@[zil_level bridge_theorem]
lemma thermalBeta_polyakov_heating_directions
    (N_c αs κ F_q T1 T2 S_R : ℝ)
    (hNc : 0 ≤ N_c) (hκ : 0 < κ) (hF : 0 ≤ F_q)
    (hT1 : 0 < T1) (hT : T1 ≤ T2) :
    betaHighTemp N_c αs T2 κ ≤ betaHighTemp N_c αs T1 κ
      ∧ polyakovMagnitude T1 F_q ≤ polyakovMagnitude T2 F_q
      ∧ polyakovMagnitude T2 F_q =
        ‖complexActionPathIntegralWeight S_R F_q T2‖ :=
  ⟨betaHighTemp_antitone_temp N_c αs κ hNc hκ hT,
    polyakov_grows_with_temperature F_q hF hT1 hT,
    polyakovMagnitude_is_master_modulus T2 F_q S_R⟩

/-! ## M. Light-front holography and the soft-wall AdS/QCD spectrum

This section formalizes the algebraic field-equation core of de Téramond and
Brodsky, arXiv:1206.4365v2.  It keeps the light-front potential, the AdS mass
parameter and the mass-squared spectrum separate from the repository's
Einstein--Maxwell, Einstein--Cartan and BCJ/Bianchi sectors.  The paper supplies
an AdS/QCD eigenvalue problem and electromagnetic/gravitational form-factor
dictionary; it does not derive those independent gravitational field equations.
-/

/-- The effective light-front potential obtained from a dilaton profile,

`U(ζ,J) = φ''/2 + (φ')²/4 + (2J-3)φ'/(2ζ)`.

The arguments `dφ` and `ddφ` expose the pointwise first and second derivatives
without introducing a duplicate differentiation API. -/
noncomputable def lightFrontDilatonPotential
    (dφ ddφ ζ J : ℝ) : ℝ :=
  ddφ / 2 + dφ ^ 2 / 4 + (2 * J - 3) * dφ / (2 * ζ)

/-- The positive-quadratic-dilaton (soft-wall) light-front potential. -/
noncomputable def lightFrontSoftWallPotential (κ ζ J : ℝ) : ℝ :=
  κ ^ 4 * ζ ^ 2 + 2 * κ ^ 2 * (J - 1)

/-- **[de Téramond--Brodsky Eq. (8), quadratic dilaton].**  Substituting the
pointwise derivatives `φ'(ζ)=2κ²ζ` and `φ''(ζ)=2κ²` into the general holographic
potential gives exactly

`U(ζ,J)=κ⁴ζ²+2κ²(J-1)`.

The nonzero-radial-coordinate premise is explicit because the general formula
contains `1/ζ`; the simplified soft-wall expression extends continuously to
`ζ=0`, but that endpoint extension is not asserted here. -/
@[zil_level bridge_theorem]
theorem lightFrontDilatonPotential_quadratic
    (κ ζ J : ℝ) (hζ : ζ ≠ 0) :
    lightFrontDilatonPotential (2 * κ ^ 2 * ζ) (2 * κ ^ 2) ζ J =
      lightFrontSoftWallPotential κ ζ J := by
  unfold lightFrontDilatonPotential lightFrontSoftWallPotential
  field_simp [hζ]
  ring

/-- The dimensionless AdS spin-`J` bulk mass parameter
`(μR)² = -(2-J)² + ℓ`, where `ℓ=L²` is the orbital Casimir. -/
noncomputable def lightFrontAdSMassParameter (J orbitalCasimir : ℝ) : ℝ :=
  -(2 - J) ^ 2 + orbitalCasimir

/-- **[de Téramond--Brodsky scalar stability].** For `J=0`, the AdS₅
Breitenlohner--Freedman condition is equivalent to nonnegativity of the
light-front orbital Casimir:

`m²R² = -4 + ℓ ≥ -4  ↔  0 ≤ ℓ`.

This reuses the repository's standard GKP--Witten BF theorem rather than
redefining AdS stability. -/
@[zil_level bridge_theorem]
theorem lightFront_scalar_bf_iff_orbitalCasimir_nonneg
    (orbitalCasimir : ℝ) :
    (-(4 / 2 : ℝ) ^ 2 ≤ lightFrontAdSMassParameter 0 orbitalCasimir) ↔
      0 ≤ orbitalCasimir := by
  rw [← breitenlohnerFreedman]
  unfold lightFrontAdSMassParameter
  norm_num

/-- The soft-wall light-front mass-squared tower
`M²(n,J,L)=4κ²(n+(J+L)/2)`. -/
noncomputable def lightFrontMassSpectrumSq
    (κ n J L : ℝ) : ℝ :=
  4 * κ ^ 2 * (n + (J + L) / 2)

/-- **[de Téramond--Brodsky Eq. (9), Regge spacings].** The soft-wall spectrum
has the same exact mass-squared increment `4κ²` under one radial excitation,
two units of spin, or two units of orbital angular momentum.  These are
algebraic consequences of the supplied light-front eigenvalue formula, not a
construction of the continuum eigenfunctions or a fit of `κ` to hadron data. -/
@[zil_level bridge_theorem]
theorem lightFrontMassSpectrumSq_reggeSpacings
    (κ n J L : ℝ) :
    lightFrontMassSpectrumSq κ (n + 1) J L -
        lightFrontMassSpectrumSq κ n J L = 4 * κ ^ 2
      ∧ lightFrontMassSpectrumSq κ n (J + 2) L -
        lightFrontMassSpectrumSq κ n J L = 4 * κ ^ 2
      ∧ lightFrontMassSpectrumSq κ n J (L + 2) -
        lightFrontMassSpectrumSq κ n J L = 4 * κ ^ 2 := by
  unfold lightFrontMassSpectrumSq
  constructor
  · ring
  · constructor <;> ring

/-- The complete pointwise soft-wall radial potential in the light-front
Schrödinger operator: centrifugal term plus dilaton potential. -/
noncomputable def lightFrontSoftWallRadialPotential
    (κ ζ J L : ℝ) : ℝ :=
  (4 * L ^ 2 - 1) / (4 * ζ ^ 2) +
    lightFrontSoftWallPotential κ ζ J

/-- **[The soft-wall light-front operator is isotonic].**  Its pointwise radial
potential is exactly

`κ⁴ζ² + (L²-1/4)/ζ² + 2κ²(J-1)`.

Thus the dynamical part is the repository's existing rational isotonic
potential, plus the spin-dependent constant shift. -/
@[zil_level bridge_theorem]
theorem lightFrontSoftWallRadialPotential_eq_isotonic
    (κ ζ J L : ℝ) (hζ : ζ ≠ 0) :
    lightFrontSoftWallRadialPotential κ ζ J L =
      isotonicRational (κ ^ 4) (L ^ 2 - 1 / 4) ζ +
        2 * κ ^ 2 * (J - 1) := by
  unfold lightFrontSoftWallRadialPotential lightFrontSoftWallPotential
    isotonicRational
  field_simp [hζ]
  ring

/-- **[Coercive lower bound away from the critical orbital channel].**  For a
nonzero soft-wall scale and `L²>1/4`, the radial potential is bounded below by

`2√(κ⁴(L²-1/4)) + 2κ²(J-1)`.

This directly reuses the existing isotonic AM--GM estimate.  The critical
`L=0` BF-stable channel is deliberately not covered by this stronger pointwise
coercivity statement. -/
@[zil_level bridge_theorem]
theorem lightFrontSoftWallRadialPotential_ge
    (κ ζ J L : ℝ) (hκ : κ ≠ 0) (hL : 1 / 4 < L ^ 2)
    (hζ : ζ ≠ 0) :
    2 * Real.sqrt (κ ^ 4 * (L ^ 2 - 1 / 4)) +
        2 * κ ^ 2 * (J - 1) ≤
      lightFrontSoftWallRadialPotential κ ζ J L := by
  rw [lightFrontSoftWallRadialPotential_eq_isotonic κ ζ J L hζ]
  have h :=
    isotonicRational_ge (κ ^ 4) (L ^ 2 - 1 / 4) ζ
      (by positivity) (by linarith) hζ
  linarith

/-- **[Light-front orbital momentum fixes the boundary dimension].**  For the
spin-zero AdS mass relation `m²R²=-4+L²`, the standard GKP--Witten dictionary
gives

`Δ₊ = 2 + |L|`.

For the physical branch `L≥0`, this is the familiar twist/orbital relation
`Δ=2+L`. -/
@[zil_level bridge_theorem]
theorem lightFront_scalar_conformalDimension (L : ℝ) :
    conformalDimension 4 (lightFrontAdSMassParameter 0 (L ^ 2)) =
      2 + |L| := by
  unfold conformalDimension lightFrontAdSMassParameter
  rw [show (4 / 2 : ℝ) ^ 2 + (-(2 - 0) ^ 2 + L ^ 2) = L ^ 2 by ring,
    Real.sqrt_sq_eq_abs]
  norm_num

/-- **[A genuine continuum radial mode].**  The light-front scalar mass
parameter `m²R²=-4+L²` makes the power profile `z^(2+|L|)` solve the differentiated
AdS₅ near-boundary radial equation

`z³ ∂z(z⁻³ ∂z z^(2+|L|)) = (-4+L²) z^|L|`.

This is the existing continuum GKP radial theorem specialized through the
light-front mass/orbital dictionary, not merely a declared eigenvalue
predicate. -/
@[zil_level bridge_theorem]
theorem lightFront_scalar_nearBoundary_radial
    (L z : ℝ) (hz : 0 < z) :
    z ^ (3 : ℝ) *
        deriv (fun w => w ^ (-3 : ℝ) *
          deriv (fun u => u ^ (2 + |L|)) w) z =
      lightFrontAdSMassParameter 0 (L ^ 2) *
        z ^ ((2 + |L|) - 2) := by
  have hBF :
      0 ≤ (4 / 2 : ℝ) ^ 2 +
        lightFrontAdSMassParameter 0 (L ^ 2) := by
    unfold lightFrontAdSMassParameter
    nlinarith [sq_nonneg L]
  have hradial :=
    conformalDimension_solves_radial
      (lightFrontAdSMassParameter 0 (L ^ 2)) z hBF hz
  rw [lightFront_scalar_conformalDimension L] at hradial
  exact hradial

/-! ## N. Electromagnetic and gravitational light-front form-factor dictionary -/

/-- The AdS/light-front spectator density
`R³/(2π) · x/(1-x) · |Φ(ζ)|²/ζ⁴`.

The argument `phiNormSq` is the pointwise squared norm of the normalizable AdS
mode. Keeping it explicit lets the definition work for real- or complex-valued
modes without duplicating a norm API. -/
noncomputable def lightFrontHolographicDensity
    (R x ζ phiNormSq : ℝ) : ℝ :=
  R ^ 3 / (2 * Real.pi) * (x / (1 - x)) * (phiNormSq / ζ ^ 4)

/-- The two-parton light-front wavefunction density obtained from the same AdS
mode: `R³/(2π) · x(1-x) · |Φ(ζ)|²/ζ⁴`. -/
noncomputable def twoPartonLightFrontWavefunctionNormSq
    (R x ζ phiNormSq : ℝ) : ℝ :=
  R ^ 3 / (2 * Real.pi) * (x * (1 - x)) * (phiNormSq / ζ ^ 4)

/-- **[The electromagnetic and gravitational mappings coincide].** The common
spectator density reconstructed independently from the AdS electromagnetic
current and energy-momentum-tensor form factors gives the two-parton
wavefunction density after multiplication by `(1-x)²`.

The premise `x ≠ 1` records the endpoint excluded by the spectator-density
formula. No equality of the electromagnetic and gravitational probes away from
zero momentum is asserted. -/
@[zil_level bridge_theorem]
theorem electromagnetic_gravitational_density_map_agree
    (R x ζ phiNormSq : ℝ) (hx : x ≠ 1) :
    (1 - x) ^ 2 * lightFrontHolographicDensity R x ζ phiNormSq =
      twoPartonLightFrontWavefunctionNormSq R x ζ phiNormSq := by
  unfold lightFrontHolographicDensity twoPartonLightFrontWavefunctionNormSq
  field_simp [sub_ne_zero.mpr hx]

/-- The continuum AdS overlap of a normalizable hadron mode `Φ` with a
bulk-to-boundary probe `P(Q²,z)`. This is the common integral carrier for both
electromagnetic and gravitational form factors. -/
noncomputable def adsProbeFormFactor
    (R : ℝ) (Φ : ℝ → ℝ) (probe : ℝ → ℝ → ℝ) (Qsq : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ),
    R ^ 3 / z ^ 3 * Φ z * probe Qsq z * Φ z

/-- The continuum normalization integral of an AdS hadron mode. -/
noncomputable def adsHadronNormalization
    (R : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), R ^ 3 / z ^ 3 * Φ z ^ 2

/-- **[Charge and momentum sum rules share one continuum normalization].** If
a bulk-to-boundary probe is pointwise one at zero momentum transfer, its AdS
form factor at `Q²=0` is exactly the hadron normalization integral. This covers
both the electromagnetic boundary condition `J(0,z)=1` and the gravitational
condition `H(0,z)=1`. -/
@[zil_level bridge_theorem]
theorem adsProbeFormFactor_zero_eq_normalization
    (R : ℝ) (Φ : ℝ → ℝ) (probe : ℝ → ℝ → ℝ)
    (hprobe : ∀ z, 0 < z → probe 0 z = 1) :
    adsProbeFormFactor R Φ probe 0 = adsHadronNormalization R Φ := by
  unfold adsProbeFormFactor adsHadronNormalization
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  rw [hprobe z hz]
  ring

/-- The twist-two soft-wall pion form factor
`Fπ(Q²) = 1/(1 + Q²/(4κ²))`. -/
noncomputable def softWallPionFormFactor (κ Qsq : ℝ) : ℝ :=
  (1 + Qsq / (4 * κ ^ 2))⁻¹

/-- The soft-wall pion form factor satisfies charge normalization
`Fπ(0)=1`. -/
lemma softWallPionFormFactor_zero (κ : ℝ) :
    softWallPionFormFactor κ 0 = 1 := by
  simp [softWallPionFormFactor]

/-- The exact zero-momentum slope of the twist-two soft-wall pion form factor. -/
lemma softWallPionFormFactor_hasDerivAt_zero
    (κ : ℝ) (hκ : κ ≠ 0) :
    HasDerivAt (softWallPionFormFactor κ) (-1 / (4 * κ ^ 2)) 0 := by
  have hdenom : HasDerivAt (fun Qsq : ℝ => 1 + Qsq / (4 * κ ^ 2))
      (1 / (4 * κ ^ 2)) 0 :=
    (hasDerivAt_id 0).div_const (4 * κ ^ 2) |>.const_add 1
  have hinv := hdenom.inv (by norm_num)
  have hslope : -(1 / (4 * κ ^ 2)) / (1 + 0 / (4 * κ ^ 2)) ^ 2 =
      -1 / (4 * κ ^ 2) := by
    norm_num
    field_simp [hκ]
  rw [hslope] at hinv
  exact hinv

/-- **[Soft-wall pion charge radius].** Through the repository's standard
form-factor-slope definition `⟨r²⟩=-6F'(0)`, the twist-two monopole gives
`⟨rπ²⟩=3/(2κ²)`. The scale `κ` remains a model parameter; this identity does
not fit its value to experimental pion-radius data. -/
@[zil_level bridge_theorem]
theorem softWallPion_chargeRadiusSq
    (κ : ℝ) (hκ : κ ≠ 0) :
    chargeRadiusSqFromSlope (-1 / (4 * κ ^ 2)) = 3 / (2 * κ ^ 2) := by
  unfold chargeRadiusSqFromSlope
  field_simp [hκ]
  ring

/-- **[Soft-wall pion form-factor chain].** For nonzero soft-wall scale, the
twist-two form factor is charge-normalized, has slope `-1/(4κ²)` at the origin,
and therefore has squared charge radius `3/(2κ²)` under the repository's
standard slope convention. -/
@[zil_level bridge_theorem]
theorem softWallPion_formFactor_normalization_slope_radius
    (κ : ℝ) (hκ : κ ≠ 0) :
    softWallPionFormFactor κ 0 = 1
      ∧ HasDerivAt (softWallPionFormFactor κ) (-1 / (4 * κ ^ 2)) 0
      ∧ chargeRadiusSqFromSlope (-1 / (4 * κ ^ 2)) =
        3 / (2 * κ ^ 2) :=
  ⟨softWallPionFormFactor_zero κ,
    softWallPionFormFactor_hasDerivAt_zero κ hκ,
    softWallPion_chargeRadiusSq κ hκ⟩

/-! ## O. Normalized soft-wall pion light-front wavefunction -/

/-- The lowest soft-wall pion light-front wavefunction in the invariant
transverse coordinate `ζ`:

`ψκ(x,ζ) = κ/√π · √(x(1-x)) · exp(-κ²ζ²/2)`.

This is the `n=L=0` two-parton mode. -/
noncomputable def softWallPionWavefunctionZeta
    (κ x ζ : ℝ) : ℝ :=
  κ / Real.sqrt Real.pi * Real.sqrt (x * (1 - x)) *
    Real.exp (-(κ ^ 2 * ζ ^ 2) / 2)

/-- The same soft-wall pion mode in transverse impact separation `b`, after
the holographic substitution `ζ²=x(1-x)b²`. -/
noncomputable def softWallPionImpactWavefunction
    (κ x b : ℝ) : ℝ :=
  κ / Real.sqrt Real.pi * Real.sqrt (x * (1 - x)) *
    Real.exp (-(κ ^ 2 * x * (1 - x) * b ^ 2) / 2)

/-- The pointwise probability density of the soft-wall pion impact mode. -/
noncomputable def softWallPionImpactDensity
    (κ x b : ℝ) : ℝ :=
  κ ^ 2 / Real.pi * (x * (1 - x)) *
    Real.exp (-(κ ^ 2 * (x * (1 - x))) * b ^ 2)

/-- The impact-space expression is exactly the invariant-`ζ` wavefunction at
`ζ=√(x(1-x))b`. -/
lemma softWallPionImpactWavefunction_eq_zeta
    (κ x b : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    softWallPionImpactWavefunction κ x b =
      softWallPionWavefunctionZeta κ x
        (Real.sqrt (x * (1 - x)) * b) := by
  have hxx : 0 ≤ x * (1 - x) :=
    mul_nonneg hx0 (sub_nonneg.mpr hx1)
  unfold softWallPionImpactWavefunction softWallPionWavefunctionZeta
  rw [mul_pow, Real.sq_sqrt hxx]
  congr 2
  ring

/-- Squaring the explicit pion wavefunction gives its Gaussian impact-space
probability density. -/
lemma softWallPionImpactWavefunction_sq
    (κ x b : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    softWallPionImpactWavefunction κ x b ^ 2 =
      softWallPionImpactDensity κ x b := by
  have hxx : 0 ≤ x * (1 - x) :=
    mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have hexp :
      Real.exp (-(κ ^ 2 * x * (1 - x) * b ^ 2) / 2) ^ 2 =
        Real.exp (-(κ ^ 2 * (x * (1 - x))) * b ^ 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  unfold softWallPionImpactWavefunction softWallPionImpactDensity
  rw [mul_pow, mul_pow, hexp, div_pow, Real.sq_sqrt Real.pi_pos.le,
    Real.sq_sqrt hxx]

/-- At each interior longitudinal momentum fraction, the pion probability
density integrates to one over the transverse plane in polar measure
`2πb db`. -/
lemma softWallPionImpactDensity_radial_normalized
    (κ x : ℝ) (hκ : κ ≠ 0) (hx0 : 0 < x) (hx1 : x < 1) :
    (∫ b in Set.Ioi (0 : ℝ),
      2 * Real.pi * b * softWallPionImpactDensity κ x b) = 1 := by
  have hxx : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
  have hA : 0 < κ ^ 2 * (x * (1 - x)) :=
    mul_pos (sq_pos_of_ne_zero hκ) hxx
  have hcore :
      (∫ b in Set.Ioi (0 : ℝ),
        b * Real.exp (-(κ ^ 2 * (x * (1 - x))) * b ^ 2)) =
        1 / (2 * (κ ^ 2 * (x * (1 - x)))) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := (1 : ℝ))
      (b := κ ^ 2 * (x * (1 - x))) (by norm_num) (by norm_num) hA
    norm_num [Real.rpow_one, Real.Gamma_one] at h ⊢
    rw [h, Real.rpow_neg_one]
    field_simp [hκ, ne_of_gt hx0, ne_of_gt (sub_pos.mpr hx1)]
  rw [show
      (fun b : ℝ =>
        2 * Real.pi * b * softWallPionImpactDensity κ x b) =
      fun b => (2 * Real.pi * (κ ^ 2 / Real.pi * (x * (1 - x)))) *
        (b * Real.exp (-(κ ^ 2 * (x * (1 - x))) * b ^ 2)) by
    funext b
    unfold softWallPionImpactDensity
    ring]
  rw [MeasureTheory.integral_const_mul, hcore]
  field_simp [Real.pi_ne_zero, hκ, ne_of_gt hx0,
    ne_of_gt (sub_pos.mpr hx1)]

/-- **[Normalized soft-wall pion wavefunction].** The exact `n=L=0`
light-front pion mode has the stated Gaussian `ζ` profile, its squared impact
amplitude is the probability density, and the latter integrates to one over
the full longitudinal/transverse carrier
`x∈(0,1)`, `b∈(0,∞)`, with polar measure `2πb db`. -/
@[zil_level bridge_theorem]
theorem softWallPionWavefunction_full_normalization
    (κ : ℝ) (hκ : κ ≠ 0) :
    (∀ x b, 0 ≤ x → x ≤ 1 →
      softWallPionImpactWavefunction κ x b =
        softWallPionWavefunctionZeta κ x
          (Real.sqrt (x * (1 - x)) * b)
      ∧ softWallPionImpactWavefunction κ x b ^ 2 =
        softWallPionImpactDensity κ x b)
      ∧ (∫ x in Set.Ioo (0 : ℝ) 1,
        ∫ b in Set.Ioi (0 : ℝ),
          2 * Real.pi * b * softWallPionImpactDensity κ x b) = 1 := by
  constructor
  · intro x b hx0 hx1
    exact ⟨softWallPionImpactWavefunction_eq_zeta κ x b hx0 hx1,
      softWallPionImpactWavefunction_sq κ x b hx0 hx1⟩
  · calc
      _ = ∫ x in Set.Ioo (0 : ℝ) 1, (1 : ℝ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
        exact softWallPionImpactDensity_radial_normalized κ x hκ hx.1 hx.2
      _ = 1 := by simp

/-! ## P. Invariant transverse-size observable -/

/-- At each interior longitudinal momentum fraction, the normalized pion
density has invariant transverse second moment

`∫ d²b ζ² |ψκ(x,b)|² = 1/κ²`,

where `ζ²=x(1-x)b²` and `d²b=2πb db`. -/
lemma softWallPionImpactDensity_zetaSq_radial_moment
    (κ x : ℝ) (hκ : κ ≠ 0) (hx0 : 0 < x) (hx1 : x < 1) :
    (∫ b in Set.Ioi (0 : ℝ),
      (x * (1 - x) * b ^ 2) *
        (2 * Real.pi * b * softWallPionImpactDensity κ x b)) =
      1 / κ ^ 2 := by
  have hxx : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
  have hA : 0 < κ ^ 2 * (x * (1 - x)) :=
    mul_pos (sq_pos_of_ne_zero hκ) hxx
  have hcore :
      (∫ b in Set.Ioi (0 : ℝ),
        b ^ 3 * Real.exp (-(κ ^ 2 * (x * (1 - x))) * b ^ 2)) =
        1 / (2 * (κ ^ 2 * (x * (1 - x))) ^ 2) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := (3 : ℝ))
      (b := κ ^ 2 * (x * (1 - x))) (by norm_num) (by norm_num) hA
    norm_num [Real.Gamma_two, Real.rpow_neg_natCast] at h ⊢
    simpa [zpow_ofNat] using h
  rw [show
      (fun b : ℝ =>
        (x * (1 - x) * b ^ 2) *
          (2 * Real.pi * b * softWallPionImpactDensity κ x b)) =
      fun b => (2 * Real.pi * (κ ^ 2 / Real.pi * (x * (1 - x)) ^ 2)) *
        (b ^ 3 * Real.exp (-(κ ^ 2 * (x * (1 - x))) * b ^ 2)) by
    funext b
    unfold softWallPionImpactDensity
    ring]
  rw [MeasureTheory.integral_const_mul, hcore]
  field_simp [Real.pi_ne_zero, hκ, ne_of_gt hx0,
    ne_of_gt (sub_pos.mpr hx1)]

/-- **[Derived soft-wall invariant transverse size].** The fully normalized
lowest pion mode has the continuum expectation

`⟨ζ²⟩ = ∫₀¹ dx ∫₀∞ 2πb db · ζ² |ψκ(x,b)|² = 1/κ²`.

Thus `κ⁻¹` is not only a width appearing in the ansatz: its square is the
derived invariant transverse second moment of that normalized state.  This
remains a model-specific soft-wall observable and does not fit `κ` to data. -/
@[zil_level bridge_theorem]
theorem softWallPionWavefunction_meanZetaSq
    (κ : ℝ) (hκ : κ ≠ 0) :
    (∫ x in Set.Ioo (0 : ℝ) 1,
      ∫ b in Set.Ioi (0 : ℝ),
        (x * (1 - x) * b ^ 2) *
          (2 * Real.pi * b * softWallPionImpactDensity κ x b)) =
      1 / κ ^ 2 := by
  calc
    _ = ∫ _x in Set.Ioo (0 : ℝ) 1, (1 / κ ^ 2 : ℝ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact softWallPionImpactDensity_zetaSq_radial_moment
        κ x hκ hx.1 hx.2
    _ = 1 / κ ^ 2 := by simp

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification

end

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.adsBoundary_qcdRunningCoupling_tendsto_zero where
  formalizes @ "claim:the-poincare-ads-boundary-limit-z-equals-exp-minus-t-to-zero-is-the-qcd-ultraviolet-limit-in-which-the-one-loop-running-coupling-tends-to-zero",
  requires @ "claim:positive-one-loop-beta-coefficient-and-positive-reference-coupling",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.runningCoupling_tendsto_zero",
  supported_by @ "paper:gubser-klebanov-polyakov-1998-witten-1998-ads-cft-correlators",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:uses-the-standard-holographic-scale-identification-t-equals-minus-log-z-and-the-one-loop-qcd-flow-not-a-derivation-of-qcd-from-ads"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.finiteDensity_holographic_complexAction_chain where
  formalizes @ "claim:d3-d7-finite-baryon-density-grand-potential-has-derivative-minus-density-and-its-euclidean-complex-action-damping-is-bounded-by-one-with-unit-modulus-at-the-second-order-threshold",
  requires @ "claim:nonnegative-d3-d7-normalization-and-the-karch-obannon-renormalized-on-shell-action",
  supported_by @ "paper:karch-obannon-2007-holographic-thermodynamics-finite-baryon-density",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.FiniteBaryonDensityPhaseTransition.sRen_hasDerivAt",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:exact-thermodynamic-and-modulus-consequences-of-the-supplied-d3-d7-on-shell-action-not-a-construction-of-the-probe-brane-solution"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.maldacena_qcd_balance_at_crossover where
  formalizes @ "claim:at-a-constructed-positive-uv-ir-matching-radius-the-magnitude-of-the-maldacena-conformal-quark-potential-equals-the-qcd-linear-string-potential",
  requires @ "claim:positive-thooft-coupling-positive-qcd-string-tension-and-a-phenomenological-cornell-type-matching-ansatz",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.maldacenaQuarkPotential",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential.cornell_terms_balance_at_crossover",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:a-controlled-algebraic-crossover-not-a-derivation-of-confining-qcd-from-conformal-n-equals-four-super-yang-mills"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.finiteDensity_baryonSusceptibility_pos where
  formalizes @ "claim:above-the-d3-d7-finite-density-threshold-the-baryon-susceptibility-is-strictly-positive",
  requires @ "claim:positive-probe-brane-normalization-positive-quark-mass-nonzero-string-scale-and-chemical-potential-at-least-the-mass",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.FiniteBaryonDensityPhaseTransition.density_hasDerivAt",
  supported_by @ "paper:karch-obannon-2007-holographic-thermodynamics-finite-baryon-density",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:stability-of-the-supplied-probe-brane-density-formula-not-a-nonperturbative-qcd-susceptibility-computation"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.qcdScale_traceAnomaly_hadronMass_chain where
  formalizes @ "claim:one-loop-dimensional-transmutation-generates-a-positive-qcd-scale-whose-fourth-power-gluon-condensate-identification-gives-a-negative-trace-anomaly-and-positive-hadron-mass-squared",
  requires @ "assumption:the-positive-gluon-condensate-scale-is-identified-with-lambda-qcd-to-the-fourth-power",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.dimensional_transmutation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.trace_anomaly_origin_of_hadron_mass",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:derives-sign-and-scale-structure-conditionally-not-the-gluon-condensate-coefficient-or-a-numerical-hadron-mass"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.thermalBeta_polyakov_heating_directions where
  formalizes @ "claim:raising-temperature-at-fixed-momentum-makes-the-displayed-thermal-beta-function-more-negative-while-the-polyakov-complex-action-modulus-increases",
  requires @ "claim:fixed-momentum-high-temperature-beta-model-and-nonnegative-single-quark-free-energy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaHighTemp_antitone_temp",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.polyakov_grows_with_temperature",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:the-two-monotonicities-are-simultaneous-but-the-thermal-beta-sign-alone-does-not-prove-confinement-or-deconfinement"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontDilatonPotential_quadratic where
  formalizes @ "claim:the-positive-quadratic-dilaton-profile-reduces-the-general-light-front-holographic-potential-to-kappa-fourth-zeta-squared-plus-two-kappa-squared-times-j-minus-one",
  requires @ "claim:nonzero-light-front-radial-coordinate-for-the-unsimplified-inverse-zeta-expression",
  supported_by @ "paper:de-teramond-brodsky-arxiv-1206-4365v2-eq-8",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:an-exact-pointwise-substitution-into-the-paper-potential-not-a-construction-of-the-continuum-light-front-eigenfunctions-or-a-derivation-of-qcd"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFront_scalar_bf_iff_orbitalCasimir_nonneg where
  formalizes @ "claim:for-the-spin-zero-light-front-ads-mass-relation-the-ads-five-breitenlohner-freedman-stability-bound-is-equivalent-to-nonnegative-orbital-casimir",
  supported_by @ "paper:de-teramond-brodsky-arxiv-1206-4365v2-ads-mass-orbital-relation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.breitenlohnerFreedman",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:an-exact-stability-dictionary-for-the-supplied-mass-orbital-identification-not-a-proof-of-the-full-boundary-unitary-representation"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontMassSpectrumSq_reggeSpacings where
  formalizes @ "claim:the-soft-wall-light-front-mass-squared-tower-has-equal-four-kappa-squared-spacing-under-one-radial-or-two-spin-or-two-orbital-units",
  supported_by @ "paper:de-teramond-brodsky-arxiv-1206-4365v2-eq-9",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:exact-spacing-consequences-of-the-paper-spectrum-formula-not-a-spectral-completeness-proof-a-continuum-mode-construction-or-an-empirical-fit-of-kappa"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontSoftWallRadialPotential_eq_isotonic where
  formalizes @ "claim:the-complete-soft-wall-light-front-radial-potential-is-exactly-a-rational-isotonic-potential-plus-the-spin-dependent-constant-shift",
  supported_by @ "paper:de-teramond-brodsky-arxiv-1206-4365v2-light-front-wave-equation-and-eq-8",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator.isotonicRational",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:an-exact-pointwise-operator-potential-identification-away-from-zeta-zero-not-yet-a-construction-of-the-singular-oscillator-eigenbasis"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontSoftWallRadialPotential_ge where
  formalizes @ "claim:outside-the-critical-orbital-channel-the-soft-wall-light-front-radial-potential-has-the-explicit-isotonic-am-gm-lower-bound",
  requires @ "claim:nonzero-soft-wall-scale-nonzero-radial-coordinate-and-orbital-square-strictly-greater-than-one-quarter",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator.isotonicRational_ge",
  epistemic_status @ "risky",
  caveat @ "claim:a-pointwise-coercive-bound-for-the-stated-orbital-range-not-a-self-adjointness-domain-or-spectral-completeness-theorem-and-not-the-l-equals-zero-bf-channel"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFront_scalar_conformalDimension where
  formalizes @ "claim:the-spin-zero-light-front-ads-mass-orbital-relation-fixes-the-standard-boundary-conformal-dimension-to-two-plus-absolute-orbital-momentum",
  supported_by @ "paper:de-teramond-brodsky-arxiv-1206-4365v2-ads-mass-orbital-relation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.conformalDimension",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:an-exact-bulk-mass-boundary-dimension-dictionary-on-the-standard-gkp-branch-not-an-independent-derivation-of-ads-cft"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFront_scalar_nearBoundary_radial where
  formalizes @ "claim:the-power-profile-z-to-two-plus-absolute-l-solves-the-differentiated-ads-five-near-boundary-radial-equation-at-the-light-front-mass-minus-four-plus-l-squared",
  requires @ "claim:positive-ads-radial-coordinate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions.conformalDimension_solves_radial",
  supported_by @ "paper:de-teramond-brodsky-arxiv-1206-4365v2-ads-wave-equation",
  epistemic_status @ "risky",
  caveat @ "claim:a-genuine-continuum-near-boundary-power-mode-not-the-full-soft-wall-laguerre-eigenfunction-normalization-self-adjoint-domain-or-completeness-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.electromagnetic_gravitational_density_map_agree where
  formalizes @ "claim:the-electromagnetic-current-and-gravitational-energy-momentum-tensor-form-factor-mappings-give-the-same-ads-light-front-spectator-density-and-the-two-parton-wavefunction-density",
  requires @ "claim:the-light-front-endpoint-x-equals-one-is-excluded-from-the-spectator-density-formula",
  supported_by @ "paper:brodsky-de-teramond-arxiv-0707-3859-electromagnetic-light-front-mapping",
  supported_by @ "paper:brodsky-de-teramond-arxiv-0804-0452-gravitational-light-front-mapping",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-exact-common-density-dictionary-does-not-identify-the-electromagnetic-and-gravitational-bulk-probes-at-nonzero-momentum-transfer"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.adsProbeFormFactor_zero_eq_normalization where
  formalizes @ "claim:any-continuum-ads-bulk-probe-that-is-pointwise-one-at-zero-momentum-transfer-reduces-to-the-common-hadron-normalization-integral",
  requires @ "claim:the-bulk-to-boundary-probe-obeys-the-zero-momentum-boundary-condition-pointwise-on-positive-ads-radius",
  supported_by @ "paper:brodsky-de-teramond-arxiv-0707-3859-electromagnetic-form-factor-normalization",
  supported_by @ "paper:brodsky-de-teramond-arxiv-0804-0452-gravitational-form-factor-normalization",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:a-continuum-overlap-and-sum-rule-reduction-not-an-integrability-proof-or-a-construction-of-bessel-bulk-to-boundary-propagators"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.softWallPion_formFactor_normalization_slope_radius where
  formalizes @ "claim:the-twist-two-soft-wall-pion-monopole-is-charge-normalized-has-origin-slope-minus-one-over-four-kappa-squared-and-charge-radius-squared-three-over-two-kappa-squared",
  requires @ "claim:nonzero-soft-wall-scale-kappa-and-the-standard-charge-radius-from-form-factor-slope-convention",
  supported_by @ "paper:brodsky-de-teramond-arxiv-0707-3859-soft-wall-twist-two-form-factor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.chargeRadiusSqFromSlope",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:an-exact-consequence-of-the-soft-wall-monopole-ansatz-not-a-fit-or-independent-prediction-of-kappa-or-the-observed-pion-radius"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.softWallPionWavefunction_full_normalization where
  formalizes @ "claim:the-lowest-soft-wall-pion-light-front-wavefunction-is-kappa-over-root-pi-times-root-x-one-minus-x-times-exp-minus-kappa-squared-zeta-squared-over-two-and-is-normalized-on-the-full-longitudinal-transverse-carrier",
  requires @ "claim:nonzero-soft-wall-scale-and-the-two-parton-holographic-coordinate-zeta-squared-equals-x-one-minus-x-times-b-squared",
  supported_by @ "paper:brodsky-de-teramond-arxiv-0707-3859-soft-wall-pion-impact-wavefunction",
  supported_by @ "lean:integral_rpow_mul_exp_neg_mul_rpow",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.electromagnetic_gravitational_density_map_agree",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:exact-continuum-normalization-and-coordinate-map-of-the-paper-supplied-n-equals-l-equals-zero-soft-wall-mode-not-spectral-completeness-an-interacting-qcd-wavefunction-or-a-fit-of-kappa"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.softWallPionWavefunction_meanZetaSq where
  formalizes @ "claim:the-normalized-lowest-soft-wall-pion-light-front-state-has-full-continuum-invariant-transverse-second-moment-mean-zeta-squared-equal-to-one-over-kappa-squared",
  requires @ "claim:the-lowest-soft-wall-pion-light-front-wavefunction-is-kappa-over-root-pi-times-root-x-one-minus-x-times-exp-minus-kappa-squared-zeta-squared-over-two-and-is-normalized-on-the-full-longitudinal-transverse-carrier",
  supported_by @ "lean:integral_rpow_mul_exp_neg_mul_rpow",
  supported_by @ "paper:brodsky-de-teramond-arxiv-0707-3859-soft-wall-pion-impact-wavefunction",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:a-derived-continuum-observable-of-the-paper-supplied-normalized-soft-wall-mode-not-an-independent-fit-of-kappa-a-measured-charge-radius-or-an-interacting-qcd-state-construction"

zil_file_contract physlib.adsCftQcdComplexActionBridges where
  promises "Eighteen AdS-CFT/QCD bridges are explicit. The Poincare radial trajectory z = exp(-t) realizes one-loop QCD ultraviolet asymptotic freedom as simultaneous z-to-zero and coupling-to-zero limits. The exact D3/D7 finite-density grand potential differentiates to minus baryon density, its Euclidean action is a bounded master complex-action damping factor restoring unit modulus at threshold, and its baryon susceptibility is strictly positive above threshold. A positive Cornell-type matching radius balances Maldacena's conformal inverse-distance potential against the QCD linear string potential. One-loop dimensional transmutation supplies a positive Lambda-QCD scale which, under the explicit gluon-condensate identification with Lambda-QCD to the fourth power, yields a negative trace anomaly and positive hadron mass-squared. Heating at fixed momentum makes the displayed thermal beta-function more negative while increasing the Polyakov complex-action modulus. The de Teramond-Brodsky light-front holographic equations are represented by the exact quadratic-dilaton soft-wall potential, scalar BF-bound/orbital-Casimir equivalence, equal radial spin and orbital Regge mass-squared spacings, exact isotonic decomposition with a coercive lower bound away from the critical orbital channel, the boundary dimension two plus absolute L, and the genuine differentiated near-boundary AdS radial power mode. The electromagnetic and gravitational form-factor derivations share the same light-front spectator density, zero-momentum continuum probes reduce to one AdS hadron normalization integral, the twist-two soft-wall pion monopole is normalized with its exact origin slope and charge-radius formula, and the explicit lowest soft-wall pion wavefunction is normalized on the full longitudinal-transverse continuum with derived invariant second moment one over kappa squared."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.runningCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.FiniteBaryonDensityPhaseTransition.sRen",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.maldacenaWilsonCoefficient",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential.crossoverRadius",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.traceAnomaly",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.polyakovMagnitude",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.breitenlohnerFreedman",
    "lean:Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator.isotonicRational_ge",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions.conformalDimension_solves_radial",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.ProtonProperties.chargeRadiusSqFromSlope"
  ]
  forbids_substitutes [
    "claiming that conformal N equals four super Yang-Mills is confining QCD",
    "claiming the radial scale convention derives the AdS-CFT correspondence",
    "claiming the D3/D7 probe-brane action is constructed rather than imported from its analytic carrier",
    "identifying a bounded scalar modulus with convergence of a quantum state or operator",
    "deriving a numerical gluon condensate or hadron mass from dimensional transmutation alone",
    "using the sign of the fixed-momentum thermal beta function as a proof of center-symmetry confinement or deconfinement",
    "claiming that the light-front spectrum constructs continuum eigenfunctions or proves spectral completeness",
    "claiming that a pointwise isotonic lower bound proves a self-adjoint domain or singular-oscillator completeness",
    "claiming that the near-boundary power mode is the normalized full soft-wall eigenbasis",
    "claiming the common electromagnetic and gravitational density map makes their nonzero-momentum bulk probes identical",
    "claiming that a zero-momentum overlap identity supplies missing integrability or constructs the Bessel propagators",
    "claiming that the soft-wall pion radius identity fits kappa or predicts the measured radius without model input",
    "claiming that normalization of the lowest soft-wall pion mode proves an interacting qcd construction or spectral completeness",
    "identifying the model-specific invariant zeta second moment with an independently measured charge radius",
    "attributing Einstein-Cartan Einstein-Maxwell BCJ or gravitational second-Bianchi dynamics to arXiv 1206.4365"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.adsBoundary_qcdRunningCoupling_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.finiteDensity_holographic_complexAction_chain,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.maldacena_qcd_balance_at_crossover,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.finiteDensity_baryonSusceptibility_pos,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.qcdScale_traceAnomaly_hadronMass_chain,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.thermalBeta_polyakov_heating_directions,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontDilatonPotential_quadratic,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFront_scalar_bf_iff_orbitalCasimir_nonneg,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontMassSpectrumSq_reggeSpacings,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontSoftWallRadialPotential_eq_isotonic,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontSoftWallRadialPotential_ge,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFront_scalar_conformalDimension,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFront_scalar_nearBoundary_radial,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.electromagnetic_gravitational_density_map_agree,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.adsProbeFormFactor_zero_eq_normalization,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.softWallPion_formFactor_normalization_slope_radius,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.softWallPionWavefunction_full_normalization,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.softWallPionWavefunction_meanZetaSq
  ]

#zil_formalization_lint physlib.adsCftQcdComplexActionBridges

/- ZIL-END -/

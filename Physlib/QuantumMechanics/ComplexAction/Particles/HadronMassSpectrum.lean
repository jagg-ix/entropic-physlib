/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel
meta import Zil

/-!
# Hadron mass spectrum: octet, decuplet, mesons, quarkonia, and the SU(3) mass formulas

Numerical hadron masses (PDG) attached to the existing `HadronFlavorModel.NamedHadron`, together with
the **Gell-Mann–Okubo** octet mass formula, the **decuplet equal-spacing rule**, and Gell-Mann's
**Ω⁻ mass prediction** — the SU(3)-symmetry relations that organize the spectrum. The masses are
**data**; the mass formulas are **theorems derived from the SU(3) mass ansatz**.

* **§A — the named-hadron masses.** `hadronMass : NamedHadron → ℝ` (MeV), with the proton/neutron
  isospin splitting (`proton_lighter_than_neutron`), the strange-quark cost (`kaon_heavier_than_pion`),
  and the quarkonium ordering (`charmonium_lighter_than_bottomonium`).
* **§B — the Gell-Mann–Okubo octet formula.** From the SU(3) mass ansatz
  `m = a + bY + c(I(I+1) − Y²/4)`, the baryon octet obeys `2(N + Ξ) = 3Λ + Σ` (`gellMannOkubo_octet`)
  and the pseudoscalar mesons (in `m²`, with `b = 0`) obey `4K = 3η + π` (`gellMannOkubo_meson`).
* **§C — the decuplet equal-spacing rule and the Ω⁻ prediction.** From the decuplet ansatz `m = a + bY`,
  the members are equally spaced (`decuplet_equal_spacing`), and `Ω = 2Ξ* − Σ*` — Gell-Mann's 1962
  prediction of the Ω⁻ mass (`decuplet_omega_prediction`).

**Honest layering.** Proven: the mass orderings, and the GMO/equal-spacing/Ω-prediction relations as
exact algebraic consequences of the SU(3) mass ansatz. Interpretive: the numerical masses are empirical
inputs (PDG); the ansatz (mass linear in the SU(3) Casimir data) is the flavor-symmetry model, which
the data satisfy to ~1% — the GMO/equal-spacing theorems here are the *reason* those near-equalities
hold.

## References

* M. Gell-Mann; S. Okubo (SU(3) mass formula); Particle Data Group, PTEP 2022, 083C01 (masses). Reuses
  `HadronFlavorModel.NamedHadron`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum

open Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel


/-- **The named-hadron masses** (PDG, MeV): baryon octet (`p, n, Λ, Σ, Ξ`), `Ω⁻`, `Λ_c⁺`, the light
mesons (`π, K`), `D⁺`, and the quarkonia `J/ψ`, `Υ`. -/
noncomputable def hadronMass : NamedHadron → ℝ
  | .proton => 938.272
  | .neutron => 939.565
  | .lambda => 1115.683
  | .sigmaPlus => 1189.37
  | .sigmaZero => 1192.642
  | .sigmaMinus => 1197.449
  | .xiZero => 1314.86
  | .xiMinus => 1321.71
  | .omegaMinus => 1672.45
  | .lambdaCPlus => 2286.46
  | .pionPlus => 139.570
  | .pionZero => 134.977
  | .pionMinus => 139.570
  | .kaonPlus => 493.677
  | .kaonZero => 497.611
  | .dPlus => 1869.66
  | .charmoniumJpsi => 3096.900
  | .bottomoniumUpsilon => 9460.30

/-- **The proton is lighter than the neutron** `m_p < m_n` — the isospin/electromagnetic mass splitting
that makes the free proton stable and the free neutron `β`-unstable. -/
lemma proton_lighter_than_neutron : hadronMass .proton < hadronMass .neutron := by
  norm_num [hadronMass]

/-- **The kaon is heavier than the pion** `m_K > m_π` — the mass cost of replacing a light quark with a
strange quark. -/
lemma kaon_heavier_than_pion : hadronMass .pionPlus < hadronMass .kaonPlus := by
  norm_num [hadronMass]

/-- **Charmonium is lighter than bottomonium** `m_{J/ψ} < m_Υ` — the `b b̄` bound state sits far above
the `c c̄` one, reflecting `m_b ≫ m_c`. -/
lemma charmonium_lighter_than_bottomonium :
    hadronMass .charmoniumJpsi < hadronMass .bottomoniumUpsilon := by
  norm_num [hadronMass]


/-- **The SU(3) octet mass ansatz** `m = a + bY + c(I(I+1) − Y²/4)`, linear in hypercharge `Y` and the
isospin Casimir `I(I+1)`. -/
noncomputable def octetMass (a b c Y I : ℝ) : ℝ := a + b * Y + c * (I * (I + 1) - Y ^ 2 / 4)

/-- **The Gell-Mann–Okubo baryon-octet formula** `2(N + Ξ) = 3Λ + Σ` (Gell-Mann, Okubo): from the SU(3)
ansatz, with `N(Y=1,I=½)`, `Λ(Y=0,I=0)`, `Σ(Y=0,I=1)`, `Ξ(Y=−1,I=½)`, the octet masses obey this exact
linear relation — the reason the measured combination holds to ~0.6%. -/
lemma gellMannOkubo_octet (a b c : ℝ) :
    2 * (octetMass a b c 1 (1 / 2) + octetMass a b c (-1) (1 / 2))
      = 3 * octetMass a b c 0 0 + octetMass a b c 0 1 := by
  unfold octetMass; ring

/-- **The Gell-Mann–Okubo pseudoscalar-meson formula** `4K = 3η + π` (in squared masses, `b = 0`): for
mesons the hypercharge-linear term vanishes by particle–antiparticle symmetry, giving the octet
relation among `m²`. -/
lemma gellMannOkubo_meson (a c : ℝ) :
    4 * octetMass a 0 c 1 (1 / 2) = 3 * octetMass a 0 c 0 0 + octetMass a 0 c 0 1 := by
  unfold octetMass; ring


/-- **The SU(3) decuplet mass ansatz** `m = a + bY`, linear in hypercharge (the decuplet's isospin is
fixed by `Y`). -/
noncomputable def decupletMass (a b Y : ℝ) : ℝ := a + b * Y

/-- **The decuplet equal-spacing rule** `Δ − Σ* = Σ* − Ξ* = Ξ* − Ω` (Gell-Mann): from the linear ansatz,
the decuplet `Δ(Y=1), Σ*(Y=0), Ξ*(Y=−1), Ω(Y=−2)` masses are equally spaced by one unit of strangeness. -/
lemma decuplet_equal_spacing (a b : ℝ) :
    decupletMass a b 1 - decupletMass a b 0 = decupletMass a b 0 - decupletMass a b (-1) ∧
      decupletMass a b 0 - decupletMass a b (-1) = decupletMass a b (-1) - decupletMass a b (-2) := by
  unfold decupletMass; constructor <;> ring

/-- **Gell-Mann's Ω⁻ mass prediction** `Ω = 2Ξ* − Σ*` (1962): the equal-spacing rule fixes the `Ω⁻`
mass from `Ξ*` and `Σ*` — the prediction (≈ 1685 MeV) that was confirmed by the discovery of the `Ω⁻`
(1672 MeV). -/
lemma decuplet_omega_prediction (a b : ℝ) :
    decupletMass a b (-2) = 2 * decupletMass a b (-1) - decupletMass a b 0 := by
  unfold decupletMass; ring

end Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.gellMannOkubo_octet where
  formalizes @ "claim:the-gell-mann-okubo-mass-formula-for-the-baryon-octet-relates-the-nucleon-sigma-lambda-and-xi-masses-from-su3-flavor-breaking-linear-in-hypercharge-and-isospin",
  supported_by @ "paper:gell-mann-okubo-su3-mass-formula"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.decuplet_equal_spacing where
  formalizes @ "claim:the-baryon-decuplet-obeys-the-equal-spacing-rule-mass-linear-in-hypercharge",
  supported_by @ "paper:gell-mann-okubo-su3-mass-formula"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.decuplet_omega_prediction where
  formalizes @ "claim:the-omega-minus-mass-is-predicted-by-the-decuplet-equal-spacing-rule-as-twice-xi-star-minus-sigma-star-the-1962-su3-prediction-confirmed-by-discovery",
  requires @ "claim:the-baryon-decuplet-obeys-the-equal-spacing-rule-mass-linear-in-hypercharge",
  supported_by @ "paper:gell-mann-okubo-su3-mass-formula"

zil_file_contract physlib.hadronMassSpectrum where
  promises "The SU(3)-flavor hadron mass spectrum: the Gell-Mann-Okubo mass formula for the baryon octet (masses linear in hypercharge and the isospin Casimir), the equal-spacing rule for the baryon decuplet (mass linear in hypercharge), the Gell-Mann Omega-minus mass prediction as twice Xi-star minus Sigma-star (the 1962 prediction confirmed by discovery), the analogous meson octet formula, and the mass orderings proton below neutron, pion below kaon, charmonium below bottomonium."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.hadronMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.octetMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.decupletMass"]
  forbids_substitutes ["a QCD calculation of the numerical hadron masses, which are PDG inputs to the mass orderings",
    "a derivation of the Gell-Mann-Okubo coefficients, which parametrize the SU(3) breaking"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.proton_lighter_than_neutron,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.gellMannOkubo_octet,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.gellMannOkubo_meson,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.decuplet_equal_spacing,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronMassSpectrum.decuplet_omega_prediction]

/- ZIL-END -/

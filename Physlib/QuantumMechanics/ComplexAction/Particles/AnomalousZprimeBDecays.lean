/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
meta import Zil

/-!
# The anomalous `U(1)_X = Y₃ + (a/6)(L_μ − L_τ)` Z′ model (Davighi, JHEP 08 (2021) 101)

Formalization of the gauge-anomaly algebra of J. Davighi, *"Anomalous Z′ bosons for anomalous B decays"*,
JHEP **08** (2021) 101, arXiv:2105.06918 — a family-non-universal `U(1)_X` extension of the Standard Model that
mediates the `b → sℓℓ` neutral-current B-anomalies through a TeV-scale Z′, with the charge assignment
`X = Y₃ + (a/6)(L_μ − L_τ)`, `a ∈ ℤ` (Eq. 2.16).

The model is deliberately **anomalous** at the weak scale: of the six gauge anomalies, four are arranged to
vanish but two — the mixed `U(1)_Y U(1)_X²` and the cubic `U(1)_X³` — are non-zero and *proportional to the
muon charge* `a/6` (Eq. 2.17), so the anomaly structure is tied to the `b→sℓℓ` data. The leftover anomalies are
cancelled in the UV by a pair of heavy fermions, chiral only under `U(1)_X` (Appendix A).

* **§A — the charge solution & Yukawa constraints.** The normalised solution (Eqs. 2.14–2.15) and the
  third-family Yukawa conditions (Eqs. 2.3–2.5) it satisfies.
* **§B — the six anomaly coefficients (Eqs. 2.8–2.13).** `A_SU3X = A_SU2X = A_YYX = A_gravX = 0`, while
  `A_YXX = a/6` and `A_XXX = a/4` (Eq. 2.17); both are muon-charge multiples
  (`anomalies_proportional_to_muon_charge`).
* **§C — Appendix-A UV cancellation.** The `N = 2` cubic anomaly equation factorises
  (Eq. A.5), isolating the non-trivial root `y = (w₁+w₂)/6` that makes the full theory anomaly-free for any `a`.

All charges are rationals; every statement is an exact `ring` / `norm_num` identity, with no approximation
or proof placeholder. The model's `a/6`-tied anomaly connects thematically to the muon-anomaly arc of this repository
(`MuonAnomaly.AnomalyRapidity`, `WMassAnomaly.EntropicTime`).

## References

* J. Davighi, "Anomalous Z′ bosons for anomalous B decays", JHEP 08 (2021) 101, arXiv:2105.06918,
  DOI:10.1007/JHEP08(2021)101 — Eqs. (2.3)–(2.17), Appendix A (A.1)–(A.5).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays

/-!

`{Q₃, U₃, D₃, L₃, E₃, H, L₂, E₂}` are the `U(1)_X` charges of the third-family quark doublet/up/down, the
third- and second-family lepton doublet/charged lepton, and the Higgs, normalised so the quark charges coincide
with third-family hypercharge `Y₃`. The integer `a` is the coefficient of the `L_μ − L_τ` component. -/

/-- `Q₃ = 1/6` — third-family quark doublet. -/
def Q3 : ℚ := 1 / 6
/-- `U₃ = 2/3` — third-family right-handed up quark. -/
def U3 : ℚ := 2 / 3
/-- `D₃ = −1/3` — third-family right-handed down quark. -/
def D3 : ℚ := -1 / 3
/-- `H = 1/2` — the Higgs `U(1)_X` charge. -/
def Hc : ℚ := 1 / 2
/-- `L₃ = (−3 − a)/6` — third-family lepton doublet. -/
def L3 (a : ℚ) : ℚ := (-3 - a) / 6
/-- `E₃ = (−6 − a)/6` — third-family right-handed charged lepton. -/
def E3 (a : ℚ) : ℚ := (-6 - a) / 6
/-- `L₂ = a/6` — second-family (muon) lepton doublet; this is the gauged muon charge. -/
def L2 (a : ℚ) : ℚ := a / 6
/-- `E₂ = a/6` — second-family right-handed charged lepton (vector-like with `L₂`, as the NCBA fit needs). -/
def E2 (a : ℚ) : ℚ := a / 6

/-- The **gauged muon charge** `a/6` — the coefficient through which `X` couples to the `L_μ − L_τ` current. -/
def muonCharge (a : ℚ) : ℚ := a / 6

/-- **[Up-Yukawa constraint, Eq. 2.3]** `Q₃ − U₃ = −H`. -/
lemma yukawa_up : Q3 - U3 = -Hc := by norm_num [Q3, U3, Hc]

/-- **[Down-Yukawa constraint, Eq. 2.4]** `Q₃ − D₃ = H`. -/
lemma yukawa_down : Q3 - D3 = Hc := by norm_num [Q3, D3, Hc]

/-- **[Lepton-Yukawa constraint, Eq. 2.5]** `L₃ − E₃ = H` — the third-family charged-lepton Yukawa. -/
lemma yukawa_lepton (a : ℚ) : L3 a - E3 a = Hc := by unfold L3 E3 Hc; ring


/-- `SU(3)² U(1)_X` anomaly `= 2Q₃ − U₃ − D₃` (Eq. 2.8). -/
def anomSU3X : ℚ := 2 * Q3 - U3 - D3
/-- `SU(2)_L² U(1)_X` anomaly `= 3Q₃ + L₂ + L₃` (Eq. 2.9). -/
def anomSU2X (a : ℚ) : ℚ := 3 * Q3 + L2 a + L3 a
/-- `U(1)_Y² U(1)_X` anomaly `= −3(3Q₃ − L₂ + L₃ + 2E₂)` (Eq. 2.10). -/
def anomYYX (a : ℚ) : ℚ := -3 * (3 * Q3 - L2 a + L3 a + 2 * E2 a)
/-- `U(1)_Y U(1)_X²` anomaly `= −L₂² + E₂² − 2H(L₃ + 3Q₃)` (Eq. 2.11). -/
def anomYXX (a : ℚ) : ℚ := -(L2 a) ^ 2 + (E2 a) ^ 2 - 2 * Hc * (L3 a + 3 * Q3)
/-- `U(1)_X³` cubic anomaly `= 2L₂³ + L₃³ − E₂³ + 3H L₃² + H³ − 3H²(L₃ + 6Q₃)` (Eq. 2.12). -/
def anomXXX (a : ℚ) : ℚ :=
  2 * (L2 a) ^ 3 + (L3 a) ^ 3 - (E2 a) ^ 3 + 3 * Hc * (L3 a) ^ 2 + Hc ^ 3
    - 3 * Hc ^ 2 * (L3 a + 6 * Q3)
/-- Gravitational `U(1)_X` anomaly `= 2L₂ + L₃ − E₂ + H` (Eq. 2.13). -/
def anomGravX (a : ℚ) : ℚ := 2 * L2 a + L3 a - E2 a + Hc

/-- **[Eq. 2.8: the mixed `SU(3)` anomaly vanishes]** `A_{SU(3),X} = 0` — by the top/bottom Yukawa constraints
`Q₃ − U₃ = −H`, `Q₃ − D₃ = H` (so no new coloured states are needed). -/
lemma anomSU3X_zero : anomSU3X = 0 := by norm_num [anomSU3X, Q3, U3, D3]

/-- **[Eq. 2.9: the `SU(2)_L` anomaly vanishes]** `A_{SU(2),X} = 0` — the first of the three linear anomalies
set to zero at the weak scale. -/
lemma anomSU2X_zero (a : ℚ) : anomSU2X a = 0 := by unfold anomSU2X Q3 L2 L3; ring

/-- **[Eq. 2.10: the `U(1)_Y²U(1)_X` anomaly vanishes]** `A_{YYX} = 0`. -/
lemma anomYYX_zero (a : ℚ) : anomYYX a = 0 := by unfold anomYYX Q3 L2 L3 E2; ring

/-- **[Eq. 2.13: the gravitational anomaly vanishes]** `A_{grav,X} = 0`. -/
lemma anomGravX_zero (a : ℚ) : anomGravX a = 0 := by unfold anomGravX L2 L3 E2 Hc; ring

/-- **[Eq. 2.11 / 2.17: the mixed `U(1)_YU(1)_X²` anomaly is the muon charge]** `A_{YXX} = a/6` — *non-zero*,
and exactly the gauged muon charge. This anomaly cannot be cancelled within the SM and signals the anomalous
nature of `U(1)_X`. -/
lemma anomYXX_eq (a : ℚ) : anomYXX a = a / 6 := by unfold anomYXX L2 E2 L3 Hc Q3; ring

/-- **[Eq. 2.12 / 2.17: the cubic `U(1)_X³` anomaly]** `A_{XXX} = a/4` — *non-zero*; the cubic anomaly the
Green–Schwarz / heavy-fermion mechanism must cancel in the UV. -/
lemma anomXXX_eq (a : ℚ) : anomXXX a = a / 4 := by unfold anomXXX L2 L3 E2 Hc Q3; ring

/-- **[Eq. 2.17: the anomalous structure is tied to the muon]** both non-vanishing anomalies are multiples of
the gauged muon charge `a/6`: `A_{YXX} = (muon charge)` and `A_{XXX} = (3/2)·(muon charge)`. Hence the entire
anomalous structure of the Z′ — and the strength of the Green–Schwarz couplings — is fixed by the `b→sℓℓ`
muon coupling. -/
lemma anomalies_proportional_to_muon_charge (a : ℚ) :
    anomYXX a = muonCharge a ∧ anomXXX a = (3 / 2) * muonCharge a := by
  refine ⟨?_, ?_⟩
  · rw [anomYXX_eq]; unfold muonCharge; ring
  · rw [anomXXX_eq]; unfold muonCharge; ring


/-- **[Eq. A.5: the `N = 2` cubic anomaly equation factorises]** With two pairs of heavy `U(1)_X`-chiral Weyl
fermions of charges `v₁,v₂` (left) and `w₁,w₂` (right) sharing hypercharge `y`, after imposing the
`U(1)_Y² U(1)_X` / gravitational constraint `Σv = Σw` (Eq. A.4, here `v₂ = w₁ + w₂ − v₁`), the cubic anomaly
sum (Eq. A.3) factorises as

  `(v₁ − w₁)(v₁ − w₂)(18y − 3(w₁ + w₂))`.

The trivial roots `v₁ = w₁`, `v₁ = w₂` give `y = 0` (no muon coupling, `a = 0`); the non-trivial root
`18y = 3(w₁ + w₂)` — i.e. `y = (w₁ + w₂)/6` — is what restores anomaly freedom for any `a ≠ 0`, as needed for
the essential coupling to muons. -/
lemma appendixA_cubic_factorisation (v₁ w₁ w₂ y : ℚ) :
    (w₁ - v₁) * (w₁ ^ 2 + w₁ * v₁ + v₁ ^ 2 - 9 * y * (w₁ + v₁))
        + (w₂ - (w₁ + w₂ - v₁)) *
          (w₂ ^ 2 + w₂ * (w₁ + w₂ - v₁) + (w₁ + w₂ - v₁) ^ 2 - 9 * y * (w₂ + (w₁ + w₂ - v₁)))
      = (v₁ - w₁) * (v₁ - w₂) * (18 * y - 3 * (w₁ + w₂)) := by ring

/-- **[The non-trivial anomaly-free root]** at `y = (w₁ + w₂)/6` the Appendix-A cubic factor `18y − 3(w₁+w₂)`
vanishes, so the cubic anomaly equation (Eq. A.3) is satisfied for *any* `v₁` — the heavy sector cancels the
`U(1)_X³` anomaly while leaving a non-zero hypercharge `y` (hence a non-zero muon coupling `a`). -/
lemma appendixA_nontrivial_root (v₁ w₁ w₂ : ℚ) :
    (w₁ - v₁) * (w₁ ^ 2 + w₁ * v₁ + v₁ ^ 2 - 9 * ((w₁ + w₂) / 6) * (w₁ + v₁))
        + (w₂ - (w₁ + w₂ - v₁)) *
          (w₂ ^ 2 + w₂ * (w₁ + w₂ - v₁) + (w₁ + w₂ - v₁) ^ 2
            - 9 * ((w₁ + w₂) / 6) * (w₂ + (w₁ + w₂ - v₁)))
      = 0 := by
  rw [appendixA_cubic_factorisation]; ring

end Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomYXX_eq where
  formalizes @ "claim:the-mixed-u1y-u1x-squared-gauge-anomaly-of-the-davighi-zprime-equals-one-sixth-the-muon-charge",
  supported_by @ "paper:davighi-anomalous-zprime-for-anomalous-b-decays-jhep-08-2021-101"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomXXX_eq where
  formalizes @ "claim:the-cubic-u1x-gauge-anomaly-of-the-davighi-zprime-equals-one-quarter-the-muon-charge",
  supported_by @ "paper:davighi-anomalous-zprime-for-anomalous-b-decays-jhep-08-2021-101"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomalies_proportional_to_muon_charge where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomXXX_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomYXX_eq",
  formalizes @ "claim:both-residual-gauge-anomalies-of-the-davighi-zprime-are-multiples-of-the-muon-charge-tying-the-anomaly-structure-to-the-b-to-s-lepton-data",
  requires @ "claim:the-mixed-u1y-u1x-squared-gauge-anomaly-of-the-davighi-zprime-equals-one-sixth-the-muon-charge",
  requires @ "claim:the-cubic-u1x-gauge-anomaly-of-the-davighi-zprime-equals-one-quarter-the-muon-charge"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.appendixA_nontrivial_root where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.appendixA_cubic_factorisation",
  formalizes @ "claim:the-appendix-a-cubic-anomaly-equation-of-the-heavy-fermion-pair-factorises-with-a-nontrivial-root-that-makes-the-uv-completed-theory-anomaly-free"

zil_file_contract physlib.anomalousZprimeBDecays where
  promises "The gauge-anomaly algebra of Davighi's family-non-universal U(1)_X = Y3 + (a/6)(L_mu - L_tau) Z-prime extension of the Standard Model, which mediates the b -> s lepton-lepton neutral-current B-anomalies through a TeV-scale Z-prime: of the six gauge anomalies four vanish (SU(3)^2 X, SU(2)^2 X, Y^2 X, grav-X) as exact rational identities, while the mixed Y X^2 and cubic X^3 anomalies equal a/6 and a/4 and are both proportional to the muon charge; the Appendix-A cubic anomaly equation of the heavy UV fermion pair factorises, isolating the nontrivial root that renders the full theory anomaly-free for any integer a."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomYXX",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomXXX",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomSU3X"]
  forbids_substitutes ["a family-universal U(1)_X charge assignment, which would not tie the residual anomaly to the muon charge",
    "an anomaly-free weak-scale model, whereas this construction is deliberately anomalous and UV-completed by heavy chiral fermions"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomSU2X_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomYYX_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomGravX_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomYXX_eq,
    Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomXXX_eq,
    Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.anomalies_proportional_to_muon_charge,
    Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.appendixA_cubic_factorisation,
    Physlib.QuantumMechanics.ComplexAction.Particles.AnomalousZprimeBDecays.appendixA_nontrivial_root]

/- ZIL-END -/

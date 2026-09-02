/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
public import Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
meta import Zil

/-!
# The flavor model of hadrons: strong Gell-Mann–Nishijima and the strange baryons

The earlier hadron files gave charge (`Particles.HadronChargeIntegrality`), baryon number and spin-statistics
(`Particles.HadronSpinStatistics`), and the *weak* Gell-Mann–Nishijima for up/down (`Particles.GellMannNishijima`). With the
flavor sector now assembled, a hadron can be modelled as a **composite of flavored quarks**, each carrying the
four flavor quantum numbers — electric charge `Q`, baryon number `B`, **strangeness `S`**, **isospin `I₃`** —
and the hadron's quantum numbers are the additive sums over its constituents.

The organizing law is the **(strong) Gell-Mann–Nishijima relation** `Q = I₃ + Y/2` with the *strong
hypercharge* `Y = B + S` (`gmn_strong_quark`). Unlike the weak version, it includes strangeness, so it covers
the strange sector. Because the quantum numbers are additive, the relation **lifts to any composite**
(`gmn_strong_baryon`): the whole baryon's charge equals its total isospin plus half its total hypercharge.

* **§A — the flavored quark.** `QuarkFlavor` (all six: `up, down, strange, charm, bottom, top`);
  `electricCharge` (via `windingCharge`), `baryonNumber` (`= 1/3`), `strangeness`, `charmness`, `bottomness`,
  `topness`, `isospinT3`, `hypercharge` (`= B + S + C + B' + T`); `gmn_strong_quark`.
* **§B — composite hadrons.** `listCharge`/`listStrangeness`/`listIsospinT3`/`listHypercharge` (additive sums);
  `gmn_strong_baryon` (the relation lifts to composites).
* **§C — the baryons.** `proton`/`neutron`/`lambda`, the Sigma triplet
  `Σ⁺ = uus`, `Σ⁰ = uds`, `Σ⁻ = dds`, the Xi doublet `Ξ⁰ = uss`, `Ξ⁻ = dss`,
  the Omega baryon `Ω⁻ = sss`, and the charmed `Λc`, with
  their *derived* charges/strangeness/charm, including the Lambda row `Λ = uds` and the strangeness ladder
  `Λ(−1), Ξ(−2), Ω(−3)`.
* **§D — the mesons.** `mesonCharge`/`mesonStrangeness`/… (antiquark negates every quantum number),
  `mesonBaryonNumber_eq_zero`, `gmn_strong_meson` (GMN for `q q̄`); the pion triplet
  `π⁺ = u dbar`, `π⁰ = (u ubar - d dbar)/sqrt 2`, `π⁻ = d ubar`;
  the kaon doublet `K⁺ = u sbar`, `K⁰ = d sbar`; `dPlus`.

**Honest layering.** Proven: the strong GMN `Q = I₃ + (B+S)/2` for each quark and (by additivity) for every
composite, and the named baryons' charges/strangeness *derived* from their quark content. The flavor quantum
numbers `(Q,B,S,I₃)` per quark are the empirical flavor assignments (input); GMN is the genuine constraint
relating them, and the hadron numbers are consequences. Hadron *masses* are QCD dynamics, not derived.

## References

* (Strong) Gell-Mann–Nishijima `Q = I₃ + (B+S)/2`; strange baryon octet/decuplet. `Physlib`
  (`Winding.QuarkChargeWinding.windingCharge`, `Particles.HadronSpinStatistics.quarkBaryonNumber`).
* J. A. Sheikh et al., "Isospin symmetry breaking in atomic nuclei", arXiv:2405.04946v1, Sec. 2:
  the isospin doublet, `T₃` projection, Pauli-generator convention `T = τ/2`, and isospin mixing/breaking.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel


/-- The six **quark flavors** — the three light (`up, down, strange`) and three heavy (`charm, bottom, top`). -/
inductive QuarkFlavor : Type
  | up | down | strange | charm | bottom | top
  deriving DecidableEq

namespace QuarkFlavor

/-- The winding number of each flavor (charge in thirds, `Winding.QuarkChargeWinding`): up-type (`up, charm, top`) `= 2`,
down-type (`down, strange, bottom`) `= −1`. -/
def windingNumber : QuarkFlavor → ℤ
  | up => 2 | down => -1 | strange => -1 | charm => 2 | bottom => -1 | top => 2

/-- **Electric charge** `Q` of a quark flavor, from its winding (up-type `+2/3`, down-type `−1/3`). -/
def electricCharge (q : QuarkFlavor) : ℚ := windingCharge q.windingNumber

/-- **Baryon number** `B = 1/3` for every quark. -/
def baryonNumber (_ : QuarkFlavor) : ℚ := quarkBaryonNumber

/-- **Strangeness** `S`: the strange quark carries `S = −1`, all others `0`. -/
def strangeness : QuarkFlavor → ℤ
  | strange => -1 | _ => 0

/-- **Charm** `C`: the charm quark carries `C = +1`, all others `0`. -/
def charmness : QuarkFlavor → ℤ
  | charm => 1 | _ => 0

/-- **Bottomness** `B'`: the bottom quark carries `B' = −1`, all others `0`. -/
def bottomness : QuarkFlavor → ℤ
  | bottom => -1 | _ => 0

/-- **Topness** `T`: the top quark carries `T = +1`, all others `0`. -/
def topness : QuarkFlavor → ℤ
  | top => 1 | _ => 0

/-- **Third isospin component** `I₃`: `up = +1/2`, `down = −1/2`, all heavier flavors `0` (isosinglets). -/
def isospinT3 : QuarkFlavor → ℚ
  | up => 1 / 2 | down => -1 / 2 | _ => 0

/-- **Strong hypercharge** `Y = B + S + C + B' + T` — the full flavor hypercharge summing baryon number,
strangeness, charm, bottomness and topness. -/
def hypercharge (q : QuarkFlavor) : ℚ :=
  baryonNumber q + (strangeness q : ℚ) + (charmness q : ℚ) + (bottomness q : ℚ) + (topness q : ℚ)

/-- **[Strong Gell-Mann–Nishijima for a quark]** `Q = I₃ + Y/2 = I₃ + (B+S+C+B'+T)/2` for *every* flavor — the
relation tying electric charge to isospin and the full flavor hypercharge, now covering the heavy quarks. -/
lemma gmn_strong_quark (q : QuarkFlavor) :
    electricCharge q = isospinT3 q + hypercharge q / 2 := by
  cases q <;>
    simp [electricCharge, isospinT3, hypercharge, baryonNumber, strangeness, charmness, bottomness,
      topness, windingNumber, windingCharge, quarkBaryonNumber] <;>
    norm_num

end QuarkFlavor


open QuarkFlavor

/-- **Electric charge of a composite** — the sum over its quark constituents. -/
def listCharge (qs : List QuarkFlavor) : ℚ := (qs.map electricCharge).sum
/-- **Strangeness of a composite** — the sum over constituents. -/
def listStrangeness (qs : List QuarkFlavor) : ℤ := (qs.map strangeness).sum
/-- **Total isospin `I₃` of a composite**. -/
def listIsospinT3 (qs : List QuarkFlavor) : ℚ := (qs.map isospinT3).sum
/-- **Total strong hypercharge of a composite**. -/
def listHypercharge (qs : List QuarkFlavor) : ℚ := (qs.map hypercharge).sum

@[simp] lemma listCharge_cons (q : QuarkFlavor) (qs : List QuarkFlavor) :
    listCharge (q :: qs) = electricCharge q + listCharge qs := by simp [listCharge]
@[simp] lemma listIsospinT3_cons (q : QuarkFlavor) (qs : List QuarkFlavor) :
    listIsospinT3 (q :: qs) = isospinT3 q + listIsospinT3 qs := by simp [listIsospinT3]
@[simp] lemma listHypercharge_cons (q : QuarkFlavor) (qs : List QuarkFlavor) :
    listHypercharge (q :: qs) = hypercharge q + listHypercharge qs := by simp [listHypercharge]

/-- **[Strong Gell-Mann–Nishijima for any composite]** `Q = I₃ + Y/2` for the whole hadron — the per-quark
relation lifts to any number of constituents by additivity of the quantum numbers. -/
lemma gmn_strong_baryon (qs : List QuarkFlavor) :
    listCharge qs = listIsospinT3 qs + listHypercharge qs / 2 := by
  induction qs with
  | nil => simp [listCharge, listIsospinT3, listHypercharge]
  | cons q qs ih =>
    rw [listCharge_cons, listIsospinT3_cons, listHypercharge_cons, gmn_strong_quark q, ih]; ring

/-- **[Hypercharge from charge and isospin]** the strong Gell-Mann--Nishijima
relation can be inverted: the flavor hypercharge is not an independent table
once electric charge and `I₃` are fixed. -/
lemma hypercharge_eq_two_mul_charge_sub_isospin (q : QuarkFlavor) :
    hypercharge q = 2 * (electricCharge q - isospinT3 q) := by
  have h := gmn_strong_quark q
  linarith

/-- **[Composite hypercharge from charge and isospin]** for any valence list,
the additive strong hypercharge is computed by `Y = 2(Q-I₃)`.  This is the
explicit quantum-number map used downstream by the loop/valence sector. -/
lemma listHypercharge_eq_two_mul_charge_sub_isospin
    (qs : List QuarkFlavor) :
    listHypercharge qs = 2 * (listCharge qs - listIsospinT3 qs) := by
  have h := gmn_strong_baryon qs
  linarith


/-- Proton `p = uud`. -/
def proton : List QuarkFlavor := [up, up, down]
/-- Neutron `n = udd`. -/
def neutron : List QuarkFlavor := [up, down, down]
/-- Lambda `Λ = uds` (strangeness `−1`). -/
def lambda : List QuarkFlavor := [up, down, strange]
/-- Sigma⁺ `Σ⁺ = uus` (strangeness `−1`). -/
def sigmaPlus : List QuarkFlavor := [up, up, strange]
/-- Sigma⁰ `Σ⁰ = uds` (same valence flavor content as `Λ`; different multiplet
state is outside this additive-flavor list model). -/
def sigmaZero : List QuarkFlavor := [up, down, strange]
/-- Sigma⁻ `Σ⁻ = dds` (strangeness `−1`). -/
def sigmaMinus : List QuarkFlavor := [down, down, strange]
/-- Xi⁰ `Ξ⁰ = uss` (strangeness `−2`). -/
def xiZero : List QuarkFlavor := [up, strange, strange]
/-- Xi⁻ `Ξ⁻ = dss` (strangeness `−2`). -/
def xiMinus : List QuarkFlavor := [down, strange, strange]
/-- Omega⁻ `Ω⁻ = sss` (strangeness `−3`). -/
def omegaMinus : List QuarkFlavor := [strange, strange, strange]

/-- **[Proton charge `+1`]** derived from `uud`. -/
lemma proton_charge : listCharge proton = 1 := by
  norm_num [listCharge, proton, electricCharge, windingNumber, windingCharge]
/-- **[Neutron charge `0`]** derived from `udd`. -/
lemma neutron_charge : listCharge neutron = 0 := by
  norm_num [listCharge, neutron, electricCharge, windingNumber, windingCharge]
/-- **[Lambda is neutral, strangeness `−1`]** `Λ = uds`. -/
lemma lambda_charge_strangeness : listCharge lambda = 0 ∧ listStrangeness lambda = -1 := by
  refine ⟨?_, ?_⟩
  · norm_num [listCharge, lambda, electricCharge, windingNumber, windingCharge]
  · simp [listStrangeness, lambda, strangeness]
/-- **[Sigma⁺: charge `+1`, strangeness `−1`]** `Σ⁺ = uus`. -/
lemma sigmaPlus_charge_strangeness : listCharge sigmaPlus = 1 ∧ listStrangeness sigmaPlus = -1 := by
  refine ⟨?_, ?_⟩
  · norm_num [listCharge, sigmaPlus, electricCharge, windingNumber, windingCharge]
  · simp [listStrangeness, sigmaPlus, strangeness]
/-- **[Sigma⁰: charge `0`, strangeness `−1`]** `Σ⁰ = uds`. -/
lemma sigmaZero_charge_strangeness : listCharge sigmaZero = 0 ∧ listStrangeness sigmaZero = -1 := by
  refine ⟨?_, ?_⟩
  · norm_num [listCharge, sigmaZero, electricCharge, windingNumber, windingCharge]
  · simp [listStrangeness, sigmaZero, strangeness]
/-- **[Sigma⁻: charge `−1`, strangeness `−1`]** `Σ⁻ = dds`. -/
lemma sigmaMinus_charge_strangeness : listCharge sigmaMinus = -1 ∧ listStrangeness sigmaMinus = -1 := by
  refine ⟨?_, ?_⟩
  · norm_num [listCharge, sigmaMinus, electricCharge, windingNumber, windingCharge]
  · simp [listStrangeness, sigmaMinus, strangeness]
/-- **[Xi⁰: charge `0`, strangeness `−2`]** `Ξ⁰ = uss`. -/
lemma xiZero_charge_strangeness : listCharge xiZero = 0 ∧ listStrangeness xiZero = -2 := by
  refine ⟨?_, ?_⟩
  · norm_num [listCharge, xiZero, electricCharge, windingNumber, windingCharge]
  · simp [listStrangeness, xiZero, strangeness]
/-- **[Xi⁻: charge `−1`, strangeness `−2`]** `Ξ⁻ = dss`. -/
lemma xiMinus_charge_strangeness : listCharge xiMinus = -1 ∧ listStrangeness xiMinus = -2 := by
  refine ⟨?_, ?_⟩
  · norm_num [listCharge, xiMinus, electricCharge, windingNumber, windingCharge]
  · simp [listStrangeness, xiMinus, strangeness]
/-- **[Omega⁻: charge `−1`, strangeness `−3`]** `Ω⁻ = sss` — the all-strange decuplet apex (Gell-Mann's
prediction), at the bottom of the strangeness ladder. -/
lemma omegaMinus_charge_strangeness :
    listCharge omegaMinus = -1 ∧ listStrangeness omegaMinus = -3 := by
  refine ⟨?_, ?_⟩
  · norm_num [listCharge, omegaMinus, electricCharge, windingNumber, windingCharge]
  · simp [listStrangeness, omegaMinus, strangeness]

/-- **[The strangeness ladder]** `Λ(−1), Ξ(−2), Ω(−3)` — each step adds one strange quark, lowering
strangeness by one. -/
lemma strangeness_ladder :
    listStrangeness lambda = -1 ∧ listStrangeness xiZero = -2 ∧ listStrangeness omegaMinus = -3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [listStrangeness, lambda, xiZero, omegaMinus, strangeness]

/-- **[Every baryon has baryon number `1`]** three quarks, each `B = 1/3`. -/
lemma baryon_baryonNumber (q₁ q₂ q₃ : QuarkFlavor) :
    baryonNumber q₁ + baryonNumber q₂ + baryonNumber q₃ = 1 := by
  simp only [baryonNumber, quarkBaryonNumber]; norm_num

/-- The Lambda baryon row has quark content `uds`. -/
lemma lambda_quarkContent : lambda = [up, down, strange] :=
  rfl

/-- The Lambda baryon contains a strange quark. -/
lemma lambda_contains_strange : strange ∈ lambda := by
  simp [lambda]

/-- The Lambda baryon has baryon number one: `B(u)+B(d)+B(s)=1`. -/
lemma lambda_baryonNumber_one :
    baryonNumber up + baryonNumber down + baryonNumber strange = 1 :=
  baryon_baryonNumber up down strange

/-- The Lambda baryon has total `I₃ = 0` and strong hypercharge `Y = 0`
because `B=1` and `S=-1`. -/
lemma lambda_isospin_hypercharge :
    listIsospinT3 lambda = 0 ∧ listHypercharge lambda = 0 := by
  refine ⟨?_, ?_⟩
  · norm_num [listIsospinT3, lambda, isospinT3]
  · norm_num [listHypercharge, lambda, hypercharge, baryonNumber, strangeness, charmness, bottomness,
      topness, quarkBaryonNumber]

/-- Capability predicate for the Lambda baryon:
`Λ = uds`, it contains one strange quark, has `Q = 0`, `S = -1`, `B = 1`,
`I₃ = 0`, `Y = 0`, satisfies strong Gell-Mann--Nishijima, and is a
three-quark fermionic baryon. -/
def HasLambdaBaryon : Prop :=
  lambda = [up, down, strange]
    ∧ strange ∈ lambda
    ∧ listCharge lambda = 0
    ∧ listStrangeness lambda = -1
    ∧ baryonNumber up + baryonNumber down + baryonNumber strange = 1
    ∧ listIsospinT3 lambda = 0
    ∧ listHypercharge lambda = 0
    ∧ listCharge lambda = listIsospinT3 lambda + listHypercharge lambda / 2
    ∧ compositeTwist 3 = -1

/-- The Lambda baryon row is checked from the existing flavor,
baryon-number, Gell-Mann--Nishijima, and spin-statistics infrastructure. -/
lemma lambdaBaryon_checked : HasLambdaBaryon :=
  ⟨lambda_quarkContent,
    lambda_contains_strange,
    lambda_charge_strangeness.1,
    lambda_charge_strangeness.2,
    lambda_baryonNumber_one,
    lambda_isospin_hypercharge.1,
    lambda_isospin_hypercharge.2,
    gmn_strong_baryon lambda,
    baryon_is_fermion⟩

/-- The Sigma baryon row has quark contents `Σ⁺ = uus`, `Σ⁰ = uds`,
`Σ⁻ = dds`. -/
lemma sigmaTriplet_quarkContent :
    sigmaPlus = [up, up, strange] ∧ sigmaZero = [up, down, strange]
      ∧ sigmaMinus = [down, down, strange] :=
  ⟨rfl, rfl, rfl⟩

/-- In the additive valence-flavor model, `Σ⁰` and `Λ` have the same `uds`
content. Distinguishing them requires extra multiplet/spin wavefunction
structure not represented by `List QuarkFlavor`. -/
lemma sigmaZero_flavor_eq_lambda : sigmaZero = lambda :=
  rfl

/-- All three Sigma baryons contain a strange quark. -/
lemma sigmaTriplet_contains_strange :
    strange ∈ sigmaPlus ∧ strange ∈ sigmaZero ∧ strange ∈ sigmaMinus := by
  simp [sigmaPlus, sigmaZero, sigmaMinus]

/-- Each Sigma baryon has baryon number one. -/
lemma sigmaTriplet_baryonNumber_one :
    baryonNumber up + baryonNumber up + baryonNumber strange = 1
      ∧ baryonNumber up + baryonNumber down + baryonNumber strange = 1
      ∧ baryonNumber down + baryonNumber down + baryonNumber strange = 1 :=
  ⟨baryon_baryonNumber up up strange,
    baryon_baryonNumber up down strange,
    baryon_baryonNumber down down strange⟩

/-- The Sigma isotriplet has `I₃ = +1,0,-1`, and all three have strong
hypercharge `Y = 0` because `B = 1` and `S = -1`. -/
lemma sigmaTriplet_isospin_hypercharge :
    listIsospinT3 sigmaPlus = 1 ∧ listIsospinT3 sigmaZero = 0
      ∧ listIsospinT3 sigmaMinus = -1
      ∧ listHypercharge sigmaPlus = 0 ∧ listHypercharge sigmaZero = 0
      ∧ listHypercharge sigmaMinus = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [listIsospinT3, sigmaPlus, isospinT3]
  · norm_num [listIsospinT3, sigmaZero, isospinT3]
  · norm_num [listIsospinT3, sigmaMinus, isospinT3]
  · norm_num [listHypercharge, sigmaPlus, hypercharge, baryonNumber, strangeness, charmness, bottomness,
      topness, quarkBaryonNumber]
  · norm_num [listHypercharge, sigmaZero, hypercharge, baryonNumber, strangeness, charmness, bottomness,
      topness, quarkBaryonNumber]
  · norm_num [listHypercharge, sigmaMinus, hypercharge, baryonNumber, strangeness, charmness, bottomness,
      topness, quarkBaryonNumber]

/-- Capability predicate for the Sigma baryon triplet:
`Σ⁺ = uus`, `Σ⁰ = uds`, `Σ⁻ = dds`; charges `+1,0,-1`; strangeness `-1`;
baryon number `1`; isotriplet values `I₃ = +1,0,-1`; hypercharge `Y = 0`;
strong Gell-Mann--Nishijima; and three-quark fermion statistics. -/
def HasSigmaBaryonTriplet : Prop :=
  sigmaPlus = [up, up, strange]
    ∧ sigmaZero = [up, down, strange]
    ∧ sigmaMinus = [down, down, strange]
    ∧ strange ∈ sigmaPlus ∧ strange ∈ sigmaZero ∧ strange ∈ sigmaMinus
    ∧ listCharge sigmaPlus = 1 ∧ listCharge sigmaZero = 0 ∧ listCharge sigmaMinus = -1
    ∧ listStrangeness sigmaPlus = -1 ∧ listStrangeness sigmaZero = -1
    ∧ listStrangeness sigmaMinus = -1
    ∧ baryonNumber up + baryonNumber up + baryonNumber strange = 1
    ∧ baryonNumber up + baryonNumber down + baryonNumber strange = 1
    ∧ baryonNumber down + baryonNumber down + baryonNumber strange = 1
    ∧ listIsospinT3 sigmaPlus = 1 ∧ listIsospinT3 sigmaZero = 0
    ∧ listIsospinT3 sigmaMinus = -1
    ∧ listHypercharge sigmaPlus = 0 ∧ listHypercharge sigmaZero = 0
    ∧ listHypercharge sigmaMinus = 0
    ∧ listCharge sigmaPlus = listIsospinT3 sigmaPlus + listHypercharge sigmaPlus / 2
    ∧ listCharge sigmaZero = listIsospinT3 sigmaZero + listHypercharge sigmaZero / 2
    ∧ listCharge sigmaMinus = listIsospinT3 sigmaMinus + listHypercharge sigmaMinus / 2
    ∧ compositeTwist 3 = -1

/-- The Sigma triplet row is checked from the existing flavor,
baryon-number, Gell-Mann--Nishijima, and spin-statistics infrastructure. -/
lemma sigmaBaryonTriplet_checked : HasSigmaBaryonTriplet :=
  ⟨sigmaTriplet_quarkContent.1,
    sigmaTriplet_quarkContent.2.1,
    sigmaTriplet_quarkContent.2.2,
    sigmaTriplet_contains_strange.1,
    sigmaTriplet_contains_strange.2.1,
    sigmaTriplet_contains_strange.2.2,
    sigmaPlus_charge_strangeness.1,
    sigmaZero_charge_strangeness.1,
    sigmaMinus_charge_strangeness.1,
    sigmaPlus_charge_strangeness.2,
    sigmaZero_charge_strangeness.2,
    sigmaMinus_charge_strangeness.2,
    sigmaTriplet_baryonNumber_one.1,
    sigmaTriplet_baryonNumber_one.2.1,
    sigmaTriplet_baryonNumber_one.2.2,
    sigmaTriplet_isospin_hypercharge.1,
    sigmaTriplet_isospin_hypercharge.2.1,
    sigmaTriplet_isospin_hypercharge.2.2.1,
    sigmaTriplet_isospin_hypercharge.2.2.2.1,
    sigmaTriplet_isospin_hypercharge.2.2.2.2.1,
    sigmaTriplet_isospin_hypercharge.2.2.2.2.2,
    gmn_strong_baryon sigmaPlus,
    gmn_strong_baryon sigmaZero,
    gmn_strong_baryon sigmaMinus,
    baryon_is_fermion⟩

/-- The Xi baryon doublet has quark contents `Ξ⁰ = uss`, `Ξ⁻ = dss`. -/
lemma xiDoublet_quarkContent :
    xiZero = [up, strange, strange] ∧ xiMinus = [down, strange, strange] :=
  ⟨rfl, rfl⟩

/-- Both Xi baryons contain strange quarks. -/
lemma xiDoublet_contains_strange : strange ∈ xiZero ∧ strange ∈ xiMinus := by
  simp [xiZero, xiMinus]

/-- Each Xi baryon has baryon number one. -/
lemma xiDoublet_baryonNumber_one :
    baryonNumber up + baryonNumber strange + baryonNumber strange = 1
      ∧ baryonNumber down + baryonNumber strange + baryonNumber strange = 1 :=
  ⟨baryon_baryonNumber up strange strange,
    baryon_baryonNumber down strange strange⟩

/-- The Xi doublet has `I₃=+1/2,-1/2` and common strong hypercharge `Y=-1`
because `B=1` and `S=-2`. -/
lemma xiDoublet_isospin_hypercharge :
    listIsospinT3 xiZero = 1 / 2 ∧ listIsospinT3 xiMinus = -1 / 2
      ∧ listHypercharge xiZero = -1 ∧ listHypercharge xiMinus = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [listIsospinT3, xiZero, isospinT3]
  · norm_num [listIsospinT3, xiMinus, isospinT3]
  · norm_num [listHypercharge, xiZero, hypercharge, baryonNumber, strangeness, charmness, bottomness,
      topness, quarkBaryonNumber]
  · norm_num [listHypercharge, xiMinus, hypercharge, baryonNumber, strangeness, charmness, bottomness,
      topness, quarkBaryonNumber]

/-- The Xi doublet has total isospin `T=1/2`, so its two projections are
admissible: `|I₃| ≤ 1/2`. -/
lemma xiDoublet_isospin_projection_allowed :
    |listIsospinT3 xiZero| ≤ (1 / 2 : ℚ)
      ∧ |listIsospinT3 xiMinus| ≤ (1 / 2 : ℚ) := by
  norm_num [listIsospinT3, xiZero, xiMinus, isospinT3]

/-- Capability predicate for the Xi baryon doublet:
`Ξ⁰ = uss`, `Ξ⁻ = dss`; charges `0,-1`; strangeness `-2`; baryon number
`1`; isodoublet values `I₃ = +1/2,-1/2`; common hypercharge `Y=-1`;
strong Gell-Mann--Nishijima; and three-quark fermion statistics. -/
def HasXiBaryonDoublet : Prop :=
  xiZero = [up, strange, strange]
    ∧ xiMinus = [down, strange, strange]
    ∧ strange ∈ xiZero ∧ strange ∈ xiMinus
    ∧ listCharge xiZero = 0 ∧ listCharge xiMinus = -1
    ∧ listStrangeness xiZero = -2 ∧ listStrangeness xiMinus = -2
    ∧ baryonNumber up + baryonNumber strange + baryonNumber strange = 1
    ∧ baryonNumber down + baryonNumber strange + baryonNumber strange = 1
    ∧ listIsospinT3 xiZero = 1 / 2 ∧ listIsospinT3 xiMinus = -1 / 2
    ∧ listHypercharge xiZero = -1 ∧ listHypercharge xiMinus = -1
    ∧ |listIsospinT3 xiZero| ≤ (1 / 2 : ℚ)
    ∧ |listIsospinT3 xiMinus| ≤ (1 / 2 : ℚ)
    ∧ listCharge xiZero = listIsospinT3 xiZero + listHypercharge xiZero / 2
    ∧ listCharge xiMinus = listIsospinT3 xiMinus + listHypercharge xiMinus / 2
    ∧ compositeTwist 3 = -1

/-- The Xi doublet row is checked from the existing flavor,
baryon-number, Gell-Mann--Nishijima, and spin-statistics infrastructure. -/
lemma xiBaryonDoublet_checked : HasXiBaryonDoublet :=
  ⟨xiDoublet_quarkContent.1,
    xiDoublet_quarkContent.2,
    xiDoublet_contains_strange.1,
    xiDoublet_contains_strange.2,
    xiZero_charge_strangeness.1,
    xiMinus_charge_strangeness.1,
    xiZero_charge_strangeness.2,
    xiMinus_charge_strangeness.2,
    xiDoublet_baryonNumber_one.1,
    xiDoublet_baryonNumber_one.2,
    xiDoublet_isospin_hypercharge.1,
    xiDoublet_isospin_hypercharge.2.1,
    xiDoublet_isospin_hypercharge.2.2.1,
    xiDoublet_isospin_hypercharge.2.2.2,
    xiDoublet_isospin_projection_allowed.1,
    xiDoublet_isospin_projection_allowed.2,
    gmn_strong_baryon xiZero,
    gmn_strong_baryon xiMinus,
    baryon_is_fermion⟩

/-- The Omega baryon row has quark content `Ω⁻ = sss`. -/
lemma omegaMinus_quarkContent : omegaMinus = [strange, strange, strange] :=
  rfl

/-- The Omega baryon is the all-strange baryon in this flavor model. -/
lemma omegaMinus_all_strange :
    omegaMinus = [strange, strange, strange] ∧ strange ∈ omegaMinus :=
  ⟨omegaMinus_quarkContent, by simp [omegaMinus]⟩

/-- The Omega baryon has baryon number one: `B(s)+B(s)+B(s)=1`. -/
lemma omegaMinus_baryonNumber_one :
    baryonNumber strange + baryonNumber strange + baryonNumber strange = 1 :=
  baryon_baryonNumber strange strange strange

/-- The Omega baryon is an isosinglet in the light `u,d` isospin and has
strong hypercharge `Y=-2` because `B=1` and `S=-3`. -/
lemma omegaMinus_isospin_hypercharge :
    listIsospinT3 omegaMinus = 0 ∧ listHypercharge omegaMinus = -2 := by
  refine ⟨?_, ?_⟩
  · norm_num [listIsospinT3, omegaMinus, isospinT3]
  · norm_num [listHypercharge, omegaMinus, hypercharge, baryonNumber, strangeness, charmness,
      bottomness, topness, quarkBaryonNumber]

/-- The Omega baryon charge is the strong Gell-Mann--Nishijima value
`Q = I₃ + Y/2 = -1`. -/
lemma omegaMinus_gellMannNishijima :
    listCharge omegaMinus = listIsospinT3 omegaMinus + listHypercharge omegaMinus / 2 :=
  gmn_strong_baryon omegaMinus

/-- Capability predicate for the Omega baryon:
`Ω⁻ = sss`; charge `-1`; strangeness `-3`; baryon number `1`; `I₃=0`;
hypercharge `Y=-2`; strong Gell-Mann--Nishijima; and three-quark fermion
statistics. -/
def HasOmegaBaryon : Prop :=
  omegaMinus = [strange, strange, strange]
    ∧ strange ∈ omegaMinus
    ∧ listCharge omegaMinus = -1
    ∧ listStrangeness omegaMinus = -3
    ∧ baryonNumber strange + baryonNumber strange + baryonNumber strange = 1
    ∧ listIsospinT3 omegaMinus = 0
    ∧ listHypercharge omegaMinus = -2
    ∧ listCharge omegaMinus = listIsospinT3 omegaMinus + listHypercharge omegaMinus / 2
    ∧ compositeTwist 3 = -1

/-- The Omega baryon row is checked from the existing flavor,
baryon-number, Gell-Mann--Nishijima, and spin-statistics infrastructure. -/
lemma omegaBaryon_checked : HasOmegaBaryon :=
  ⟨omegaMinus_all_strange.1,
    omegaMinus_all_strange.2,
    omegaMinus_charge_strangeness.1,
    omegaMinus_charge_strangeness.2,
    omegaMinus_baryonNumber_one,
    omegaMinus_isospin_hypercharge.1,
    omegaMinus_isospin_hypercharge.2,
    omegaMinus_gellMannNishijima,
    baryon_is_fermion⟩


/-- The nuclear-physics isospin doublet convention used in Sheikh et al.:
the neutron has `t_z=+1/2`, the proton has `t_z=-1/2`. This is the
opposite sign from the strong quark-isospin convention used above for
Gell-Mann--Nishijima. -/
inductive NucleonIsospinMember : Type
  | neutron
  | proton
  deriving DecidableEq

/-- The nuclear-physics projection `t_z` for the nucleon doublet:
`n ↦ +1/2`, `p ↦ -1/2`. -/
def nucleonNuclearIsospinT3 : NucleonIsospinMember → ℚ
  | NucleonIsospinMember.neutron => 1 / 2
  | NucleonIsospinMember.proton => -1 / 2

/-- Both proton and neutron are members of a `t=1/2` isospin doublet. -/
def nucleonTotalIsospin (_ : NucleonIsospinMember) : ℚ := 1 / 2

/-- For a nucleus with `N` neutrons and `Z` protons, the paper's convention is
`T_z = (N-Z)/2`. -/
def nuclearIsospinT3 (N Z : ℕ) : ℚ := ((N : ℚ) - (Z : ℚ)) / 2

/-- The nucleon doublet has total isospin `1/2` and projections
`t_z(n)=+1/2`, `t_z(p)=-1/2`. -/
lemma nucleon_isospin_doublet :
    nucleonTotalIsospin NucleonIsospinMember.neutron = 1 / 2
      ∧ nucleonNuclearIsospinT3 NucleonIsospinMember.neutron = 1 / 2
      ∧ nucleonTotalIsospin NucleonIsospinMember.proton = 1 / 2
      ∧ nucleonNuclearIsospinT3 NucleonIsospinMember.proton = -1 / 2 := by
  norm_num [nucleonTotalIsospin, nucleonNuclearIsospinT3]

/-- `T_z=(N-Z)/2` is exactly the additive sum of the nuclear-physics
nucleon projections. -/
lemma nuclearIsospinT3_eq_sum_nucleon_projections (N Z : ℕ) :
    nuclearIsospinT3 N Z =
      (N : ℚ) * nucleonNuclearIsospinT3 NucleonIsospinMember.neutron
        + (Z : ℚ) * nucleonNuclearIsospinT3 NucleonIsospinMember.proton := by
  unfold nuclearIsospinT3 nucleonNuclearIsospinT3
  ring

/-- The nuclear-physics `t_z` convention is the negative of the strong
quark-isospin projection already used for the `udd` neutron and `uud` proton. -/
lemma nucleon_nuclearT3_eq_neg_quark_isospin :
    nucleonNuclearIsospinT3 NucleonIsospinMember.neutron = -listIsospinT3 neutron
      ∧ nucleonNuclearIsospinT3 NucleonIsospinMember.proton = -listIsospinT3 proton := by
  norm_num [nucleonNuclearIsospinT3, listIsospinT3, neutron, proton, isospinT3]

/-- Combining the paper's `T_z=(N-Z)/2` convention with the repo's quark model:
the nuclear projection is the negative of the proton/neutron strong-isospin sum. -/
lemma nuclearIsospinT3_eq_neg_quark_isospin_sum (N Z : ℕ) :
    nuclearIsospinT3 N Z =
      -((N : ℚ) * listIsospinT3 neutron + (Z : ℚ) * listIsospinT3 proton) := by
  unfold nuclearIsospinT3
  norm_num [listIsospinT3, neutron, proton, isospinT3]
  ring

/-- Capability predicate for the nuclear-physics isospin convention from
Sheikh et al., Sec. 2, linked to the repo's existing quark-level isospin. -/
def HasNuclearIsospinConvention : Prop :=
  nucleonTotalIsospin NucleonIsospinMember.neutron = 1 / 2
    ∧ nucleonNuclearIsospinT3 NucleonIsospinMember.neutron = 1 / 2
    ∧ nucleonTotalIsospin NucleonIsospinMember.proton = 1 / 2
    ∧ nucleonNuclearIsospinT3 NucleonIsospinMember.proton = -1 / 2
    ∧ (∀ N Z : ℕ,
        nuclearIsospinT3 N Z =
          (N : ℚ) * nucleonNuclearIsospinT3 NucleonIsospinMember.neutron
            + (Z : ℚ) * nucleonNuclearIsospinT3 NucleonIsospinMember.proton)
    ∧ nucleonNuclearIsospinT3 NucleonIsospinMember.neutron = -listIsospinT3 neutron
    ∧ nucleonNuclearIsospinT3 NucleonIsospinMember.proton = -listIsospinT3 proton
    ∧ (∀ N Z : ℕ,
        nuclearIsospinT3 N Z =
          -((N : ℚ) * listIsospinT3 neutron + (Z : ℚ) * listIsospinT3 proton))

/-- The nuclear-physics isospin convention is checked and connected to the
existing proton/neutron quark-isospin assignments. -/
lemma nuclearIsospinConvention_checked : HasNuclearIsospinConvention :=
  ⟨nucleon_isospin_doublet.1,
    nucleon_isospin_doublet.2.1,
    nucleon_isospin_doublet.2.2.1,
    nucleon_isospin_doublet.2.2.2,
    nuclearIsospinT3_eq_sum_nucleon_projections,
    nucleon_nuclearT3_eq_neg_quark_isospin.1,
    nucleon_nuclearT3_eq_neg_quark_isospin.2,
    nuclearIsospinT3_eq_neg_quark_isospin_sum⟩

/-- Exchange parity of the light `u,d` pair inside an `uds` flavor wavefunction.
This is the extra isospin-wavefunction datum needed to distinguish `Σ⁰` from
`Λ` after their common valence content `uds` has been fixed. -/
inductive LightPairExchangeParity : Type
  | symmetric
  | antisymmetric
  deriving DecidableEq

/-- A compact carrier for an isospin multiplet state: valence quark content,
total isospin `T`, third component `T₃`, strong hypercharge `Y`, and light-pair
exchange parity. The paper's Sec. 2 convention is the same `SU(2)` structure as
spin, with the third projection labelling multiplet members. -/
structure BaryonIsospinMultipletState where
  valence : List QuarkFlavor
  totalIsospin : ℚ
  thirdComponent : ℚ
  strongHypercharge : ℚ
  lightPairParity : LightPairExchangeParity

/-- A projection is allowed inside a total-isospin multiplet when
`|T₃| ≤ T`, matching the paper's `T ≥ |T_z|` condition. -/
def isospinProjectionAllowed (ψ : BaryonIsospinMultipletState) : Prop :=
  |ψ.thirdComponent| ≤ ψ.totalIsospin

/-- `Σ⁺` is the `T=1`, `T₃=+1` member of the strange Sigma isotriplet. -/
def sigmaPlusIsospinState : BaryonIsospinMultipletState where
  valence := sigmaPlus
  totalIsospin := 1
  thirdComponent := 1
  strongHypercharge := 0
  lightPairParity := LightPairExchangeParity.symmetric

/-- `Σ⁰` is the `T=1`, `T₃=0` member of the strange Sigma isotriplet. -/
def sigmaZeroIsospinState : BaryonIsospinMultipletState where
  valence := sigmaZero
  totalIsospin := 1
  thirdComponent := 0
  strongHypercharge := 0
  lightPairParity := LightPairExchangeParity.symmetric

/-- `Σ⁻` is the `T=1`, `T₃=-1` member of the strange Sigma isotriplet. -/
def sigmaMinusIsospinState : BaryonIsospinMultipletState where
  valence := sigmaMinus
  totalIsospin := 1
  thirdComponent := -1
  strongHypercharge := 0
  lightPairParity := LightPairExchangeParity.symmetric

/-- `Λ` is the `T=0`, `T₃=0` strange isosinglet. It has the same valence
content as `Σ⁰`, but the light-pair isospin wavefunction is antisymmetric. -/
def lambdaIsospinState : BaryonIsospinMultipletState where
  valence := lambda
  totalIsospin := 0
  thirdComponent := 0
  strongHypercharge := 0
  lightPairParity := LightPairExchangeParity.antisymmetric

/-- The `Σ⁰` and `Λ` states have the same valence quark content in this model. -/
lemma sigmaZero_lambda_same_valence :
    sigmaZeroIsospinState.valence = lambdaIsospinState.valence := by
  rfl

/-- The isospin-wavefunction label separates `Σ⁰` from `Λ` even though the
valence list is the same. -/
lemma sigmaZeroIsospinState_ne_lambdaIsospinState :
    sigmaZeroIsospinState ≠ lambdaIsospinState := by
  intro h
  have hT := congrArg BaryonIsospinMultipletState.totalIsospin h
  norm_num [sigmaZeroIsospinState, lambdaIsospinState] at hT

/-- The Sigma triplet has common total isospin `T=1`. -/
lemma sigmaTriplet_totalIsospin_one :
    sigmaPlusIsospinState.totalIsospin = 1
      ∧ sigmaZeroIsospinState.totalIsospin = 1
      ∧ sigmaMinusIsospinState.totalIsospin = 1 := by
  norm_num [sigmaPlusIsospinState, sigmaZeroIsospinState, sigmaMinusIsospinState]

/-- The Sigma triplet has `T₃=+1,0,-1`. -/
lemma sigmaTriplet_thirdComponents :
    sigmaPlusIsospinState.thirdComponent = 1
      ∧ sigmaZeroIsospinState.thirdComponent = 0
      ∧ sigmaMinusIsospinState.thirdComponent = -1 := by
  norm_num [sigmaPlusIsospinState, sigmaZeroIsospinState, sigmaMinusIsospinState]

/-- The Lambda is an isosinglet: `T=0`, `T₃=0`. -/
lemma lambda_isosinglet :
    lambdaIsospinState.totalIsospin = 0 ∧ lambdaIsospinState.thirdComponent = 0 := by
  norm_num [lambdaIsospinState]

/-- The named Sigma/Lambda multiplet states obey the admissibility condition
`|T₃| ≤ T`. -/
lemma sigmaLambda_isospin_projection_allowed :
    isospinProjectionAllowed sigmaPlusIsospinState
      ∧ isospinProjectionAllowed sigmaZeroIsospinState
      ∧ isospinProjectionAllowed sigmaMinusIsospinState
      ∧ isospinProjectionAllowed lambdaIsospinState := by
  norm_num [isospinProjectionAllowed, sigmaPlusIsospinState, sigmaZeroIsospinState,
    sigmaMinusIsospinState, lambdaIsospinState]

/-- The Sigma triplet has `Y=0`, so Gell-Mann--Nishijima reduces to
`Q = T₃` on these three states. -/
lemma sigmaTriplet_charge_eq_isospinProjection :
    listCharge sigmaPlus = sigmaPlusIsospinState.thirdComponent
      ∧ listCharge sigmaZero = sigmaZeroIsospinState.thirdComponent
      ∧ listCharge sigmaMinus = sigmaMinusIsospinState.thirdComponent := by
  exact ⟨sigmaPlus_charge_strangeness.1,
    sigmaZero_charge_strangeness.1,
    sigmaMinus_charge_strangeness.1⟩

/-- Flavor amplitude for the `Σ⁰` light-pair isospin wavefunction:
`(|uds⟩ + |dus⟩)/sqrt 2`. -/
noncomputable def sigmaZeroIsospinAmplitude : List QuarkFlavor → ℝ
  | [up, down, strange] => 1 / Real.sqrt 2
  | [down, up, strange] => 1 / Real.sqrt 2
  | _ => 0

/-- Flavor amplitude for the `Λ` light-pair isospin wavefunction:
`(|uds⟩ - |dus⟩)/sqrt 2`. -/
noncomputable def lambdaIsospinAmplitude : List QuarkFlavor → ℝ
  | [up, down, strange] => 1 / Real.sqrt 2
  | [down, up, strange] => -(1 / Real.sqrt 2)
  | _ => 0

/-- `Σ⁰` is symmetric under exchange of the light `u,d` pair. -/
lemma sigmaZero_wavefunction_symmetric :
    sigmaZeroIsospinAmplitude [up, down, strange]
      = sigmaZeroIsospinAmplitude [down, up, strange] := by
  rfl

/-- `Λ` is antisymmetric under exchange of the light `u,d` pair. -/
lemma lambda_wavefunction_antisymmetric :
    lambdaIsospinAmplitude [up, down, strange]
      = -lambdaIsospinAmplitude [down, up, strange] := by
  norm_num [lambdaIsospinAmplitude]

/-- The two neutral strange baryon wavefunctions differ on the exchanged
`dus` basis component. -/
lemma sigmaZero_lambda_wavefunctions_differ_on_dus :
    sigmaZeroIsospinAmplitude [down, up, strange]
      = -lambdaIsospinAmplitude [down, up, strange] := by
  norm_num [sigmaZeroIsospinAmplitude, lambdaIsospinAmplitude]

/-- Capability predicate for the isospin-wavefunction layer that resolves the
`Σ⁰`/`Λ` valence-content degeneracy. It records the paper's `SU(2)`-multiplet
logic at the formal level used by the hadron flavor model: `T`, `T₃`, common
hypercharge, symmetric/antisymmetric wavefunctions, and the resulting
distinction of `Σ⁰` from `Λ`. -/
def HasSigmaLambdaIsospinWavefunctions : Prop :=
  sigmaPlusIsospinState.totalIsospin = 1
    ∧ sigmaZeroIsospinState.totalIsospin = 1
    ∧ sigmaMinusIsospinState.totalIsospin = 1
    ∧ sigmaPlusIsospinState.thirdComponent = 1
    ∧ sigmaZeroIsospinState.thirdComponent = 0
    ∧ sigmaMinusIsospinState.thirdComponent = -1
    ∧ lambdaIsospinState.totalIsospin = 0
    ∧ lambdaIsospinState.thirdComponent = 0
    ∧ isospinProjectionAllowed sigmaPlusIsospinState
    ∧ isospinProjectionAllowed sigmaZeroIsospinState
    ∧ isospinProjectionAllowed sigmaMinusIsospinState
    ∧ isospinProjectionAllowed lambdaIsospinState
    ∧ sigmaZeroIsospinState.valence = lambdaIsospinState.valence
    ∧ sigmaZeroIsospinState ≠ lambdaIsospinState
    ∧ listCharge sigmaPlus = sigmaPlusIsospinState.thirdComponent
    ∧ listCharge sigmaZero = sigmaZeroIsospinState.thirdComponent
    ∧ listCharge sigmaMinus = sigmaMinusIsospinState.thirdComponent
    ∧ sigmaZeroIsospinAmplitude [up, down, strange]
        = sigmaZeroIsospinAmplitude [down, up, strange]
    ∧ lambdaIsospinAmplitude [up, down, strange]
        = -lambdaIsospinAmplitude [down, up, strange]
    ∧ sigmaZeroIsospinAmplitude [down, up, strange]
        = -lambdaIsospinAmplitude [down, up, strange]

/-- The Sigma/Lambda isospin-wavefunction layer is checked from the existing
flavor assignments plus the explicit symmetric/antisymmetric `uds` amplitudes. -/
lemma sigmaLambdaIsospinWavefunctions_checked :
    HasSigmaLambdaIsospinWavefunctions :=
  ⟨sigmaTriplet_totalIsospin_one.1,
    sigmaTriplet_totalIsospin_one.2.1,
    sigmaTriplet_totalIsospin_one.2.2,
    sigmaTriplet_thirdComponents.1,
    sigmaTriplet_thirdComponents.2.1,
    sigmaTriplet_thirdComponents.2.2,
    lambda_isosinglet.1,
    lambda_isosinglet.2,
    sigmaLambda_isospin_projection_allowed.1,
    sigmaLambda_isospin_projection_allowed.2.1,
    sigmaLambda_isospin_projection_allowed.2.2.1,
    sigmaLambda_isospin_projection_allowed.2.2.2,
    sigmaZero_lambda_same_valence,
    sigmaZeroIsospinState_ne_lambdaIsospinState,
    sigmaTriplet_charge_eq_isospinProjection.1,
    sigmaTriplet_charge_eq_isospinProjection.2.1,
    sigmaTriplet_charge_eq_isospinProjection.2.2,
    sigmaZero_wavefunction_symmetric,
    lambda_wavefunction_antisymmetric,
    sigmaZero_lambda_wavefunctions_differ_on_dus⟩

/-- **[Λc⁺: charge `+1`, charm `+1`]** the charmed baryon `Λc⁺ = udc` — a heavy-flavor baryon. -/
lemma lambdaC_charge_charm :
    listCharge [up, down, charm] = 1 ∧ (([up, down, charm].map charmness).sum) = 1 := by
  refine ⟨?_, ?_⟩
  · norm_num [listCharge, electricCharge, windingNumber, windingCharge]
  · simp [charmness]


/-- **Electric charge of a meson** `q q̄'` — `Q(q) − Q(q')` (the antiquark carries `−Q`). -/
def mesonCharge (q qbar : QuarkFlavor) : ℚ := electricCharge q - electricCharge qbar
/-- **Strangeness of a meson** `q q̄'` — `S(q) − S(q')`. -/
def mesonStrangeness (q qbar : QuarkFlavor) : ℤ := strangeness q - strangeness qbar
/-- **Isospin `I₃` of a meson**. -/
def mesonIsospinT3 (q qbar : QuarkFlavor) : ℚ := isospinT3 q - isospinT3 qbar
/-- **Hypercharge of a meson**. -/
def mesonHypercharge (q qbar : QuarkFlavor) : ℚ := hypercharge q - hypercharge qbar
/-- **Baryon number of a meson** — `B(q) − B(q')`. -/
def mesonBaryonNumber (q qbar : QuarkFlavor) : ℚ := baryonNumber q - baryonNumber qbar

/-- A real-amplitude quark-antiquark flavor component. `antiquarkOf = q`
means the component contains the antiquark `qbar`. -/
structure MesonFlavorComponent where
  quark : QuarkFlavor
  antiquarkOf : QuarkFlavor
  amplitude : ℝ

/-- `π⁺ = u dbar`. -/
noncomputable def pionPlusFlavor : List MesonFlavorComponent :=
  [{ quark := up, antiquarkOf := down, amplitude := 1 }]

/-- `π⁰ = (u ubar - d dbar)/sqrt 2`. -/
noncomputable def pionZeroFlavor : List MesonFlavorComponent :=
  [{ quark := up, antiquarkOf := up, amplitude := 1 / Real.sqrt 2 },
    { quark := down, antiquarkOf := down, amplitude := -(1 / Real.sqrt 2) }]

/-- `π⁻ = d ubar`. -/
noncomputable def pionMinusFlavor : List MesonFlavorComponent :=
  [{ quark := down, antiquarkOf := up, amplitude := 1 }]

/-- `K⁺ = u sbar`. -/
noncomputable def kaonPlusFlavor : List MesonFlavorComponent :=
  [{ quark := up, antiquarkOf := strange, amplitude := 1 }]

/-- `K⁰ = d sbar`. -/
noncomputable def kaonZeroFlavor : List MesonFlavorComponent :=
  [{ quark := down, antiquarkOf := strange, amplitude := 1 }]

/-- **[Mesons have baryon number 0]** `1/3 − 1/3 = 0` — a quark and an antiquark cancel. -/
lemma mesonBaryonNumber_eq_zero (q qbar : QuarkFlavor) : mesonBaryonNumber q qbar = 0 := by
  simp [mesonBaryonNumber, baryonNumber]

/-- **[Strong Gell-Mann–Nishijima for a meson]** `Q = I₃ + Y/2` for a quark–antiquark composite — the per-quark
relation holds with the antiquark's negated quantum numbers. -/
lemma gmn_strong_meson (q qbar : QuarkFlavor) :
    mesonCharge q qbar = mesonIsospinT3 q qbar + mesonHypercharge q qbar / 2 := by
  simp only [mesonCharge, mesonIsospinT3, mesonHypercharge]
  rw [gmn_strong_quark q, gmn_strong_quark qbar]; ring

/-- **[π⁺ = u d̄: charge `+1`, strangeness `0`]**. -/
lemma pionPlus : mesonCharge up down = 1 ∧ mesonStrangeness up down = 0 := by
  refine ⟨?_, ?_⟩
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · simp [mesonStrangeness, strangeness]

/-- **[π⁰ neutral components]** both `u ubar` and `d dbar` have zero charge and
zero strangeness, so their normalized difference is neutral componentwise. -/
lemma pionZero_components_neutral :
    mesonCharge up up = 0 ∧ mesonCharge down down = 0
      ∧ mesonStrangeness up up = 0 ∧ mesonStrangeness down down = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · simp [mesonStrangeness, strangeness]
  · simp [mesonStrangeness, strangeness]

/-- **[π⁻ = d ubar: charge `-1`, strangeness `0`]**. -/
lemma pionMinus : mesonCharge down up = -1 ∧ mesonStrangeness down up = 0 := by
  refine ⟨?_, ?_⟩
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · simp [mesonStrangeness, strangeness]

/-- Capability predicate for the complete pion flavor triplet:
`π⁺ = u dbar`, `π⁰ = (u ubar - d dbar)/sqrt 2`, and `π⁻ = d ubar`,
with charges `+1,0,-1` and mesonic boson statistics. -/
def HasPionFlavorTriplet : Prop :=
  pionPlusFlavor =
      [{ quark := up, antiquarkOf := down, amplitude := 1 }]
    ∧ pionZeroFlavor =
      [{ quark := up, antiquarkOf := up, amplitude := 1 / Real.sqrt 2 },
        { quark := down, antiquarkOf := down, amplitude := -(1 / Real.sqrt 2) }]
    ∧ pionMinusFlavor =
      [{ quark := down, antiquarkOf := up, amplitude := 1 }]
    ∧ mesonCharge up down = 1
    ∧ mesonCharge up up = 0
    ∧ mesonCharge down down = 0
    ∧ mesonCharge down up = -1
    ∧ mesonBaryonNumber up down = 0
    ∧ mesonBaryonNumber up up = 0
    ∧ mesonBaryonNumber down down = 0
    ∧ mesonBaryonNumber down up = 0
    ∧ compositeTwist 2 = 1

/-- The full pion flavor triplet is checked from the existing quark-flavor,
meson-charge, baryon-number, and spin-statistics infrastructure. -/
lemma pionFlavorTriplet_checked : HasPionFlavorTriplet :=
  ⟨rfl,
    rfl,
    rfl,
    pionPlus.1,
    pionZero_components_neutral.1,
    pionZero_components_neutral.2.1,
    pionMinus.1,
    mesonBaryonNumber_eq_zero up down,
    mesonBaryonNumber_eq_zero up up,
    mesonBaryonNumber_eq_zero down down,
    mesonBaryonNumber_eq_zero down up,
    meson_is_boson⟩

/-- **[K⁺ = u s̄: charge `+1`, strangeness `+1`]** — the anti-strange quark gives the kaon `S = +1`. -/
lemma kaonPlus : mesonCharge up strange = 1 ∧ mesonStrangeness up strange = 1 := by
  refine ⟨?_, ?_⟩
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · simp [mesonStrangeness, strangeness]

/-- **[K⁰ = d s̄: charge `0`, strangeness `+1`]**. -/
lemma kaonZero : mesonCharge down strange = 0 ∧ mesonStrangeness down strange = 1 := by
  refine ⟨?_, ?_⟩
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · simp [mesonStrangeness, strangeness]

/-- Capability predicate for the kaon flavor doublet:
`K⁺ = u sbar` and `K⁰ = d sbar`, with charges `+1,0`, strangeness `+1`,
zero baryon number, and mesonic boson statistics. The row's "strange" content
is represented precisely as `antiquarkOf := strange`. -/
def HasKaonFlavorDoublet : Prop :=
  kaonPlusFlavor =
      [{ quark := up, antiquarkOf := strange, amplitude := 1 }]
    ∧ kaonZeroFlavor =
      [{ quark := down, antiquarkOf := strange, amplitude := 1 }]
    ∧ mesonCharge up strange = 1
    ∧ mesonCharge down strange = 0
    ∧ mesonStrangeness up strange = 1
    ∧ mesonStrangeness down strange = 1
    ∧ mesonBaryonNumber up strange = 0
    ∧ mesonBaryonNumber down strange = 0
    ∧ compositeTwist 2 = 1

/-- The kaon doublet is checked from the existing quark-flavor,
meson-charge/strangeness, baryon-number, and spin-statistics infrastructure. -/
lemma kaonFlavorDoublet_checked : HasKaonFlavorDoublet :=
  ⟨rfl,
    rfl,
    kaonPlus.1,
    kaonZero.1,
    kaonPlus.2,
    kaonZero.2,
    mesonBaryonNumber_eq_zero up strange,
    mesonBaryonNumber_eq_zero down strange,
    meson_is_boson⟩

/-- **[D⁺ = c d̄: charge `+1`, charm `+1`]** — a charmed meson (the heavy-flavor sector). -/
lemma dPlus : mesonCharge charm down = 1 ∧ charmness charm - charmness down = 1 := by
  refine ⟨?_, ?_⟩
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · simp [charmness]

/-- **Charm of a meson** `q q̄'` — `C(q) - C(q')`. -/
def mesonCharmness (q qbar : QuarkFlavor) : ℤ := charmness q - charmness qbar

/-- **Bottomness of a meson** `q q̄'` — `B'(q) - B'(q')`. -/
def mesonBottomness (q qbar : QuarkFlavor) : ℤ := bottomness q - bottomness qbar

/-- Total charm of a baryonic valence list. -/
def listCharmness (qs : List QuarkFlavor) : ℤ := (qs.map charmness).sum

/-- Total bottomness of a baryonic valence list. -/
def listBottomness (qs : List QuarkFlavor) : ℤ := (qs.map bottomness).sum

/-- `D⁺ = c dbar`. -/
noncomputable def dPlusFlavor : List MesonFlavorComponent :=
  [{ quark := charm, antiquarkOf := down, amplitude := 1 }]

/-- `J/ψ = c cbar`, the hidden-charm charmonium valence model. -/
noncomputable def charmoniumJpsiFlavor : List MesonFlavorComponent :=
  [{ quark := charm, antiquarkOf := charm, amplitude := 1 }]

/-- `Υ = b bbar`, the hidden-bottom bottomonium valence model. -/
noncomputable def bottomoniumUpsilonFlavor : List MesonFlavorComponent :=
  [{ quark := bottom, antiquarkOf := bottom, amplitude := 1 }]

/-- **[Charmonium `J/ψ = c cbar`]** is neutral, has zero net charm, zero baryon
number, and mesonic boson statistics. It still records hidden charm through the
explicit `c cbar` flavor row. -/
lemma charmoniumJpsi_quantum_numbers :
    mesonCharge charm charm = 0
      ∧ mesonCharmness charm charm = 0
      ∧ mesonBaryonNumber charm charm = 0
      ∧ compositeTwist 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · simp [mesonCharmness]
  · exact mesonBaryonNumber_eq_zero charm charm
  · exact meson_is_boson

/-- **[Bottomonium `Υ = b bbar`]** is neutral, has zero net bottomness, zero
baryon number, and mesonic boson statistics. It records hidden bottom through
the explicit `b bbar` flavor row. -/
lemma bottomoniumUpsilon_quantum_numbers :
    mesonCharge bottom bottom = 0
      ∧ mesonBottomness bottom bottom = 0
      ∧ mesonBaryonNumber bottom bottom = 0
      ∧ compositeTwist 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [mesonCharge, electricCharge, windingNumber, windingCharge]
  · simp [mesonBottomness]
  · exact mesonBaryonNumber_eq_zero bottom bottom
  · exact meson_is_boson


/-- Named hadrons currently covered by the finite valence-flavor table. -/
inductive NamedHadron : Type
  | proton | neutron
  | lambda | sigmaPlus | sigmaZero | sigmaMinus | xiZero | xiMinus | omegaMinus | lambdaCPlus
  | pionPlus | pionZero | pionMinus | kaonPlus | kaonZero | dPlus
  | charmoniumJpsi | bottomoniumUpsilon
  deriving DecidableEq

/-- A named hadron is either a baryon valence list or a meson flavor-component
list. This is the data-driven carrier: computations below consume this table
uniformly instead of writing one theorem per particle by hand. -/
inductive HadronValenceModel : Type
  | baryon (qs : List QuarkFlavor)
  | meson (components : List MesonFlavorComponent)

namespace MesonFlavorComponent

/-- Electric charge computed from a quark-antiquark component. -/
def charge (c : MesonFlavorComponent) : ℚ := mesonCharge c.quark c.antiquarkOf

/-- Strangeness computed from a quark-antiquark component. -/
def strangeness (c : MesonFlavorComponent) : ℤ := mesonStrangeness c.quark c.antiquarkOf

/-- Charm computed from a quark-antiquark component. -/
def charmness (c : MesonFlavorComponent) : ℤ := mesonCharmness c.quark c.antiquarkOf

/-- Bottomness computed from a quark-antiquark component. -/
def bottomness (c : MesonFlavorComponent) : ℤ := mesonBottomness c.quark c.antiquarkOf

/-- Baryon number computed from a quark-antiquark component. -/
def baryonNumber (c : MesonFlavorComponent) : ℚ := mesonBaryonNumber c.quark c.antiquarkOf

end MesonFlavorComponent

namespace HadronValenceModel

/-- Computed electric charge of a valence model. For a mixed meson such as
`π⁰`, the first component gives the common quantum numbers; coherence is
checked separately by `namedHadronMesonChargeCoherent`. -/
def electricCharge : HadronValenceModel → ℚ
  | baryon qs => listCharge qs
  | meson [] => 0
  | meson (c :: _) => c.charge

/-- Computed baryon number of a valence model. -/
def baryonNumber : HadronValenceModel → ℚ
  | baryon qs => (qs.map QuarkFlavor.baryonNumber).sum
  | meson [] => 0
  | meson (c :: _) => c.baryonNumber

/-- Computed strangeness of a valence model. -/
def strangeness : HadronValenceModel → ℤ
  | baryon qs => listStrangeness qs
  | meson [] => 0
  | meson (c :: _) => c.strangeness

/-- Computed charm of a valence model. -/
def charmness : HadronValenceModel → ℤ
  | baryon qs => listCharmness qs
  | meson [] => 0
  | meson (c :: _) => c.charmness

/-- Computed bottomness of a valence model. -/
def bottomness : HadronValenceModel → ℤ
  | baryon qs => listBottomness qs
  | meson [] => 0
  | meson (c :: _) => c.bottomness

end HadronValenceModel

/-- The data table for the named hadrons. -/
noncomputable def namedHadronValence : NamedHadron → HadronValenceModel
  | NamedHadron.proton => .baryon proton
  | NamedHadron.neutron => .baryon neutron
  | NamedHadron.lambda => .baryon lambda
  | NamedHadron.sigmaPlus => .baryon sigmaPlus
  | NamedHadron.sigmaZero => .baryon sigmaZero
  | NamedHadron.sigmaMinus => .baryon sigmaMinus
  | NamedHadron.xiZero => .baryon xiZero
  | NamedHadron.xiMinus => .baryon xiMinus
  | NamedHadron.omegaMinus => .baryon omegaMinus
  | NamedHadron.lambdaCPlus => .baryon [up, down, charm]
  | NamedHadron.pionPlus => .meson pionPlusFlavor
  | NamedHadron.pionZero => .meson pionZeroFlavor
  | NamedHadron.pionMinus => .meson pionMinusFlavor
  | NamedHadron.kaonPlus => .meson kaonPlusFlavor
  | NamedHadron.kaonZero => .meson kaonZeroFlavor
  | NamedHadron.dPlus => .meson dPlusFlavor
  | NamedHadron.charmoniumJpsi => .meson charmoniumJpsiFlavor
  | NamedHadron.bottomoniumUpsilon => .meson bottomoniumUpsilonFlavor

/-- Computed charge of a named hadron from the data table. -/
noncomputable def namedHadronCharge (h : NamedHadron) : ℚ :=
  (namedHadronValence h).electricCharge

/-- Computed baryon number of a named hadron from the data table. -/
noncomputable def namedHadronBaryonNumber (h : NamedHadron) : ℚ :=
  (namedHadronValence h).baryonNumber

/-- Computed strangeness of a named hadron from the data table. -/
noncomputable def namedHadronStrangeness (h : NamedHadron) : ℤ :=
  (namedHadronValence h).strangeness

/-- Computed charm of a named hadron from the data table. -/
noncomputable def namedHadronCharmness (h : NamedHadron) : ℤ :=
  (namedHadronValence h).charmness

/-- Computed bottomness of a named hadron from the data table. -/
noncomputable def namedHadronBottomness (h : NamedHadron) : ℤ :=
  (namedHadronValence h).bottomness

/-- Expected electric-charge row for the named-hadron table. -/
def namedHadronExpectedCharge : NamedHadron → ℚ
  | NamedHadron.proton => 1
  | NamedHadron.neutron => 0
  | NamedHadron.lambda => 0
  | NamedHadron.sigmaPlus => 1
  | NamedHadron.sigmaZero => 0
  | NamedHadron.sigmaMinus => -1
  | NamedHadron.xiZero => 0
  | NamedHadron.xiMinus => -1
  | NamedHadron.omegaMinus => -1
  | NamedHadron.lambdaCPlus => 1
  | NamedHadron.pionPlus => 1
  | NamedHadron.pionZero => 0
  | NamedHadron.pionMinus => -1
  | NamedHadron.kaonPlus => 1
  | NamedHadron.kaonZero => 0
  | NamedHadron.dPlus => 1
  | NamedHadron.charmoniumJpsi => 0
  | NamedHadron.bottomoniumUpsilon => 0

/-- Expected baryon-number row for the named-hadron table. -/
def namedHadronExpectedBaryonNumber : NamedHadron → ℚ
  | NamedHadron.proton | NamedHadron.neutron | NamedHadron.lambda
  | NamedHadron.sigmaPlus | NamedHadron.sigmaZero | NamedHadron.sigmaMinus
  | NamedHadron.xiZero | NamedHadron.xiMinus | NamedHadron.omegaMinus
  | NamedHadron.lambdaCPlus => 1
  | _ => 0

/-- Expected strangeness row for the named-hadron table. -/
def namedHadronExpectedStrangeness : NamedHadron → ℤ
  | NamedHadron.lambda | NamedHadron.sigmaPlus | NamedHadron.sigmaZero | NamedHadron.sigmaMinus => -1
  | NamedHadron.xiZero | NamedHadron.xiMinus => -2
  | NamedHadron.omegaMinus => -3
  | NamedHadron.kaonPlus | NamedHadron.kaonZero => 1
  | _ => 0

/-- Expected charm row for the named-hadron table. Hidden-charm `J/ψ = c cbar`
has zero net charm. -/
def namedHadronExpectedCharmness : NamedHadron → ℤ
  | NamedHadron.lambdaCPlus | NamedHadron.dPlus => 1
  | _ => 0

/-- Expected bottomness row for the named-hadron table. Hidden-bottom `Υ = b bbar`
has zero net bottomness. -/
def namedHadronExpectedBottomness : NamedHadron → ℤ := fun _ => 0

/-- The data table computes the electric charges of all named hadrons. -/
lemma namedHadronCharge_eq_expected (h : NamedHadron) :
    namedHadronCharge h = namedHadronExpectedCharge h := by
  cases h <;>
    norm_num [namedHadronCharge, namedHadronExpectedCharge, namedHadronValence,
      HadronValenceModel.electricCharge, MesonFlavorComponent.charge, listCharge,
      proton, neutron, lambda, sigmaPlus, sigmaZero, sigmaMinus, xiZero, xiMinus,
      omegaMinus, pionPlusFlavor, pionZeroFlavor, pionMinusFlavor, kaonPlusFlavor,
      kaonZeroFlavor, dPlusFlavor, charmoniumJpsiFlavor, bottomoniumUpsilonFlavor,
      mesonCharge, electricCharge, windingNumber, windingCharge]

/-- The data table computes the baryon numbers of all named hadrons. -/
lemma namedHadronBaryonNumber_eq_expected (h : NamedHadron) :
    namedHadronBaryonNumber h = namedHadronExpectedBaryonNumber h := by
  cases h <;>
    norm_num [namedHadronBaryonNumber, namedHadronExpectedBaryonNumber, namedHadronValence,
      HadronValenceModel.baryonNumber, MesonFlavorComponent.baryonNumber, mesonBaryonNumber,
      baryonNumber, quarkBaryonNumber, proton, neutron, lambda, sigmaPlus, sigmaZero,
      sigmaMinus, xiZero, xiMinus, omegaMinus, pionPlusFlavor, pionZeroFlavor, pionMinusFlavor,
      kaonPlusFlavor, kaonZeroFlavor, dPlusFlavor, charmoniumJpsiFlavor, bottomoniumUpsilonFlavor]

/-- The data table computes the strangeness of all named hadrons. -/
lemma namedHadronStrangeness_eq_expected (h : NamedHadron) :
    namedHadronStrangeness h = namedHadronExpectedStrangeness h := by
  cases h <;>
    norm_num [namedHadronStrangeness, namedHadronExpectedStrangeness, namedHadronValence,
      HadronValenceModel.strangeness, MesonFlavorComponent.strangeness, listStrangeness,
      mesonStrangeness, strangeness, proton, neutron, lambda, sigmaPlus, sigmaZero,
      sigmaMinus, xiZero, xiMinus, omegaMinus, pionPlusFlavor, pionZeroFlavor, pionMinusFlavor,
      kaonPlusFlavor, kaonZeroFlavor, dPlusFlavor, charmoniumJpsiFlavor, bottomoniumUpsilonFlavor]

/-- The data table computes the net charm of all named hadrons. -/
lemma namedHadronCharmness_eq_expected (h : NamedHadron) :
    namedHadronCharmness h = namedHadronExpectedCharmness h := by
  cases h <;>
    norm_num [namedHadronCharmness, namedHadronExpectedCharmness, namedHadronValence,
      HadronValenceModel.charmness, MesonFlavorComponent.charmness, listCharmness,
      mesonCharmness, charmness, proton, neutron, lambda, sigmaPlus, sigmaZero,
      sigmaMinus, xiZero, xiMinus, omegaMinus, pionPlusFlavor, pionZeroFlavor, pionMinusFlavor,
      kaonPlusFlavor, kaonZeroFlavor, dPlusFlavor, charmoniumJpsiFlavor, bottomoniumUpsilonFlavor]

/-- The data table computes the net bottomness of all named hadrons. -/
lemma namedHadronBottomness_eq_expected (h : NamedHadron) :
    namedHadronBottomness h = namedHadronExpectedBottomness h := by
  cases h <;>
    norm_num [namedHadronBottomness, namedHadronExpectedBottomness, namedHadronValence,
      HadronValenceModel.bottomness, MesonFlavorComponent.bottomness, listBottomness,
      mesonBottomness, bottomness, proton, neutron, lambda, sigmaPlus, sigmaZero,
      sigmaMinus, xiZero, xiMinus, omegaMinus, pionPlusFlavor, pionZeroFlavor, pionMinusFlavor,
      kaonPlusFlavor, kaonZeroFlavor, dPlusFlavor, charmoniumJpsiFlavor, bottomoniumUpsilonFlavor]

/-- A meson flavor row is charge-coherent when every listed component carries
the same charge as the row's computed charge. This is the data-driven check
that makes mixed rows such as `π⁰` honest. -/
def namedHadronMesonChargeCoherent (h : NamedHadron) : Prop :=
  ∀ components, namedHadronValence h = HadronValenceModel.meson components →
    ∀ c ∈ components, c.charge = namedHadronCharge h

/-- Every named meson row in the data table is charge-coherent componentwise. -/
lemma namedHadronMesonChargeCoherent_checked (h : NamedHadron) :
    namedHadronMesonChargeCoherent h := by
  cases h <;>
    simp [namedHadronMesonChargeCoherent, namedHadronValence, namedHadronCharge,
      HadronValenceModel.electricCharge, MesonFlavorComponent.charge, pionPlusFlavor,
      pionZeroFlavor, pionMinusFlavor, kaonPlusFlavor, kaonZeroFlavor, dPlusFlavor,
      charmoniumJpsiFlavor, bottomoniumUpsilonFlavor, mesonCharge, electricCharge,
      windingNumber, windingCharge]

/-- Capability predicate for the heavy quarkonium rows: `J/ψ = c cbar` and
`Υ = b bbar` are neutral hidden-flavor mesons with zero baryon number and boson
statistics. -/
def HasHeavyQuarkoniumFlavorModels : Prop :=
  charmoniumJpsiFlavor =
      [{ quark := charm, antiquarkOf := charm, amplitude := 1 }]
    ∧ bottomoniumUpsilonFlavor =
      [{ quark := bottom, antiquarkOf := bottom, amplitude := 1 }]
    ∧ mesonCharge charm charm = 0
    ∧ mesonCharmness charm charm = 0
    ∧ mesonBaryonNumber charm charm = 0
    ∧ mesonCharge bottom bottom = 0
    ∧ mesonBottomness bottom bottom = 0
    ∧ mesonBaryonNumber bottom bottom = 0
    ∧ compositeTwist 2 = 1

/-- Heavy quarkonium rows are checked from the same quark-antiquark machinery as
the pion and kaon rows. -/
lemma heavyQuarkoniumFlavorModels_checked : HasHeavyQuarkoniumFlavorModels :=
  ⟨rfl,
    rfl,
    charmoniumJpsi_quantum_numbers.1,
    charmoniumJpsi_quantum_numbers.2.1,
    charmoniumJpsi_quantum_numbers.2.2.1,
    bottomoniumUpsilon_quantum_numbers.1,
    bottomoniumUpsilon_quantum_numbers.2.1,
    bottomoniumUpsilon_quantum_numbers.2.2.1,
    meson_is_boson⟩

/-- Capability predicate for the whole data-driven particle table. It covers the
already-modelled nucleons, hyperons, pion/kaon rows, open charm `D⁺`, and the
new hidden-flavor charmonium/bottomonium rows. -/
def HasDataDrivenNamedHadronTable : Prop :=
  (∀ h : NamedHadron, namedHadronCharge h = namedHadronExpectedCharge h)
    ∧ (∀ h : NamedHadron, namedHadronBaryonNumber h = namedHadronExpectedBaryonNumber h)
    ∧ (∀ h : NamedHadron, namedHadronStrangeness h = namedHadronExpectedStrangeness h)
    ∧ (∀ h : NamedHadron, namedHadronCharmness h = namedHadronExpectedCharmness h)
    ∧ (∀ h : NamedHadron, namedHadronBottomness h = namedHadronExpectedBottomness h)
    ∧ (∀ h : NamedHadron, namedHadronMesonChargeCoherent h)
    ∧ HasHeavyQuarkoniumFlavorModels

/-- The named particle table is checked by computation from valence quark data. -/
lemma dataDrivenNamedHadronTable_checked : HasDataDrivenNamedHadronTable :=
  ⟨namedHadronCharge_eq_expected,
    namedHadronBaryonNumber_eq_expected,
    namedHadronStrangeness_eq_expected,
    namedHadronCharmness_eq_expected,
    namedHadronBottomness_eq_expected,
    namedHadronMesonChargeCoherent_checked,
    heavyQuarkoniumFlavorModels_checked⟩


/-- Additive `(Q,B,L)` quantum numbers, using the repository's shared
conservation-law record. -/
abbrev AdditiveQuantumNumbers :=
  Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.QuantumNumbers

/-- Baryon/meson statistics class derived from the valence carrier. -/
inductive NamedHadronStatistics : Type
  | fermion | boson
  deriving DecidableEq

/-- The number of constituent fermion slots in a valence model. Baryons use
their quark-list length; a nonempty meson row is a superposition of two-slot
`q qbar` components, so mixed rows such as `π⁰` still have constituent count
`2`. -/
def HadronValenceModel.constituentCount : HadronValenceModel → ℕ
  | HadronValenceModel.baryon qs => qs.length
  | HadronValenceModel.meson [] => 0
  | HadronValenceModel.meson (_ :: _) => 2

/-- Statistics class derived from the valence carrier. -/
def HadronValenceModel.statistics : HadronValenceModel → NamedHadronStatistics
  | HadronValenceModel.baryon _ => NamedHadronStatistics.fermion
  | HadronValenceModel.meson _ => NamedHadronStatistics.boson

/-- Expected constituent-count row for the named-hadron table. -/
def namedHadronExpectedConstituentCount : NamedHadron → ℕ
  | NamedHadron.proton | NamedHadron.neutron | NamedHadron.lambda
  | NamedHadron.sigmaPlus | NamedHadron.sigmaZero | NamedHadron.sigmaMinus
  | NamedHadron.xiZero | NamedHadron.xiMinus | NamedHadron.omegaMinus
  | NamedHadron.lambdaCPlus => 3
  | _ => 2

/-- Constituent count computed from the generated valence model. -/
noncomputable def namedHadronConstituentCount (h : NamedHadron) : ℕ :=
  (namedHadronValence h).constituentCount

/-- The data table computes the constituent count of every named hadron. -/
lemma namedHadronConstituentCount_eq_expected (h : NamedHadron) :
    namedHadronConstituentCount h = namedHadronExpectedConstituentCount h := by
  cases h <;>
    simp [namedHadronConstituentCount, namedHadronExpectedConstituentCount,
      namedHadronValence, HadronValenceModel.constituentCount, proton, neutron, lambda,
      sigmaPlus, sigmaZero, sigmaMinus, xiZero, xiMinus, omegaMinus, pionPlusFlavor,
      pionZeroFlavor, pionMinusFlavor, kaonPlusFlavor, kaonZeroFlavor, dPlusFlavor,
      charmoniumJpsiFlavor, bottomoniumUpsilonFlavor]

/-- Statistics class computed from the generated valence model. -/
noncomputable def namedHadronStatistics (h : NamedHadron) : NamedHadronStatistics :=
  (namedHadronValence h).statistics

/-- Expected statistics row for the named-hadron table. -/
def namedHadronExpectedStatistics : NamedHadron → NamedHadronStatistics
  | NamedHadron.proton | NamedHadron.neutron | NamedHadron.lambda
  | NamedHadron.sigmaPlus | NamedHadron.sigmaZero | NamedHadron.sigmaMinus
  | NamedHadron.xiZero | NamedHadron.xiMinus | NamedHadron.omegaMinus
  | NamedHadron.lambdaCPlus => NamedHadronStatistics.fermion
  | _ => NamedHadronStatistics.boson

/-- The data table computes the statistics class of every named hadron. -/
lemma namedHadronStatistics_eq_expected (h : NamedHadron) :
    namedHadronStatistics h = namedHadronExpectedStatistics h := by
  cases h <;>
    simp [namedHadronStatistics, namedHadronExpectedStatistics, namedHadronValence,
      HadronValenceModel.statistics]

/-- Exchange phase computed from the generated constituent count. -/
noncomputable def namedHadronExchangePhase (h : NamedHadron) : ℂ :=
  compositeTwist (namedHadronConstituentCount h)

/-- Expected exchange phase row: baryons are fermionic and mesons are bosonic. -/
noncomputable def namedHadronExpectedExchangePhase : NamedHadron → ℂ
  | NamedHadron.proton | NamedHadron.neutron | NamedHadron.lambda
  | NamedHadron.sigmaPlus | NamedHadron.sigmaZero | NamedHadron.sigmaMinus
  | NamedHadron.xiZero | NamedHadron.xiMinus | NamedHadron.omegaMinus
  | NamedHadron.lambdaCPlus => -1
  | _ => 1

/-- The generated particle model recovers the exchange phase for every named
hadron from its computed constituent count. -/
lemma namedHadronExchangePhase_eq_expected (h : NamedHadron) :
    namedHadronExchangePhase h = namedHadronExpectedExchangePhase h := by
  cases h <;>
    simp [namedHadronExchangePhase, namedHadronExpectedExchangePhase,
      namedHadronConstituentCount, namedHadronValence, HadronValenceModel.constituentCount,
      proton, neutron, lambda, sigmaPlus, sigmaZero, sigmaMinus, xiZero, xiMinus,
      omegaMinus, pionPlusFlavor, pionZeroFlavor, pionMinusFlavor, kaonPlusFlavor,
      kaonZeroFlavor, dPlusFlavor, charmoniumJpsiFlavor, bottomoniumUpsilonFlavor,
      baryon_is_fermion, meson_is_boson]

/-- Additive quantum numbers generated from the named-hadron valence table. All
named hadrons here are hadrons, so lepton number is zero. -/
noncomputable def namedHadronQuantumNumbers (h : NamedHadron) : AdditiveQuantumNumbers :=
  { electric := namedHadronCharge h
    baryon := namedHadronBaryonNumber h
    lepton := 0 }

/-- The generated additive quantum-number model has the expected electric
charge. -/
lemma namedHadronQuantumNumbers_electric_eq_expected (h : NamedHadron) :
    (namedHadronQuantumNumbers h).electric = namedHadronExpectedCharge h := by
  simpa [namedHadronQuantumNumbers] using namedHadronCharge_eq_expected h

/-- The generated additive quantum-number model has the expected baryon number. -/
lemma namedHadronQuantumNumbers_baryon_eq_expected (h : NamedHadron) :
    (namedHadronQuantumNumbers h).baryon = namedHadronExpectedBaryonNumber h := by
  simpa [namedHadronQuantumNumbers] using namedHadronBaryonNumber_eq_expected h

/-- The generated additive quantum-number model has zero lepton number. -/
lemma namedHadronQuantumNumbers_lepton_eq_zero (h : NamedHadron) :
    (namedHadronQuantumNumbers h).lepton = 0 := rfl

/-- A reusable generated particle model for a named hadron. The fields are data;
the theorems below prove that this data is not an unchecked row, but the result
of the valence computation. -/
structure NamedHadronParticleModel where
  name : NamedHadron
  valence : HadronValenceModel
  quantumNumbers : AdditiveQuantumNumbers
  constituentCount : ℕ
  statistics : NamedHadronStatistics
  exchangePhase : ℂ

/-- Generic constructor: every named hadron is modelled by applying the same
data-driven construction to its table row. -/
noncomputable def namedHadronParticleModel (h : NamedHadron) : NamedHadronParticleModel where
  name := h
  valence := namedHadronValence h
  quantumNumbers := namedHadronQuantumNumbers h
  constituentCount := namedHadronConstituentCount h
  statistics := namedHadronStatistics h
  exchangePhase := namedHadronExchangePhase h

/-- The model's electric charge agrees with the checked computed table. -/
lemma namedHadronParticleModel_electric_eq_expected (h : NamedHadron) :
    (namedHadronParticleModel h).quantumNumbers.electric = namedHadronExpectedCharge h := by
  simpa [namedHadronParticleModel] using namedHadronQuantumNumbers_electric_eq_expected h

/-- The model's baryon number agrees with the checked computed table. -/
lemma namedHadronParticleModel_baryon_eq_expected (h : NamedHadron) :
    (namedHadronParticleModel h).quantumNumbers.baryon = namedHadronExpectedBaryonNumber h := by
  simpa [namedHadronParticleModel] using namedHadronQuantumNumbers_baryon_eq_expected h

/-- The model's lepton number is zero for every hadron row. -/
lemma namedHadronParticleModel_lepton_eq_zero (h : NamedHadron) :
    (namedHadronParticleModel h).quantumNumbers.lepton = 0 := by
  simp [namedHadronParticleModel, namedHadronQuantumNumbers]

/-- The model's constituent count agrees with the checked computed table. -/
lemma namedHadronParticleModel_constituentCount_eq_expected (h : NamedHadron) :
    (namedHadronParticleModel h).constituentCount =
      namedHadronExpectedConstituentCount h := by
  simpa [namedHadronParticleModel] using namedHadronConstituentCount_eq_expected h

/-- The model's statistics class agrees with the checked computed table. -/
lemma namedHadronParticleModel_statistics_eq_expected (h : NamedHadron) :
    (namedHadronParticleModel h).statistics = namedHadronExpectedStatistics h := by
  simpa [namedHadronParticleModel] using namedHadronStatistics_eq_expected h

/-- The model's exchange phase agrees with the computed fermion/boson phase. -/
lemma namedHadronParticleModel_exchangePhase_eq_expected (h : NamedHadron) :
    (namedHadronParticleModel h).exchangePhase =
      namedHadronExpectedExchangePhase h := by
  simpa [namedHadronParticleModel] using namedHadronExchangePhase_eq_expected h

/-- Proton particle model, generated from the common named-hadron constructor. -/
noncomputable def protonParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.proton

/-- Neutron particle model, generated from the common named-hadron constructor. -/
noncomputable def neutronParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.neutron

/-- Lambda baryon particle model, generated from the common constructor. -/
noncomputable def lambdaParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.lambda

/-- Sigma-plus baryon particle model, generated from the common constructor. -/
noncomputable def sigmaPlusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.sigmaPlus

/-- Sigma-zero baryon particle model, generated from the common constructor. -/
noncomputable def sigmaZeroParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.sigmaZero

/-- Sigma-minus baryon particle model, generated from the common constructor. -/
noncomputable def sigmaMinusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.sigmaMinus

/-- Xi-zero baryon particle model, generated from the common constructor. -/
noncomputable def xiZeroParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.xiZero

/-- Xi-minus baryon particle model, generated from the common constructor. -/
noncomputable def xiMinusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.xiMinus

/-- Omega-minus baryon particle model, generated from the common constructor. -/
noncomputable def omegaMinusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.omegaMinus

/-- Charmed Lambda particle model, generated from the common constructor. -/
noncomputable def lambdaCPlusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.lambdaCPlus

/-- Pion-plus particle model, generated from the common constructor. -/
noncomputable def pionPlusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.pionPlus

/-- Pion-zero particle model, generated from the common constructor. -/
noncomputable def pionZeroParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.pionZero

/-- Pion-minus particle model, generated from the common constructor. -/
noncomputable def pionMinusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.pionMinus

/-- Kaon-plus particle model, generated from the common constructor. -/
noncomputable def kaonPlusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.kaonPlus

/-- Kaon-zero particle model, generated from the common constructor. -/
noncomputable def kaonZeroParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.kaonZero

/-- `D⁺` particle model, generated from the common constructor. -/
noncomputable def dPlusParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.dPlus

/-- `J/ψ` charmonium particle model, generated from the common constructor. -/
noncomputable def charmoniumJpsiParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.charmoniumJpsi

/-- `Υ` bottomonium particle model, generated from the common constructor. -/
noncomputable def bottomoniumUpsilonParticleModel : NamedHadronParticleModel :=
  namedHadronParticleModel NamedHadron.bottomoniumUpsilon

/-- The complete finite index of generated named-hadron particle models. -/
noncomputable def allNamedHadronParticleModels : List NamedHadronParticleModel :=
  [protonParticleModel,
    neutronParticleModel,
    lambdaParticleModel,
    sigmaPlusParticleModel,
    sigmaZeroParticleModel,
    sigmaMinusParticleModel,
    xiZeroParticleModel,
    xiMinusParticleModel,
    omegaMinusParticleModel,
    lambdaCPlusParticleModel,
    pionPlusParticleModel,
    pionZeroParticleModel,
    pionMinusParticleModel,
    kaonPlusParticleModel,
    kaonZeroParticleModel,
    dPlusParticleModel,
    charmoniumJpsiParticleModel,
    bottomoniumUpsilonParticleModel]

/-- The complete finite index of named hadrons covered by the generated models. -/
def allNamedHadrons : List NamedHadron :=
  [NamedHadron.proton,
    NamedHadron.neutron,
    NamedHadron.lambda,
    NamedHadron.sigmaPlus,
    NamedHadron.sigmaZero,
    NamedHadron.sigmaMinus,
    NamedHadron.xiZero,
    NamedHadron.xiMinus,
    NamedHadron.omegaMinus,
    NamedHadron.lambdaCPlus,
    NamedHadron.pionPlus,
    NamedHadron.pionZero,
    NamedHadron.pionMinus,
    NamedHadron.kaonPlus,
    NamedHadron.kaonZero,
    NamedHadron.dPlus,
    NamedHadron.charmoniumJpsi,
    NamedHadron.bottomoniumUpsilon]

/-- Every named hadron has a generated model in the finite index. -/
lemma allNamedHadrons_complete (h : NamedHadron) : h ∈ allNamedHadrons := by
  cases h <;> simp [allNamedHadrons]

/-- The generated model index has exactly the same names as the named-hadron
index. -/
lemma allNamedHadronParticleModels_names :
    allNamedHadronParticleModels.map NamedHadronParticleModel.name = allNamedHadrons := by
  simp [allNamedHadronParticleModels, allNamedHadrons, protonParticleModel,
    neutronParticleModel, lambdaParticleModel, sigmaPlusParticleModel,
    sigmaZeroParticleModel, sigmaMinusParticleModel, xiZeroParticleModel,
    xiMinusParticleModel, omegaMinusParticleModel, lambdaCPlusParticleModel,
    pionPlusParticleModel, pionZeroParticleModel, pionMinusParticleModel,
    kaonPlusParticleModel, kaonZeroParticleModel, dPlusParticleModel,
    charmoniumJpsiParticleModel, bottomoniumUpsilonParticleModel,
    namedHadronParticleModel]

/-- Capability predicate for the generated particle models: every named model
has checked additive quantum numbers, constituent count, statistics and exchange
phase, and the explicit model index is complete. -/
def HasDataDrivenNamedHadronParticleModels : Prop :=
  (∀ h : NamedHadron,
      (namedHadronParticleModel h).quantumNumbers.electric = namedHadronExpectedCharge h)
    ∧ (∀ h : NamedHadron,
      (namedHadronParticleModel h).quantumNumbers.baryon = namedHadronExpectedBaryonNumber h)
    ∧ (∀ h : NamedHadron, (namedHadronParticleModel h).quantumNumbers.lepton = 0)
    ∧ (∀ h : NamedHadron,
      (namedHadronParticleModel h).constituentCount =
        namedHadronExpectedConstituentCount h)
    ∧ (∀ h : NamedHadron,
      (namedHadronParticleModel h).statistics = namedHadronExpectedStatistics h)
    ∧ (∀ h : NamedHadron,
      (namedHadronParticleModel h).exchangePhase =
        namedHadronExpectedExchangePhase h)
    ∧ (∀ h : NamedHadron, namedHadronMesonChargeCoherent h)
    ∧ allNamedHadronParticleModels.map NamedHadronParticleModel.name = allNamedHadrons
    ∧ (∀ h : NamedHadron, h ∈ allNamedHadrons)

/-- All generated named-particle models are checked from the shared valence
table. -/
lemma dataDrivenNamedHadronParticleModels_checked :
    HasDataDrivenNamedHadronParticleModels :=
  ⟨namedHadronParticleModel_electric_eq_expected,
    namedHadronParticleModel_baryon_eq_expected,
    namedHadronParticleModel_lepton_eq_zero,
    namedHadronParticleModel_constituentCount_eq_expected,
    namedHadronParticleModel_statistics_eq_expected,
    namedHadronParticleModel_exchangePhase_eq_expected,
    namedHadronMesonChargeCoherent_checked,
    allNamedHadronParticleModels_names,
    allNamedHadrons_complete⟩


set_option backward.isDefEq.respectTransparency false in
/-- The light-flavor baryon octet: `N`, `Λ`, `Σ`, and `Ξ`. -/
inductive BaryonOctetMember : Type
  | proton | neutron | lambda
  | sigmaPlus | sigmaZero | sigmaMinus
  | xiZero | xiMinus
  deriving DecidableEq, Fintype, Repr

namespace BaryonOctetMember

/-- Valence quark content of each baryon-octet member. -/
def valence : BaryonOctetMember → List QuarkFlavor
  | proton => [up, up, down]
  | neutron => [up, down, down]
  | lambda => [up, down, strange]
  | sigmaPlus => [up, up, strange]
  | sigmaZero => [up, down, strange]
  | sigmaMinus => [down, down, strange]
  | xiZero => [up, strange, strange]
  | xiMinus => [down, strange, strange]

/-- Computed electric charge of a baryon-octet member. -/
def charge (b : BaryonOctetMember) : ℚ :=
  listCharge b.valence

/-- Computed strangeness of a baryon-octet member. -/
def strangeness (b : BaryonOctetMember) : ℤ :=
  listStrangeness b.valence

/-- Expected charge row for the octet, checked from `valence` below. -/
def expectedCharge : BaryonOctetMember → ℚ
  | proton => 1
  | neutron => 0
  | lambda => 0
  | sigmaPlus => 1
  | sigmaZero => 0
  | sigmaMinus => -1
  | xiZero => 0
  | xiMinus => -1

/-- Expected strangeness row for the octet, checked from `valence` below. -/
def expectedStrangeness : BaryonOctetMember → ℤ
  | proton | neutron => 0
  | lambda | sigmaPlus | sigmaZero | sigmaMinus => -1
  | xiZero | xiMinus => -2

/-- The baryon octet has eight members. -/
lemma card_eq_eight : Fintype.card BaryonOctetMember = 8 := by
  decide

/-- Every baryon-octet member has three valence quarks. -/
lemma valence_length_three (b : BaryonOctetMember) :
    b.valence.length = 3 := by
  cases b <;> rfl

/-- Every baryon-octet member has baryon number one. -/
lemma baryonNumber_one (b : BaryonOctetMember) :
    (b.valence.map QuarkFlavor.baryonNumber).sum = 1 := by
  cases b <;>
    norm_num [valence, proton, neutron, lambda, sigmaPlus, sigmaZero, sigmaMinus,
      xiZero, xiMinus, QuarkFlavor.baryonNumber, quarkBaryonNumber]

/-- The baryon-octet charges are computed from quark content. -/
lemma charge_eq_expected (b : BaryonOctetMember) :
    b.charge = b.expectedCharge := by
  cases b <;>
    norm_num [charge, expectedCharge, valence, listCharge, proton, neutron, lambda,
      sigmaPlus, sigmaZero, sigmaMinus, xiZero, xiMinus, QuarkFlavor.electricCharge,
      QuarkFlavor.windingNumber, windingCharge]

/-- The baryon-octet strangeness values are computed from quark content. -/
lemma strangeness_eq_expected (b : BaryonOctetMember) :
    b.strangeness = b.expectedStrangeness := by
  cases b <;>
    simp [strangeness, expectedStrangeness, valence, listStrangeness, QuarkFlavor.strangeness]

/-- Strong Gell-Mann--Nishijima holds for every baryon-octet valence row. -/
lemma gellMannNishijima (b : BaryonOctetMember) :
    b.charge = listIsospinT3 b.valence + listHypercharge b.valence / 2 := by
  simpa [charge] using gmn_strong_baryon b.valence

/-- Every baryon-octet row is a three-quark fermion in the exchange-phase
model. -/
lemma exchangePhase_fermion (b : BaryonOctetMember) :
    compositeTwist b.valence.length = -1 := by
  rw [valence_length_three b]
  exact baryon_is_fermion

end BaryonOctetMember

set_option backward.isDefEq.respectTransparency false in
/-- The spin-3/2 light-flavor baryon decuplet. The valence lists are the
flavor rows; spin-wavefunction symmetrization is represented by membership in
this decuplet carrier. -/
inductive BaryonDecupletMember : Type
  | deltaPlusPlus | deltaPlus | deltaZero | deltaMinus
  | sigmaStarPlus | sigmaStarZero | sigmaStarMinus
  | xiStarZero | xiStarMinus
  | omegaMinus
  deriving DecidableEq, Fintype, Repr

namespace BaryonDecupletMember

/-- Valence quark content of each baryon-decuplet member. -/
def valence : BaryonDecupletMember → List QuarkFlavor
  | deltaPlusPlus => [up, up, up]
  | deltaPlus => [up, up, down]
  | deltaZero => [up, down, down]
  | deltaMinus => [down, down, down]
  | sigmaStarPlus => [up, up, strange]
  | sigmaStarZero => [up, down, strange]
  | sigmaStarMinus => [down, down, strange]
  | xiStarZero => [up, strange, strange]
  | xiStarMinus => [down, strange, strange]
  | omegaMinus => [strange, strange, strange]

/-- Computed electric charge of a baryon-decuplet member. -/
def charge (b : BaryonDecupletMember) : ℚ :=
  listCharge b.valence

/-- Computed strangeness of a baryon-decuplet member. -/
def strangeness (b : BaryonDecupletMember) : ℤ :=
  listStrangeness b.valence

/-- Expected charge row for the decuplet, checked from `valence` below. -/
def expectedCharge : BaryonDecupletMember → ℚ
  | deltaPlusPlus => 2
  | deltaPlus => 1
  | deltaZero => 0
  | deltaMinus => -1
  | sigmaStarPlus => 1
  | sigmaStarZero => 0
  | sigmaStarMinus => -1
  | xiStarZero => 0
  | xiStarMinus => -1
  | omegaMinus => -1

/-- Expected strangeness row for the decuplet, checked from `valence` below. -/
def expectedStrangeness : BaryonDecupletMember → ℤ
  | deltaPlusPlus | deltaPlus | deltaZero | deltaMinus => 0
  | sigmaStarPlus | sigmaStarZero | sigmaStarMinus => -1
  | xiStarZero | xiStarMinus => -2
  | omegaMinus => -3

/-- The baryon decuplet has ten members. -/
lemma card_eq_ten : Fintype.card BaryonDecupletMember = 10 := by
  decide

/-- Every baryon-decuplet member has three valence quarks. -/
lemma valence_length_three (b : BaryonDecupletMember) :
    b.valence.length = 3 := by
  cases b <;> rfl

/-- Every baryon-decuplet member has baryon number one. -/
lemma baryonNumber_one (b : BaryonDecupletMember) :
    (b.valence.map QuarkFlavor.baryonNumber).sum = 1 := by
  cases b <;>
    norm_num [valence, omegaMinus, QuarkFlavor.baryonNumber, quarkBaryonNumber]

/-- The baryon-decuplet charges are computed from quark content. -/
lemma charge_eq_expected (b : BaryonDecupletMember) :
    b.charge = b.expectedCharge := by
  cases b <;>
    norm_num [charge, expectedCharge, valence, listCharge, omegaMinus,
      QuarkFlavor.electricCharge, QuarkFlavor.windingNumber, windingCharge]

/-- The baryon-decuplet strangeness values are computed from quark content. -/
lemma strangeness_eq_expected (b : BaryonDecupletMember) :
    b.strangeness = b.expectedStrangeness := by
  cases b <;>
    simp [strangeness, expectedStrangeness, valence, listStrangeness, QuarkFlavor.strangeness]

/-- Strong Gell-Mann--Nishijima holds for every baryon-decuplet valence row. -/
lemma gellMannNishijima (b : BaryonDecupletMember) :
    b.charge = listIsospinT3 b.valence + listHypercharge b.valence / 2 := by
  simpa [charge] using gmn_strong_baryon b.valence

/-- Every baryon-decuplet row is a three-quark fermion in the exchange-phase
model. -/
lemma exchangePhase_fermion (b : BaryonDecupletMember) :
    compositeTwist b.valence.length = -1 := by
  rw [valence_length_three b]
  exact baryon_is_fermion

end BaryonDecupletMember

/-! ### Meson nonet -/

/-- `K⁻ = s ubar`. -/
noncomputable def kaonMinusFlavor : List MesonFlavorComponent :=
  [{ quark := strange, antiquarkOf := up, amplitude := 1 }]

/-- `Kbar⁰ = s dbar`. -/
noncomputable def antiKaonZeroFlavor : List MesonFlavorComponent :=
  [{ quark := strange, antiquarkOf := down, amplitude := 1 }]

/-- `η₈ = (u ubar + d dbar - 2 s sbar)/sqrt 6`, the octet neutral state. -/
noncomputable def etaEightFlavor : List MesonFlavorComponent :=
  [{ quark := up, antiquarkOf := up, amplitude := 1 / Real.sqrt 6 },
    { quark := down, antiquarkOf := down, amplitude := 1 / Real.sqrt 6 },
    { quark := strange, antiquarkOf := strange, amplitude := -(2 / Real.sqrt 6) }]

/-- `η₁ = (u ubar + d dbar + s sbar)/sqrt 3`, the singlet neutral state. -/
noncomputable def etaSingletFlavor : List MesonFlavorComponent :=
  [{ quark := up, antiquarkOf := up, amplitude := 1 / Real.sqrt 3 },
    { quark := down, antiquarkOf := down, amplitude := 1 / Real.sqrt 3 },
    { quark := strange, antiquarkOf := strange, amplitude := 1 / Real.sqrt 3 }]

set_option backward.isDefEq.respectTransparency false in
/-- The light pseudoscalar flavor nonet: pion triplet, kaon quadruplet, and
the `η₈/η₁` neutral states whose mixing gives `η/η'`. -/
inductive MesonNonetMember : Type
  | pionPlus | pionZero | pionMinus
  | kaonPlus | kaonZero | kaonMinus | antiKaonZero
  | etaEight | etaSinglet
  deriving DecidableEq, Fintype, Repr

namespace MesonNonetMember

/-- Flavor-component model of each nonet member. -/
noncomputable def flavor : MesonNonetMember → List MesonFlavorComponent
  | pionPlus => pionPlusFlavor
  | pionZero => pionZeroFlavor
  | pionMinus => pionMinusFlavor
  | kaonPlus => kaonPlusFlavor
  | kaonZero => kaonZeroFlavor
  | kaonMinus => kaonMinusFlavor
  | antiKaonZero => antiKaonZeroFlavor
  | etaEight => etaEightFlavor
  | etaSinglet => etaSingletFlavor

/-- Computed charge of a nonet member from the first flavor component. Charge
coherence below proves this is component-independent. -/
noncomputable def charge (m : MesonNonetMember) : ℚ :=
  (HadronValenceModel.meson m.flavor).electricCharge

/-- Expected charge row for the meson nonet, checked from `flavor` below. -/
def expectedCharge : MesonNonetMember → ℚ
  | pionPlus => 1
  | pionZero => 0
  | pionMinus => -1
  | kaonPlus => 1
  | kaonZero => 0
  | kaonMinus => -1
  | antiKaonZero => 0
  | etaEight => 0
  | etaSinglet => 0

/-- The meson nonet has nine members. -/
lemma card_eq_nine : Fintype.card MesonNonetMember = 9 := by
  decide

/-- The nonet charges are computed from quark-antiquark components. -/
lemma charge_eq_expected (m : MesonNonetMember) :
    m.charge = m.expectedCharge := by
  cases m <;>
    norm_num [charge, expectedCharge, flavor, HadronValenceModel.electricCharge,
      MesonFlavorComponent.charge, pionPlusFlavor, pionZeroFlavor, pionMinusFlavor,
      kaonPlusFlavor, kaonZeroFlavor, kaonMinusFlavor, antiKaonZeroFlavor,
      etaEightFlavor, etaSingletFlavor, mesonCharge, QuarkFlavor.electricCharge,
      QuarkFlavor.windingNumber, windingCharge]

/-- Every component of a nonet row carries the row's computed charge; this is
the coherence check for mixed neutral states such as `π⁰`, `η₈`, and `η₁`. -/
lemma charge_coherent (m : MesonNonetMember) :
    ∀ c ∈ m.flavor, c.charge = m.charge := by
  cases m <;>
    simp [flavor, charge, HadronValenceModel.electricCharge, MesonFlavorComponent.charge,
      pionPlusFlavor, pionZeroFlavor, pionMinusFlavor, kaonPlusFlavor, kaonZeroFlavor,
      kaonMinusFlavor, antiKaonZeroFlavor, etaEightFlavor, etaSingletFlavor,
      mesonCharge, QuarkFlavor.electricCharge, QuarkFlavor.windingNumber, windingCharge]

/-- Every component of a meson-nonet row has baryon number zero. -/
lemma component_baryonNumber_zero (m : MesonNonetMember) :
    ∀ c ∈ m.flavor, c.baryonNumber = 0 := by
  cases m <;>
    simp [flavor, MesonFlavorComponent.baryonNumber, pionPlusFlavor, pionZeroFlavor,
      pionMinusFlavor, kaonPlusFlavor, kaonZeroFlavor, kaonMinusFlavor,
      antiKaonZeroFlavor, etaEightFlavor, etaSingletFlavor, mesonBaryonNumber,
      QuarkFlavor.baryonNumber, quarkBaryonNumber]

/-- Every meson-nonet row is bosonic in the two-constituent exchange-phase
model. -/
lemma exchangePhase_boson (_m : MesonNonetMember) :
    compositeTwist 2 = 1 :=
  meson_is_boson

end MesonNonetMember

/-- Checked capability for the finite flavor-multiplet layer. It enumerates the
light baryon octet, baryon decuplet, and meson nonet, and checks each from
constituent flavor data rather than standalone particle rows. -/
def HasFlavorMultipletEnumeration : Prop :=
  Fintype.card BaryonOctetMember = 8
    ∧ (∀ b : BaryonOctetMember, b.valence.length = 3)
    ∧ (∀ b : BaryonOctetMember, (b.valence.map QuarkFlavor.baryonNumber).sum = 1)
    ∧ (∀ b : BaryonOctetMember, b.charge = b.expectedCharge)
    ∧ (∀ b : BaryonOctetMember, b.strangeness = b.expectedStrangeness)
    ∧ (∀ b : BaryonOctetMember,
      b.charge = listIsospinT3 b.valence + listHypercharge b.valence / 2)
    ∧ (∀ b : BaryonOctetMember, compositeTwist b.valence.length = -1)
    ∧ Fintype.card BaryonDecupletMember = 10
    ∧ (∀ b : BaryonDecupletMember, b.valence.length = 3)
    ∧ (∀ b : BaryonDecupletMember, (b.valence.map QuarkFlavor.baryonNumber).sum = 1)
    ∧ (∀ b : BaryonDecupletMember, b.charge = b.expectedCharge)
    ∧ (∀ b : BaryonDecupletMember, b.strangeness = b.expectedStrangeness)
    ∧ (∀ b : BaryonDecupletMember,
      b.charge = listIsospinT3 b.valence + listHypercharge b.valence / 2)
    ∧ (∀ b : BaryonDecupletMember, compositeTwist b.valence.length = -1)
    ∧ Fintype.card MesonNonetMember = 9
    ∧ (∀ m : MesonNonetMember, m.charge = m.expectedCharge)
    ∧ (∀ m : MesonNonetMember, ∀ c ∈ m.flavor, c.charge = m.charge)
    ∧ (∀ m : MesonNonetMember, ∀ c ∈ m.flavor, c.baryonNumber = 0)
    ∧ (∀ _m : MesonNonetMember, compositeTwist 2 = 1)

/-- The flavor-multiplet enumeration is checked by finite case computation
from quark charge, strangeness, baryon-number, GMN, and exchange-phase
theorems. -/
lemma flavorMultipletEnumeration_checked :
    HasFlavorMultipletEnumeration :=
  ⟨BaryonOctetMember.card_eq_eight,
    BaryonOctetMember.valence_length_three,
    BaryonOctetMember.baryonNumber_one,
    BaryonOctetMember.charge_eq_expected,
    BaryonOctetMember.strangeness_eq_expected,
    BaryonOctetMember.gellMannNishijima,
    BaryonOctetMember.exchangePhase_fermion,
    BaryonDecupletMember.card_eq_ten,
    BaryonDecupletMember.valence_length_three,
    BaryonDecupletMember.baryonNumber_one,
    BaryonDecupletMember.charge_eq_expected,
    BaryonDecupletMember.strangeness_eq_expected,
    BaryonDecupletMember.gellMannNishijima,
    BaryonDecupletMember.exchangePhase_fermion,
    MesonNonetMember.card_eq_nine,
    MesonNonetMember.charge_eq_expected,
    MesonNonetMember.charge_coherent,
    MesonNonetMember.component_baryonNumber_zero,
    MesonNonetMember.exchangePhase_boson⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.gmn_strong_quark where
  formalizes @ "claim:the-strong-gell-mann-nishijima-relation-q-equals-i3-plus-half-hypercharge-holds-for-every-quark-flavor",
  supported_by @ "paper:gell-mann-nishijima-strong-hypercharge-relation"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.gmn_strong_baryon where
  formalizes @ "claim:the-strong-gell-mann-nishijima-relation-lifts-additively-to-every-baryon-total-charge-equals-total-isospin-plus-half-total-hypercharge",
  requires @ "claim:the-strong-gell-mann-nishijima-relation-q-equals-i3-plus-half-hypercharge-holds-for-every-quark-flavor",
  supported_by @ "paper:gell-mann-nishijima-strong-hypercharge-relation"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.gmn_strong_meson where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.gmn_strong_quark",
  formalizes @ "claim:the-strong-gell-mann-nishijima-relation-holds-for-every-quark-antiquark-meson",
  requires @ "claim:the-strong-gell-mann-nishijima-relation-q-equals-i3-plus-half-hypercharge-holds-for-every-quark-flavor"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.mesonBaryonNumber_eq_zero where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:a-quark-antiquark-meson-has-zero-baryon-number"

zil_file_contract physlib.hadronFlavorModel where
  promises "The flavor model of hadrons organized by the strong Gell-Mann-Nishijima relation Q = I3 + Y/2 with strong hypercharge Y = B + S + C + B' + T: the relation holds for every quark flavor, lifts additively to every baryon (total charge equals total isospin plus half total hypercharge) and to every quark-antiquark meson; mesons have zero baryon number; and the strange baryon octet and decuplet assignments are covered."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.electricCharge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.isospinT3",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.hypercharge"]
  forbids_substitutes ["a dynamical derivation of the flavor quantum numbers, which are model assignments",
    "the QCD mass spectrum or hadron masses, only the additive charge/isospin/hypercharge bookkeeping is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.QuarkFlavor.gmn_strong_quark,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.gmn_strong_baryon,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.gmn_strong_meson,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.mesonBaryonNumber_eq_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel.sigmaZero_lambda_same_valence]

/- ZIL-END -/

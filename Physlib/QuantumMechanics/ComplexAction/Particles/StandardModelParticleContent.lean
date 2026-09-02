/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic
public import Physlib.QuantumMechanics.ComplexAction.Particles.Su5GrandUnification


/-!
# The complete Standard-Model fundamental particle content

A single enumeration of **all seventeen** fundamental Standard-Model particle types — the capstone tying
together the sector modules (`HadronFlavorModel.QuarkFlavor`, the lepton generations, `GaugeBosonZoo`,
`HiggsBoson`). Every fundamental particle is a `SMParticle`, and their counts split into the physical sectors.

* **§A — the fermions (12 = 6 quarks + 6 leptons).** `SMQuark` (`u,d,s,c,b,t`), `SMLepton`
  (`e,μ,τ,νₑ,ν_μ,ν_τ`), `SMFermion = SMQuark ⊕ SMLepton`. `card_SMFermion` (`= 12`),
  `fermions_eq_quarks_add_leptons` (`6 + 6`), `fermions_eq_three_generations` (`12 = 3 × 4` — three generations
  of `(up-quark, down-quark, charged lepton, neutrino)`).
* **§B — the bosons (5 types) and the 12 gauge-boson states.** `SMBosonType` (`γ, W, Z, g, H`);
  `gauge_boson_states` (`8 gluons + 3 weak + 1 hypercharge = 12`, via `Su5GrandUnification.standardModel_gauge_bosons`
  / `SuNGaugeSector.sunAdjointDim`).
* **§C — the complete count (17).** `SMParticle = SMFermion ⊕ SMBosonType`; **`card_SMParticle`** (`= 17`): the
  six quarks, six leptons, photon, `W`, `Z`, gluon, and Higgs — every fundamental particle of the Standard
  Model.
* **§D — quantum numbers.** `fermionCharge` (`u,c,t = +2/3`; `d,s,b = −1/3`; `e,μ,τ = −1`; neutrinos `0`) and
  `fermionSpinHalf` / `bosonSpin` (fermions spin ½, gauge bosons spin 1, Higgs spin 0).

**Honest layering.** Exact: the finite enumeration of the fundamental particle types and their counts (`= 17`,
`12 = 6+6 = 3×4`, gauge states `= 12`), and the assignment of electric charge and spin. The identification with
the physical particles (and the antiparticles, colour multiplicity, and chiral states of a full generation,
`Su5GrandUnification`'s `5̄ ⊕ 10 = 15`) is the standard dictionary, recorded in the docstrings.

## References

* The Standard-Model particle content (17 fundamental types). Reuses `Particles.Su5GrandUnification` /
  `SuNGaugeSector` (the `8+3+1 = 12` gauge bosons) and complements `Particles.GaugeBosonZoo` (the 12 gauge-boson
  states), `HadronFlavorModel` (`QuarkFlavor`), and the lepton/`HiggsBoson` modules.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.StandardModelParticleContent


set_option backward.isDefEq.respectTransparency false in
/-- The six **quark** flavours `u, d, s, c, b, t`. -/
inductive SMQuark | up | down | strange | charm | bottom | top
  deriving DecidableEq, Fintype

set_option backward.isDefEq.respectTransparency false in
/-- The six **leptons** `e, μ, τ, νₑ, ν_μ, ν_τ`. -/
inductive SMLepton | electron | muon | tau | nuE | nuMu | nuTau
  deriving DecidableEq, Fintype

/-- The twelve **fundamental fermions** — six quarks and six leptons. -/
abbrev SMFermion := SMQuark ⊕ SMLepton

/-- **There are twelve fundamental fermions** `|SMFermion| = 12`. -/
lemma card_SMFermion : Fintype.card SMFermion = 12 := by decide

/-- **The fermions are six quarks plus six leptons** `12 = 6 + 6`. -/
lemma fermions_eq_quarks_add_leptons :
    Fintype.card SMFermion = Fintype.card SMQuark + Fintype.card SMLepton := by decide

/-- **The fermions are three generations of four** `12 = 3 × 4`: three generations, each with an up-quark, a
down-quark, a charged lepton, and a neutrino. -/
lemma fermions_eq_three_generations : Fintype.card SMFermion = 3 * 4 := by decide


set_option backward.isDefEq.respectTransparency false in
/-- The five **boson types**: the photon `γ`, the weak `W`/`Z`, the gluon `g`, and the Higgs `H`. -/
inductive SMBosonType | photon | wBoson | zBoson | gluon | higgs
  deriving DecidableEq, Fintype

/-- **There are twelve gauge-boson states** `8 gluons + 3 weak + 1 hypercharge = 12`
(`Su5GrandUnification.standardModel_gauge_bosons`). -/
lemma gauge_boson_states : sunAdjointDim 3 + sunAdjointDim 2 + 1 = 12 :=
  Physlib.QuantumMechanics.ComplexAction.Particles.Su5GrandUnification.standardModel_gauge_bosons


/-- The **fundamental Standard-Model particles**: the twelve fermions plus the five boson types. -/
abbrev SMParticle := SMFermion ⊕ SMBosonType

/-- **There are seventeen fundamental Standard-Model particles** `|SMParticle| = 17` — six quarks, six leptons,
the photon, `W`, `Z`, gluon, and Higgs. -/
lemma card_SMParticle : Fintype.card SMParticle = 17 := by decide

/-- **The seventeen split as fermions + bosons** `17 = 12 + 5`. -/
lemma particles_eq_fermions_add_bosons :
    Fintype.card SMParticle = Fintype.card SMFermion + Fintype.card SMBosonType := by decide


/-- The **electric charge** of a fundamental fermion: `+2/3` (`u,c,t`), `−1/3` (`d,s,b`), `−1` (`e,μ,τ`), `0`
(neutrinos). -/
def fermionCharge : SMFermion → ℚ
  | .inl .up | .inl .charm | .inl .top => 2 / 3
  | .inl .down | .inl .strange | .inl .bottom => -1 / 3
  | .inr .electron | .inr .muon | .inr .tau => -1
  | .inr .nuE | .inr .nuMu | .inr .nuTau => 0

/-- **The up-quark charge is `+2/3`.** -/
lemma up_charge : fermionCharge (.inl .up) = 2 / 3 := rfl

/-- **The electron charge is `−1`.** -/
lemma electron_charge : fermionCharge (.inr .electron) = -1 := rfl

/-- **The neutrino is neutral** `Q = 0`. -/
lemma neutrino_charge : fermionCharge (.inr .nuE) = 0 := rfl

/-- Every fundamental fermion is **spin ½**. -/
def fermionSpin : SMFermion → ℚ := fun _ => 1 / 2

/-- The **spin** of a boson type: gauge bosons are spin `1`, the Higgs is spin `0`. -/
def bosonSpin : SMBosonType → ℚ
  | .higgs => 0
  | _ => 1

/-- **The Higgs is spin 0** (the only fundamental scalar). -/
lemma higgs_spin : bosonSpin .higgs = 0 := rfl

/-- **The photon is spin 1** (a gauge boson). -/
lemma photon_spin : bosonSpin .photon = 1 := rfl

end Physlib.QuantumMechanics.ComplexAction.Particles.StandardModelParticleContent

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers
meta import Zil


/-!
# Hadrons: integer charge from color triality — the electric-charge signature of confinement

Quarks carry fractional charge `Q = n/3` with winding `n ≡ 2 (mod 3)` (`Winding.QuarkChargeWinding`). A single quark is
therefore never integer-charged. But the **color-singlet** combinations — three quarks (a baryon), three
antiquarks (an antibaryon), or a quark–antiquark pair (a meson) — have winding summing to a multiple of three,
hence **integer** electric charge:

  `baryon (qqq): n₁+n₂+n₃ ≡ 2+2+2 = 6 ≡ 0 (mod 3)`,  `meson (q q̄): n − n' ≡ 2−2 = 0 (mod 3)`.

This is exactly the electric-charge face of quark confinement: only the `3 ∣ n` (color-singlet) sector is
integer-charged and observed free; isolated fractional quarks are not.

* **§A — composite charges.** `baryonCharge` (`qqq`), `mesonCharge` (`q q̄`).
* **§B — the named hadrons.** `proton_charge` (`uud = +1`), `neutron_charge` (`udd = 0`),
  `pion_plus_charge` (`u d̄ = +1`).
* **§C — integrality from triality.** `baryon_integer_charge` / `meson_integer_charge` (color singlets are
  integer-charged), and `isolated_quark_fractional` (a single quark is not) — the confinement signature.
* **§E/§F — finite matter generators.** The two charge bases extend to all six lepton flavors and all
  six quark flavors, with `18 = 3 × 6` colored quark states and `24 = 6 + 18` lepton-plus-colored-quark
  matter states.

**Honest layering.** Proven and structural: charge additivity in the winding, and that any winding `≡ 2 (mod 3)`
combination closing to `3 ∣ Σn` is integer-charged — so baryons/mesons have integer charge while quarks do not.
This is the *charge* signature of confinement (a quantization fact), **not** a dynamical proof of confinement
(that is QCD non-perturbative dynamics, not formalized here). Flavor assignments match observation.

## References

* Baryon `Q = +1/0`, meson integer charge, quark confinement (charge quantization). `Physlib`
  (`Winding.QuarkChargeWinding.windingCharge`/`upWinding`/`downWinding`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality


/-- **The baryon electric charge** `Q = Q(n₁) + Q(n₂) + Q(n₃)` — three quarks (a color singlet). -/
def baryonCharge (n₁ n₂ n₃ : ℤ) : ℚ :=
  windingCharge n₁ + windingCharge n₂ + windingCharge n₃

/-- **The meson electric charge** `Q = Q(n) + Q(−n')` — a quark (`n`) and an antiquark (`−n'`). -/
def mesonCharge (n n' : ℤ) : ℚ := windingCharge n + windingCharge (-n')

/-- **The tetraquark electric charge** `Q = Q(q₁)+Q(q₂)+Q(qbar₃)+Q(qbar₄)`. -/
def tetraquarkCharge (n₁ n₂ n₃ n₄ : ℤ) : ℚ :=
  windingCharge n₁ + windingCharge n₂ + windingCharge (-n₃) + windingCharge (-n₄)

/-- **The pentaquark electric charge** `Q = Q(q₁)+Q(q₂)+Q(q₃)+Q(q₄)+Q(qbar₅)`. -/
def pentaquarkCharge (n₁ n₂ n₃ n₄ n₅ : ℤ) : ℚ :=
  windingCharge n₁ + windingCharge n₂ + windingCharge n₃ + windingCharge n₄
    + windingCharge (-n₅)


/-- **[Proton charge `+1`]** `uud`: `2/3 + 2/3 − 1/3 = 1`. -/
lemma proton_charge : baryonCharge upWinding upWinding downWinding = 1 := by
  unfold baryonCharge windingCharge upWinding downWinding; norm_num

/-- **[Neutron charge `0`]** `udd`: `2/3 − 1/3 − 1/3 = 0`. -/
lemma neutron_charge : baryonCharge upWinding downWinding downWinding = 0 := by
  unfold baryonCharge windingCharge upWinding downWinding; norm_num

/-- **[π⁺ charge `+1`]** `u d̄`: `2/3 + 1/3 = 1` (the anti-down has charge `+1/3`). -/
lemma pion_plus_charge : mesonCharge upWinding downWinding = 1 := by
  unfold mesonCharge windingCharge upWinding downWinding; norm_num


/-- **[Baryon charge is an integer]** any three quarks with windings `≡ 2 (mod 3)` (the quark sector) have
total winding `≡ 0 (mod 3)`, hence integer charge — a color singlet is integer-charged. -/
lemma baryon_integer_charge (n₁ n₂ n₃ : ℤ)
    (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2) (h₃ : n₃ % 3 = 2) :
    ∃ k : ℤ, baryonCharge n₁ n₂ n₃ = (k : ℚ) := by
  have hsum : (3 : ℤ) ∣ (n₁ + n₂ + n₃) := by omega
  unfold baryonCharge
  rw [windingCharge_add, windingCharge_add]
  exact (windingCharge_integer_iff _).mpr hsum

/-- **[Meson charge is an integer]** a quark (`n ≡ 2`) and an antiquark (`−n'`, `n' ≡ 2`) have total winding
`≡ 0 (mod 3)`, hence integer charge. -/
lemma meson_integer_charge (n n' : ℤ) (h₁ : n % 3 = 2) (h₂ : n' % 3 = 2) :
    ∃ k : ℤ, mesonCharge n n' = (k : ℚ) := by
  have hsum : (3 : ℤ) ∣ (n + -n') := by omega
  unfold mesonCharge
  rw [windingCharge_add]
  exact (windingCharge_integer_iff _).mpr hsum

/-- **[Tetraquark charge is an integer]** two quarks and two antiquarks have
total triality `2+2-2-2 ≡ 0 (mod 3)`, so the electric charge is integer. -/
lemma tetraquark_integer_charge (n₁ n₂ n₃ n₄ : ℤ)
    (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2)
    (h₃ : n₃ % 3 = 2) (h₄ : n₄ % 3 = 2) :
    ∃ k : ℤ, tetraquarkCharge n₁ n₂ n₃ n₄ = (k : ℚ) := by
  have hsum : (3 : ℤ) ∣ (n₁ + n₂ + -n₃ + -n₄) := by omega
  rcases hsum with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    tetraquarkCharge n₁ n₂ n₃ n₄ =
        ((n₁ + n₂ + -n₃ + -n₄ : ℤ) : ℚ) / 3 := by
          unfold tetraquarkCharge windingCharge
          push_cast
          ring
    _ = (k : ℚ) := by
          rw [hk]
          push_cast
          ring

/-- **[Pentaquark charge is an integer]** four quarks and one antiquark have
total triality `2+2+2+2-2 ≡ 0 (mod 3)`, so the electric charge is integer. -/
lemma pentaquark_integer_charge (n₁ n₂ n₃ n₄ n₅ : ℤ)
    (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2)
    (h₃ : n₃ % 3 = 2) (h₄ : n₄ % 3 = 2) (h₅ : n₅ % 3 = 2) :
    ∃ k : ℤ, pentaquarkCharge n₁ n₂ n₃ n₄ n₅ = (k : ℚ) := by
  have hsum : (3 : ℤ) ∣ (n₁ + n₂ + n₃ + n₄ + -n₅) := by omega
  rcases hsum with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    pentaquarkCharge n₁ n₂ n₃ n₄ n₅ =
        ((n₁ + n₂ + n₃ + n₄ + -n₅ : ℤ) : ℚ) / 3 := by
          unfold pentaquarkCharge windingCharge
          push_cast
          ring
    _ = (k : ℚ) := by
          rw [hk]
          push_cast
          ring

/-- **[An isolated quark is fractionally charged]** a single quark (`n ≡ 2 (mod 3)`) is never integer-charged
(`¬ 3 ∣ n`) — the electric-charge signature of confinement: only color singlets appear with integer charge. -/
lemma isolated_quark_fractional (n : ℤ) (h : n % 3 = 2) :
    ¬ ∃ k : ℤ, windingCharge n = (k : ℚ) := by
  rw [windingCharge_integer_iff]
  omega

/-- **[The quark sector is the residue `2 (mod 3)`]** both quark windings lie in the fractional sector. -/
lemma quark_windings_mod_three : upWinding % 3 = 2 ∧ downWinding % 3 = 2 := by
  unfold upWinding downWinding; decide


/-- The nonzero `Z/3` residue classes are exactly the fractional-charge sector
for the winding charge `Q = n/3`. -/
def IsZOverThreeFractionalClass (n : ℤ) : Prop :=
  ¬ (3 : ℤ) ∣ n

/-- The quark-base threefold loop is the `2 mod 3` residue used by the
repository's quark windings (`up = 2`, `down = -1`). -/
def IsThreeFoldQuarkBase (n : ℤ) : Prop :=
  n % 3 = 2

/-- The `Z/3` fractional class is equivalent to non-integral electric charge. -/
lemma zOverThree_fractionalClass_iff_not_integer (n : ℤ) :
    IsZOverThreeFractionalClass n ↔ ¬ ∃ k : ℤ, windingCharge n = (k : ℚ) := by
  unfold IsZOverThreeFractionalClass
  rw [windingCharge_integer_iff]

/-- A threefold quark-base residue is a nonzero `Z/3` fractional class. -/
lemma threeFoldQuarkBase_fractionalClass {n : ℤ}
    (h : IsThreeFoldQuarkBase n) :
    IsZOverThreeFractionalClass n := by
  unfold IsThreeFoldQuarkBase IsZOverThreeFractionalClass at *
  omega

/-- A threefold quark-base residue has non-integral electric charge. -/
lemma threeFoldQuarkBase_not_integer {n : ℤ}
    (h : IsThreeFoldQuarkBase n) :
    ¬ ∃ k : ℤ, windingCharge n = (k : ℚ) :=
  (zOverThree_fractionalClass_iff_not_integer n).mp
    (threeFoldQuarkBase_fractionalClass h)

/-- A valid threefold quark loop: a winding in the `Z/3` quark-base class. -/
structure ThreeFoldQuarkLoop where
  winding : ℤ
  triality : IsThreeFoldQuarkBase winding

namespace ThreeFoldQuarkLoop

/-- The loop multiplicity of a quark-base carrier. -/
def fold (_ : ThreeFoldQuarkLoop) : ℕ := 3

/-- The electric charge carried by a threefold quark loop. -/
def charge (q : ThreeFoldQuarkLoop) : ℚ := windingCharge q.winding

/-- Threefold quark loops have fold count `3`. -/
lemma fold_eq_three (q : ThreeFoldQuarkLoop) : q.fold = 3 := rfl

/-- Threefold quark loops carry the quark-base `Z/3` residue. -/
lemma zOverThree_base (q : ThreeFoldQuarkLoop) :
    IsThreeFoldQuarkBase q.winding :=
  q.triality

/-- Threefold quark-loop charge is fractional, hence not an integer. -/
lemma charge_fractional (q : ThreeFoldQuarkLoop) :
    ¬ ∃ k : ℤ, q.charge = (k : ℚ) := by
  simpa [charge] using threeFoldQuarkBase_not_integer q.triality

end ThreeFoldQuarkLoop

/-- The generated threefold up-type quark loop. -/
def upThreeFoldLoop : ThreeFoldQuarkLoop :=
  ⟨upWinding, quark_windings_mod_three.1⟩

/-- The generated threefold down-type quark loop. -/
def downThreeFoldLoop : ThreeFoldQuarkLoop :=
  ⟨downWinding, quark_windings_mod_three.2⟩

/-- The generated up-type loop has charge `+2/3`. -/
lemma upThreeFoldLoop_charge :
    upThreeFoldLoop.charge = 2 / 3 := by
  simpa [upThreeFoldLoop, ThreeFoldQuarkLoop.charge] using upQuark_charge

/-- The generated down-type loop has charge `-1/3`. -/
lemma downThreeFoldLoop_charge :
    downThreeFoldLoop.charge = -1 / 3 := by
  simpa [downThreeFoldLoop, ThreeFoldQuarkLoop.charge] using downQuark_charge

/-- A sixfold lepton loop is represented by the integer-charge `3 ∣ n`
winding sector. The name records the `2 × 3` closure used for the lepton
carrier; the charge proof is the existing `windingCharge_integer_iff`. -/
structure SixFoldIntegerLeptonLoop where
  winding : ℤ
  integerClass : (3 : ℤ) ∣ winding

namespace SixFoldIntegerLeptonLoop

/-- The loop multiplicity of an integer-charge lepton carrier. -/
def fold (_ : SixFoldIntegerLeptonLoop) : ℕ := 6

/-- The electric charge carried by a sixfold lepton loop. -/
def charge (ℓ : SixFoldIntegerLeptonLoop) : ℚ := windingCharge ℓ.winding

/-- Sixfold lepton loops have fold count `6`. -/
lemma fold_eq_six (ℓ : SixFoldIntegerLeptonLoop) : ℓ.fold = 6 := rfl

/-- Sixfold lepton-loop charge is integer-valued. -/
lemma charge_integer (ℓ : SixFoldIntegerLeptonLoop) :
    ∃ k : ℤ, ℓ.charge = (k : ℚ) := by
  simpa [charge] using (windingCharge_integer_iff ℓ.winding).mpr ℓ.integerClass

end SixFoldIntegerLeptonLoop

/-- The electron as the `n = -3` integer-charge sixfold loop. -/
def electronSixFoldLoop : SixFoldIntegerLeptonLoop :=
  ⟨-3, ⟨-1, by norm_num⟩⟩

/-- The neutrino as the neutral `n = 0` sixfold loop. -/
def neutrinoSixFoldLoop : SixFoldIntegerLeptonLoop :=
  ⟨0, ⟨0, by norm_num⟩⟩

/-- The electron sixfold loop has charge `-1`. -/
lemma electronSixFoldLoop_charge :
    electronSixFoldLoop.charge = -1 := by
  simpa [electronSixFoldLoop, SixFoldIntegerLeptonLoop.charge] using electron_charge

/-- The neutrino sixfold loop has charge `0`. -/
lemma neutrinoSixFoldLoop_charge :
    neutrinoSixFoldLoop.charge = 0 := by
  simpa [neutrinoSixFoldLoop, SixFoldIntegerLeptonLoop.charge] using neutrino_charge

/-- A baryon occupation is exactly three threefold quark loops. This is the
configuration carrier used for enumerating valid three-quark occupations. -/
structure BaryonThreeLoopOccupation where
  q1 : ThreeFoldQuarkLoop
  q2 : ThreeFoldQuarkLoop
  q3 : ThreeFoldQuarkLoop

namespace BaryonThreeLoopOccupation

/-- A baryon occupation contains three quark loops. -/
def loopCount (_ : BaryonThreeLoopOccupation) : ℕ := 3

/-- The total winding of the three-loop baryon occupation. -/
def totalWinding (B : BaryonThreeLoopOccupation) : ℤ :=
  B.q1.winding + B.q2.winding + B.q3.winding

/-- The total electric charge of the three-loop baryon occupation. -/
def totalCharge (B : BaryonThreeLoopOccupation) : ℚ :=
  B.q1.charge + B.q2.charge + B.q3.charge

/-- The three-loop occupation has loop count `3`. -/
lemma loopCount_eq_three (B : BaryonThreeLoopOccupation) :
    B.loopCount = 3 := rfl

/-- The total charge is the existing baryon charge formula, with no new charge
equation introduced. -/
lemma totalCharge_eq_baryonCharge (B : BaryonThreeLoopOccupation) :
    B.totalCharge = baryonCharge B.q1.winding B.q2.winding B.q3.winding := rfl

/-- Three threefold quark loops close to an integer-charge total winding. -/
lemma totalWinding_divisible_by_three (B : BaryonThreeLoopOccupation) :
    (3 : ℤ) ∣ B.totalWinding := by
  have h1 := B.q1.triality
  have h2 := B.q2.triality
  have h3 := B.q3.triality
  unfold totalWinding IsThreeFoldQuarkBase at *
  omega

/-- A baryon made from three threefold quark loops has integer electric charge. -/
lemma totalCharge_integer (B : BaryonThreeLoopOccupation) :
    ∃ k : ℤ, B.totalCharge = (k : ℚ) := by
  simpa [totalCharge_eq_baryonCharge B] using
    baryon_integer_charge B.q1.winding B.q2.winding B.q3.winding
      B.q1.triality B.q2.triality B.q3.triality

end BaryonThreeLoopOccupation

/-- Constructor from three valid quark-base windings. -/
def baryonThreeLoopOccupationOfWindings
    (n₁ n₂ n₃ : ℤ)
    (h₁ : IsThreeFoldQuarkBase n₁)
    (h₂ : IsThreeFoldQuarkBase n₂)
    (h₃ : IsThreeFoldQuarkBase n₃) :
    BaryonThreeLoopOccupation :=
  { q1 := ⟨n₁, h₁⟩
    q2 := ⟨n₂, h₂⟩
    q3 := ⟨n₃, h₃⟩ }

/-- The occupation constructor recovers the existing baryon charge. -/
lemma baryonThreeLoopOccupationOfWindings_charge
    (n₁ n₂ n₃ : ℤ)
    (h₁ : IsThreeFoldQuarkBase n₁)
    (h₂ : IsThreeFoldQuarkBase n₂)
    (h₃ : IsThreeFoldQuarkBase n₃) :
    (baryonThreeLoopOccupationOfWindings n₁ n₂ n₃ h₁ h₂ h₃).totalCharge =
      baryonCharge n₁ n₂ n₃ := rfl

/-- Proton occupation as three threefold loops: `u,u,d`. -/
def protonThreeLoopOccupation : BaryonThreeLoopOccupation :=
  { q1 := upThreeFoldLoop
    q2 := upThreeFoldLoop
    q3 := downThreeFoldLoop }

/-- Neutron occupation as three threefold loops: `u,d,d`. -/
def neutronThreeLoopOccupation : BaryonThreeLoopOccupation :=
  { q1 := upThreeFoldLoop
    q2 := downThreeFoldLoop
    q3 := downThreeFoldLoop }

/-- The proton three-loop occupation has charge `+1`. -/
lemma protonThreeLoopOccupation_charge :
    protonThreeLoopOccupation.totalCharge = 1 := by
  exact proton_charge

/-- The neutron three-loop occupation has charge `0`. -/
lemma neutronThreeLoopOccupation_charge :
    neutronThreeLoopOccupation.totalCharge = 0 := by
  exact neutron_charge


set_option backward.isDefEq.respectTransparency false in
/-- The finite quark-loop base used to generate three-loop baryon
configurations. This is the two charge base, not a hadron table: up-type
loops carry `+2/3`, down-type loops carry `-1/3`. -/
inductive QuarkLoopBase where
  | up
  | down
  deriving DecidableEq, Fintype, Repr

namespace QuarkLoopBase

/-- Interpret a finite quark-loop base as the existing threefold loop carrier. -/
def threeFoldLoop : QuarkLoopBase → ThreeFoldQuarkLoop
  | up => upThreeFoldLoop
  | down => downThreeFoldLoop

/-- Winding number of a finite quark-loop base. -/
def winding (q : QuarkLoopBase) : ℤ :=
  q.threeFoldLoop.winding

/-- Electric charge of a finite quark-loop base. -/
def charge (q : QuarkLoopBase) : ℚ :=
  q.threeFoldLoop.charge

/-- The finite quark-loop base has two generated charge types. -/
lemma card_eq_two : Fintype.card QuarkLoopBase = 2 := by
  decide

/-- Every finite quark-loop base is a valid threefold quark loop. -/
lemma triality (q : QuarkLoopBase) :
    IsThreeFoldQuarkBase q.winding :=
  q.threeFoldLoop.triality

/-- Every finite quark-loop base carries fractional charge. -/
lemma charge_fractional (q : QuarkLoopBase) :
    ¬ ∃ k : ℤ, q.charge = (k : ℚ) :=
  ThreeFoldQuarkLoop.charge_fractional q.threeFoldLoop

/-- The up-type generated base has charge `+2/3`. -/
lemma up_charge : charge up = 2 / 3 :=
  upThreeFoldLoop_charge

/-- The down-type generated base has charge `-1/3`. -/
lemma down_charge : charge down = -1 / 3 :=
  downThreeFoldLoop_charge

end QuarkLoopBase

set_option backward.isDefEq.respectTransparency false in
/-- The finite lepton-loop base used by the sixfold integer-charge sector. -/
inductive IntegerLeptonLoopBase where
  | electron
  | neutrino
  deriving DecidableEq, Fintype, Repr

namespace IntegerLeptonLoopBase

/-- Interpret a finite lepton-loop base as the existing sixfold loop carrier. -/
def sixFoldLoop : IntegerLeptonLoopBase → SixFoldIntegerLeptonLoop
  | electron => electronSixFoldLoop
  | neutrino => neutrinoSixFoldLoop

/-- Electric charge of a finite lepton-loop base. -/
def charge (ℓ : IntegerLeptonLoopBase) : ℚ :=
  ℓ.sixFoldLoop.charge

/-- The finite integer-charge lepton base has two generated carriers here:
electron and neutral lepton. -/
lemma card_eq_two : Fintype.card IntegerLeptonLoopBase = 2 := by
  decide

/-- Every finite lepton-loop base has sixfold integer-charge closure. -/
lemma charge_integer (ℓ : IntegerLeptonLoopBase) :
    ∃ k : ℤ, ℓ.charge = (k : ℚ) :=
  SixFoldIntegerLeptonLoop.charge_integer ℓ.sixFoldLoop

/-- The electron generated base has charge `-1`. -/
lemma electron_charge : charge electron = -1 :=
  electronSixFoldLoop_charge

/-- The neutrino generated base has charge `0`. -/
lemma neutrino_charge : charge neutrino = 0 :=
  neutrinoSixFoldLoop_charge

end IntegerLeptonLoopBase


set_option backward.isDefEq.respectTransparency false in
/-- The six lepton flavors generated from the integer-charge sixfold loop
sector: three charged leptons and three neutrinos. -/
inductive LeptonLoopFlavor where
  | electron
  | muon
  | tau
  | electronNeutrino
  | muonNeutrino
  | tauNeutrino
  deriving DecidableEq, Fintype, Repr

namespace LeptonLoopFlavor

/-- Forget generation/family labels to the two charge carriers:
charged leptons use the electron charge loop, neutrinos use the neutral loop. -/
def chargeBase : LeptonLoopFlavor → IntegerLeptonLoopBase
  | electron => .electron
  | muon => .electron
  | tau => .electron
  | electronNeutrino => .neutrino
  | muonNeutrino => .neutrino
  | tauNeutrino => .neutrino

/-- Interpret a lepton flavor as its sixfold integer-charge loop. -/
def sixFoldLoop (ℓ : LeptonLoopFlavor) : SixFoldIntegerLeptonLoop :=
  ℓ.chargeBase.sixFoldLoop

/-- Electric charge of a lepton flavor, inherited from the sixfold loop. -/
def charge (ℓ : LeptonLoopFlavor) : ℚ :=
  ℓ.sixFoldLoop.charge

/-- The family-number carrier from `Particles.LeptonFlavorNumbers`. -/
def familyNumber :
    LeptonLoopFlavor →
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.LeptonFlavor
  | electron =>
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.electron
  | muon =>
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muon
  | tau =>
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.tau
  | electronNeutrino =>
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.eNeutrino
  | muonNeutrino =>
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muNeutrino
  | tauNeutrino =>
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.tauNeutrino

/-- There are six generated lepton flavors. -/
lemma card_eq_six : Fintype.card LeptonLoopFlavor = 6 := by
  decide

/-- Every generated lepton flavor has integer electric charge. -/
lemma charge_integer (ℓ : LeptonLoopFlavor) :
    ∃ k : ℤ, ℓ.charge = (k : ℚ) :=
  SixFoldIntegerLeptonLoop.charge_integer ℓ.sixFoldLoop

/-- Every generated lepton flavor is either charged `-1` or neutral `0`. -/
lemma charge_eq_charged_or_neutral (ℓ : LeptonLoopFlavor) :
    ℓ.charge = -1 ∨ ℓ.charge = 0 := by
  cases ℓ <;>
    simp [charge, sixFoldLoop, chargeBase, IntegerLeptonLoopBase.sixFoldLoop,
      SixFoldIntegerLeptonLoop.charge, electronSixFoldLoop, neutrinoSixFoldLoop,
      windingCharge]

/-- The three charged-lepton flavors share charge `-1`. -/
lemma charged_leptons_charge :
    charge electron = -1 ∧ charge muon = -1 ∧ charge tau = -1 := by
  simp [charge, sixFoldLoop, chargeBase, IntegerLeptonLoopBase.sixFoldLoop,
    SixFoldIntegerLeptonLoop.charge, electronSixFoldLoop, windingCharge]

/-- The three neutrino flavors are electrically neutral. -/
lemma neutrinos_charge :
    charge electronNeutrino = 0 ∧ charge muonNeutrino = 0 ∧ charge tauNeutrino = 0 := by
  simp [charge, sixFoldLoop, chargeBase, IntegerLeptonLoopBase.sixFoldLoop,
    SixFoldIntegerLeptonLoop.charge, neutrinoSixFoldLoop, windingCharge]

/-- Each generated lepton flavor has total family number one. -/
lemma familyNumber_total_one (ℓ : LeptonLoopFlavor) :
    Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.total
      (familyNumber ℓ) = 1 := by
  cases ℓ <;>
    simp [familyNumber,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.total,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.electron,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muon,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.tau,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.eNeutrino,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muNeutrino,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.tauNeutrino]

end LeptonLoopFlavor

set_option backward.isDefEq.respectTransparency false in
/-- The six quark flavors generated from the two threefold fractional-charge
loop bases. Up/charm/top use the up-type loop; down/strange/bottom use the
down-type loop. -/
inductive QuarkLoopFlavor where
  | up
  | charm
  | top
  | down
  | strange
  | bottom
  deriving DecidableEq, Fintype, Repr

namespace QuarkLoopFlavor

/-- Forget generation/flavor labels to the two quark charge bases. -/
def chargeBase : QuarkLoopFlavor → QuarkLoopBase
  | up => .up
  | charm => .up
  | top => .up
  | down => .down
  | strange => .down
  | bottom => .down

/-- Interpret a quark flavor as its threefold fractional-charge loop. -/
def threeFoldLoop (q : QuarkLoopFlavor) : ThreeFoldQuarkLoop :=
  q.chargeBase.threeFoldLoop

/-- Winding number of a generated quark flavor. -/
def winding (q : QuarkLoopFlavor) : ℤ :=
  q.threeFoldLoop.winding

/-- Electric charge of a generated quark flavor. -/
def charge (q : QuarkLoopFlavor) : ℚ :=
  q.threeFoldLoop.charge

/-- There are six generated quark flavors. -/
lemma card_eq_six : Fintype.card QuarkLoopFlavor = 6 := by
  decide

/-- Every generated quark flavor lies in the threefold quark-base residue. -/
lemma triality (q : QuarkLoopFlavor) :
    IsThreeFoldQuarkBase q.winding :=
  q.threeFoldLoop.triality

/-- Every generated quark flavor has fractional, non-integer charge. -/
lemma charge_fractional (q : QuarkLoopFlavor) :
    ¬ ∃ k : ℤ, q.charge = (k : ℚ) :=
  ThreeFoldQuarkLoop.charge_fractional q.threeFoldLoop

/-- Every generated quark flavor has one of the two Standard-Model quark
charges, `+2/3` or `-1/3`. -/
lemma charge_eq_up_or_down (q : QuarkLoopFlavor) :
    q.charge = 2 / 3 ∨ q.charge = -1 / 3 := by
  cases q <;>
    simp [charge, threeFoldLoop, chargeBase, QuarkLoopBase.threeFoldLoop,
      ThreeFoldQuarkLoop.charge, upThreeFoldLoop, downThreeFoldLoop,
      upWinding, downWinding, windingCharge]

/-- The up-type quark flavors have charge `+2/3`. -/
lemma up_type_charges :
    charge up = 2 / 3 ∧ charge charm = 2 / 3 ∧ charge top = 2 / 3 := by
  simp [charge, threeFoldLoop, chargeBase, QuarkLoopBase.threeFoldLoop,
    ThreeFoldQuarkLoop.charge, upThreeFoldLoop, upWinding, windingCharge]

/-- The down-type quark flavors have charge `-1/3`. -/
lemma down_type_charges :
    charge down = -1 / 3 ∧ charge strange = -1 / 3 ∧ charge bottom = -1 / 3 := by
  simp [charge, threeFoldLoop, chargeBase, QuarkLoopBase.threeFoldLoop,
    ThreeFoldQuarkLoop.charge, downThreeFoldLoop, downWinding, windingCharge]

end QuarkLoopFlavor

/-- A coloured quark state: one of three colour slots together with one of
the six quark flavors. The colour slot is represented minimally as `Fin 3`,
so no separate colour table is introduced here. -/
abbrev ColoredQuarkLoopFlavor : Type :=
  Fin 3 × QuarkLoopFlavor

namespace ColoredQuarkLoopFlavor

/-- The electric charge of a coloured quark is the flavor charge; colour does
not change electric charge. -/
def charge (q : ColoredQuarkLoopFlavor) : ℚ :=
  q.2.charge

/-- There are `3 × 6 = 18` coloured generated quark states. -/
lemma card_eq_eighteen : Fintype.card ColoredQuarkLoopFlavor = 18 := by
  decide

/-- Colour does not affect electric charge. -/
lemma charge_independent_of_colour (c₁ c₂ : Fin 3) (q : QuarkLoopFlavor) :
    charge (c₁, q) = charge (c₂, q) := rfl

/-- Every coloured generated quark state has fractional charge. -/
lemma charge_fractional (q : ColoredQuarkLoopFlavor) :
    ¬ ∃ k : ℤ, charge q = (k : ℚ) :=
  QuarkLoopFlavor.charge_fractional q.2

end ColoredQuarkLoopFlavor

/-- Matter loop flavors in this finite generator: six leptons plus eighteen
coloured quark states. -/
abbrev MatterLoopFlavor : Type :=
  Sum LeptonLoopFlavor ColoredQuarkLoopFlavor

namespace MatterLoopFlavor

/-- Electric charge of a generated matter-loop flavor. -/
def charge : MatterLoopFlavor → ℚ
  | .inl ℓ => ℓ.charge
  | .inr q => q.charge

/-- There are `6 + 18 = 24` generated lepton-plus-coloured-quark matter states. -/
lemma card_eq_twenty_four : Fintype.card MatterLoopFlavor = 24 := by
  decide

/-- Matter states are partitioned by the charge arithmetic already proved:
leptons have integer charge, while coloured quark states are fractional. -/
lemma charge_integer_or_fractional (m : MatterLoopFlavor) :
    (∃ k : ℤ, m.charge = (k : ℚ))
      ∨ ¬ ∃ k : ℤ, m.charge = (k : ℚ) := by
  cases m with
  | inl ℓ =>
      exact Or.inl (LeptonLoopFlavor.charge_integer ℓ)
  | inr q =>
      exact Or.inr (ColoredQuarkLoopFlavor.charge_fractional q)

end MatterLoopFlavor

/-- Ordered three-loop baryon configurations generated from the finite
up/down quark-loop base. There are `2^3 = 8` such ordered configurations. -/
abbrev BaryonLoopConfiguration : Type :=
  Fin 3 → QuarkLoopBase

namespace BaryonLoopConfiguration

/-- Read an ordered finite configuration as the existing three-loop baryon
occupation carrier. -/
def toOccupation (cfg : BaryonLoopConfiguration) : BaryonThreeLoopOccupation :=
  { q1 := (cfg 0).threeFoldLoop
    q2 := (cfg 1).threeFoldLoop
    q3 := (cfg 2).threeFoldLoop }

/-- Total charge of an ordered finite baryon-loop configuration. -/
def totalCharge (cfg : BaryonLoopConfiguration) : ℚ :=
  (toOccupation cfg).totalCharge

/-- Total winding of an ordered finite baryon-loop configuration. -/
def totalWinding (cfg : BaryonLoopConfiguration) : ℤ :=
  (toOccupation cfg).totalWinding

/-- Validity predicate for generated ordered baryon-loop configurations. -/
def IsValid (cfg : BaryonLoopConfiguration) : Prop :=
  (toOccupation cfg).loopCount = 3
    ∧ (3 : ℤ) ∣ totalWinding cfg
    ∧ ∃ k : ℤ, totalCharge cfg = (k : ℚ)

/-- The ordered three-loop generator has exactly `2^3 = 8` configurations. -/
lemma card_eq_eight : Fintype.card BaryonLoopConfiguration = 8 := by
  decide

/-- Every generated ordered configuration is a valid baryon loop occupation:
three loops, closed total winding, and integer total charge. -/
lemma valid (cfg : BaryonLoopConfiguration) : IsValid cfg := by
  exact ⟨BaryonThreeLoopOccupation.loopCount_eq_three (toOccupation cfg),
    BaryonThreeLoopOccupation.totalWinding_divisible_by_three (toOccupation cfg),
    BaryonThreeLoopOccupation.totalCharge_integer (toOccupation cfg)⟩

/-- The proton ordered configuration: `u,u,d`. -/
def proton : BaryonLoopConfiguration :=
  fun i =>
    match i.val with
    | 0 => QuarkLoopBase.up
    | 1 => QuarkLoopBase.up
    | _ => QuarkLoopBase.down

/-- The neutron ordered configuration: `u,d,d`. -/
def neutron : BaryonLoopConfiguration :=
  fun i =>
    match i.val with
    | 0 => QuarkLoopBase.up
    | _ => QuarkLoopBase.down

/-- The generated proton configuration has charge `+1`. -/
lemma proton_charge : totalCharge proton = 1 := by
  norm_num [totalCharge, toOccupation, proton, BaryonThreeLoopOccupation.totalCharge,
    QuarkLoopBase.threeFoldLoop, ThreeFoldQuarkLoop.charge, upThreeFoldLoop,
    downThreeFoldLoop, upWinding, downWinding, windingCharge]

/-- The generated neutron configuration has charge `0`. -/
lemma neutron_charge : totalCharge neutron = 0 := by
  norm_num [totalCharge, toOccupation, neutron, BaryonThreeLoopOccupation.totalCharge,
    QuarkLoopBase.threeFoldLoop, ThreeFoldQuarkLoop.charge, upThreeFoldLoop,
    downThreeFoldLoop, upWinding, downWinding, windingCharge]

end BaryonLoopConfiguration

/-- Unordered occupation classes for a three-loop baryon base: the value is the
number of up-type loops, so the down-type count is `3 - upCount`. -/
abbrev BaryonLoopOccupationClass : Type :=
  Fin 4

namespace BaryonLoopOccupationClass

/-- Number of up-type loops in an unordered three-loop occupation class. -/
def upCount (c : BaryonLoopOccupationClass) : ℕ :=
  c.val

/-- Number of down-type loops in an unordered three-loop occupation class. -/
def downCount (c : BaryonLoopOccupationClass) : ℕ :=
  3 - c.val

/-- The unordered occupation classes always contain exactly three loops. -/
lemma count_total (c : BaryonLoopOccupationClass) :
    upCount c + downCount c = 3 := by
  have h : c.val < 4 := c.isLt
  unfold upCount downCount
  omega

/-- Charge of an unordered three-loop occupation class, computed from the
finite quark-loop charges. -/
def charge (c : BaryonLoopOccupationClass) : ℚ :=
  (upCount c : ℚ) * (2 / 3) + (downCount c : ℚ) * (-1 / 3)

/-- There are four unordered three-loop occupation classes:
`uuu`, `uud`, `udd`, `ddd`, organized by up-count. -/
lemma card_eq_four : Fintype.card BaryonLoopOccupationClass = 4 := by
  decide

/-- The charge of a three-loop occupation class is `upCount - 1`, hence
integer-valued. -/
lemma charge_eq_upCount_sub_one (c : BaryonLoopOccupationClass) :
    charge c = (upCount c : ℚ) - 1 := by
  fin_cases c <;> norm_num [charge, upCount, downCount]

/-- Every unordered three-loop occupation class has integer charge. -/
lemma charge_integer (c : BaryonLoopOccupationClass) :
    ∃ k : ℤ, charge c = (k : ℚ) := by
  fin_cases c
  · exact ⟨-1, by norm_num [charge, upCount, downCount]⟩
  · exact ⟨0, by norm_num [charge, upCount, downCount]⟩
  · exact ⟨1, by norm_num [charge, upCount, downCount]⟩
  · exact ⟨2, by norm_num [charge, upCount, downCount]⟩

end BaryonLoopOccupationClass

/-- Capability predicate for the threefold/sixfold loop occupation model. It
packages the quark `Z/3` fractional base, integer-charge lepton sector, and
baryon-as-three-threefold-loops construction for downstream enumeration. -/
def HasThreeSixBaryonLoopOccupationModel : Prop :=
  (∀ q : ThreeFoldQuarkLoop,
      q.fold = 3
        ∧ IsThreeFoldQuarkBase q.winding
        ∧ ¬ ∃ k : ℤ, q.charge = (k : ℚ))
    ∧ (∀ ℓ : SixFoldIntegerLeptonLoop,
      ℓ.fold = 6
        ∧ ∃ k : ℤ, ℓ.charge = (k : ℚ))
    ∧ upThreeFoldLoop.charge = 2 / 3
    ∧ downThreeFoldLoop.charge = -1 / 3
    ∧ electronSixFoldLoop.charge = -1
    ∧ neutrinoSixFoldLoop.charge = 0
    ∧ (∀ B : BaryonThreeLoopOccupation,
      B.loopCount = 3
        ∧ (3 : ℤ) ∣ B.totalWinding
        ∧ ∃ k : ℤ, B.totalCharge = (k : ℚ))
    ∧ protonThreeLoopOccupation.totalCharge = 1
    ∧ neutronThreeLoopOccupation.totalCharge = 0

/-- Capability predicate for finite enumeration of the generated loop bases:
two quark bases, two integer-charge lepton bases, eight ordered three-loop
baryon configurations, and four unordered charge classes. -/
def HasFiniteThreeSixLoopEnumeration : Prop :=
  Fintype.card QuarkLoopBase = 2
    ∧ Fintype.card IntegerLeptonLoopBase = 2
    ∧ Fintype.card LeptonLoopFlavor = 6
    ∧ Fintype.card QuarkLoopFlavor = 6
    ∧ Fintype.card ColoredQuarkLoopFlavor = 18
    ∧ Fintype.card MatterLoopFlavor = 24
    ∧ (∀ ℓ : LeptonLoopFlavor, ∃ k : ℤ, LeptonLoopFlavor.charge ℓ = (k : ℚ))
    ∧ (∀ ℓ : LeptonLoopFlavor,
      LeptonLoopFlavor.charge ℓ = -1 ∨ LeptonLoopFlavor.charge ℓ = 0)
    ∧ (∀ ℓ : LeptonLoopFlavor,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.total
        (LeptonLoopFlavor.familyNumber ℓ) = 1)
    ∧ (∀ q : QuarkLoopFlavor, IsThreeFoldQuarkBase q.winding)
    ∧ (∀ q : QuarkLoopFlavor, ¬ ∃ k : ℤ, q.charge = (k : ℚ))
    ∧ (∀ q : QuarkLoopFlavor, q.charge = 2 / 3 ∨ q.charge = -1 / 3)
    ∧ (∀ q : ColoredQuarkLoopFlavor, ¬ ∃ k : ℤ, q.charge = (k : ℚ))
    ∧ (∀ m : MatterLoopFlavor,
      (∃ k : ℤ, MatterLoopFlavor.charge m = (k : ℚ))
        ∨ ¬ ∃ k : ℤ, MatterLoopFlavor.charge m = (k : ℚ))
    ∧ Fintype.card BaryonLoopConfiguration = 8
    ∧ Fintype.card BaryonLoopOccupationClass = 4
    ∧ (∀ cfg : BaryonLoopConfiguration, BaryonLoopConfiguration.IsValid cfg)
    ∧ (∀ c : BaryonLoopOccupationClass,
      BaryonLoopOccupationClass.upCount c
        + BaryonLoopOccupationClass.downCount c = 3)
    ∧ (∀ c : BaryonLoopOccupationClass,
      BaryonLoopOccupationClass.charge c =
        (BaryonLoopOccupationClass.upCount c : ℚ) - 1)
    ∧ (∀ c : BaryonLoopOccupationClass,
      ∃ k : ℤ, BaryonLoopOccupationClass.charge c = (k : ℚ))
    ∧ BaryonLoopConfiguration.totalCharge BaryonLoopConfiguration.proton = 1
    ∧ BaryonLoopConfiguration.totalCharge BaryonLoopConfiguration.neutron = 0

/-- The threefold/sixfold loop occupation model is checked from the existing
winding-charge, triality, and baryon-charge theorems. -/
lemma threeSixBaryonLoopOccupationModel_checked :
    HasThreeSixBaryonLoopOccupationModel :=
  ⟨fun q => ⟨ThreeFoldQuarkLoop.fold_eq_three q,
      ThreeFoldQuarkLoop.zOverThree_base q,
      ThreeFoldQuarkLoop.charge_fractional q⟩,
    fun ℓ => ⟨SixFoldIntegerLeptonLoop.fold_eq_six ℓ,
      SixFoldIntegerLeptonLoop.charge_integer ℓ⟩,
    upThreeFoldLoop_charge,
    downThreeFoldLoop_charge,
    electronSixFoldLoop_charge,
    neutrinoSixFoldLoop_charge,
    fun B => ⟨BaryonThreeLoopOccupation.loopCount_eq_three B,
      BaryonThreeLoopOccupation.totalWinding_divisible_by_three B,
      BaryonThreeLoopOccupation.totalCharge_integer B⟩,
    protonThreeLoopOccupation_charge,
    neutronThreeLoopOccupation_charge⟩

/-- The finite threefold/sixfold enumeration is checked by computation of the
finite carriers and by the existing baryon-loop validity proofs. -/
lemma finiteThreeSixLoopEnumeration_checked :
    HasFiniteThreeSixLoopEnumeration :=
  ⟨QuarkLoopBase.card_eq_two,
    IntegerLeptonLoopBase.card_eq_two,
    LeptonLoopFlavor.card_eq_six,
    QuarkLoopFlavor.card_eq_six,
    ColoredQuarkLoopFlavor.card_eq_eighteen,
    MatterLoopFlavor.card_eq_twenty_four,
    LeptonLoopFlavor.charge_integer,
    LeptonLoopFlavor.charge_eq_charged_or_neutral,
    LeptonLoopFlavor.familyNumber_total_one,
    QuarkLoopFlavor.triality,
    QuarkLoopFlavor.charge_fractional,
    QuarkLoopFlavor.charge_eq_up_or_down,
    ColoredQuarkLoopFlavor.charge_fractional,
    MatterLoopFlavor.charge_integer_or_fractional,
    BaryonLoopConfiguration.card_eq_eight,
    BaryonLoopOccupationClass.card_eq_four,
    BaryonLoopConfiguration.valid,
    BaryonLoopOccupationClass.count_total,
    BaryonLoopOccupationClass.charge_eq_upCount_sub_one,
    BaryonLoopOccupationClass.charge_integer,
    BaryonLoopConfiguration.proton_charge,
    BaryonLoopConfiguration.neutron_charge⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.quark_windings_mod_three where
  formalizes @ "claim:up-and-down-quark-charge-windings-are-congruent-to-two-mod-three-the-fractional-charge-class",
  supported_by @ "paper:gell-mann-1964-schematic-model-of-baryons-and-mesons"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.baryon_integer_charge where
  formalizes @ "claim:a-color-singlet-three-quark-baryon-has-integer-electric-charge-from-color-triality",
  requires @ "claim:up-and-down-quark-charge-windings-are-congruent-to-two-mod-three-the-fractional-charge-class",
  supported_by @ "paper:gell-mann-1964-schematic-model-of-baryons-and-mesons"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.isolated_quark_fractional where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding.windingCharge_integer_iff",
  formalizes @ "claim:an-isolated-single-quark-carries-fractional-non-integer-electric-charge-the-charge-signature-of-confinement",
  requires @ "claim:up-and-down-quark-charge-windings-are-congruent-to-two-mod-three-the-fractional-charge-class"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.proton_charge where
  formalizes @ "claim:the-proton-uud-has-electric-charge-one",
  requires @ "claim:a-color-singlet-three-quark-baryon-has-integer-electric-charge-from-color-triality"

zil_file_contract physlib.hadronChargeIntegrality where
  promises "Integer hadron charge from color triality, the electric-charge signature of confinement: up and down quark charge windings are congruent to two mod three (the fractional-charge class); a color-singlet three-quark baryon and a quark-antiquark meson have integer electric charge (proton one, neutron zero, pi-plus one); while an isolated single quark carries fractional charge, so a free fractional charge cannot be isolated."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.baryonCharge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.mesonCharge"]
  forbids_substitutes ["a dynamical proof of confinement, only the charge-integrality signature is carried",
    "a derivation of the quark charge assignments, which are taken from the winding model"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.quark_windings_mod_three,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.baryon_integer_charge,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.meson_integer_charge,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.isolated_quark_fractional,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.proton_charge,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.neutron_charge]

/- ZIL-END -/

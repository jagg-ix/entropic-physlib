/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.SuperoperatorComplexEinsteinBCJSector
meta import Zil

/-!
# The complete complex Einstein field equations: tensor equation + superoperator + BCJ sector

Completes the complex Einstein field equations (`ComplexEinstein.FieldEquations`,
`complexEinsteinFieldEquation`) into a **single canonical system** that includes the fused EM–Lorentz–Dirac
**superoperator equations** and the **mapped BCJ sector** of `ComplexEinstein.SuperoperatorComplexEinsteinBCJSector`. The
complete system `CompleteComplexEinsteinFieldEquation` asserts, in one structure:

* **the tensor field equation** `𝒢 = κ(T + iS)` (`fieldEquation`, `κ ≠ 0`);
* **the BCJ entropic split** `m_I c² = S₁ + S₂` (`entropicSplit`) — the superoperator's entropic gap is the
  sum of two gauge (double-copy) actions.

From these two data the whole structure of the theory follows, packaged as projectors:

* **superoperator equations** (`superoperatorEquations`) — `m_I c² = Im E`, `Re 𝒜 = A` (Levi-Civita's true
  tensor), `Im 𝒜 = −S` (the entropic source), and the complex d'Alembert balance `(T + iS) + 𝒜 = 0`;
* **the mapped BCJ sector** (`bcjDoubleCopy`) — the entropic Einstein source factorizes as the double copy
  `exp(−Im E) = exp(−S₁)·exp(−S₂)` (`gravity = gauge²`);
* **the real sector** (`realSector`) — the standard Einstein equation `G = κT` and the entropic curvature
  `Λ = κS`;
* assembled in `CompleteComplexEinsteinFieldEquation.complete`.

The system is **built** from the GR sector, the entropic identification, and the BCJ split
(`CompleteComplexEinsteinFieldEquation.of_real_and_entropic`), and at **equilibrium** (`Λ = 0`, `S = 0`)
reduces exactly to standard GR (`complete_equilibrium_reduces`). So the complete complex Einstein field
equations are GR (real) ⊕ the superoperator entropic source (imaginary), with the entropic source carried
by the BCJ double copy.

* **§A — the complete system and its superoperator/BCJ projectors** (`CompleteComplexEinsteinFieldEquation`,
  `superoperatorEquations`, `bcjDoubleCopy`, `realSector`).
* **§B — construction, the full assembly, and the equilibrium limit**
  (`of_real_and_entropic`, `complete`, `complete_equilibrium_reduces`).

## References

* complex-action/entropic-time complex Einstein equations; Z. Bern, J. J. M. Carrasco, H. Johansson (arXiv:0805.3993). Carriers:
  `ComplexEinstein.SuperoperatorComplexEinsteinBCJSector` (`superoperator_complexEinstein_incorporates_bcj`),
  `Electromagnetic.SuperoperatorGravitationalTensor` (`superoperator_complexGravitationalTensor`),
  `ComplexEinstein.FieldEquations` (`complexEinsteinFieldEquation_iff_einstein`,
  `complexEinstein_equilibrium_reduces`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.SuperoperatorGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.SuperoperatorComplexEinsteinBCJSector

variable {ι : Type*}


/-- **The complete complex Einstein field equation** — the tensor equation `𝒢 = κ(T + iS)` together with the
superoperator's BCJ entropic split `m_I c² = S₁ + S₂`. The two data determine the full theory: the
superoperator equations, the BCJ double-copy of the entropic source, and the real (GR) sector. -/
structure CompleteComplexEinsteinFieldEquation (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ m_R m_I c S₁ S₂ : ℝ) : Prop where
  /-- The coupling `κ = 8πG/c⁴` is nonzero. -/
  kappa_ne : κ ≠ 0
  /-- The tensor complex Einstein field equation `𝒢 = κ(T + iS)`. -/
  fieldEquation : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ
  /-- The superoperator's entropic gap is the BCJ double-copy split `m_I c² = S₁ + S₂`. -/
  entropicSplit : m_I * c ^ 2 = S₁ + S₂

variable {Ric : Matrix ι ι ℝ} {scalarR : ℝ} {g Λ T S : Matrix ι ι ℝ} {κ m_R m_I c S₁ S₂ : ℝ}

/-- **[The superoperator equations].** The complete system carries the fused superoperator's complex
gravitational tensor: `m_I c² = Im E`, `Re 𝒜 = A` (Levi-Civita's true tensor), `Im 𝒜 = −S` (the entropic
source), and the complex d'Alembert balance `(T + iS) + 𝒜 = 0`. -/
lemma CompleteComplexEinsteinFieldEquation.superoperatorEquations
    (H : CompleteComplexEinsteinFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.re
          = gravitationalTensor Ric scalarR g κ
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.im = -S
      ∧ complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0 :=
  superoperator_complexGravitationalTensor Ric scalarR g Λ T S κ m_R m_I c H.kappa_ne H.fieldEquation

/-- **[The mapped BCJ sector].** The entropic Einstein source of the complete system factorizes as the BCJ
double copy `exp(−Im E) = exp(−S₁)·exp(−S₂)` — the gravity entropic source is `gauge²`. -/
lemma CompleteComplexEinsteinFieldEquation.bcjDoubleCopy
    (H : CompleteComplexEinsteinFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂) :
    Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂) :=
  entropic_einstein_doublecopy_factorizes m_R m_I c S₁ S₂ H.entropicSplit

/-- **[The real sector is standard GR].** The complete system contains the standard Einstein equation
`G = κT` and the entropic curvature `Λ = κS`. -/
lemma CompleteComplexEinsteinFieldEquation.realSector
    (H : CompleteComplexEinsteinFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂) :
    einsteinFieldEquation Ric scalarR g T κ ∧ Λ = κ • S :=
  (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp H.fieldEquation


/-- **[Constructing the complete system] from the GR sector, the entropic identification, and the BCJ
split.** The complete complex Einstein field equation is assembled from the standard Einstein equation
`G = κT` (real), the entropic curvature `Λ = κS` (imaginary), and the BCJ entropic split `m_I c² = S₁ + S₂`. -/
lemma CompleteComplexEinsteinFieldEquation.of_real_and_entropic (hκ : κ ≠ 0)
    (hReal : einsteinFieldEquation Ric scalarR g T κ) (hImag : Λ = κ • S)
    (hsplit : m_I * c ^ 2 = S₁ + S₂) :
    CompleteComplexEinsteinFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ where
  kappa_ne := hκ
  fieldEquation := (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mpr ⟨hReal, hImag⟩
  entropicSplit := hsplit

/-- **[The complete complex Einstein field equations, assembled].** From the complete system follow, in one
statement:

* the **superoperator equations** — `m_I c² = Im E`, `Re 𝒜 = A`, `Im 𝒜 = −S`, and `(T + iS) + 𝒜 = 0`;
* the **mapped BCJ sector** — the entropic source factorizes as the double copy `exp(−Im E) = exp(−S₁)·exp(−S₂)`;
* the **real sector** — the standard Einstein equation `G = κT` and the entropic curvature `Λ = κS`.

The complete complex Einstein field equations are standard GR (real) ⊕ the superoperator entropic source
(imaginary), the entropic source carried by the BCJ double copy. -/
lemma CompleteComplexEinsteinFieldEquation.complete
    (H : CompleteComplexEinsteinFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂) :
    ((m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.re
          = gravitationalTensor Ric scalarR g κ
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.im = -S
      ∧ complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0)
      ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂)
      ∧ (einsteinFieldEquation Ric scalarR g T κ ∧ Λ = κ • S) :=
  ⟨H.superoperatorEquations, H.bcjDoubleCopy, H.realSector⟩

/-- **[Equilibrium limit] the complete system reduces to standard GR.** With the entropic sector off
(`Λ = 0`, `S = entropicStressTensor 0 0 g = 0`), the complete complex Einstein equation reduces exactly to
the standard Einstein field equation `G = κT` — the superoperator and BCJ sectors vanish, leaving GR. -/
lemma complete_equilibrium_reduces (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ) (κ : ℝ) :
    complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) 0 T (entropicStressTensor 0 0 g) κ
      ↔ einsteinFieldEquation Ric scalarR g T κ :=
  complexEinstein_equilibrium_reduces Ric scalarR g T κ

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.of_real_and_entropic where
  formalizes @ "claim:the-complete-complex-einstein-system-is-assembled-from-the-real-einstein-equation-plus-the-entropic-curvature-lambda-equals-kappa-s-and-the-bcj-entropic-split-m-I-c-squared-equals-s-one-plus-s-two"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete where
  formalizes @ "claim:from-the-complete-complex-einstein-system-follow-the-superoperator-equations-m-I-c-squared-equals-im-e-and-the-real-and-imaginary-projections-and-t-plus-i-s-plus-the-superoperator-equals-zero-the-bcj-double-copy-factorization-of-the-entropic-source-and-the-real-einstein-sector-g-equals-kappa-t-with-lambda-equals-kappa-s",
  requires @ "claim:the-complete-complex-einstein-system-is-assembled-from-the-real-einstein-equation-plus-the-entropic-curvature-lambda-equals-kappa-s-and-the-bcj-entropic-split-m-I-c-squared-equals-s-one-plus-s-two"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.complete_equilibrium_reduces where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinstein_equilibrium_reduces",
  formalizes @ "claim:with-the-entropic-sector-off-lambda-zero-and-s-zero-the-complete-complex-einstein-equation-reduces-exactly-to-the-standard-einstein-field-equation-g-equals-kappa-t"

zil_file_contract physlib.completeComplexEinsteinFieldEquations where
  promises "Completes the complex Einstein field equations into one canonical system: the tensor field equation G_complex = kappa(T + iS) with kappa nonzero, plus the BCJ entropic split m_I c² = S1 + S2. From these two data (of_real_and_entropic) the whole structure follows (complete): the fused superoperator equations (m_I c² = Im E, the real/imaginary projections of the complex gravitational tensor, and (T + iS) + superoperator = 0), the mapped BCJ double-copy factorization exp(-Im E) = exp(-S1) exp(-S2) of the entropic source, and the real Einstein sector G = kappa T with entropic curvature Lambda = kappa S. With the entropic sector off (Lambda = 0, S = 0) the system reduces exactly to standard GR (complete_equilibrium_reduces): the complete theory is standard general relativity (real) plus a superoperator entropic source (imaginary) carried by the BCJ double copy."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation"]
  forbids_substitutes ["the tensor general-relativity infrastructure -- the Einstein tensor, Ricci curvature, and stress-energy tensors -- which is the cited geometric machinery",
    "the microscopic origin of the BCJ double-copy split and the superoperator, only the algebraic assembly and equilibrium reduction are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.of_real_and_entropic,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.complete_equilibrium_reduces]

/- ZIL-END -/

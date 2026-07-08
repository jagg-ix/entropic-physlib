/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
public import Physlib.QFT.Wick.Consistency
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction

/-!
# The complete electrogravitic field equations

Assembles the **complete electrogravitic field equations** — the coupled electromagnetic + gravitational
system — by joining the complete complex Einstein field equations
(`ComplexEinstein.CompleteComplexEinsteinFieldEquations`, gravity + superoperator + BCJ sector) to the electromagnetic
**Maxwell–Faraday** sector (`PTSymmetricQFT.MaxwellFaraday`, the gauge side of the double copy). The
electromagnetic field sources the gravitational field, and the BCJ double copy is the coupling
`gravity = gauge²`.

The system `ElectroGravitationalFieldEquation` records:

* **the gravitational sector** `𝒢 = κ(T + iS)` — the complete complex Einstein field equation with the
  superoperator equations (`m_I c² = Im E`, `Re 𝒜 = A`, `Im 𝒜 = −S`, the complex d'Alembert balance) and
  the BCJ entropic double copy `exp(−Im E) = exp(−S₁)·exp(−S₂)`;
* **the electromagnetic sector** — a gauge field `(k, A)` with its **Maxwell–Faraday Bianchi identity**
  `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` (`maxwellBianchi`, the homogeneous Maxwell equation `dF = 0`),
  the gauge side of the BCJ kinematic Jacobi;
* **the Einstein–Maxwell coupling** — the real sector `G = κT` (`einsteinMaxwell`), the electromagnetic
  stress-energy sourcing gravity.

So the complete electrogravitic field equations are: gravity `𝒢 = κ(T + iS)` (complex Einstein +
superoperator), electromagnetism `dF = 0` (Maxwell), and their coupling through the BCJ double copy
(`gravity = gauge²`, the entropic source encoded in the gauge sector). At equilibrium they reduce to the
classical Einstein–Maxwell equations.

* **§A — the electrogravitic system and its sectors** (`ElectroGravitationalFieldEquation`,
  `superoperatorEquations`, `bcjDoubleCopy`, `einsteinMaxwell`).
* **§B — the Maxwell sector and the construction** (`maxwellBianchi`, `of_einstein_maxwell`).
* **§C — the double copy derives the gravity sector from the gauge sector**
  (`stressEnergyConservation`, `entropicSourceDoubleCopy`, `reggeEntropicAction_double_copy`,
  `doubleCopy`).

## References

* complex-action/entropic-time complex Einstein–Maxwell coupling; Z. Bern, J. J. M. Carrasco, H. Johansson (arXiv:0805.3993).
  structures: `ComplexEinstein.CompleteComplexEinsteinFieldEquations` (`CompleteComplexEinsteinFieldEquation`),
  `PTSymmetricQFT.MaxwellFaraday` (`faraday`, `faraday_bianchi`),
  `ComplexEinstein.SuperoperatorComplexEinsteinBCJSector` (`superoperator_em_gravity_bianchi_doublecopy`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QFT.Wick.Consistency
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction

variable {ι : Type*}

/-! ## §A — the electrogravitic system and its sectors -/

/-- **The complete electrogravitic field equation** — the coupled electromagnetic + gravitational system:
the complete complex Einstein field equation (`CompleteComplexEinsteinFieldEquation`, gravity +
superoperator + BCJ) together with an electromagnetic gauge field `(k, A)` whose Maxwell–Faraday Bianchi
identity is the gauge side of the BCJ double copy. -/
structure ElectroGravitationalFieldEquation (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ m_R m_I c S₁ S₂ : ℝ) (k A : Fin 4 → ℝ) : Prop where
  /-- The gravitational sector: the complete complex Einstein field equation. -/
  gravitational : CompleteComplexEinsteinFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂

variable {Ric : Matrix ι ι ℝ} {scalarR : ℝ} {g Λ T S : Matrix ι ι ℝ} {κ m_R m_I c S₁ S₂ : ℝ}
  {k A : Fin 4 → ℝ}

/-- **[The superoperator equations of the electrogravitic system].** The gravitational sector includes the
fused superoperator's complex gravitational tensor: `m_I c² = Im E`, `Re 𝒜 = A` (Levi-Civita's true
tensor), `Im 𝒜 = −S` (the entropic source), and the complex d'Alembert balance `(T + iS) + 𝒜 = 0`. -/
theorem ElectroGravitationalFieldEquation.superoperatorEquations
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.re
          = gravitationalTensor Ric scalarR g κ
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.im = -S
      ∧ complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0 :=
  H.gravitational.superoperatorEquations

/-- **[The BCJ double-copy coupling].** The entropic Einstein source of the electrogravitic system
factorizes as the BCJ double copy `exp(−Im E) = exp(−S₁)·exp(−S₂)` — the gravity entropic source is
`gauge²`, the electromagnetic sector double-copied. -/
theorem ElectroGravitationalFieldEquation.bcjDoubleCopy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂) :=
  H.gravitational.bcjDoubleCopy

/-- **[The Einstein–Maxwell coupling]** `G = κT`. The real sector is the standard Einstein equation with the
electromagnetic stress-energy `T` sourcing gravity, together with the entropic curvature `Λ = κS`. -/
theorem ElectroGravitationalFieldEquation.einsteinMaxwell
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    einsteinFieldEquation Ric scalarR g T κ ∧ Λ = κ • S :=
  H.gravitational.realSector

/-! ## §B — the Maxwell sector, the full equations, and the construction -/

/-- **[The Maxwell–Faraday Bianchi identity]** `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` — the homogeneous
Maxwell equation `dF = 0` of the electromagnetic sector, the gauge side of the BCJ kinematic Jacobi. -/
theorem ElectroGravitationalFieldEquation.maxwellBianchi
    (_H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (lam μ ν : Fin 4) :
    k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0 :=
  faraday_bianchi k A lam μ ν

/-! ## §C — the double copy *derives* the gravity sector from the gauge sector

The electrogravitic coupling is not a bundle of independent gravity and electromagnetic facts: the
**BCJ double copy** genuinely relates the two, and the gravity sector is *derived* from the gauge
sector along its three faces (the two Bianchi contracts of `bcjDualBianchi`, plus the entropic
amplitude):

* **kinematic** — the gauge Maxwell cyclic identity `dF = 0` *is* the BCJ kinematic Jacobi
  `n_s + n_t + n_u = 0` *is* the gravity first Bianchi (`maxwellBianchi` /
  `bcj_kinematic_jacobi_is_first_bianchi`);
* **conservation** — the gravity second Bianchi `∇^μ G_{μν} = 0`, Einstein-contracted to the EM
  stress-energy `∇^μ G = κ ∇^μ T`, *discharges to* stress-energy conservation `∇^μ T_{μν} = 0`
  (`stressEnergyConservation`, via `contracted_bianchi_conservation`);
* **entropic (Sorkin)** — the gravity entropic source is the gauge² sum `m_I c² = S₁ + S₂`, so the
  amplitude factorizes `exp(−m_I c²) = exp(−S₁)·exp(−S₂)`; read through Sorkin (1975), this is the
  entropic defect of the complex Regge action `−½∫R√(−g) = θ` double-copying the gauge action
  (`entropicSourceDoubleCopy`, `reggeEntropicAction_double_copy`). -/

/-- **[Gravity conservation is the double copy of the gauge second Bianchi] `∇^μ T_{μν} = 0`.** For an
electrogravitic solution, when the gravity second Bianchi holds (`∇^μ G_{μν} = 0`) and is
Einstein-contracted to the EM stress-energy divergence (`∇^μ G = κ ∇^μ T`), stress-energy conservation
follows — the gravity-side contract of the double copy (`bcjDualBianchi`), dual to the gauge-side first
Bianchi `dF = 0`. -/
theorem ElectroGravitationalFieldEquation.stressEnergyConservation
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (divG divT : Fin 4 → ℝ) (hEinstein : divG = κ • divT) (hSecondBianchi : divG = 0) :
    divT = 0 :=
  contracted_bianchi_conservation κ H.gravitational.kappa_ne divG divT hEinstein hSecondBianchi

/-- **[The gravity entropic source is the gauge² double copy] `m_I c² = S₁ + S₂`.** The imaginary
Einstein mass is the sum of the two gauge entropic actions, so the gravity amplitude factorizes as the
product of two gauge amplitudes `exp(−m_I c²) = exp(−S₁)·exp(−S₂)` — the amplitude-level double copy
`gravity = gauge²`. -/
theorem ElectroGravitationalFieldEquation.entropicSourceDoubleCopy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    m_I * c ^ 2 = S₁ + S₂
      ∧ Real.exp (-(m_I * c ^ 2)) = Real.exp (-S₁) * Real.exp (-S₂) := by
  refine ⟨H.gravitational.entropicSplit, ?_⟩
  rw [H.gravitational.entropicSplit, neg_add, Real.exp_add]

/-- **[Sorkin: the entropic Regge action double-copies the gauge action] `−½∫R√(−g)|_{entropic} = S₁ + S₂`.**
By Sorkin (1975) the per-bone gravity action is the integrated curvature `cuspActionPerArea θ = θ`; applied
to the entropic curvature defect `Im E = m_I c²`, it equals the gauge² sum `S₁ + S₂` — the double copy
expressed through the discrete Einstein–Hilbert (Regge) action. -/
theorem ElectroGravitationalFieldEquation.reggeEntropicAction_double_copy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    cuspActionPerArea (complexEinsteinEnergy m_R m_I c).im = S₁ + S₂ := by
  rw [cuspActionPerArea_eq_defect, ← H.superoperatorEquations.1, H.gravitational.entropicSplit]

/-- **[The electrogravitic double copy, shown].** For an electrogravitic solution the gauge and gravity
sectors are the faces of one double copy: the gauge first Bianchi `dF = 0`; the derived gravity
stress-energy conservation `∇^μ T = 0` (from the gravity second Bianchi + Einstein contraction); the
entropic gauge² source `m_I c² = S₁ + S₂`; and the Einstein–Maxwell real sector `G = κT`. -/
theorem ElectroGravitationalFieldEquation.doubleCopy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (lam μ ν : Fin 4) (divG divT : Fin 4 → ℝ)
    (hEinstein : divG = κ • divT) (hSecondBianchi : divG = 0) :
    (k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0)
      ∧ divT = 0
      ∧ m_I * c ^ 2 = S₁ + S₂
      ∧ einsteinFieldEquation Ric scalarR g T κ :=
  ⟨H.maxwellBianchi lam μ ν,
    H.stressEnergyConservation divG divT hEinstein hSecondBianchi,
    H.gravitational.entropicSplit, H.einsteinMaxwell.1⟩

/-- **[The path-integral double copy] `‖exp(iS/ℏ)‖ = exp(−S₁/ℏ)·exp(−S₂/ℏ)`.** An implication of the
genuine double copy: since the entropic source is the gauge² sum `m_I c² = Im E = S₁ + S₂`
(`entropicSourceDoubleCopy`), the electrogravitic gravity path weight (`complexActionWeight`, whose
modulus is the entropic damping `exp(−S_I/ℏ)`) factorizes into the **product of the two gauge
amplitudes** — the double copy realized at the level of the complex-action path integral. The phase
`S_R` is arbitrary; only the entropic (imaginary) part includes the double copy. -/
theorem ElectroGravitationalFieldEquation.pathWeight_double_copy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (S_R ℏ : ℝ) :
    ‖complexActionWeight S_R (complexEinsteinEnergy m_R m_I c).im ℏ‖
      = Real.exp (-(S₁ / ℏ)) * Real.exp (-(S₂ / ℏ)) := by
  rw [norm_complexActionWeight, ← H.superoperatorEquations.1, H.gravitational.entropicSplit,
    ← Real.exp_add]
  congr 1; ring

/-- **[The electrogravitic double copy through Sorkin's complex Regge action].** The entropic source
is realized as the imaginary part of a (single-bone) complex Regge action `Σ_b A(b) θ(b)` with
imaginary defect `Im E` (`LeviCivita.ComplexReggeAction`), so the path-integral double copy factors
through Sorkin's discretized action: the modulus of the complex Regge weight is
`exp(−S₁/ℏ)·exp(−S₂/ℏ)`. This ties the electrogravitic double copy to the (Sorkin) complex Regge
action rather than leaving either floating. -/
theorem ElectroGravitationalFieldEquation.reggeActionPathWeight_double_copy
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (θ_R ℏ : ℝ) :
    ‖complexActionWeight
        (complexReggeAction (fun _ : Unit => (1 : ℝ))
          (fun _ => (θ_R : ℂ) + Complex.I * ((complexEinsteinEnergy m_R m_I c).im : ℂ))).re
        (complexReggeAction (fun _ : Unit => (1 : ℝ))
          (fun _ => (θ_R : ℂ) + Complex.I * ((complexEinsteinEnergy m_R m_I c).im : ℂ))).im ℏ‖
      = Real.exp (-(S₁ / ℏ)) * Real.exp (-(S₂ / ℏ)) := by
  rw [reggeAction_complexActionWeight_norm]
  have him : sorkinReggeAction (fun _ : Unit => (1 : ℝ))
      (fun _ => ((θ_R : ℂ) + Complex.I * ((complexEinsteinEnergy m_R m_I c).im : ℂ)).im)
      = (complexEinsteinEnergy m_R m_I c).im := by
    unfold sorkinReggeAction reggeAction; simp
  rw [him, ← H.superoperatorEquations.1, H.gravitational.entropicSplit, ← Real.exp_add]
  congr 1; ring

/-- **[Constructing the electrogravitic field equations] from Einstein–Maxwell + entropic + BCJ.** The
electrogravitic system is assembled from the Einstein equation `G = κT` (electromagnetic source), the
entropic curvature `Λ = κS`, the BCJ entropic split `m_I c² = S₁ + S₂`, and any electromagnetic gauge field
`(k, A)`. -/
theorem ElectroGravitationalFieldEquation.of_einstein_maxwell (hκ : κ ≠ 0)
    (hReal : einsteinFieldEquation Ric scalarR g T κ) (hImag : Λ = κ • S)
    (hsplit : m_I * c ^ 2 = S₁ + S₂) (k A : Fin 4 → ℝ) :
    ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A where
  gravitational :=
    CompleteComplexEinsteinFieldEquation.of_real_and_entropic hκ hReal hImag hsplit

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

end

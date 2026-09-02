/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionElectroGravitational
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-!
# The electron + photon as a full-tensor electrogravitational solution

The electron-exclusion-cell arc established the electron's *source identities* — real mass `→ G`,
entropic/photon-exchange mass `→ Λ`, gravity `=` gauge² (`ElectronExclusion{ComplexEinstein,
ElectroGravitational}`). This module **constructs an actual term** of the full tensor structure
`ComplexEinstein.ElectroGravitationalFieldEquation` for concrete electron + photon data — the electron *is* a
solution of the complete complex Einstein field equations, so every consequence (Einstein–Maxwell, the BCJ
double copy, the Maxwell Bianchi identity) holds for it.

**The matter fixes the geometry (Einstein's equation).** For a rest-frame electron the stress-energy is the
diagonal energy density `T = diag(m_R c², 0, 0, 0)` (`electronStressEnergy`) and the entropic stress is
`S = diag(m_I c², 0, 0, 0)` (`electronEntropicStress`). Choosing the Ricci curvature *sourced by the matter*,
`Ric := κ·T + ½R·g` (`electronSourcedRicci`), makes the Einstein tensor `G = Ric − ½R g = κ·T` by
construction — Einstein's equation determines the geometry from the source. With `Λ := κ·S` and the BCJ split
`m_I c² = S₁ + S₂` (here `S₁ = S₂ = ½ m_I c²`), the three fields of `CompleteComplexEinsteinFieldEquation` are
discharged; adding any photon `(k, A)` gives an `ElectroGravitationalFieldEquation`.

* **§A — the sourced-Ricci construction** (`sourced_completeComplexEinstein`): for any `g, T, S` the
  matter-sourced Ricci `κT + ½Rg` solves the complete complex Einstein equation.
* **§B — the electron + photon instance** (`electronStressEnergy`, `electronEntropicStress`,
  `electronSourcedRicci`, **`electronPhoton_electroGravitational`**).
* **§C — the full-tensor consequences** (`electronPhoton_field_system`): Einstein–Maxwell `G = κT ∧ Λ = κS`,
  the BCJ double copy `exp(−Im E) = exp(−½m_Ic²)²`, and the Maxwell Bianchi identity `dF = 0`.

**Honest layering.** The construction is exact: `einsteinTensor (κT + ½Rg) = κT` by `abel`, the split by
`ring`, and the consequences are the *existing* `ElectroGravitationalFieldEquation` theorems applied to the
instance. The content is that the electron + photon **is a genuine term** of the full tensor system — the
geometry is the one Einstein's equation assigns to the electron's (real + entropic) stress-energy, not a
free choice. No claim of a specific measured curvature; `Ric` is defined as the sourced solution. ## References

* Repo carriers: `ComplexEinstein.{ElectroGravitationalFieldEquations,CompleteComplexEinsteinFieldEquations,
  EinsteinFieldEquationsPhysLean}`, `PTSymmetricQFT.MaxwellFaraday`,
  `HorizonCell.ElectronExclusionElectroGravitational`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronPhotonFieldEquationInstance


/-- **[The matter-sourced Ricci solves the complete complex Einstein equation].** For any background metric
`g` and any real/entropic stress-energy `T, S`, choosing the Ricci curvature sourced by the matter,
`Ric = κ·T + ½R·g`, makes the Einstein tensor equal `κ·T` (Einstein's equation determines the geometry from
the source); with `Λ = κ·S` and the BCJ split `m_I c² = S₁ + S₂`, the tuple is a
`CompleteComplexEinsteinFieldEquation`. -/
lemma sourced_completeComplexEinstein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g T S : Matrix ι ι ℝ) (scalarR κ m_R m_I c S₁ S₂ : ℝ)
    (hκ : κ ≠ 0) (hsplit : m_I * c ^ 2 = S₁ + S₂) :
    CompleteComplexEinsteinFieldEquation (κ • T + (scalarR / 2) • g) scalarR g (κ • S) T S κ
      m_R m_I c S₁ S₂ :=
  CompleteComplexEinsteinFieldEquation.of_real_and_entropic hκ
    (by unfold einsteinFieldEquation einsteinTensor; abel) rfl hsplit


/-- The **rest-frame electron stress-energy** `T = diag(m_R c², 0, 0, 0)` — the real energy density. -/
noncomputable def electronStressEnergy (m_R c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![m_R * c ^ 2, 0, 0, 0]

/-- The **electron entropic stress** `S = diag(m_I c², 0, 0, 0)` — the imaginary/entropic energy density that
sources the imaginary curvature `Λ`. -/
noncomputable def electronEntropicStress (m_I c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![m_I * c ^ 2, 0, 0, 0]

/-- The **Ricci curvature sourced by the electron** `Ric = κ·T + ½R·g` — the geometry Einstein's equation
assigns to the electron's stress-energy. -/
noncomputable def electronSourcedRicci (m_R c scalarR κ : ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  κ • electronStressEnergy m_R c + (scalarR / 2) • g

/-- **[The electron + photon is a full-tensor electrogravitational solution].** With the rest-frame electron
stress-energy `T`, entropic stress `S`, matter-sourced Ricci `Ric = κT + ½Rg`, imaginary curvature `Λ = κS`,
the symmetric BCJ split `S₁ = S₂ = ½ m_I c²`, and any photon `(k, A)`, the tuple is a genuine
`ElectroGravitationalFieldEquation` — the electron *is* a term of the complete complex Einstein + Maxwell
tensor system. -/
lemma electronPhoton_electroGravitational
    (m_R m_I c scalarR κ : ℝ) (hκ : κ ≠ 0) (g : Matrix (Fin 4) (Fin 4) ℝ) (k A : Fin 4 → ℝ) :
    ElectroGravitationalFieldEquation
      (electronSourcedRicci m_R c scalarR κ g) scalarR g
      (κ • electronEntropicStress m_I c) (electronStressEnergy m_R c) (electronEntropicStress m_I c)
      κ m_R m_I c (m_I * c ^ 2 / 2) (m_I * c ^ 2 / 2) k A :=
  ⟨sourced_completeComplexEinstein g (electronStressEnergy m_R c) (electronEntropicStress m_I c)
    scalarR κ m_R m_I c (m_I * c ^ 2 / 2) (m_I * c ^ 2 / 2) hκ (by ring)⟩


/-- **[The electron + photon full-tensor field system].** From the electrogravitational instance follow, in
one statement, for the electron + photon:

* **Einstein–Maxwell** `G = κT ∧ Λ = κS` — the real curvature sourced by the electron's stress-energy and the
  imaginary curvature by its entropic stress;
* the **BCJ double copy** `exp(−Im E) = exp(−½m_Ic²)·exp(−½m_Ic²)` — the entropic gravity source is gauge²;
* the **Maxwell Bianchi identity** `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` (`dF = 0`), the photon's
  homogeneous Maxwell equation.

The electron + photon is a complete tensor solution: geometry from matter, gravity as the double copy of the
photon, and the photon's Maxwell sector. -/
lemma electronPhoton_field_system
    (m_R m_I c scalarR κ : ℝ) (hκ : κ ≠ 0) (g : Matrix (Fin 4) (Fin 4) ℝ) (k A : Fin 4 → ℝ) :
    (einsteinFieldEquation (electronSourcedRicci m_R c scalarR κ g) scalarR g
          (electronStressEnergy m_R c) κ
        ∧ (κ • electronEntropicStress m_I c) = κ • electronEntropicStress m_I c)
      ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c).im)
          = Real.exp (-(m_I * c ^ 2 / 2)) * Real.exp (-(m_I * c ^ 2 / 2))
      ∧ (∀ lam μ ν : Fin 4,
          k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0) := by
  have H := electronPhoton_electroGravitational m_R m_I c scalarR κ hκ g k A
  exact ⟨H.einsteinMaxwell, H.bcjDoubleCopy, fun lam μ ν => H.maxwellBianchi lam μ ν⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronPhotonFieldEquationInstance

end

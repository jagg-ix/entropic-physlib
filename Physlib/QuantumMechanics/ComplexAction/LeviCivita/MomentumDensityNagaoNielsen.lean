/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

/-!
# Levi-Civita relativistic mechanics: the momentum-density vector and the Nagao–Nielsen `p·q` action

Applies Levi-Civita's gravitational-tensor formalism (`LeviCivita.GravitationalTensor`,
arXiv:physics/9906004) to **relativistic mechanics**: the **momentum-density vector**
`qᵘ = Tᵘᵛ uᵥ`, the energy–momentum tensor contracted with the four-velocity `u`
(`relMomentumDensity`). This is the momentum-current the d'Alembert balance acts on, and the
quantity the Nagao–Nielsen complex action pairs with the complex momentum `p` through the canonical
`p·q` term.

* the **relativistic momentum density** `q = T *ᵥ u` (`relMomentumDensity`) and the **entropic momentum
  density** `S *ᵥ u` (`entropicMomentumDensity`), the matter and entropy-production momentum currents;
* the **complex momentum density** `q_ℂ = (T + iS) *ᵥ u` (`complexMomentumDensity`) of the Nagao–Nielsen
  complex action, whose real part is the relativistic momentum density and whose imaginary part is the
  entropic one (`complexMomentumDensity_re`, `complexMomentumDensity_im`);
* **Levi-Civita's d'Alembert balance read in momentum space** — on a solution of the field equation the
  momentum density equals minus the gravitational tensor contracted with `u`, `q = −(A *ᵥ u)`
  (`relMomentumDensity_eq_neg_grav`), and the complex momentum density is `q_ℂ = −(𝒜 *ᵥ u)`
  (`complexMomentumDensity_eq_neg_complexGrav`): the matter momentum current and the gravitational/inertial
  momentum current identically cancel, the d'Alembert principle in relativistic mechanics;
* the **Nagao–Nielsen canonical `p·q` pairing** `nnCanonicalPairing p q = p ⬝ᵥ q` (`nnCanonicalPairing`),
  the vector form of the NN phase-space Lagrangian's kinetic term `p q̇` (`phaseLagrangian_eq_canonicalPairing`,
  reusing `PathIntegral.MomentumPathIntegral.phaseLagrangian`);
* the **assembly** — the NN complex action `p·q` evaluated on the relativistic momentum density equals
  minus the same pairing on the gravitational tensor, `p·q_ℂ = −p·(𝒜 *ᵥ u)`
  (`nn_momentumDensity_dAlembert`): the complex action's canonical pairing includes the d'Alembert balance,
  so energy–momentum (real `p·(T *ᵥ u)`) and entropic (imaginary `p·(S *ᵥ u)`) momentum currents are the
  matter face of the complex gravitational tensor.

* **§A — the momentum-density vector** (`relMomentumDensity`, `entropicMomentumDensity`,
  `relMomentumDensity_eq_neg_grav`).
* **§B — the complex momentum density** (`complexMomentumDensity`, `complexMomentumDensity_apply`,
  `complexMomentumDensity_re`, `complexMomentumDensity_im`, `complexMomentumDensity_eq_neg_complexGrav`).
* **§C — the Nagao–Nielsen `p·q` canonical pairing** (`nnCanonicalPairing`,
  `phaseLagrangian_eq_canonicalPairing`).
* **§D — the assembly** (`nn_momentumDensity_dAlembert`, `leviCivita_momentumDensity_nagaoNielsen`).

## References

* T. Levi-Civita (arXiv:physics/9906004), the gravitational tensor and the balance `T + A = 0`.
* K. Nagao, H. B. Nielsen, the complex action `S = ∫(p q̇ − H) dt`. structures:
  `LeviCivita.GravitationalTensor` (`gravitationalTensor`, `dAlembert_balance`),
  `LeviCivita.ComplexLeviCivitaGravitationalTensor` (`complexGravitationalTensor`, `complex_dAlembert_balance`),
  `ComplexEinstein.FieldEquations` (`complexStressEnergy`), `PathIntegral.MomentumPathIntegral` (`phaseLagrangian`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Matrix

variable {ι : Type*} [Fintype ι]

/-! ## §A — the relativistic momentum-density vector `qᵘ = Tᵘᵛ uᵥ` -/

/-- **The relativistic momentum-density vector** `qᵘ = Tᵘᵛ uᵥ` — the energy–momentum tensor `T`
contracted with the four-velocity `u`. In relativistic mechanics this is the momentum current of the
matter; its conservation `∇·q = 0` is the Levi-Civita d'Alembert balance read in momentum space. -/
def relMomentumDensity (T : Matrix ι ι ℝ) (u : ι → ℝ) : ι → ℝ := T *ᵥ u

/-- **The entropic momentum-density vector** `Sᵘᵛ uᵥ` — the entropic stress tensor contracted with the
four-velocity, the entropy-production momentum current (the imaginary partner of `relMomentumDensity`). -/
def entropicMomentumDensity (S : Matrix ι ι ℝ) (u : ι → ℝ) : ι → ℝ := S *ᵥ u

/-- **[The momentum density is minus the gravitational momentum current] `q = −(A *ᵥ u)`.** On a solution
of the Einstein field equation, Levi-Civita's d'Alembert balance `T + A = 0` gives, in momentum space,
that the matter momentum density equals minus the gravitational/inertial tensor contracted with the
four-velocity — the two momentum currents identically cancel (d'Alembert's principle, relativistic). -/
theorem relMomentumDensity_eq_neg_grav (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (κ : ℝ) (u : ι → ℝ) (hκ : κ ≠ 0) (h : einsteinFieldEquation Ric scalarR g T κ) :
    relMomentumDensity T u = -(gravitationalTensor Ric scalarR g κ *ᵥ u) := by
  have hT : T = -gravitationalTensor Ric scalarR g κ :=
    eq_neg_of_add_eq_zero_left (dAlembert_balance Ric scalarR g T κ hκ h)
  rw [relMomentumDensity, hT, Matrix.neg_mulVec]

/-! ## §B — the complex momentum density `q_ℂ = (T + iS) *ᵥ u` -/

/-- **The complex momentum-density vector** `q_ℂ = (T + iS)ᵘᵛ uᵥ` — the complex stress-energy of the
Nagao–Nielsen complex action (`complexStressEnergy = T + iS`) contracted with the four-velocity. Its real
part is the relativistic momentum density, its imaginary part the entropic one. -/
noncomputable def complexMomentumDensity (T S : Matrix ι ι ℝ) (u : ι → ℝ) : ι → ℂ :=
  complexStressEnergy T S *ᵥ fun μ => (u μ : ℂ)

/-- **[The complex momentum density splits] `q_ℂ = (T *ᵥ u) + i(S *ᵥ u)`.** -/
theorem complexMomentumDensity_apply (T S : Matrix ι ι ℝ) (u : ι → ℝ) (ν : ι) :
    complexMomentumDensity T S u ν
      = ((T *ᵥ u) ν : ℂ) + Complex.I * ((S *ᵥ u) ν : ℂ) := by
  simp only [complexMomentumDensity, complexStressEnergy, complexCombine, mulVec, dotProduct]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- **[Real part is the relativistic momentum density] `Re q_ℂ = T *ᵥ u`.** -/
theorem complexMomentumDensity_re (T S : Matrix ι ι ℝ) (u : ι → ℝ) (ν : ι) :
    (complexMomentumDensity T S u ν).re = relMomentumDensity T u ν := by
  rw [complexMomentumDensity_apply, relMomentumDensity]; simp

/-- **[Imaginary part is the entropic momentum density] `Im q_ℂ = S *ᵥ u`.** -/
theorem complexMomentumDensity_im (T S : Matrix ι ι ℝ) (u : ι → ℝ) (ν : ι) :
    (complexMomentumDensity T S u ν).im = entropicMomentumDensity S u ν := by
  rw [complexMomentumDensity_apply, entropicMomentumDensity]; simp

/-- **[The complex momentum density is minus the complex gravitational momentum current]
`q_ℂ = −(𝒜 *ᵥ u)`.** On a solution of the complex Einstein equation `𝒢 = κ(T + iS)` (`κ ≠ 0`), the complex
d'Alembert balance `(T + iS) + 𝒜 = 0` gives, contracted with the four-velocity, that the complex matter
momentum density equals minus the complex gravitational/inertial tensor contracted with `u`. -/
theorem complexMomentumDensity_eq_neg_complexGrav (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ : ℝ) (u : ι → ℝ) (hκ : κ ≠ 0)
    (h : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    complexMomentumDensity T S u
      = -(complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ *ᵥ fun μ => (u μ : ℂ)) := by
  have hC : complexStressEnergy T S
      = -complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ :=
    eq_neg_of_add_eq_zero_left
      (complex_dAlembert_balance (einsteinTensor Ric scalarR g) Λ T S κ hκ h)
  rw [complexMomentumDensity, hC, Matrix.neg_mulVec]

/-! ## §C — the Nagao–Nielsen `p·q` canonical pairing -/

/-- **The Nagao–Nielsen canonical pairing** `p · q = pᵤ qᵘ` — the symplectic pairing of the complex
momentum covector `p` with a momentum(-density) vector `q`, the vector form of the kinetic term `p q̇` of
the NN phase-space Lagrangian. -/
noncomputable def nnCanonicalPairing (p q : ι → ℂ) : ℂ := p ⬝ᵥ q

/-- **[The NN phase-space Lagrangian's kinetic term is the canonical pairing] `p q̇ = p · q̇`.** The
Nagao–Nielsen phase-space Lagrangian `L = p q̇ − H` (`PathIntegral.MomentumPathIntegral.phaseLagrangian`,
`H = p²/2m + V`) has its kinetic term equal to the canonical pairing on a single degree of freedom — the
scalar NN action is the one-component case of the momentum-density pairing. -/
theorem phaseLagrangian_eq_canonicalPairing (m p qdot V : ℂ) :
    phaseLagrangian m p qdot V
      = nnCanonicalPairing (fun _ : Fin 1 => p) (fun _ => qdot) - (p ^ 2 / (2 * m) + V) := by
  rw [phaseLagrangian, nnCanonicalPairing]
  simp [dotProduct]

/-! ## §D — the assembly: the NN `p·q` action includes the d'Alembert balance -/

/-- **[The NN complex action pairs the momentum density against the gravitational tensor]
`p · q_ℂ = −p · (𝒜 *ᵥ u)`.** On a solution of the complex Einstein equation, the Nagao–Nielsen canonical
`p·q` pairing evaluated on the complex momentum density equals minus the same pairing on the complex
gravitational/inertial tensor contracted with the four-velocity. Levi-Civita's d'Alembert balance is
encoded in the NN complex action's canonical term. -/
theorem nn_momentumDensity_dAlembert (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ : ℝ) (u : ι → ℝ) (p : ι → ℂ) (hκ : κ ≠ 0)
    (h : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    nnCanonicalPairing p (complexMomentumDensity T S u)
      = -nnCanonicalPairing p
          (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ *ᵥ fun μ => (u μ : ℂ)) := by
  rw [nnCanonicalPairing, nnCanonicalPairing,
    complexMomentumDensity_eq_neg_complexGrav Ric scalarR g Λ T S κ u hκ h, dotProduct_neg]

/-- **[Levi-Civita relativistic mechanics in the Nagao–Nielsen complex action, assembled].** For a
solution of the complex Einstein equation `𝒢 = κ(T + iS)` (`κ ≠ 0`) and a four-velocity `u`:

* the complex momentum density splits into the relativistic and entropic momentum currents,
  `Re q_ℂ = T *ᵥ u` and `Im q_ℂ = S *ᵥ u`;
* the real momentum density obeys the d'Alembert balance `q = −(A *ᵥ u)` (matter ⊕ gravitational momentum
  currents cancel);
* the complex momentum density obeys the complex balance `q_ℂ = −(𝒜 *ᵥ u)`;
* the Nagao–Nielsen canonical `p·q` action records it: `p · q_ℂ = −p · (𝒜 *ᵥ u)`.

Levi-Civita's gravitational tensor, the relativistic momentum density, and the Nagao–Nielsen complex
action's canonical pairing are one structure — the matter momentum current is the negative of the
gravitational one, real (energy–momentum) plus imaginary (entropic). -/
theorem leviCivita_momentumDensity_nagaoNielsen (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ : ℝ) (u : ι → ℝ) (p : ι → ℂ) (ν : ι) (hκ : κ ≠ 0)
    (h : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    (complexMomentumDensity T S u ν).re = relMomentumDensity T u ν
      ∧ (complexMomentumDensity T S u ν).im = entropicMomentumDensity S u ν
      ∧ relMomentumDensity T u = -(gravitationalTensor Ric scalarR g κ *ᵥ u)
      ∧ complexMomentumDensity T S u
          = -(complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ *ᵥ fun μ => (u μ : ℂ))
      ∧ nnCanonicalPairing p (complexMomentumDensity T S u)
          = -nnCanonicalPairing p
              (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ *ᵥ fun μ => (u μ : ℂ)) := by
  obtain ⟨hReal, _⟩ := (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp h
  exact ⟨complexMomentumDensity_re T S u ν, complexMomentumDensity_im T S u ν,
    relMomentumDensity_eq_neg_grav Ric scalarR g T κ u hκ hReal,
    complexMomentumDensity_eq_neg_complexGrav Ric scalarR g Λ T S κ u hκ h,
    nn_momentumDensity_dAlembert Ric scalarR g Λ T S κ u p hκ h⟩

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen

end

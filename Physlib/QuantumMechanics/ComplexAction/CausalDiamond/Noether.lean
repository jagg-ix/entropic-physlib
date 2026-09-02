/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Noether-charge derivation of the Smarr formula (Jacobson–Visser §3.1)

`CausalDiamondThermodynamics` obtained the Smarr formula abstractly from Euler's theorem. This file
formalizes the **Noether-charge bookkeeping** that *derives* it (Jacobson–Visser §3.1, Wald's
formalism): the Smarr formula is exactly the integral identity `∮_{∂Σ} Q_ζ = ∫_Σ j_ζ` (Eq. 3.4,
Stokes' theorem for the closed Noether current `j_ζ = dQ_ζ` on shell), evaluated.

Taking the differential-form integrals at their computed geometric values (the only inputs from the
unformalized Wald computation):

* `∮_{∂Σ} Q_ζ = −κA/(8πG)`                       (Eq. 3.6, Noether charge of the edge `∂Σ`);
* `∫_Σ θ(g, 𝓛_ζ g) = −(d-1)κk V/((d-2)·8πG)`    (Eq. 3.9, symplectic potential);
* `−∫_Σ ζ·L = −Λ V_ζ/((d-2)·4πG)`               (Eq. 3.12, on-shell Lagrangian);

the Noether current integral is their sum `j_ζ = θ − ζ·L` (Eq. 3.2):

* `∫_Σ j_ζ = −[(d-1)κk V + 2Λ V_ζ]/((d-2)·8πG)`   (Eq. 3.15, `noetherCurrentIntegral_eq`),

and the Stokes identity `∮Q_ζ = ∫j_ζ` (the one geometric assumption `hStokes`) yields

  `(d-2)κA = (d-1)κk V + 2 V_ζ Λ`   (Eq. 3.16, `smarr_from_noether`).

This is the *logical skeleton* of the Noether derivation: the differential-geometric evaluation of each
form-integral is taken as given, but the assembly `j_ζ = θ − ζ·L` and the Stokes identity combine them
into the Smarr formula — exactly how §3.1 produces it.

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, §3.1 (Wald, Noether charge). This development:
  `CausalDiamondThermodynamics`, `CausalDiamond.Area`.


-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether


/-- **The Noether charge of the edge `∂Σ`** `∮_{∂Σ} Q_ζ = −κA/(8πG)` (Eq. 3.6). -/
def noetherCharge (κ A G : ℝ) : ℝ := -(κ * A) / (8 * Real.pi * G)

/-- **The symplectic-potential integral** `∫_Σ θ(g, 𝓛_ζ g) = −(d-1)κk V/((d-2)·8πG)` (Eq. 3.9). -/
def sympPotentialIntegral (κ k V d G : ℝ) : ℝ :=
  -((d - 1) * κ * k * V) / ((d - 2) * (8 * Real.pi * G))

/-- **Minus the Lagrangian integral** `−∫_Σ ζ·L = −Λ V_ζ/((d-2)·4πG)` (Eq. 3.12, on-shell). -/
def negLagrangianIntegral (Λ Vζ d G : ℝ) : ℝ := -(Λ * Vζ) / ((d - 2) * (4 * Real.pi * G))

/-- **The Noether current integral** `∫_Σ j_ζ = ∫θ − ∫ζ·L` (Eq. 3.2, `j_ζ = θ − ζ·L`). -/
def noetherCurrentIntegral (κ k V Λ Vζ d G : ℝ) : ℝ :=
  sympPotentialIntegral κ k V d G + negLagrangianIntegral Λ Vζ d G


/-- **Eq. 3.15** `∫_Σ j_ζ = −[(d-1)κk V + 2Λ V_ζ]/((d-2)·8πG)`: the two contributions (3.9) and (3.12)
combine, the factor of `2` arising because `8πG/(4πG) = 2`. -/
lemma noetherCurrentIntegral_eq (κ k V Λ Vζ d G : ℝ) (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hd : d - 2 ≠ 0) :
    noetherCurrentIntegral κ k V Λ Vζ d G
      = -((d - 1) * κ * k * V + 2 * Λ * Vζ) / ((d - 2) * (8 * Real.pi * G)) := by
  unfold noetherCurrentIntegral sympPotentialIntegral negLagrangianIntegral
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  field_simp
  ring


/-- **The Smarr formula from the Noether-charge identity** (Eq. 3.16). The hypothesis `hStokes` is the
integral identity `∮_{∂Σ} Q_ζ = ∫_Σ j_ζ` (Eq. 3.4, Stokes' theorem for the on-shell-exact Noether
current) — the single geometric input. Multiplying through by `−(d-2)·8πG` turns it into the Smarr
formula. -/
lemma smarr_from_noether (κ A k V Λ Vζ d G : ℝ) (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hd : d - 2 ≠ 0)
    (hStokes : noetherCharge κ A G = noetherCurrentIntegral κ k V Λ Vζ d G) :
    (d - 2) * κ * A = (d - 1) * κ * k * V + 2 * Vζ * Λ := by
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  set M : ℝ := -(d - 2) * (8 * Real.pi * G) with hM
  have e1 : (d - 2) * κ * A = M * noetherCharge κ A G := by
    rw [hM]; unfold noetherCharge; field_simp
  have e2 : M * noetherCurrentIntegral κ k V Λ Vζ d G = (d - 1) * κ * k * V + 2 * Vζ * Λ := by
    rw [hM, noetherCurrentIntegral_eq κ k V Λ Vζ d G hπ hG hd]; field_simp
  rw [e1, hStokes, e2]

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The first law of causal diamonds — the variational Wald derivation (Jacobson–Visser §3.2)

`CausalDiamond.Noether` assembled the **Smarr formula** from the Noether-charge identity (§3.1). This
file formalizes the **first law** (§3.2), the *variational* analogue: the Wald variational identity
`δH_χ = ∮_{∂Σ}[δQ_χ − χ·θ]` (Eq. 3.26), evaluated on the conformal Killing vector `ζ` of the diamond.

Taking the variational form-integrals at their computed values (the inputs from the unformalized Wald
computation):

* `δH_ζ = ∮_{∂Σ} δQ_ζ = −κ δA/(8πG)`     (Eqs. 3.27–3.28; `ζ = 0` on `∂Σ` kills the `χ·θ` term);
* `δH_ζ = δH_ζ^g + δH_ζ^m`               (Eq. 3.29, gravity + matter split);
* `δH_ζ^g = −κk δV/(8πG)`                (Eq. 3.35, gravitational term, `= ` Eq. 1.4);
* `δH_ζ^m = δH_ζ^m̃ + δH_ζ^Λ`            (Eq. 3.43, matter = non-Λ matter + cosmological constant);
* `δH_ζ^Λ = V_ζ δΛ/(8πG)`               (Eq. 3.44, cosmological term, `= ` Eq. 1.3);

the algebra assembles them into the **final first law of causal diamonds** (Eq. 3.45):

  `δH_ζ^m̃ = (1/8πG)(−κ δA + κk δV − V_ζ δΛ)`   (`firstLaw_causalDiamond`).

The intermediate `δH_ζ^m = (κ/8πG)(−δA + k δV)` (Eq. 3.36) and the fixed-volume / fixed-area relations
(Eqs. 3.46–3.47), and the **vacuum** law `κ δA = κk δV − V_ζ δΛ` (Eq. 3.22, recovered when
`δH_ζ^m̃ = 0`), follow.

This is the variational counterpart of `CausalDiamond.Noether.smarr_from_noether`: the differential-form
integrals are taken as evaluated inputs (`hWald`, `hSplit`, `hMatterSplit`), and the assembly produces
the first law — exactly how §3.2 derives it.

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, §3.2 (Eqs. 3.26–3.47). This development:
  `CausalDiamond.Noether`, `CausalDiamondThermodynamics`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.FirstLawVariational

/-! ## §A — the variational form-integrals at their evaluated values -/

/-- **The boundary Noether-charge variation** `∮_{∂Σ} δQ_ζ = −κ δA/(8πG)` (Eqs. 3.27–3.28). Since
`ζ = 0` on the edge `∂Σ`, the `ζ·θ` term of the Wald identity (3.26) drops, so this is also `δH_ζ`. -/
def boundaryChargeVar (κ G δA : ℝ) : ℝ := -(κ * δA) / (8 * Real.pi * G)

/-- **The gravitational Hamiltonian variation** `δH_ζ^g = −κk δV/(8πG)` (Eq. 3.35 `=` Eq. 1.4):
proportional to minus the maximal-slice proper-volume variation (the York-time Hamiltonian). -/
def gravHamiltonianVar (κ k G δV : ℝ) : ℝ := -(κ * k * δV) / (8 * Real.pi * G)

/-- **The cosmological-constant Hamiltonian variation** `δH_ζ^Λ = V_ζ δΛ/(8πG)` (Eq. 3.44 `=` Eq. 1.3):
the thermodynamic volume times the variation of `Λ`. -/
def cosmoHamiltonianVar (Vζ G δΛ : ℝ) : ℝ := Vζ * δΛ / (8 * Real.pi * G)

/-! ## §B — the matter Hamiltonian variation (Eq. 3.36) -/

/-- **Eq. 3.36** `δH_ζ^m = (κ/8πG)(−δA + k δV)`: the *total* matter Hamiltonian variation, obtained by
subtracting the gravitational term (3.35) from `δH_ζ = −κδA/(8πG)` via the split (3.29). -/
theorem matterHamiltonianVar_eq (κ k G δA δV dHtot dHmatter : ℝ) (hπ : (0 : ℝ) < Real.pi)
    (hG : G ≠ 0)
    (hWald : dHtot = boundaryChargeVar κ G δA)
    (hSplit : dHtot = gravHamiltonianVar κ k G δV + dHmatter) :
    dHmatter = κ / (8 * Real.pi * G) * (-δA + k * δV) := by
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have hm : dHmatter = boundaryChargeVar κ G δA - gravHamiltonianVar κ k G δV := by
    rw [hWald] at hSplit; linarith
  rw [hm, boundaryChargeVar, gravHamiltonianVar]
  field_simp
  ring

/-! ## §C — the final first law of causal diamonds (Eq. 3.45) -/

/-- **The first law of causal diamonds** (Jacobson–Visser Eq. 3.45):
`δH_ζ^m̃ = (1/8πG)(−κ δA + κk δV − V_ζ δΛ)`. The conformal Killing energy variation of matter (other
than the cosmological constant) is fixed by the variations of the bounding area `A`, the maximal-slice
volume `V`, and the cosmological constant `Λ`. Assembled from the Wald boundary identity (3.28), the
gravity/matter split (3.29), the gravitational term (3.35), and the `Λ`/non-`Λ` matter split (3.43)
with the cosmological term (3.44). -/
theorem firstLaw_causalDiamond (κ k Vζ G δA δV δΛ dHtot dHmatter dHmTilde : ℝ)
    (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hWald : dHtot = boundaryChargeVar κ G δA)
    (hSplit : dHtot = gravHamiltonianVar κ k G δV + dHmatter)
    (hMatterSplit : dHmatter = dHmTilde + cosmoHamiltonianVar Vζ G δΛ) :
    dHmTilde = 1 / (8 * Real.pi * G) * (-(κ * δA) + κ * k * δV - Vζ * δΛ) := by
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have hmt : dHmTilde =
      boundaryChargeVar κ G δA - gravHamiltonianVar κ k G δV - cosmoHamiltonianVar Vζ G δΛ := by
    rw [hWald] at hSplit; linarith
  rw [hmt, boundaryChargeVar, gravHamiltonianVar, cosmoHamiltonianVar]
  field_simp
  ring

/-- **The vacuum first law** (Eq. 3.22): with no conformal Killing matter energy (`δH_ζ^m̃ = 0`) the
first law reduces to the purely geometric `κ δA = κk δV − V_ζ δΛ` — recovering
`CausalDiamondThermodynamics.causalDiamond_firstLaw` / `CausalDiamond.AdS.adsSmarr` in differential
form. -/
theorem firstLaw_vacuum (κ k Vζ G δA δV δΛ dHtot dHmatter : ℝ)
    (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hWald : dHtot = boundaryChargeVar κ G δA)
    (hSplit : dHtot = gravHamiltonianVar κ k G δV + dHmatter)
    (hVac : dHmatter = cosmoHamiltonianVar Vζ G δΛ) :
    κ * δA = κ * k * δV - Vζ * δΛ := by
  have h := firstLaw_causalDiamond κ k Vζ G δA δV δΛ dHtot dHmatter 0 hπ hG hWald hSplit
    (by rw [hVac]; ring)
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have h8 : (8 * Real.pi * G) ≠ 0 := by positivity
  field_simp at h
  linarith [h]

/-! ## §D — fixed-volume and fixed-area variations (Eqs. 3.46–3.47) -/

/-- **Fixed-volume variation** (Eq. 3.46) `(κ/8πG) δA|_V = −δH_ζ^m`: positive conformal Killing matter
energy produces an area deficit at fixed volume. -/
theorem firstLaw_fixedVolume (κ k G δA δV dHtot dHmatter : ℝ) (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hWald : dHtot = boundaryChargeVar κ G δA)
    (hSplit : dHtot = gravHamiltonianVar κ k G δV + dHmatter)
    (hV : δV = 0) :
    κ / (8 * Real.pi * G) * δA = -dHmatter := by
  rw [matterHamiltonianVar_eq κ k G δA δV dHtot dHmatter hπ hG hWald hSplit, hV]
  ring

/-- **Fixed-area variation** (Eq. 3.47) `(κk/8πG) δV|_A = δH_ζ^m`: positive conformal Killing matter
energy produces a volume excess at fixed area. -/
theorem firstLaw_fixedArea (κ k G δA δV dHtot dHmatter : ℝ) (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hWald : dHtot = boundaryChargeVar κ G δA)
    (hSplit : dHtot = gravHamiltonianVar κ k G δV + dHmatter)
    (hA : δA = 0) :
    κ * k / (8 * Real.pi * G) * δV = dHmatter := by
  rw [matterHamiltonianVar_eq κ k G δA δV dHtot dHmatter hπ hG hWald hSplit, hA]
  ring

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.FirstLawVariational

end

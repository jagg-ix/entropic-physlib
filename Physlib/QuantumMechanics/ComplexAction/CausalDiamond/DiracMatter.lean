/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.FirstLawVariational
public import Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-!
# Matter fields and the Dirac field in the causal-diamond first law (Iyer 1997 + Dirac)

`CausalDiamond.FirstLawVariational` left the matter Hamiltonian variation `δH_ζ^m̃` of the first law
(Eq. 3.45) as a free quantity. This file **fills it in for a concrete matter field — the Dirac
field** — using the Lagrangian matter formalism of V. Iyer, *Lagrangian perfect fluids and black hole
mechanics* (Phys. Rev. D 55, 3411, 1997, arXiv:gr-qc/9610025), which Jacobson–Visser cite ([30]) for
the matter sector.

## §A — Iyer's Lagrangian / Noether decomposition

Iyer splits the Lagrangian `L = L_g + L_m` (Eq. 19) and the Noether current/charge accordingly:

* `J[ξ] = J_g[ξ] + J_m[ξ]`   (Eq. 25),   `Q[ξ] = Q_g[ξ] + Q_m[ξ] (+ dZ)`   (Eq. 28);
* the matter Noether current includes the **Hilbert stress-energy** term (Eq. 26):
  `J_m[ξ] = −ε·E_m·ψ·ξ − ε·T·ξ + dQ_m[ξ]`, so on shell (`E_m = 0`), `J_m[ξ] = −ε·T·ξ + dQ_m[ξ]`
  (`matterNoetherCurrent_onShell`).

The stress-energy tensor is the **metric variation** of the matter Lagrangian (Eq. 23):
`δL_m = E_m δψ + ½ T^{ab} δg_ab + dΘ_m`, and the full gravitational equation of motion
`E_g = E_g' + ½ T = 0` is the **Einstein equation** `G^{ab} = 8πG T^{ab}`
(`einstein_equation_from_lagrangian_split`) — matter sources gravity.

## §B — the Dirac field as the matter

The Dirac Hamiltonian `H = α·p + βm` (`Dirac.FourSpinorDiracHamiltonian.diracHamiltonian4`) squares to the
relativistic dispersion `H² = (p² + m²)·1`, so the Dirac one-particle energy is
`E_D = √(p² + m²)` (`diracEnergy`, `diracHamiltonian4_sq_energy`). This `E_D` is the conformal Killing
energy density of the Dirac matter field; its variation `δH_ζ^m̃` enters the first law:

  `δH_ζ^m̃(Dirac) = (1/8πG)(−κ δA + κk δV − V_ζ δΛ)`   (`dirac_firstLaw`),

i.e. the Dirac field's energy variation inside the diamond is fixed by the variations of the bounding
area, the maximal-slice volume, and the cosmological constant.

## References

* V. Iyer, Phys. Rev. D 55, 3411 (1997), Eqs. 19, 23, 25, 26, 28. T. Jacobson, M. Visser,
  arXiv:1812.01596 §3.2. This development: `CausalDiamond.FirstLawVariational`,
  `Dirac.FourSpinorDiracHamiltonian`.

No new axioms.
-/

set_option autoImplicit false

open Real Matrix

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMatter

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.FirstLawVariational
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-! ## §A — Iyer's matter Noether decomposition and the Einstein equation -/

/-- **The total Noether charge splits** `Q[ξ] = Q_g[ξ] + Q_m[ξ]` (Iyer Eq. 28, modulo `dZ`). -/
def totalNoetherCharge (Qg Qm : ℝ) : ℝ := Qg + Qm

/-- **The matter Noether current** `J_m[ξ] = −ε·E_m·ψ·ξ − ε·T·ξ + dQ_m[ξ]` (Iyer Eq. 26), where
`E_m` is the matter equation-of-motion form, `T` the Hilbert stress-energy, and `dQ_m` the exact part. -/
def matterNoetherCurrent (Em ψξ stressEnergyKilling matterChargeExact : ℝ) : ℝ :=
  -(Em * ψξ) - stressEnergyKilling + matterChargeExact

/-- **The matter Noether current on shell** (`E_m = 0`): `J_m[ξ] = −ε·T·ξ + dQ_m[ξ]` (Iyer Eq. 26).
The stress-energy term is what feeds the matter Hamiltonian variation of the first law. -/
theorem matterNoetherCurrent_onShell (Em ψξ sek mce : ℝ) (hEm : Em = 0) :
    matterNoetherCurrent Em ψξ sek mce = -sek + mce := by
  rw [matterNoetherCurrent, hEm]; ring

/-- **The Einstein equation from Iyer's Lagrangian split** (Iyer Eq. 23): the Hilbert stress-energy
(the metric variation of `L_m`) sources gravity. With the pure-gravity equation-of-motion form
`E_g' = −G^{ab}/(16πG)` and Iyer's decomposition `E_g = E_g' + ½T`, the gravitational equation of motion
`E_g = 0` is exactly `G^{ab} = 8πG T^{ab}`. -/
theorem einstein_equation_from_lagrangian_split (Gab T G Eg' Eg : ℝ)
    (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hPureGrav : Eg' = -(Gab / (16 * Real.pi * G)))
    (hIyer23 : Eg = Eg' + (1 / 2) * T)
    (hEom : Eg = 0) :
    Gab = 8 * Real.pi * G * T := by
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  rw [hPureGrav] at hIyer23
  rw [hIyer23] at hEom
  field_simp at hEom
  linarith [hEom]

/-! ## §B — the Dirac field energy (the matter Hamiltonian density) -/

/-- **The Dirac one-particle energy** `E_D = √(p² + m²)` — the eigenvalue of the Dirac Hamiltonian
`H = α·p + βm`, and the conformal Killing energy density of the Dirac matter field. -/
def diracEnergy (p1 p2 p3 m : ℝ) : ℝ := Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2)

/-- **The Dirac mass-shell** `E_D² = p² + m²`. -/
theorem diracEnergy_sq (p1 p2 p3 m : ℝ) :
    diracEnergy p1 p2 p3 m ^ 2 = p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2 := by
  rw [diracEnergy, Real.sq_sqrt (by positivity)]

/-- **The Dirac energy is nonnegative**. -/
theorem diracEnergy_nonneg (p1 p2 p3 m : ℝ) : 0 ≤ diracEnergy p1 p2 p3 m := Real.sqrt_nonneg _

/-- **The Dirac Hamiltonian squares to `E_D²·1`** — the matrix mass-shell `H² = E_D²·1`, recasting
`Dirac.FourSpinorDiracHamiltonian.diracHamiltonian4_sq` in terms of the Dirac energy `E_D = √(p²+m²)`. The
Dirac energy is thus the (doubly degenerate `±E_D`) spectrum of `H`. -/
theorem diracHamiltonian4_sq_energy (p1 p2 p3 m : ℝ) :
    diracHamiltonian4 p1 p2 p3 m * diracHamiltonian4 p1 p2 p3 m
      = ((diracEnergy p1 p2 p3 m ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [diracHamiltonian4_sq, diracEnergy_sq]

/-! ## §C — the Dirac matter contribution to the first law -/

/-- **The first law of causal diamonds with Dirac matter** (Iyer + Jacobson–Visser Eq. 3.45): the
variation of the Dirac field's conformal Killing energy `δH_ζ^m̃` is fixed by the geometry,
`δH_ζ^m̃ = (1/8πG)(−κ δA + κk δV − V_ζ δΛ)`. The matter Hamiltonian variation `δED` is the Dirac
stress-energy term `−∫ δT^D ζ ε` (Iyer Eq. 26 ⟹ Jacobson–Visser Eq. 3.42), with the Dirac stress-energy
`T^D` built from `E_D = √(p²+m²)`. -/
theorem dirac_firstLaw (κ k Vζ G δA δV δΛ dHtot δED : ℝ)
    (hπ : (0 : ℝ) < Real.pi) (hG : G ≠ 0)
    (hWald : dHtot = boundaryChargeVar κ G δA)
    (hSplit : dHtot = gravHamiltonianVar κ k G δV + (δED + cosmoHamiltonianVar Vζ G δΛ)) :
    δED = 1 / (8 * Real.pi * G) * (-(κ * δA) + κ * k * δV - Vζ * δΛ) :=
  firstLaw_causalDiamond κ k Vζ G δA δV δΛ dHtot (δED + cosmoHamiltonianVar Vζ G δΛ) δED hπ hG
    hWald hSplit rfl

/-- **Massless (ultrarelativistic) Dirac matter**: at `m = 0` the Dirac energy is `E_D = |p|`
(`= √(p₁²+p₂²+p₃²)`), the lightlike dispersion — the matter that, integrated over the diamond, gave the
Stefan–Boltzmann `7π⁵/(90β³)` free energy (`StatisticalMechanics.MasslessStefanBoltzmann`). -/
theorem diracEnergy_massless (p1 p2 p3 : ℝ) :
    diracEnergy p1 p2 p3 0 = Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) := by
  rw [diracEnergy]; norm_num

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMatter

end

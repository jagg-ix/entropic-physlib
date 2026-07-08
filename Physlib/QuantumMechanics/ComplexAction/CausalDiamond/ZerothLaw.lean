/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMetricRoot

/-!
# The zeroth law (Appendix C) and the mean curvature ↔ Dirac momentum (Appendix B)

This extends the Dirac-field / metric-common-root join through the two remaining geometric facts of
Jacobson–Visser: the **zeroth law** (Appendix C) and the **mean curvature** (Appendix B).

## §A — the zeroth law for bifurcate conformal Killing horizons (Appendix C)

The surface gravity `κ` of a conformal Killing horizon `𝓗` is defined by `∇_a(ζ²) = −2κ ζ_a` on `𝓗`
(Eq. C.1). It is **constant on `𝓗`** (Jacobson–Visser Zeroth Law), in two parts:

* **along the generators** — taking `𝓛_ζ` of `∇_a ζ²` two ways (Eq. C.2 `= −4ακ ζ_a`; Eq. C.3 via
  C.1 `= (−2 𝓛_ζκ − 4ακ) ζ_a`) and equating gives `𝓛_ζκ = 0` (`zerothLaw_along_generators`, Eq. C.4);
* **across the generators** — on the bifurcation surface `𝓑`, contracting `∇_c∇_aζ_b` with `n^{ab}m^c`
  gives `−2 m^a∇_aκ` (Eq. C.7), while the conformal Killing identity (Eq. C.8) contracted with
  `n^{ab}m^c` vanishes on `𝓑` (since `ζ^d` and `α` vanish there), so `m^a∇_aκ = 0`
  (`zerothLaw_across_generators`).

So `κ` is constant on `𝓗` (`zeroth_law`). Thermodynamically, this is **uniform temperature** — and via
the equivalence principle (`κ = ` proper acceleration), uniform Unruh/Hawking temperature
(`zerothLaw_uniform_temperature`): the horizon is in **thermal equilibrium**.

## §B — the mean curvature includes the Dirac momentum (Appendix B)

The mean curvature of the constant-conformal-Killing-time slices is `K = (1−d) sinh s/(L sinh(R_*/L))`
(Eq. B.6). Its denominator `sinh(R_*/L)` is exactly the Bogoliubov / helicity / Dirac momentum
`ξ = |p|` (`CausalDiamond.DiracMetricRoot`), so

  `K = (1−d) sinh s/(L |p|)`   (`meanCurvature_via_diracMomentum`),

the mean curvature scales inversely with the Dirac momentum, and the maximal slice `K|_{s=0} = 0`
(`CausalDiamond.ConformalIsometry.meanCurvature_maximal_slice`) is momentum-independent — the
equilibrium (extremal-volume) slice of the Dirac thermal state.

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, Appendices B, C. This development:
  `CausalDiamond.DiracMetricRoot`, `CausalDiamond.ConformalIsometry`, `CausalDiamond.EquivalencePrinciple`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw

open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum

/-! ## §A — the zeroth law for bifurcate conformal Killing horizons (Appendix C) -/

/-- **The zeroth law along the generators** `𝓛_ζκ = 0` (Jacobson–Visser Eq. C.4). The hypothesis is
the equality of the two computations of `𝓛_ζ ∇_a ζ²` on `𝓗`: directly (Eq. C.2, the coefficient of
`ζ_a` is `−4ακ`) and via `∇_a ζ² = −2κ ζ_a` (Eq. C.1) followed by `𝓛_ζ` (Eq. C.3, coefficient
`−2 𝓛_ζκ − 4ακ`). The surface gravity is constant along each null generator. -/
theorem zerothLaw_along_generators (α κ LζκVal : ℝ)
    (hC2_eq_C3 : -4 * α * κ = -2 * LζκVal - 4 * α * κ) :
    LζκVal = 0 := by linarith

/-- **The zeroth law across the generators** `m^a∇_aκ = 0` on the bifurcation surface `𝓑`
(Jacobson–Visser, Eqs. C.7–C.8). The hypothesis `hC7` is `n^{ab}m^c∇_c∇_aζ_b = −2 m^a∇_aκ` (Eq. C.7),
and `hC8` is that this contraction vanishes on `𝓑` (the conformal Killing identity Eq. C.8 contracted
with `n^{ab}m^c` is zero, since `ζ^d` and `α` vanish on `𝓑`). The surface gravity does not vary from
generator to generator. -/
theorem zerothLaw_across_generators (mNablaKappa contractionC7 : ℝ)
    (hC7 : contractionC7 = -2 * mNablaKappa) (hC8 : contractionC7 = 0) :
    mNablaKappa = 0 := by
  rw [hC8] at hC7; linarith

/-- **The zeroth law for bifurcate conformal Killing horizons** (Jacobson–Visser Appendix C): the
surface gravity `κ` is constant on `𝓗` — constant along each generator (`𝓛_ζκ = 0`) *and* across
generators (`m^a∇_aκ = 0` on `𝓑`). -/
theorem zeroth_law (α κ LζκVal mNablaKappa contractionC7 : ℝ)
    (hAlong : -4 * α * κ = -2 * LζκVal - 4 * α * κ)
    (hC7 : contractionC7 = -2 * mNablaKappa) (hC8 : contractionC7 = 0) :
    LζκVal = 0 ∧ mNablaKappa = 0 :=
  ⟨zerothLaw_along_generators α κ LζκVal hAlong,
   zerothLaw_across_generators mNablaKappa contractionC7 hC7 hC8⟩

/-! ## §B — the zeroth law is uniform temperature (equilibrium) -/

/-- **Constant surface gravity is uniform temperature** (the zeroth law as thermal equilibrium): if `κ`
is constant on `𝓗` (`κ = κ'`) then the Hawking temperature is the same — and via the equivalence
principle (`κ = ` proper acceleration), the **Unruh temperature** is uniform too. The conformal Killing
horizon is in thermal equilibrium. -/
theorem zerothLaw_uniform_temperature (ℏ κ κ' c kB : ℝ) (h : κ = κ') :
    hawkingTemperature ℏ κ c kB = hawkingTemperature ℏ κ' c kB
      ∧ unruhTemperature ℏ κ c kB = unruhTemperature ℏ κ' c kB := by
  rw [h]; exact ⟨rfl, rfl⟩

/-! ## §C — the mean curvature includes the Dirac momentum (Appendix B) -/

/-- **The mean curvature scales inversely with the Dirac momentum** `K = (1−d) sinh s/(L |p|)`: the
denominator `sinh(R_*/L)` of the Jacobson–Visser mean curvature (Eq. B.6) is the Bogoliubov / helicity
/ Dirac momentum `ξ = |p|` (`CausalDiamond.DiracMetricRoot`). So the constant-conformal-Killing-time
slices' extrinsic curvature is set by the Dirac momentum of the matter mode. -/
theorem meanCurvature_via_diracMomentum (d L Rstar s : ℝ) (p : Fin 3 → ℝ)
    (hp : helicityMomentum p = Real.sinh (Rstar / L)) :
    meanCurvature d L Rstar s = (1 - d) * Real.sinh s / (L * helicityMomentum p) := by
  rw [meanCurvature, hp]

/-- **The maximal slice is momentum-independent** `K|_{s=0} = 0` for any Dirac momentum: the
extremal-volume slice `Σ` (the equilibrium slice underpinning the geometric first law) has zero mean
curvature regardless of `|p|`. -/
theorem meanCurvature_maximal_diracMomentum (d L Rstar : ℝ) (p : Fin 3 → ℝ)
    (hp : helicityMomentum p = Real.sinh (Rstar / L)) :
    meanCurvature d L Rstar 0 = 0 ∧
      meanCurvature d L Rstar 0 = (1 - d) * Real.sinh 0 / (L * helicityMomentum p) := by
  refine ⟨meanCurvature_maximal_slice d L Rstar, ?_⟩
  rw [meanCurvature_via_diracMomentum d L Rstar 0 p hp]

/-! ## §D — the synthesis: zeroth law + mean curvature + Dirac matter -/

/-- **The zeroth law, the mean curvature, and the Dirac matter field, synthesized.** With the
surface-gravity inputs of Appendix C and a Dirac mode whose momentum is `|p| = sinh(R_*/L)`:

* **(Appendix C, zeroth law)** `κ` is constant on `𝓗` (`𝓛_ζκ = 0`, `m^a∇_aκ = 0`) — uniform
  Unruh/Hawking temperature, thermal equilibrium;
* **(Appendix B, mean curvature)** `K = (1−d) sinh s/(L |p|)` — set by the Dirac momentum, with the
  maximal slice `K|_{s=0} = 0` momentum-independent.

So the horizon's thermal equilibrium (constant `κ`) and the slices' geometry (mean curvature) are tied
to the Dirac matter field's momentum `|p|` — the same `|p|` that is the metric common root
`v = |p|/E_D` of gravity, information, and dissipation. -/
theorem zerothLaw_meanCurvature_dirac_synthesis (α κ LζκVal mNablaKappa contractionC7 : ℝ)
    (d L Rstar : ℝ) (p : Fin 3 → ℝ)
    (hAlong : -4 * α * κ = -2 * LζκVal - 4 * α * κ)
    (hC7 : contractionC7 = -2 * mNablaKappa) (hC8 : contractionC7 = 0)
    (hp : helicityMomentum p = Real.sinh (Rstar / L)) :
    (LζκVal = 0 ∧ mNablaKappa = 0)
      ∧ meanCurvature d L Rstar 0 = 0
      ∧ meanCurvature d L Rstar 0 = (1 - d) * Real.sinh 0 / (L * helicityMomentum p) :=
  ⟨zeroth_law α κ LζκVal mNablaKappa contractionC7 hAlong hC7 hC8,
   (meanCurvature_maximal_diracMomentum d L Rstar p hp).1,
   (meanCurvature_maximal_diracMomentum d L Rstar p hp).2⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw

end

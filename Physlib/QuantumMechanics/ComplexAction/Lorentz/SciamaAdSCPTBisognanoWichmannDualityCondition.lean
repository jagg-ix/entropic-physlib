/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannOperatorFlow
meta import Zil

/-!
# The duality condition: the complex boost reaches the reflected wedge
(Bisognano–Wichmann, J. Math. Phys. 16 (1975) 985)

Extends the operator-BW assembly with the **analytic core of the original paper**: Bisognano–Wichmann continue
the wedge boost `V(e₃,t)` (their Eq. 1 — the `[[cosh t, sinh t],[sinh t, cosh t]]` block, the repo's
`thermoBogoliubov`/`modularBoost`) into the complex strip `0 ≤ Im z ≤ π`, and their main relation Eq. 2,
`e^{πK₃} XΩ = JX*Ω`, lives at the strip's edge: the boost at imaginary rapidity `iπ` reaches the **reflected
wedge** (`W_R → W_L`), producing the modular conjugation `J` and the duality `𝒜(W_R)' = 𝒜(W_L)` (their
Theorems 3–4).  This module formalizes the strip's geometric spine on the complexified boost plane:

* `complexBoost` — the analytically-continued boost `Λ(z) = [[cosh z, sinh z],[sinh z, cosh z]]`, with
  `complexBoost_restricts_real` (real rapidity = the repo's `thermoBogoliubov`, BW Eq. 1) and the group law
  `complexBoost_group` (`Λ(z)Λ(w) = Λ(z+w)` — the strip's semigroup structure).
* `complexBoost_strip_edge` — **the boost at `iπ` is the wedge reflection**: `Λ(iπ) = −𝟙` on the boost plane
  (`cosh iπ = cos π = −1`, `sinh iπ = 0`): the analytic continuation across the strip lands on `x ↦ −x`,
  mapping `W_R` onto `W_L` — the geometric content of BW Eq. 2.
* `complexBoost_half_strip` — **the modular conjugation appears at the half strip**:
  `Λ(iπ/2) = i·J` (`J = wedgeModularHamiltonian`, the `!![0,1;1,0]` reflection): halfway across the strip the
  continued boost is `i` times the modular conjugation — the geometric origin of `S = JΔ^{1/2}`.
* `complexBoost_full_rotation` — `Λ(2πi) = 𝟙`: the full Euclidean rotation closes (the matrix-level form of the
  four-clock `2π` reading), consistent with `Λ(iπ)² = (−𝟙)² = 𝟙`.
* `reflection_commutes_complexBoost` — `J Λ(z) J = Λ(z)`: the wedge reflection commutes with the *entire
  complex* boost flow (`JΔ^{it}J = Δ^{it}` for the antiunitary `J`, real-symmetric shadow).
* `bisognanoWichmann_duality_condition` — the capstone: the strip spine (edge `= −𝟙`, half-strip `= i·J`,
  closure at `2πi`, `J`-invariance) together with the wedge Tomita–Takesaki Haag duality — the duality
  condition of the paper's Theorems 3–4 on the finite carrier.

Honest scope: the boost-plane (2×2) geometric spine of the strip continuation, exact; the operator-valued
distribution side of BW Eq. 2 (`e^{πK₃}XΩ = JX*Ω` on the field polynomial algebra, tempered-distribution
analyticity, Theorems 1–4 in full) is the paper's content — the state-side identification remains
`assumption:bisognano-wichmann-wedge`, as in `SciamaAdSCPTBisognanoWichmannOperatorFlow`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart

/-! ## §1. The analytically-continued boost -/

/-- **The complexified wedge boost** `Λ(z) = [[cosh z, sinh z],[sinh z, cosh z]]` — BW Eq. 1's boost block
continued into the strip `0 ≤ Im z ≤ π`. -/
def complexBoost (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cosh z, Complex.sinh z; Complex.sinh z, Complex.cosh z]

/-- **[Real rapidity restricts to the repo's boost]** `Λ(t) = thermoBogoliubov t` (BW Eq. 1). -/
theorem complexBoost_restricts_real (t : ℝ) :
    complexBoost (t : ℂ) = (thermoBogoliubov t).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexBoost, thermoBogoliubov, Complex.ofReal_cosh, Complex.ofReal_sinh]

/-- **[The strip's group law]** `Λ(z)Λ(w) = Λ(z+w)` — cosh/sinh addition. -/
theorem complexBoost_group (z w : ℂ) :
    complexBoost z * complexBoost w = complexBoost (z + w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexBoost, Matrix.mul_apply, Fin.sum_univ_two, Complex.cosh_add, Complex.sinh_add] <;>
    ring

/-! ## §2. The strip spine: edge, half strip, closure -/

/-- **[The boost at `iπ` is the wedge reflection] `Λ(iπ) = −𝟙`** — the analytic continuation across the strip
lands on `x ↦ −x` of the boost plane, mapping `W_R` onto `W_L`: the geometric content of BW Eq. 2
(`cosh iπ = cos π = −1`, `sinh iπ = i sin π = 0`). -/
theorem complexBoost_strip_edge :
    complexBoost ((Real.pi : ℂ) * Complex.I) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexBoost, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]

/-- **[The modular conjugation appears at the half strip] `Λ(iπ/2) = i·J`** — halfway across the strip the
continued boost is `i` times the wedge reflection `J = wedgeModularHamiltonian` (`!![0,1;1,0]`): the geometric
origin of `S = JΔ^{1/2}` (`cosh iπ/2 = cos π/2 = 0`, `sinh iπ/2 = i sin π/2 = i`). -/
theorem complexBoost_half_strip :
    complexBoost (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I • wedgeModularHamiltonian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexBoost, Complex.cosh_mul_I, Complex.sinh_mul_I, wedgeModularHamiltonian,
      Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf.bogoliubovGenerator,
      Matrix.map_apply, Matrix.smul_apply]

/-- **[The full Euclidean rotation closes] `Λ(2πi) = 𝟙`** — the matrix-level form of the four-clock `2π`
reading, consistent with `Λ(iπ)² = (−𝟙)² = 𝟙`. -/
theorem complexBoost_full_rotation :
    complexBoost (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexBoost, Complex.cosh_mul_I, Complex.sinh_mul_I]

/-! ## §3. The reflection commutes with the complex flow -/

/-- **[`J` commutes with the entire complex boost flow] `J Λ(z) J = Λ(z)`** — the wedge reflection commutes
with the continued boost (the real-symmetric shadow of `JΔ^{it}J = Δ^{it}` for the antiunitary `J`). -/
theorem reflection_commutes_complexBoost (z : ℂ) :
    wedgeModularHamiltonian * complexBoost z * wedgeModularHamiltonian = complexBoost z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexBoost, wedgeModularHamiltonian,
      Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf.bogoliubovGenerator,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]

/-! ## §4. The duality condition -/

/-- **[The Bisognano–Wichmann duality condition, boost-plane spine]** — the strip continuation reaches the
reflected wedge (`Λ(iπ) = −𝟙`), passes through `i` times the modular conjugation at the half strip
(`Λ(iπ/2) = i·J`), closes at the full rotation (`Λ(2πi) = 𝟙`), commutes with the reflection
(`JΛ(z)J = Λ(z)`) — and the wedge satisfies Tomita–Takesaki Haag duality
(`wedge_tomita_takesaki_haag_duality`, the finite form of the paper's Theorems 3–4,
`𝒜(W_R)' = 𝒜(W_L)`). -/
theorem bisognanoWichmann_duality_condition (z : ℂ) :
    complexBoost ((Real.pi : ℂ) * Complex.I) = -1
      ∧ complexBoost (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I • wedgeModularHamiltonian
      ∧ complexBoost (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1
      ∧ wedgeModularHamiltonian * complexBoost z * wedgeModularHamiltonian = complexBoost z
      ∧ (commutant (wedgeAlgebra wedgeModularHamiltonian)
            = causalComplementAlgebra wedgeModularHamiltonian
          ∧ IsBicommutantClosed (wedgeAlgebra wedgeModularHamiltonian)
          ∧ causalComplementAlgebra wedgeModularHamiltonian
              = modularFixed wedgeModularHamiltonian
          ∧ wedgeModularHamiltonian ∈ wedgeAlgebra wedgeModularHamiltonian) :=
  ⟨complexBoost_strip_edge, complexBoost_half_strip, complexBoost_full_rotation,
    reflection_commutes_complexBoost z, wedge_tomita_takesaki_haag_duality⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition.complexBoost_strip_edge where
  formalizes @ "claim:the-wedge-boost-analytically-continued-to-imaginary-rapidity-pi-is-the-boost-plane-reflection-mapping-the-wedge-onto-its-causal-complement",
  supported_by @ "paper:bisognano-wichmann-1975-duality-condition-hermitian-scalar-field",
  caveat @ "epistemic:boost-plane-geometric-spine-the-operator-valued-distribution-side-of-bw-eq-2-is-the-papers-content"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition.bisognanoWichmann_duality_condition where
  formalizes @ "claim:the-strip-continuation-of-the-wedge-boost-carries-the-duality-condition-edge-reflection-half-strip-conjugation-full-rotation-closure-and-haag-duality",
  requires @ "assumption:bisognano-wichmann-wedge",
  requires @ "claim:the-wedge-boost-analytically-continued-to-imaginary-rapidity-pi-is-the-boost-plane-reflection-mapping-the-wedge-onto-its-causal-complement",
  supported_by @ "paper:bisognano-wichmann-1975-duality-condition-hermitian-scalar-field",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.wedge_tomita_takesaki_haag_duality",
  caveat @ "epistemic:finite-boost-plane-carrier-the-state-side-vacuum-identification-remains-the-assumption"

/- ZIL-END -/

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
public import Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinDoubleDualCotton
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.DAlembertPrinciple

/-!
# Topologically massive gauge theory (Deser–Jackiw–Templeton)

Deser, Jackiw & Templeton, *Topologically massive gauge theories* (Ann. Phys. **140** (1982) 372;
reprinted **281** (2000) 409). In `2+1` dimensions a **gauge-invariant, `P`- and `T`-odd term of
topological (Chern–Simons) origin** gives the gauge field a **mass** — no Higgs field required. The
massless Maxwell excitation (spinless) becomes a massive spin-1 particle; the analogous gravitational
Chern–Simons term gives a massive spin-2 mode. This is the formal backbone of "mass from topology"
(the clock/entropic sector of the complex-action arc).

This module formalizes the algebraic core:

* **§A — the `2+1`D Dirac algebra** (Eq. 2.6). With `γ⁰ = σ³`, `γ¹ = iσ¹`, `γ² = iσ²` and metric
 `g = diag(1,−1,−1)`: `γ⁰² = 1`, `γ¹² = γ²² = −1`, and the three `γ^μ` mutually anticommute — the
 Clifford relation `{γ^μ,γ^ν} = 2g^{μν}` in three dimensions.
* **§B — the mass shell** (from Eq. 2.3b). `(γ·p)² = (p₀²−p₁²−p₂²)·1 = p²·1` (`gammaDot_sq`), so the
 Dirac equation `(γ·p − m)ψ = 0` forces `p² = m²` (`dirac_mass_shell`) — the fermion mass.
* **§C — the topological mass** (Eq. 2.3a). A self-dual (topologically massive) field `μ f = p × f`
 satisfies the second-order Klein–Gordon-type relation `μ² f = −(p·p) f` on the transverse subspace
 (`selfDual_kleinGordon`) — the first-order Chern–Simons equation squares to a massive wave equation
 with mass `μ`, the topological photon mass.
* **§D — `P`, `T`, `CPT` structure** (Eqs. 2.8–2.9). The gauge mass `μ` and the fermion mass `m` are
 both **`P`-odd and `T`-odd** but **`PT`-even** (and `CPT`-even, mass being `C`-even) — they "belong
 together" as the paper stresses (`mass_PT_even`, `mass_CPT_even`).

Proven: the `2+1`D Dirac/Clifford algebra as concrete `2×2` matrices, the mass
shell, the self-dual→Klein–Gordon squaring, and the `P`/`T`/`CPT` sign structure. Interpretive: `§C`
uses the Euclidean 3-cross-product, giving the spatial-reduction form `μ² f = −(p·p) f`; the Lorentzian
`2+1`D completion reads `p² = μ²` (the physical topological-mass dispersion). The gauge-field and
gravitational Chern–Simons actions themselves, and their quantum (IR/UV) properties, are the field-
theory content behind these algebraic facts.

## References

* S. Deser, R. Jackiw, S. Templeton, "Topologically massive gauge theories", Ann. Phys. **140** (1982)
 372, **281** (2000) 409 [`Deser:1982vy`], §II, Eqs. (2.1)–(2.9). Reuses Mathlib `crossProduct`
 (`dot_cross_self`) and matrix/Complex infrastructure.

No additional assumptions.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.DAlembertPrinciple

/-! ## §A — the `2+1`D Dirac algebra (Eq. 2.6) -/

/-- **`γ⁰ = σ³`** (Deser–Jackiw–Templeton Eq. 2.6). -/
noncomputable def γ0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- **`γ¹ = iσ¹`** (Eq. 2.6). -/
noncomputable def γ1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

/-- **`γ² = iσ²`** (Eq. 2.6). -/
noncomputable def γ2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- **`γ⁰² = 1`** (`g^{00} = +1`). -/
theorem γ0_sq : γ0 * γ0 = 1 := by
  unfold γ0; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`γ¹² = −1`** (`g^{11} = −1`). -/
theorem γ1_sq : γ1 * γ1 = -1 := by
  unfold γ1; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- **`γ²² = −1`** (`g^{22} = −1`). -/
theorem γ2_sq : γ2 * γ2 = -1 := by
  unfold γ2; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`{γ⁰,γ¹} = 0`** — the off-diagonal Clifford relation `g^{01} = 0`. -/
theorem γ0_anticomm_γ1 : γ0 * γ1 + γ1 * γ0 = 0 := by
  unfold γ0 γ1; ext i j; fin_cases i <;> fin_cases j <;>
    simp

/-- **`{γ¹,γ²} = 0`** (`g^{12} = 0`). -/
theorem γ1_anticomm_γ2 : γ1 * γ2 + γ2 * γ1 = 0 := by
  unfold γ1 γ2; ext i j; fin_cases i <;> fin_cases j <;>
    simp

/-- **`{γ⁰,γ²} = 0`** (`g^{02} = 0`). -/
theorem γ0_anticomm_γ2 : γ0 * γ2 + γ2 * γ0 = 0 := by
  unfold γ0 γ2; ext i j; fin_cases i <;> fin_cases j <;>
    simp

/-- **Abstract three-generator Clifford square.** If three operators square to scalar metric components
`qᵢ·1` and mutually anticommute, then their momentum contraction squares to the scalar quadratic form.
This is the common algebraic engine behind the DJT `2+1`D square and the repository's higher-dimensional
Dirac mass-shell squares: anticommutators kill the cross terms. -/
theorem threeTermCliffordSquare {α : Type*} [Fintype α] [DecidableEq α]
    (M0 M1 M2 : Matrix α α ℂ) (p0 p1 p2 q0 q1 q2 : ℂ)
    (h0 : M0 * M0 = q0 • (1 : Matrix α α ℂ))
    (h1 : M1 * M1 = q1 • (1 : Matrix α α ℂ))
    (h2 : M2 * M2 = q2 • (1 : Matrix α α ℂ))
    (h01 : M0 * M1 + M1 * M0 = 0)
    (h02 : M0 * M2 + M2 * M0 = 0)
    (h12 : M1 * M2 + M2 * M1 = 0) :
    (p0 • M0 + p1 • M1 + p2 • M2) * (p0 • M0 + p1 • M1 + p2 • M2)
      = (p0 ^ 2 * q0 + p1 ^ 2 * q1 + p2 ^ 2 * q2) • (1 : Matrix α α ℂ) := by
  have h01r : M1 * M0 = -(M0 * M1) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using h01
  have h02r : M2 * M0 = -(M0 * M2) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using h02
  have h12r : M2 * M1 = -(M1 * M2) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using h12
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h0, h1, h2, h01r, h02r, h12r,
    smul_add, smul_neg, smul_smul]
  module

/-! ## §B — the mass shell (Eq. 2.3b) -/

/-- **The contracted momentum operator** `γ·p = p₀γ⁰ + p₁γ¹ + p₂γ²`. -/
noncomputable def gammaDot (p0 p1 p2 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  p0 • γ0 + p1 • γ1 + p2 • γ2

/-- **The contracted operator in explicit form** `γ·p = !![p₀, p₂+ip₁; −p₂+ip₁, −p₀]` — a traceless
`2×2` matrix. -/
theorem gammaDot_eq (p0 p1 p2 : ℂ) :
    gammaDot p0 p1 p2 = !![p0, p2 + Complex.I * p1; -p2 + Complex.I * p1, -p0] := by
  unfold gammaDot γ0 γ1 γ2
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply] <;> ring

/-- **A traceless `2×2` matrix squares to a scalar** `!![a,b;c,−a]² = (a² + bc)·1` (Cayley–Hamilton for a
traceless matrix). -/
theorem traceless_sq (a b c : ℂ) :
    !![a, b; c, -a] * !![a, b; c, -a] = (a ^ 2 + b * c) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The mass-shell identity** `(γ·p)² = (p₀²−p₁²−p₂²)·1 = p²·1` (Deser–Jackiw–Templeton): squaring the
Dirac operator contracts the momenta with the Minkowski metric `g = diag(1,−1,−1)`, killing the
antisymmetric `ε`-part. Hence the Dirac equation `(γ·p − m)ψ = 0` puts the fermion on the mass shell
`p² = m²`. -/
theorem gammaDot_sq (p0 p1 p2 : ℂ) :
    gammaDot p0 p1 p2 * gammaDot p0 p1 p2
      = (p0 ^ 2 - p1 ^ 2 - p2 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h0 : γ0 * γ0 = ((1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simpa using γ0_sq
  have h1 : γ1 * γ1 = ((-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simpa using γ1_sq
  have h2 : γ2 * γ2 = ((-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simpa using γ2_sq
  have h := threeTermCliffordSquare γ0 γ1 γ2 p0 p1 p2 (1 : ℂ) (-1 : ℂ) (-1 : ℂ)
    h0 h1 h2 γ0_anticomm_γ1 γ0_anticomm_γ2 γ1_anticomm_γ2
  simpa [gammaDot, sub_eq_add_neg] using h

/-! ## §C — the topological mass (Eq. 2.3a) -/

/-- **The self-dual field is transverse** `p·f = 0` (Deser–Jackiw–Templeton): the topologically massive
self-duality `μ f = p × f` forces the field orthogonal to the momentum, since `p·(p × f) = 0`. -/
theorem selfDual_transverse (μ : ℝ) (p f : Fin 3 → ℝ) (hμ : μ ≠ 0)
    (hsd : μ • f = p ⨯₃ f) : p ⬝ᵥ f = 0 := by
  have h0 : p ⬝ᵥ (p ⨯₃ f) = 0 := by
    simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring
  rw [← hsd, dotProduct_smul, smul_eq_mul] at h0
  exact (mul_eq_zero.mp h0).resolve_left hμ

/-- **The double cross-product** `p × (p × f) = (p·f) p − (p·p) f` (the `BAC–CAB` / 3D `ε`-`ε`
identity). -/
theorem cross_cross (p f : Fin 3 → ℝ) :
    p ⨯₃ (p ⨯₃ f) = (p ⬝ᵥ f) • p - (p ⬝ᵥ p) • f := by
  ext i
  fin_cases i <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply] <;> ring

/-- **The topological mass is Klein–Gordon** `μ² f = −(p·p) f` (Deser–Jackiw–Templeton Eq. 2.3a): the
first-order self-duality `μ f = p × f` (the Chern–Simons/topological mass equation) **squares** to a
second-order massive wave equation. The Chern–Simons term thus gives the gauge field a mass `μ` with a
single Klein–Gordon mode — no Higgs. (Lorentzian `2+1`D completion: `p² = μ²`.) -/
theorem selfDual_kleinGordon (μ : ℝ) (p f : Fin 3 → ℝ) (hμ : μ ≠ 0)
    (hsd : μ • f = p ⨯₃ f) :
    (μ ^ 2) • f = -(p ⬝ᵥ p) • f := by
  have htr : p ⬝ᵥ f = 0 := selfDual_transverse μ p f hμ hsd
  have h2 : (μ ^ 2) • f = p ⨯₃ (p ⨯₃ f) := by
    have hpp : p ⨯₃ (p ⨯₃ f) = p ⨯₃ (μ • f) := by rw [hsd]
    rw [hpp, map_smul, ← hsd, smul_smul, ← pow_two]
  rw [h2, cross_cross, htr, zero_smul, zero_sub, neg_smul]

/-! ## §D — `P`, `T`, `CPT` structure of the mass terms (Eqs. 2.8–2.9) -/

/-- **The parity sign of a mass term** `−1` (Eq. 2.8): both the gauge mass `μ` and the fermion mass `m`
flip sign under a parity transformation. -/
def massSignParity : ℤ := -1

/-- **The time-reversal sign of a mass term** `−1` (Eq. 2.9). -/
def massSignTime : ℤ := -1

/-- **The charge-conjugation sign of a mass term** `+1` — the mass is `C`-even. -/
def massSignCharge : ℤ := 1

/-- **The mass terms are `PT`-even** (Deser–Jackiw–Templeton): both `μ` and `m` are `P`-odd and `T`-odd,
so the combined `PT` leaves them invariant — the topological gauge mass and the fermion mass "belong
together". -/
theorem mass_PT_even : massSignParity * massSignTime = 1 := by decide

/-- **The mass terms are `CPT`-even** — `C`-even, `P`-odd, `T`-odd multiply to `+1`, the discrete
symmetry that any local field theory must respect. -/
theorem mass_CPT_even : massSignCharge * massSignParity * massSignTime = 1 := by decide

/-! ## §E — bridge to the repository DJT level normalization -/

/-- **Signed Chern–Simons mass parameter.** The older DJT file records the physical mass as the
non-negative magnitude `e² |k|/(2π)`. The first-order self-dual equation uses the signed parameter
`μ = e² k/(2π)`, whose sign is the `P`/`T`-odd datum. -/
noncomputable def signedChernSimonsMass (dj : DJTData) : ℝ :=
  dj.e ^ 2 * (dj.level : ℝ) / (2 * Real.pi)

/-- **The repository DJT topological mass is the magnitude of the signed self-dual mass.** This is the
precise bridge between this module's `μ` and `ChernSimons.TopologicalMassDJT.topologicalMass`. -/
theorem abs_signedChernSimonsMass_eq_topologicalMass (dj : DJTData) :
    |signedChernSimonsMass dj| = topologicalMass dj := by
  have hden_pos : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  unfold signedChernSimonsMass topologicalMass
  rw [abs_div, abs_of_pos hden_pos, abs_mul, abs_of_nonneg (sq_nonneg dj.e)]

/-- **Orientation/level reversal flips the signed mass.** This is the algebraic part of the
`P`/`T`-odd statement: reversing the Chern–Simons level changes `μ` to `-μ`. -/
theorem signedChernSimonsMass_negLevel (dj : DJTData) :
    signedChernSimonsMass { e := dj.e, level := -dj.level } = -signedChernSimonsMass dj := by
  unfold signedChernSimonsMass
  simp
  ring_nf

/-- **Orientation/level reversal leaves the physical mass magnitude invariant.** -/
theorem topologicalMass_negLevel (dj : DJTData) :
    topologicalMass { e := dj.e, level := -dj.level } = topologicalMass dj := by
  unfold topologicalMass
  simp

/-- **The existing DJT level mass can be used directly in the self-dual/Klein–Gordon bridge.** If the
signed Chern–Simons mass `μ = e²k/(2π)` satisfies the first-order self-dual equation, then the
second-order equation has mass squared equal to the square of the existing repository mass
`topologicalMass = |μ|`. -/
theorem selfDual_kleinGordon_at_DJTLevel (dj : DJTData) (p f : Fin 3 → ℝ)
    (hμ : signedChernSimonsMass dj ≠ 0)
    (hsd : signedChernSimonsMass dj • f = p ⨯₃ f) :
    (topologicalMass dj ^ 2) • f = -(p ⬝ᵥ p) • f := by
  have hkg := selfDual_kleinGordon (signedChernSimonsMass dj) p f hμ hsd
  have hsq : topologicalMass dj ^ 2 = signedChernSimonsMass dj ^ 2 := by
    rw [← abs_signedChernSimonsMass_eq_topologicalMass dj, sq_abs]
  rw [hsq]
  exact hkg

/-! ## §F — Maxwell/Yang--Mills--Chern--Simons equations -/

variable {X ι 𝔤 : Type*}

/-- **The DJT dual field strength** `*F^ν`, represented as the one-index current-shaped object already used
by the Yang--Mills layer. -/
abbrev GaugeDualCurvature (X ι 𝔤 : Type*) := GaugeCurrent X ι 𝔤

/-- **The Chern--Simons mass current** `μ *F^ν`. This is the additional term in
`D_μ F^{μν} + μ *F^ν = J^ν`. -/
def chernSimonsMassCurrent [SMul ℝ 𝔤]
    (dualF : GaugeDualCurvature X ι 𝔤) (μ : ℝ) : GaugeCurrent X ι 𝔤 :=
  fun x ν => μ • dualF x ν

/-- **Deser--Jackiw--Templeton Yang--Mills--Chern--Simons equation**
`D_μ F^{μν} + μ *F^ν = J^ν` (non-Abelian §III, Abelian §II after commutative reduction). -/
def TopologicallyMassiveYangMillsEquation [Fintype ι] [Ring 𝔤] [Module ℝ 𝔤]
    (deriv : GaugePartial X ι 𝔤)
    (A : GaugePotential X ι 𝔤) (F : GaugeCurvature X ι 𝔤)
    (dualF : GaugeDualCurvature X ι 𝔤) (J : GaugeCurrent X ι 𝔤) (μ : ℝ) : Prop :=
  ∀ (ν : ι) (x : X),
    yangMillsDivergence deriv A F ν x + chernSimonsMassCurrent dualF μ x ν = J x ν

/-- **Zero topological mass gives ordinary Yang--Mills.** This is the exact algebraic reduction
`D_μF^{μν}+0*F^ν=J^ν ↔ D_μF^{μν}=J^ν`. -/
theorem topologicallyMassiveYangMills_zeroMass_iff_yangMills [Fintype ι] [Ring 𝔤] [Module ℝ 𝔤]
    (deriv : GaugePartial X ι 𝔤)
    (A : GaugePotential X ι 𝔤) (F : GaugeCurvature X ι 𝔤)
    (dualF : GaugeDualCurvature X ι 𝔤) (J : GaugeCurrent X ι 𝔤) :
    TopologicallyMassiveYangMillsEquation deriv A F dualF J 0 ↔
      YangMillsEquation deriv A F J := by
  constructor
  · intro h ν x
    have hx := h ν x
    simpa [TopologicallyMassiveYangMillsEquation, chernSimonsMassCurrent] using hx
  · intro h ν x
    have hx := h ν x
    simpa [TopologicallyMassiveYangMillsEquation, chernSimonsMassCurrent] using hx

/-- **Move the Chern--Simons term to the source side.** The DJT equation is exactly ordinary
Yang--Mills with shifted current `J^ν - μ *F^ν`. -/
theorem topologicallyMassiveYangMills_iff_yangMills_shiftedCurrent [Fintype ι] [Ring 𝔤] [Module ℝ 𝔤]
    (deriv : GaugePartial X ι 𝔤)
    (A : GaugePotential X ι 𝔤) (F : GaugeCurvature X ι 𝔤)
    (dualF : GaugeDualCurvature X ι 𝔤) (J : GaugeCurrent X ι 𝔤) (μ : ℝ) :
    TopologicallyMassiveYangMillsEquation deriv A F dualF J μ ↔
      YangMillsEquation deriv A F (fun x ν => J x ν - chernSimonsMassCurrent dualF μ x ν) := by
  constructor
  · intro h ν x
    have hx := h ν x
    dsimp
    rw [← hx]
    abel_nf
  · intro h ν x
    have hx := h ν x
    dsimp at hx
    rw [hx]
    abel_nf

/-- **The Abelian Maxwell--Chern--Simons equation** in the existing coordinate Maxwell/Yang--Mills API.
The curvature is not duplicated: it is `yangMillsCurvature`, whose real commutative specialization is already
proved to be the coordinate Faraday tensor. -/
def MaxwellChernSimonsFlatPotential [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (dualF : GaugeDualCurvature (CoordinateVector ι) ι ℝ) (J : CoordinateCurrent ι) (μ : ℝ) : Prop :=
  TopologicallyMassiveYangMillsEquation
    (X := CoordinateVector ι) (ι := ι) (𝔤 := ℝ)
    coordDeriv A
    (yangMillsCurvature
      (X := CoordinateVector ι) (ι := ι) (𝔤 := ℝ) coordDeriv A)
    dualF J μ

/-- **Zero CS mass recovers the existing flat Maxwell potential equation.** This closes the Abelian DJT
equation back into `CoordinateMaxwellEinstein.MaxwellInhomogeneousFlatPotential`. -/
theorem maxwellChernSimons_zeroMass_iff_maxwellFlatPotential [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (dualF : GaugeDualCurvature (CoordinateVector ι) ι ℝ) (J : CoordinateCurrent ι) :
    MaxwellChernSimonsFlatPotential coordDeriv A dualF J 0 ↔
      MaxwellInhomogeneousFlatPotential coordDeriv A J := by
  unfold MaxwellChernSimonsFlatPotential
  rw [topologicallyMassiveYangMills_zeroMass_iff_yangMills]
  exact yangMillsPotentialEquation_real_iff_maxwellFlatPotential coordDeriv A J

/-! ## §G — non-Abelian large-gauge quantization -/

/-- **DJT non-Abelian level** `4π μ / g²`. In the paper, large gauge invariance requires this real number
to be an integer. -/
noncomputable def nonAbelianChernSimonsLevel (μ g : ℝ) : ℝ :=
  4 * Real.pi * μ / g ^ 2

/-- **Large-gauge quantization condition** `4π μ / g² ∈ ℤ`. -/
def NonAbelianChernSimonsQuantized (μ g : ℝ) : Prop :=
  ∃ n : ℤ, nonAbelianChernSimonsLevel μ g = n

/-- **DJT large-gauge action shift** `(8π² μ/g²) w`, for winding number `w`. -/
noncomputable def djtLargeGaugeActionShift (μ g : ℝ) (w : ℤ) : ℝ :=
  (8 * Real.pi ^ 2 * μ / g ^ 2) * (w : ℝ)

/-- **Quantized level makes the large-gauge action shift a `2π` multiple.** This is the algebra behind
the paper's condition `4π μ/g² = n`: the shift is `2π n w`. -/
theorem djtLargeGaugeActionShift_eq_twoPi_integer
    {μ g : ℝ} {n w : ℤ} (hlevel : nonAbelianChernSimonsLevel μ g = (n : ℝ)) :
    djtLargeGaugeActionShift μ g w = 2 * Real.pi * ((n * w : ℤ) : ℝ) := by
  unfold djtLargeGaugeActionShift nonAbelianChernSimonsLevel at *
  calc
    (8 * Real.pi ^ 2 * μ / g ^ 2) * (w : ℝ)
        = (2 * Real.pi) * (4 * Real.pi * μ / g ^ 2) * (w : ℝ) := by ring_nf
    _ = (2 * Real.pi) * (n : ℝ) * (w : ℝ) := by rw [hlevel]
    _ = 2 * Real.pi * ((n * w : ℤ) : ℝ) := by
      rw [Int.cast_mul]
      ring

/-- **Quantized DJT data produce integer `2π` action shifts for every winding number.** -/
theorem djtLargeGaugeActionShift_quantized
    {μ g : ℝ} (hquant : NonAbelianChernSimonsQuantized μ g) :
    ∃ n : ℤ, ∀ w : ℤ,
      djtLargeGaugeActionShift μ g w = 2 * Real.pi * ((n * w : ℤ) : ℝ) := by
  rcases hquant with ⟨n, hlevel⟩
  exact ⟨n, fun w => djtLargeGaugeActionShift_eq_twoPi_integer (μ := μ) (g := g) (n := n) hlevel⟩

/-- **Non-Abelian DJT mass at integer level** `|μ| = g² |n|/(4π)`. -/
noncomputable def nonAbelianTopologicalMassFromLevel (g : ℝ) (n : ℤ) : ℝ :=
  g ^ 2 * |(n : ℝ)| / (4 * Real.pi)

/-- **The quantization condition solves for the signed mass parameter**:
`4π μ/g² = n` implies `μ = g² n/(4π)`, at nonzero gauge coupling. -/
theorem nonAbelianLevel_solves_signedMass
    {μ g : ℝ} {n : ℤ} (hg : g ≠ 0)
    (hlevel : nonAbelianChernSimonsLevel μ g = (n : ℝ)) :
    μ = g ^ 2 * (n : ℝ) / (4 * Real.pi) := by
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have hden : 4 * Real.pi ≠ 0 := ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  unfold nonAbelianChernSimonsLevel at hlevel
  calc
    μ = (4 * Real.pi * μ / g ^ 2) * g ^ 2 / (4 * Real.pi) := by
      field_simp [hg2, hden]
    _ = (n : ℝ) * g ^ 2 / (4 * Real.pi) := by rw [hlevel]
    _ = g ^ 2 * (n : ℝ) / (4 * Real.pi) := by ring

/-- **The quantized non-Abelian topological mass magnitude.** At nonzero coupling and integer level,
the physical mass is `g² |n|/(4π)`. -/
theorem abs_signedMass_eq_nonAbelianTopologicalMassFromLevel
    {μ g : ℝ} {n : ℤ} (hg : g ≠ 0)
    (hlevel : nonAbelianChernSimonsLevel μ g = (n : ℝ)) :
    |μ| = nonAbelianTopologicalMassFromLevel g n := by
  have hden_pos : (0 : ℝ) < 4 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [nonAbelianLevel_solves_signedMass (μ := μ) (g := g) (n := n) hg hlevel]
  unfold nonAbelianTopologicalMassFromLevel
  rw [abs_div, abs_of_pos hden_pos, abs_mul, abs_of_nonneg (sq_nonneg g)]

/-! ## §H — topologically massive gravity equation -/

/-- **Topologically massive gravity equation** `G + μ⁻¹ C = κ T`, the algebraic form of
Deser--Jackiw--Templeton §IV. Here `C` is the Cotton/York tensor structure supplied as a two-index matrix. -/
def TopologicallyMassiveGravityEquation {ι : Type*}
    (G C T : Matrix ι ι ℝ) (μ κ : ℝ) : Prop :=
  G + μ⁻¹ • C = κ • T

/-- **With no Cotton term, TMG is exactly Einstein's equation** `G = κT`. -/
theorem topologicallyMassiveGravity_noCotton_iff_einstein {ι : Type*}
    (G T : Matrix ι ι ℝ) (μ κ : ℝ) :
    TopologicallyMassiveGravityEquation G 0 T μ κ ↔ G = κ • T := by
  unfold TopologicallyMassiveGravityEquation
  simp

/-- **Vacuum TMG component balance** `Gᵢⱼ = - μ⁻¹ Cᵢⱼ`. -/
theorem topologicallyMassiveGravity_vacuum_component_balance {ι : Type*}
    (G C : Matrix ι ι ℝ) (μ κ : ℝ)
    (h : TopologicallyMassiveGravityEquation G C 0 μ κ) (i j : ι) :
    G i j = - μ⁻¹ * C i j := by
  unfold TopologicallyMassiveGravityEquation at h
  have hc := congrArg (fun M : Matrix ι ι ℝ => M i j) h
  simp at hc
  linarith

/-- **Vacuum TMG with zero Cotton tensor gives vacuum Einstein** `G=0`. -/
theorem topologicallyMassiveGravity_vacuum_cottonZero_implies_einsteinZero {ι : Type*}
    (G C : Matrix ι ι ℝ) (μ κ : ℝ)
    (h : TopologicallyMassiveGravityEquation G C 0 μ κ) (hC : C = 0) :
    G = 0 := by
  ext i j
  have hb := topologicallyMassiveGravity_vacuum_component_balance G C μ κ h i j
  simpa [hC] using hb

/-- **Repository Cotton infrastructure link.** The three-index Cotton tensor already available in the
curvature layer has the antisymmetry used by Chern--Simons gravity constructions. The DJT two-index
Cotton/York tensor is a contraction/dualization of this kind of Cotton structure; this theorem records the
checked reusable identity rather than duplicating it. -/
theorem djt_threeIndexCotton_antisymm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℝ) (g : Matrix ι ι ℝ) (nablaRic : ι → ι → ι → ℝ) (nablaR : ι → ℝ)
    (j k l : ι) :
    cottonTensor n g nablaRic nablaR j k l =
      -cottonTensor n g nablaRic nablaR j l k :=
  cottonTensor_antisymm n g nablaRic nablaR j k l

/-! ## §I — BCJ, Compton/winding, and Levi-Civita inertia bridges -/

/-- **The Abelian DJT Bianchi identity is a BCJ kinematic Jacobi identity.** The Chern--Simons mass term
changes the inhomogeneous equation, while the homogeneous Maxwell/Faraday identity still supplies the
BCJ numerator relation `n_s+n_t+n_u=0`. -/
theorem djt_faradayBCJ_kinematic_jacobi (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (c_s c_t c_u : ℝ) (hcolor : c_s + c_t + c_u = 0) :
    (faradayBCJDuality k A lam μ ν c_s c_t c_u hcolor).n_s
      + (faradayBCJDuality k A lam μ ν c_s c_t c_u hcolor).n_t
      + (faradayBCJDuality k A lam μ ν c_s c_t c_u hcolor).n_u = 0 :=
  (faradayBCJDuality k A lam μ ν c_s c_t c_u hcolor).kinematic_jacobi

/-- The three Faraday numerators used by the Abelian DJT/BCJ bridge. -/
noncomputable def djtFaradayBCJNumerator (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) : Fin 3 → ℝ
  | 0 => k lam * faraday k A μ ν
  | 1 => k μ * faraday k A ν lam
  | 2 => k ν * faraday k A lam μ

/-- The one-row DDM matrix that tests the Jacobi sum of three numerators. -/
def djtBCJJacobiRow : PUnit → Fin 3 → ℝ := fun _ _ => 1

/-- **Faraday/Bianchi numerators are a DDM generalized-gauge kernel vector.** This is the non-cosmetic BCJ
content of the DJT bridge: the homogeneous Maxwell identity gives an actual kinematic numerator vector in
the kernel of the Jacobi-row propagator matrix. -/
theorem djt_faradayBCJ_numerator_in_jacobi_kernel (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) :
    InPropagatorKernel djtBCJJacobiRow (djtFaradayBCJNumerator k A lam μ ν) := by
  intro s
  simpa [partialAmplitudeFromPropagatorMatrix, djtBCJJacobiRow, djtFaradayBCJNumerator,
    Fin.sum_univ_three] using faraday_bianchi k A lam μ ν

/-- **The DJT/Faraday BCJ numerator can be used as a generalized-gauge shift.** Because the Faraday
numerator vector is in the DDM Jacobi kernel, adding it to any numerator vector preserves the Jacobi-row
partial amplitude. -/
theorem djt_faradayBCJ_kernel_shift_preserves_partialAmplitude
    (N : Fin 3 → ℝ) (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) :
    partialAmplitudeFromPropagatorMatrix djtBCJJacobiRow
        (fun i => N i + djtFaradayBCJNumerator k A lam μ ν i) PUnit.unit =
      partialAmplitudeFromPropagatorMatrix djtBCJJacobiRow N PUnit.unit :=
  partialAmplitude_shift_by_kernel djtBCJJacobiRow N (djtFaradayBCJNumerator k A lam μ ν)
    (djt_faradayBCJ_numerator_in_jacobi_kernel k A lam μ ν) PUnit.unit

/-- **Every DJT topological mass has its Compton clock.** This is the exact inverse
`m = ħω_C/c²`, with `m` instantiated by the existing repository `topologicalMass`. -/
theorem djtTopologicalMass_eq_comptonMass_comptonFrequency
    (dj : DJTData) (c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    topologicalMass dj =
      comptonMass (comptonFrequency (topologicalMass dj) c ħ) c ħ :=
  (comptonMass_comptonFrequency (topologicalMass dj) c ħ hc hħ).symm

/-- **DJT topological mass plugged into the `3+1`D Dirac Hamiltonian mass shell.** This is the
`diracHamiltonian4_sq_comptonMass` theorem with the mass chosen to be the DJT topological mass through
its Compton clock. -/
theorem djtTopologicalMass_diracHamiltonian4_sq
    (dj : DJTData) (p1 p2 p3 c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    diracHamiltonian4 p1 p2 p3 (topologicalMass dj)
      * diracHamiltonian4 p1 p2 p3 (topologicalMass dj)
        = ((p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + topologicalMass dj ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hcm := comptonMass_comptonFrequency (topologicalMass dj) c ħ hc hħ
  rw [← hcm]
  exact diracHamiltonian4_sq_comptonMass p1 p2 p3
    (comptonFrequency (topologicalMass dj) c ħ) c ħ

/-- **The conditional winding bridge.** If the Compton clock of the DJT topological mass is the winding
frequency `ω_n = nω₀`, then the DJT field mass is exactly the winding mass. This theorem isolates the real
remaining hypothesis: the frequency/winding identification. -/
theorem djtTopologicalMass_eq_windingMass_of_comptonClock_eq_windingFrequency
    (dj : DJTData) (n : ℤ) (ω₀ c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hω : comptonFrequency (topologicalMass dj) c ħ = windingFrequency n ω₀) :
    topologicalMass dj = windingMass n ω₀ c ħ := by
  rw [← comptonMass_comptonFrequency (topologicalMass dj) c ħ hc hħ]
  unfold windingMass
  rw [← hω]

/-- **Chern--Simons level quantization derives the winding clock.** If the non-Abelian DJT level is the
nonnegative integer `n`, then the Compton clock of the physical mass magnitude is the winding frequency
with one level-unit clock `ω₀ = ω_C(g²/(4π))`. This discharges the frequency hypothesis in the winding
bridge from the already-proven large-gauge quantization algebra. Negative level is the opposite
orientation; the physical mass uses the magnitude. -/
theorem nonAbelianLevel_comptonFrequency_eq_windingFrequency
    {μ g : ℝ} {n : ℤ} (c ħ : ℝ) (hg : g ≠ 0) (hħ : ħ ≠ 0)
    (hn : 0 ≤ (n : ℝ))
    (hlevel : nonAbelianChernSimonsLevel μ g = (n : ℝ)) :
    comptonFrequency |μ| c ħ =
      windingFrequency n (comptonFrequency (g ^ 2 / (4 * Real.pi)) c ħ) := by
  have hden_pos : (0 : ℝ) < 4 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hμ : μ = g ^ 2 * (n : ℝ) / (4 * Real.pi) :=
    nonAbelianLevel_solves_signedMass (μ := μ) (g := g) (n := n) hg hlevel
  rw [hμ]
  have habs : |g ^ 2 * (n : ℝ) / (4 * Real.pi)| = g ^ 2 * (n : ℝ) / (4 * Real.pi) := by
    exact abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg g) hn) hden_pos.le)
  rw [habs]
  unfold comptonFrequency windingFrequency
  field_simp [hħ]

/-- **Quantized non-Abelian CS mass equals a winding mass.** With the level-unit clock
`ω₀ = ω_C(g²/(4π))`, large-gauge quantization gives `|μ| = windingMass n ω₀ c ħ` for nonnegative level
`n`; the winding spectrum is no longer an independent hypothesis in this case. -/
theorem nonAbelianLevel_absMass_eq_windingMass
    {μ g : ℝ} {n : ℤ} (c ħ : ℝ) (hg : g ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hn : 0 ≤ (n : ℝ))
    (hlevel : nonAbelianChernSimonsLevel μ g = (n : ℝ)) :
    |μ| = windingMass n (comptonFrequency (g ^ 2 / (4 * Real.pi)) c ħ) c ħ := by
  rw [← comptonMass_comptonFrequency |μ| c ħ hc hħ]
  unfold windingMass
  rw [nonAbelianLevel_comptonFrequency_eq_windingFrequency (μ := μ) (g := g) (n := n)
    c ħ hg hħ hn hlevel]

/-- **DJT signed mass: quantized level supplies the winding-clock hypothesis.** This is the concrete
§G→§I fusion: once `signedChernSimonsMass dj` has non-Abelian level `n ≥ 0`, the Compton clock of
`topologicalMass dj` is the winding clock with fundamental unit `ω_C(g²/(4π))`. -/
theorem djtTopologicalMass_comptonFrequency_eq_quantizedWindingFrequency
    (dj : DJTData) {g : ℝ} {n : ℤ} (c ħ : ℝ) (hg : g ≠ 0) (hħ : ħ ≠ 0)
    (hn : 0 ≤ (n : ℝ))
    (hlevel : nonAbelianChernSimonsLevel (signedChernSimonsMass dj) g = (n : ℝ)) :
    comptonFrequency (topologicalMass dj) c ħ =
      windingFrequency n (comptonFrequency (g ^ 2 / (4 * Real.pi)) c ħ) := by
  rw [← abs_signedChernSimonsMass_eq_topologicalMass dj]
  exact nonAbelianLevel_comptonFrequency_eq_windingFrequency
    (μ := signedChernSimonsMass dj) (g := g) (n := n) c ħ hg hħ hn hlevel

/-- **DJT topological mass as a derived winding mass.** The previous conditional bridge becomes derived
when its clock equation is supplied by non-Abelian Chern--Simons level quantization. -/
theorem djtTopologicalMass_eq_quantizedWindingMass_of_nonAbelianLevel
    (dj : DJTData) {g : ℝ} {n : ℤ} (c ħ : ℝ) (hg : g ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hn : 0 ≤ (n : ℝ))
    (hlevel : nonAbelianChernSimonsLevel (signedChernSimonsMass dj) g = (n : ℝ)) :
    topologicalMass dj =
      windingMass n (comptonFrequency (g ^ 2 / (4 * Real.pi)) c ħ) c ħ := by
  rw [← abs_signedChernSimonsMass_eq_topologicalMass dj]
  exact nonAbelianLevel_absMass_eq_windingMass
    (μ := signedChernSimonsMass dj) (g := g) (n := n) c ħ hg hc hħ hn hlevel

/-- **Signed DJT mass fused to a winding mass, conditionally on the frequency map.** This is the exact
statement `|μ_CS| = m_n` once `ω_C(|μ_CS|)=ω_n` is supplied. -/
theorem abs_signedChernSimonsMass_eq_windingMass_of_comptonClock_eq_windingFrequency
    (dj : DJTData) (n : ℤ) (ω₀ c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hω : comptonFrequency (topologicalMass dj) c ħ = windingFrequency n ω₀) :
    |signedChernSimonsMass dj| = windingMass n ω₀ c ħ := by
  rw [abs_signedChernSimonsMass_eq_topologicalMass]
  exact djtTopologicalMass_eq_windingMass_of_comptonClock_eq_windingFrequency
    dj n ω₀ c ħ hc hħ hω

/-- **The DJT field equation at the Compton clock mass.** The self-dual topological equation squares to the
same Klein--Gordon mass term written as `comptonMass ω_C`. This is the spatial-reduction sign convention
`μ² f = −(p·p)f`; the Lorentzian `2+1`D dispersion reads `p² = μ²`. -/
theorem selfDual_kleinGordon_at_DJTComptonClock (dj : DJTData) (p f : Fin 3 → ℝ)
    (c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hμ : signedChernSimonsMass dj ≠ 0)
    (hsd : signedChernSimonsMass dj • f = p ⨯₃ f) :
    (comptonMass (comptonFrequency (topologicalMass dj) c ħ) c ħ ^ 2) • f =
      -(p ⬝ᵥ p) • f := by
  rw [comptonMass_comptonFrequency (topologicalMass dj) c ħ hc hħ]
  exact selfDual_kleinGordon_at_DJTLevel dj p f hμ hsd

/-- **No-Cotton topologically massive gravity falls through to Levi-Civita d'Alembert inertia.** When the
Cotton/York sector is zero, the TMG equation is Einstein's equation, so the Levi-Civita lost tensor
`T + A` vanishes. -/
theorem topologicallyMassiveGravity_noCotton_leviCivita_dAlembert {ι : Type*}
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ) (massμ κ : ℝ)
    (hκ : κ ≠ 0)
    (hTMG : TopologicallyMassiveGravityEquation (einsteinTensor Ric scalarR g) 0 T massμ κ) :
    DAlembertPrinciple T (gravitationalTensor Ric scalarR g κ)
      ∧ gravitationalTensor Ric scalarR g κ = -T
      ∧ ∀ i j, T i j + (gravitationalTensor Ric scalarR g κ) i j = 0 := by
  have hEFE : einsteinFieldEquation Ric scalarR g T κ :=
    (topologicallyMassiveGravity_noCotton_iff_einstein (einsteinTensor Ric scalarR g) T massμ κ).1 hTMG
  exact leviCivita_dAlembert_principle Ric scalarR g T κ hκ hEFE

end Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge

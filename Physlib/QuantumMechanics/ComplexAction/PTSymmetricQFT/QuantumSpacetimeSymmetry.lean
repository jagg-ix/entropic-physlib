/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.HyperbolicInterval
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.FisherQuantumPotential

/-!
# Greaves–Thomas §2.4: equations (12)–(13) — quantum spacetime symmetry ⟺ `[ρω]_q`-invariance of `D^form`

Formalizes the §2.4 reduction of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674): a quantum
field theory `D` is specified by a formal field theory `D^form` (12), and — given (12) — **`G` acts by
spacetime symmetries on `D` (13) iff `D^form` is `[ρω]_q(G)`-invariant**. So the existence of quantum
spacetime symmetries reduces to the invariance of a *formal* field theory, where the theorems of this arc
(`PTSymmetricQFT.FieldFormulaDuality`, `PTSymmetricQFT.TemporalOrientation`) apply.

Here `[ρω]_q` is the quantum geometric action of `PTSymmetricQFT.TemporalOrientation` — `ℂ`-linear (unitary)
for time-preserving `g`, `ℂ`-antilinear (antiunitary) for time-reversing `g` (Wigner).

* **§A — equations (12)–(13)** (`qLargest`, `mem_qLargest`, `form_invariant_of_spacetime_symmetry`). With
  `D = quantumDynamics evv D^form` the field theory defined by `D^form` (12), the two directions of (13):
  - **`D^form`-invariance ⟹ spacetime symmetry** is `PTSymmetricQFT.QuantumSymmetry.symmetry_preserves_dynamics`
    (the formula automorphism `σ` preserving `D^form` makes the field transformation `T` a symmetry of `D`).
  - **spacetime symmetry ⟹ `D^form`-invariance** (`form_invariant_of_spacetime_symmetry`, new): if a
    *bijective* field transformation `T` is a symmetry of `D`, then `σ` preserves the **largest** formal
    field theory `qLargest evv D = ⋂_{φ∈D} ker(realize Φ)` — the canonical `D^form` of `D`.

  Together these are the §2.4 equivalence (13) ⟺ `[ρω]_q(G)`-invariance of `D^form`.
* **§B — temporal orientation meets the lapse interval** (`timeReversal_lapse`, `lorentzianForm_timeReversal`,
  `lapse_timeReversal_massShell`). The time-reversing conjugation `conjFactor true = conj` of
  `PTSymmetricQFT.TemporalOrientation` acts on the Banihashemi–Jacobson lapse
  `complexEnergy N ε = N − iε` of `GravLapse.HyperbolicInterval` by reversing the displacement,
  `N − iε ↦ N + iε` (`ε ↦ −ε`); and the Minkowski interval `lorentzianForm` — the mass shell `Δ²` — is
  **invariant** under it. So the antiunitary time reversal is the complex conjugation of the lapse contour,
  and the diamond/boost mass shell is time-reversal invariant: the time-reversed lapse sits on the *same*
  hyperbolic spacetime interval (`lapse_timeReversal_massShell`, consuming
  `GravLapse.HyperbolicInterval.lapse_on_massShell`).
* **§C — the Jacobson causal diamond** (`timeReversal_diamond_mode`, `diamond_energy_timeReversal_invariant`,
  `diamond_velocity_timeReversal`). Time reversal maps the diamond Bogoliubov mode at rapidity `θ` to the
  mode at `−θ`: it **reverses** the diamond rapidity `R⋆/L` and horizon momentum `|p| = sinh θ`, while the
  horizon energy `E = cosh θ = bogoliubovEnergy(sinh θ, 1)` and the gap stay **invariant** — the diamond
  velocity `tanh θ` flips sign.
* **§D — the Nagao–Nielsen contour** (`timeReversal_nn_contour_triangle`). The NN `p,q` contour point
  `N − iε` reflects across the real axis (`q ↦ −q`) while the NN convergence cone `lorentzianForm = p² − q²`
  is invariant — antiunitary time reversal is a symmetry of the NN contour, and the closed
  lapse/boost/diamond triangle acquires its `θ ↦ −θ` reflection.
* **§E — the Bohm quantum potential and the Fisher metric** (`madelungAmplitude_timeReversal`,
  `bornWeight_timeReversal_invariant`, `bohmQuantumPotential_from_bornWeight`,
  `fisherQuantumPotential_from_bornWeight`, `bohm_fisher_timeReversal`). Time reversal reverses the Madelung
  phase `S_R` and the Bohmian guidance velocity `tanh θ`, but the Born weight `e^{−S_I/ℏ}` — hence the
  de Broglie–Bohm quantum potential `Q = S_I·ℏ/2m` and the Fisher metric `I(p)` — is **invariant**. The
  amplitude/metric invariants complement the reversed velocity, exactly as the diamond horizon energy is
  invariant while the rapidity reverses (§C).

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §2.4 (Eqs. 12–13; the reduction to formal
  field theories; the free-field study deferred to §9.1).
* Repo dependencies: `PTSymmetricQFT.QuantumSymmetry` (`quantumDynamics`, `Compatible`, `Preserves`,
  `symmetry_preserves_dynamics`); `PTSymmetricQFT.TemporalOrientation` (`conjFactor`, the quantum action);
  `GravLapse.HyperbolicInterval` (`lapse_on_massShell`); `WickRotation` (`complexEnergy`),
  `ComplexDelta.Convergence` (`lorentzianForm`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSpacetimeSymmetry

open Complex
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation
open Physlib.QuantumMechanics.ComplexAction.GravLapse.HyperbolicInterval
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential
open Physlib.QuantumMechanics.ComplexAction.GravLapse.FisherQuantumPotential
open Physlib.StatisticalMechanics

/-! ## §A — equations (12)–(13): symmetry of `D` ⟺ `[ρω]_q`-invariance of `D^form` -/

variable {U : Type*} [AddCommGroup U] [Module ℂ U] {A : Type*} [Ring A] [Algebra ℂ A] {Φ : Type*}

/-- **The largest formal field theory of a quantum field theory `D`** — the canonical `D^form`,
`⋂_{φ∈D} ker(realize Φ)`: all differential formulae vanishing on every field of `D`. -/
noncomputable def qLargest (evv : Φ → (U →ₗ[ℂ] A)) (D : Set Φ) : Submodule ℂ (KForm U) :=
  ⨅ φ ∈ D, LinearMap.ker (quantumRealize (evv φ)).toLinearMap

/-- A formula lies in the largest formal field theory iff it vanishes on every field of `D`. -/
theorem mem_qLargest (evv : Φ → (U →ₗ[ℂ] A)) (D : Set Φ) (F : KForm U) :
    F ∈ qLargest evv D ↔ ∀ φ ∈ D, quantumRealize (evv φ) F = 0 := by
  simp [qLargest, Submodule.mem_iInf, LinearMap.mem_ker]

/-- **[Greaves–Thomas (13) ⟹ `[ρω]_q`-invariance] A spacetime symmetry of `D` invariates `D^form`.** If a
*bijective* quantum geometric action `T` is a spacetime symmetry of the field theory `D` (`Tφ ∈ D ↔ φ ∈ D`),
compatible with the formula automorphism `σ` (`D_F(Tφ) = D_{σF}(φ)`), then `σ` **preserves** the canonical
formal field theory `qLargest evv D`. With `symmetry_preserves_dynamics` (the converse), this is the §2.4
equivalence: quantum spacetime symmetry ⟺ `[ρω]_q(G)`-invariance of `D^form`. -/
theorem form_invariant_of_spacetime_symmetry (evv : Φ → (U →ₗ[ℂ] A)) (T : Φ ≃ Φ)
    (σ : KForm U ≃ₐ[ℂ] KForm U) (D : Set Φ)
    (hcompat : Compatible evv T σ) (hsym : ∀ φ, T φ ∈ D ↔ φ ∈ D) :
    Preserves σ ((qLargest evv D : Submodule ℂ (KForm U)) : Set (KForm U)) := by
  intro F
  simp only [SetLike.mem_coe, mem_qLargest]
  constructor
  · intro h ψ hψ
    have hTψ : T.symm ψ ∈ D := (hsym (T.symm ψ)).mp (by rw [T.apply_symm_apply]; exact hψ)
    have hh := h (T.symm ψ) hTψ
    rw [← hcompat, T.apply_symm_apply] at hh
    exact hh
  · intro h φ hφ
    rw [← hcompat]; exact h (T φ) ((hsym φ).mpr hφ)

/-! ## §B — temporal orientation meets the lapse hyperbolic interval -/

/-- **[Link] Time reversal conjugates the lapse contour.** The time-reversing conjugation `conjFactor true`
acts on the Banihashemi–Jacobson lapse `complexEnergy N ε = N − iε` by reversing the displacement:
`conj (N − iε) = N + iε = complexEnergy N (−ε)`. The antiunitary `T` is the complex conjugation of the
lapse `iε`-contour. -/
theorem timeReversal_lapse (N ε : ℝ) :
    conjFactor true (complexEnergy N ε) = complexEnergy N (-ε) := by
  simp [conjFactor, complexEnergy]

/-- **[Link] The Minkowski interval is time-reversal invariant.** `lorentzianForm (conj z) = lorentzianForm z`
— the mass shell `Re² − Im²` is unchanged by the time-reversing conjugation (`Im ↦ −Im`). -/
theorem lorentzianForm_timeReversal (z : ℂ) :
    lorentzianForm (conjFactor true z) = lorentzianForm z := by
  simp [conjFactor, lorentzianForm]

/-- **[Link] The time-reversed lapse is on the same mass shell.** The time-reversed lapse contour point
`conj(N − iε)` sits on the *same* hyperbolic spacetime interval `Δ²` as the lapse — Jacobson's causal-diamond
/ boost mass shell is invariant under the antiunitary time reversal. Consumes
`GravLapse.HyperbolicInterval.lapse_on_massShell`. -/
theorem lapse_timeReversal_massShell (Δ θ : ℝ) :
    lorentzianForm (conjFactor true (complexEnergy (Δ * Real.cosh θ) (Δ * Real.sinh θ))) = Δ ^ 2 := by
  rw [lorentzianForm_timeReversal]; exact lapse_on_massShell Δ θ

/-! ## §C — time reversal of the Jacobson causal-diamond Bogoliubov mode -/

/-- **[Link — Jacobson diamond] Time reversal maps the diamond mode at rapidity `θ` to the mode at `−θ`.**
The unit-gap lapse `cosh θ − i sinh θ` is the Jacobson causal-diamond Bogoliubov mode (`E = cosh θ`,
`|p| = sinh θ`, `Δ = 1`); the time-reversing conjugation sends it to the diamond mode at the reversed
rapidity `−θ` — `conj(cosh θ − i sinh θ) = cosh(−θ) − i sinh(−θ)`. The antiunitary `T` reverses the diamond
rapidity `R⋆/L`. -/
theorem timeReversal_diamond_mode (θ : ℝ) :
    conjFactor true (complexEnergy (Real.cosh θ) (Real.sinh θ))
      = complexEnergy (Real.cosh (-θ)) (Real.sinh (-θ)) := by
  rw [timeReversal_lapse, Real.cosh_neg, Real.sinh_neg]

/-- **[Link — Jacobson diamond] The diamond horizon energy is time-reversal invariant.** The
conformal-Killing-horizon energy `E = cosh θ = bogoliubovEnergy(sinh θ, 1)` of `CausalDiamond.Helicity`
is unchanged under `θ ↦ −θ` — the Bogoliubov gap (the lapse `N`, the mass shell) is invariant under
antiunitary time reversal. -/
theorem diamond_energy_timeReversal_invariant (θ : ℝ) :
    bogoliubovEnergy (Real.sinh (-θ)) 1 = bogoliubovEnergy (Real.sinh θ) 1 := by
  rw [diamond_horizon_energy, diamond_horizon_energy, Real.cosh_neg]

/-- **[Link — Jacobson diamond] The diamond velocity (rapidity `R⋆/L`) is reversed by time reversal.**
The causal-diamond velocity `sinh θ / bogoliubovEnergy(sinh θ, 1) = tanh θ` flips sign under `θ ↦ −θ` — the
horizon momentum `|p| = sinh θ` reverses while the horizon energy stays fixed, so the diamond velocity
reverses. -/
theorem diamond_velocity_timeReversal (θ : ℝ) :
    Real.sinh (-θ) / bogoliubovEnergy (Real.sinh (-θ)) 1
      = -(Real.sinh θ / bogoliubovEnergy (Real.sinh θ) 1) := by
  rw [diamond_energy_timeReversal_invariant, Real.sinh_neg, neg_div]

/-! ## §D — time reversal of the Nagao–Nielsen contour -/

/-- **[Link — Nagao–Nielsen contour] Time reversal reflects the NN `p,q` contour across the real axis,
preserving the convergence cone.** The lapse `complexEnergy N ε = N − iε` is the Nagao–Nielsen contour point
(`p = N = Re`, `q = ε = −Im`); the time-reversing conjugation reflects it `N − iε ↦ N + iε` (`q ↦ −q`,
`ε ↦ −ε`), and the NN convergence cone `lorentzianForm = p² − q²` (`ComplexDelta.Convergence`) is **invariant**
(`lorentzianForm_timeReversal`). So the NN contour is symmetric under antiunitary time reversal: the
subluminal/timelike convergence condition is preserved, and the time-reversed contour lies on the same
hyperbolic interval as the diamond mode and the boost vector — the closed lapse/boost/diamond triangle of
`GravLapse.HyperbolicInterval`, now with its `θ ↦ −θ` reflection. -/
theorem timeReversal_nn_contour_triangle (θ : ℝ) :
    conjFactor true (complexEnergy (Real.cosh θ) (Real.sinh θ))
        = complexEnergy (Real.cosh (-θ)) (Real.sinh (-θ))
      ∧ lorentzianForm (conjFactor true (complexEnergy (Real.cosh θ) (Real.sinh θ))) = 1
      ∧ Real.sinh (-θ) / bogoliubovEnergy (Real.sinh (-θ)) 1
          = -(Real.sinh θ / bogoliubovEnergy (Real.sinh θ) 1) :=
  ⟨timeReversal_diamond_mode θ, by simpa using lapse_timeReversal_massShell 1 θ,
    diamond_velocity_timeReversal θ⟩

/-! ## §E — the Bohm quantum potential and the Fisher metric under time reversal -/

/-- **[Link — Bohm/Madelung] Time reversal reverses the Madelung phase, preserves the imaginary action.**
The Madelung pilot wave `ψ = e^{iS_R/ℏ} e^{−S_I/ℏ}` (`GravLapse.BohmQuantumPotential.madelungAmplitude`)
maps under the time-reversing conjugation to `ψ* = e^{−iS_R/ℏ} e^{−S_I/ℏ}` — the phase `S_R` (the momentum /
guidance velocity) reverses while the imaginary action `S_I` is unchanged. -/
theorem madelungAmplitude_timeReversal (S_R S_I ℏ : ℝ) :
    conjFactor true (madelungAmplitude S_R S_I ℏ) = madelungAmplitude (-S_R) S_I ℏ := by
  simp only [conjFactor_true, madelungAmplitude, map_mul, ← Complex.exp_conj, Complex.conj_I,
    Complex.conj_ofReal]
  push_cast; ring_nf

/-- **[Link — Born weight] The Born weight is time-reversal invariant.** `‖ψ*‖ = ‖ψ‖ = e^{−S_I/ℏ}`: the
probability amplitude / density (the Born weight `bornWeight S_I ℏ`) is unchanged by antiunitary time
reversal — the amplitude is the invariant face, complementing the reversed phase. -/
theorem bornWeight_timeReversal_invariant (S_R S_I ℏ : ℝ) :
    ‖conjFactor true (madelungAmplitude S_R S_I ℏ)‖ = bornWeight S_I ℏ := by
  rw [conjFactor_true, RCLike.norm_conj, madelungAmplitude_norm]

/-- **[Link — Bohm quantum potential] The Bohm quantum potential is a function of the invariant Born
weight.** `Q = S_I·ℏ/2m` with `S_I = −ℏ log(bornWeight S_I ℏ)`; since the Born weight is time-reversal
invariant (`bornWeight_timeReversal_invariant`), so is the de Broglie–Bohm quantum potential. -/
theorem bohmQuantumPotential_from_bornWeight (S_I ℏ m : ℝ) (hℏ : ℏ ≠ 0) :
    bohmQuantumPotential (-ℏ * Real.log (bornWeight S_I ℏ)) ℏ m = bohmQuantumPotential S_I ℏ m := by
  unfold bornWeight bohmQuantumPotential; rw [Real.log_exp]; field_simp

/-- **[Link — Fisher metric] The Fisher quantum potential is a function of the invariant Born weight.**
`Q_Fisher = I(p)·ℏ/2m` with the Fisher information `I(p) = S_I = −ℏ log(bornWeight)`; since the density
`p = |ψ|² = |ψ*|²` (the Born weight) is time-reversal invariant, the Fisher-information quantum potential —
the Fisher metric on the statistical manifold — is invariant. -/
theorem fisherQuantumPotential_from_bornWeight {Ψ : Type} (data : FisherInformationData Ψ) (ψ : Ψ)
    (S_I ℏ m : ℝ) (hℏ : ℏ ≠ 0) (hfish : data.fisherInfo ψ = S_I) :
    fisherQuantumPotential data ψ ℏ m
      = bohmQuantumPotential (-ℏ * Real.log (bornWeight S_I ℏ)) ℏ m := by
  unfold fisherQuantumPotential
  rw [hfish]
  exact (bohmQuantumPotential_from_bornWeight S_I ℏ m hℏ).symm

/-- **[Bundle] The Bohm/Fisher split under time reversal.** The antiunitary time reversal **reverses** the
Madelung phase `S_R` and the Bohmian guidance / diamond velocity `tanh θ`, but **leaves invariant** the Born
weight `e^{−S_I/ℏ}` — and hence the Bohm quantum potential `Q = S_I·ℏ/2m` and the Fisher metric `I(p)`. So
the amplitude/metric invariants (Bohm potential, Fisher information) complement the reversed velocity,
exactly as the Jacobson diamond's horizon energy is invariant while its rapidity `R⋆/L` reverses (§C). -/
theorem bohm_fisher_timeReversal (S_R S_I ℏ θ : ℝ) :
    conjFactor true (madelungAmplitude S_R S_I ℏ) = madelungAmplitude (-S_R) S_I ℏ
      ∧ ‖conjFactor true (madelungAmplitude S_R S_I ℏ)‖ = bornWeight S_I ℏ
      ∧ Real.tanh (-θ) = -(Real.tanh θ) :=
  ⟨madelungAmplitude_timeReversal S_R S_I ℏ, bornWeight_timeReversal_invariant S_R S_I ℏ,
    Real.tanh_neg θ⟩

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSpacetimeSymmetry

end

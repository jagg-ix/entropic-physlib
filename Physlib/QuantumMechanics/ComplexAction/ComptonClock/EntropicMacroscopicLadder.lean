/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.OneRegionGeometry
public import Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy
public import Physlib.QuantumMechanics.ComplexAction.VanDerWaalsRadii

/-!
# From the Compton wavelength to macroscopic lengths: the entropic and atomic ladders

Two independent ladders climb from the one-region quantum length scale to macroscopic
lengths, and both are anchored to the **Compton wavelength** `λ_C = ħ/(mc)`
(`ComptonClock.FrequencyTrinity`):

**The entropic ladder** — lengths as counts of entangled bits.
* `collisionWeight`, `collisionWeight_prod` — the collision weight `Σ|ρ_{ij}|² = Tr ρ²` is
  **multiplicative under the state product** `⊗ᴹ`, so the Schmidt number `K = (Tr ρ²)⁻¹`
  multiplies and the entropic radius `r = λ_C log K`
  (`ComptonClock.EntropicProperDistance`) is **additive**: independent entangled regions
  compose by adding radii (`entropicRadius_add`).
* `collisionWeight_bellMarginal`, `bellMarginal_radius` — one Bell pair contributes
  `r = λ_C log 2`: one entangled bit is `log 2` Compton units.
* `bellStack_radius` — `n` independent pairs give `r = n·λ_C log 2` (`log_pow`): a
  macroscopic entropic length is a **count of entangled bits** times `λ_C log 2`.

**The atomic ladder** — lengths through the fine structure constant and the shells.
* `bohr_mul_alpha` — the Bohr radius is the Compton wavelength amplified by `1/α`
  (`Particles.CasimirLengthHierarchy.bohrRadius`): `a₀·α = λ_C`.
* `atomicShellRadius_eq` — the Batsanov/van-der-Waals outer-shell radius
  (`VanDerWaalsRadii.maxRadius`, whose consecutive ratio `((n+1)/n)²` is
  `maxRadius_div_groundStateRadius`) seated on the Bohr radius:
  `R(n) = λ_C·(n+1)²/(α·Z_eff)` — the atomic/van-der-Waals length as an explicit
  dimensionless multiple of `λ_C`.  (The polarizability route `R_vdW ∝ α_pol^{1/7}` is the
  carrier `VanDerWaalsPolarizabilityScaling`.)
* `chainLength_from_compton` — stacking `N` atoms: the macroscopic chain length is
  `N·2(n+1)²/(α·Z_eff)` Compton wavelengths — **every macroscopic length is a
  dimensionless number of Compton units**.

**The exchange rate between the ladders** (`entropicBit_per_bohr`): one entangled bit of
length per Bohr radius is `α·log 2` — the dimensionless constant converting entropic
length-counting into atomic length-counting.

## References

* Carriers: `ComptonClock.FrequencyTrinity` (`comptonWavelength`),
  `ComptonClock.EntropicProperDistance` (`r = λ_C log K`, Schmidt dictionary),
  `Particles.CasimirLengthHierarchy` (`bohrRadius`, Thomson/Hartree rungs),
  `VanDerWaalsRadii` (Batsanov shells), `VanDerWaalsPolarizabilityScaling`
  (`α_pol^{1/7}`), `Bell.OneRegionGeometry` (the Bell collision datum `1/2`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy
open Physlib.QuantumMechanics.ComplexAction.VanDerWaalsRadii

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicMacroscopicLadder

/-! ## §A — the entropic ladder: radii add under the state product -/

/-- **The collision weight** `Σ_{ij} |ρ_{ij}|² = Tr ρ²` of a state — the inverse Schmidt
number datum. -/
noncomputable def collisionWeight {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (ρ.m i j)

/-- **The collision weight is multiplicative under the state product**: independent
subsystems multiply their `Tr ρ²`, hence multiply their Schmidt numbers. -/
theorem collisionWeight_prod {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    [DecidableEq d₁] [DecidableEq d₂] (ρ₁ : MState d₁) (ρ₂ : MState d₂) :
    collisionWeight (ρ₁ ⊗ᴹ ρ₂) = collisionWeight ρ₁ * collisionWeight ρ₂ := by
  unfold collisionWeight
  have hm : ∀ (p q : d₁ × d₂),
      (ρ₁ ⊗ᴹ ρ₂).m p q = ρ₁.m p.1 q.1 * ρ₂.m p.2 q.2 := fun p q => rfl
  have expand : (∑ i, ∑ j, Complex.normSq (ρ₁.m i j))
        * (∑ k, ∑ l, Complex.normSq (ρ₂.m k l))
      = ∑ i, ∑ k, ∑ j, ∑ l,
          Complex.normSq (ρ₁.m i j) * Complex.normSq (ρ₂.m k l) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_mul_sum _ _ _ _
  rw [expand, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hm, Complex.normSq_mul]

/-- **The entropic radius of a state**: `r = λ_C · log K` with `K = (Tr ρ²)⁻¹` — the
`ComptonClock.EntropicProperDistance` dictionary read through the collision weight. -/
noncomputable def entropicRadius (m c ħ : ℝ) {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) : ℝ :=
  comptonWavelength m c ħ * Real.log (collisionWeight ρ)⁻¹

/-- **Entropic radii add under the state product**: independent entangled regions compose
by adding their radii — the accumulation law of the entropic ladder. -/
theorem entropicRadius_add (m c ħ : ℝ) {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    [DecidableEq d₁] [DecidableEq d₂] (ρ₁ : MState d₁) (ρ₂ : MState d₂)
    (h₁ : collisionWeight ρ₁ ≠ 0) (h₂ : collisionWeight ρ₂ ≠ 0) :
    entropicRadius m c ħ (ρ₁ ⊗ᴹ ρ₂)
      = entropicRadius m c ħ ρ₁ + entropicRadius m c ħ ρ₂ := by
  unfold entropicRadius
  rw [collisionWeight_prod, mul_inv, Real.log_mul (inv_ne_zero h₁) (inv_ne_zero h₂)]
  ring

/-- **The Bell marginal's collision weight is `1/2`** — the matrix form of the collision
datum of `Bell.OneRegionGeometry.bellMarginal_collision_trace`. -/
theorem collisionWeight_bellMarginal :
    collisionWeight ((MState.pure bellPhiPlus).traceRight) = 1/2 := by
  unfold collisionWeight
  have hm : ((MState.pure bellPhiPlus).traceRight).m
      = Matrix.diagonal (fun _ : Fin 2 => ((1/2 : ℝ) : ℂ)) := by
    rw [congrArg MState.m bellPhiPlus_traceRight_uniform, uniform_m_eq]
  rw [hm, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [Matrix.diagonal]
  norm_num

/-- **One Bell pair is one entangled bit of length**: `r = λ_C · log 2`. -/
theorem bellMarginal_radius (m c ħ : ℝ) :
    entropicRadius m c ħ ((MState.pure bellPhiPlus).traceRight)
      = comptonWavelength m c ħ * Real.log 2 := by
  unfold entropicRadius
  rw [collisionWeight_bellMarginal]
  norm_num

/-- **`n` independent pairs give `n` bits of length**: `λ_C·log 2ⁿ = n·(λ_C·log 2)` — the
macroscopic accumulation of the entropic ladder. -/
theorem bellStack_radius (m c ħ : ℝ) (n : ℕ) :
    comptonWavelength m c ħ * Real.log ((2:ℝ)^n)
      = n * (comptonWavelength m c ħ * Real.log 2) := by
  rw [Real.log_pow]
  ring

/-! ## §B — the atomic ladder: Compton → Bohr → shell → chain -/

/-- **The Bohr rung**: `a₀·α = λ_C` — the Bohr radius is the Compton wavelength amplified
by the inverse fine-structure constant. -/
theorem bohr_mul_alpha (m c ħ α : ℝ) (hα : α ≠ 0) :
    bohrRadius m c ħ α * α = comptonWavelength m c ħ := by
  unfold bohrRadius
  field_simp

/-- **The atomic/van-der-Waals shell radius seated on the Bohr radius**: the Batsanov
outer-shell radius of `VanDerWaalsRadii` with `a₀ = λ_C/α`. -/
noncomputable def atomicShellRadius (m c ħ α Zeff n : ℝ) : ℝ :=
  maxRadius (bohrRadius m c ħ α) Zeff n

/-- **The atomic length as a dimensionless multiple of the Compton wavelength**:
`R(n) = λ_C·(n+1)²/(α·Z_eff)`. -/
theorem atomicShellRadius_eq (m c ħ α Zeff n : ℝ) (hα : α ≠ 0) (hZ : Zeff ≠ 0) :
    atomicShellRadius m c ħ α Zeff n
      = comptonWavelength m c ħ * (n + 1)^2 / (α * Zeff) := by
  unfold atomicShellRadius maxRadius bohrRadius
  field_simp

/-- **Stacking**: the length of a chain of `N` atoms of radius `R`. -/
noncomputable def chainLength (N : ℕ) (R : ℝ) : ℝ := N * (2 * R)

/-- **Every macroscopic chain length is a dimensionless number of Compton units**:
`L = N·2(n+1)²/(α·Z_eff) · λ_C`. -/
theorem chainLength_from_compton (N : ℕ) (m c ħ α Zeff n : ℝ)
    (hα : α ≠ 0) (hZ : Zeff ≠ 0) :
    chainLength N (atomicShellRadius m c ħ α Zeff n)
      = (N * 2 * (n + 1)^2 / (α * Zeff)) * comptonWavelength m c ħ := by
  unfold chainLength
  rw [atomicShellRadius_eq m c ħ α Zeff n hα hZ]
  field_simp

/-! ## §C — the exchange rate between the ladders -/

/-- **One entangled bit of length per Bohr radius is `α·log 2`**: the dimensionless
constant converting the entropic ladder's unit (`λ_C log 2` per Bell pair) into the atomic
ladder's unit (`a₀ = λ_C/α` per atom). -/
theorem entropicBit_per_bohr (m c ħ α : ℝ)
    (hlc : comptonWavelength m c ħ ≠ 0) (hα : α ≠ 0) :
    (comptonWavelength m c ħ * Real.log 2) / bohrRadius m c ħ α = α * Real.log 2 := by
  unfold bohrRadius
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicMacroscopicLadder

end

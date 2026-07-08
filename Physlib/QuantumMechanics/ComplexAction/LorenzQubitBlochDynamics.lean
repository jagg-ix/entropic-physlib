/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic.Ring
public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu
public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.NambuEntropicContour
public import Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion
public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellBifurcation

/-!
# Lorenz qubit Bloch dynamics

This file formalizes the equation-level core of M. R. Geller, *Proposal for a Lorenz qubit*,
Sci. Rep. 13, 14106 (2023), arXiv:2112.13476v2.

The paper proposes nonlinear positive trace-preserving qubit dynamics whose normalized Bloch-vector
flow realizes Lorenz-type equations. The proof-ready content formalized here is the algebra that Lean
can check directly:

* the Lor63 Bloch ODE
  `ẋ = σ(y-x)`, `ẏ = ρx-y-gxz`, `ż = -βz+gxy`;
* its paper matrix form `r_dot = (L + gx Jx) r`, with the symmetric/dissipative plus rotational
  split `L = L_+ + L_-`;
* the GP-butterfly example `r_dot = (m λ₄ + gz Jz) r`;
* links to the existing Hopf/Bloch sphere, dissipative-Nambu, strange-attractor contour-deformation,
  bifurcation, and positive-Lyapunov certificate layers.

The repo already contains the Axenides-Floratos dissipative-Nambu theorem
`dissipative_contour_decays`, documented there as the checked contour/strange-attractor deformation
statement. This file reuses that formalization for Bloch-vector Lorenz-qubit data. What remains outside this
file is a Tucker-style global invariant-set proof for the normalized nonlinear PTP channel and a physical
device realization theorem. The file proves the exact finite-dimensional matrix identities that such a later
analytic layer would consume.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics

open Matrix
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.NambuEntropicContour
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion.ThreeNodulePhaseRegion
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellBifurcation

/-! ## A. Bloch-vector structures -/

/-- A real Bloch vector `r = (x,y,z)`. -/
abbrev BlochVector : Type := Fin 3 → ℝ

/-- The closed Bloch ball condition `x² + y² + z² ≤ 1`. -/
def BlochBall (r : BlochVector) : Prop := r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1

/-- The Bloch/Poincare sphere condition `x² + y² + z² = 1`. -/
def BlochSphere (r : BlochVector) : Prop := r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1

/-- A real Bloch vector represented by the repository's spinor Hopf base coordinates. -/
def IsHopfBlochVector (χ : Fin 2 → ℂ) (r : BlochVector) : Prop :=
  ∀ i : Fin 3, hopfBase χ i = (r i : ℂ)

/-- The Hopf/Bloch representative satisfies the existing Poincare-sphere identity. -/
theorem hopfBlochVector_lies_on_poincare_sphere (χ : Fin 2 → ℂ) (r : BlochVector)
    (h : IsHopfBlochVector χ r) :
    (r 0 : ℂ) ^ 2 + (r 1 : ℂ) ^ 2 + (r 2 : ℂ) ^ 2 = hopfIntensity χ ^ 2 := by
  have hs := hopfBase_lies_on_poincare_sphere χ
  rw [h 0, h 1, h 2] at hs
  simpa using hs

/-- The Hopf/Bloch representative is insensitive to a unit global spinor phase. -/
theorem hopfBlochVector_phase_invariant (u : ℂ) (χ : Fin 2 → ℂ) (r : BlochVector)
    (hu : star u * u = 1) (h : IsHopfBlochVector χ r) :
    IsHopfBlochVector (phaseRotate u χ) r := by
  intro i
  rw [hopfBase_phase_invariant u χ hu, h i]

/-! ## B. The paper's `so(3)` and Gell-Mann generators -/

/-- The paper's `Jx`, with `(Jx r) = (0,-z,y)`. -/
def so3Jx : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, -1; 0, 1, 0]

/-- The paper's `Jz`, with `(Jz r) = (-y,x,0)`. -/
def so3Jz : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 0]

/-- The symmetric Gell-Mann generator `λ₁`. -/
def gellMannLambda1 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- The symmetric Gell-Mann generator `λ₄`. -/
def gellMannLambda4 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 0, 0; 1, 0, 0]

/-- The damping matrix `D = diag(σ,1,β)`. -/
def dampingD (sigma beta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![sigma, 0, 0; 0, 1, 0; 0, 0, beta]

@[simp] theorem so3Jx_mulVec (r : BlochVector) : so3Jx *ᵥ r = ![0, -r 2, r 1] := by
  ext i
  fin_cases i <;> simp [so3Jx, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] theorem so3Jz_mulVec (r : BlochVector) : so3Jz *ᵥ r = ![-r 1, r 0, 0] := by
  ext i
  fin_cases i <;> simp [so3Jz, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] theorem gellMannLambda1_mulVec (r : BlochVector) :
    gellMannLambda1 *ᵥ r = ![r 1, r 0, 0] := by
  ext i
  fin_cases i <;> simp [gellMannLambda1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] theorem gellMannLambda4_mulVec (r : BlochVector) :
    gellMannLambda4 *ᵥ r = ![r 2, 0, r 0] := by
  ext i
  fin_cases i <;> simp [gellMannLambda4, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The `x` axis as a Bloch-vector/Nambu-gradient structure. -/
def blochXAxis : BlochVector := ![1, 0, 0]

/-- The `z` axis as a Bloch-vector/Nambu-gradient structure. -/
def blochZAxis : BlochVector := ![0, 0, 1]

/-- The paper's `Jx` generator is exactly the Nambu/cross-product flow `e_x × r`. -/
theorem so3Jx_mulVec_eq_nambuFlow_xAxis (r : BlochVector) :
    so3Jx *ᵥ r = nambuFlow blochXAxis r := by
  ext i
  fin_cases i <;>
    simp [so3Jx, nambuFlow, blochXAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_three, crossProduct]

/-- The paper's `Jz` generator is exactly the Nambu/cross-product flow `e_z × r`. -/
theorem so3Jz_mulVec_eq_nambuFlow_zAxis (r : BlochVector) :
    so3Jz *ᵥ r = nambuFlow blochZAxis r := by
  ext i
  fin_cases i <;>
    simp [so3Jz, nambuFlow, blochZAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_three, crossProduct]

/-! ## C. Lor63 qubit equation -/

/-- The Lor63 linear matrix `L` from the paper. -/
def lor63LinearMatrix (sigma rho beta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-sigma, sigma, 0; rho, -1, 0; 0, 0, -beta]

/-- The symmetric/dissipative part `L_+ = ((ρ+σ)/2) λ₁ - D`. -/
noncomputable def lor63LPlus (sigma rho beta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((rho + sigma) / 2) • gellMannLambda1 - dampingD sigma beta

/-- The rotational part `L_- = ((ρ-σ)/2) Jz`. -/
noncomputable def lor63LMinus (sigma rho : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((rho - sigma) / 2) • so3Jz

/-- The nonlinear Lor63 generator `G(r) = L + g x Jx`. -/
def lor63Generator (sigma rho beta g : ℝ) (r : BlochVector) : Matrix (Fin 3) (Fin 3) ℝ :=
  lor63LinearMatrix sigma rho beta + (g * r 0) • so3Jx

/-- The Lor63 Bloch-vector field in component form. -/
def lor63VectorField (sigma rho beta g : ℝ) (r : BlochVector) : BlochVector :=
  ![sigma * (r 1 - r 0), rho * r 0 - r 1 - g * r 0 * r 2, -beta * r 2 + g * r 0 * r 1]

/-- The paper's split `L = L_+ + L_-`. -/
theorem lor63LinearMatrix_split (sigma rho beta : ℝ) :
    lor63LPlus sigma rho beta + lor63LMinus sigma rho = lor63LinearMatrix sigma rho beta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lor63LPlus, lor63LMinus, lor63LinearMatrix, dampingD, gellMannLambda1, so3Jz] <;> ring

/-- The paper's Lor63 identity `r_dot = (L + gx Jx) r`, checked componentwise. -/
theorem lor63Generator_mulVec_eq_vectorField (sigma rho beta g : ℝ) (r : BlochVector) :
    lor63Generator sigma rho beta g r *ᵥ r = lor63VectorField sigma rho beta g r := by
  ext i
  fin_cases i <;>
    simp [lor63Generator, lor63LinearMatrix, lor63VectorField, so3Jx, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- The component equations of the Lor63 qubit proposal. -/
theorem lor63VectorField_components (sigma rho beta g : ℝ) (r : BlochVector) :
    lor63VectorField sigma rho beta g r 0 = sigma * (r 1 - r 0)
      ∧ lor63VectorField sigma rho beta g r 1 = rho * r 0 - r 1 - g * r 0 * r 2
      ∧ lor63VectorField sigma rho beta g r 2 = -beta * r 2 + g * r 0 * r 1 := by
  simp [lor63VectorField]

/-! ## D. GP-butterfly qubit equation -/

/-- The GP-butterfly generator `G(r) = m λ₄ + g z Jz`. -/
def gpButterflyGenerator (m g : ℝ) (r : BlochVector) : Matrix (Fin 3) (Fin 3) ℝ :=
  m • gellMannLambda4 + (g * r 2) • so3Jz

/-- The GP-butterfly vector field induced by `m λ₄ + gz Jz`. -/
def gpButterflyVectorField (m g : ℝ) (r : BlochVector) : BlochVector :=
  ![m * r 2 - g * r 2 * r 1, g * r 2 * r 0, m * r 0]

/-- The GP-butterfly identity `r_dot = (m λ₄ + gz Jz) r`, checked componentwise. -/
theorem gpButterflyGenerator_mulVec_eq_vectorField (m g : ℝ) (r : BlochVector) :
    gpButterflyGenerator m g r *ᵥ r = gpButterflyVectorField m g r := by
  ext i
  fin_cases i
  · simp [gpButterflyGenerator, gpButterflyVectorField, gellMannLambda4, so3Jz, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
    ring
  · simp [gpButterflyGenerator, gpButterflyVectorField, gellMannLambda4, so3Jz, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · simp [gpButterflyGenerator, gpButterflyVectorField, gellMannLambda4, so3Jz, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

/-- The component equations of the GP-butterfly qubit proposal. -/
theorem gpButterflyVectorField_components (m g : ℝ) (r : BlochVector) :
    gpButterflyVectorField m g r 0 = m * r 2 - g * r 2 * r 1
      ∧ gpButterflyVectorField m g r 1 = g * r 2 * r 0
      ∧ gpButterflyVectorField m g r 2 = m * r 0 := by
  simp [gpButterflyVectorField]

/-! ## E. Links to existing repo infrastructure -/

/-- The Lor63 linear matrix split exposes a symmetric/dissipative part and a rotational `so(3)` part. -/
theorem lor63_split_as_dissipative_plus_rotational (sigma rho beta : ℝ) :
    lor63LinearMatrix sigma rho beta = lor63LPlus sigma rho beta + lor63LMinus sigma rho := by
  rw [lor63LinearMatrix_split]

/-- The Lor63 nonlinear part is generated by the same `Jx` cross-axis used in `R³` Nambu mechanics. -/
theorem lor63_nonlinear_part_is_cross_axis (g : ℝ) (r : BlochVector) :
    (g * r 0) • (so3Jx *ᵥ r) = (g * r 0) • (![0, -r 2, r 1] : BlochVector) := by
  rw [so3Jx_mulVec]

/-- If the Lorenz-qubit flow is supplied with a monotone critical parameter crossing, it feeds the
existing bifurcation index-jump theorem. This is a non-vacuous obligation interface: the monotone crossing
is the missing analytic hypothesis, and the sign change is the checked topological conclusion. -/
theorem lorenzQubit_bifurcation_signs_differ (α : ℝ → ℝ) (ε₀ d : ℝ) (hd : 0 < d)
    (hmono : StrictMono α) (hzero : α ε₀ = 0) :
    SignType.sign (α (ε₀ - d)) ≠ SignType.sign (α (ε₀ + d)) :=
  bifurcation_signs_differ α ε₀ d hd hmono hzero

/-- The Lorenz-qubit `BlochVector` structure is the same `R³` structure used by the existing
Axenides-Floratos/Nagao-Nielsen strange-attractor deformation theorem. A nonzero dissipative Nambu
gradient therefore gives the already-formalized contour decay/attractor deformation. -/
theorem lorenzQubit_existing_nambu_attractor_deformation (S_R : ℝ) {gD : BlochVector} {t ℏ : ℝ}
    (hgD : gD ≠ 0) (ht : 0 < t) (hℏ : 0 < ℏ) :
    ‖nnPathWeight S_R (nambuImaginaryAction gD t) ℏ‖ < 1 :=
  dissipative_contour_decays S_R hgD ht hℏ

/-- In the zero-dissipation Lorenz-qubit/Nambu interface, the existing contour formalization gives the
undeformed reversible limit: the path-weight norm is exactly `1`. -/
theorem lorenzQubit_conservative_nambu_contour_undeformed (S_R ℏ t : ℝ) :
    ‖nnPathWeight S_R (nambuImaginaryAction (0 : BlochVector) t) ℏ‖ = 1 := by
  simpa using conservative_contour_undeformed S_R ℏ t

/-- A Lorenz-qubit Lyapunov marker is exactly the repo's positive-Lyapunov chaos predicate. -/
abbrev LorenzQubitChaosMarker : Type := LyapunovExponent

/-- Positive Lyapunov growth is the checked local chaos marker reused from the three-nodule phase region. -/
def IsLorenzQubitChaotic (lambda : LorenzQubitChaosMarker) : Prop :=
  IsChaoticLyapunov lambda

/-- The local chaos marker is definitionally positive Lyapunov growth. -/
theorem isLorenzQubitChaotic_iff_positiveLyapunov (lambda : LorenzQubitChaosMarker) :
    IsLorenzQubitChaotic lambda ↔ PositiveLyapunov lambda :=
  Iff.rfl

/-- The Lorenz-qubit equations plus Hopf/Bloch data assemble into one checked core theorem. -/
theorem lorenz_qubit_checked_core (χ : Fin 2 → ℂ) (r : BlochVector)
    (h : IsHopfBlochVector χ r) (sigma rho beta g m gp : ℝ) :
    lor63Generator sigma rho beta g r *ᵥ r = lor63VectorField sigma rho beta g r
      ∧ gpButterflyGenerator m gp r *ᵥ r = gpButterflyVectorField m gp r
      ∧ (r 0 : ℂ) ^ 2 + (r 1 : ℂ) ^ 2 + (r 2 : ℂ) ^ 2 = hopfIntensity χ ^ 2 :=
  ⟨lor63Generator_mulVec_eq_vectorField sigma rho beta g r,
    gpButterflyGenerator_mulVec_eq_vectorField m gp r,
    hopfBlochVector_lies_on_poincare_sphere χ r h⟩

/-! ## F. Paper parameter examples -/

/-- The Lor63 example parameter values used in the paper: `(σ,ρ,β,g) = (10,28,8/3,80)`. -/
noncomputable def paperLor63Parameters : ℝ × ℝ × ℝ × ℝ := (10, 28, 8 / 3, 80)

/-- The GP-butterfly example parameter values used in the paper: `(m,g) = (10,40)`. -/
def paperGPButterflyParameters : ℝ × ℝ := (10, 40)

/-- The paper's Lor63 nonlinear coupling example is strictly positive. -/
theorem paperLor63_g_positive : 0 < paperLor63Parameters.2.2.2 := by
  norm_num [paperLor63Parameters]

/-- The paper's GP-butterfly parameters are strictly positive. -/
theorem paperGPButterfly_parameters_positive :
    0 < paperGPButterflyParameters.1 ∧ 0 < paperGPButterflyParameters.2 := by
  norm_num [paperGPButterflyParameters]

end Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics

end

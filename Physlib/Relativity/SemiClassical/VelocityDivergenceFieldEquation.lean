/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.MatterContent
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
public import Physlib.Thermodynamics.GravitationalCouplingSystem
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The velocity-field divergence form of the Newtonian and Einstein field equations

Blume (J. Appl. Math. Phys. 10 (2022) 1461) shows that Newton's and Einstein's gravitational field
equations are the *same* velocity-field divergence equation

  `w[div(w)] + div(w,w) = −4πρ`   (Eqs. 6, 8),

with `div(w) = tr(Dw)`, `div(v,w) = tr(Dv·Dw)` the traces of the Jacobian derivative matrices. The
mechanism, in the Lorentz frame at an event (metric `η = diag(1,−1,−1,−1)`, dust `T = ρ u⊗u` at rest,
`u = e₀`):

* the dust Einstein equation `Ric − (R/2)η = 8πρ u⊗u` (Eq. 7) forces `R = −8πρ` by the `η`-trace;
* substituting back, the Ricci matrix collapses to **`Ric = 4πρ·1` — `4πρ` times the *Euclidean*
  identity** (Eq. 9): the Lorentzian field equation stores a Euclidean-form Ricci, and `4πρ` is
  Newton's Poisson source;
* by the divergence representation `w[div(w)] + div(w,w) = −Ric(w,w)` (Theorem 4.1/Corollary 4.4),
  every direction `w` of **Euclidean** unit length — timelike `u`, spacelike `u_⊥`, or null
  `(u + u_⊥)/√2`, Blume's conditions (a), (b), (c), Eq. 16 — satisfies the same equation `= −4πρ` as
  the Newtonian trajectory field (Eq. 6): the two theories are formally identical;
* recontracting, `Ric(x,x) − (R/2)η(x,x) = 8π·ρ η(x,u)²` for every `x`: **Einstein's `8π` is the
  Euclidean `4π` of the Ricci plus the Lorentzian `4π` of the scalar term** — the `4π ↔ 8π`
  transition is a trace bookkeeping, not new physics.

Newtonian anchor: the free-particle trajectory field `v = (1, x/x⁰)` has explicit Jacobian `Dv` with
`v[div(v)] = −3/(x⁰)² = −tr((Dv)²)` (Eq. 3), so it satisfies the vacuum divergence equation — the
classical vacuum row of Blume's table, verified on the explicit field.

* **§A** the free-particle Jacobian: `div v = 3/t`, `div(v,v) = 3/t²`, and the vacuum equation
  `v[div v] + div(v,v) = 0` (Eq. 3).
* **§B** dust in the Lorentz frame: `T = ρ u⊗u` is the pressureless
  `Cosmology.FLRW.MatterContent.perfectFluidStressEnergy`.
* **§C** the trace step `R = −k·ε` and the Euclidean collapse `Ric = (k·ε/2)·1` for a general
  coupling `k` (Eq. 9 at `k = 8π`, `ε = ρ`).
* **§D** the divergence equation `−Ric(w,w) = −4πρ` for every Euclidean-unit `w`; the timelike,
  spacelike and null instances (a)/(b)/(c); the vacuum instance `ρ = 0`.
* **§E** the `8π = 4π + 4π` recontraction (the closing computation of Theorem 5.1).
* **§F** physical units: at `k = 8πG/c⁴`, `ε = ρc²` the `00`-component is `4πGρ/c²` — the hypothesis
  of `ComptonClock.NewtonianAndGRLimit.weakField_einstein_poisson`, closing the chain
  dust EFE → `R₀₀ = 4πGρ/c²` → `∇²Φ = 4πGρ` with the coupling split
  `Thermodynamics.GravitationalCouplingSystem.dust_traceReversed_source`.

## References

* F. Blume, *On the Transition from Newtonian Gravity to General Relativity*, J. Appl. Math. Phys. 10
  (2022) 1461 — Eqs. 3-9, 15-16, Theorems 4.1 and 5.1.
* C. W. Misner, K. S. Thorne, J. A. Wheeler, *Gravitation* (Freeman, 1973) — the weak-field limit.
-/

set_option autoImplicit false

open Matrix
open Cosmology.FLRW.MatterContent
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.Thermodynamics.GravitationalCouplingSystem

namespace Physlib.Relativity.SemiClassical.VelocityDivergenceFieldEquation

@[expose] public section

/-- The trace of a `Fin 4` diagonal matrix is the sum of its entries. -/
lemma traceDiagFour (a b c d : ℝ) : (Matrix.diagonal ![a, b, c, d]).trace = a + b + c + d := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply_eq, Fin.sum_univ_four]

/-! ## A. The Newtonian free-particle field satisfies the vacuum divergence equation -/

/-- **[The free-particle Jacobian, Blume §3]** The Newtonian free-particle trajectory field
`v(x⁰,x) = (1, x¹/x⁰, x²/x⁰, x³/x⁰)` (straight lines through the origin of absolute spacetime) has
the Jacobian derivative matrix `Dv` with first column `(0, −xⁱ/t²)` and diagonal `(0, 1/t, 1/t, 1/t)`. -/
noncomputable def freeParticleJacobian (t x₁ x₂ x₃ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0;
     -(x₁ / t ^ 2), 1 / t, 0, 0;
     -(x₂ / t ^ 2), 0, 1 / t, 0;
     -(x₃ / t ^ 2), 0, 0, 1 / t]

/-- **[`div(v) = tr(Dv) = 3/t`]** The divergence of the free-particle field. -/
lemma freeParticle_div (t x₁ x₂ x₃ : ℝ) :
    (freeParticleJacobian t x₁ x₂ x₃).trace = 3 / t := by
  simp [freeParticleJacobian, Matrix.trace, Matrix.diag, Fin.sum_univ_four]
  ring

/-- **[`div(v,v) = tr((Dv)²) = 3/t²`]** The pair divergence of the free-particle field: the
off-diagonal first column never meets itself, only the diagonal `1/t` entries square. -/
lemma freeParticle_divPair (t x₁ x₂ x₃ : ℝ) :
    (freeParticleJacobian t x₁ x₂ x₃ * freeParticleJacobian t x₁ x₂ x₃).trace = 3 / t ^ 2 := by
  simp [freeParticleJacobian, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-- **[The classical vacuum divergence equation, Blume Eq. 3]** Along the trajectory through
`(t, x)` the divergence is `s ↦ 3/s`, so the directional derivative along the field is
`v[div(v)] = −3/t² = −div(v,v)`: the free-particle field satisfies
`v[div(v)] + div(v,v) = 0` — the velocity-divergence form of the classical vacuum field equation
`ΔV = 0`, verified on the explicit field. -/
theorem freeParticle_vacuum_equation (t x₁ x₂ x₃ : ℝ) (ht : t ≠ 0) :
    deriv (fun s => 3 / s) t
      + (freeParticleJacobian t x₁ x₂ x₃ * freeParticleJacobian t x₁ x₂ x₃).trace = 0 := by
  have h : HasDerivAt (fun s => 3 / s) (3 * -(t ^ 2)⁻¹) t := (hasDerivAt_inv ht).const_mul 3
  rw [h.deriv, freeParticle_divPair t x₁ x₂ x₃]
  field_simp
  ring

/-! ## B. Dust at rest in the Lorentz frame -/

/-- **The mostly-minus Minkowski metric** `η = diag(1,−1,−1,−1)` — Blume's sign convention `(+−−−)`,
in which the geodesic velocity field is unit: `g(u,u) = 1`. -/
noncomputable def etaMostlyMinus : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

/-- **[Dust is the pressureless perfect fluid]** Blume's stress-energy `T = ρ u⊗u` of a swarm of free
particles is `Cosmology.FLRW.MatterContent.perfectFluidStressEnergy` at zero pressure — the outer
product of the rest-frame velocity with itself, weighted by the density. -/
lemma dust_is_pressureless_perfectFluid (ρ c : ℝ) (u : Fin 4 → ℝ) :
    perfectFluidStressEnergy ρ 0 c u etaMostlyMinus = ρ • Matrix.vecMulVec u u := by
  simp [perfectFluidStressEnergy]

/-- **[The rest-frame outer product]** For the unit rest velocity `u = e₀ = comovingVelocity 1`, the
outer product `u⊗u` is the single-entry diagonal `diag(1,0,0,0)`. -/
lemma vecMulVec_restVelocity :
    Matrix.vecMulVec (comovingVelocity 1) (comovingVelocity 1)
      = Matrix.diagonal ![1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMulVec_apply, comovingVelocity, Matrix.diagonal]

/-- `η·η = 1` in diagonal form: the mostly-minus metric squares to the identity. -/
lemma eta_mul_eta : etaMostlyMinus * etaMostlyMinus = Matrix.diagonal ![1, 1, 1, 1] := by
  rw [etaMostlyMinus, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- `η·(u⊗u) = diag(1,0,0,0)`: contracting the metric into the dust outer product. -/
lemma eta_mul_rest :
    etaMostlyMinus * Matrix.vecMulVec (comovingVelocity 1) (comovingVelocity 1)
      = Matrix.diagonal ![1, 0, 0, 0] := by
  rw [vecMulVec_restVelocity, etaMostlyMinus, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-! ## C. The trace step and the Euclidean collapse of the Ricci matrix -/

/-- **[The dust scalar curvature, Blume Theorem 5.1 trace step]** If the Ricci matrix solves the dust
field equation `Ric = (R/2)η + (k·ε)·u⊗u` (Eq. 7 rearranged, coupling `k`, rest energy density `ε`)
and `R` is its own `η`-contraction (`ricciScalarContraction`, `η⁻¹ = η`), then `R = −k·ε`: the
`η`-trace turns `R = 2R + k·ε` (four from `tr(η·η) = tr 1`, one from `tr(η·u⊗u) = g(u,u) = 1`) into
the scalar curvature. At `k = 8π`, `ε = ρ` this is Blume's `R = −8πρ`. -/
theorem dust_scalarCurvature (Ric : Matrix (Fin 4) (Fin 4) ℝ) (R k ε : ℝ)
    (hEFE : Ric = (R / 2) • etaMostlyMinus
      + (k * ε) • Matrix.vecMulVec (comovingVelocity 1) (comovingVelocity 1))
    (hR : R = ricciScalarContraction etaMostlyMinus Ric) :
    R = -(k * ε) := by
  rw [ricciScalarContraction, hEFE, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    eta_mul_eta, eta_mul_rest, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    traceDiagFour, traceDiagFour, smul_eq_mul, smul_eq_mul] at hR
  linear_combination -hR

/-- **[The Euclidean collapse of the Ricci matrix, Blume Eq. 9]** Substituting `R = −k·ε` back into
the dust field equation collapses the Ricci matrix to `Ric = (k·ε/2)·1` — `k·ε/2` times the
**Euclidean** identity: the time-time entry gets `−k·ε/2 + k·ε`, each space-space entry gets
`+k·ε/2` from the flipped metric sign, and the Lorentzian signature disappears. At `k = 8π`, `ε = ρ`
this is `Ric = 4πρ·1`, i.e. `Ric(e_μ,e_ν) = 4πρ δ_μν`: the Einstein equation for dust stores exactly
Newton's Poisson source `4πρ` in every frame direction. -/
theorem dust_ricci_euclidean (Ric : Matrix (Fin 4) (Fin 4) ℝ) (R k ε : ℝ)
    (hEFE : Ric = (R / 2) • etaMostlyMinus
      + (k * ε) • Matrix.vecMulVec (comovingVelocity 1) (comovingVelocity 1))
    (hR : R = ricciScalarContraction etaMostlyMinus Ric) :
    Ric = (k * ε / 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hscalar := dust_scalarCurvature Ric R k ε hEFE hR
  rw [hEFE, hscalar, vecMulVec_restVelocity, etaMostlyMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

/-! ## D. The divergence equation: identical for timelike, spacelike and null directions -/

/-- The quadratic form `M(w,w) = w ⬝ (M ⬝ w)` of a frame matrix on a direction `w`. -/
noncomputable def matQuadratic (M : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ) : ℝ :=
  w ⬝ᵥ (M *ᵥ w)

/-- **[The quadratic form of a diagonal matrix]**
`diag(a,b,c,d)(w,w) = a w₀² + b w₁² + c w₂² + d w₃²`. -/
lemma matQuadratic_diagonal (a b c d : ℝ) (w : Fin 4 → ℝ) :
    matQuadratic (Matrix.diagonal ![a, b, c, d]) w
      = a * w 0 ^ 2 + b * w 1 ^ 2 + c * w 2 ^ 2 + d * w 3 ^ 2 := by
  have hv : (Matrix.diagonal ![a, b, c, d] *ᵥ w) = fun i => ![a, b, c, d] i * w i := by
    funext i; exact Matrix.mulVec_diagonal _ _ _
  rw [matQuadratic, hv, show (w ⬝ᵥ fun i => ![a, b, c, d] i * w i)
      = ∑ i, w i * (![a, b, c, d] i * w i) from rfl, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]
  ring

/-- **[The Euclidean quadratic form]** For `Ric = c·1`, `Ric(w,w) = c·(w₀² + w₁² + w₂² + w₃²)`. -/
lemma matQuadratic_smul_one (c : ℝ) (w : Fin 4 → ℝ) :
    matQuadratic (c • (1 : Matrix (Fin 4) (Fin 4) ℝ)) w
      = c * (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) := by
  rw [matQuadratic, Matrix.smul_mulVec, Matrix.one_mulVec,
    show (w ⬝ᵥ (c • w)) = ∑ i, w i * (c • w) i from rfl, Fin.sum_univ_four]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **[The Minkowski quadratic form]** `η(w,w) = w₀² − w₁² − w₂² − w₃²`. -/
lemma matQuadratic_eta (w : Fin 4 → ℝ) :
    matQuadratic etaMostlyMinus w = w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2 - w 3 ^ 2 := by
  rw [etaMostlyMinus, matQuadratic_diagonal]; ring

/-- **[The dust divergence equation, Blume Eqs. 8, 15, 16]** With the Euclidean Ricci
`Ric = 4πρ·1`, the divergence representation `w[div(w)] + div(w,w) = −Ric(w,w)` (Theorem
4.1/Corollary 4.4) evaluates to `−4πρ · Σ(wᵘ)²` — so **every direction of Euclidean unit length**
satisfies `−Ric(w,w) = −4πρ`, the same equation as the Newtonian matter field `v[div(v)] + div(v,v)
= −4πρ` (Eq. 6). The causal character of `w` is irrelevant; only the Euclidean normalization Eq. 16
enters. This is the formal identity of the two theories. -/
theorem dust_divergence_equation (Ric : Matrix (Fin 4) (Fin 4) ℝ) (ρ : ℝ) (w : Fin 4 → ℝ)
    (hRic : Ric = (4 * Real.pi * ρ) • (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (hw : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 = 1) :
    -matQuadratic Ric w = -(4 * Real.pi * ρ) := by
  rw [hRic, matQuadratic_smul_one, hw, mul_one]

/-- **[Condition (a): the timelike rest direction]** `w = u = e₀` has `η(w,w) = 1` (timelike unit)
and Euclidean norm `1`: the divergence equation gives `−4πρ`. -/
theorem dust_divergence_timelike (Ric : Matrix (Fin 4) (Fin 4) ℝ) (ρ : ℝ)
    (hRic : Ric = (4 * Real.pi * ρ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) :
    matQuadratic etaMostlyMinus (comovingVelocity 1) = 1
    ∧ -matQuadratic Ric (comovingVelocity 1) = -(4 * Real.pi * ρ) := by
  refine ⟨?_, dust_divergence_equation Ric ρ _ hRic ?_⟩ <;>
    simp [matQuadratic_eta, comovingVelocity]

/-- **[Condition (b): a spacelike unit direction]** `w = u_⊥ = e₁` has `η(w,w) = −1` (spacelike) and
Euclidean norm `1`: the divergence equation gives the same `−4πρ`. -/
theorem dust_divergence_spacelike (Ric : Matrix (Fin 4) (Fin 4) ℝ) (ρ : ℝ)
    (hRic : Ric = (4 * Real.pi * ρ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) :
    matQuadratic etaMostlyMinus ![0, 1, 0, 0] = -1
    ∧ -matQuadratic Ric ![0, 1, 0, 0] = -(4 * Real.pi * ρ) := by
  refine ⟨?_, dust_divergence_equation Ric ρ _ hRic ?_⟩ <;>
    simp [matQuadratic_eta]

/-- **[Condition (c): the null direction]** `w = (u + u_⊥)/√2` has `η(w,w) = 0` (lightlike!) yet
Euclidean norm `1`: even along the light cone the divergence equation gives the same `−4πρ`. Blume's
reading: in the `c → ∞` limit the Newtonian spatial rest frame merges with the light cone, and `(c)`
is exactly the condition that keeps the Newtonian and relativistic matter equations identified. -/
theorem dust_divergence_null (Ric : Matrix (Fin 4) (Fin 4) ℝ) (ρ : ℝ)
    (hRic : Ric = (4 * Real.pi * ρ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) :
    matQuadratic etaMostlyMinus ![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0, 0] = 0
    ∧ -matQuadratic Ric ![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0, 0] = -(4 * Real.pi * ρ) := by
  have h2 : (Real.sqrt 2)⁻¹ ^ 2 = 2⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  refine ⟨?_, dust_divergence_equation Ric ρ _ hRic ?_⟩ <;>
    · simp only [matQuadratic_eta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      rw [h2]
      ring

/-- **[The vacuum instance]** At `ρ = 0` the Euclidean Ricci vanishes and every direction satisfies
`−Ric(w,w) = 0` — the relativistic vacuum row `u[div(u)] + div(u,u) = 0` of Blume's table, the
divergence form of `R_μν = 0`. -/
theorem vacuum_divergence_equation (Ric : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ)
    (hRic : Ric = (4 * Real.pi * (0:ℝ)) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) :
    -matQuadratic Ric w = 0 := by
  rw [hRic, matQuadratic_smul_one]; ring

/-! ## E. The `8π = 4π + 4π` recontraction -/

/-- **[The dust quadratic form]** `T(x,x) = ρ·η(x,u)² = ρ·(x⁰)²` — the stress-energy quadratic form
of dust is the density times the squared time component. -/
lemma dust_quadratic (ρ : ℝ) (x : Fin 4 → ℝ) :
    matQuadratic (ρ • Matrix.vecMulVec (comovingVelocity 1) (comovingVelocity 1)) x
      = ρ * x 0 ^ 2 := by
  rw [vecMulVec_restVelocity, matQuadratic, Matrix.smul_mulVec,
    show (x ⬝ᵥ (ρ • (Matrix.diagonal ![(1:ℝ), 0, 0, 0] *ᵥ x)))
        = ∑ i, x i * (ρ • (Matrix.diagonal ![(1:ℝ), 0, 0, 0] *ᵥ x)) i from rfl, Fin.sum_univ_four]
  simp only [Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons]
  ring

/-- **[`8π = 4π + 4π`, the closing computation of Blume Theorem 5.1]** Recontracting the Euclidean
Ricci with a general direction `x`,

  `Ric(x,x) − (R/2)·η(x,x) = 4πρ·Σ(xᵘ)² + 4πρ·((x⁰)² − Σ(xⁱ)²) = 8πρ·(x⁰)² = 8π·T(x,x)`:

the **Euclidean** Ricci quadratic form contributes one `4πρ`, the **Lorentzian** scalar term
contributes the second, and their sum is Einstein's `8π` on the dust stress-energy. The doubling of
Newton's `4π` into Einstein's `8π` is nothing but this trace bookkeeping — the tensor-side face of
`Thermodynamics.GravitationalCouplingSystem.dust_traceReversed_source`. -/
theorem dust_traceReversed_recontraction (Ric : Matrix (Fin 4) (Fin 4) ℝ) (R ρ : ℝ)
    (x : Fin 4 → ℝ)
    (hRic : Ric = (4 * Real.pi * ρ) • (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (hscalar : R = -(8 * Real.pi * ρ)) :
    matQuadratic Ric x - (R / 2) * matQuadratic etaMostlyMinus x
      = 8 * Real.pi
        * matQuadratic (ρ • Matrix.vecMulVec (comovingVelocity 1) (comovingVelocity 1)) x := by
  rw [dust_quadratic, hRic, hscalar, matQuadratic_smul_one, matQuadratic_eta]
  ring

/-! ## F. Physical units: the chain to the Poisson equation -/

/-- **[Dust EFE → Poisson, in physical units]** At the Einstein coupling `k = 8πG/c⁴` and rest
energy density `ε = ρc²`, the Euclidean collapse gives `Ric = (4πGρ/c²)·1` — the `00`-entry is
`4πGρ/c²`, exactly the coupling split `κ·(ρc²/2) = 4πGρ/c²` of
`Thermodynamics.GravitationalCouplingSystem.dust_traceReversed_source`. If the weak-field `00`-Ricci
`ComptonClock.NewtonianAndGRLimit.weakFieldRicci00` matches it, the Poisson equation `∇²Φ = 4πGρ`
follows: the full chain dust EFE → `R₀₀ = 4πGρ/c²` → Newton, through Blume's frame mechanism. -/
theorem dust_efe_poisson_units (Ric : Matrix (Fin 4) (Fin 4) ℝ) (R G c ρ d2Φ : ℝ)
    (hc : c ≠ 0)
    (hEFE : Ric = (R / 2) • etaMostlyMinus
      + (8 * Real.pi * G / c ^ 4 * (ρ * c ^ 2))
          • Matrix.vecMulVec (comovingVelocity 1) (comovingVelocity 1))
    (hR : R = ricciScalarContraction etaMostlyMinus Ric)
    (hweak : weakFieldRicci00 d2Φ c = Ric 0 0) :
    Ric 0 0 = 4 * Real.pi * G * ρ / c ^ 2 ∧ d2Φ = 4 * Real.pi * G * ρ := by
  have hcollapse := dust_ricci_euclidean Ric R (8 * Real.pi * G / c ^ 4) (ρ * c ^ 2) hEFE hR
  have h00 : Ric 0 0 = 4 * Real.pi * G * ρ / c ^ 2 := by
    rw [hcollapse]
    have hsplit := dust_traceReversed_source G c ρ hc
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    linear_combination hsplit
  exact ⟨h00, weakField_einstein_poisson d2Φ c G ρ hc (hweak.trans h00)⟩

end

end Physlib.Relativity.SemiClassical.VelocityDivergenceFieldEquation

/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.VariationalCalculus.HasVarGradient
public import Physlib.SpaceAndTime.Time.Derivatives
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic
/-!

# Hamilton's equations

In this module, given a Hamiltonian function `H : Time → X → X → ℝ`,
we define the operator `hamiltonEqOp`
which when equals zero implies hamilton's equations.

We show that the variational derivative of the action functional
`∫ ⟪p, dq/dt⟫ - H(t, p, q) dt` is equal to the `hamiltonEqOp`
applied to `(p, q)`.

## References

- G. J. Sussman and J. Wisdom, "Structure and Interpretation of Classical Mechanics", Section 3.1.2.
<https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book-Z-H-36.html#%_sec_3.1.2>

-/

@[expose] public section

open MeasureTheory ContDiff InnerProductSpace Time

namespace ClassicalMechanics

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- Given a hamiltonian `H : Time → X → X → ℝ` the operator which when
  set to zero implies the Hamilton equations. -/
noncomputable def hamiltonEqOp (H : Time → X → X → ℝ) (p : Time → X) (q : Time → X) :
    Time → X × X :=
  fun t => (∂ₜ q t + -gradient (fun x => H t x (q t)) (p t),
    - ∂ₜ p t + -gradient (fun x => H t (p t) x) (q t))

lemma hamiltonEqOp_eq (H : Time → X → X → ℝ) (p : Time → X) (q : Time → X) :
    hamiltonEqOp H p q = fun t => (∂ₜ q t + -gradient (fun x => H t x (q t)) (p t),
      - ∂ₜ p t + -gradient (fun x => H t (p t) x) (q t)) := by
  rfl

lemma hamiltonEqOp_eq_zero_iff_hamiltons_equations (H : Time → X → X → ℝ)
    (p : Time → X) (q : Time → X) :
    hamiltonEqOp H p q = 0 ↔
    (∀ t, ∂ₜ q t = gradient (fun x => H t x (q t)) (p t)) ∧
    (∀ t, ∂ₜ p t = -gradient (fun x => H t (p t) x) (q t)) := by
  simp [hamiltonEqOp_eq, funext_iff, Prod.mk_eq_zero, forall_and, add_eq_zero_iff_neg_eq]

theorem hamiltons_equations_varGradient
    (H : Time → X → X → ℝ) (pq : Time → X × X) (hp : ContDiff ℝ ∞ pq)
    (hL : ContDiff ℝ ∞ ↿H) :
    (δ (pq':= pq), ∫ t, ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ - H t (pq' t).1 (pq' t).2) =
    fun t => hamiltonEqOp H (fun t => (pq t).1) (fun t => (pq t).2) t := by
  apply HasVarGradientAt.varGradient
  apply HasVarGradientAt.intro _
  · apply HasVarAdjDerivAt.add
    · let i := fun (t : Time) (x : X × X) => ⟪x.1, x.2⟫_ℝ
      apply HasVarAdjDerivAt.comp
        (F := fun (φ : Time → X × X) t => i t (φ t))
        (G := fun (φ : Time → X × X) t => ((φ t).1, fderiv ℝ (Prod.snd ∘ φ) t 1))
      · exact HasVarAdjDerivAt.fmap _ _ (by fun_prop) (by fun_prop)
          fun x _ => (by fun_prop : DifferentiableAt ℝ _ _).hasAdjFDerivAt
      · apply HasVarAdjDerivAt.prod
        · exact HasVarAdjDerivAt.fst (HasVarAdjDerivAt.id _ (by fun_prop))
        · apply HasVarAdjDerivAt.fderiv' (F := fun (φ : Time → X × X) t => (φ t).2)
          exact HasVarAdjDerivAt.fmap _ _ (by fun_prop) (by fun_prop)
            fun x _ => (by fun_prop : DifferentiableAt ℝ _ _).hasAdjFDerivAt
    · apply HasVarAdjDerivAt.neg
      exact HasVarAdjDerivAt.fmap (fun t => ↿(H t)) _ (by fun_prop) (by fun_prop)
        fun x _ => (((by fun_prop : ContDiff ℝ ∞ _).differentiable
          (by simp)).differentiableAt).hasAdjFDerivAt
  · simp only [adjFDeriv_prod_snd, Prod.mk_add_mk, add_zero, zero_add]
    funext x
    rw [adjFDeriv_uncurry
      ((by fun_prop : ContDiff ℝ ∞ _).differentiable (by simp)).differentiableAt]
    simp only [Prod.neg_mk, Prod.mk_add_mk]
    rw [adjFDeriv_inner]
    simp only [one_smul]
    conv_rhs =>
      enter [2, 1, 1, 1, 2, x]
      rw [adjFDeriv_inner]
      simp
    rw [← gradient_eq_adjFDeriv, ← gradient_eq_adjFDeriv]
    rfl
    all_goals exact ((by fun_prop : ContDiff ℝ ∞ _).differentiable (by simp)).differentiableAt

end ClassicalMechanics

namespace Physlib.Thermodynamics.SecondLaw

/-! ## Phase C — Non-Hamiltonian flow + measure-compressibility arrow

[Sergi & Ferrario 2001] introduce a finite-dimensional generalisation of
the symplectic Hamilton equations of motion,

  `ẋᵢ = ∑ⱼ B_{ij} · ∂H/∂xⱼ`     with     `B_{ij} = −B_{ji}`     (Eq. *)

Because `B` is antisymmetric, energy is automatically conserved:

  `dH/dt = ∑ᵢ (∂H/∂xᵢ) · ẋᵢ = ∑_{ij} (∂H/∂xᵢ) · B_{ij} · (∂H/∂xⱼ) = 0`,

regardless of whether the flow is Hamiltonian.  Independent of this,
the phase-space compressibility

  `κ(x) = ∑ᵢ ∂ẋᵢ/∂xᵢ`

can be non-zero (the flow contracts or expands phase-space volume),
producing a Liouville-violating measure dynamics.  Sergi & Ferrario
emphasise the *separation* this affords: conserved Hamiltonian H *and*
controllable compressibility κ.

This is the *classical* analogue of complex-action/entropic-time's `H_R = S_R / ℏ` (the
conserved part of the action) and `H_I = ℏ·γ/2` (the dissipative part).
Concretely:

  `S_R = ∫ H dt`  (conserved → no flow on it)
  `S_I = −ℏ · ∫ κ(x(t)) dt`  (statistical-weight generator)

For constant compressibility `κ = const ≤ 0` (contractive flow):

  `S_I(t) = −ℏ · κ · t`

is monotone increasing in `t` — a *classical* derivation of the entropic
arrow, sister to Phase F's quantum Sergi constant-decay derivation.

No new axioms.  Source: [Sergi & Ferrario 2001, Eqs. (1)–(*) of
"Non-Hamiltonian Equations of Motion with a Conserved Energy"].
-/

/-- **Non-Hamiltonian flow with antisymmetric structure matrix**
[Sergi & Ferrario 2001].  Data of a phase-space flow

  `ẋᵢ = ∑ⱼ B_{ij} · ∂H/∂xⱼ`

with `B` antisymmetric — energy `H` is automatically conserved
regardless of whether the flow is Hamiltonian.

The gradient `gradH` is exposed as a field (we do not assume any
specific definitional relation to `H`); consumers provide both `H`
and `gradH` consistently. -/
structure NonHamiltonianFlow (n : ℕ) where
  /-- Antisymmetric structure matrix `B : Matrix (Fin n) (Fin n) ℝ`. -/
  B : Matrix (Fin n) (Fin n) ℝ
  /-- `B` is antisymmetric: `B i j = − B j i`. -/
  B_antisymm : ∀ i j, B i j = -B j i
  /-- The Hamiltonian (conserved dynamical generator). -/
  H : (Fin n → ℝ) → ℝ
  /-- Gradient of the Hamiltonian, `(∂H/∂xᵢ)`. -/
  gradH : (Fin n → ℝ) → (Fin n → ℝ)

namespace NonHamiltonianFlow

variable {n : ℕ} (F : NonHamiltonianFlow n)

/-- **Velocity field**: `velocity = B.mulVec gradH(x)` (Sergi & Ferrario). -/
def velocity (x : Fin n → ℝ) : Fin n → ℝ := Matrix.mulVec F.B (F.gradH x)

/-- **Energy time-derivative**: `dH/dt = dotProduct gradH(x) velocity`. -/
def energyRate (x : Fin n → ℝ) : ℝ :=
  dotProduct (F.gradH x) (F.velocity x)

/-- **Energy conservation theorem** (Sergi & Ferrario):

  `dH/dt = dotProduct gradH (B.mulVec gradH) = 0`

for antisymmetric `B`.  Proof via the `S = −S` route: use
`dotProduct_mulVec`, transpose `B` to `−B`, then commute the
dot product. -/
theorem energyRate_eq_zero (x : Fin n → ℝ) : F.energyRate x = 0 := by
  unfold energyRate velocity
  have hBT : F.B.transpose = -F.B := by
    funext i j
    show F.B j i = -F.B i j
    exact F.B_antisymm j i
  have h : dotProduct (F.gradH x) (Matrix.mulVec F.B (F.gradH x))
         = -dotProduct (F.gradH x) (Matrix.mulVec F.B (F.gradH x)) := by
    -- Rewrite ONLY the LHS via conv_lhs so rewriting doesn't propagate to RHS.
    -- Chain: g ⬝ᵥ B *ᵥ g  =  (g ᵥ* B) ⬝ᵥ g           [dotProduct_mulVec]
    --                    =  (Bᵀ *ᵥ g) ⬝ᵥ g           [vecMul/transpose swap]
    --                    =  ((-B) *ᵥ g) ⬝ᵥ g         [hBT]
    --                    =  -(B *ᵥ g) ⬝ᵥ g           [neg_mulVec]
    --                    =  -((B *ᵥ g) ⬝ᵥ g)         [neg_dotProduct]
    --                    =  -(g ⬝ᵥ (B *ᵥ g))         [dotProduct_comm]  — this is RHS.
    conv_lhs =>
      rw [Matrix.dotProduct_mulVec,
          show (Matrix.vecMul (F.gradH x) F.B)
                = Matrix.mulVec F.B.transpose (F.gradH x) from by
            rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose],
          hBT, Matrix.neg_mulVec, neg_dotProduct,
          dotProduct_comm (Matrix.mulVec F.B (F.gradH x)) (F.gradH x)]
  linarith

end NonHamiltonianFlow

/-! ### Reduction to standard Hamilton's equations

The Sergi-Ferrario framework reduces to **standard Hamiltonian mechanics**
when the structure matrix `B` is the canonical symplectic matrix.  For a
single degree of freedom (n = 2, with `x = (q, p)`), the canonical
symplectic matrix is

  `J = !![0, 1; -1, 0]`,

which is antisymmetric.  The resulting `NonHamiltonianFlow` produces

  `ẋ₀ = q̇ = +∂H/∂p`,    `ẋ₁ = ṗ = −∂H/∂q`,

the standard Hamilton equations of motion.  In this regime the
phase-space compressibility vanishes identically (`κ = 0`, Liouville's
theorem), so the Sergi-Ferrario entropic arrow trivialises: standard
Hamiltonian mechanics is the *no-dissipation* limit of the framework. -/

/-- **Canonical symplectic matrix** on `Fin 2` (single degree of freedom):
`J = !![0, 1; -1, 0]`.  Antisymmetric, `J = -J^T`. -/
def symplecticForm2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0]

/-- `symplecticForm2` is antisymmetric. -/
theorem symplecticForm2_antisymm :
    ∀ i j : Fin 2, symplecticForm2 i j = -symplecticForm2 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [symplecticForm2]

/-- **Standard Hamiltonian flow as an instance of `NonHamiltonianFlow`**:
single DOF with the canonical symplectic structure matrix `J`. -/
noncomputable def NonHamiltonianFlow.ofHamiltonian2
    (H : (Fin 2 → ℝ) → ℝ) (gradH : (Fin 2 → ℝ) → (Fin 2 → ℝ)) :
    NonHamiltonianFlow 2 where
  B := symplecticForm2
  B_antisymm := symplecticForm2_antisymm
  H := H
  gradH := gradH

/-- **Hamilton's equation (first component)**: `q̇ = +∂H/∂p`.

For a Sergi-Ferrario flow with the canonical symplectic `J`, the
velocity at index 0 (the q-component) equals `gradH x 1` (the
p-component of the gradient, i.e. `∂H/∂p`). -/
theorem ofHamiltonian2_velocity_q_eq_dHdp
    (H : (Fin 2 → ℝ) → ℝ) (gradH : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
    (NonHamiltonianFlow.ofHamiltonian2 H gradH).velocity x 0 = gradH x 1 := by
  unfold NonHamiltonianFlow.velocity NonHamiltonianFlow.ofHamiltonian2
  show Matrix.mulVec symplecticForm2 (gradH x) 0 = gradH x 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, symplecticForm2]

/-- **Hamilton's equation (second component)**: `ṗ = −∂H/∂q`. -/
theorem ofHamiltonian2_velocity_p_eq_neg_dHdq
    (H : (Fin 2 → ℝ) → ℝ) (gradH : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
    (NonHamiltonianFlow.ofHamiltonian2 H gradH).velocity x 1 = -gradH x 0 := by
  unfold NonHamiltonianFlow.velocity NonHamiltonianFlow.ofHamiltonian2
  show Matrix.mulVec symplecticForm2 (gradH x) 1 = -gradH x 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, symplecticForm2]

/-- **Energy conservation in the Hamiltonian limit** — corollary of
`energyRate_eq_zero` for any antisymmetric B.  Standard Hamilton's
equations conserve energy automatically: `dH/dt = 0`. -/
theorem ofHamiltonian2_energy_conservation
    (H : (Fin 2 → ℝ) → ℝ) (gradH : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
    (NonHamiltonianFlow.ofHamiltonian2 H gradH).energyRate x = 0 :=
  (NonHamiltonianFlow.ofHamiltonian2 H gradH).energyRate_eq_zero x

/-- **Non-Hamiltonian measure-compressibility bridge** [Sergi & Ferrario 2001]:

For a flow with constant compressibility `κ ≤ 0` (Liouville-volume
*contraction*), the entropic-time generator is

  `S_I(t) = −ℏ · κ · t`,

monotone non-decreasing in `t`.  This is the *classical* analogue of
the quantum Sergi constant-decay arrow (Phase F): the imaginary action
emerges from phase-space measure compression while real-energy
conservation is preserved.

We expose this as a *scalar representative*; the flow's energy conservation
`H` is decoupled from the compressibility `κ` so that the same H can be
paired with any κ ≤ 0. -/
structure NonHamiltonianMeasureBridge where
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ
  /-- Phase-space compressibility `κ = ∇·ẋ` (constant along the
      worldline — the simplest non-trivial case). -/
  κ : ℝ
  /-- `κ ≤ 0`: the flow contracts phase-space volume (the entropic-arrow
      condition). -/
  κ_nonpos : κ ≤ 0

namespace NonHamiltonianMeasureBridge

variable (M : NonHamiltonianMeasureBridge)

/-- Imaginary action along the worldline: `S_I(t) = −ℏ · κ · t`. -/
noncomputable def S_I_along (t : ℝ) : ℝ := -M.ℏ * M.κ * t

@[simp]
theorem S_I_along_at_zero : M.S_I_along 0 = 0 := by
  unfold S_I_along; ring

/-- `−ℏ · κ ≥ 0` from `ℏ > 0` and `κ ≤ 0`. -/
theorem neg_hbar_kappa_nonneg : 0 ≤ -M.ℏ * M.κ := by
  have h₁ : 0 ≤ -M.κ := by linarith [M.κ_nonpos]
  nlinarith [M.ℏ_pos]

/-- **The classical entropic-arrow theorem**: `S_I_along` is monotone
non-decreasing, derived from `ℏ > 0` and `κ ≤ 0` alone (the contractive
condition on the non-Hamiltonian flow). -/
theorem S_I_along_monotone : Monotone M.S_I_along := by
  intro t₁ t₂ h
  unfold S_I_along
  exact mul_le_mul_of_nonneg_left h M.neg_hbar_kappa_nonneg

/-- Entropic proper time `τ_ent(t) = S_I(t)/ℏ = -κ·t`. -/
noncomputable def τ_ent_along (t : ℝ) : ℝ := -M.κ * t

@[simp]
theorem τ_ent_along_eq_S_I_div_hbar (t : ℝ) :
    M.τ_ent_along t = M.S_I_along t / M.ℏ := by
  unfold τ_ent_along S_I_along
  have h : M.ℏ ≠ 0 := ne_of_gt M.ℏ_pos
  field_simp

/-! ### Liouville reduction: κ = 0 ⇒ trivial entropic arrow

In the Hamiltonian (symplectic-`B`) limit, phase-space volume is
preserved by Liouville's theorem, so the Sergi-Ferrario compressibility
vanishes: `κ = 0`.  In this regime the entropic-time arrow trivialises
— there is no imaginary-action accumulation and `τ_ent ≡ 0`.

Standard Hamiltonian mechanics is recovered as the `κ = 0` regime of
the Sergi-Ferrario / `NonHamiltonianMeasureBridge` framework. -/

/-- **Liouville/Hamiltonian limit**: when `κ = 0`, the imaginary action
along the worldline vanishes identically: `S_I_along t = 0`.

Recovers the standard Hamiltonian conservation regime: no entropic-time
arrow when the flow is volume-preserving. -/
@[simp]
theorem S_I_along_eq_zero_of_κ_zero (hκ : M.κ = 0) (t : ℝ) :
    M.S_I_along t = 0 := by
  unfold S_I_along
  rw [hκ]; ring

/-- **Liouville/Hamiltonian limit**: when `κ = 0`, the entropic proper
time vanishes identically: `τ_ent_along t = 0`. -/
@[simp]
theorem τ_ent_along_eq_zero_of_κ_zero (hκ : M.κ = 0) (t : ℝ) :
    M.τ_ent_along t = 0 := by
  unfold τ_ent_along
  rw [hκ]; ring

end NonHamiltonianMeasureBridge

end Physlib.Thermodynamics.SecondLaw

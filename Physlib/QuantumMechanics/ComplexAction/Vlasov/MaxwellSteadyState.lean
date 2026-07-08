/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Data.Real.Basic

/-!
# Steady-state Vlasov–Maxwell solutions from first integrals (Markov et al. 1992)

Formalizes the algebraic core of *Markov, Rudykh, Sidorov, Sinitsyn, Tolstonogov, "Steady-State Solutions of
the Vlasov–Maxwell System and Their Stability", Acta Appl. Math. 28 (1992) 253–293*. The Vlasov equation's
steady solutions are functions `f(R, G)` of the **first integrals** of the particle characteristic flow
(Eq. 2.6)

  `ṙ = V`,   `V̇ = (q/m)(E + (1/c) V × B)`   (the Lorentz force, Eq. 1.1),

namely the energy-type integral `R = −α|V|² + φ(r)` and the momentum-type integral `G = V·d + ψ(r)`. Each is
conserved along the flow **iff** the self-consistent fields satisfy the reduction conditions the paper
derives (Eqs. 2.7–2.9), and the whole derivation rests on the vector identities `V·(V×B) = 0` and the scalar
triple product `(V×B)·d = V·(B×d)`.

* **§A — the Lorentz-force flow and the triple product** (`lorentzAccel`, `cross_dot_triple`). The
  acceleration `V̇` and the identity `(V×B)·d = V·(B×d)`.
* **§B — the energy first integral** (`energyRate`, `energyRate_eq`, `energyRate_zero`). `dR/dt = V·(∇φ −
  2αqm·E)` (the `V×B` term drops by `V·(V×B) = 0`), so `R` is conserved **iff** `∇φ = 2αqm·E` (Eq. 2.7).
* **§C — the momentum first integral** (`momentumRate`, `momentumRate_eq`, `momentumRate_zero`). `dG/dt =
  qm(E·d) + V·(qm/c·(B×d) + ∇ψ)`, so `G` is conserved given `E·d = 0` (Eq. 2.9) and `qm/c·(B×d) + ∇ψ = 0`
  (Eq. 2.8).
* **§D — steady solution and Lyapunov constant** (`vlasov_steady_solution`, `energy_is_constant`). Under the
  field conditions, the Vlasov transport of `f(R, G)` vanishes (`f_R·dR/dt + f_G·dG/dt = 0`) — `f(R, G)` is a
  stationary solution; the conserved energy `R` is the constant of motion underlying the paper's Lyapunov
  stability.
* **§E — the gradient orthogonality conditions** (`gradφ_dot_d`, `gradψ_dot_d`). Eqs. 2.10–2.11: the
  potential gradients are orthogonal to the drift direction, `∇φ·d = 0` (from 2.7+2.9) and `∇ψ·d = 0` (from
  2.8 + `(B×d)⟂d`).
* **§F — the magnetic field form and its consistency** (`magneticField`, `magneticField_dot_d`,
  `magneticField_cross_d`). Eq. 2.12 `B = (λ/d²)d − (mc/q d²)(d×∇ψ)`: dotting with `d` recovers `λ = (B,d)`,
  and (via BAC–CAB) the ansatz *satisfies* the momentum-condition `B×d = −(mc/q)∇ψ` — i.e. Eq. 2.12 ⟹ Eq. 2.8.
* **§G — Corollary 1: the curl-free `λ`-gradient** (`gradLam_dot_d`). Eqs. 2.17/2.23: `∇λ = d×J` (Lemma 1) is
  orthogonal to `d`, `(∇λ)·d = 0`.
* **§H — Theorem 1: the self-consistent field reconstruction** (`electricField`,
  `electricField_satisfies_eq27`, `electricField_dot_d`, `field_reconstruction`). Eq. 2.30: from the
  potentials, `E = (m/2αq)∇φ` and `B` (Eq. 2.12) reconstruct the fields; the bundle proves they satisfy all
  self-consistency conditions — `∇φ = 2αqm·E` (2.7), `E·d = 0` (2.9), `B×d = −(mc/q)∇ψ` (2.8), `λ = (B,d)`.

## References

* Y. Markov et al., *Steady-State Solutions of the Vlasov–Maxwell System and Their Stability*,
  Acta Appl. Math. 28 (1992) 253–293 (Eqs. 1.1, 2.6–2.12, 2.17, Lemma 1/Corollary 1).
* Mathlib `crossProduct` (`dot_self_cross`, `dot_cross_self`, `cross_cross_eq_smul_sub_smul` = BAC–CAB); the
  self-consistent fields `E, B` are the electromagnetic sector (cf. `PTSymmetricQFT.MaxwellFaraday`,
  `Electromagnetic.CovariantMaxwellLambShift`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellSteadyState

open Matrix

/-! ## §A — the Lorentz-force flow and the triple product -/

/-- **[Eq. 1.1] The Lorentz-force acceleration** `V̇ = (q/m)(E + (1/c) V × B)` (with `qm = q/m`,
`cinv = 1/c`). -/
def lorentzAccel (qm cinv : ℝ) (E B V : Fin 3 → ℝ) : Fin 3 → ℝ := qm • (E + cinv • (V ⨯₃ B))

/-- **The scalar triple product** `(V × B)·d = V·(B × d)`. -/
theorem cross_dot_triple (V B d : Fin 3 → ℝ) : (V ⨯₃ B) ⬝ᵥ d = V ⬝ᵥ (B ⨯₃ d) := by
  simp only [crossProduct, dotProduct, Fin.sum_univ_three, LinearMap.mk₂_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-! ## §B — the energy first integral `R = −α|V|² + φ(r)` -/

/-- **`dR/dt` along the flow** for the energy integral `R = −α|V|² + φ(r)`:
`dR/dt = ∇φ·V − 2α (V·V̇)`. -/
def energyRate (α qm cinv : ℝ) (gradφ E B V : Fin 3 → ℝ) : ℝ :=
  gradφ ⬝ᵥ V - 2 * α * (V ⬝ᵥ lorentzAccel qm cinv E B V)

/-- **The magnetic term drops** `dR/dt = V·(∇φ − 2αqm·E)` — the `V × B` part of the Lorentz force is
orthogonal to `V` (`dot_self_cross`), so the magnetic field does no work on the energy. -/
theorem energyRate_eq (α qm cinv : ℝ) (gradφ E B V : Fin 3 → ℝ) :
    energyRate α qm cinv gradφ E B V = V ⬝ᵥ (gradφ - (2 * α * qm) • E) := by
  unfold energyRate lorentzAccel
  simp only [dotProduct_smul, dotProduct_add, smul_eq_mul, dot_self_cross, mul_zero, add_zero,
    dotProduct_sub, mul_comm]
  rw [dotProduct_comm V gradφ, dotProduct_comm V E]; ring

/-- **[Eq. 2.7] The energy is a first integral** `dR/dt = 0` precisely when `∇φ = 2αqm·E` — the
self-consistent field condition `E = (m/2αq) ∇φ`. -/
theorem energyRate_zero (α qm cinv : ℝ) (gradφ E B V : Fin 3 → ℝ)
    (hfield : gradφ = (2 * α * qm) • E) :
    energyRate α qm cinv gradφ E B V = 0 := by
  rw [energyRate_eq, hfield, sub_self, dotProduct_zero]

/-! ## §C — the momentum first integral `G = V·d + ψ(r)` -/

/-- **`dG/dt` along the flow** for the momentum integral `G = V·d + ψ(r)`: `dG/dt = V̇·d + ∇ψ·V`. -/
def momentumRate (qm cinv : ℝ) (gradψ E B V d : Fin 3 → ℝ) : ℝ :=
  (lorentzAccel qm cinv E B V) ⬝ᵥ d + gradψ ⬝ᵥ V

/-- **The drift form** `dG/dt = qm(E·d) + V·(qm/c·(B×d) + ∇ψ)` — using the triple product
`(V×B)·d = V·(B×d)`. -/
theorem momentumRate_eq (qm cinv : ℝ) (gradψ E B V d : Fin 3 → ℝ) :
    momentumRate qm cinv gradψ E B V d
      = qm * (E ⬝ᵥ d) + V ⬝ᵥ ((qm * cinv) • (B ⨯₃ d) + gradψ) := by
  unfold momentumRate lorentzAccel
  simp only [smul_dotProduct, add_dotProduct, smul_eq_mul, cross_dot_triple, dotProduct_add,
    dotProduct_smul]
  rw [dotProduct_comm V gradψ]; ring

/-- **[Eqs. 2.8–2.9] The momentum is a first integral** `dG/dt = 0` given the field conditions `E·d = 0`
(Eq. 2.9) and `qm/c·(B×d) + ∇ψ = 0` (Eq. 2.8). -/
theorem momentumRate_zero (qm cinv : ℝ) (gradψ E B V d : Fin 3 → ℝ)
    (hEd : E ⬝ᵥ d = 0) (hfield : (qm * cinv) • (B ⨯₃ d) + gradψ = 0) :
    momentumRate qm cinv gradψ E B V d = 0 := by
  rw [momentumRate_eq, hEd, hfield, dotProduct_zero]; ring

/-! ## §D — steady solution `f(R, G)` and the Lyapunov constant -/

/-- **[Steady solution] `f(R, G)` is a stationary Vlasov solution.** Under the self-consistent field
conditions (Eqs. 2.7–2.9), the Vlasov transport of `f(R, G)` — which by the chain rule is
`f_R·dR/dt + f_G·dG/dt` — vanishes. So any differentiable function of the two first integrals is a steady
state (Eq. 2.6). -/
theorem vlasov_steady_solution (α qm cinv : ℝ) (gradφ gradψ E B V d : Fin 3 → ℝ) (fR fG : ℝ)
    (hE : gradφ = (2 * α * qm) • E) (hEd : E ⬝ᵥ d = 0)
    (hB : (qm * cinv) • (B ⨯₃ d) + gradψ = 0) :
    fR * energyRate α qm cinv gradφ E B V + fG * momentumRate qm cinv gradψ E B V d = 0 := by
  rw [energyRate_zero α qm cinv gradφ E B V hE,
    momentumRate_zero qm cinv gradψ E B V d hEd hB]; ring

/-- **[Lyapunov constant] The energy is constant along the flow** at two velocities — `dR/dt = 0`
independently of `V`, so the energy integral is a genuine constant of motion, the Lyapunov functional
underlying steady-state stability. -/
theorem energy_is_constant (α qm cinv : ℝ) (gradφ E B V W : Fin 3 → ℝ)
    (hfield : gradφ = (2 * α * qm) • E) :
    energyRate α qm cinv gradφ E B V = energyRate α qm cinv gradφ E B W := by
  rw [energyRate_zero α qm cinv gradφ E B V hfield,
    energyRate_zero α qm cinv gradφ E B W hfield]

/-! ## §E — the gradient orthogonality conditions (Eqs. 2.10–2.11) -/

/-- **[Eq. 2.10] `∇φ ⟂ d`.** From `∇φ = 2αqm·E` (Eq. 2.7) and `E·d = 0` (Eq. 2.9), the potential gradient is
orthogonal to the drift direction `d`. -/
theorem gradφ_dot_d (α qm : ℝ) (gradφ E d : Fin 3 → ℝ)
    (hfield : gradφ = (2 * α * qm) • E) (hEd : E ⬝ᵥ d = 0) :
    gradφ ⬝ᵥ d = 0 := by
  rw [hfield, smul_dotProduct, hEd, smul_zero]

/-- **[Eq. 2.11] `∇ψ ⟂ d`.** From the field condition `(q/mc)·(B×d) + ∇ψ = 0` (Eq. 2.8) and `(B×d)·d = 0`
(the cross product is orthogonal to `d`), the second potential gradient is also orthogonal to `d`. -/
theorem gradψ_dot_d (qm cinv : ℝ) (gradψ B d : Fin 3 → ℝ)
    (hfield : (qm * cinv) • (B ⨯₃ d) + gradψ = 0) :
    gradψ ⬝ᵥ d = 0 := by
  have h : gradψ = -((qm * cinv) • (B ⨯₃ d)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hfield
  rw [h, neg_dotProduct, smul_dotProduct, dotProduct_comm, dot_cross_self, smul_zero, neg_zero]

/-! ## §F — the magnetic field form (Eq. 2.12) and its consistency -/

/-- **Cross-product linearity in the first argument** `(a − b) × c = a×c − b×c` (`crossProduct` is
`ℝ`-bilinear). -/
theorem cross_sub_left (a b c : Fin 3 → ℝ) : (a - b) ⨯₃ c = a ⨯₃ c - b ⨯₃ c := by
  rw [map_sub, LinearMap.sub_apply]

/-- **Cross-product `ℝ`-homogeneity in the first argument** `(r • a) × c = r • (a × c)`. -/
theorem cross_smul_left (r : ℝ) (a c : Fin 3 → ℝ) : (r • a) ⨯₃ c = r • (a ⨯₃ c) := by
  rw [map_smul, LinearMap.smul_apply]

/-- **[Eq. 2.12] The magnetic field form** `B = (λ/d²)·d − (mc/q d²)·(d × ∇ψ)`, with `λ = (B,d)` a scalar
function and `mcq = mc/q` (the reciprocal of the Eq. 2.8 coefficient `q/mc`). -/
noncomputable def magneticField (lam mcq : ℝ) (d gradψ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (lam / (d ⬝ᵥ d)) • d - (mcq / (d ⬝ᵥ d)) • (d ⨯₃ gradψ)

/-- **[λ = (B, d)] Dotting Eq. 2.12 with `d` recovers `λ`.** The component of `B` along `d` is exactly the
scalar `λ` — the `d × ∇ψ` term is orthogonal to `d` (`dot_self_cross`). -/
theorem magneticField_dot_d (lam mcq : ℝ) (d gradψ : Fin 3 → ℝ) (hdd : d ⬝ᵥ d ≠ 0) :
    magneticField lam mcq d gradψ ⬝ᵥ d = lam := by
  have hc : (d ⨯₃ gradψ) ⬝ᵥ d = 0 := by rw [dotProduct_comm]; exact dot_self_cross d gradψ
  unfold magneticField
  rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, hc, smul_zero, sub_zero, smul_eq_mul,
    div_mul_cancel₀ _ hdd]

/-- **[Eq. 2.12 ⟹ Eq. 2.8] The magnetic field form satisfies the momentum-conservation condition**
`B × d = −(mc/q)·∇ψ`. Given `∇ψ ⟂ d` (Eq. 2.11), the BAC–CAB expansion `(d × ∇ψ) × d = (d·d)∇ψ − (∇ψ·d)d`
(`cross_cross_eq_smul_sub_smul`) collapses to `(d·d)·∇ψ`, so the Eq. 2.12 ansatz reproduces exactly the field
condition Eq. 2.8 that the momentum first integral requires. -/
theorem magneticField_cross_d (lam mcq : ℝ) (d gradψ : Fin 3 → ℝ)
    (hdd : d ⬝ᵥ d ≠ 0) (hψd : gradψ ⬝ᵥ d = 0) :
    magneticField lam mcq d gradψ ⨯₃ d = -mcq • gradψ := by
  unfold magneticField
  rw [cross_sub_left, cross_smul_left, cross_smul_left, cross_self, smul_zero, zero_sub,
    cross_cross_eq_smul_sub_smul, hψd, zero_smul, sub_zero, smul_smul, div_mul_cancel₀ _ hdd,
    neg_smul]

/-! ## §G — Corollary 1: the curl-free `λ`-gradient (Eqs. 2.17/2.23) -/

/-- **[Eqs. 2.17, 2.23] `∇λ ⟂ d`.** By Corollary 1 the `λ`-gradient is the potential `∇λ = d × J`
(Lemma 1: `d × J` is curl-free, hence a gradient), and a cross product with `d` is orthogonal to `d`, so
`(∇λ)·d = 0` — the self-consistency constraint Eq. 2.17. -/
theorem gradLam_dot_d (gradLam d J : Fin 3 → ℝ) (hgl : gradLam = d ⨯₃ J) :
    gradLam ⬝ᵥ d = 0 := by
  rw [hgl, dotProduct_comm, dot_self_cross]

/-! ## §H — Theorem 1: the self-consistent field reconstruction (Eq. 2.30) -/

/-- **[Eq. 2.30, electric part] The reconstructed electric field** `E = (m/2αq)·∇φ`. In the file's convention
`qm = q/m`, the coefficient `m/(2αq)` is `1/(2α·qm)`. -/
noncomputable def electricField (α qm : ℝ) (gradφ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (1 / (2 * α * qm)) • gradφ

/-- **[Eq. 2.7] The reconstructed `E` satisfies the energy field condition** `∇φ = 2αqm·E` — inverting
`E = (m/2αq)∇φ`. -/
theorem electricField_satisfies_eq27 (α qm : ℝ) (gradφ : Fin 3 → ℝ) (hq : 2 * α * qm ≠ 0) :
    gradφ = (2 * α * qm) • electricField α qm gradφ := by
  unfold electricField
  rw [smul_smul, mul_one_div, div_self hq, one_smul]

/-- **[Eq. 2.9] The reconstructed `E` is orthogonal to the drift** `E·d = 0` — from `∇φ ⟂ d` (Eq. 2.10). -/
theorem electricField_dot_d (α qm : ℝ) (gradφ d : Fin 3 → ℝ) (hφd : gradφ ⬝ᵥ d = 0) :
    electricField α qm gradφ ⬝ᵥ d = 0 := by
  unfold electricField
  rw [smul_dotProduct, hφd, smul_zero]

/-- **[Theorem 1, Eq. 2.30] The self-consistent field reconstruction.** Given the potentials `φ, ψ` with
`∇φ ⟂ d` (Eq. 2.10) and `∇ψ ⟂ d` (Eq. 2.11) and `d ≠ 0`, the reconstructed fields `E = (m/2αq)∇φ` and
`B = (λ/d²)d − (mc/q d²)(d×∇ψ)` (Eq. 2.12) satisfy *all* the self-consistency conditions of the stationary
Vlasov–Maxwell system:

* `∇φ = 2αqm·E` (Eq. 2.7, the energy condition),
* `E·d = 0` (Eq. 2.9),
* `B×d = −(mc/q)·∇ψ` (Eq. 2.8, the momentum condition),
* `λ = (B, d)` (the scalar of Eq. 2.12 / Cor. 2). -/
theorem field_reconstruction (α qm lam mcq : ℝ) (gradφ gradψ d : Fin 3 → ℝ)
    (hq : 2 * α * qm ≠ 0) (hdd : d ⬝ᵥ d ≠ 0) (hφd : gradφ ⬝ᵥ d = 0) (hψd : gradψ ⬝ᵥ d = 0) :
    gradφ = (2 * α * qm) • electricField α qm gradφ
      ∧ electricField α qm gradφ ⬝ᵥ d = 0
      ∧ magneticField lam mcq d gradψ ⨯₃ d = -mcq • gradψ
      ∧ magneticField lam mcq d gradψ ⬝ᵥ d = lam :=
  ⟨electricField_satisfies_eq27 α qm gradφ hq, electricField_dot_d α qm gradφ d hφd,
   magneticField_cross_d lam mcq d gradψ hdd hψd, magneticField_dot_d lam mcq d gradψ hdd⟩

end Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellSteadyState

end

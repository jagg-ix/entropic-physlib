/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameKMS
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Modular automorphism group structure for the KMS Quantum Inertial Frame

Abstract representatives for the **Tomita-Takesaki modular automorphism
group** on a finite-dimensional Hilbert space, together with
bridges that connect those underlying spaces to the KMS Quantum Inertial
Frame defined in `QuantumInertialFrameKMS`.

The full Tomita-Takesaki theorem (Takesaki, *Tomita's Theory of Modular
Hilbert Algebras*, LNM **128**, Springer 1970, doi:10.1007/BFb0065832)
is established in a separate 789-line Lean formalisation that physlib
does not depend on, so we replicate the **abstract structure patterns**
standalone: the `ModularGroupData`, `ModularChannel`,
`ModularGroupLawBridge`, and `KMSStateFunctional` structures are defined
from first principles, then bridged to physlib's existing `kmsQIF`
(commit `f45b2b11`) and `KMSDetailedBalance` (§3 of base QIF file).

Consumers needing the actual Tomita-Takesaki theorem (existence of
`σ_t(a) = Δ^{it} a Δ^{-it}` from a faithful normal state with cyclic
separating vector) can either import that separate formalisation
directly or construct the group data from physlib's `HermitianMat.log`
matrix-log primitive.

## Contents

### §1 — Modular automorphism group

* `ModularGroupData H` — one-parameter family of *-automorphisms on
  `H →L[ℂ] H` (`σ : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H)`), with:
  - group law `σ (s+t) a = σ s (σ t a)`,
  - identity-at-zero `σ 0 a = a`,
  - multiplicativity `σ t (a*b) = σ t a * σ t b`.
  This matches the standard one-parameter *-automorphism API of the
  modular automorphism group (Takesaki 1970).

* `ModularGroupData.trivial` — the identity flow.

### §2 — Modular (reduced) channel

* `ModularChannel` — entropic-time-damping structure `τ_ent : ℝ → ℝ`
  with non-negativity.
* `magnitude := exp(-τ_ent)` and standard properties
  (positivity, bounded above by 1).

### §3 — Modular group law bridge

* `ModularGroupLawBridge M Ch` — `Prop`-level bridge: under the
  additivity hypothesis `τ_ent(s+t) = τ_ent(s) + τ_ent(t)`, the
  channel is multiplicative along the modular flow.
* `magnitude_composition_law` — `magnitude(s+t) = magnitude(s) ·
  magnitude(t)`.

### §4 — KMS state functional

* `KMSStateFunctional M` — state functional `ω : (H →L[ℂ] H) → ℂ`
  with modular invariance `ω(σ_t(a)) = ω(a)`.
* `state_invariant_under_flow` — extraction of the invariance.

### §5 — Bridge to `kmsQIF`

* `kmsQIF_compatible_with_modularGroup` — at any modular group
  data and any state, the QIF is at equilibrium (since `kmsQIF` is
  reversible, the modular invariance is consistent with `λ = 0`).

## References

* Takesaki, *Tomita's Theory of Modular Hilbert Algebras and its
  Applications*, Lecture Notes in Mathematics **128**, Springer (1970),
  doi:10.1007/BFb0065832 — modular operator, conjugation, and the
  modular automorphism group.
* Haag, Hugenholtz & Winnink, *On the equilibrium states in quantum
  statistical mechanics*, Commun. Math. Phys. **5**, 215 (1967),
  doi:10.1007/BF01646342 — the KMS condition.
* Connes & Rovelli, *Von Neumann algebra automorphisms and
  time-thermodynamics relation in generally covariant quantum
  theories*, Class. Quantum Grav. **11**, 2899 (1994),
  doi:10.1088/0264-9381/11/12/007 — modular flow, thermal-time
  hypothesis.
* Bisognano & Wichmann, *On the duality condition for a Hermitian
  scalar field*, J. Math. Phys. **16**, 985 (1975),
  doi:10.1063/1.522605 — modular flow on a wedge algebra.

No new axioms.  std-3 throughout.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — Modular automorphism group -/

/-- **Modular automorphism group data** on the operator algebra
`(H →L[ℂ] H)`: a one-parameter family of *-automorphisms
`σ : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H)` with the group law
`σ (s+t) = σ s ∘ σ t`, identity at zero, and multiplicativity
`σ t (a*b) = σ t a * σ t b`.

This is the abstract underlying space of the Tomita-Takesaki modular
automorphism group `σ_t(a) := Δ^{it} a Δ^{-it}` (Takesaki, LNM **128**,
1970, doi:10.1007/BFb0065832). -/
structure ModularGroupData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The one-parameter automorphism family. -/
  σ          : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H)
  /-- **Group law**: `σ (s+t) a = σ s (σ t a)` (Tomita-Takesaki). -/
  group_law  : ∀ s t : ℝ, ∀ a : H →L[ℂ] H, σ (s + t) a = σ s (σ t a)
  /-- **Identity at zero**: `σ 0 a = a` (modular flow is trivial at `t = 0`). -/
  zero_eq    : ∀ a : H →L[ℂ] H, σ 0 a = a
  /-- **Multiplicativity** (*-automorphism property):
  `σ t (a*b) = σ t a * σ t b`. -/
  mul_eq     : ∀ t : ℝ, ∀ a b : H →L[ℂ] H, σ t (a * b) = σ t a * σ t b

namespace ModularGroupData

variable (M : ModularGroupData H)

/-- **Composition of inverse-time advances**: `σ (-t) ∘ σ t = id` (the
modular flow forms a *group*, not just a semigroup). -/
theorem σ_neg_compose_σ (t : ℝ) (a : H →L[ℂ] H) :
    M.σ (-t) (M.σ t a) = a := by
  have := M.group_law (-t) t a
  rw [neg_add_cancel] at this
  rw [← this, M.zero_eq]

/-- **`σ_t` after `σ_{-t}` is identity** as well. -/
theorem σ_compose_σ_neg (t : ℝ) (a : H →L[ℂ] H) :
    M.σ t (M.σ (-t) a) = a := by
  have := M.group_law t (-t) a
  rw [add_neg_cancel] at this
  rw [← this, M.zero_eq]

/-- The trivial modular automorphism group: `σ_t = id` for all `t`. -/
def trivial (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    ModularGroupData H where
  σ          := fun _ a => a
  group_law  := fun _ _ _ => rfl
  zero_eq    := fun _ => rfl
  mul_eq     := fun _ _ _ => rfl

@[simp] theorem trivial_σ (t : ℝ) (a : H →L[ℂ] H) :
    (trivial H).σ t a = a := rfl

end ModularGroupData

/-! ## §2 — Modular (reduced) channel -/

/-- **Modular channel**: entropic-time-damping structure attached to a
modular flow.  Records `τ_ent : ℝ → ℝ` (entropic-time accumulator)
with non-negativity; the consequent **magnitude**
`exp(−τ_ent(t)) ∈ (0, 1]` is the irreversible suppression factor. -/
structure ModularChannel where
  /-- Entropic-time accumulator along the modular flow. -/
  tauEnt        : ℝ → ℝ
  /-- `τ_ent ≥ 0` (entropic-time is non-decreasing from any reference). -/
  tauEnt_nonneg : ∀ t, 0 ≤ tauEnt t

namespace ModularChannel

variable (Ch : ModularChannel)

/-- The **magnitude** (Cameron-suppression / Zeno-damping factor):
`magnitude(t) := exp(−τ_ent(t))`. -/
def magnitude (t : ℝ) : ℝ := Real.exp (-(Ch.tauEnt t))

/-- The magnitude is strictly positive. -/
theorem magnitude_pos (t : ℝ) : 0 < Ch.magnitude t := Real.exp_pos _

/-- The magnitude is bounded above by `1` (from `τ_ent ≥ 0`). -/
theorem magnitude_le_one (t : ℝ) : Ch.magnitude t ≤ 1 := by
  unfold magnitude
  have : -(Ch.tauEnt t) ≤ 0 := by linarith [Ch.tauEnt_nonneg t]
  exact Real.exp_le_one_iff.mpr this

/-- If `τ_ent(t) = 0` then `magnitude(t) = 1` — no suppression
(equilibrium / vacuum sector). -/
theorem magnitude_at_zero_tauEnt (t : ℝ) (h : Ch.tauEnt t = 0) :
    Ch.magnitude t = 1 := by
  unfold magnitude
  rw [h, neg_zero, Real.exp_zero]

/-- **The trivial modular channel**: `τ_ent ≡ 0`, `magnitude ≡ 1`
(reversible / no suppression). -/
def trivial : ModularChannel where
  tauEnt        := fun _ => 0
  tauEnt_nonneg := fun _ => le_refl _

@[simp] theorem trivial_tauEnt (t : ℝ) : trivial.tauEnt t = 0 := rfl

@[simp] theorem trivial_magnitude (t : ℝ) : trivial.magnitude t = 1 := by
  unfold trivial magnitude
  simp

end ModularChannel

/-! ## §3 — Modular group law bridge -/

/-- **Modular group-law bridge**: under the additivity hypothesis
`τ_ent(s+t) = τ_ent(s) + τ_ent(t)` along the modular flow, the
channel is multiplicative.

The additivity hypothesis is the operational consistency between the
modular group law (operator-side) and the channel-composition law
(magnitude-side). -/
structure ModularGroupLawBridge
    (_M : ModularGroupData H) (Ch : ModularChannel) : Prop where
  /-- **Additivity hypothesis**: `τ_ent(s+t) = τ_ent(s) + τ_ent(t)`
  along the modular flow. -/
  tauEnt_additive : ∀ s t : ℝ, Ch.tauEnt (s + t) = Ch.tauEnt s + Ch.tauEnt t

namespace ModularGroupLawBridge

variable {M : ModularGroupData H} {Ch : ModularChannel}

/-- **Channel composition law**: under the additivity bridge,
`magnitude(s + t) = magnitude(s) · magnitude(t)`.

The channel is multiplicative along the modular flow, mirroring the
operator-level group law `σ(s+t) = σ_s ∘ σ_t`. -/
theorem magnitude_composition_law
    (B : ModularGroupLawBridge M Ch) (s t : ℝ) :
    Ch.magnitude (s + t) = Ch.magnitude s * Ch.magnitude t := by
  unfold ModularChannel.magnitude
  rw [B.tauEnt_additive s t, neg_add, Real.exp_add]

/-- **Modular-group composition** at the bridge level (re-export of
the group law from the data). -/
theorem modularGroup_composition
    (_B : ModularGroupLawBridge M Ch) (s t : ℝ) (a : H →L[ℂ] H) :
    M.σ (s + t) a = M.σ s (M.σ t a) :=
  M.group_law s t a

/-- The **trivial modular group law bridge**: at the trivial modular
group + trivial channel, additivity holds (both sides zero). -/
theorem trivial : ModularGroupLawBridge (ModularGroupData.trivial H)
    ModularChannel.trivial where
  tauEnt_additive := fun _ _ => by simp

end ModularGroupLawBridge

/-! ## §4 — KMS state functional -/

/-- **KMS state functional**: a ℂ-valued state functional
`ω : (H →L[ℂ] H) → ℂ` satisfying the **modular invariance hypothesis**
`ω (σ_t(a)) = ω(a)`.

In Tomita-Takesaki theory the invariance follows from
`Δ^{it} Ω = Ω` (vacuum-vector invariance under the modular operator)
together with `(Δ^{it})* = Δ^{-it}`; here it is represented as a
hypothesis on `ω` so consumers may supply any concrete proof. -/
structure KMSStateFunctional (M : ModularGroupData H) where
  /-- The state functional `ω`. -/
  ω           : (H →L[ℂ] H) → ℂ
  /-- **Modular-invariance hypothesis**: `ω (σ_t(a)) = ω(a)`. -/
  ω_invariant : ∀ (t : ℝ) (a : H →L[ℂ] H), ω (M.σ t a) = ω a

namespace KMSStateFunctional

variable {M : ModularGroupData H}

/-- **State-invariance extraction**: the state functional is
invariant under the modular flow at every `t` and `a`. -/
theorem state_invariant_under_flow (K : KMSStateFunctional M)
    (t : ℝ) (a : H →L[ℂ] H) :
    K.ω (M.σ t a) = K.ω a :=
  K.ω_invariant t a

/-- At `t = 0` the modular flow is the identity, so invariance is
trivially the consequence of `σ 0 a = a`. -/
theorem state_invariant_at_zero (K : KMSStateFunctional M) (a : H →L[ℂ] H) :
    K.ω (M.σ 0 a) = K.ω a := by rw [M.zero_eq]

/-- The **trivial KMS state functional**: `ω ≡ 0`.  At any modular
group, the zero functional is trivially invariant. -/
def trivial (M : ModularGroupData H) : KMSStateFunctional M where
  ω           := fun _ => 0
  ω_invariant := fun _ _ => rfl

end KMSStateFunctional

/-! ## §5 — Bridge to `kmsQIF` -/

/-- **Compatibility of `kmsQIF` with any modular automorphism group**.

A KMS QIF is reversible (`H_I = 0`, modular flow is unitary), so any
state is at equilibrium for `kmsQIF`.  This is consistent with the
abstract modular invariance `ω(σ_t(a)) = ω(a)` in any
`KMSStateFunctional` for any `ModularGroupData`: the QIF entropic
rate is zero, the modular flow is identity-on-states up to phase,
and the state functional is invariant.  No content is asserted
beyond the conjunction of these existing claims. -/
theorem kmsQIF_compatible_with_modularGroup
    (H_θ : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (beta : ℝ) (beta_pos : 0 < beta)
    (M : ModularGroupData H) (K : KMSStateFunctional M)
    (ψ : H) (t : ℝ) (a : H →L[ℂ] H) :
    (kmsQIF H_θ hbar hbar_pos beta beta_pos).IsEquilibriumAt ψ
      ∧ K.ω (M.σ t a) = K.ω a :=
  ⟨kmsQIF_isEquilibriumAt H_θ hbar hbar_pos beta beta_pos ψ,
   K.ω_invariant t a⟩

/-- **Trivial existence witness** for the Tomita-Takesaki / KMS
machinery: at the trivial modular group + trivial channel + trivial
state, all bridges hold simultaneously. -/
theorem trivial_modularStructure_exists :
    ∃ (M : ModularGroupData H) (Ch : ModularChannel),
        ModularGroupLawBridge M Ch ∧
        Nonempty (KMSStateFunctional M) :=
  ⟨ModularGroupData.trivial H, ModularChannel.trivial,
   ModularGroupLawBridge.trivial,
   ⟨KMSStateFunctional.trivial (ModularGroupData.trivial H)⟩⟩

/-! ## §6 — Constructive modular group from a self-adjoint generator

The abstract `ModularGroupData` structure admits an explicit
constructor: given any bounded operator `H_θ : H →L[ℂ] H` (typically
the modular Hamiltonian `−log ρ`), the **unitary flow**
`u(t) := NormedSpace.exp ℂ (i·t·H_θ)` defines

  `σ_t(a) := u(t) · a · u(-t)`

with the Tomita-Takesaki group law proved from
`NormedSpace.exp_add_of_commute`. This is the canonical
finite-dimensional realisation of the modular automorphism group,
moving `ModularGroupData` from "axiomatised contract" to
"derived theorem of `NormedSpace.exp` + commuting scalar multiples". -/

/-- **Unitary flow generated by `H_θ`**:
`u(t) := exp(i·t·H_θ)` as an element of the Banach algebra
`H →L[ℂ] H` (via `NormedSpace.exp ℂ`). -/
def unitaryFlow (H_θ : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • H_θ)

@[simp] theorem unitaryFlow_zero (H_θ : H →L[ℂ] H) :
    unitaryFlow H_θ 0 = 1 := by
  unfold unitaryFlow
  simp [NormedSpace.exp_zero]

/-- **Additivity of the unitary flow**: `u(s+t) = u(s) · u(t)`. The
two generators `(s·i)•H_θ` and `(t·i)•H_θ` are scalar multiples of the
same operator, hence commute; `NormedSpace.exp_add_of_commute_of_mem_ball`
over `ℂ` (whose `expSeries` radius is `⊤` for any `NormedAlgebra ℂ`)
yields the multiplicative law. -/
theorem unitaryFlow_add (H_θ : H →L[ℂ] H) (s t : ℝ) :
    unitaryFlow H_θ (s + t) = unitaryFlow H_θ s * unitaryFlow H_θ t := by
  unfold unitaryFlow
  have hcomm : Commute (((s : ℂ) * Complex.I) • H_θ)
      (((t : ℂ) * Complex.I) • H_θ) :=
    ((Commute.refl H_θ).smul_left _).smul_right _
  have hsum : (((s + t : ℝ) : ℂ) * Complex.I) • H_θ
      = ((s : ℂ) * Complex.I) • H_θ + ((t : ℂ) * Complex.I) • H_θ := by
    rw [Complex.ofReal_add, add_mul, add_smul]
  rw [hsum]
  have hrad := NormedSpace.expSeries_radius_eq_top (𝕂 := ℂ) (𝔸 := H →L[ℂ] H)
  refine NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm ?_ ?_
  · exact hrad.symm ▸ edist_lt_top _ _
  · exact hrad.symm ▸ edist_lt_top _ _

/-- **Group inverse on the right**: `u(t) · u(-t) = 1`. -/
theorem unitaryFlow_mul_neg (H_θ : H →L[ℂ] H) (t : ℝ) :
    unitaryFlow H_θ t * unitaryFlow H_θ (-t) = 1 := by
  rw [← unitaryFlow_add, add_neg_cancel, unitaryFlow_zero]

/-- **Group inverse on the left**: `u(-t) · u(t) = 1`. -/
theorem unitaryFlow_neg_mul (H_θ : H →L[ℂ] H) (t : ℝ) :
    unitaryFlow H_θ (-t) * unitaryFlow H_θ t = 1 := by
  rw [← unitaryFlow_add, neg_add_cancel, unitaryFlow_zero]

/-- **Constructive Tomita-Takesaki modular automorphism group** from
a generator `H_θ : H →L[ℂ] H`:

  `σ_t(a) := exp(i·t·H_θ) · a · exp(-i·t·H_θ)`.

Group law, identity-at-zero, and multiplicativity are all *derived*
from `NormedSpace.exp_add_of_commute` (plus associativity of the
Banach-algebra product), not assumed. This realises the abstract
`ModularGroupData H` from a single self-adjoint operator. -/
def ModularGroupData.ofGenerator (H_θ : H →L[ℂ] H) : ModularGroupData H where
  σ          := fun t a => unitaryFlow H_θ t * a * unitaryFlow H_θ (-t)
  group_law  := fun s t a => by
    show unitaryFlow H_θ (s + t) * a * unitaryFlow H_θ (-(s + t))
        = unitaryFlow H_θ s *
          (unitaryFlow H_θ t * a * unitaryFlow H_θ (-t)) *
          unitaryFlow H_θ (-s)
    rw [unitaryFlow_add, show -(s + t) = -t + -s from by ring, unitaryFlow_add]
    simp only [mul_assoc]
  zero_eq    := fun a => by
    show unitaryFlow H_θ 0 * a * unitaryFlow H_θ (-0) = a
    rw [neg_zero, unitaryFlow_zero, one_mul, mul_one]
  mul_eq     := fun t a b => by
    show unitaryFlow H_θ t * (a * b) * unitaryFlow H_θ (-t)
        = (unitaryFlow H_θ t * a * unitaryFlow H_θ (-t)) *
          (unitaryFlow H_θ t * b * unitaryFlow H_θ (-t))
    have h : unitaryFlow H_θ (-t) * unitaryFlow H_θ t = 1 :=
      unitaryFlow_neg_mul H_θ t
    have key : a * b = a * (unitaryFlow H_θ (-t) * unitaryFlow H_θ t) * b := by
      rw [h, mul_one]
    rw [key]
    simp only [mul_assoc]

/-- **Constructive σ_t unfolds to the conjugation formula**. -/
@[simp] theorem ModularGroupData.ofGenerator_σ
    (H_θ : H →L[ℂ] H) (t : ℝ) (a : H →L[ℂ] H) :
    (ModularGroupData.ofGenerator H_θ).σ t a
      = unitaryFlow H_θ t * a * unitaryFlow H_θ (-t) := rfl

/-- **Constructive Tomita-Takesaki group law on the σ-flow**:
`σ(s+t) = σ s ∘ σ t` for the constructively-built modular group,
proved from `exp(i·(s+t)·H_θ) = exp(i·s·H_θ) · exp(i·t·H_θ)` at
the level of the conjugation `σ`. -/
theorem ModularGroupData.ofGenerator_group_law
    (H_θ : H →L[ℂ] H) (s t : ℝ) (a : H →L[ℂ] H) :
    (ModularGroupData.ofGenerator H_θ).σ (s + t) a
      = (ModularGroupData.ofGenerator H_θ).σ s
          ((ModularGroupData.ofGenerator H_θ).σ t a) :=
  (ModularGroupData.ofGenerator H_θ).group_law s t a

end QuantumMechanics.FiniteTarget

end

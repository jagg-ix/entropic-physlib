/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame
public import QuantumInfo.States.Pure.Qubit

/-!
# Page–Wootters skeleton and effective clock-frame Hamiltonian

A neutral structure framework for the **Page–Wootters relational-time**
construction (Page & Wootters 1983) together with the effective
non-Hermitian Hamiltonians that arise from changing the clock frame in
that framework (Suleymanov & Cohen 2023, EPJ-ST, Eqs. 42, 49, 53, 56,
63).

The bridge that this module makes precise: an effective Hamiltonian of
the Suleymanov–Cohen shape `H_eff = A⁻¹ · H_raw` whose anti-Hermitian
part is positive assembles a
`QuantumMechanics.FiniteTarget.QuantumInertialFrame`.  The QIF structure
is therefore the destination type for the clock-frame-change
construction reviewed in the paper.

## Contents

### §A — Page–Wootters Hamiltonian constraint

* `HamiltonianConstraint H` — the abstract Wheeler–DeWitt / PaW
  constraint `H_total |Ψ⟩ = 0`.  A physical state is a kernel element
  of `H_total`.
* `HamiltonianConstraint.IsPhysical` predicate plus closure under
  scalar multiplication and addition (the kernel is a `ℂ`-subspace).
* `HamiltonianConstraint.trivial` — the zero constraint, under which
  every state is physical.

### §C — Effective clock-frame Hamiltonian

* `hermitianPart` / `antiHermitianPart` — the standard
  `T = T_R − i·T_I` decomposition of a bounded operator
  (`T_R := (T + T*)/2`, `T_I := i·(T − T*)/2`).
* `hermitianPart_sub_I_smul_antiHermitianPart` — the decomposition
  identity.
* `EffectiveClockHamiltonian H` — the factored structure
  `H_eff := A_inv · H_raw` matching the shape of Suleymanov & Cohen
  2023 Eqs. 42, 49, 53, 56, 63 where `A := I + g(T)·P` or
  `A := I + f(T_C,…)`.
* `QuantumInertialFrame.ofEffectiveClockHamiltonian` — the bridge
  theorem: an effective Hamiltonian whose anti-Hermitian part is
  positive assembles a Quantum Inertial Frame, with `H_R` and `H_I`
  given by the decomposition of `H_eff`.

## Scope

This module supplies the **structure types and bridge** only.  Two
neighbouring pieces are not built here because adequate physlib
structures already exist:

* **Clock-rate variable** (`dT_B/dt_A = I + g(t_A)·P_E` in the paper,
  Eq. 40).  Existing physlib structures:
  `Physlib.QuantumMechanics.Clock.Phase.PhaseClock` (`ω₀ > 0`
  accumulator), `Physlib.FluidDynamics.CourantNumber` (`λ(t) := dτ/dt`
  positive monotone reparameterisation), and
  `Physlib.SpaceAndTime.SpaceTime.Lapse` (ADM lapse `N(x) > 0`).

* **Calibration witness** between an internal clock parameter and
  physical proper time.  existing physlib structure:
  `Physlib.QuantumMechanics.Clock.EntropicAgreement
  .EntropicOscillatorClockAgreement` and its lapse-version sibling.

What this module does *not* attempt:

* The full Page–Wootters derivation
  `Ĥ_T|Ψ⟩ = 0  + conditioning on |t⟩  ⇒  i ∂_t |ψ⟩ = H_R |ψ⟩`.  That
  requires a tensor split `H = H_C ⊗ H_R` and a chosen family of clock
  states, which are downstream consumer constructions.
* A proof that `[A, H] ≠ 0` implies `H_eff` is non-Hermitian.  In the
  paper this is observed concretely from the explicit Eqs. 42, 49, 53;
  here the consumer supplies whatever decomposition they have proved
  and the bridge accepts it.

## References

- Page & Wootters 1983, *Evolution without evolution: Dynamics
  described by stationary observables*, Phys. Rev. D 27, 2885,
  doi:10.1103/PhysRevD.27.2885.
- DeWitt 1967, *Quantum theory of gravity. I.*, Phys. Rev. 160, 1113,
  doi:10.1103/PhysRev.160.1113.
- Suleymanov & Cohen 2023, *Quantum frames of reference and the
  relational flow of time*, Eur. Phys. J. Spec. Top.,
  doi:10.1140/epjs/s11734-023-00973-8 — Eqs. 42, 49, 53, 56, 63
  exhibit the effective non-Hermitian Hamiltonians that this module
  abstracts.
- Höhn, Smith & Lock 2021, *Trinity of relational quantum dynamics*,
  Phys. Rev. D 104, 066001,
  doi:10.1103/PhysRevD.104.066001.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.RelationalTime

open QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §A — Page–Wootters Hamiltonian constraint -/

/-- **Page–Wootters Hamiltonian constraint** on a Hilbert space `H`:
a total Hamiltonian `H_total` whose kernel is the physical subspace.
The Wheeler–DeWitt equation is `H_total |Ψ⟩ = 0`. -/
structure HamiltonianConstraint (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The total Hamiltonian. -/
  H_total : H →L[ℂ] H

namespace HamiltonianConstraint

variable (C : HamiltonianConstraint H)

/-- A state `Ψ ∈ H` is **physical** iff it satisfies the constraint
`H_total Ψ = 0`. -/
def IsPhysical (Ψ : H) : Prop := C.H_total Ψ = 0

/-- The zero vector is physical. -/
@[simp] theorem isPhysical_zero : C.IsPhysical 0 := by
  unfold IsPhysical
  exact map_zero _

/-- Physical states are closed under scalar multiplication. -/
theorem isPhysical_smul {Ψ : H} (h : C.IsPhysical Ψ) (c : ℂ) :
    C.IsPhysical (c • Ψ) := by
  unfold IsPhysical at h ⊢
  rw [map_smul, h, smul_zero]

/-- Physical states are closed under addition.

Does not prove: PaW clock is entropic; relational time equals
entropic time; conditioned `τ_ent` is monotone or discrete.
The same conclusion holds for `H_total := 0` (every state physical),
i.e. for an ideal unitary clock — so the closure says nothing about
irreversibility.
-/
theorem isPhysical_add {Ψ Φ : H} (hΨ : C.IsPhysical Ψ) (hΦ : C.IsPhysical Φ) :
    C.IsPhysical (Ψ + Φ) := by
  unfold IsPhysical at hΨ hΦ ⊢
  rw [map_add, hΨ, hΦ, add_zero]

/-- **Trivial constraint**: `H_total := 0`.  Every state is physical. -/
def trivial (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    HamiltonianConstraint H where
  H_total := 0

@[simp] theorem trivial_isPhysical (Ψ : H) :
    (trivial H).IsPhysical Ψ := by
  unfold IsPhysical trivial
  rfl

end HamiltonianConstraint

/-! ### Physical kernel inner product -/

/-- The physical inner product is the ambient Hilbert inner product restricted
to the Hamiltonian-constraint kernel. -/
noncomputable def physicalKernelInnerProduct
    (_C : HamiltonianConstraint H) (Ψ Φ : H) : ℂ :=
  inner ℂ Ψ Φ

/-- The Page-Wootters physical subspace is a linear kernel with the
restricted Hilbert inner product. -/
theorem hilbertSpace_innerProduct_obligation_discharged
    (C : HamiltonianConstraint H) :
    C.IsPhysical 0
      ∧ (∀ {Ψ : H}, C.IsPhysical Ψ → ∀ c : ℂ, C.IsPhysical (c • Ψ))
      ∧ (∀ {Ψ Φ : H}, C.IsPhysical Ψ → C.IsPhysical Φ → C.IsPhysical (Ψ + Φ))
      ∧ (∀ Ψ Φ : H, C.IsPhysical Ψ → C.IsPhysical Φ →
          physicalKernelInnerProduct C Ψ Φ = inner ℂ Ψ Φ) :=
  ⟨HamiltonianConstraint.isPhysical_zero C,
    fun {_} h c => HamiltonianConstraint.isPhysical_smul C h c,
    fun {_ _} hΨ hΦ => HamiltonianConstraint.isPhysical_add C hΨ hΦ,
    fun _ _ _ _ => rfl⟩

/-! ## §C — Effective clock-frame Hamiltonian -/

/-- **Hermitian part** of a bounded operator: `T_R := (T + T*)/2`. -/
def hermitianPart (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (1/2 : ℂ) • (T + star T)

/-- **Anti-Hermitian-as-Hermitian part**: `T_I := i·(T − T*)/2`, so
that `T = T_R − i·T_I`. -/
def antiHermitianPart (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (Complex.I / 2) • (T - star T)

/-- The **Hermitian / anti-Hermitian decomposition**:
`T = T_R − i·T_I` for any bounded operator. -/
theorem hermitianPart_sub_I_smul_antiHermitianPart (T : H →L[ℂ] H) :
    hermitianPart T - Complex.I • antiHermitianPart T = T := by
  unfold hermitianPart antiHermitianPart
  rw [smul_smul]
  have h_I : Complex.I * (Complex.I / 2) = -(1/2 : ℂ) := by
    rw [mul_div_assoc', Complex.I_mul_I]
    ring
  rw [h_I, neg_smul, sub_neg_eq_add, ← smul_add]
  have : T + star T + (T - star T) = (2 : ℂ) • T := by
    rw [show (T + star T) + (T - star T) = (T + T) + (star T - star T) by abel]
    rw [sub_self, add_zero]
    rw [two_smul]
  rw [this, smul_smul]
  norm_num

/-- **Effective clock-frame Hamiltonian** in the factored shape
`H_eff := A_inv · H_raw` of Suleymanov & Cohen 2023 Eqs. 42, 49, 53,
56, 63 (where the paper takes `A := I + g(T)·P_E` and similar).  The
field `A_inv` represents the pre-computed inverse `[I + g(T)·P]⁻¹`. -/
structure EffectiveClockHamiltonian (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The pre-computed inverse `A_inv := [I + g(T)·P]⁻¹`. -/
  A_inv : H →L[ℂ] H
  /-- The raw inside-the-brackets Hamiltonian `H_raw`. -/
  H_raw : H →L[ℂ] H

namespace EffectiveClockHamiltonian

variable (E : EffectiveClockHamiltonian H)

/-- The **effective Hamiltonian** `H_eff := A_inv · H_raw`. -/
def H_eff : H →L[ℂ] H := E.A_inv ∘L E.H_raw

end EffectiveClockHamiltonian

/-! ## §C-bridge — Effective Hamiltonian to Quantum Inertial Frame -/

/-- **Bridge: `EffectiveClockHamiltonian` → `QuantumInertialFrame`**.

When the anti-Hermitian part of `E.H_eff` has a positivity
witness, the effective Hamiltonian assembles a `QuantumInertialFrame`
with `H_R := hermitianPart E.H_eff` and `H_I := antiHermitianPart E.H_eff`.
By `hermitianPart_sub_I_smul_antiHermitianPart`, the resulting QIF's
complex Hamiltonian `H_R − i·H_I` equals `E.H_eff`.

The positivity hypothesis on the anti-Hermitian part is precisely the
condition that the paper's effective Hamiltonian dissipates rather
than amplifies — equivalent in finite dimensions to contractivity of
the non-Hermitian Schrödinger evolution generated by `E.H_eff`. -/
def QuantumInertialFrame.ofEffectiveClockHamiltonian
    (E : EffectiveClockHamiltonian H)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (h_pos : (antiHermitianPart E.H_eff).IsPositive) :
    QuantumInertialFrame H where
  H_R            := hermitianPart E.H_eff
  H_I            := antiHermitianPart E.H_eff
  H_I_isPositive := h_pos
  hbar           := hbar
  hbar_pos       := hbar_pos

/-- The bridged QIF's complex Hamiltonian equals the input effective
Hamiltonian. -/
theorem QuantumInertialFrame.ofEffectiveClockHamiltonian_complexHamiltonian
    (E : EffectiveClockHamiltonian H)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (h_pos : (antiHermitianPart E.H_eff).IsPositive) :
    (QuantumInertialFrame.ofEffectiveClockHamiltonian
        E hbar hbar_pos h_pos).complexHamiltonian = E.H_eff := by
  unfold QuantumInertialFrame.complexHamiltonian
    QuantumInertialFrame.ofEffectiveClockHamiltonian
  exact hermitianPart_sub_I_smul_antiHermitianPart E.H_eff

/-! ## §D — Dissipative conditional state (Page–Wootters appendix A.2–A.4)

At clock reading `τ` the conditional system state `ρ_S(τ)` of the dissipative
Page–Wootters extension is generated by a Hermitian commutator term plus a GKSL
dissipator,
`dρ_S/dτ = −(i/ℏ)[H_S, ρ_S] + 𝓛_S(ρ_S)`
(Page & Wootters 1983 for the unitary part; the dissipative extension follows
the appendix's Eqs. A.2–A.4: `H_S` generates the real action `S_R`, the
Lindbladian `𝓛_S` encodes the imaginary action `S_I`).

This structure supplies the **generator** as a superoperator; deriving it from the
tensor constraint `H_C ⊗ H_S` and the partial trace over the clock — the
appendix's proof sketch — is deferred, consistent with the scope note above (the
clock basis `{|τ⟩}` and translation property are downstream constructions).

`gksLGen_eq_vonNeumannGen_of_lindblad_zero` formalises the appendix's structural
claim that the unitary von Neumann equation is exactly the `𝓛_S → 0` limit of
the dissipative conditional dynamics. -/

/-- **Dissipative Page–Wootters conditional clock.** A system Hamiltonian `H_S`
(Hermitian generator) together with a GKSL superoperator `lindblad := 𝓛_S`
acting on the system operator algebra. -/
structure DissipativeConditionalClock (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ
  /-- The system Hamiltonian `H_S` (Hermitian generator → `S_R`). -/
  H_S : H →L[ℂ] H
  /-- The GKSL dissipator `𝓛_S` as a superoperator on the operator algebra
  (→ `S_I`). -/
  lindblad : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)

namespace DissipativeConditionalClock

variable (P : DissipativeConditionalClock H)

/-- The **von Neumann generator** `−(i/ℏ)[H_S, ρ]` of the conditional state — the
Hermitian part of the conditional dynamics (App. A.2, Eq. pw_vn). -/
def vonNeumannGen (ρ : H →L[ℂ] H) : H →L[ℂ] H :=
  (-(Complex.I / (P.ℏ : ℂ))) • (P.H_S ∘L ρ - ρ ∘L P.H_S)

/-- The full **GKSL conditional generator**
`−(i/ℏ)[H_S, ρ] + 𝓛_S(ρ)` (App. A.3, Eq. pw_dissipative). -/
def gksLGen (ρ : H →L[ℂ] H) : H →L[ℂ] H :=
  P.vonNeumannGen ρ + P.lindblad ρ

/-- **A.4 reduction**: with no dissipation (`𝓛_S = 0`) the GKSL conditional
generator is the von Neumann generator — unitary Page–Wootters evolution is the
`𝓛_S → 0` limit of the dissipative dynamics. -/
theorem gksLGen_eq_vonNeumannGen_of_lindblad_zero (ρ : H →L[ℂ] H)
    (h : P.lindblad = 0) : P.gksLGen ρ = P.vonNeumannGen ρ := by
  simp only [gksLGen, h, LinearMap.zero_apply, add_zero]

/-- A vanishing system Hamiltonian freezes the von Neumann generator. -/
theorem vonNeumannGen_eq_zero_of_H_S_zero (ρ : H →L[ℂ] H) (h : P.H_S = 0) :
    P.vonNeumannGen ρ = 0 := by
  simp only [vonNeumannGen, h, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero, sub_zero, smul_zero]

/-- With no Hamiltonian and no dissipation the conditional state is frozen: the
generator vanishes identically. -/
theorem gksLGen_eq_zero_of_unitary_frozen (ρ : H →L[ℂ] H)
    (hH : P.H_S = 0) (hL : P.lindblad = 0) : P.gksLGen ρ = 0 := by
  rw [P.gksLGen_eq_vonNeumannGen_of_lindblad_zero ρ hL,
    P.vonNeumannGen_eq_zero_of_H_S_zero ρ hH]

end DissipativeConditionalClock

/-- **Non-vacuity witness**: the dissipationless, free clock on
`EuclideanSpace ℂ (Fin 1)` (`H_S = 0`, `𝓛_S = 0`). -/
def DissipativeConditionalClock.trivial (ℏ : ℝ) (hℏ : 0 < ℏ) :
    DissipativeConditionalClock (EuclideanSpace ℂ (Fin 1)) where
  ℏ := ℏ
  ℏ_pos := hℏ
  H_S := 0
  lindblad := 0

/-! ## §E — GKSL dissipation rate and entropic-clock monotonicity

For explicit Lindblad jump operators `L : ι → (H →L[ℂ] H)` over a finite index
set, the conditional state of a dissipative Page–Wootters clock evolves with the
**GKSL dissipation functional**

  `λ(ρ) := (1/ℏ) · ∑ⱼ Tr(Lⱼᴴ Lⱼ ρ)`,    `τ_ent = ∫ λ dτ'`,

the accumulated entropic time of the worldline.  Specialised to a pure state
`ρ = |ψ⟩⟨ψ|`, each summand is the diagonal matrix element
`Tr(Lⱼᴴ Lⱼ |ψ⟩⟨ψ|) = ⟨ψ, Lⱼᴴ Lⱼ ψ⟩ = ‖Lⱼ ψ‖²`, so the rate is the manifestly
non-negative `(1/ℏ) · ∑ⱼ ‖Lⱼ ψ‖²`.

`dissipationRate_nonneg` is the GKSL counterpart of
`QuantumInertialFrame.entropicRate_nonneg`: a clock whose conditional state
evolves by a genuine GKSL generator has a non-negative entropic rate, so
`τ_ent` is non-decreasing along the worldline — the discrete/pointwise form of
Spohn's `dS/dτ ≥ 0`.  `dissipationRate_eq_zero_iff` is the dissipationless
(equilibrium) condition: the rate vanishes exactly when every jump annihilates
`ψ`, paralleling `QuantumInertialFrame.IsEquilibriumAt`.

This does **not** establish strict positivity, that any physical clock has
non-vanishing jumps, or full Spohn monotonicity of the von Neumann entropy —
those require the CPTP-semigroup hypotheses left to consumers. -/

/-- The **pure-state GKSL dissipation rate** at `ψ` for jump operators
`L : ι → (H →L[ℂ] H)` and Planck constant `ℏ`: `(1/ℏ) · ∑ⱼ ‖Lⱼ ψ‖²`.
The pure-state (`ρ = |ψ⟩⟨ψ|`) specialisation of `(1/ℏ) ∑ⱼ Tr(Lⱼᴴ Lⱼ ρ)`. -/
def dissipationRate {ι : Type*} [Fintype ι] (ℏ : ℝ)
    (L : ι → (H →L[ℂ] H)) (ψ : H) : ℝ :=
  (∑ j, ‖L j ψ‖ ^ 2) / ℏ

omit [FiniteDimensional ℂ H] in
/-- **Each summand is the positive operator `Lᴴ L` read on `ψ`**:
`‖L ψ‖² = (Lᴴ ∘L L).reApplyInnerSelf ψ = ⟨ψ, Lᴴ L ψ⟩`, the diagonal matrix
element that appears as `Tr(Lᴴ L |ψ⟩⟨ψ|)`. -/
theorem norm_sq_eq_reApplyInnerSelf (L : H →L[ℂ] H) (ψ : H) :
    ‖L ψ‖ ^ 2 = ((ContinuousLinearMap.adjoint L) ∘L L).reApplyInnerSelf ψ := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  exact ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left L ψ

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
/-- **Non-negativity of the GKSL dissipation rate**: a sum of squared norms over
`ℏ > 0`.  GKSL analogue of `QuantumInertialFrame.entropicRate_nonneg`. -/
theorem dissipationRate_nonneg {ι : Type*} [Fintype ι] {ℏ : ℝ} (hℏ : 0 < ℏ)
    (L : ι → (H →L[ℂ] H)) (ψ : H) : 0 ≤ dissipationRate ℏ L ψ :=
  div_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2) hℏ.le

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
/-- **Equilibrium condition**: the dissipation rate vanishes exactly when every
jump operator annihilates `ψ`. -/
theorem dissipationRate_eq_zero_iff {ι : Type*} [Fintype ι] {ℏ : ℝ} (hℏ : 0 < ℏ)
    (L : ι → (H →L[ℂ] H)) (ψ : H) :
    dissipationRate ℏ L ψ = 0 ↔ ∀ j, L j ψ = 0 := by
  rw [dissipationRate, div_eq_zero_iff, or_iff_left hℏ.ne',
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2]
  constructor
  · intro h j
    have hj : ‖L j ψ‖ ^ 2 = 0 := h j (Finset.mem_univ j)
    rw [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hj
    exact hj
  · intro h i _
    rw [h i, norm_zero]; norm_num

/-- The **conditional entropic rate** of a dissipative clock `P` for jump
operators `L`, evaluated at pure state `ψ`: `dissipationRate P.ℏ L ψ`. -/
def DissipativeConditionalClock.conditionalEntropicRate
    (P : DissipativeConditionalClock H) {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℂ] H)) (ψ : H) : ℝ :=
  dissipationRate P.ℏ L ψ

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
/-- The conditional entropic rate of a dissipative clock is non-negative. -/
theorem DissipativeConditionalClock.conditionalEntropicRate_nonneg
    (P : DissipativeConditionalClock H) {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℂ] H)) (ψ : H) : 0 ≤ P.conditionalEntropicRate L ψ :=
  dissipationRate_nonneg P.ℏ_pos L ψ

end QuantumMechanics.RelationalTime

namespace Physlib.Thermodynamics.Landauer

/-! ## L3: Page-Wootters quantum-clock subsystem (full bipartite Hilbert)

Full bipartite Hilbert-subsystem instantiation of the Page-Wootters
relational time construction (Page & Wootters 1983; Weberszpil &
Sotolongo-Costa 2026 §E, Eqs. 12-14), using physlib's
`Ket (d_sys × d_clock)` + `MState.traceLeft/Right` + `Sᵥₙ`
bipartite infrastructure.

This complements the magnitude-level Page-Wootters underlying structure
by adding the explicit bipartite state vector `Ψ ∈ ℋ_sys ⊗ ℋ_clock`
together with system/clock marginal extraction and entanglement-entropy
theorems — the "quantum-clock subsystem machinery" previously deferred
in this file.

The WDW constraint is kept in eigenvalue form (matching the
pattern); the operator-level form `(H_sys ⊗ id + id ⊗ H_clock) · Ψ = 0`
requires tensor-product HermitianMat machinery and is left to the
operator-side modules.
-/

/-- **Page-Wootters bipartite structure** — full bipartite Hilbert-subsystem
instantiation of the Page-Wootters construction.

Records:
* `d_sys`, `d_clock`: finite types for system and clock Hilbert dims;
* `ℏ`, `E_sys`, `E_clock`: real eigenvalue data;
* `Ψ : Ket (d_sys × d_clock)`: the explicit bipartite total state
  (Weberszpil-Sotolongo-Costa Eq. 12);
* `t`, `tauPW`, `phaseS`: clock reading, PW conditional time,
  system phase;
* WDW eigenvalue constraint (Eq. 14), PW time identification (Eq. 13),
  Schrödinger phase (PW4-eig). -/
structure PageWoottersBipartite (d_sys d_clock : Type)
    [Fintype d_sys] [DecidableEq d_sys]
    [Fintype d_clock] [DecidableEq d_clock] where
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ
  /-- System Hamiltonian eigenvalue. -/
  E_sys : ℝ
  /-- Clock Hamiltonian eigenvalue. -/
  E_clock : ℝ
  /-- **Total bipartite state** `|Ψ⟩ ∈ ℋ_sys ⊗ ℋ_clock`
  (Weberszpil-Sotolongo-Costa 2026 Eq. 12). -/
  Ψ : Ket (d_sys × d_clock)
  /-- Clock reading parameter. -/
  t : ℝ
  /-- Page-Wootters conditional time. -/
  tauPW : ℝ
  /-- System phase. -/
  phaseS : ℝ
  /-- **WDW eigenvalue constraint** (Weberszpil-Sotolongo-Costa Eq. 14,
  eigenvalue form): `E_sys + E_clock = 0`.  The eigenvalue form of the
  operator-level constraint `(Ĥ_sys + Ĥ_clock)|Ψ⟩ = 0`. -/
  WDW_constraint : E_sys + E_clock = 0
  /-- **Page-Wootters time identification** (Weberszpil-Sotolongo-Costa
  Eq. 13): conditional time equals the clock reading. -/
  tauPW_eq : tauPW = t
  /-- **Schrödinger phase identification** (PW4-eig):
  `phaseS = -E_sys · t / ℏ`. -/
  phaseS_eq : phaseS = -(E_sys * t) / ℏ

namespace PageWoottersBipartite

variable {d_sys d_clock : Type}
  [Fintype d_sys] [DecidableEq d_sys]
  [Fintype d_clock] [DecidableEq d_clock]
variable (M : PageWoottersBipartite d_sys d_clock)

/-! ### Magnitude-level theorems (mirror `PageWoottersCarrier`) -/

/-- **(Eq. 13)** PW conditional time equals the clock reading. -/
theorem tauPW_eq_t : M.tauPW = M.t := M.tauPW_eq

/-- **(Eq. 14 rearranged)** Clock energy equals negative system energy. -/
theorem E_clock_eq_neg_E_sys : M.E_clock = -M.E_sys := by
  have h := M.WDW_constraint; linarith

/-- **(PW4-eig, alternate form)** `phaseS = E_clock · t / ℏ`. -/
theorem phaseS_eq_clock_form : M.phaseS = M.E_clock * M.t / M.ℏ := by
  rw [M.phaseS_eq, M.E_clock_eq_neg_E_sys]; ring

/-- **(PW4-eig, initial condition)** `phaseS = 0` at clock origin. -/
theorem phaseS_at_zero (h : M.t = 0) : M.phaseS = 0 := by
  rw [M.phaseS_eq, h]; ring

/-! ### Bipartite-extraction theorems (new in L3) -/

/-- **System marginal** = right partial trace of `MState.pure Ψ`.

Mirrors paper Eq. 13 at the operator level: `ρ_sys = Tr_clock |Ψ⟩⟨Ψ|`.
The conditional state of the system, marginalising over the clock. -/
noncomputable def sysMarginal : MState d_sys := (MState.pure M.Ψ).traceRight

/-- **Clock marginal** = left partial trace of `MState.pure Ψ`. -/
noncomputable def clockMarginal : MState d_clock := (MState.pure M.Ψ).traceLeft

/-- **Entanglement-entropy symmetry** — for the pure bipartite total
state, the system and clock marginals have *equal* von Neumann
entropies.  Direct application of `Sᵥₙ_of_partial_eq`.

This is the symmetric entanglement-entropy content of the Page-Wootters
construction: system and clock are equally informative about each other. -/
theorem marginal_entropies_equal :
    Sᵥₙ M.clockMarginal = Sᵥₙ M.sysMarginal := by
  unfold sysMarginal clockMarginal
  exact Sᵥₙ_of_partial_eq M.Ψ

/-- **Non-negativity of marginal entropy** — direct from `Sᵥₙ_nonneg`. -/
theorem sysMarginal_entropy_nonneg : 0 ≤ Sᵥₙ M.sysMarginal :=
  Sᵥₙ_nonneg _

/-- **Non-negativity of clock marginal entropy**. -/
theorem clockMarginal_entropy_nonneg : 0 ≤ Sᵥₙ M.clockMarginal :=
  Sᵥₙ_nonneg _

/-- **Maximum-entropy bound** — system marginal entropy ≤ log(dim sys).
Direct from `Sᵥₙ_le_log_d`. -/
theorem sysMarginal_entropy_le_log_dim_sys :
    Sᵥₙ M.sysMarginal ≤ Real.log (Fintype.card d_sys) :=
  Sᵥₙ_le_log_d _

/-- **Product-state corollary** — if the total `Ψ` is a product state,
the system marginal is pure with zero von Neumann entropy. The clock
"knows nothing" about the system in this case — no entanglement. -/
theorem sysMarginal_entropy_zero_of_Ψ_isProd
    (h : M.Ψ.IsProd) :
    Sᵥₙ M.sysMarginal = 0 := by
  obtain ⟨ξ, φ, hΨ⟩ := h
  unfold sysMarginal
  rw [hΨ, MState.pure_prod_pure, MState.traceRight_prod_eq]
  exact Sᵥₙ_of_pure_zero ξ

end PageWoottersBipartite

/-- **Trivial existence** of a `PageWoottersBipartite` structure on
1-dim system + 1-dim clock — `Ψ = |0⟩ ⊗ |0⟩` (the unique pure state). -/
theorem PageWoottersBipartite.exists_trivial :
    ∃ _ : PageWoottersBipartite (Fin 1) (Fin 1), True := by
  refine ⟨{
    ℏ := 1
    ℏ_pos := one_pos
    E_sys := 0
    E_clock := 0
    Ψ := Ket.basis (0, 0)
    t := 0
    tauPW := 0
    phaseS := 0
    WDW_constraint := by ring
    tauPW_eq := by ring
    phaseS_eq := by ring }, trivial⟩

end Physlib.Thermodynamics.Landauer

end

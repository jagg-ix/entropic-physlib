/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.NagaoNielsenSchrodinger

/-!
# Quantum Inertial Frames and KMS detailed balance

This module formalises the **Quantum Inertial Frame (QIF)** distinction
introduced in Garcia 2026 APS PRL submission v3 §"Equilibrium vs
Non-Equilibrium Quantum Reference Frames".  The term *inertial* is
used in place of the paper's *reference* throughout this module: an
inertial frame is one in which the reduced quantum dynamics is
**time-homogeneous** (an effective CPTP semigroup with stationary
generator), paralleling the classical notion that an inertial frame
is one in which Newton's first law holds without fictitious forces.
Non-inertial QIFs encode dissipative "fictitious openness" in the same
sense that non-inertial classical frames encode centrifugal/Coriolis
terms.

## Two regimes

* **Equilibrium QIF at `ψ`**: the local entropic rate
  `λ(ψ) := H_I.reApplyInnerSelf ψ / ℏ` vanishes; equivalently,
  `Re ⟨ψ, H_I ψ⟩ = 0`.  By the positive-operator pointwise-kernel
  theorem
  (`ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero`),
  this forces `H_I ψ = 0` at the operator level — so the full complex
  Hamiltonian reduces to its Hermitian part: `H_C ψ = H_R ψ`.  If `ψ`
  is also an `H_R`-eigenvector with eigenvalue `E`, then `ψ` satisfies
  the **time-independent Schrödinger equation** for the full complex
  Hamiltonian: `H_C ψ = E·ψ`.

* **Non-equilibrium QIF at `ψ`**: `λ(ψ) > 0`; dissipation is active
  and the entropic time `τ_ent` accumulates along the worldline
  with `ψ`.

## KMS detailed balance (operational form)

The detailed-balance form of the Kubo-Martin-Schwinger condition is
the Fourier-transformed two-point correlator identity

  `W^+(E) = exp(β·E) · W^-(E)`

at inverse temperature `β := 1/(k_B T)`.  This is the operational,
real-valued counterpart of the imaginary-time periodicity
`G^+(τ − iβ) = G^-(τ)` (Haag-Hugenholtz-Winnink 1967;
Bisognano-Wichmann 1975) — equivalent under analyticity of the
correlator in the strip `0 ≤ Im(τ) ≤ β`.

The **thermal rate**

  `λ_KMS := k_B · T / ℏ = 1 / (β · ℏ)`

is the universal entropic rate of a stationary thermal frame in the
Connes-Rovelli 1994 *thermal time hypothesis*: at a KMS-stationary
state at temperature `T`, the QIF's entropic rate equals `λ_KMS`.

## Equivalence chain in this module

Combining §§1-3 below, this module realises in Lean the QIF
equivalence chain from the paper (Eq. 32 of
`paper5_prl_qrf/prl_entropic_qrf_body.tex`):

  `λ(ψ) = 0 ⟺ Re⟨ψ, H_I ψ⟩ = 0 ⟹ H_I ψ = 0 ⟹ H_C ψ = H_R ψ ⟹ TISE`

with the new theorem `QIF.tise_at_equilibrium` closing the chain.
The Cameron-Martin path-integral weight `W = exp(−τ_ent)` (formalised
in `Physlib.FluidDynamics.NavierStokes.NoetherInvariant.cameronMartinWeight_eq_zenoSuppression`)
then satisfies `W = 1` exactly when `λ = 0`, completing the
Cameron ↔ Zeno ↔ equilibrium-QIF triple identification.

## References

- Haag, Hugenholtz & Winnink 1967, *On the equilibrium states in
  quantum statistical mechanics*, Commun. Math. Phys. 5, 215,
  doi:10.1007/BF01646342 — KMS condition foundational.
- Bisognano & Wichmann 1975, *On the duality condition for a
  Hermitian scalar field*, J. Math. Phys. 16, 985,
  doi:10.1063/1.522605 — modular flow / wedge-algebra KMS.
- Connes & Rovelli 1994, *Von Neumann algebra automorphisms and
  time–thermodynamics relation in generally covariant quantum
  theories*, Class. Quant. Grav. 11, 2899,
  doi:10.1088/0264-9381/11/12/007 — thermal time hypothesis.
- Giacomini, Castro-Ruiz & Brukner 2019, *Quantum mechanics and the
  covariance of physical laws in quantum reference frames*,
  Nat. Commun. 10, 494, doi:10.1038/s41467-018-08155-0 — operational
  QRF framework that the QIF structure refines.
- Suleymanov & Cohen 2023, *Quantum frames of reference and the
  relational flow of time*, Eur. Phys. J. Spec. Top.,
  doi:10.1140/epjs/s11734-023-00973-8 — Page–Wootters review that
  exhibits effective non-Hermitian Hamiltonians of the form
  `H_eff = [I + g(T)P]⁻¹·H` (their Eqs. 42, 49, 53, 56, 63) under
  clock-frame change, accelerating clocks, and gravitationally
  interacting clocks. The QIF structure here is a destination type
  for such effective Hamiltonians when their anti-Hermitian sector
  satisfies `H_I.IsPositive`; see
  `Physlib.QuantumMechanics.RelationalTime.PageWootters` for the
  Page–Wootters skeleton and the effective-Hamiltonian bridge.
- Rovelli 1991, *Time in quantum gravity: An hypothesis*,
  Phys. Rev. D 43, 442, doi:10.1103/PhysRevD.43.442 — partial
  observables / frame-clocking.
- Kubo 1957, *Statistical-mechanical theory of irreversible processes*,
  J. Phys. Soc. Japan 12, 570, doi:10.1143/JPSJ.12.570.
- Martin & Schwinger 1959, *Theory of many-particle systems*,
  Phys. Rev. 115, 1342, doi:10.1103/PhysRev.115.1342.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open QuantumInfo.Finite

namespace QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — Quantum Inertial Frame structure -/

/-- A **Quantum Inertial Frame (QIF)** on a finite-dimensional complex
Hilbert space `H`.

Bundles:

* `H_R : H →L[ℂ] H` — the reversible (Hermitian) generator,
* `H_I : H →L[ℂ] H` — the irreversible (positive) generator with
  the `IsPositive` witness,
* `ℏ > 0` — Planck constant.

The complex Hamiltonian `H_C := H_R − i·H_I` is exposed via
`complexHamiltonian` below; positivity of `H_I` is the operational
condition for contractivity (norm non-increase) of the non-Hermitian
Schrödinger evolution.

We deliberately do **not** require `H_R` self-adjointness or any
specific commutation between `H_R` and `H_I` here — consumers add
those as needed (e.g. via `ContinuousLinearMap.IsSelfAdjoint H_R`). -/
structure QuantumInertialFrame
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] where
  H_R            : H →L[ℂ] H
  H_I            : H →L[ℂ] H
  H_I_isPositive : H_I.IsPositive
  hbar           : ℝ
  hbar_pos       : 0 < hbar

namespace QuantumInertialFrame

variable (Q : QuantumInertialFrame H)

/-- The QIF's **complex Hamiltonian** `H_C = H_R − i·H_I`.
Defined inline (rather than via `QuantumMechanics.FiniteTarget.complexHamiltonian`)
to avoid a namespace ambiguity now that both the wrapper and this QIF
projector live under the `QuantumMechanics.FiniteTarget` namespace. -/
def complexHamiltonian : H →L[ℂ] H :=
  Q.H_R - Complex.I • Q.H_I

/-- The **local entropic rate** at state `ψ`:
`λ(ψ) := H_I.reApplyInnerSelf ψ / ℏ = Re ⟨H_I ψ, ψ⟩ / ℏ`.

Matches Garcia 2026 APS PRL Eq. (lambda) `λ = ⟨H_I⟩/ℏ`. -/
def entropicRate (ψ : H) : ℝ :=
  Q.H_I.reApplyInnerSelf ψ / Q.hbar

/-- **Non-negativity of the entropic rate** — positivity of `H_I` plus
`ℏ > 0`. -/
theorem entropicRate_nonneg (ψ : H) : 0 ≤ Q.entropicRate ψ := by
  unfold entropicRate
  exact div_nonneg (Q.H_I_isPositive.2 ψ) (le_of_lt Q.hbar_pos)

/-! ## §2 — Equilibrium QIF at a state -/

/-- **Equilibrium QIF at state `ψ`**: the local entropic rate vanishes.

Equivalent (by `entropicRate_zero_iff_reApplyInnerSelf_zero` below)
to the operator condition `Re ⟨ψ, H_I ψ⟩ = 0`, which the
positive-operator pointwise-kernel theorem strengthens to
`H_I ψ = 0`. -/
def IsEquilibriumAt (Q : QuantumInertialFrame H) (ψ : H) : Prop :=
  Q.entropicRate ψ = 0

/-- **Entropic-rate-zero is equivalent to `reApplyInnerSelf` zero**:
since `ℏ > 0`, the rate `λ = Re⟨ψ,H_I ψ⟩/ℏ = 0` iff the numerator
vanishes. -/
theorem entropicRate_zero_iff_reApplyInnerSelf_zero (ψ : H) :
    Q.entropicRate ψ = 0 ↔ Q.H_I.reApplyInnerSelf ψ = 0 := by
  unfold entropicRate
  rw [div_eq_zero_iff]
  refine ⟨?_, fun h => Or.inl h⟩
  rintro (h | h)
  · exact h
  · exact absurd h (ne_of_gt Q.hbar_pos)

/-- **Dissipation operator vanishes pointwise at an equilibrium-QIF
state**: at an equilibrium QIF state, `Q.H_I ψ = 0`.  Specialises
`ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero`
(physlib NagaoNielsen §5b') to the equilibrium-QIF hypothesis. -/
theorem H_I_apply_eq_zero_of_isEquilibrium
    {ψ : H} (h_eq : Q.IsEquilibriumAt ψ) : Q.H_I ψ = 0 := by
  have h_re : Q.H_I.reApplyInnerSelf ψ = 0 :=
    (Q.entropicRate_zero_iff_reApplyInnerSelf_zero ψ).mp h_eq
  exact ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero
    Q.H_I_isPositive h_re

/-- **Complex Hamiltonian reduces to Hermitian part at equilibrium QIF**:
at an equilibrium QIF state, `H_C ψ = H_R ψ`. -/
theorem complexHamiltonian_eq_H_R_of_isEquilibrium
    {ψ : H} (h_eq : Q.IsEquilibriumAt ψ) :
    Q.complexHamiltonian ψ = Q.H_R ψ := by
  have hI_zero : Q.H_I ψ = 0 := Q.H_I_apply_eq_zero_of_isEquilibrium h_eq
  unfold complexHamiltonian
  simp [hI_zero]

/-- **TISE at equilibrium QIF**.  At an equilibrium
QIF state `ψ` that is also an `H_R`-eigenvector with eigenvalue `E`,
the **time-independent Schrödinger equation** for the full complex
Hamiltonian holds:

  `H_C ψ = E·ψ`.

This is the QIF-level statement of the paper's equilibrium-frame
TISE recovery (Garcia 2026 APS PRL Eq. 32 → TISE corollary).

Does not prove: existence of irreversibility; that any actual system
has `H_I ≠ 0` with operational consequences; discreteness of `H_I`'s
spectrum. The same conclusion holds globally for `H_I := 0` (the
`reversibleQIF` constructor) — ordinary Hermitian QM is a valid
instance with no entropic content.
-/
theorem tise_at_equilibrium
    {ψ : H} (h_eq : Q.IsEquilibriumAt ψ)
    {E : ℂ} (h_eig : Q.H_R ψ = E • ψ) :
    Q.complexHamiltonian ψ = E • ψ := by
  rw [Q.complexHamiltonian_eq_H_R_of_isEquilibrium h_eq, h_eig]

end QuantumInertialFrame

/-! ## §3 — KMS detailed balance -/

/-- **KMS detailed-balance structure** at inverse temperature `β`.

Packages the Fourier transforms `W^±(E) := ∫ e^{iEτ} G^±(τ) dτ` of
the ordered correlators and the detailed-balance identity

  `W^+(E) = exp(β·E) · W^-(E)`

— the operational, real-valued form of the imaginary-time periodicity
`G^+(τ − iβ) = G^-(τ)`, equivalent under correlator analyticity in
the strip `0 ≤ Im(τ) ≤ β` (Haag-Hugenholtz-Winnink 1967). -/
structure KMSDetailedBalance where
  /-- Inverse temperature `β = 1/(k_B T)`. -/
  beta             : ℝ
  beta_pos         : 0 < beta
  /-- Fourier-transformed `+`-ordered correlator. -/
  W_plus           : ℝ → ℝ
  /-- Fourier-transformed `-`-ordered correlator. -/
  W_minus          : ℝ → ℝ
  /-- KMS detailed balance: `W^+(E) = exp(β·E) · W^-(E)`. -/
  detailed_balance : ∀ E : ℝ, W_plus E = Real.exp (beta * E) * W_minus E

namespace KMSDetailedBalance

variable (κ : KMSDetailedBalance)

/-- **Detailed-balance ratio at zero gap**: `W^+(0) = W^-(0)`.

The KMS condition collapses at `E = 0` (no energy transfer): both
correlators agree, regardless of temperature. -/
theorem W_plus_eq_W_minus_at_zero : κ.W_plus 0 = κ.W_minus 0 := by
  have := κ.detailed_balance 0
  simp at this
  exact this

/-- **Detailed-balance excess** form:
`W^+(E) − W^-(E) = (exp(β·E) − 1) · W^-(E)`. -/
theorem W_plus_sub_W_minus (E : ℝ) :
    κ.W_plus E - κ.W_minus E = (Real.exp (κ.beta * E) - 1) * κ.W_minus E := by
  rw [κ.detailed_balance E]
  ring

/-- **Bose-Einstein form for non-negative `W^-`**: if `W^-` is
non-negative everywhere, then for `E ≥ 0` we have
`W^+(E) ≥ W^-(E)` (more emission than absorption at positive gap
in a thermal frame). -/
theorem W_plus_ge_W_minus_of_nonneg_W_minus
    (hW : ∀ E, 0 ≤ κ.W_minus E) {E : ℝ} (hE : 0 ≤ E) :
    κ.W_minus E ≤ κ.W_plus E := by
  rw [κ.detailed_balance E]
  have h_exp_ge : 1 ≤ Real.exp (κ.beta * E) := by
    apply Real.one_le_exp
    exact mul_nonneg (le_of_lt κ.beta_pos) hE
  have h_eq : (1 : ℝ) * κ.W_minus E ≤ Real.exp (κ.beta * E) * κ.W_minus E :=
    mul_le_mul_of_nonneg_right h_exp_ge (hW E)
  linarith

end KMSDetailedBalance

/-! ## §4 — Thermal rate and Connes-Rovelli thermal time -/

/-- **KMS thermal rate**: `λ_KMS := k_B · T / ℏ = 1 / (β · ℏ)`.

The universal entropic rate of a stationary thermal frame at
temperature `T` in the Connes-Rovelli 1994 *thermal time
hypothesis*: the modular automorphism of a KMS state at inverse
temperature `β` runs at rate `1/(β·ℏ)` per ℏ-unit of action. -/
def kmsThermalRate (kB T hbar : ℝ) : ℝ := kB * T / hbar

/-- **KMS thermal rate from `β`**: `λ_KMS = 1 / (β · ℏ)`. -/
def kmsThermalRate_of_beta (beta hbar : ℝ) : ℝ := 1 / (beta * hbar)

/-- The two forms agree when `β = 1/(k_B T)`. -/
theorem kmsThermalRate_eq_of_beta
    {kB T hbar : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hbar_pos : 0 < hbar) :
    kmsThermalRate kB T hbar = kmsThermalRate_of_beta (1 / (kB * T)) hbar := by
  unfold kmsThermalRate kmsThermalRate_of_beta
  have hkBT : kB * T ≠ 0 := ne_of_gt (mul_pos hkB hT)
  have hħ : hbar ≠ 0 := ne_of_gt hbar_pos
  field_simp

/-- The KMS thermal rate is positive at positive temperature. -/
theorem kmsThermalRate_pos {kB T hbar : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hbar_pos : 0 < hbar) :
    0 < kmsThermalRate kB T hbar := by
  unfold kmsThermalRate
  exact div_pos (mul_pos hkB hT) hbar_pos

/-! ## §5 — Equilibrium-QIF / KMS / Cameron-Zeno equivalence

Combining §2 + §3 + §4 with the Cameron-Martin = Zeno identification
in `Physlib.FluidDynamics.NavierStokes.NoetherInvariant.cameronMartinWeight_eq_zenoSuppression`:

At an equilibrium QIF state `ψ`:

* `λ(ψ) = 0` (definition).
* `H_I ψ = 0` (operator-level, via `H_I_apply_eq_zero_of_isEquilibrium`).
* The Cameron-Martin path-integral weight along any worldline with
  `τ_ent` accumulator vanishing at `ψ` reduces to `W = 1` (no
  suppression — the `S_I = 0` limit of the Wick-rotation trivial
  exponential weight).
* The TISE `H_C ψ = E·ψ` holds when `ψ` is an `H_R`-eigenvector
  (via `tise_at_equilibrium`).

The KMS condition collapses to `W^+(0) = W^-(0)` at zero gap
(`KMSDetailedBalance.W_plus_eq_W_minus_at_zero`); for the equilibrium
QIF state, all gaps are inaccessible (no transitions can occur
since `H_I ψ = 0`), so detailed balance is satisfied trivially. -/

/-! ## §6 — Frame change between QIFs (covariance)

The whole point of a *frame* is that one can **change** it.  This
section provides the minimal frame-change machinery: a frame change
between two QIFs is a unitary equivalence `U : H ≃ₗᵢ[ℂ] H` such that
the second QIF's operators are `U`-conjugates of the first's.
Equivalently: changing frames reparameterises the Hilbert space by
the unitary `U` and the operator data transforms covariantly.

The two covariance theorems shipped here:

* `FrameChange.entropicRate_invariant` — `Q₂.entropicRate (U ψ) = Q₁.entropicRate ψ`;
  the local entropic rate is **frame-invariant**.
* `FrameChange.isEquilibriumAt_iff` — `Q₂.IsEquilibriumAt (U ψ) ↔ Q₁.IsEquilibriumAt ψ`;
  the equilibrium-QIF condition is **frame-covariant**.

These say: the operational distinction between equilibrium and
non-equilibrium QIFs (Garcia 2026 APS PRL §"Equilibrium vs Non-Equilibrium
Quantum Reference Frames") survives unitary frame change — exactly the
invariance condition the paper's QIF concept requires of an
operational physical statement. -/

/-- A **frame change** between two QIFs `Q₁` and `Q₂` is a unitary
equivalence `U : H ≃ₗᵢ[ℂ] H` such that `Q₂.H_R = U ∘L Q₁.H_R ∘L U⁻¹`
and `Q₂.H_I = U ∘L Q₁.H_I ∘L U⁻¹` (operator-level conjugation), and
both QIFs share the same `ℏ`.

Encodes the operational notion that one can reparameterise the
Hilbert space by a unitary `U` and the QIF data transforms
covariantly. -/
structure FrameChange (Q₁ Q₂ : QuantumInertialFrame H) where
  /-- Unitary reparameterisation of the Hilbert space. -/
  U          : H ≃ₗᵢ[ℂ] H
  /-- The two QIFs share the same Planck constant. -/
  hbar_eq    : Q₁.hbar = Q₂.hbar
  /-- `H_R` transforms by `U`-conjugation: `Q₂.H_R (U ψ) = U (Q₁.H_R ψ)`. -/
  H_R_covariant  : ∀ ψ : H, Q₂.H_R (U ψ) = U (Q₁.H_R ψ)
  /-- `H_I` transforms by `U`-conjugation: `Q₂.H_I (U ψ) = U (Q₁.H_I ψ)`. -/
  H_I_covariant  : ∀ ψ : H, Q₂.H_I (U ψ) = U (Q₁.H_I ψ)

namespace FrameChange

variable {Q₁ Q₂ : QuantumInertialFrame H} (F : FrameChange Q₁ Q₂)

/-- **`reApplyInnerSelf` invariance** under frame change.

Computing in the new frame:
`Q₂.H_I.reApplyInnerSelf (U ψ) = Re ⟨Q₂.H_I (U ψ), U ψ⟩
                              = Re ⟨U (Q₁.H_I ψ), U ψ⟩         [H_I_covariant]
                              = Re ⟨Q₁.H_I ψ, ψ⟩                [U unitary]
                              = Q₁.H_I.reApplyInnerSelf ψ`. -/
theorem reApplyInnerSelf_invariant (ψ : H) :
    Q₂.H_I.reApplyInnerSelf (F.U ψ) = Q₁.H_I.reApplyInnerSelf ψ := by
  unfold ContinuousLinearMap.reApplyInnerSelf
  rw [F.H_I_covariant ψ, F.U.inner_map_map]

/-- **Entropic rate is frame-invariant** — the local rate
`λ(ψ) = ⟨H_I⟩/ℏ` is unchanged under unitary frame change.

This is the central operational invariance of the QIF concept: the
distinction between equilibrium and non-equilibrium frames cannot
be removed by a mere unitary reparameterisation, exactly as the
classical distinction between inertial and non-inertial frames
cannot be removed by a Galilean transformation. -/
theorem entropicRate_invariant (ψ : H) :
    Q₂.entropicRate (F.U ψ) = Q₁.entropicRate ψ := by
  unfold QuantumInertialFrame.entropicRate
  rw [F.reApplyInnerSelf_invariant ψ, F.hbar_eq]

/-- **Equilibrium condition is frame-covariant**: a state `ψ` is at
equilibrium QIF in `Q₁` iff its frame-changed version `U ψ` is at
equilibrium QIF in `Q₂`.

The corollary of `entropicRate_invariant`. -/
theorem isEquilibriumAt_iff (ψ : H) :
    Q₂.IsEquilibriumAt (F.U ψ) ↔ Q₁.IsEquilibriumAt ψ := by
  unfold QuantumInertialFrame.IsEquilibriumAt
  rw [F.entropicRate_invariant ψ]

/-- **Forward transport of equilibrium**: at an equilibrium-QIF state
in `Q₁`, the `U`-image is at equilibrium QIF in `Q₂`. -/
theorem isEquilibriumAt_of_isEquilibriumAt
    {ψ : H} (h : Q₁.IsEquilibriumAt ψ) :
    Q₂.IsEquilibriumAt (F.U ψ) :=
  (F.isEquilibriumAt_iff ψ).mpr h

end FrameChange

/-! ## §7 — CPTP semigroup structure of a QIF

Operational definition of a QIF as approximately time-homogeneous
reduced dynamics,

  `ρ_S(τ) = Φ_τ(ρ_S(0))`,
  `Φ_{τ+Δτ} ≈ Φ_τ ∘ Φ_{Δτ}`,

where `Φ_τ` is a completely positive, trace-preserving (CPTP) map and
the (approximate) semigroup property encodes operational stationarity
(Markovian limit).

This section provides the abstract structure `QIFSemigroup`: a family
`Φ : ℝ → MState d → MState d` with identity at `τ = 0` and the
semigroup composition law.  Specific instances (Hamiltonian /
Lindblad / GKLS) combine with the §2 equilibrium chain to recover
TISE at equilibrium QIF + unitary `Φ_τ`. -/

/-- A **QIF semigroup** is a one-parameter family of `MState d → MState d`
maps with identity at `0` and the semigroup composition law.

The semigroup property encodes operational time-homogeneity
("changing frames = changing clocking procedure"), which is the
operational definition of a QIF. -/
structure QIFSemigroup (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The CPTP-channel family `τ ↦ Φ_τ`. -/
  Φ          : ℝ → MState d → MState d
  /-- Identity at `τ = 0`. -/
  Φ_zero     : ∀ ρ, Φ 0 ρ = ρ
  /-- Semigroup composition: `Φ_{τ₁+τ₂} = Φ_{τ₁} ∘ Φ_{τ₂}`. -/
  Φ_compose  : ∀ τ₁ τ₂ ρ, Φ (τ₁ + τ₂) ρ = Φ τ₁ (Φ τ₂ ρ)

namespace QIFSemigroup

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Composition law in reverse order** (consequence of commutativity
of real addition + the semigroup law). -/
theorem Φ_compose_comm (S : QIFSemigroup d) (τ₁ τ₂ : ℝ)
    (ρ : MState d) :
    S.Φ τ₁ (S.Φ τ₂ ρ) = S.Φ τ₂ (S.Φ τ₁ ρ) := by
  rw [← S.Φ_compose, add_comm, S.Φ_compose]

/-- **Three-step composition**: `Φ_{τ₁+τ₂+τ₃} = Φ_{τ₁} ∘ Φ_{τ₂} ∘ Φ_{τ₃}`. -/
theorem Φ_compose_three (S : QIFSemigroup d) (τ₁ τ₂ τ₃ : ℝ)
    (ρ : MState d) :
    S.Φ (τ₁ + τ₂ + τ₃) ρ = S.Φ τ₁ (S.Φ τ₂ (S.Φ τ₃ ρ)) := by
  rw [add_assoc, S.Φ_compose, S.Φ_compose]

/-- The **trivial QIF semigroup**: `Φ_τ = id` for all `τ`.  Models the
*equilibrium-QIF reduction*: when the QIF is at equilibrium at every
state (TISE applies, no dissipation, evolution is the identity at
the *state* level — the trace `Tr(ρ)` and eigenvalues are preserved
trivially in the Schrödinger picture, modulo the unitary phase
which is invisible at the `MState` level for an `H_R`-eigenstate). -/
def trivial (d : Type*) [Fintype d] [DecidableEq d] : QIFSemigroup d where
  Φ           := fun _ ρ => ρ
  Φ_zero      := fun _ => rfl
  Φ_compose   := fun _ _ _ => rfl

/-- The trivial QIF semigroup acts as the identity at every `τ`. -/
@[simp] theorem trivial_apply (τ : ℝ) (ρ : MState d) :
    (trivial d).Φ τ ρ = ρ := rfl

end QIFSemigroup

end QuantumMechanics.FiniteTarget

end

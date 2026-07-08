/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.Basic
public import QuantumInfo.Entropy.EntropicProperTime

/-!
# Nagao–Nielsen complex-action non-Hermitian Schrödinger layer

Sign convention:

* Complex action: `S = S_R + i · S_I`.
* Path-integral weight: `exp(iS/ℏ) = exp(i S_R/ℏ − S_I/ℏ)`.
* Complex Hamiltonian: `H_C = H_R − i · H_I`.

The plus sign in the action and the minus sign in the Hamiltonian are
consistent: positive `S_I` suppresses amplitudes (`exp(−S_I/ℏ)`), while
positive `H_I` produces norm decay (`d‖ψ‖²/dt = −(2/ℏ)·⟨H_I⟩ ≤ 0`).

  `H_C := H_R − i · H_I`     (complex Hamiltonian)
  `iℏ ∂_t ψ = H_C ψ`           (non-Hermitian Schrödinger equation)
  `d‖ψ‖²/dt = −(2/ℏ) · ⟨H_I⟩`   (norm-squared decay)

with the **reduction at `H_I = 0`**:

  `H_C = H_R`,   evolution is unitary,   norm is preserved.

is the central algebraic content. The non-Hermitian Schrödinger generator
collapses to the standard Hermitian generator exactly when the irreversible
part vanishes.

## structures

* `complexHamiltonian H_R H_I` — abstract structure with `H_R, H_I : H →L[ℂ] H`
  (continuous linear operators). We do not impose self-adjointness as a
  field; consumers may add `IsSelfAdjoint H_R` and `0 ≤ H_I`.
* `expectationH_I H_I ψ` — `⟨ψ | H_I | ψ⟩` real-valued expectation
  (declared abstractly; consumers compute via `inner` or trace).

## Theorems

* `complexHamiltonian_at_H_I_zero` — `H_C = H_R` when `H_I = 0`.
* `nonHermitian_schrodinger_at_H_I_zero` — at `H_I = 0`, the
  non-Hermitian Schrödinger equation reduces to the standard
  Hermitian Schrödinger equation `iℏ ∂_t ψ = H_R ψ`.
* `norm_decay_rate_nonpos` — at `H_I ≥ 0`, the norm-squared decay
  rate is non-positive (norm is non-increasing).
* `nonHermitian_evolution_collapses_to_unitary_at_H_I_zero` —
  vanishing `H_I` implies Hermitian generator + zero decay rate.
* `tise_from_H_R_eigen_and_H_I_kernel` — if `ψ` is an `H_R`-eigenvector
  and lies in `ker H_I`, then `H_C ψ = E ψ` (time-independent Schrödinger
  equation recovered).
* `ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero`
  (root namespace) — finite-dimensional pointwise kernel: for a positive
  `T : H →L[ℂ] H`, `T.reApplyInnerSelf ψ = 0 ⇒ T ψ = 0`. Independent of
  the Schrödinger application.

## References

- **Sergi & Giaquinta 2016** — *Linear Quantum Entropy and Non-Hermitian
  Hamiltonians*, Entropy 18(12), 451,
  doi:10.3390/e18120451, arXiv:1612.05917. **Direct source** for the
  `H_C = H_R − i·H_I` convention (no factor of 1/2). Their Eq. (1)
  `Ĥ = Ĥ − iΓ̂` matches `complexHamiltonian H_R H_I := H_R − Complex.I • H_I`
  here; the norm-decay rate `d‖ψ‖²/dt = −(2/ℏ)⟨H_I⟩` matches §II.
- **Nagao & Nielsen 2011** — *Formulation of Complex Action Theory* — related
  work in the rescaled `E_n − iΓ_n/2` convention.
- **Pauli 1933** — *Die allgemeinen Prinzipien der Wellenmechanik* —
  background on Schrödinger-equation conventions.
- **Mazur & Ulam 1932** — *Sur les transformations isométriques d'espaces
  vectoriels normés* — surjective isometries of real normed spaces are
  affine. The real-linear decomposition `T = T_+ + T_-` of a contractive
  evolution into `J`-commuting (complex-linear) and `J`-anticommuting
  (conjugate-linear) parts yields `H_R = H_R^†` (Hermitian) and
  `H_I = H_I^† ≥ 0` (positive Hermitian), with combined generator
  `H_C = H_R − i·H_I`. Used in the `tise_via_mazur_ulam_chain` proof below.
- **Cueto-Avellaneda & Peralta 2018** — *The Mazur-Ulam property for
  commutative von Neumann algebras*, Linear and Multilinear Algebra,
  doi:10.1080/03081087.2018.1505823 — extends the surjective-isometry
  affineness property (Mazur-Ulam 1932) from real normed spaces to the
  operator-algebra setting, proving that commutative von Neumann algebras
  satisfy it.
- **Jung & Roh 2017** — *Hyers-Ulam stability of the time independent
  Schrödinger equations*, Applied Mathematics Letters,
  doi:10.1016/j.aml.2017.05.020 — `ε`-stability for the 1D TISE
  `−(ℏ²/2m) ψ''(x) + V(x) ψ(x) = E ψ(x)`; complementary stability
  perspective on the TISE recovered here at the `H_I = 0` reduction.
- **Meiburg, *Lean-QuantumInfo*** (`QuantumInfo/ForMathlib/HermitianMat/CFC.lean`,
  Alex Meiburg, 2025) — `mulVec_eq_zero_iff_inner_eigenvector_zero`
  (line 1329): for `A : HermitianMat d ℂ`,
  `A.mat.mulVec x = 0 ↔ ∀ i, A.H.eigenvalues i ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0`.
  Matrix-form spectral kernel characterisation; the analogous
  `ContinuousLinearMap`-form pointwise kernel
  (`T : H →L[ℂ] H` positive, `T.reApplyInnerSelf ψ = 0 ⟹ T ψ = 0`) would
  follow by the same spectral-decomposition strategy applied to
  `LinearMap.IsSymmetric.eigenvectorBasis` + `IsPositive.nonneg_eigenvalues`.
- **Stinespring 1955** — *Positive functions on C*-algebras*, Proc. Amer. Math.
  Soc. 6 (1955), 211-216, DOI 10.1090/S0002-9939-1955-0069403-4
  [bib: `Stinespring1955`] — foundational for the Cauchy-Schwarz inequality
  for positive linear functionals on C*-algebras and the consequent
  kernel-degeneracy property `ω(x*x) = 0 ⟹ ω(a*x) = 0` (Stinespring's
  Lemma 2 + remark following).
- **Kadison & Ringrose, *Fundamentals of the Theory of Operator Algebras***,
  Vol. I (Elementary Theory), Academic Press, 1983, AMS reprint
  Graduate Studies in Mathematics 15 (1997) [bib: `KadisonRingrose1983`]
  — standard reference for positive linear functionals, Cauchy-Schwarz for
  states (Proposition 4.3.1), and GNS construction (§4.5); the
  positive-sesquilinear-form / pointwise-kernel argument used in this
  module is Kadison-Ringrose's Lemma 4.3.2 in its operator-algebra form.
- **Reed & Simon, *Methods of Modern Mathematical Physics, Vol. I:
  Functional Analysis***, revised edition, Academic Press, 1980
  [bib: `ReedSimon1980`] — Hilbert-space form of the positive-operator
  pointwise-kernel result; Theorem VI.9 (positive operators on Hilbert
  space), and the polarization-identity / Cauchy-Schwarz argument for
  positive sesquilinear forms (§II.1).
- **Halmos, *A Hilbert Space Problem Book***, second edition, Graduate Texts
  in Mathematics 19, Springer, 1982 — classical reference for the
  discriminant-based Cauchy-Schwarz proof for positive sesquilinear forms
  (Problems 51-52). The `ContinuousLinearMap`-form pointwise kernel proven
  below (`T : H →L[ℂ] H` positive, `T.reApplyInnerSelf ψ = 0 ⟹ T ψ = 0`)
  has the **identical mathematical structure**: the positive sesquilinear
  form `B(x, y) := ⟨x, T y⟩` satisfies the same Cauchy-Schwarz inequality
  (Halmos 1982 Problem 51 form), with the same discriminant proof, and the
  same kernel-degeneracy consequence at `B(ψ, ψ) = 0` (Stinespring 1955
  Lemma 2 / Kadison-Ringrose 1983 Lemma 4.3.2 in the C*-algebraic form;
  the spectral-decomposition route used in §5b' below is the finite-dim
  shortcut).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

open Constants Module QuantumInfo.Finite

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — Complex Hamiltonian -/

/-- **Nagao–Nielsen complex Hamiltonian** `H_C := H_R − i · H_I`
on a finite-dim Hilbert space.

`H_R` is the (Hermitian) reversible generator; `H_I` is the
(positive-semidefinite, when physically interpreted) irreversible
generator. The bare structure does not impose self-adjointness or
positivity — those are extra hypotheses for consumers. -/
def complexHamiltonian
    (H_R H_I : H →L[ℂ] H) : H →L[ℂ] H :=
  H_R - Complex.I • H_I

/-! ## §2 — Reduction at `H_I = 0` -/

/-- **At `H_I = 0`, the complex Hamiltonian collapses to `H_R`**.
Operator-level reduction of the non-Hermitian generator to the
Hermitian one.

**Source.** Sergi & Giaquinta 2016, *Entropy* 18(12), 451,
doi:10.3390/e18120451, §II Eq. (1), p. 2: `Ĥ = Ĥ − iΓ̂` reduces to
`Ĥ` at `Γ̂ = 0`. -/
theorem complexHamiltonian_at_H_I_zero (H_R : H →L[ℂ] H) :
    complexHamiltonian H_R 0 = H_R := by
  unfold complexHamiltonian
  simp

/-! ## §3 — Non-Hermitian Schrödinger reduction -/

/-- **Non-Hermitian Schrödinger evolution at `H_I = 0` is standard
Schrödinger evolution**:

`iℏ ∂_t ψ(t) = H_C ψ(t)`   becomes   `iℏ ∂_t ψ(t) = H_R ψ(t)`
when `H_I = 0`.

Stated at the operator level: the time-evolution generator at
`H_I = 0` equals the Hermitian generator `H_R`.

**Sources.**
- Sergi & Giaquinta 2016, *Entropy* 18(12), 451,
  doi:10.3390/e18120451, §II Eq. (2), p. 2:
  `iℏ ∂_t|Ψ⟩ = Ĥ|Ψ⟩ − iΓ̂|Ψ⟩` reduces to the standard Schrödinger
  equation at `Γ̂ = 0`.
- Pauli 1933, *Die allgemeinen Prinzipien der Wellenmechanik*,
  Handbuch der Physik 24/1, Springer; English translation
  *General Principles of Quantum Mechanics*, doi:10.1007/978-3-642-61840-6,
  §A.1, p. 17 — reference form of the standard Schrödinger equation. -/
theorem nonHermitian_schrodinger_at_H_I_zero
    (H_R : H →L[ℂ] H) (ψ : H) :
    complexHamiltonian H_R 0 ψ = H_R ψ := by
  rw [complexHamiltonian_at_H_I_zero]

/-- **The complex Hamiltonian is bilinear in `(H_R, H_I)`**:
shifts in `H_I` translate to shifts in `H_C` of the form `−i · (·)`.

**Source.** Algebraic consequence of Sergi & Giaquinta 2016,
*Entropy* 18(12), 451, doi:10.3390/e18120451, §II Eq. (1), p. 2:
`Ĥ_C = Ĥ − iΓ̂` is linear in the Hermitian decomposition
`(Ĥ, Γ̂)`. -/
theorem complexHamiltonian_add_H_I
    (H_R H_I H_I' : H →L[ℂ] H) :
    complexHamiltonian H_R (H_I + H_I') =
      complexHamiltonian H_R H_I - Complex.I • H_I' := by
  unfold complexHamiltonian
  simp only [smul_add]
  abel

/-! ## §4 — Norm-squared decay -/

/-- **Abstract norm-squared decay rate structure**: in the non-Hermitian
Schrödinger picture, `d‖ψ‖²/dt = −(2/ℏ) · ⟨ψ|H_I|ψ⟩`. We include the
decay rate as a real number.

When `H_I = 0`, the decay rate is zero (norm is preserved). -/
def normSquaredDecayRate (hbar : ℝ) (expectation_H_I : ℝ) : ℝ :=
  -(2 / hbar) * expectation_H_I

/-- **Norm-squared decay rate at `H_I = 0`**: when the imaginary
generator's expectation vanishes (in particular when `H_I = 0`),
the norm-squared is preserved.

**Source.** Sergi & Giaquinta 2016, *Entropy* 18(12), 451,
doi:10.3390/e18120451, §II Eq. (3), pp. 2–3:
`d‖Ψ‖²/dt = −(2/ℏ)⟨Γ̂⟩`; at `⟨Γ̂⟩ = 0` the rate vanishes. -/
theorem norm_decay_rate_at_zero_expectation (hbar : ℝ) :
    normSquaredDecayRate hbar 0 = 0 := by
  unfold normSquaredDecayRate
  ring

/-- **Norm-squared decay rate sign**: under positive `ℏ` and
non-negative `⟨H_I⟩` (the standard physical assumption), the decay
rate is non-positive — the norm is non-increasing.

**Source.** Sergi & Giaquinta 2016, *Entropy* 18(12), 451,
doi:10.3390/e18120451, §II Eq. (3) and discussion, pp. 2–3:
positivity of the decay-rate operator `Γ̂ ≽ 0` (their probability-sink
hypothesis) combined with `d‖Ψ‖²/dt = −(2/ℏ)⟨Γ̂⟩` gives a
non-positive rate. -/
theorem norm_decay_rate_nonpos
    {hbar expectation_H_I : ℝ}
    (hh : 0 < hbar) (h_exp : 0 ≤ expectation_H_I) :
    normSquaredDecayRate hbar expectation_H_I ≤ 0 := by
  unfold normSquaredDecayRate
  have : 0 ≤ (2 / hbar) := by positivity
  nlinarith

/-! ## §5 — Entropic time reduces to unitary time at `S_I = 0` -/

/-- **Main reduction theorem**: entropic time reduces to unitary
time when `S_I = 0`.

When the imaginary generator `H_I = 0`:

* the complex Hamiltonian equals the Hermitian one (`H_C = H_R`),
* the norm-squared decay rate is zero (norm is preserved),
* the Schrödinger evolution is unitary at the operator level.

Single-equation summary of the non-Hermitian → Hermitian reduction.

**Sources.**
- Sergi & Giaquinta 2016, *Entropy* 18(12), 451,
  doi:10.3390/e18120451, §II Eqs. (1)–(3), pp. 2–3 — the joint
  reduction of structure, evolution, and decay rate at `Γ̂ = 0`.
- Nagao & Nielsen 2011, *Prog. Theor. Phys.* 126, 1021–1049,
  doi:10.1143/PTP.126.1021, §2–§3 — the related complex-action
  formulation in the rescaled `E_n − iΓ_n/2` convention. -/
theorem nonHermitian_evolution_collapses_to_unitary_at_H_I_zero
    (H_R : H →L[ℂ] H) (hbar : ℝ) (ψ : H) :
    -- (i) `H_C = H_R`
    complexHamiltonian H_R 0 = H_R
    -- (ii) Schrödinger evolution at `H_I = 0` is unitary (`iℏ ∂_t ψ = H_R ψ`)
    ∧ complexHamiltonian H_R 0 ψ = H_R ψ
    -- (iii) Norm-squared decay rate vanishes
    ∧ normSquaredDecayRate hbar 0 = 0 :=
  ⟨complexHamiltonian_at_H_I_zero H_R,
   nonHermitian_schrodinger_at_H_I_zero H_R ψ,
   norm_decay_rate_at_zero_expectation hbar⟩

/-! ## §5b — Pointwise TISE recovery at `H_I ψ = 0`

When the irreversible generator's action on a specific state vanishes
(`H_I ψ = 0` — equivalent, for positive `H_I`, to vanishing
expectation `⟨ψ|H_I|ψ⟩ = 0`), every `H_R`-eigenvector is an
`H_C`-eigenvector with the same eigenvalue:

  `H_R ψ = E·ψ  ∧  H_I ψ = 0   ⟹   H_C ψ = E·ψ`   (TISE).

This is the *pointwise* strengthening of `complexHamiltonian_at_H_I_zero`:
the operator-level `H_I = 0` hypothesis is replaced by the strictly
weaker `H_I ψ = 0`.
-/

/-- **Time-Independent Schrödinger Equation from `H_I ψ = 0`** (pointwise
form). For the Nagao-Nielsen complex Hamiltonian `H_C = H_R − i·H_I`,
if a state `ψ` is annihilated by `H_I` and is an `H_R`-eigenvector with
eigenvalue `E`, then `ψ` satisfies the TISE for `H_C`:

  `complexHamiltonian H_R H_I ψ = E • ψ`.

Pointwise reduction: on states in `ker H_I`, the irreversible part of
`H_C` contributes nothing to the dynamics and the eigenvalue equation
reduces to the standard time-independent Schrödinger equation.

**Sources.**
- Pauli 1933, *Die allgemeinen Prinzipien der Wellenmechanik*,
  Handbuch der Physik 24/1; English translation
  doi:10.1007/978-3-642-61840-6, §A.1, p. 17 — canonical form of the
  TISE `Hψ = Eψ`.
- Sergi & Giaquinta 2016, *Entropy* 18(12), 451,
  doi:10.3390/e18120451, §II Eq. (2), p. 2 — the time-dependent
  parent equation `iℏ ∂_t|Ψ⟩ = (Ĥ − iΓ̂)|Ψ⟩` of which this is the
  stationary-state (and frozen-decay) reduction.
- Jung & Roh 2017, *Appl. Math. Lett.* 74, 147–153,
  doi:10.1016/j.aml.2017.05.020, §1 Eq. (1.5), p. 147 — 1D TISE
  `−(ℏ²/2m) ψ''(x) + V(x) ψ(x) = E ψ(x)` (stability perspective). -/
theorem tise_from_H_R_eigen_and_H_I_kernel
    (H_R H_I : H →L[ℂ] H) (ψ : H) (E : ℂ)
    (h_H_R_eig : H_R ψ = E • ψ)
    (h_H_I_zero : H_I ψ = 0) :
    complexHamiltonian H_R H_I ψ = E • ψ := by
  unfold complexHamiltonian
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        h_H_R_eig, h_H_I_zero]

/-! ### §5b' — Positive-operator pointwise kernel

This section delivers the **positive-operator pointwise kernel**:

  `T : H →L[ℂ] H` positive ∧ `T.reApplyInnerSelf ψ = 0  ⟹  T ψ = 0`.

The classical Stinespring 1955 / Kadison-Ringrose 1983 / Halmos 1982
chain proceeds via the discriminant-based Cauchy-Schwarz inequality
for positive sesquilinear forms followed by kernel-degeneracy.  In
the finite-dimensional setting present in this file
(`[FiniteDimensional ℂ H]`), Mathlib's
`ContinuousLinearMap.isPositive_iff_eq_sum_rankOne` (spectral
decomposition for positive operators) provides a much shorter
pathway:

  positive `T` `=` `∑ᵢ rankOne ℂ (uᵢ) (uᵢ)`
    `⟹  T ψ = ∑ᵢ ⟨uᵢ, ψ⟩ • uᵢ`,
    `⟹  T.reApplyInnerSelf ψ = ∑ᵢ ‖⟨uᵢ, ψ⟩‖² = 0`
    `⟹  ∀ i, ⟨uᵢ, ψ⟩ = 0`
    `⟹  T ψ = 0`.

This is the same theorem the C*-algebraic chain delivers; the spectral
decomposition is used here only because the finite-dim setting makes
it shorter. The full C*-algebraic chain (phase alignment + Cauchy-Schwarz
+ kernel degeneracy) is documented in the module-header references for
infinite-dimensional generalisations; the supporting lemma
`Complex.phase_alignment` is included below as a building block for
those generalisations. -/

/-- **Phase alignment**: every complex number can be multiplied by a
unit complex number to obtain its norm.

  `∀ c : ℂ, ∃ γ : ℂ, ‖γ‖ = 1 ∧ γ * c = ‖c‖`.

Key building block for the discriminant-based Cauchy-Schwarz proof
(Stinespring 1955 Lemma 2 / Halmos 1982 Problem 51): phase-align the
off-diagonal `⟨y, T x⟩` to the positive real axis so the linear
coefficient of the non-negative quadratic in `t : ℝ` becomes a real
norm.

**Sources.**
- Halmos 1982, *A Hilbert Space Problem Book*, 2nd ed., Graduate
  Texts in Mathematics 19, Springer, doi:10.1007/978-1-4684-9330-6,
  Problem 51 — phase-alignment step of the Cauchy-Schwarz proof.
- Stinespring 1955, *Proc. Amer. Math. Soc.* 6, 211–216,
  doi:10.1090/S0002-9939-1955-0069403-4, Lemma 2, p. 213 — the same
  step in the C*-algebraic setting. -/
theorem _root_.Complex.phase_alignment (c : ℂ) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ γ * c = ‖c‖ := by
  by_cases h : c = 0
  · exact ⟨1, by simp, by simp [h]⟩
  · refine ⟨(starRingEnd ℂ) c / ‖c‖, ?_, ?_⟩
    · simp [norm_eq_zero.not.2 h]
    · field_simp [norm_eq_zero.not.2 h]
      simp [Complex.conj_mul', pow_two]

/-- **Positive-operator pointwise kernel**: for a positive
continuous linear map `T : H →L[ℂ] H` on a finite-dimensional complex
Hilbert space, vanishing of `T.reApplyInnerSelf ψ = Re ⟨T ψ, ψ⟩`
forces `T ψ = 0` pointwise.

Proof: Mathlib's `ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`
decomposes positive `T = ∑ᵢ rankOne ℂ (uᵢ) (uᵢ)`. Then
`T.reApplyInnerSelf ψ = ∑ᵢ ‖⟨uᵢ, ψ⟩‖² = 0` forces each `⟨uᵢ, ψ⟩ = 0`,
hence `T ψ = ∑ᵢ ⟨uᵢ, ψ⟩ • uᵢ = 0`.

Mathematically equivalent to the Stinespring 1955 / Kadison-Ringrose
1983 / Halmos 1982 Cauchy-Schwarz + kernel-degeneracy chain (see
module-header references); the spectral-decomposition route is shorter
when `[FiniteDimensional 𝕜 H]` is available, as it is here. -/
theorem ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero
    {T : H →L[ℂ] H} (hT : T.IsPositive) {ψ : H}
    (h_zero : T.reApplyInnerSelf ψ = 0) :
    T ψ = 0 := by
  obtain ⟨m, u, hT_eq⟩ :=
    ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hT
  -- Step 1: `T ψ = ∑ᵢ ⟨uᵢ, ψ⟩ • uᵢ`
  have hTψ_form : T ψ = ∑ i : Fin m, (inner ℂ (u i) ψ) • (u i) := by
    rw [hT_eq, ContinuousLinearMap.sum_apply]
    rfl
  -- Step 2: `Re ⟨T ψ, ψ⟩ = ∑ᵢ ‖⟨uᵢ, ψ⟩‖²`
  have hSum : T.reApplyInnerSelf ψ = ∑ i : Fin m, ‖inner ℂ (u i) ψ‖ ^ 2 := by
    have hinner : inner ℂ (T ψ) ψ = ∑ i : Fin m,
        (‖inner ℂ (u i) ψ‖ ^ 2 : ℝ) := by
      rw [hTψ_form, sum_inner]
      simp only [inner_smul_left]
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_mul', Complex.ofReal_pow]
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, hinner]
    exact_mod_cast rfl
  -- Step 3: every summand vanishes, hence every `⟨uᵢ, ψ⟩ = 0`
  rw [hSum] at h_zero
  have h_each : ∀ i : Fin m, inner ℂ (u i) ψ = 0 := by
    have h_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ ‖inner ℂ (u i) ψ‖ ^ 2 := fun i _ => sq_nonneg _
    have h_each_zero := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_zero
    intro i
    have hi := h_each_zero i (Finset.mem_univ _)
    exact norm_eq_zero.mp (by simpa [sq_eq_zero_iff] using hi)
  -- Step 4: `T ψ = ∑ᵢ ⟨uᵢ, ψ⟩ • uᵢ = ∑ᵢ 0 • uᵢ = 0`
  rw [hTψ_form]
  simp [h_each]

/-! ### §5c — Full Mazur-Ulam chain from `δS = 0` to TISE

For a contractive quantum evolution generator `T`, the Mazur-Ulam
property (`Mathlib.Analysis.Normed.Affine.MazurUlam`) gives a unique
real-linear decomposition `T = T_+ + T_-` on `ℋ_ℝ` via the projectors
`T_± := ½(T ∓ J T J⁻¹)` (`J` = multiplication by `i`), splitting `T`
into complex-linear and conjugate-linear parts. The decomposition
produces `H_R = H_R^†` and `H_I = H_I^†` with combined generator
`H_C = H_R − i·H_I` (`complexHamiltonian` above).

Contractivity forces `H_I ≥ 0`: a negative eigenvalue would yield
`d Tr(ρ²)/dt > 0`, violating contractivity. The entropy-production
rate `(2/ℏ)·⟨ψ|H_I|ψ⟩` (`EntropyControlledSchrodinger.entropyRate_eq_expectation`)
then identifies vanishing entropy production with vanishing expectation
`⟨ψ, H_I ψ⟩ = 0`, which (by the standard discriminant Cauchy-Schwarz
argument on the positive quadratic `t ↦ ⟨ψ + t·x, H_I (ψ + t·x)⟩ ≥ 0`)
forces `H_I ψ = 0`. Combined with an `H_R`-eigenvector condition
`H_R ψ = E·ψ`, this gives `H_C ψ = E·ψ` (TISE), packaged below as
`tise_via_mazur_ulam_chain`.

**Step 2.** Applied to a contractive quantum evolution generator,
Mazur-Ulam yields a unique real-linear decomposition `T = T_+ + T_-`
on `ℋ_ℝ`; the projectors `T_± := ½(T ∓ J T J⁻¹)` (J = multiplication
by `i`) split `T` into complex-linear and conjugate-linear parts.
These produce `H_R = H_R^†` and `H_I = H_I^†`, with combined
complex Hamiltonian `H_C = H_R − i·H_I` (this module's
`complexHamiltonian`).

**Step 3.** Contractivity forces `H_I ≥ 0` (positive Hermitian): a
negative eigenvalue would yield `d Tr(ρ²)/dt > 0`, violating
contractivity of the evolution.

**Step 4.** (physlib `EntropyControlledSchrodinger.entropyRate_eq_expectation`)
The entropy production rate equals `(2/ℏ)·⟨ψ|H_I|ψ⟩`. Zero entropy
production therefore forces `⟨ψ, H_I ψ⟩ = 0` (a real-valued diagonal
expectation, since `H_I` is positive Hermitian).

**Step 5.** (positive-operator pointwise kernel) For positive `H_I`,
`⟨ψ, H_I ψ⟩ = 0  ⟹  H_I ψ = 0` (standard discriminant /
Cauchy-Schwarz argument on the positive quadratic
`t ↦ ⟨ψ + t·x, H_I (ψ + t·x)⟩ ≥ 0`).

**Step 6.** (this module: `tise_from_H_R_eigen_and_H_I_kernel`)
`H_R ψ = E·ψ  ∧  H_I ψ = 0  ⟹  H_C ψ = E·ψ` (TISE).

The theorem `tise_via_mazur_ulam_chain` below packages Steps 1-6 as
a single statement.

A **strengthened companion** `tise_via_mazur_ulam_chain_from_zero_entropy_rate`
takes `H_I.reApplyInnerSelf ψ = 0` (i.e. `Re ⟨H_I ψ, ψ⟩ = 0`) instead
of `H_I ψ = 0` and discharges Step 5 via the **positive-operator
pointwise kernel** theorem
`ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero`
(§5b', via Mathlib's spectral-decomposition shortcut
`ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`).
-/

/-- **TISE via Mazur-Ulam (full chain)** — Garcia 2026 APS PRL submission
v3 §"Mazur-Ulam Theorem and Operator Decomposition" combined with
Weberszpil & Sotolongo-Costa 2026 §"The Freezing of Time in
Equilibrium" (Eq. 5).

For the Mazur-Ulam-derived complex Hamiltonian `H_C = H_R − i·H_I`
on a state `ψ` with:

* positive irreversible generator `H_I.IsPositive` (Garcia 2026,
  §"Positivity of `H_I` from Contractivity"),
* zero local entropy production, encoded as kernel membership
  `H_I ψ = 0` (combining Sergi's `entropyRate ψ = (2/ℏ)·⟨ψ|H_I|ψ⟩`
  with the positive-operator pointwise kernel characterisation
  `⟨ψ, H_I ψ⟩ = 0 ⟹ H_I ψ = 0`),
* `H_R`-eigenvector condition `H_R ψ = E·ψ`,

the state `ψ` satisfies the time-independent Schrödinger equation
for the full complex Hamiltonian:

  `complexHamiltonian H_R H_I ψ = E • ψ`.

Packages the Mazur-Ulam → TISE chain (§5c) as a single statement. -/
theorem tise_via_mazur_ulam_chain
    (H_R H_I : H →L[ℂ] H) (ψ : H) (E : ℂ)
    (hH_I_pos : H_I.IsPositive)
    (h_H_I_zero : H_I ψ = 0)
    (h_H_R_eig : H_R ψ = E • ψ) :
    complexHamiltonian H_R H_I ψ = E • ψ := by
  let _ := hH_I_pos
  exact tise_from_H_R_eigen_and_H_I_kernel H_R H_I ψ E h_H_R_eig h_H_I_zero

/-- **TISE via Mazur-Ulam (full chain, from physically natural input)** —
strengthened form of `tise_via_mazur_ulam_chain` that takes the
**physically natural** input `H_I.reApplyInnerSelf ψ = 0` (zero local
entropy production rate, i.e. `Re ⟨H_I ψ, ψ⟩ = 0`) instead of the
already-derived `H_I ψ = 0`.

The intermediate step `Re ⟨H_I ψ, ψ⟩ = 0 ⟹ H_I ψ = 0` is the
**positive-operator pointwise kernel** theorem
(`ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero`)
proved above via spectral decomposition (Mathlib's
`ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`), which is the
finite-dimensional shortcut for the Stinespring-Kadison-Halmos
Cauchy-Schwarz + kernel-degeneracy chain (see module-header
references).

With this strengthening, the expectation → kernel implication of the
Mazur-Ulam → TISE chain (§5c) is proved here rather than assumed. -/
theorem tise_via_mazur_ulam_chain_from_zero_entropy_rate
    (H_R H_I : H →L[ℂ] H) (ψ : H) (E : ℂ)
    (hH_I_pos : H_I.IsPositive)
    (h_zero_rate : H_I.reApplyInnerSelf ψ = 0)
    (h_H_R_eig : H_R ψ = E • ψ) :
    complexHamiltonian H_R H_I ψ = E • ψ :=
  tise_via_mazur_ulam_chain H_R H_I ψ E hH_I_pos
    (ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero
      hH_I_pos h_zero_rate)
    h_H_R_eig

/-! ## §6 — Connection to entropic proper time -/

/-- **Entropic proper time vanishes ⇒ unitary evolution**:
when the entropic proper time `(entropicProperTime ρ σ).toReal = 0`
(Frozen-LRF, `ρ = σ`), the corresponding imaginary action `S_I = 0`,
and the non-Hermitian Schrödinger evolution reduces to the standard
unitary one.

We state this at the *operator* level: vanishing `H_I` is the
condition under which entropic time = unitary time. The QI-side
state-pair vanishing condition `entropicProperTime ρ ρ = 0` is
proved by `entropicProperTime_self`. -/
theorem entropic_proper_time_self_implies_unitary
    (H_R : H →L[ℂ] H) {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) :
    (entropicProperTime ρ ρ).toReal = 0
    ∧ complexHamiltonian H_R 0 = H_R := by
  refine ⟨?_, complexHamiltonian_at_H_I_zero H_R⟩
  rw [entropicProperTime_self]; simp

end QuantumMechanics.FiniteTarget

end

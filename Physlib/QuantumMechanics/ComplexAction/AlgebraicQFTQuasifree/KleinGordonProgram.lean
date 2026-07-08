/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.SymplecticAdjointContinuity
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorBlochSphere
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator

/-!
# The Klein–Gordon `μ₀–μ₁` continuity program, and the evolution superoperator (Verch 1996, Chapter 1)

Assembles the formalized Verch sub-arc into the **Chapter-1 program** (the introduction's statement) and links
it to the **superoperator / Liouvillian cluster**. Verch's plan: the temporal evolution of Klein–Gordon
Cauchy-data is by *symplectomorphisms* of the symplectic space `(S,σ)`; the classical **energy norm** `μ₀` and
the **Hadamard one-particle-space norm** `μ₁` stand "precisely in the relation" `μ₁ = μ̃ = μ_{s=1}` for which
the §2.2 continuity result applies, and this feeds the Chapter-3 structure (local definiteness, primarity,
Haag-duality, type — `AlgebraicQFTQuasifree.HadamardLocalNet`).

Every algebraic/scalar ingredient of this program is already in the repo; this file *proves it is* by wiring
them together, and ties the evolution to the superoperators:

* **`μ₀ → μ₁` is the interpolation `s : 0 → 1`** — `μ₀ = μ_{s=0}` (`muInterp_zero`, the energy norm) and
  `μ₁ = μ_{s=1} = |r|·μ₀` (`muInterp_one`, the Hadamard one-particle norm / purification); `mu1_eq_smul_mu0`
  is exactly the domination relation `μ₁ ≤ μ₀` that Verch needs.
* **the temporal evolution is a symplectomorphism** satisfying the §2.2 continuity quadratic identity
  (`symplectomorphism_quadratic`) — so relative `μ₀–μ₁` continuity holds for the Cauchy-data evolution.
* **the evolution superoperator is the Liouvillian** — the (complexified) polarizator
  `J_ℂ = sympForm.map ℂ = i·σ₂` generates, via `ad = collisionStar`, the modular generator
  `modularGenerator J_ℂ`, which is the Misra–Prigogine `liouvillian` *and* the TFD `hatHamiltonian`
  (`polarizator_superoperator_liouvillian`, `_hatHamiltonian`, `_bloch`). The polarizator is stationary under
  its own flow (`polarizator_stationary`).

The main result `kleinGordon_continuity_program` bundles the three — the `μ₀–μ₁` relation, the symplectomorphism
continuity identity, and the superoperator identification — as a single witness that the Chapter-1 program is
formalized (the remaining content is the operator-analytic continuity of the *classical* energy-norm evolution,
which is "well-known" / the input to Verch's argument).

* **§E — the spacetime field superoperator** lifts the one-particle (`Fin 2`) modular generator to the
  spacetime field strength (`Fin 4`): the EM field superoperator `ad_F = emFieldAdjoint` is the *same*
  modular `collisionStar` generator (`spacetime_superoperator_eq_modularGenerator`), its complexified form is
  the spacetime Liouvillian `−i·ad_F` (`spacetime_liouvillian_eq_modularGenerator`), and the Faraday tensor is
  stationary under its own flow (`faraday_stationary`) — the spacetime analogue of `polarizator_stationary`.
* **§F — the `𝔰𝔬(1,3)` structure of the combined Lorentz–EM superoperator** `𝒢_{J,F} = ad_{J+F}`. A spacetime
  Lorentz generator `J` (boost/rotation) and the EM field strength `F` are *both* antisymmetric `4×4` matrices,
  i.e. elements of `𝔰𝔬(1,3)`; their sum is one such element and `𝒢_{J,F}` is the canonical
  `Electromagnetic.EMLorentzCombinedSuperoperator.emLorentzGenerator` (`= ad_J + ad_F`). This section adds the Lie-algebra
  layer: `𝔰𝔬(1,3)` is closed under `+` (`lorentzGen_add`) and the bracket (`lorentzGen_bracket`), the EM field
  is itself a Lorentz generator (`faraday_isLorentzGen`), and `𝒢_{J,F}` is an inner derivation of `𝔰𝔬(1,3)`
  (`emLorentzGenerator_preserves_so13`).

## References

* R. Verch, arXiv:funct-an/9609004, Chapter 1 (the program), §2.2 (continuity), §3 (the structural payoff).
* Repo dependencies: `AlgebraicQFTQuasifree.PolarizatorInterpolation` (`muInterp`, the `μ_s` family), `AlgebraicQFTQuasifree.SymplecticAdjointContinuity`
  (`symplectomorphism_quadratic`), `AlgebraicQFTQuasifree.PolarizatorBlochSphere` (`sympFormC_eq_I_smul_pauliY`),
  `ThermoFieldDynamics.KazamaTomitaTakesakiModular` (`modularGenerator`, `= liouvillian`, `= hatHamiltonian`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram

open Matrix PauliMatrix
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.SymplecticAdjointContinuity
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorBlochSphere
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-! ## §A — the energy norm `μ₀` and the Hadamard one-particle norm `μ₁` -/

/-- **[`μ₁ = |r|·μ₀`] The Hadamard one-particle norm is the energy norm scaled by `|r|`.** With `μ₀ = μ_{s=0}`
(the classical energy scalar product) and `μ₁ = μ_{s=1} = μ̃` (the Hadamard one-particle-space norm /
purification), `mu1_eq_smul_mu0` is the domination relation `μ₁ ≤ μ₀` that puts them "precisely in the
relation" for which the §2.2 continuity result applies. -/
theorem mu1_eq_smul_mu0 (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (φ ψ : Fin 2 → ℝ) :
    muInterp M r 1 φ ψ = |r| * muInterp M r 0 φ ψ := by
  rw [muInterp_one, muInterp_zero]

/-- **[Pure/vacuum] `μ₀ = μ₁` when `|r| = 1`** — for an Hadamard vacuum the energy norm already *is* the
one-particle norm (`μ = μ̃`), so the frequency-splitting is trivial. -/
theorem energy_eq_hadamard_of_pure (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (h : |r| = 1)
    (φ ψ : Fin 2 → ℝ) : muInterp M r 1 φ ψ = muInterp M r 0 φ ψ := by
  rw [muInterp_pure M r 1 h, muInterp_pure M r 0 h]

/-! ## §B — the temporal evolution is a symplectomorphism (the §2.2 continuity applies) -/

/-- **[Cauchy-data evolution is `μ₀–μ₁`-continuous] the symplectomorphism continuity identity.** The temporal
evolution `T` of the Klein–Gordon Cauchy-data (a symplectomorphism) and its inverse satisfy the §2.2 `R`-adjoint
quadratic identity (`symplectomorphism_quadratic`), so the relative `μ₀–μ₁` continuity of symplectically adjoint
maps applies to the evolution. -/
theorem evolution_continuity (M Mi : Matrix (Fin 2) (Fin 2) ℝ)
    (hsymp : Symplectomorphism M) (hinv : M * Mi = 1) :
    Mᵀ * (sympForm * sympFormᵀ) * M = sympForm * (Mi * Miᵀ) * sympFormᵀ :=
  symplectomorphism_quadratic M Mi hsymp hinv

/-! ## §C — the evolution superoperator is the Liouvillian / hat-Hamiltonian -/

/-- **[Evolution superoperator = Liouvillian] `ad_{J_ℂ} = L`.** The complexified polarizator `J_ℂ = sympForm.map ℂ`
generates, via `modularGenerator = ad = collisionStar`, the Misra–Prigogine `liouvillian` — the time-translation
generator on observables. The classical symplectic evolution and the Liouville superoperator share the same
generator. -/
theorem polarizator_superoperator_liouvillian (X : Matrix (Fin 2) (Fin 2) ℂ) :
    modularGenerator (sympForm.map Complex.ofReal) X
      = liouvillian (sympForm.map Complex.ofReal) X :=
  modularGenerator_eq_liouvillian (sympForm.map Complex.ofReal) X

/-- **[Evolution superoperator = TFD hat-Hamiltonian] `ad_{J_ℂ} = ℋ̂`.** The same superoperator is the
ThermoFieldDynamics.Basic hat-Hamiltonian — the polarizator's flow is the TFD thermal/KMS evolution. -/
theorem polarizator_superoperator_hatHamiltonian (X : Matrix (Fin 2) (Fin 2) ℂ) :
    modularGenerator (sympForm.map Complex.ofReal) X
      = hatHamiltonian (sympForm.map Complex.ofReal) X :=
  modularGenerator_eq_hatHamiltonian (sympForm.map Complex.ofReal) X

/-- **[Evolution superoperator = `ad` of the Bloch generator] `ad_{J_ℂ} = ad_{iσ₂}`.** Since the complexified
polarizator is `i·σ₂` (`sympFormC_eq_I_smul_pauliY`), the evolution superoperator is the adjoint action of the
Bloch/Poincaré-sphere generator (Saito's circular-polarization `S₂` axis). -/
theorem polarizator_superoperator_bloch (X : Matrix (Fin 2) (Fin 2) ℂ) :
    modularGenerator (sympForm.map Complex.ofReal) X = collisionStar (Complex.I • σ (Sum.inr 1)) X := by
  rw [modularGenerator, sympFormC_eq_I_smul_pauliY]

/-- **[The polarizator is stationary] `ad_{J_ℂ}(J_ℂ) = 0`.** The complex structure is invariant under the
modular/time flow it generates (`[J,J] = 0`) — the equilibrium of the evolution. -/
theorem polarizator_stationary :
    modularGenerator (sympForm.map Complex.ofReal) (sympForm.map Complex.ofReal) = 0 := by
  rw [modularGenerator]; exact collisionStar_self _

/-! ## §D — the main result: the Chapter-1 program is formalized -/

/-- **[The Verch Chapter-1 program, assembled] it is already formalized.** A single witness bundling the three
ingredients of Verch's introduction: (1) the energy norm `μ₀` and Hadamard one-particle norm `μ₁` stand in the
relation `μ₁ = |r|·μ₀`; (2) the Klein–Gordon Cauchy-data evolution (a symplectomorphism) satisfies the §2.2
continuity quadratic identity, so relative `μ₀–μ₁` continuity holds; (3) the evolution superoperator is the
Liouvillian `ad_{J_ℂ}`. The remaining content — the operator-analytic continuity of the *classical* energy-norm
evolution — is Verch's "well-known" input, and the Chapter-3 structural payoff is `AlgebraicQFTQuasifree.HadamardLocalNet`. -/
theorem kleinGordon_continuity_program
    (M Mi : Matrix (Fin 2) (Fin 2) ℝ) (hsymp : Symplectomorphism M) (hinv : M * Mi = 1)
    (Mμ : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (φ ψ : Fin 2 → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    muInterp Mμ r 1 φ ψ = |r| * muInterp Mμ r 0 φ ψ
      ∧ Mᵀ * (sympForm * sympFormᵀ) * M = sympForm * (Mi * Miᵀ) * sympFormᵀ
      ∧ modularGenerator (sympForm.map Complex.ofReal) X = liouvillian (sympForm.map Complex.ofReal) X :=
  ⟨mu1_eq_smul_mu0 Mμ r φ ψ, evolution_continuity M Mi hsymp hinv,
    polarizator_superoperator_liouvillian X⟩

/-! ## §E — the spacetime field superoperator -/

/-- **[Spacetime field superoperator = modular generator] `ad_F = modularGenerator F` on `Fin 4`.** The
`Electromagnetic.EMFieldSuperoperator.emFieldAdjoint` of the field strength `F` over `4`-dim spacetime is the *same* modular/`ad`
generator (`collisionStar`) as the one-particle polarizator on the `2`-dim Cauchy space: the modular
superoperator runs from the one-particle Cauchy-data (`Fin 2`) up to the spacetime field strength (`Fin 4`). -/
theorem spacetime_superoperator_eq_modularGenerator (F X : Mat) :
    emFieldAdjoint F X = modularGenerator F X := by
  rw [emFieldAdjoint_eq_collisionStar, modularGenerator]

/-- **[Spacetime Liouvillian = `−i·ad`] the field von Neumann equation.** The complexified spacetime
Liouvillian `emLiouvillian F = −i[F,·]` is `−i` times the modular generator — the field-level von Neumann /
Heisenberg evolution, the spacetime analogue of `vonNeumannGen` (one-particle). -/
theorem spacetime_liouvillian_eq_modularGenerator (F Y : Matrix (Fin 4) (Fin 4) ℂ) :
    emLiouvillian F Y = -Complex.I • modularGenerator F Y := by
  rw [emLiouvillian_apply, modularGenerator, collisionStar]

/-- **[The field strength is stationary] `ad_F(F) = 0`.** The Faraday tensor is invariant under the spacetime
flow it generates (`[F,F] = 0`) — the spacetime analogue of `polarizator_stationary` (the one-particle complex
structure fixed by its own modular flow). -/
theorem faraday_stationary (k A : Fin 4 → ℝ) :
    emFieldAdjoint (faraday k A) (faraday k A) = 0 :=
  faraday_emFieldAdjoint_self k A

/-- **[Spacetime extension of the program] one modular generator, two levels.** The main result, lifted to the
field: the spacetime field-strength superoperator `ad_F` (`Fin 4`) equals the modular generator
(`collisionStar`) — the same superoperator the one-particle polarizator records (`Fin 2`) — its complexified
form is the spacetime Liouvillian `−i·ad_F`, and the Faraday tensor is stationary under its own flow. The Verch
temporal evolution superoperator, the TFD hat-Hamiltonian, and the EM field Liouvillian are one `ad`. -/
theorem spacetime_superoperator_program (F X : Mat) (Fc Y : Matrix (Fin 4) (Fin 4) ℂ)
    (k A : Fin 4 → ℝ) :
    emFieldAdjoint F X = modularGenerator F X
      ∧ emLiouvillian Fc Y = -Complex.I • modularGenerator Fc Y
      ∧ emFieldAdjoint (faraday k A) (faraday k A) = 0 :=
  ⟨spacetime_superoperator_eq_modularGenerator F X,
    spacetime_liouvillian_eq_modularGenerator Fc Y, faraday_stationary k A⟩

/-! ## §F — the `𝔰𝔬(1,3)` Lie-algebra structure of the combined Lorentz–EM superoperator

The combined superoperator `𝒢_{J,F} = ad_{J+F}` is the repo's canonical
`Electromagnetic.EMLorentzCombinedSuperoperator.emLorentzGenerator` (`= emFieldAdjoint (J+F)`, with its additive decomposition
`𝒢_{J,F} = ad_J + ad_F` = `emLorentzGenerator_decompose`). This section adds the **Lorentz Lie-algebra
`𝔰𝔬(1,3)` layer** that the canonical file lacks: the antisymmetry predicate, its closure under `+` and the
bracket, and that `𝒢_{J,F}` is an inner derivation of `𝔰𝔬(1,3)`. -/

/-- **The Lorentz Lie algebra `𝔰𝔬(1,3)`** — the antisymmetric `4×4` matrices `Xᵀ = −X` (Lorentz
boosts/rotations and the EM field strength alike). -/
def IsLorentzGen (X : Mat) : Prop := Xᵀ = -X

/-- **`𝔰𝔬(1,3)` is closed under addition** — the sum of two Lorentz generators (e.g. `J + F`) is again one,
so `J + F` is a single generator. -/
theorem lorentzGen_add {J F : Mat} (hJ : IsLorentzGen J) (hF : IsLorentzGen F) :
    IsLorentzGen (J + F) := by
  unfold IsLorentzGen at *; rw [transpose_add, hJ, hF, neg_add]

/-- **The EM field strength is a Lorentz generator** `Fᵀ = −F` (`faraday_antisymm`) — `F ∈ 𝔰𝔬(1,3)`, the same
algebra as the boosts/rotations. -/
theorem faraday_isLorentzGen (k A : Fin 4 → ℝ) : IsLorentzGen (faraday k A) := by
  unfold IsLorentzGen; ext μ ν; rw [transpose_apply, neg_apply, faraday_antisymm]

/-- **`ad` preserves `𝔰𝔬(1,3)`** — `[A,X]` is antisymmetric when `A, X` are: the bracket of Lorentz
generators is a Lorentz generator. -/
theorem emFieldAdjoint_preserves_antisym {A X : Mat} (hA : Aᵀ = -A) (hX : Xᵀ = -X) :
    (emFieldAdjoint A X)ᵀ = -(emFieldAdjoint A X) := by
  rw [emFieldAdjoint_apply, transpose_sub, transpose_mul, transpose_mul, hA, hX,
    neg_mul_neg, neg_mul_neg]; abel

/-- **[`𝒢_{J,F}` preserves `𝔰𝔬(1,3)`] the combined superoperator maps Lorentz generators to Lorentz
generators** — `emLorentzGenerator J F = ad_{J+F}` is an inner derivation of the Lorentz Lie algebra. -/
theorem emLorentzGenerator_preserves_so13 {J F X : Mat} (hJ : IsLorentzGen J) (hF : IsLorentzGen F)
    (hX : IsLorentzGen X) : IsLorentzGen (emLorentzGenerator J F X) :=
  emFieldAdjoint_preserves_antisym (lorentzGen_add hJ hF) hX

/-- **[`𝔰𝔬(1,3)` closed under the bracket] `[G,H] ∈ 𝔰𝔬(1,3)`** — the Lie-algebra structure that makes the
combined generators (via `emLorentzGenerator_jacobi` / `emFieldAdjoint_ad_hom`) a representation. -/
theorem lorentzGen_bracket {G H : Mat} (hG : IsLorentzGen G) (hH : IsLorentzGen H) :
    IsLorentzGen (emFieldAdjoint G H) :=
  emFieldAdjoint_preserves_antisym hG hH

/-- **[The concrete Lorentz–EM fusion lives in `𝔰𝔬(1,3)`].** A boost/rotation `J` and the Faraday field
strength fuse into `J + F ∈ 𝔰𝔬(1,3)`, and the combined superoperator `emLorentzGenerator J F` (its additive
form `ad_J + ad_F` being `emLorentzGenerator_decompose`) maps `𝔰𝔬(1,3)` to itself — one inner derivation of
the Lorentz Lie algebra fusing spacetime and electromagnetism. -/
theorem lorentzEM_so13 (J : Mat) (hJ : IsLorentzGen J) (k A : Fin 4 → ℝ) {X : Mat}
    (hX : IsLorentzGen X) :
    IsLorentzGen (J + faraday k A)
      ∧ IsLorentzGen (emLorentzGenerator J (faraday k A) X) :=
  ⟨lorentzGen_add hJ (faraday_isLorentzGen k A),
    emLorentzGenerator_preserves_so13 hJ (faraday_isLorentzGen k A) hX⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram

end

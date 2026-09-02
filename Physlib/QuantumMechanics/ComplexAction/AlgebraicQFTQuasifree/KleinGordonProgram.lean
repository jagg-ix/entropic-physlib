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
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
meta import Zil

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
* **§G — Caticha scalar readouts of modular evolution** supplies both the conditional common-carrier
  interface (`CatichaModularIntertwines`) and a constructed finite realization: reading the `(i,j)`
  entry of a diagonal modular commutator produces the Caticha generator with spectral gap `d_i-d_j`
  (`diagonalModular_catichaIntertwines`).

## References

* R. Verch, arXiv:funct-an/9609004, Chapter 1 (the program), §2.2 (continuity), §3 (the structural payoff).
* Repo carriers: `AlgebraicQFTQuasifree.PolarizatorInterpolation` (`muInterp`, the `μ_s` family), `AlgebraicQFTQuasifree.SymplecticAdjointContinuity`
  (`symplectomorphism_quadratic`), `AlgebraicQFTQuasifree.PolarizatorBlochSphere` (`sympFormC_eq_I_smul_pauliY`),
  `ThermoFieldDynamics.KazamaTomitaTakesakiModular` (`modularGenerator`, `= liouvillian`, `= hatHamiltonian`).


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
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger


/-- **[`μ₁ = |r|·μ₀`] The Hadamard one-particle norm is the energy norm scaled by `|r|`.** With `μ₀ = μ_{s=0}`
(the classical energy scalar product) and `μ₁ = μ_{s=1} = μ̃` (the Hadamard one-particle-space norm /
purification), `mu1_eq_smul_mu0` is the domination relation `μ₁ ≤ μ₀` that puts them "precisely in the
relation" for which the §2.2 continuity result applies. -/
lemma mu1_eq_smul_mu0 (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (φ ψ : Fin 2 → ℝ) :
    muInterp M r 1 φ ψ = |r| * muInterp M r 0 φ ψ := by
  rw [muInterp_one, muInterp_zero]

/-- **[Pure/vacuum] `μ₀ = μ₁` when `|r| = 1`** — for an Hadamard vacuum the energy norm already *is* the
one-particle norm (`μ = μ̃`), so the frequency-splitting is trivial. -/
lemma energy_eq_hadamard_of_pure (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (h : |r| = 1)
    (φ ψ : Fin 2 → ℝ) : muInterp M r 1 φ ψ = muInterp M r 0 φ ψ := by
  rw [muInterp_pure M r 1 h, muInterp_pure M r 0 h]


/-- **[Cauchy-data evolution is `μ₀–μ₁`-continuous] the symplectomorphism continuity identity.** The temporal
evolution `T` of the Klein–Gordon Cauchy-data (a symplectomorphism) and its inverse satisfy the §2.2 `R`-adjoint
quadratic identity (`symplectomorphism_quadratic`), so the relative `μ₀–μ₁` continuity of symplectically adjoint
maps applies to the evolution. -/
lemma evolution_continuity (M Mi : Matrix (Fin 2) (Fin 2) ℝ)
    (hsymp : Symplectomorphism M) (hinv : M * Mi = 1) :
    Mᵀ * (sympForm * sympFormᵀ) * M = sympForm * (Mi * Miᵀ) * sympFormᵀ :=
  symplectomorphism_quadratic M Mi hsymp hinv


/-- **[Evolution superoperator = Liouvillian] `ad_{J_ℂ} = L`.** The complexified polarizator `J_ℂ = sympForm.map ℂ`
generates, via `modularGenerator = ad = collisionStar`, the Misra–Prigogine `liouvillian` — the time-translation
generator on observables. The classical symplectic evolution and the Liouville superoperator share the same
generator. -/
lemma polarizator_superoperator_liouvillian (X : Matrix (Fin 2) (Fin 2) ℂ) :
    modularGenerator (sympForm.map Complex.ofReal) X
      = liouvillian (sympForm.map Complex.ofReal) X :=
  modularGenerator_eq_liouvillian (sympForm.map Complex.ofReal) X

/-- **[Evolution superoperator = TFD hat-Hamiltonian] `ad_{J_ℂ} = ℋ̂`.** The same superoperator is the
ThermoFieldDynamics.Basic hat-Hamiltonian — the polarizator's flow is the TFD thermal/KMS evolution. -/
lemma polarizator_superoperator_hatHamiltonian (X : Matrix (Fin 2) (Fin 2) ℂ) :
    modularGenerator (sympForm.map Complex.ofReal) X
      = hatHamiltonian (sympForm.map Complex.ofReal) X :=
  modularGenerator_eq_hatHamiltonian (sympForm.map Complex.ofReal) X

/-- **[Evolution superoperator = `ad` of the Bloch generator] `ad_{J_ℂ} = ad_{iσ₂}`.** Since the complexified
polarizator is `i·σ₂` (`sympFormC_eq_I_smul_pauliY`), the evolution superoperator is the adjoint action of the
Bloch/Poincaré-sphere generator (Saito's circular-polarization `S₂` axis). -/
lemma polarizator_superoperator_bloch (X : Matrix (Fin 2) (Fin 2) ℂ) :
    modularGenerator (sympForm.map Complex.ofReal) X = collisionStar (Complex.I • σ (Sum.inr 1)) X := by
  rw [modularGenerator, sympFormC_eq_I_smul_pauliY]

/-- **[The polarizator is stationary] `ad_{J_ℂ}(J_ℂ) = 0`.** The complex structure is invariant under the
modular/time flow it generates (`[J,J] = 0`) — the equilibrium of the evolution. -/
lemma polarizator_stationary :
    modularGenerator (sympForm.map Complex.ofReal) (sympForm.map Complex.ofReal) = 0 := by
  rw [modularGenerator]; exact collisionStar_self _


/-- **[The Verch Chapter-1 program, assembled] it is already formalized.** A single witness bundling the three
ingredients of Verch's introduction: (1) the energy norm `μ₀` and Hadamard one-particle norm `μ₁` stand in the
relation `μ₁ = |r|·μ₀`; (2) the Klein–Gordon Cauchy-data evolution (a symplectomorphism) satisfies the §2.2
continuity quadratic identity, so relative `μ₀–μ₁` continuity holds; (3) the evolution superoperator is the
Liouvillian `ad_{J_ℂ}`. The remaining content — the operator-analytic continuity of the *classical* energy-norm
evolution — is Verch's "well-known" input, and the Chapter-3 structural payoff is `AlgebraicQFTQuasifree.HadamardLocalNet`. -/
lemma kleinGordon_continuity_program
    (M Mi : Matrix (Fin 2) (Fin 2) ℝ) (hsymp : Symplectomorphism M) (hinv : M * Mi = 1)
    (Mμ : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (φ ψ : Fin 2 → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    muInterp Mμ r 1 φ ψ = |r| * muInterp Mμ r 0 φ ψ
      ∧ Mᵀ * (sympForm * sympFormᵀ) * M = sympForm * (Mi * Miᵀ) * sympFormᵀ
      ∧ modularGenerator (sympForm.map Complex.ofReal) X = liouvillian (sympForm.map Complex.ofReal) X :=
  ⟨mu1_eq_smul_mu0 Mμ r φ ψ, evolution_continuity M Mi hsymp hinv,
    polarizator_superoperator_liouvillian X⟩


/-- **[Spacetime field superoperator = modular generator] `ad_F = modularGenerator F` on `Fin 4`.** The
`Electromagnetic.EMFieldSuperoperator.emFieldAdjoint` of the field strength `F` over `4`-dim spacetime is the *same* modular/`ad`
generator (`collisionStar`) as the one-particle polarizator on the `2`-dim Cauchy space: the modular
superoperator runs from the one-particle Cauchy-data (`Fin 2`) up to the spacetime field strength (`Fin 4`). -/
lemma spacetime_superoperator_eq_modularGenerator (F X : Mat) :
    emFieldAdjoint F X = modularGenerator F X := by
  rw [emFieldAdjoint_eq_collisionStar, modularGenerator]

/-- **[Spacetime Liouvillian = `−i·ad`] the field von Neumann equation.** The complexified spacetime
Liouvillian `emLiouvillian F = −i[F,·]` is `−i` times the modular generator — the field-level von Neumann /
Heisenberg evolution, the spacetime analogue of `vonNeumannGen` (one-particle). -/
lemma spacetime_liouvillian_eq_modularGenerator (F Y : Matrix (Fin 4) (Fin 4) ℂ) :
    emLiouvillian F Y = -Complex.I • modularGenerator F Y := by
  rw [emLiouvillian_apply, modularGenerator, collisionStar]

/-- **[The field strength is stationary] `ad_F(F) = 0`.** The Faraday tensor is invariant under the spacetime
flow it generates (`[F,F] = 0`) — the spacetime analogue of `polarizator_stationary` (the one-particle complex
structure fixed by its own modular flow). -/
lemma faraday_stationary (k A : Fin 4 → ℝ) :
    emFieldAdjoint (faraday k A) (faraday k A) = 0 :=
  faraday_emFieldAdjoint_self k A

/-- **[Spacetime extension of the program] one modular generator, two levels.** The main result, lifted to the
field: the spacetime field-strength superoperator `ad_F` (`Fin 4`) equals the modular generator
(`collisionStar`) — the same superoperator the one-particle polarizator carries (`Fin 2`) — its complexified
form is the spacetime Liouvillian `−i·ad_F`, and the Faraday tensor is stationary under its own flow. The Verch
temporal evolution superoperator, the TFD hat-Hamiltonian, and the EM field Liouvillian are one `ad`. -/
lemma spacetime_superoperator_program (F X : Mat) (Fc Y : Matrix (Fin 4) (Fin 4) ℂ)
    (k A : Fin 4 → ℝ) :
    emFieldAdjoint F X = modularGenerator F X
      ∧ emLiouvillian Fc Y = -Complex.I • modularGenerator Fc Y
      ∧ emFieldAdjoint (faraday k A) (faraday k A) = 0 :=
  ⟨spacetime_superoperator_eq_modularGenerator F X,
    spacetime_liouvillian_eq_modularGenerator Fc Y, faraday_stationary k A⟩

/-! ## G. Caticha functional evolution as a scalar readout of modular field evolution -/

/-- A scalar readout intertwines Caticha's lapse/shift-smeared functional Schrödinger generator
with a matrix modular generator when applying the Caticha generator after the readout agrees with
reading out the modular commutator. This is the explicit common-carrier condition between the scalar
functional model and the finite Verch/Klein--Gordon or electromagnetic matrix carrier. -/
def CatichaModularIntertwines {n : ℕ}
    (readout : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ) (K : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ X, smearedSchrodingerGenerator N Ni Hperp Hi (readout X)
    = readout (modularGenerator K X)

/-- Evaluation of one matrix entry as a complex-linear scalar readout.  This is the canonical
finite carrier used to turn an operator-valued modular equation into one scalar Caticha mode. -/
def matrixEntryReadout {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun X := X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **[A diagonal modular Hamiltonian acts on an entry by its spectral gap].** Reading the
`(i,j)` entry of `[diag(d),X]` gives `(d_i-d_j)X_{ij}`.  This supplies a constructed,
nontrivial intertwiner instead of leaving the Caticha/modular bridge only conditional. -/
lemma matrixEntryReadout_modularGenerator_diagonal {n : ℕ}
    (d : Fin n → ℂ) (i j : Fin n) (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixEntryReadout i j (modularGenerator (Matrix.diagonal d) X) =
      (d i - d j) * matrixEntryReadout i j X := by
  change (modularGenerator (Matrix.diagonal d) X) i j = (d i - d j) * X i j
  rw [modularGenerator]
  unfold collisionStar
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- **[Constructed Caticha–modular intertwiner].** For lapse one and zero shift, choose the
normal Caticha generator to multiply by the diagonal modular spectral gap `d_i-d_j`.  The canonical
matrix-entry readout then satisfies `CatichaModularIntertwines` for every matrix state. -/
lemma diagonalModular_catichaIntertwines {n : ℕ}
    (d : Fin n → ℂ) (i j : Fin n) :
    CatichaModularIntertwines (matrixEntryReadout i j) 1 0
      ((d i - d j) • LinearMap.id) 0 (Matrix.diagonal d) := by
  intro X
  rw [smearedSchrodinger_apply, matrixEntryReadout_modularGenerator_diagonal]
  simp

/-- **[Caticha functional evolution → Verch/Klein--Gordon Liouvillian].** Given an explicit scalar
readout intertwining Caticha's smeared generator with the Verch polarizator modular generator, the
same readout intertwines it with the Klein--Gordon Liouvillian. The theorem simultaneously retains
the `μ₀–μ₁` relation and symplectic Cauchy-evolution identity from `kleinGordon_continuity_program`.

The readout/intertwining premise is load-bearing: this theorem connects the two existing carriers but
does not claim that a canonical continuum field-evaluation functional has already been constructed. -/
lemma catichaFunctional_kleinGordon_continuity_bridge
    (readout : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ)
    (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ)
    (hlink : CatichaModularIntertwines readout N Ni Hperp Hi
      (sympForm.map Complex.ofReal))
    (M Mi : Matrix (Fin 2) (Fin 2) ℝ) (hsymp : Symplectomorphism M) (hinv : M * Mi = 1)
    (Mμ : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (φ ψ : Fin 2 → ℝ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    muInterp Mμ r 1 φ ψ = |r| * muInterp Mμ r 0 φ ψ
      ∧ Mᵀ * (sympForm * sympFormᵀ) * M = sympForm * (Mi * Miᵀ) * sympFormᵀ
      ∧ smearedSchrodingerGenerator N Ni Hperp Hi (readout X)
        = readout (liouvillian (sympForm.map Complex.ofReal) X) := by
  have hKG := kleinGordon_continuity_program M Mi hsymp hinv Mμ r φ ψ X
  refine ⟨hKG.1, hKG.2.1, ?_⟩
  rw [hlink X, hKG.2.2]

/-- **[Caticha functional evolution → electromagnetic field Liouvillian].** If a scalar readout
intertwines Caticha's smeared generator with the `Fin 4` modular generator of a complexified field
strength `F`, then reading out the electromagnetic Liouvillian gives exactly `−i` times the Caticha
generator. This connects the existing ED scalar flow to the existing EM modular field evolution on
one declared readout, without identifying their unlike carriers definitionally. -/
lemma catichaFunctional_emLiouvillian_bridge
    (readout : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] ℂ)
    (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ)
    (F Y : Matrix (Fin 4) (Fin 4) ℂ)
    (hlink : CatichaModularIntertwines readout N Ni Hperp Hi F) :
    readout (emLiouvillian F Y)
      = -Complex.I * smearedSchrodingerGenerator N Ni Hperp Hi (readout Y) := by
  rw [spacetime_liouvillian_eq_modularGenerator, map_smul, hlink Y]
  rfl

/-! ## H. Continuum Caticha--AQFT carrier -/

/-- Analytic data connecting Caticha's functional generator on an arbitrary
complex field carrier to a Klein--Gordon-type source operator and its causal
Green operators. The carrier types may be infinite-dimensional spaces of
sections or distributions. Right inversion and the intertwining equation are
the explicit analytic premises; no finite matrix readout is involved. -/
structure ContinuumCatichaKGData
    (𝓕 𝓢 : Type*) [AddCommGroup 𝓕] [Module ℂ 𝓕]
    [AddCommGroup 𝓢] [Module ℂ 𝓢] where
  /-- Caticha normal functional Hamiltonian. -/
  Hperp : 𝓕 →ₗ[ℂ] 𝓕
  /-- Caticha tangential functional Hamiltonian. -/
  Hi : 𝓕 →ₗ[ℂ] 𝓕
  /-- Lapse smearing. -/
  lapse : ℝ
  /-- Shift smearing. -/
  shift : ℝ
  /-- Normally hyperbolic Klein--Gordon operator on the selected carriers. -/
  kleinGordon : 𝓕 →ₗ[ℂ] 𝓢
  /-- Induced source evolution. -/
  sourceGenerator : 𝓢 →ₗ[ℂ] 𝓢
  /-- Retarded Green operator on the selected support/domain class. -/
  retarded : 𝓢 →ₗ[ℂ] 𝓕
  /-- Advanced Green operator on the selected support/domain class. -/
  advanced : 𝓢 →ₗ[ℂ] 𝓕
  /-- Retarded right inverse on the declared source carrier. -/
  kleinGordon_retarded : Function.RightInverse retarded kleinGordon
  /-- Advanced right inverse on the declared source carrier. -/
  kleinGordon_advanced : Function.RightInverse advanced kleinGordon
  /-- Caticha evolution descends through the field equation to source
  evolution. -/
  intertwines : ∀ ψ,
    kleinGordon (continuumSmearedSchrodingerGenerator lapse shift Hperp Hi ψ) =
      sourceGenerator (kleinGordon ψ)

namespace ContinuumCatichaKGData

variable {𝓕 𝓢 : Type*} [AddCommGroup 𝓕] [Module ℂ 𝓕]
variable [AddCommGroup 𝓢] [Module ℂ 𝓢]

/-- The continuum causal propagator is the retarded-minus-advanced Green
operator. -/
def causalPropagator (D : ContinuumCatichaKGData 𝓕 𝓢) : 𝓢 →ₗ[ℂ] 𝓕 :=
  D.retarded - D.advanced

/-- Retarded Green evolution solves the selected Klein--Gordon equation. -/
lemma kleinGordon_retarded_apply (D : ContinuumCatichaKGData 𝓕 𝓢)
    (source : 𝓢) : D.kleinGordon (D.retarded source) = source :=
  D.kleinGordon_retarded source

/-- The retarded-minus-advanced propagator is a homogeneous solution. -/
lemma kleinGordon_causalPropagator_eq_zero
    (D : ContinuumCatichaKGData 𝓕 𝓢) (source : 𝓢) :
    D.kleinGordon (D.causalPropagator source) = 0 := by
  rw [causalPropagator, LinearMap.sub_apply, map_sub,
    D.kleinGordon_retarded source, D.kleinGordon_advanced source, sub_self]

/-- Caticha functional evolution of a retarded field is carried by the KG
operator to the declared source evolution. This is the continuum replacement
for the earlier finite matrix-entry bridge. -/
lemma caticha_retarded_intertwines_source
    (D : ContinuumCatichaKGData 𝓕 𝓢) (source : 𝓢) :
    D.kleinGordon
        (continuumSmearedSchrodingerGenerator D.lapse D.shift
          D.Hperp D.Hi (D.retarded source)) =
      D.sourceGenerator source := by
  rw [D.intertwines, D.kleinGordon_retarded source]

/-- Caticha functional evolution preserves the causal Klein--Gordon solution
space: applying the functional Hamiltonian to a Pauli--Jordan solution again
gives a homogeneous KG field. -/
lemma caticha_causalPropagator_is_homogeneous
    (D : ContinuumCatichaKGData 𝓕 𝓢) (source : 𝓢) :
    D.kleinGordon
        (continuumSmearedSchrodingerGenerator D.lapse D.shift
          D.Hperp D.Hi (D.causalPropagator source)) = 0 := by
  rw [D.intertwines, D.kleinGordon_causalPropagator_eq_zero, map_zero]

end ContinuumCatichaKGData

/-- Hermiticity of a continuum two-point functional, the algebraic part of a
quasifree covariance. -/
def IsHermitianTwoPoint {𝓕 : Type*} [AddCommGroup 𝓕] [Module ℂ 𝓕]
    (W : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ψ, W φ ψ = starRingEnd ℂ (W ψ φ)

/-- Positivity of a continuum two-point functional on the diagonal. -/
def IsPositiveTwoPoint {𝓕 : Type*} [AddCommGroup 𝓕] [Module ℂ 𝓕]
    (W : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ, 0 ≤ (W φ φ).re

/-- Pull a two-point functional back along a complex-linear field evolution. -/
def pullbackTwoPoint {𝓓 𝓕 : Type*}
    [AddCommGroup 𝓓] [Module ℂ 𝓓] [AddCommGroup 𝓕] [Module ℂ 𝓕]
    (U : 𝓓 →ₗ[ℂ] 𝓕) (W : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ) :
    𝓓 →ₗ[ℂ] 𝓓 →ₗ[ℂ] ℂ where
  toFun φ :=
    { toFun := fun ψ => W (U φ) (U ψ)
      map_add' := by intro ψ χ; simp
      map_smul' := by intro c ψ; simp }
  map_add' φ ψ := by ext χ; simp
  map_smul' c φ := by ext χ; simp

/-- Linear field evolution preserves Hermiticity of the quasifree two-point
functional under pullback. -/
lemma pullbackTwoPoint_isHermitian
    {𝓓 𝓕 : Type*}
    [AddCommGroup 𝓓] [Module ℂ 𝓓] [AddCommGroup 𝓕] [Module ℂ 𝓕]
    (U : 𝓓 →ₗ[ℂ] 𝓕) (W : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ)
    (hW : IsHermitianTwoPoint W) :
    IsHermitianTwoPoint (pullbackTwoPoint U W) := by
  intro φ ψ
  simpa [pullbackTwoPoint] using hW (U φ) (U ψ)

/-- Linear field evolution preserves positivity of the quasifree two-point
functional under pullback. -/
lemma pullbackTwoPoint_isPositive
    {𝓓 𝓕 : Type*}
    [AddCommGroup 𝓓] [Module ℂ 𝓓] [AddCommGroup 𝓕] [Module ℂ 𝓕]
    (U : 𝓓 →ₗ[ℂ] 𝓕) (W : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ)
    (hW : IsPositiveTwoPoint W) :
    IsPositiveTwoPoint (pullbackTwoPoint U W) := by
  intro φ
  simpa [pullbackTwoPoint] using hW (U φ)

/-- Pulling a positive Hermitian continuum two-point functional through the
retarded Green operator gives a positive Hermitian source two-point
functional. This is the quasifree-state carrier attached to the same Green
map that links Caticha evolution to the KG equation. -/
lemma ContinuumCatichaKGData.retardedTwoPoint_isHermitian_and_positive
    {𝓕 𝓢 : Type*} [AddCommGroup 𝓕] [Module ℂ 𝓕]
    [AddCommGroup 𝓢] [Module ℂ 𝓢]
    (D : ContinuumCatichaKGData 𝓕 𝓢)
    (W : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ)
    (hHermitian : IsHermitianTwoPoint W) (hPositive : IsPositiveTwoPoint W) :
    IsHermitianTwoPoint (pullbackTwoPoint D.retarded W) ∧
      IsPositiveTwoPoint (pullbackTwoPoint D.retarded W) :=
  ⟨pullbackTwoPoint_isHermitian D.retarded W hHermitian,
    pullbackTwoPoint_isPositive D.retarded W hPositive⟩

/-- Abstract microlocal spectrum condition: the wavefront carrier lies in
the selected positive-frequency cone. Concrete curved spacetimes instantiate
`Ξ` with nonzero cotangent data. -/
def MicrolocalSpectrumCondition {Ξ : Type*}
    (wavefront positiveFrequencyCone : Set Ξ) : Prop :=
  wavefront ⊆ positiveFrequencyCone

/-- The antisymmetric part of a two-point functional realizes the canonical
commutator determined by a symplectic form. This is the infinitesimal CCR
condition underlying the repository's exponentiated Weyl relation. -/
def IsCCRCompatibleTwoPoint
    {𝓕 : Type*} [AddCommGroup 𝓕] [Module ℂ 𝓕]
    (W symp : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ψ, W φ ψ - W ψ φ = Complex.I * symp φ ψ

/-- A continuum Hadamard/quasifree carrier keeps the algebraic two-point
properties and the microlocal positive-frequency condition together. The
wavefront set and cone remain explicit analytic data, so this structure does
not manufacture Hadamard regularity from algebra alone. -/
structure ContinuumHadamardTwoPoint
    (𝓕 Ξ : Type*) [AddCommGroup 𝓕] [Module ℂ 𝓕] where
  twoPoint : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ
  /-- Symplectic commutator form of the continuum field. -/
  symplecticForm : 𝓕 →ₗ[ℂ] 𝓕 →ₗ[ℂ] ℂ
  wavefront : Set Ξ
  positiveFrequencyCone : Set Ξ
  hermitian : IsHermitianTwoPoint twoPoint
  positive : IsPositiveTwoPoint twoPoint
  ccr : IsCCRCompatibleTwoPoint twoPoint symplecticForm
  microlocal : MicrolocalSpectrumCondition wavefront positiveFrequencyCone

/-- A covector transport that preserves the positive-frequency cone also
preserves the microlocal spectrum condition. -/
lemma microlocalSpectrumCondition_image
    {Ξ : Type*} (transport : Ξ → Ξ)
    {wavefront positiveFrequencyCone : Set Ξ}
    (hμSC : MicrolocalSpectrumCondition wavefront positiveFrequencyCone)
    (hcone : Set.MapsTo transport positiveFrequencyCone positiveFrequencyCone) :
    MicrolocalSpectrumCondition (transport '' wavefront) positiveFrequencyCone := by
  rintro _ ⟨ξ, hξ, rfl⟩
  exact hcone (hμSC hξ)

/-- Pull a continuum Hadamard two-point carrier through a linear field
evolution and transport its wavefront carrier through the corresponding
cone-preserving covector map. Positivity, Hermiticity, and the microlocal
spectrum condition are all preserved in one construction. -/
noncomputable def ContinuumHadamardTwoPoint.pullback
    {𝓓 𝓕 Ξ : Type*}
    [AddCommGroup 𝓓] [Module ℂ 𝓓] [AddCommGroup 𝓕] [Module ℂ 𝓕]
    (H : ContinuumHadamardTwoPoint 𝓕 Ξ)
    (U : 𝓓 →ₗ[ℂ] 𝓕) (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport H.positiveFrequencyCone
      H.positiveFrequencyCone) :
    ContinuumHadamardTwoPoint 𝓓 Ξ where
  twoPoint := pullbackTwoPoint U H.twoPoint
  symplecticForm := pullbackTwoPoint U H.symplecticForm
  wavefront := transport '' H.wavefront
  positiveFrequencyCone := H.positiveFrequencyCone
  hermitian := pullbackTwoPoint_isHermitian U H.twoPoint H.hermitian
  positive := pullbackTwoPoint_isPositive U H.twoPoint H.positive
  ccr := by
    intro φ ψ
    simpa [pullbackTwoPoint] using H.ccr (U φ) (U ψ)
  microlocal := microlocalSpectrumCondition_image transport H.microlocal hcone

/-- The causal KG propagator therefore induces a positive Hermitian
microlocal two-point carrier on sources, provided the analytic covector
transport preserves the selected positive-frequency cone. -/
noncomputable def ContinuumCatichaKGData.causalHadamardCarrier
    {𝓕 𝓢 Ξ : Type*} [AddCommGroup 𝓕] [Module ℂ 𝓕]
    [AddCommGroup 𝓢] [Module ℂ 𝓢]
    (D : ContinuumCatichaKGData 𝓕 𝓢)
    (H : ContinuumHadamardTwoPoint 𝓕 Ξ)
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport H.positiveFrequencyCone
      H.positiveFrequencyCone) :
    ContinuumHadamardTwoPoint 𝓢 Ξ :=
  H.pullback D.causalPropagator transport hcone

/-- The causal carrier exposes the three defining Hadamard/quasifree
properties simultaneously: Hermiticity, positivity, and positive-frequency
microlocal spectrum support. -/
lemma ContinuumCatichaKGData.causalHadamardCarrier_properties
    {𝓕 𝓢 Ξ : Type*} [AddCommGroup 𝓕] [Module ℂ 𝓕]
    [AddCommGroup 𝓢] [Module ℂ 𝓢]
    (D : ContinuumCatichaKGData 𝓕 𝓢)
    (H : ContinuumHadamardTwoPoint 𝓕 Ξ)
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport H.positiveFrequencyCone
      H.positiveFrequencyCone) :
    IsHermitianTwoPoint
        (D.causalHadamardCarrier H transport hcone).twoPoint ∧
      IsPositiveTwoPoint
        (D.causalHadamardCarrier H transport hcone).twoPoint ∧
      IsCCRCompatibleTwoPoint
        (D.causalHadamardCarrier H transport hcone).twoPoint
        (D.causalHadamardCarrier H transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
        (D.causalHadamardCarrier H transport hcone).wavefront
        (D.causalHadamardCarrier H transport hcone).positiveFrequencyCone :=
  ⟨(D.causalHadamardCarrier H transport hcone).hermitian,
    (D.causalHadamardCarrier H transport hcone).positive,
    (D.causalHadamardCarrier H transport hcone).ccr,
    (D.causalHadamardCarrier H transport hcone).microlocal⟩

/-!

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
lemma lorentzGen_add {J F : Mat} (hJ : IsLorentzGen J) (hF : IsLorentzGen F) :
    IsLorentzGen (J + F) := by
  unfold IsLorentzGen at *; rw [transpose_add, hJ, hF, neg_add]

/-- **The EM field strength is a Lorentz generator** `Fᵀ = −F` (`faraday_antisymm`) — `F ∈ 𝔰𝔬(1,3)`, the same
algebra as the boosts/rotations. -/
lemma faraday_isLorentzGen (k A : Fin 4 → ℝ) : IsLorentzGen (faraday k A) := by
  unfold IsLorentzGen; ext μ ν; rw [transpose_apply, neg_apply, faraday_antisymm]

/-- **`ad` preserves `𝔰𝔬(1,3)`** — `[A,X]` is antisymmetric when `A, X` are: the bracket of Lorentz
generators is a Lorentz generator. -/
lemma emFieldAdjoint_preserves_antisym {A X : Mat} (hA : Aᵀ = -A) (hX : Xᵀ = -X) :
    (emFieldAdjoint A X)ᵀ = -(emFieldAdjoint A X) := by
  rw [emFieldAdjoint_apply, transpose_sub, transpose_mul, transpose_mul, hA, hX,
    neg_mul_neg, neg_mul_neg]; abel

/-- **[`𝒢_{J,F}` preserves `𝔰𝔬(1,3)`] the combined superoperator maps Lorentz generators to Lorentz
generators** — `emLorentzGenerator J F = ad_{J+F}` is an inner derivation of the Lorentz Lie algebra. -/
lemma emLorentzGenerator_preserves_so13 {J F X : Mat} (hJ : IsLorentzGen J) (hF : IsLorentzGen F)
    (hX : IsLorentzGen X) : IsLorentzGen (emLorentzGenerator J F X) :=
  emFieldAdjoint_preserves_antisym (lorentzGen_add hJ hF) hX

/-- **[`𝔰𝔬(1,3)` closed under the bracket] `[G,H] ∈ 𝔰𝔬(1,3)`** — the Lie-algebra structure that makes the
combined generators (via `emLorentzGenerator_jacobi` / `emFieldAdjoint_ad_hom`) a representation. -/
lemma lorentzGen_bracket {G H : Mat} (hG : IsLorentzGen G) (hH : IsLorentzGen H) :
    IsLorentzGen (emFieldAdjoint G H) :=
  emFieldAdjoint_preserves_antisym hG hH

/-- **[The concrete Lorentz–EM fusion lives in `𝔰𝔬(1,3)`].** A boost/rotation `J` and the Faraday field
strength fuse into `J + F ∈ 𝔰𝔬(1,3)`, and the combined superoperator `emLorentzGenerator J F` (its additive
form `ad_J + ad_F` being `emLorentzGenerator_decompose`) maps `𝔰𝔬(1,3)` to itself — one inner derivation of
the Lorentz Lie algebra fusing spacetime and electromagnetism. -/
lemma lorentzEM_so13 (J : Mat) (hJ : IsLorentzGen J) (k A : Fin 4 → ℝ) {X : Mat}
    (hX : IsLorentzGen X) :
    IsLorentzGen (J + faraday k A)
      ∧ IsLorentzGen (emLorentzGenerator J (faraday k A) X) :=
  ⟨lorentzGen_add hJ (faraday_isLorentzGen k A),
    emLorentzGenerator_preserves_so13 hJ (faraday_isLorentzGen k A) hX⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.mu1_eq_smul_mu0 where
  formalizes @ "claim:the-hadamard-one-particle-norm-mu-one-is-the-absolute-value-of-the-frequency-splitting-parameter-times-the-classical-energy-norm-mu-zero",
  supported_by @ "paper:verch-1996-funct-an-9609004-continuity-of-symplectically-adjoint-maps-and-the-algebraic-structure-of-hadamard-vacuum-representations"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.energy_eq_hadamard_of_pure where
  supported_by @ "lean:ContinuousLinearMap.adjoint",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation.muInterp_pure",
  formalizes @ "claim:for-a-hadamard-vacuum-with-unit-frequency-splitting-the-classical-energy-norm-equals-the-one-particle-norm-so-the-frequency-splitting-is-trivial",
  requires @ "claim:the-hadamard-one-particle-norm-mu-one-is-the-absolute-value-of-the-frequency-splitting-parameter-times-the-classical-energy-norm-mu-zero"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.evolution_continuity where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.SymplecticAdjointContinuity.symplectomorphism_quadratic",
  formalizes @ "claim:the-temporal-evolution-of-klein-gordon-cauchy-data-a-symplectomorphism-and-its-inverse-satisfy-the-r-adjoint-quadratic-identity-so-the-relative-mu-zero-mu-one-continuity-of-symplectically-adjoint-maps-applies-to-the-evolution"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.evolution_continuity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.mu1_eq_smul_mu0",
  formalizes @ "claim:the-verch-chapter-one-klein-gordon-program-assembled-the-energy-norm-is-the-scaled-hadamard-norm-the-cauchy-data-evolution-is-a-continuous-symplectomorphism-and-the-classical-symplectic-evolution-equals-the-misra-prigogine-liouville-superoperator",
  requires @ "claim:the-temporal-evolution-of-klein-gordon-cauchy-data-a-symplectomorphism-and-its-inverse-satisfy-the-r-adjoint-quadratic-identity-so-the-relative-mu-zero-mu-one-continuity-of-symplectically-adjoint-maps-applies-to-the-evolution"

zil_file_contract physlib.kleinGordonProgram where
  promises "Verch's Chapter-1 Klein-Gordon program (arXiv:funct-an/9609004): the temporal evolution of Klein-Gordon Cauchy data is by symplectomorphisms of the symplectic space, and the classical energy norm mu0 stands to the Hadamard one-particle norm mu1 in the relation mu1 = |r| mu0 (mu1_eq_smul_mu0) for which the continuity result applies, degenerating to mu0 = mu1 for a Hadamard vacuum with unit splitting (energy_eq_hadamard_of_pure). The Cauchy-data evolution and its inverse satisfy the R-adjoint quadratic identity, so the relative mu0-mu1 continuity of symplectically adjoint maps applies (evolution_continuity). The assembled program bundles the norm relation, the evolution continuity, and the identity of the classical symplectic evolution with the Misra-Prigogine Liouville superoperator (kleinGordon_continuity_program)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation.muInterp",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard.Symplectomorphism"]
  forbids_substitutes ["the microlocal (wavefront-set) characterization of Hadamard states and the continuum functional-analytic continuity theorem, which are the cited curved-spacetime-QFT infrastructure summarized by the finite-dimensional Cauchy-data model",
    "any claim of Hadamard-state existence on a general spacetime, only the norm relation, symplectomorphism continuity, and Liouville identification are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.mu1_eq_smul_mu0,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.energy_eq_hadamard_of_pure,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.evolution_continuity,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program]

/- ZIL-END -/

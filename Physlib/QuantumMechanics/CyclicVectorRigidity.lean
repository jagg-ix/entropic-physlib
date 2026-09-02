/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.UnitaryConjugacy
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
public import Physlib.QuantumMechanics.CyclicAutomatonSpectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
meta import Zil

/-!
# Cyclic-vector rigidity for finite unitary clocks

A finite unitary is not determined by its dimension alone.  The load-bearing
rigidity hypothesis is a cyclic orbit that is an orthonormal Hilbert basis.  If
`U` advances that basis by one `ZMod N` label, the basis representation
conjugates `U` to the standard finite cyclic shift.

This is the standard cyclic-vector argument in an exact Lean interface.  It
proves uniqueness up to unitary equivalence once the orthonormal cyclic basis is
available.  The two previously recorded boundaries are discharged below: the
hypothesis is inhabited (`standardCyclicOrbitBasis` — the standard model's own
computational basis), and the spectral-existence implication is proved
(`cyclicOrbitBasisOfCharacterEigenbasis` — a character eigenbasis with simple
`N`-th-root spectrum yields a cyclic orbit basis by discrete Fourier
transform).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.CyclicVectorRigidity

open Physlib.QuantumMechanics.Conjugacy
open Physlib.QuantumMechanics.CyclicAutomatonSpectrum

/-- A finite unitary together with an orthonormal cyclic orbit basis. -/
structure CyclicOrbitBasis
    (N : ℕ) [NeZero N]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The candidate one-step unitary. -/
  step : H ≃ₗᵢ[ℂ] H
  /-- Complete orthonormal basis indexed by the cycle. -/
  basis : HilbertBasis (ZMod N) ℂ H
  /-- One unitary step advances the cyclic basis label by one. -/
  step_basis : ∀ i,
    step (basis i) = basis (cyclicShift N i)

namespace CyclicOrbitBasis

variable {N : ℕ} [NeZero N]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (P : CyclicOrbitBasis N H)

/-- Coordinates in the cyclic orbit basis. -/
abbrev coordinates : H ≃ₗᵢ[ℂ] lp (fun _ : ZMod N => ℂ) 2 :=
  P.basis.repr

/-- In cyclic coordinates, one application of the candidate unitary is exactly
pullback by the inverse cyclic shift. -/
@[zil_level structural]
theorem coordinates_step_apply (ψ : H) (i : ZMod N) :
    P.coordinates (P.step ψ) i =
      P.coordinates ψ ((cyclicShift N).symm i) := by
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  have hb := P.step_basis ((cyclicShift N).symm i)
  have hb' :
      P.step (P.basis ((cyclicShift N).symm i)) = P.basis i := by
    simpa using hb
  rw [← hb', P.step.inner_map_map]

/-- The basis representation intertwines the candidate unitary with the
standard cyclic shift. -/
theorem coordinates_intertwine (ψ : H) :
    P.coordinates (P.step ψ) =
      cyclicStateStep N (P.coordinates ψ) := by
  ext i
  rw [cyclicStateStep_apply]
  exact P.coordinates_step_apply ψ i

/-- **Cyclic-vector rigidity.** Every finite unitary admitting an orthonormal
`ZMod N` cyclic orbit basis is unitarily conjugate to the standard cyclic shift.
-/
@[zil_level bridge_theorem]
noncomputable def toStandardConjugacy :
    UnitaryConjugacy P.step (cyclicStateStep N) where
  carrier := P.coordinates
  intertwines := P.coordinates_intertwine

/-- The conjugacy transports every finite iterate of the candidate unitary to
the corresponding standard cyclic iterate. -/
theorem coordinates_iterate (n : ℕ) (ψ : H) :
    P.coordinates (unitaryIterate P.step n ψ) =
      unitaryIterate (cyclicStateStep N) n (P.coordinates ψ) :=
  P.toStandardConjugacy.intertwines_iterate n ψ

/-- Two cyclic presentations of the same order are unitarily conjugate through
the standard cyclic model. -/
noncomputable def conjugacyBetween
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (Q : CyclicOrbitBasis N K) :
    UnitaryConjugacy P.step Q.step :=
  P.toStandardConjugacy.trans Q.toStandardConjugacy.symm

/-- The coordinate map carries the cyclic vector to the standard basis origin. -/
theorem coordinates_cyclicVector :
    P.coordinates (P.basis 0) = lp.single 2 (0 : ZMod N) 1 :=
  P.basis.repr_self 0

end CyclicOrbitBasis

/-! ## The GNS realization of the cyclic clock

The cyclic orbit basis is the concrete GNS structure of the vector state at
the cyclic vector: the abstract GNS form `ω(x*y)` of that state is realized as
the Hilbert inner product of the operator orbit, evaluates on step powers to
the orthonormality Kronecker delta, and is identical across any two cyclic
presentations of the same order — rigidity is GNS uniqueness. -/

section GNSVectorState

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant

variable {N : ℕ} [NeZero N]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The vector state of `Ω` on the bounded-operator star algebra:
`ω(x) = ⟪Ω, x Ω⟫`. -/
noncomputable def vectorState (Ω : H) (x : H →L[ℂ] H) : ℂ :=
  inner ℂ Ω (x Ω)

/-- **The GNS form of a vector state is the Hilbert inner product of the
operator orbit**: `gnsForm ω x y = ⟪x Ω, y Ω⟫`.  The abstract GNS sesquilinear
form of `StarAlgebraGNSFormCommutant` is realized concretely on the carrier by
the vector state — with `gns_cyclic` this is the GNS triple of `ω` with cyclic
vector `Ω`. -/
@[zil_level physical_theorem]
theorem gnsForm_vectorState (Ω : H) (x y : H →L[ℂ] H) :
    gnsForm (vectorState Ω) x y = inner ℂ (x Ω) (y Ω) := by
  unfold gnsForm vectorState
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

namespace CyclicOrbitBasis

variable (P : CyclicOrbitBasis N H)

/-- The candidate unitary as a bounded operator in the GNS star algebra. -/
noncomputable def stepCLM : H →L[ℂ] H :=
  P.step.toLinearIsometry.toContinuousLinearMap

@[simp] theorem stepCLM_apply (ψ : H) : P.stepCLM ψ = P.step ψ :=
  rfl

/-- Operator powers of the step are the unitary iterates. -/
theorem stepCLM_pow_apply (k : ℕ) (ψ : H) :
    (P.stepCLM ^ k) ψ = unitaryIterate P.step k ψ := by
  induction k with
  | zero => rw [pow_zero, ContinuousLinearMap.one_apply, unitaryIterate]
  | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, unitaryIterate,
        stepCLM_apply]

/-- **Every basis vector is an operator-power orbit of the cyclic vector**:
`basis k = step^k Ω` — the cyclic vector generates the whole basis through the
algebra of step powers. -/
theorem basis_eq_stepCLM_pow (k : ℕ) :
    P.basis ((k : ℕ) : ZMod N) = (P.stepCLM ^ k) (P.basis 0) := by
  induction k with
  | zero =>
      rw [pow_zero, ContinuousLinearMap.one_apply, Nat.cast_zero]
  | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ZMod N) = ((k : ℕ) : ZMod N) + 1 := by
        push_cast
        ring
      have hstep : P.step (P.basis ((k : ℕ) : ZMod N)) =
          P.basis (((k : ℕ) : ZMod N) + 1) := P.step_basis ((k : ℕ) : ZMod N)
      rw [hcast, ← hstep, ih, pow_succ', ContinuousLinearMap.mul_apply,
        stepCLM_apply]

/-- **The cyclic orbit basis is the GNS basis of the cyclic-vector state**:
the GNS form of `ω = ⟪Ω, ·Ω⟫` on step powers is the orthonormality Kronecker
delta of the cyclic labels. -/
@[zil_level bridge_theorem]
theorem gnsForm_vectorState_stepPow (i j : ℕ) :
    gnsForm (vectorState (P.basis 0)) (P.stepCLM ^ i) (P.stepCLM ^ j) =
      if ((i : ℕ) : ZMod N) = ((j : ℕ) : ZMod N) then 1 else 0 := by
  rw [gnsForm_vectorState, ← P.basis_eq_stepCLM_pow, ← P.basis_eq_stepCLM_pow]
  exact orthonormal_iff_ite.mp P.basis.orthonormal _ _

/-- **Rigidity is GNS uniqueness**: any two cyclic presentations of the same
order carry identical GNS data — the vector-state form on corresponding step
powers agrees exactly — which is why they are unitarily conjugate
(`conjugacyBetween`). -/
@[zil_level bridge_theorem]
theorem gnsForm_presentation_invariant
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (Q : CyclicOrbitBasis N K) (i j : ℕ) :
    gnsForm (vectorState (P.basis 0)) (P.stepCLM ^ i) (P.stepCLM ^ j) =
      gnsForm (vectorState (Q.basis 0)) (Q.stepCLM ^ i) (Q.stepCLM ^ j) := by
  rw [P.gnsForm_vectorState_stepPow, Q.gnsForm_vectorState_stepPow]

end CyclicOrbitBasis

end GNSVectorState

/-! ## The standard witness and the spectral-existence construction

Two discharges of the module's recorded boundaries.  First, the rigidity
hypothesis is inhabited: the standard finite cyclic model itself carries a
cyclic orbit basis (the computational `lp.single` family).  Second, the
separate spectral-existence implication is proved: a unitary with a character
eigenbasis — simple `N`-th-root-of-unity spectrum `χ(k) = e^{2πik/N}` — admits
a cyclic orbit basis, constructed as the discrete Fourier transform of the
eigenbasis. -/

section StandardWitness

open Physlib.QuantumMechanics.KoopmanQuantization

variable (N : ℕ) [NeZero N]

/-- Multiplication by a unit as a label relabeling. -/
def unitMulEquiv (u : (ZMod N)ˣ) : ZMod N ≃ ZMod N where
  toFun i := (u : ZMod N) * i
  invFun i := ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * i
  left_inv i := by
    show ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * i) = i
    rw [← mul_assoc,
      show ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 from u.inv_mul, one_mul]
  right_inv i := by
    show (u : ZMod N) * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * i) = i
    rw [← mul_assoc,
      show (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 from u.mul_inv, one_mul]

/-- **The unit-shifted cyclic step is unitarily conjugate to the standard cyclic
step**: for a unit `u`, advancing labels by `u` is the standard `+1` shift seen
through multiplication by `u⁻¹`.  This is the concrete unitary conjugacy — a
change of state representation intertwining the two evolutions — that stands in
for a stored global rigidity certificate: distinct generator presentations of
the cyclic clock are the same dynamics up to representation. -/
@[zil_level bridge_theorem]
noncomputable def shiftStateStep_conjugate_cyclicStateStep (u : (ZMod N)ˣ) :
    UnitaryConjugacy (shiftStateStep N (u : ZMod N)) (cyclicStateStep N) where
  carrier := koopmanStateStep (unitMulEquiv N u⁻¹)
  intertwines ψ := by
    apply lp.ext
    funext x
    show koopmanStateStep (unitMulEquiv N u⁻¹)
        (shiftStateStep N (u : ZMod N) ψ) x
      = cyclicStateStep N (koopmanStateStep (unitMulEquiv N u⁻¹) ψ) x
    rw [koopmanStateStep_apply,
      show shiftStateStep N (u : ZMod N)
          = koopmanStateStep (labelShift N (u : ZMod N)) from rfl,
      koopmanStateStep_apply, cyclicStateStep_apply, koopmanStateStep_apply]
    have hidx : (labelShift N (u : ZMod N)).symm ((unitMulEquiv N u⁻¹).symm x)
        = (unitMulEquiv N u⁻¹).symm ((cyclicShift N).symm x) := by
      show ((u⁻¹⁻¹ : (ZMod N)ˣ) : ZMod N) * x - (u : ZMod N)
        = ((u⁻¹⁻¹ : (ZMod N)ˣ) : ZMod N) * (x - 1)
      rw [inv_inv]
      ring
    rw [hidx]

/-- The computational basis of the standard state carrier: the orthonormal
`lp.single` family with trivial orthogonal complement. -/
noncomputable def standardHilbertBasis :
    HilbertBasis (ZMod N) ℂ (lp (fun _ : ZMod N => ℂ) 2) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (v := fun i => lp.single 2 i (1 : ℂ))
    (by
      rw [orthonormal_iff_ite]
      intro i j
      rw [lp.inner_single_left]
      simp [lp.single_apply, Pi.single_apply, eq_comm])
    (by
      rw [Submodule.eq_bot_iff]
      intro ψ hψ
      rw [Submodule.mem_orthogonal] at hψ
      apply lp.ext
      funext i
      have h := hψ (lp.single 2 i 1) (Submodule.subset_span ⟨i, rfl⟩)
      rw [lp.inner_single_left] at h
      simpa using h)

@[simp] theorem standardHilbertBasis_apply (i : ZMod N) :
    standardHilbertBasis N i = lp.single 2 i (1 : ℂ) := by
  unfold standardHilbertBasis
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- **The rigidity hypothesis is inhabited**: the standard finite cyclic model
carries a cyclic orbit basis — its own computational basis, advanced by the
Koopman step. -/
@[zil_level physical_theorem]
noncomputable def standardCyclicOrbitBasis :
    CyclicOrbitBasis N (lp (fun _ : ZMod N => ℂ) 2) where
  step := cyclicStateStep N
  basis := standardHilbertBasis N
  step_basis := by
    intro i
    rw [standardHilbertBasis_apply, standardHilbertBasis_apply]
    exact Physlib.QuantumMechanics.KoopmanQuantization.koopman_single
      (cyclicShift N) i 1

end StandardWitness

section SpectralExistence

open Physlib.QuantumMechanics.CyclicAutomatonSpectrum

variable {N : ℕ} [NeZero N]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Character sum with the summation variable on the left of the product. -/
lemma sum_stdAddChar_mul_right (c : ZMod N) :
    ∑ n : ZMod N, ZMod.stdAddChar (n * c) = if c = 0 then (N : ℂ) else 0 := by
  calc ∑ n : ZMod N, ZMod.stdAddChar (n * c)
      = ∑ n : ZMod N, ZMod.stdAddChar (c * n) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [mul_comm]
    _ = _ := sum_stdAddChar_mul N c

/-- The discrete Fourier vectors of a character eigenbasis:
`b j = N^{-1/2} ∑ₖ χ(jk) eₖ`. -/
noncomputable def fourierOrbitVector
    (e : HilbertBasis (ZMod N) ℂ H) (j : ZMod N) : H :=
  (((Real.sqrt N : ℝ) : ℂ))⁻¹ •
    ∑ k : ZMod N, ZMod.stdAddChar (j * k) • e k

lemma sqrtN_ne_zero : (((Real.sqrt N : ℝ) : ℂ)) ≠ 0 := by
  have hN : (0 : ℝ) < (N : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact_mod_cast (Real.sqrt_pos.mpr hN).ne'

lemma conj_invSqrtN_mul :
    (starRingEnd ℂ) ((((Real.sqrt N : ℝ) : ℂ))⁻¹) *
      (((Real.sqrt N : ℝ) : ℂ))⁻¹ = (((N : ℝ) : ℂ))⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg N)]

/-- Inner product of the eigenbasis with a Fourier sum collapses to the
character coefficient. -/
lemma inner_eigen_fourierSum (e : HilbertBasis (ZMod N) ℂ H)
    (j k : ZMod N) :
    inner ℂ (e k) (∑ l : ZMod N, ZMod.stdAddChar (j * l) • e l) =
      ZMod.stdAddChar (j * k) := by
  rw [inner_sum]
  have hterm : ∀ l : ZMod N,
      inner ℂ (e k) (ZMod.stdAddChar (j * l) • e l) =
        if l = k then ZMod.stdAddChar (j * l) else 0 := by
    intro l
    rw [inner_smul_right]
    rcases eq_or_ne l k with h | h
    · subst h
      rw [if_pos rfl, orthonormal_iff_ite.mp e.orthonormal, if_pos rfl,
        mul_one]
    · rw [if_neg h, orthonormal_iff_ite.mp e.orthonormal, if_neg fun hk => h hk.symm,
        mul_zero]
  rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_ite_eq'
    Finset.univ k fun l => ZMod.stdAddChar (j * l)]
  rw [if_pos (Finset.mem_univ k)]

/-- **The Fourier vectors are orthonormal** — the DFT unitarity, by character
orthogonality. -/
@[zil_level physical_theorem]
lemma inner_fourierOrbitVector (e : HilbertBasis (ZMod N) ℂ H)
    (i j : ZMod N) :
    inner ℂ (fourierOrbitVector e i) (fourierOrbitVector e j) =
      if i = j then 1 else 0 := by
  unfold fourierOrbitVector
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, conj_invSqrtN_mul,
    sum_inner]
  have hterm : ∀ k : ZMod N,
      inner ℂ (ZMod.stdAddChar (i * k) • e k)
        (∑ l : ZMod N, ZMod.stdAddChar (j * l) • e l) =
      ZMod.stdAddChar ((j - i) * k) := by
    intro k
    rw [inner_smul_left, inner_eigen_fourierSum, stdAddChar_conj]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, sum_stdAddChar_mul N (j - i)]
  have hNne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rcases eq_or_ne i j with h | h
  · subst h
    rw [if_pos (sub_self i), if_pos rfl]
    push_cast
    field_simp
  · rw [if_neg (sub_ne_zero.mpr (Ne.symm h)), if_neg h, mul_zero]

/-- The unitary advances each Fourier vector by one cyclic label:
`U bⱼ = bⱼ₊₁`. -/
lemma step_fourierOrbitVector (U : H ≃ₗᵢ[ℂ] H)
    (e : HilbertBasis (ZMod N) ℂ H)
    (heig : ∀ k, U (e k) = ZMod.stdAddChar k • e k) (j : ZMod N) :
    U (fourierOrbitVector e j) = fourierOrbitVector e (j + 1) := by
  unfold fourierOrbitVector
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, heig k, smul_smul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The Fourier family has trivial orthogonal complement: a vector orthogonal
to every Fourier vector has vanishing eigenbasis coefficients, by the inverse
transform. -/
lemma fourierOrbitVector_orthogonal_eq_bot
    (e : HilbertBasis (ZMod N) ℂ H) :
    (Submodule.span ℂ (Set.range (fourierOrbitVector e)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro ψ hψ
  rw [Submodule.mem_orthogonal] at hψ
  have hb : ∀ j : ZMod N,
      ∑ k : ZMod N, ZMod.stdAddChar (-(j * k)) * inner ℂ (e k) ψ = 0 := by
    intro j
    have h := hψ (fourierOrbitVector e j)
      (Submodule.subset_span ⟨j, rfl⟩)
    unfold fourierOrbitVector at h
    rw [inner_smul_left, sum_inner] at h
    have hterm : ∀ k : ZMod N,
        inner ℂ (ZMod.stdAddChar (j * k) • e k) ψ =
          ZMod.stdAddChar (-(j * k)) * inner ℂ (e k) ψ := by
      intro k
      rw [inner_smul_left, stdAddChar_conj]
    rw [Finset.sum_congr rfl fun k _ => hterm k] at h
    have hs : (starRingEnd ℂ) ((((Real.sqrt N : ℝ) : ℂ))⁻¹) ≠ 0 := by
      simp [inv_ne_zero (sqrtN_ne_zero (N := N))]
    exact (mul_eq_zero.mp h).resolve_left hs
  have hc : ∀ k₀ : ZMod N, inner ℂ (e k₀) ψ = 0 := by
    intro k₀
    have hz : ∑ j : ZMod N, ZMod.stdAddChar (j * k₀) *
        (∑ k : ZMod N, ZMod.stdAddChar (-(j * k)) * inner ℂ (e k) ψ) = 0 := by
      rw [Finset.sum_congr rfl fun j _ => by rw [hb j, mul_zero]]
      exact Finset.sum_const_zero
    have hswap : ∑ j : ZMod N, ZMod.stdAddChar (j * k₀) *
          (∑ k : ZMod N, ZMod.stdAddChar (-(j * k)) * inner ℂ (e k) ψ)
        = ∑ k : ZMod N,
            (∑ j : ZMod N, ZMod.stdAddChar (j * (k₀ - k))) *
              inner ℂ (e k) ψ := by
      calc ∑ j : ZMod N, ZMod.stdAddChar (j * k₀) *
              (∑ k : ZMod N, ZMod.stdAddChar (-(j * k)) * inner ℂ (e k) ψ)
          = ∑ j : ZMod N, ∑ k : ZMod N,
              ZMod.stdAddChar (j * (k₀ - k)) * inner ℂ (e k) ψ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← mul_assoc, ← AddChar.map_add_eq_mul]
            congr 2
            ring
        _ = _ := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_mul]
    have hcollapse : ∑ k : ZMod N,
        (∑ j : ZMod N, ZMod.stdAddChar (j * (k₀ - k))) * inner ℂ (e k) ψ
        = (N : ℂ) * inner ℂ (e k₀) ψ := by
      have hterm : ∀ k : ZMod N,
          (∑ j : ZMod N, ZMod.stdAddChar (j * (k₀ - k))) * inner ℂ (e k) ψ
            = if k = k₀ then (N : ℂ) * inner ℂ (e k) ψ else 0 := by
        intro k
        rw [sum_stdAddChar_mul_right (k₀ - k)]
        rcases eq_or_ne k k₀ with h | h
        · subst h
          rw [if_pos (sub_self k), if_pos rfl]
        · rw [if_neg (sub_ne_zero.mpr (Ne.symm h)), if_neg h, zero_mul]
      rw [Finset.sum_congr rfl fun k _ => hterm k,
        Finset.sum_ite_eq' Finset.univ k₀
          fun k => (N : ℂ) * inner ℂ (e k) ψ]
      rw [if_pos (Finset.mem_univ k₀)]
    have hNne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have h0 : (N : ℂ) * inner ℂ (e k₀) ψ = 0 := by
      rw [← hcollapse, ← hswap]
      exact hz
    exact (mul_eq_zero.mp h0).resolve_left hNne
  have hrepr : e.repr ψ = 0 := by
    apply lp.ext
    funext k
    rw [e.repr_apply_apply, hc k]
    simp
  exact e.repr.injective (by rw [hrepr, map_zero])

/-- **Spectral existence**: a unitary with a character eigenbasis — simple
`N`-th-root-of-unity spectrum `U eₖ = χ(k) eₖ` — admits a cyclic orbit basis:
the discrete Fourier transform of the eigenbasis.  This discharges the
spectral-existence implication recorded as this module's open boundary; with
`toStandardConjugacy` it makes any such unitary conjugate to the standard
cyclic shift. -/
@[zil_level bridge_theorem]
noncomputable def cyclicOrbitBasisOfCharacterEigenbasis
    (U : H ≃ₗᵢ[ℂ] H) (e : HilbertBasis (ZMod N) ℂ H)
    (heig : ∀ k, U (e k) = ZMod.stdAddChar k • e k) :
    CyclicOrbitBasis N H where
  step := U
  basis := HilbertBasis.mkOfOrthogonalEqBot
    (v := fourierOrbitVector e)
    (orthonormal_iff_ite.mpr (inner_fourierOrbitVector e))
    (fourierOrbitVector_orthogonal_eq_bot e)
  step_basis := by
    intro i
    simp only [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact step_fourierOrbitVector U e heig i

end SpectralExistence

/-! ## The character spectral resolution of a finite-order unitary

From nothing but finite order `U^N = 1`, the character projectors
`Pₖ = N⁻¹ ∑ⱼ χ(−jk) Uʲ` resolve the identity and isolate the `χ(k)`
eigencomponents; eigencomponents of distinct characters are orthogonal for
any isometry; and a cyclic vector with full spectral support and dense
component span produces a cyclic orbit basis through the discrete Fourier
construction — closing the spectral route from finite order to the standard
cyclic shift. -/

section SpectralResolution

open Physlib.QuantumMechanics.CyclicAutomatonSpectrum

variable {N : ℕ} [NeZero N]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A linear isometry equivalence as a bounded operator. -/
noncomputable def isometryCLM (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  U.toLinearIsometry.toContinuousLinearMap

@[simp] theorem isometryCLM_apply (U : H ≃ₗᵢ[ℂ] H) (ψ : H) :
    isometryCLM U ψ = U ψ :=
  rfl

/-- Operator powers of a finite-order unitary depend only on the exponent
modulo the order. -/
theorem isometryCLM_pow_mod (U : H ≃ₗᵢ[ℂ] H)
    (hN : isometryCLM U ^ N = 1) (a : ℕ) :
    isometryCLM U ^ a = isometryCLM U ^ (a % N) := by
  conv_lhs => rw [← Nat.div_add_mod a N]
  rw [pow_add, pow_mul, hN, one_pow, one_mul]

/-- Powers indexed by cyclic labels absorb the label successor. -/
theorem isometryCLM_pow_val_succ (U : H ≃ₗᵢ[ℂ] H)
    (hN : isometryCLM U ^ N = 1) (j : ZMod N) :
    isometryCLM U ^ ((j + 1).val) = isometryCLM U ^ (j.val + 1) := by
  rw [isometryCLM_pow_mod U hN (j.val + 1)]
  congr 1
  have h1 : (1 : ZMod N).val = 1 % N := by
    rw [← Nat.cast_one (R := ZMod N), ZMod.val_natCast]
  rw [ZMod.val_add, h1]
  exact (Nat.mod_modEq 1 N).add_left j.val

/-- The character spectral projector `Pₖ = N⁻¹ ∑ⱼ χ(−jk) Uʲ`. -/
noncomputable def characterProjector (U : H ≃ₗᵢ[ℂ] H) (k : ZMod N) :
    H →L[ℂ] H :=
  ((N : ℂ))⁻¹ •
    ∑ j : ZMod N, ZMod.stdAddChar (-(j * k)) • isometryCLM U ^ (j.val)

/-- **Completeness of the spectral resolution**: `∑ₖ Pₖ = 1`, by character
orthogonality alone. -/
@[zil_level physical_theorem]
theorem sum_characterProjector (U : H ≃ₗᵢ[ℂ] H) :
    ∑ k : ZMod N, characterProjector U k = 1 := by
  unfold characterProjector
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hterm : ∀ j : ZMod N,
      ∑ k : ZMod N, ZMod.stdAddChar (-(j * k)) • (isometryCLM U ^ j.val)
        = if j = 0 then (N : ℂ) • (isometryCLM U ^ j.val) else 0 := by
    intro j
    rw [← Finset.sum_smul]
    have hs : ∑ k : ZMod N, ZMod.stdAddChar (-(j * k))
        = if j = 0 then (N : ℂ) else 0 := by
      calc ∑ k : ZMod N, ZMod.stdAddChar (-(j * k))
          = ∑ k : ZMod N, ZMod.stdAddChar ((-j) * k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [neg_mul]
        _ = if -j = 0 then (N : ℂ) else 0 := sum_stdAddChar_mul N (-j)
        _ = if j = 0 then (N : ℂ) else 0 := by simp only [neg_eq_zero]
    rw [hs]
    split_ifs
    · rfl
    · rw [zero_smul]
  rw [Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_ite_eq' Finset.univ (0 : ZMod N)
      fun j => (N : ℂ) • (isometryCLM U ^ j.val),
    if_pos (Finset.mem_univ _), ZMod.val_zero, pow_zero, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)), one_smul]

set_option maxHeartbeats 1000000 in
/-- **Spectral covariance**: `U ∘ Pₖ = χ(k)·Pₖ` — the projector range is the
`χ(k)` eigencomponent. -/
@[zil_level physical_theorem]
theorem isometryCLM_mul_characterProjector (U : H ≃ₗᵢ[ℂ] H)
    (hN : isometryCLM U ^ N = 1) (k : ZMod N) :
    isometryCLM U * characterProjector U k
      = ZMod.stdAddChar k • characterProjector U k := by
  unfold characterProjector
  rw [mul_smul_comm, smul_comm (ZMod.stdAddChar k) (((N : ℂ))⁻¹)]
  congr 1
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod N))
    (fun j => isometryCLM U *
      (ZMod.stdAddChar (-(j * k)) • isometryCLM U ^ (j.val)))
    (fun j => ZMod.stdAddChar k •
      (ZMod.stdAddChar (-(j * k)) • isometryCLM U ^ (j.val)))
    fun j => ?_
  simp only [Equiv.coe_addRight]
  rw [mul_smul_comm, ← pow_succ', isometryCLM_pow_val_succ U hN j, smul_smul]
  congr 1
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The projector component of any vector is a `χ(k)` eigenvector. -/
theorem characterProjector_eigen (U : H ≃ₗᵢ[ℂ] H)
    (hN : isometryCLM U ^ N = 1) (k : ZMod N) (ψ : H) :
    U (characterProjector U k ψ)
      = ZMod.stdAddChar k • characterProjector U k ψ := by
  have h := congrArg (fun T : H →L[ℂ] H => T ψ)
    (isometryCLM_mul_characterProjector U hN k)
  exact h

/-- The standard character is `1` only at `0` — by the vanishing character
sum. -/
theorem stdAddChar_ne_one {a : ZMod N} (ha : a ≠ 0) :
    ZMod.stdAddChar a ≠ 1 := by
  intro h1
  have hsum := sum_stdAddChar_mul N a
  rw [if_neg ha] at hsum
  have hall : ∑ n : ZMod N, ZMod.stdAddChar (a * n) = (N : ℂ) := by
    rw [Finset.sum_congr rfl fun n _ => by
      rw [mul_comm a n, stdAddChar_mul_eq_pow N a n, h1, one_pow]]
    simp [Finset.card_univ, ZMod.card]
  rw [hall] at hsum
  exact (Nat.cast_ne_zero.mpr (NeZero.ne N)) hsum

omit [CompleteSpace H] in
/-- **Distinct-character eigenvectors of an isometry are orthogonal** — the
elementary unitary orthogonality, no adjoint needed. -/
@[zil_level physical_theorem]
theorem eigenvector_orthogonal (U : H ≃ₗᵢ[ℂ] H) {k l : ZMod N}
    (hkl : k ≠ l) {v w : H}
    (hv : U v = ZMod.stdAddChar k • v)
    (hw : U w = ZMod.stdAddChar l • w) :
    inner ℂ v w = 0 := by
  have h := U.inner_map_map v w
  rw [hv, hw, inner_smul_left, inner_smul_right, stdAddChar_conj] at h
  have hs : ZMod.stdAddChar (l - k) * inner ℂ v w = inner ℂ v w := by
    rw [show (l - k : ZMod N) = -k + l from by ring, AddChar.map_add_eq_mul]
    linear_combination h
  have hne : ZMod.stdAddChar (l - k) ≠ 1 :=
    stdAddChar_ne_one (sub_ne_zero.mpr (Ne.symm hkl))
  have h0 : (ZMod.stdAddChar (l - k) - 1) * inner ℂ v w = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

/-- The normalized spectral component of a reference vector. -/
noncomputable def spectralComponent (U : H ≃ₗᵢ[ℂ] H) (ψ₀ : H) (k : ZMod N) :
    H :=
  ((‖characterProjector U k ψ₀‖ : ℝ) : ℂ)⁻¹ • characterProjector U k ψ₀

/-- Normalization preserves the eigenvector law. -/
theorem spectralComponent_eigen (U : H ≃ₗᵢ[ℂ] H)
    (hN : isometryCLM U ^ N = 1) (ψ₀ : H) (k : ZMod N) :
    U (spectralComponent U ψ₀ k)
      = ZMod.stdAddChar k • spectralComponent U ψ₀ k := by
  unfold spectralComponent
  rw [map_smul, characterProjector_eigen U hN k ψ₀, smul_comm]

/-- **The normalized spectral components are orthonormal**: unit norms from
full spectral support, orthogonality from the distinct-character law. -/
theorem spectralComponent_orthonormal (U : H ≃ₗᵢ[ℂ] H)
    (hN : isometryCLM U ^ N = 1) (ψ₀ : H)
    (hcomp : ∀ k : ZMod N, characterProjector U k ψ₀ ≠ 0) :
    Orthonormal ℂ (spectralComponent (N := N) U ψ₀) := by
  rw [orthonormal_iff_ite]
  intro k l
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl]
    have hr : ((‖characterProjector U k ψ₀‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hcomp k))
    unfold spectralComponent
    rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
      map_inv₀, Complex.conj_ofReal]
    field_simp
    rfl
  · rw [if_neg hkl]
    unfold spectralComponent
    rw [inner_smul_left, inner_smul_right,
      eigenvector_orthogonal U hkl
        (characterProjector_eigen U hN k ψ₀)
        (characterProjector_eigen U hN l ψ₀),
      mul_zero, mul_zero]

/-- Normalization does not change the spectral span. -/
theorem spectralComponent_orthogonal_eq_bot (U : H ≃ₗᵢ[ℂ] H) (ψ₀ : H)
    (hcomp : ∀ k : ZMod N, characterProjector U k ψ₀ ≠ 0)
    (hdense : (Submodule.span ℂ
      (Set.range fun k : ZMod N => characterProjector U k ψ₀))ᗮ = ⊥) :
    (Submodule.span ℂ (Set.range (spectralComponent (N := N) U ψ₀)))ᗮ = ⊥ := by
  have hspan : Submodule.span ℂ (Set.range (spectralComponent (N := N) U ψ₀))
      = Submodule.span ℂ (Set.range fun k : ZMod N => characterProjector U k ψ₀) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hk : characterProjector U k ψ₀
          = ((‖characterProjector U k ψ₀‖ : ℝ) : ℂ) •
              spectralComponent U ψ₀ k := by
        unfold spectralComponent
        rw [smul_smul, mul_inv_cancel₀
          (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hcomp k))),
          one_smul]
      show characterProjector U k ψ₀
        ∈ Submodule.span ℂ (Set.range (spectralComponent (N := N) U ψ₀))
      rw [hk]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  rw [hspan, hdense]

/-- **From finite order to the cyclic shift**: a reference vector with full
spectral support and dense spectral span yields a cyclic orbit basis — the
spectral resolution closes the route from `U^N = 1` to the standard cyclic
model, through the discrete Fourier construction. -/
@[zil_level bridge_theorem]
noncomputable def cyclicOrbitBasisOfSpectralComponents (U : H ≃ₗᵢ[ℂ] H)
    (hN : isometryCLM U ^ N = 1) (ψ₀ : H)
    (hcomp : ∀ k : ZMod N, characterProjector U k ψ₀ ≠ 0)
    (hdense : (Submodule.span ℂ
      (Set.range fun k : ZMod N => characterProjector U k ψ₀))ᗮ = ⊥) :
    CyclicOrbitBasis N H :=
  cyclicOrbitBasisOfCharacterEigenbasis U
    (HilbertBasis.mkOfOrthogonalEqBot
      (v := spectralComponent U ψ₀)
      (spectralComponent_orthonormal U hN ψ₀ hcomp)
      (spectralComponent_orthogonal_eq_bot U ψ₀ hcomp hdense))
    (by
      intro k
      rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
      exact spectralComponent_eigen U hN ψ₀ k)

end SpectralResolution

end Physlib.QuantumMechanics.CyclicVectorRigidity

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.CyclicVectorRigidity

zil attach CyclicOrbitBasis.coordinates_step_apply where
  formalizes @ "claim:a-unitary-that-advances-an-orthonormal-zmod-cyclic-basis-is-the-standard-shift-in-those-coordinates",
  supported_by @ "mathlib:HilbertBasis.repr_apply_apply",
  epistemic_status @ "consistency-identity"

zil attach CyclicOrbitBasis.toStandardConjugacy where
  formalizes @ "claim:an-orthonormal-cyclic-orbit-basis-determines-the-finite-unitary-clock-up-to-unitary-equivalence",
  requires @ "claim:a-unitary-that-advances-an-orthonormal-zmod-cyclic-basis-is-the-standard-shift-in-those-coordinates",
  epistemic_status @ "conditional-model",
  supported_by @ "claim:a-simple-nth-root-character-eigenbasis-yields-a-cyclic-orbit-basis-by-discrete-fourier-transform",
  caveat @ "claim:general-spectral-decompositions-beyond-a-supplied-character-eigenbasis-are-not-constructed-here"

zil attach shiftStateStep_conjugate_cyclicStateStep where
  formalizes @ "claim:a-unit-shifted-cyclic-state-step-is-unitarily-conjugate-to-the-standard-cyclic-step-through-multiplication-by-the-inverse-unit",
  unique_up_to @ "lean:Physlib.QuantumMechanics.Conjugacy.UnitaryConjugacy",
  supported_by @ "lean:Physlib.QuantumMechanics.CyclicAutomatonSpectrum.shiftStateStep"

zil attach gnsForm_vectorState where
  formalizes @ "claim:the-gns-form-of-a-vector-state-is-the-hilbert-inner-product-of-the-operator-orbit",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.gnsForm",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.gns_cyclic",
  epistemic_status @ "consistency-identity"

zil attach CyclicOrbitBasis.gnsForm_vectorState_stepPow where
  formalizes @ "claim:the-cyclic-orbit-basis-is-the-gns-basis-of-the-cyclic-vector-state",
  requires @ "claim:the-gns-form-of-a-vector-state-is-the-hilbert-inner-product-of-the-operator-orbit",
  supported_by @ "mathlib:orthonormal_iff_ite",
  epistemic_status @ "consistency-identity"

zil attach CyclicOrbitBasis.gnsForm_presentation_invariant where
  supported_by @ "lean:CyclicOrbitBasis.gnsForm_vectorState_stepPow",
  formalizes @ "claim:cyclic-rigidity-is-gns-uniqueness-the-vector-state-data-is-presentation-independent",
  requires @ "claim:the-cyclic-orbit-basis-is-the-gns-basis-of-the-cyclic-vector-state",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:full-gns-representation-uniqueness-for-general-states-is-not-claimed-only-the-cyclic-orbit-case"

zil attach standardCyclicOrbitBasis where
  formalizes @ "claim:the-standard-finite-cyclic-model-inhabits-the-cyclic-orbit-basis-hypothesis",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopman_single",
  epistemic_status @ "consistency-identity"

zil attach inner_fourierOrbitVector where
  formalizes @ "claim:the-discrete-fourier-transform-of-a-character-eigenbasis-is-orthonormal",
  supported_by @ "lean:Physlib.QuantumMechanics.CyclicAutomatonSpectrum.sum_stdAddChar_mul",
  epistemic_status @ "consistency-identity"

zil attach cyclicOrbitBasisOfCharacterEigenbasis where
  formalizes @ "claim:a-simple-nth-root-character-eigenbasis-yields-a-cyclic-orbit-basis-by-discrete-fourier-transform",
  requires @ "claim:the-discrete-fourier-transform-of-a-character-eigenbasis-is-orthonormal",
  supported_by @ "lean:Physlib.QuantumMechanics.CyclicAutomatonSpectrum.sum_stdAddChar_mul",
  supported_by @ "mathlib:HilbertBasis.mkOfOrthogonalEqBot",
  epistemic_status @ "consistency-identity"

zil attach sum_characterProjector where
  formalizes @ "claim:the-character-spectral-projectors-of-a-finite-order-unitary-resolve-the-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.CyclicAutomatonSpectrum.sum_stdAddChar_mul"

zil attach isometryCLM_mul_characterProjector where
  formalizes @ "claim:the-finite-order-unitary-acts-on-each-character-spectral-projector-by-its-character-eigenvalue",
  supported_by @ "mathlib:AddChar.map_add_eq_mul"

zil attach eigenvector_orthogonal where
  formalizes @ "claim:distinct-character-eigenvectors-of-an-isometry-are-orthogonal",
  supported_by @ "mathlib:LinearIsometryEquiv.inner_map_map"

zil attach cyclicOrbitBasisOfSpectralComponents where
  formalizes @ "claim:full-spectral-support-with-dense-component-span-turns-a-finite-order-unitary-into-a-cyclic-orbit-basis",
  supported_by @ "lean:Physlib.QuantumMechanics.CyclicVectorRigidity.cyclicOrbitBasisOfCharacterEigenbasis",
  caveat @ "claim:full-spectral-support-and-density-of-the-components-remain-hypotheses-on-the-reference-vector"

zil_file_contract physlib.cyclicVectorRigidity where
  promises "Any finite complex unitary with a complete orthonormal ZMod N orbit basis advanced by one step is unitarily conjugate to the standard finite cyclic shift; any two such presentations of the same order are conjugate through that standard shift. The rigidity hypothesis is inhabited by the standard model's computational basis, and the spectral-existence implication is proved: a character eigenbasis with simple Nth-root spectrum yields a cyclic orbit basis by discrete Fourier transform, and the eigenbasis input is itself derived from finite order alone - the character spectral projectors resolve the identity, carry the character eigenvalue action, are pairwise orthogonal across distinct characters, and turn any reference vector with full spectral support and dense component span into that basis. The rigidity is GNS-absorbed: the cyclic orbit basis is the GNS basis of the vector state at the cyclic vector - the abstract GNS form is realized as the Hilbert inner product of the operator orbit, evaluates to the orthonormality Kronecker delta on step powers, and is identical across presentations."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Conjugacy.UnitaryConjugacy",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.gnsForm",
    "lean:Physlib.QuantumMechanics.CyclicAutomatonSpectrum.cyclicStateStep"
  ]
  forbids_substitutes [
    "claiming that dimension alone determines a finite unitary",
    "claiming that simple spectrum alone supplies the required orthonormal cyclic basis",
    "identifying unitary conjugacy with physical calibration"
  ]
  witnessed_by [
    CyclicOrbitBasis.coordinates_step_apply,
    CyclicOrbitBasis.toStandardConjugacy,
    shiftStateStep_conjugate_cyclicStateStep,
    gnsForm_vectorState,
    CyclicOrbitBasis.gnsForm_vectorState_stepPow,
    CyclicOrbitBasis.gnsForm_presentation_invariant,
    standardCyclicOrbitBasis,
    inner_fourierOrbitVector,
    cyclicOrbitBasisOfCharacterEigenbasis,
    sum_characterProjector,
    isometryCLM_mul_characterProjector,
    eigenvector_orthogonal,
    cyclicOrbitBasisOfSpectralComponents
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.cyclicVectorRigidity

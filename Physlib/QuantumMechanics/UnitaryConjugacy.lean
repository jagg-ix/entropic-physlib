/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Unitary conjugacy of one-step evolutions

When two reversible one-step evolutions live on different state carriers,
sameness cannot mean literal equality of maps whose types differ.  The correct
relation is unitary conjugacy: an isometric equivalence of state spaces that
intertwines the two steps.  The API is stated for arbitrary complex
inner-product spaces, and preserves every finite iterate.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Conjugacy

/-- Unitary conjugacy between two one-step evolutions on possibly different
complex inner-product spaces. -/
structure UnitaryConjugacy
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] H) (V : K ≃ₗᵢ[ℂ] K) where
  /-- Change of state representation. -/
  carrier : H ≃ₗᵢ[ℂ] K
  /-- The representation change intertwines one evolution step. -/
  intertwines : ∀ ψ, carrier (U ψ) = V (carrier ψ)

/-- Recursive iteration of a one-step unitary. -/
def unitaryIterate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) : ℕ → H → H
  | 0, ψ => ψ
  | n + 1, ψ => U (unitaryIterate U n ψ)

namespace UnitaryConjugacy

variable {H K L : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L]
variable {U : H ≃ₗᵢ[ℂ] H} {V : K ≃ₗᵢ[ℂ] K} {W : L ≃ₗᵢ[ℂ] L}

/-- Every unitary is conjugate to itself. -/
def refl (U : H ≃ₗᵢ[ℂ] H) : UnitaryConjugacy U U where
  carrier := LinearIsometryEquiv.refl ℂ _
  intertwines _ := rfl

/-- Unitary conjugacy is symmetric. -/
def symm (C : UnitaryConjugacy U V) : UnitaryConjugacy V U where
  carrier := C.carrier.symm
  intertwines ψ := by
    apply C.carrier.injective
    rw [C.carrier.apply_symm_apply, C.intertwines,
      C.carrier.apply_symm_apply]

/-- Unitary conjugacies compose. -/
def trans (C₁ : UnitaryConjugacy U V)
    (C₂ : UnitaryConjugacy V W) : UnitaryConjugacy U W where
  carrier := C₁.carrier.trans C₂.carrier
  intertwines ψ := by
    change C₂.carrier (C₁.carrier (U ψ)) =
      W (C₂.carrier (C₁.carrier ψ))
    rw [C₁.intertwines, C₂.intertwines]

/-- The intertwining equation can be read as a conjugation identity. -/
theorem conjugation_apply (C : UnitaryConjugacy U V) (ψ : K) :
    C.carrier (U (C.carrier.symm ψ)) = V ψ := by
  rw [C.intertwines, C.carrier.apply_symm_apply]

/-- Intertwining preserves every finite iterate. -/
theorem intertwines_iterate (C : UnitaryConjugacy U V)
    (n : ℕ) (ψ : H) :
    C.carrier (unitaryIterate U n ψ) =
      unitaryIterate V n (C.carrier ψ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [unitaryIterate, C.intertwines, unitaryIterate, ih]

end UnitaryConjugacy

end Physlib.QuantumMechanics.Conjugacy

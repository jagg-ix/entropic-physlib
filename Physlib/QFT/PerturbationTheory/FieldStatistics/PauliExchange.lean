/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PerturbationTheory.FieldStatistics.ExchangeSign
meta import Zil

/-!
# Fermion exchange and Pauli exclusion bridge

The existing perturbative-QFT statistics layer already defines the exchange
character and proves that exchanging two fermionic fields contributes `-1`.
This file packages that theorem with the elementary antisymmetrized two-state
carrier consumed by the OpenWave spin-statistics criterion.

This establishes fermionic exchange algebra and identical-state exclusion. It
does not derive that a particular emergent CAT/EPT excitation must be assigned
fermionic statistics.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange

open FieldStatistic

/-- Antisymmetrization of a two-state amplitude. -/
def antisymmetrize {α V : Type*} [AddCommGroup V]
    (ψ : α → α → V) (a b : α) : V :=
  ψ a b - ψ b a

/-- Swapping the two labels reverses the antisymmetrized amplitude. -/
theorem antisymmetrize_swap {α V : Type*} [AddCommGroup V]
    (ψ : α → α → V) (a b : α) :
    antisymmetrize ψ b a = - antisymmetrize ψ a b := by
  simp only [antisymmetrize]
  exact (neg_sub _ _).symm

/-- Coincident labels vanish after antisymmetrization: the algebraic Pauli
exclusion identity. -/
@[simp] theorem antisymmetrize_self {α V : Type*} [AddCommGroup V]
    (ψ : α → α → V) (a : α) :
    antisymmetrize ψ a a = 0 := by
  simp [antisymmetrize]

/-- Two exchanges restore the original sign. -/
theorem fermionic_exchange_involution :
    FieldStatistic.exchangeSign FieldStatistic.fermionic
      FieldStatistic.fermionic *
    FieldStatistic.exchangeSign FieldStatistic.fermionic
      FieldStatistic.fermionic = 1 := by
  simpa using
    FieldStatistic.exchangeSign_mul_self
      FieldStatistic.fermionic FieldStatistic.fermionic

end Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange

/- ZIL-BEGIN -/

zil attach Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange.antisymmetrize_swap where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-two-state-antisymmetrized-amplitude-changes-sign-under-label-exchange"

zil attach Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange.antisymmetrize_self where
  formalizes @ "claim:the-antisymmetrized-two-state-amplitude-vanishes-for-identical-labels",
  caveat @ "claim:this-is-the-algebraic-pauli-exclusion-identity-not-a-dynamical-derivation-of-fermionic-statistics-for-a-specific-cat-ept-excitation"

zil_file_contract physlib.m9.pauliExchange where
  promises "Fermion-fermion exchange phase minus one, antisymmetry under exchange, identical-state exclusion, and exchange involution, reusing the existing QFT field-statistics character."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:FieldStatistic.fermionic_exchangeSign_fermionic",
    "lean:FieldStatistic.exchangeSign_mul_self"]
  forbids_substitutes ["a dynamical derivation of fermionic statistics for a specific CAT/EPT excitation, this is the algebraic antisymmetry identity",
    "the spin-statistics theorem, which relates spin to the exchange sign and is not proven here"]
  witnessed_by [
    Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange.antisymmetrize_swap,
    Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange.antisymmetrize_self,
    Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange.fermionic_exchange_involution ]

/- ZIL-END -/

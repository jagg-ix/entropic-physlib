/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry
meta import Zil

/-!
# Concrete finite spectral triples, heat action, and APS asymmetry

This module supplies three exact finite-dimensional upgrades to the Connes carrier:

* a concrete faithful scalar spectral triple on `EuclideanSpace C iota`, with the real constant
  Dirac operator `D = mu`; its represented commutators vanish and its spectral action is explicit;
* the heat-kernel spectral action, including its value at zero diffusion time, monotone decay, and
  decomposition over a sum of spectral sectors;
* a finite APS eta invariant.  An equivalence pairing every eigenvalue with its negative forces eta
  to vanish.  This cancellation is combined with the repository's existing configuration-space
  spectral-asymmetry cancellation theorem.

## Honest scope

The scalar triple is a concrete finite spectral triple, not the configuration-space Dirac operator.
Its central algebra action makes the commutator vanish.  The heat trace is a finite eigenvalue sum,
not a proof of a Seeley--DeWitt asymptotic expansion.  `finiteEta` is the finite signed eigenvalue
count; it does not construct the meromorphic APS eta function or prove the APS boundary index
theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry

/-! ## A. A concrete scalar spectral triple -/

/-- A faithful finite spectral triple on a nonempty finite Euclidean mode space.  The coordinate
algebra is `C`, acting by scalar multiplication, and `D = mu` for a real mass/energy scale `mu`. -/
def scalarConstantTriple
    (iota : Type*) [Fintype iota] [DecidableEq iota] [Nonempty iota] (mu : Real) :
    FiniteSpectralTriple Complex (EuclideanSpace Complex iota) iota where
  representation := Algebra.lsmul Complex Complex (EuclideanSpace Complex iota)
  representation_faithful := by
    intro a b hab
    let i : iota := Classical.choice inferInstance
    have hvec := LinearMap.congr_fun hab ((EuclideanSpace.basisFun iota Complex) i)
    have hcoord := congrArg (fun v : EuclideanSpace Complex iota => v i) hvec
    simpa [EuclideanSpace.basisFun_apply] using hcoord
  dirac := (mu : Complex) • LinearMap.id
  eigenbasis := (EuclideanSpace.basisFun iota Complex).toBasis
  eigenvalue := fun _ => mu
  dirac_eigenvector := by simp
  dirac_symmetric := by
    intro x y
    change inner Complex ((mu : Complex) • x) y = inner Complex x ((mu : Complex) • y)
    rw [inner_smul_left, inner_smul_right]
    simp

/-- The scalar coordinate algebra is central, so every represented commutator with the constant
Dirac operator vanishes. -/
theorem scalarConstantTriple_representedCommutator
    (iota : Type*) [Fintype iota] [DecidableEq iota] [Nonempty iota]
    (mu : Real) (a : Complex) :
    (scalarConstantTriple iota mu).representedCommutator a = 0 := by
  ext x i
  simp [FiniteSpectralTriple.representedCommutator, scalarConstantTriple]
  ring

/-- The concrete triple's spectral action is its mode multiplicity times its one eigenvalue
contribution. -/
theorem scalarConstantTriple_spectralAction
    (iota : Type*) [Fintype iota] [DecidableEq iota] [Nonempty iota]
    (mu : Real) (f : Real → Real) (Lambda : Real) :
    (scalarConstantTriple iota mu).spectralAction f Lambda =
      (Fintype.card iota : Real) * f (|mu| / Lambda) := by
  simp [FiniteSpectralTriple.spectralAction, scalarConstantTriple]

/-! ## B. Heat-kernel spectral action and sector decomposition -/

/-- Finite heat-kernel spectral action `Tr exp (-t |D|^2)`. -/
def heatSpectralAction
    {A H iota : Type*} [Semiring A] [Algebra Complex A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Fintype iota]
    (T : FiniteSpectralTriple A H iota) (t : Real) : Real :=
  T.spectralAction (fun x => Real.exp (-t * x ^ 2)) 1

/-- At heat time zero, the heat spectral action is the full eigenbasis multiplicity. -/
theorem heatSpectralAction_zero
    {A H iota : Type*} [Semiring A] [Algebra Complex A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Fintype iota]
    (T : FiniteSpectralTriple A H iota) :
    heatSpectralAction T 0 = Fintype.card iota := by
  simp [heatSpectralAction, FiniteSpectralTriple.spectralAction]

/-- Heat evolution decreases the finite heat spectral action: larger heat time suppresses every
nonzero Dirac eigenmode. -/
theorem heatSpectralAction_antitone
    {A H iota : Type*} [Semiring A] [Algebra Complex A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Fintype iota]
    (T : FiniteSpectralTriple A H iota) {t1 t2 : Real} (ht : t1 ≤ t2) :
    heatSpectralAction T t2 ≤ heatSpectralAction T t1 := by
  apply Finset.sum_le_sum
  intro i _
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ |T.eigenvalue i| ^ 2 := sq_nonneg _
  nlinarith

/-- A spectral action indexed by a disjoint sum is exactly the sum of its two sector actions.  This
is the finite direct-sum trace law without constructing a duplicate block-operator carrier. -/
theorem spectralAction_sum_decomposition
    {A H iota kappa : Type*} [Semiring A] [Algebra Complex A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Fintype iota] [Fintype kappa]
    (T : FiniteSpectralTriple A H (iota ⊕ kappa)) (f : Real → Real) (Lambda : Real) :
    T.spectralAction f Lambda =
      (∑ i : iota, f (|T.eigenvalue (.inl i)| / Lambda)) +
      ∑ j : kappa, f (|T.eigenvalue (.inr j)| / Lambda) := by
  simp [FiniteSpectralTriple.spectralAction, Fintype.sum_sum_type]

/-! ## C. Finite eta invariant and the configuration-space APS bridge -/

/-- Finite APS eta invariant: the signed count of positive and negative real Dirac eigenvalues. -/
def finiteEta
    {A H iota : Type*} [Semiring A] [Algebra Complex A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Fintype iota]
    (T : FiniteSpectralTriple A H iota) : Real :=
  ∑ i, Real.sign (T.eigenvalue i)

/-- A finite Dirac spectrum is paired when an index equivalence maps every eigenvalue to its
negative.  Zero modes are allowed and contribute zero to `finiteEta`. -/
def HasPairedSpectrum
    {A H iota : Type*} [Semiring A] [Algebra Complex A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Fintype iota]
    (T : FiniteSpectralTriple A H iota) : Prop :=
  ∃ tau : iota ≃ iota, ∀ i, T.eigenvalue (tau i) = -T.eigenvalue i

/-- A paired finite Dirac spectrum has vanishing eta invariant. -/
theorem finiteEta_eq_zero_of_paired
    {A H iota : Type*} [Semiring A] [Algebra Complex A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Fintype iota]
    (T : FiniteSpectralTriple A H iota) (h : HasPairedSpectrum T) :
    finiteEta T = 0 := by
  obtain ⟨tau, htau⟩ := h
  have hreindex : (∑ i, Real.sign (T.eigenvalue (tau i))) =
      ∑ i, Real.sign (T.eigenvalue i) := by
    exact tau.sum_comp (fun i => Real.sign (T.eigenvalue i))
  have hneg : (∑ i, Real.sign (T.eigenvalue (tau i))) =
      -(∑ i, Real.sign (T.eigenvalue i)) := by
    calc
      (∑ i, Real.sign (T.eigenvalue (tau i))) =
          ∑ i, -Real.sign (T.eigenvalue i) := by simp_rw [htau, Real.sign_neg]
      _ = -(∑ i, Real.sign (T.eigenvalue i)) := by simp
  unfold finiteEta
  linarith

/-- Common symmetry boundary for the two existing spectral-asymmetry faces: a paired finite Connes
spectrum has zero eta, while a configuration-space matrix conjugate to its negative has zero
`spectralInvariant`. -/
theorem finiteEta_and_configurationSpectralInvariant_vanish
    {A H iota : Type*} [Semiring A] [Algebra Complex A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Fintype iota]
    (T : FiniteSpectralTriple A H iota) (hT : HasPairedSpectrum T)
    {n : Nat} {Dv G G' : Matrix (Fin n) (Fin n) Complex}
    (hG : G' * G = 1) (hconj : G * Dv * G' = -Dv) :
    finiteEta T = 0 ∧ spectralInvariant Dv = 0 :=
  ⟨finiteEta_eq_zero_of_paired T hT,
    spectralAsymmetry_vanishes_of_symmetric hG hconj⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics

end


/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.scalarConstantTriple_spectralAction where
  formalizes @ "claim:a-concrete-faithful-finite-scalar-spectral-triple-has-an-explicit-multiplicity-weighted-spectral-action",
  supported_by @ "lean:EuclideanSpace.basisFun",
  caveat @ "claim:central-scalar-triple-not-the-interacting-configuration-space-dirac-geometry"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.heatSpectralAction_antitone where
  formalizes @ "claim:the-finite-heat-kernel-spectral-action-is-antitone-in-heat-time",
  supported_by @ "lean:Real.exp_le_exp",
  caveat @ "claim:finite-heat-trace-not-a-seeley-dewitt-asymptotic-expansion"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.finiteEta_and_configurationSpectralInvariant_vanish where
  formalizes @ "claim:paired-connes-and-configuration-space-spectra-have-vanishing-finite-eta-and-spectral-invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.spectralAsymmetry_vanishes_of_symmetric",
  caveat @ "claim:finite-eta-cancellation-not-the-meromorphic-APS-eta-function-or-boundary-index-theorem"

zil_file_contract physlib.connesFiniteSpectralDynamics where
  promises "A concrete faithful scalar finite spectral triple has explicit central commutators and spectral action; the finite heat spectral action starts at the mode count, decays monotonically, and splits over sum sectors; paired finite Connes spectra and conjugation-symmetric configuration-space spectra have vanishing asymmetry invariants."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:EuclideanSpace.basisFun",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.spectralAsymmetry_vanishes_of_symmetric"]
  forbids_substitutes ["the scalar triple presented as the interacting configuration-space geometry",
    "a finite heat trace presented as a heat-kernel asymptotic expansion",
    "finite eta cancellation presented as the APS boundary index theorem"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.scalarConstantTriple_representedCommutator,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.scalarConstantTriple_spectralAction,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.heatSpectralAction_zero,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.heatSpectralAction_antitone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.spectralAction_sum_decomposition,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics.finiteEta_and_configurationSpectralInvariant_vanish]

/- ZIL-END -/

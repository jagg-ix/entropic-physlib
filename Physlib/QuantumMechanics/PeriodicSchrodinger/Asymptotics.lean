/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.Continuum

/-!
# Arbitrary-order Bloch spectral asymptotics

Veliev constructs recursive known parts for nonresonant and resonant Bloch
eigenvalues and proves an error estimate at every admissible perturbation
order.  The analytic estimates depend on Sobolev regularity, lattice counting,
and denominator geometry.  This file provides a precise theorem interface for
those estimates and formalizes the recursive algebra of the known parts.

An asymptotic claim records an explicit threshold and error-rate function.  It
does not silently replace a proof of the PDE estimates with an unrestricted
`O` notation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PeriodicSchrodinger

/-- Approximation of a spectral function by a known part above a high-energy
threshold. -/
def IsSpectralApproximation {K : Type*}
    (actual known : K → ℝ)
    (scale : K → ℝ) (threshold : ℝ)
    (errorRate : ℝ → ℝ) : Prop :=
  ∀ k, threshold ≤ scale k →
    dist (actual k) (known k) ≤ errorRate (scale k)

/-- An arbitrary-order family of spectral approximations. -/
structure ArbitraryOrderSpectralExpansion (K : Type*) where
  /-- True spectral value. -/
  actual : K → ℝ
  /-- High-energy scale. -/
  scale : K → ℝ
  /-- Known part at each perturbation order. -/
  knownPart : ℕ → K → ℝ
  /-- Error rate at each order. -/
  errorRate : ℕ → ℝ → ℝ
  /-- High-energy threshold at each order. -/
  threshold : ℕ → ℝ
  /-- Proven approximation statement at every order. -/
  approximates : ∀ order,
    IsSpectralApproximation actual (knownPart order) scale
      (threshold order) (errorRate order)

namespace ArbitraryOrderSpectralExpansion

variable {K : Type*}

/-- Extract the error estimate at one order and one quasimomentum. -/
theorem error_bound
    (A : ArbitraryOrderSpectralExpansion K)
    (order : ℕ) (k : K)
    (hk : A.threshold order ≤ A.scale k) :
    dist (A.actual k) (A.knownPart order k) ≤
      A.errorRate order (A.scale k) :=
  A.approximates order k hk

/-- If a later error rate is no larger and its threshold is satisfied, the
later approximation inherits the sharper bound. -/
theorem error_bound_mono
    (A : ArbitraryOrderSpectralExpansion K)
    {m n : ℕ} (k : K)
    (hk : A.threshold n ≤ A.scale k)
    (hrate : A.errorRate n (A.scale k) ≤
      A.errorRate m (A.scale k)) :
    dist (A.actual k) (A.knownPart n k) ≤
      A.errorRate m (A.scale k) :=
  (A.error_bound n k hk).trans hrate

end ArbitraryOrderSpectralExpansion

/-! ## Recursive known parts -/

/-- Recursive perturbative correction sequence.  `correction n energy k`
represents the order-`n+1` self-energy evaluated at a trial energy. -/
def recursiveCorrection {K : Type*}
    (base : K → ℝ)
    (correction : ℕ → ℝ → K → ℝ) : ℕ → K → ℝ
  | 0 => 0
  | n + 1 => fun k =>
      correction n (base k + recursiveCorrection base correction n k) k

/-- Known spectral part obtained by adding the recursive correction to the
unperturbed energy. -/
def recursiveKnownPart {K : Type*}
    (base : K → ℝ)
    (correction : ℕ → ℝ → K → ℝ)
    (order : ℕ) (k : K) : ℝ :=
  base k + recursiveCorrection base correction order k

@[simp] theorem recursiveCorrection_zero {K : Type*}
    (base : K → ℝ)
    (correction : ℕ → ℝ → K → ℝ) :
    recursiveCorrection base correction 0 = 0 :=
  rfl

@[simp] theorem recursiveKnownPart_zero {K : Type*}
    (base : K → ℝ)
    (correction : ℕ → ℝ → K → ℝ) (k : K) :
    recursiveKnownPart base correction 0 k = base k := by
  simp [recursiveKnownPart]

/-- Recursive correction equation corresponding to
`F_s = A_s(base + F_{s-1})`. -/
theorem recursiveCorrection_succ {K : Type*}
    (base : K → ℝ)
    (correction : ℕ → ℝ → K → ℝ)
    (n : ℕ) (k : K) :
    recursiveCorrection base correction (n + 1) k =
      correction n (recursiveKnownPart base correction n k) k :=
  rfl

/-- Recursive equation for the known spectral part. -/
theorem recursiveKnownPart_succ {K : Type*}
    (base : K → ℝ)
    (correction : ℕ → ℝ → K → ℝ)
    (n : ℕ) (k : K) :
    recursiveKnownPart base correction (n + 1) k =
      base k + correction n
        (recursiveKnownPart base correction n k) k :=
  rfl

/-- Nonresonant known parts use the free Bloch energy as base. -/
def nonresonantKnownPart {d : ℕ}
    (correction : ℕ → ℝ → Momentum d → ℝ)
    (order : ℕ) (k : Momentum d) : ℝ :=
  recursiveKnownPart freeEnergy correction order k

/-- Resonant known parts use a directional or finite-matrix reference
eigenvalue as base. -/
def resonantKnownPart {K : Type*}
    (referenceEnergy : K → ℝ)
    (correction : ℕ → ℝ → K → ℝ)
    (order : ℕ) (k : K) : ℝ :=
  recursiveKnownPart referenceEnergy correction order k

@[simp] theorem nonresonantKnownPart_zero {d : ℕ}
    (correction : ℕ → ℝ → Momentum d → ℝ)
    (k : Momentum d) :
    nonresonantKnownPart correction 0 k = freeEnergy k := by
  simp [nonresonantKnownPart]

@[simp] theorem resonantKnownPart_zero {K : Type*}
    (referenceEnergy : K → ℝ)
    (correction : ℕ → ℝ → K → ℝ)
    (k : K) :
    resonantKnownPart referenceEnergy correction 0 k =
      referenceEnergy k := by
  simp [resonantKnownPart]

/-- A power-law error profile with explicit exponent. -/
def powerErrorRate (constant exponent : ℝ) (ρ : ℝ) : ℝ :=
  constant * ρ ^ (-exponent)

/-- Positivity of a power-law error profile at positive scale and
nonnegative constant. -/
theorem powerErrorRate_nonneg
    {constant exponent ρ : ℝ}
    (hconstant : 0 ≤ constant) (hρ : 0 ≤ ρ) :
    0 ≤ powerErrorRate constant exponent ρ := by
  unfold powerErrorRate
  positivity

/-- Interface for the paper's statement that every sufficiently high Bloch
eigenvalue is described either by a nonresonant expansion or by a finite
resonance-matrix expansion. -/
def CoveredByNonresonantOrResonant
    {K A B : Type*}
    (classify : K → Sum A B)
    (actual : K → ℝ)
    (knownNonresonant : A → ℝ)
    (knownResonant : B → ℝ)
    (error : K → ℝ) : Prop :=
  ∀ k,
    match classify k with
    | Sum.inl a => dist (actual k) (knownNonresonant a) ≤ error k
    | Sum.inr b => dist (actual k) (knownResonant b) ≤ error k

end Physlib.QuantumMechanics.PeriodicSchrodinger

end

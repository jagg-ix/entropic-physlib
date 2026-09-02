/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.ComputationLandauer
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
public import Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality
public import Physlib.QuantumMechanics.KoopmanQuantization
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity
public import Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# 't Hooft's deterministic cellular automaton and its bosonic-duality skeleton

This module formalizes the exact discrete constructions of G. 't Hooft, *Duality between a
deterministic cellular automaton and a bosonic quantum field theory in 1+1 dimensions*,
arXiv:1205.4107 (Found. Phys. 43 (2013) 597), and threads them through the library's existing
computation-thermodynamics and algebraic-QFT layers.

* **Section A - the automaton (Eqs. 5.1-5.3).** Integer field `Q(x,t)` on sites, integer momenta
  `P(x, t+1/2)` on timelike links; the update `P' = P + (discrete Laplacian of Q)`, `Q' = Q + P'`.
  The step is a genuine bijection (`stepEquiv`) - the automaton is exactly reversible.
* **Section B - integer left/right movers (Eqs. 5.6-5.7) and light-speed transport (Eq. 4.13).**
  `moverLeft` and `moverRight` are conserved data streams: one step moves them exactly one site,
  `moverLeft (step s) x = moverLeft s (x+1)`, and `n` steps move them `n` sites - quantised units
  of information moving left and right at the speed of light.
* **Section C - the discrete wave equation.** Combining the two update laws gives the exact
  discrete d'Alembert equation `Q(t+1) - 2Q(t) + Q(t-1) = Q(x+1) - 2Q(x) + Q(x-1)`.
* **Section D - reversible computation (leveraging `Thermodynamics.ComputationLandauer`).** The
  spatially homogeneous sector evolves by the shear `(Q,P) -> (Q+P, P)`; encoded on the naturals
  it is an injective driver, so it sits on the *reversible* side of the Carneiro-basis split
  (injective `succ`/`pair` vs non-injective `left`/`right`/`const`) of `ComputationLandauer`
  (Mathlib `Computability.PartrecCode`, Carneiro ITP 2019): its `computationKernel` preserves the
  KL divergence exactly and produces zero entropy - the automaton step costs nothing by Landauer,
  in exact contrast with the erasure step `erasureStep_tauEnt_nonneg`.
* **Section E - the sawtooth Hamiltonian coefficient (Eqs. 5.4-5.5).** The Fourier coefficient of
  the sawtooth defining 't Hooft's periodic Hamiltonian
  `H = sum_n ((-1)^(n-1) i / 2 pi n)(U(n) - U(-n))`:
  `2 int_{-1/2}^{1/2} x sin(2 pi n x) dx = 2 (-1)^(n-1)/(2 pi n)`, by the fundamental theorem of
  calculus.
* **Section F - the integer Weyl commutation (Eqs. 6.2-6.3).** In the library's Weyl CCR system,
  two Weyl operators whose symplectic pairing is `2 pi` times an integer commute exactly - the
  algebraic reason the automaton's integer raising operators all commute, which anchors 't Hooft's
  identification of the automaton's fractional-part operators with the field theory's
  exponentiated fields.
* **Section G - the mover commutator kernel (Eqs. 4.4-4.5).** The lattice mover commutator
  `[a^L(x), a^L(y)] = plus-or-minus i/2 pi` for `y = x plus-or-minus 1` defines a nearest-neighbour Pauli-Jordan
  kernel; it is antisymmetric, invariant under the lattice shift that implements the time
  evolution, and any symmetric Hadamard part with non-negative diagonal completes it to a
  Sorkin-Johnston-type state (`wightman_isSJState`) - the algebraic-QFT face of the duality.
* **Section F' and the von Neumann commutant layer.** The integer Weyl family lies in its own
  commutant and its bicommutant - its von Neumann algebra in the algebraic sense of
  `StarAlgebraGNSFormCommutant` - is all centre (`automaton_beable_bicommutant_abelian`): the
  beable algebra is abelian, the maximally non-factor case. The mover kernel vanishes beyond
  nearest neighbours (`moverCommutatorKernel_eq_zero_of_far`), so every operator realization
  with that c-number commutator is Einstein-causal at distance two or more
  (`mover_cnumber_commutation_of_far`), while on the lightlike adjacency no normalized state is
  weakly local (`mover_adjacent_no_weak_locality`, through the c-number upgrade of
  `HadamardLocalNet`).
* **Section H - the automaton as an instance of cellular-automaton locality.** The update packs
  to a radius-one local rule of `CellularAutomatonLocality`, so its `n`-step evolution has an
  exact unit-speed causal cone and cone determinism (`automaton_causal_cone`).
* **Section I - the quantized automaton.** The homogeneous shear is a lattice bijection whose
  Koopman lift (from `KoopmanQuantization`) is unitary and shadows the classical machine; its
  Page-Wootters timeless constraint has physical states exactly the zero-momentum amplitudes
  (`automaton_physical_iff_zeroMomentum`) - moving configurations admit no normalizable
  stationary amplitude - and, with the qubit-trace Landauer model, the machine upgrades to a
  measurement-free thermodynamically costless quantum Turing machine
  (`automaton_quantum_turing_machine`).
* **Section J - the fermionic edge layer (Eqs. 6.21-6.22, 8.1).** The alternating edge sign
  `(-1)^(P+Q)` over a mover pair is unimodular, hence outside the amplitude space
  (`edgeSign_not_memℓp` - the infinite-energy exclusion); every ontological basis state, in
  particular the vacuum, violates the edge constraint
  (`ontological_basis_violates_edge_constraint`, `vacuum_violates_edge_constraint` -
  't Hooft's Eq. 8.1 obstruction forcing "either highly excited automata or add fermions");
  multiplication by the edge sign is the involutive isometric fermion-parity grading whose
  eigenvectors are exactly the basis states (`parityMul_involution`, `parityMul_single` -
  the lattice face of the CAR `fermionParity`); and the edge-constraint family is
  evolution-covariant by the mover transport (`edge_pair_step_covariant`).

**Honest boundary.** This is the exact discrete skeleton of the duality: the automaton, its
movers, its reversibility/computability, and the kernel-level CCR structure. It does **not**
construct the full Hilbert-space unitary equivalence of 't Hooft's section 6: the fractional-part
operators `eta`, the phase function `phi(eta, xi)` with its elliptic-theta representation
(Eq. 6.14) and vortex singularities, and the QFT-side Hamiltonian kernels (Eqs. 4.9-4.18) are not
formalized. Of the edge states, the parity/exclusion layer of Section J is formalized - the
infinite-energy exclusion, the basis-state violation of the constraint, the parity grading, and
the evolution covariance - but not the supersymmetric boson-plus-fermion completion that lifts
the constraint, which 't Hooft defers to a subsequent publication. No claim is made that quantum
field theory *is* a deterministic automaton - only the exact identities above.
-/

set_option autoImplicit false

open Real
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality

open Physlib.Thermodynamics.ComputationLandauer
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality
open Physlib.QuantumMechanics.KoopmanQuantization
open Physlib.QuantumMechanics.RelationalTime
open Physlib.Thermodynamics.Landauer

/-! ## Section A - the cellular automaton (Eqs. 5.1-5.3) -/

/-- **The automaton state**: the integer field `Q(x)` on the sites of the spatial lattice and the
integer momenta `P(x)` on the timelike links just below the current time slice ('t Hooft
Eq. 5.1). -/
@[ext] structure AutomatonState where
  /-- The integer field `Q(x, t)` on the lattice sites. -/
  Q : ℤ → ℤ
  /-- The integer momentum `P(x, t - 1/2)` on the timelike link below the slice. -/
  P : ℤ → ℤ

/-- **'t Hooft Eq. (5.3)**: the updated link momentum
`P(x, t+1/2) = P(x, t-1/2) + Q(x-1, t) - 2Q(x, t) + Q(x+1, t)` - the discrete spatial Laplacian
drives the momentum. -/
def stepMomentum (s : AutomatonState) (x : ℤ) : ℤ :=
  s.P x + s.Q (x - 1) - 2 * s.Q x + s.Q (x + 1)

/-- **'t Hooft Eq. (5.2)**: one automaton time step - the field moves by the updated momentum,
`Q(x, t+1) = Q(x, t) + P(x, t+1/2)`. -/
def step (s : AutomatonState) : AutomatonState where
  Q := fun x => s.Q x + stepMomentum s x
  P := stepMomentum s

/-- The explicit inverse step: recover `Q(x,t)` as `Q' - P'` and undo the Laplacian kick. -/
def stepInv (s : AutomatonState) : AutomatonState where
  Q := fun x => s.Q x - s.P x
  P := fun x => s.P x -
    ((s.Q (x - 1) - s.P (x - 1)) - 2 * (s.Q x - s.P x) + (s.Q (x + 1) - s.P (x + 1)))

/-- **The automaton is exactly reversible**: the update (5.2)-(5.3) is a bijection of the state
space - the permutation of basis states whose matrix 't Hooft observes "only contains ones and
zeros". -/
def stepEquiv : AutomatonState ≃ AutomatonState where
  toFun := step
  invFun := stepInv
  left_inv s := by
    ext x <;> simp [step, stepInv, stepMomentum] <;> ring
  right_inv s := by
    ext x <;> simp [step, stepInv, stepMomentum] <;> ring

/-! ## Section B - the integer movers and light-speed transport (Eqs. 5.6-5.7, 4.13) -/

/-- **'t Hooft Eq. (5.6)**: the integer left mover
`A^L(x+t) = P(x, t+1/2) + Q(x, t) - Q(x-1, t)`. -/
def moverLeft (s : AutomatonState) (x : ℤ) : ℤ :=
  stepMomentum s x + s.Q x - s.Q (x - 1)

/-- **'t Hooft Eq. (5.7)**: the integer right mover
`A^R(x-t) = P(x, t+1/2) + Q(x, t) - Q(x+1, t)`. -/
def moverRight (s : AutomatonState) (x : ℤ) : ℤ :=
  stepMomentum s x + s.Q x - s.Q (x + 1)

/-- **[Left movers move left at the speed of light]** one automaton step transports the left-mover
stream exactly one site: `A^L` after the step at `x` is `A^L` before the step at `x+1` (the lattice
Eq. 4.13). -/
@[zil_level physical_theorem]
theorem moverLeft_step (s : AutomatonState) (x : ℤ) :
    moverLeft (step s) x = moverLeft s (x + 1) := by
  simp only [moverLeft, step, stepMomentum, Int.add_sub_cancel, Int.sub_add_cancel]
  ring

/-- **[Right movers move right at the speed of light]** one automaton step transports the
right-mover stream exactly one site the other way. -/
@[zil_level physical_theorem]
theorem moverRight_step (s : AutomatonState) (x : ℤ) :
    moverRight (step s) x = moverRight s (x - 1) := by
  simp only [moverRight, step, stepMomentum, Int.add_sub_cancel, Int.sub_add_cancel]
  ring

/-- **[Quantised information transport]** `n` automaton steps move the left-mover stream exactly
`n` sites: the movers are conserved integer data streams travelling at the speed of light - the
"quantised units of information" of the duality. -/
@[zil_level physical_theorem]
theorem moverLeft_iterate (s : AutomatonState) (n : ℕ) (x : ℤ) :
    moverLeft (step^[n] s) x = moverLeft s (x + n) := by
  induction n generalizing s with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (step s), moverLeft_step]
    congr 1
    push_cast
    ring

/-- **[The discrete d'Alembert equation]** two consecutive updates satisfy the exact discrete wave
equation `Q(x, t+1) - 2Q(x, t) + Q(x, t-1) = Q(x+1, t) - 2Q(x, t) + Q(x-1, t)` - the automaton is
the integer-valued discrete free wave. -/
@[zil_level physical_theorem]
theorem discrete_wave_equation (s : AutomatonState) (x : ℤ) :
    (step (step s)).Q x - 2 * (step s).Q x + s.Q x
      = (step s).Q (x + 1) - 2 * (step s).Q x + (step s).Q (x - 1) := by
  simp only [step, stepMomentum, Int.add_sub_cancel, Int.sub_add_cancel]
  ring

/-! ## Section D - the homogeneous sector as a reversible computation

The spatially homogeneous states (constant `Q`, constant `P`) are preserved by the update: the
discrete Laplacian vanishes and the step is the shear `(Q, P) -> (Q + P, P)`. Encoded on the
naturals, this is an injective total driver, so the library's `computationKernel` machinery
(`Thermodynamics.ComputationLandauer`, built on Mathlib's `Computability.PartrecCode`) applies:
the automaton's deterministic channel preserves KL divergence exactly and produces zero entropy -
the Landauer-free reversible side of the Carneiro-basis split. -/

/-- The spatially homogeneous automaton state `Q(x) = q`, `P(x) = p`. -/
def homogeneousState (q p : ℤ) : AutomatonState where
  Q := fun _ => q
  P := fun _ => p

/-- **[The update preserves homogeneity]** on constant data the Laplacian kick vanishes and the
step is the exact shear `(q, p) -> (q + p, p)`. -/
theorem step_homogeneousState (q p : ℤ) :
    step (homogeneousState q p) = homogeneousState (q + p) p := by
  ext x <;> simp [step, stepMomentum, homogeneousState] <;> ring

/-- The homogeneous-sector shear on the integer pair. -/
def homogeneousStep : ℤ × ℤ → ℤ × ℤ := fun s => (s.1 + s.2, s.2)

theorem homogeneousStep_injective : Function.Injective homogeneousStep := by
  intro a b h
  obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ h
  exact Prod.ext (by omega) h2

/-- The homogeneous automaton step as a total driver on the naturals, through the canonical
denumerable encoding of the integer pair. -/
def homogeneousNatStep : ℕ → ℕ := fun n =>
  Denumerable.eqv (ℤ × ℤ) (homogeneousStep ((Denumerable.eqv (ℤ × ℤ)).symm n))

/-- **[The automaton driver is injective]** - the homogeneous automaton step sits on the
*reversible* side of the Carneiro-basis split of `ComputationLandauer` (with the injective
`succ`/`pair` primitives, against the non-injective `left`/`right`/`const`). -/
@[zil_level bridge_theorem]
theorem homogeneousNatStep_injective : Function.Injective homogeneousNatStep :=
  (Denumerable.eqv (ℤ × ℤ)).injective.comp
    (homogeneousStep_injective.comp (Denumerable.eqv (ℤ × ℤ)).symm.injective)

/-- **[The automaton channel preserves KL divergence]** the deterministic Markov channel of the
automaton step keeps the Kullback-Leibler divergence of any two priors exactly - Bennett's
history-keeping reversibility, instantiated on 't Hooft's automaton through
`ComputationLandauer.computation_keeps_kl`. -/
@[zil_level physical_theorem]
theorem automaton_channel_keeps_kl (μ ν : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.compProd (computationKernel homogeneousNatStep))
        (ν.compProd (computationKernel homogeneousNatStep)) = klDiv μ ν :=
  computation_keeps_kl homogeneousNatStep μ ν

/-- **[Zero entropy production]** the automaton's deterministic channel produces exactly zero
entropy: the reversible cellular automaton evolves at zero Landauer cost, in exact contrast with
the erasure step (`erasureStep_tauEnt_nonneg`), whose cost is non-negative. -/
@[zil_level physical_theorem]
theorem automaton_entropy_production_zero
    (μ ν : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (klDiv (μ.compProd (computationKernel homogeneousNatStep))
        (ν.compProd (computationKernel homogeneousNatStep))).toReal
      - (klDiv μ ν).toReal = 0 :=
  reversible_entropy_production_zero homogeneousNatStep μ ν

/-! ## Section E - the sawtooth Hamiltonian coefficient (Eqs. 5.4-5.5) -/

/-- The closed-form antiderivative of `x sin(cx)`: `sin(cx)/c^2 - x cos(cx)/c`. -/
noncomputable def sawtoothAntideriv (c x : ℝ) : ℝ :=
  Real.sin (c * x) / c ^ 2 - x * Real.cos (c * x) / c

theorem sawtoothAntideriv_hasDerivAt (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (sawtoothAntideriv c) (x * Real.sin (c * x)) x := by
  have hcx : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (c * y)) (Real.cos (c * x) * c) x :=
    (Real.hasDerivAt_sin (c * x)).comp x hcx
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (c * y)) (-Real.sin (c * x) * c) x :=
    (Real.hasDerivAt_cos (c * x)).comp x hcx
  have hxcos : HasDerivAt (fun y : ℝ => y * Real.cos (c * y))
      (1 * Real.cos (c * x) + x * (-Real.sin (c * x) * c)) x :=
    (hasDerivAt_id x).mul hcos
  have h := (hsin.div_const (c ^ 2)).sub (hxcos.div_const c)
  convert h using 1 <;>
    first
      | rfl
      | (field_simp; ring)

/-- **['t Hooft Eq. (5.5)]** the sawtooth Fourier coefficient defining the periodic automaton
Hamiltonian (5.4): `2 int_{-1/2}^{1/2} x sin(2 pi n x) dx = 2 (-1)^(n-1)/(2 pi n)` - the exact
weight of `U(n) - U(-n)` in `H = sum_n ((-1)^(n-1) i / 2 pi n)(U(n) - U(-n))`, the branch of
`i log U` with eigenvalues in `(-1/2, 1/2]`. -/
@[zil_level bridge_theorem]
theorem sawtooth_fourier_coefficient (n : ℕ) (hn : n ≠ 0) :
    2 * ∫ x in (-(1 : ℝ) / 2)..(1 / 2), x * Real.sin (2 * π * n * x)
      = 2 * (-1) ^ (n - 1) / (2 * π * n) := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hn2 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hc : (2 * π * n : ℝ) ≠ 0 := by positivity
  have hint :
      ∫ x in (-(1 : ℝ) / 2)..(1 / 2), x * Real.sin (2 * π * n * x)
        = sawtoothAntideriv (2 * π * n) (1 / 2)
          - sawtoothAntideriv (2 * π * n) (-(1 : ℝ) / 2) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => sawtoothAntideriv_hasDerivAt (2 * π * n) hc x) ?_
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hhalf : (2 * π * n : ℝ) * (1 / 2) = n * π := by ring
  have hsin : Real.sin ((2 * π * n : ℝ) * (1 / 2)) = 0 := by
    rw [hhalf]; exact Real.sin_nat_mul_pi n
  have hcos : Real.cos ((2 * π * n : ℝ) * (1 / 2)) = (-1) ^ n := by
    rw [hhalf]; exact Real.cos_nat_mul_pi n
  have hpow : ((-1 : ℝ)) ^ (n - 1) = -(-1 : ℝ) ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_sub_one, pow_succ]
    ring
  rw [hint]
  unfold sawtoothAntideriv
  rw [show (2 * π * n : ℝ) * (-(1 : ℝ) / 2) = -((2 * π * n : ℝ) * (1 / 2)) by ring,
    Real.sin_neg, Real.cos_neg, hsin, hcos, hpow]
  field_simp
  ring

/-! ## Section F - the integer Weyl commutation (Eqs. 6.2-6.3) -/

/-- **['t Hooft Eq. (6.2) for integers]** in the Weyl CCR system, two Weyl operators whose
symplectic pairing is `2 pi` times an integer commute exactly: the Weyl phase is
`e^(2 pi i k) = 1`. This is the algebraic mechanism that lets the automaton's integer raising
operators all commute, anchoring the identification of the automaton's fractional-part operators
with the field theory's exponentiated fields (Eq. 6.3). -/
@[zil_level bridge_theorem]
theorem weyl_integer_commutation {A : Type*} [Ring A] [Algebra ℂ A]
    (w : WeylSystem (A := A) symplecticPairing) (φ ψ : Fin 2 → ℝ) (k : ℤ)
    (hσ : symplecticPairing φ ψ = 2 * π * k) :
    w.W φ * w.W ψ = w.W ψ * w.W φ := by
  rw [weyl_commutation w φ ψ, hσ]
  have hphase : Complex.exp (-(Complex.I * ((2 * π * k : ℝ) : ℂ))) = 1 := by
    rw [show -(Complex.I * ((2 * π * k : ℝ) : ℂ))
        = ((-k : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)
  rw [hphase, one_smul]

/-! ## Section F' - the beable subalgebra as a commutant structure (Eq. 6.3) -/

/-- **['t Hooft's beables lie in their own commutant]** a family of Weyl operators over test
functions with pairwise `2 pi`-integer symplectic pairing is contained in its own commutant
(`StarAlgebraGNSFormCommutant.commutant`, the centralizer): the automaton's ontological
observables form a mutually commuting family inside the field algebra. -/
@[zil_level bridge_theorem]
theorem automaton_weyl_family_in_own_commutant {A : Type*} [Ring A] [Algebra ℂ A]
    (w : WeylSystem (A := A) symplecticPairing) (S : Set (Fin 2 → ℝ))
    (hS : ∀ φ ∈ S, ∀ ψ ∈ S, ∃ k : ℤ, symplecticPairing φ ψ = 2 * π * k) :
    w.W '' S ⊆ commutant (w.W '' S) := by
  intro x hx
  obtain ⟨φ, hφ, rfl⟩ := hx
  intro m hm
  obtain ⟨ψ, hψ, rfl⟩ := hm
  obtain ⟨k, hk⟩ := hS ψ hψ φ hφ
  exact weyl_integer_commutation w ψ φ k hk

/-- **[The beable algebra is abelian - all centre, maximally non-factor]** the double commutant
generated by the integer Weyl family - its von Neumann algebra in the algebraic bicommutant
sense of the repository's commutant layer - coincides with its own centre:
`Z(M) = M ∩ M' = M`. A factor has trivial centre; the beable algebra is the opposite extreme,
totally commutative - the operator-algebraic face of 't Hooft's ontological basis. -/
@[zil_level bridge_theorem]
theorem automaton_beable_bicommutant_abelian {A : Type*} [Ring A] [Algebra ℂ A]
    (w : WeylSystem (A := A) symplecticPairing) (S : Set (Fin 2 → ℝ))
    (hS : ∀ φ ∈ S, ∀ ψ ∈ S, ∃ k : ℤ, symplecticPairing φ ψ = 2 * π * k) :
    commutantCentre (commutant (commutant (w.W '' S))) =
      commutant (commutant (w.W '' S)) := by
  unfold commutantCentre
  rw [commutant_triple]
  exact Set.inter_eq_left.mpr
    (commutant_antitone (automaton_weyl_family_in_own_commutant w S hS))

/-! ## Section G - the mover commutator kernel (Eqs. 4.4-4.5) as a Pauli-Jordan structure -/

/-- **The lattice mover commutator kernel** ('t Hooft Eqs. 4.4-4.5):
`[a^L(x), a^L(y)] = i K(x,y)` with `K(x, x+1) = 1/2 pi`, `K(x, x-1) = -1/2 pi` and zero
otherwise - the nearest-neighbour symplectic structure of the left-mover algebra. -/
noncomputable def moverCommutatorKernel (x y : ℤ) : ℝ :=
  if y = x + 1 then 1 / (2 * π) else if y = x - 1 then -(1 / (2 * π)) else 0

/-- **[The mover kernel is a Pauli-Jordan commutator]** - antisymmetric, hence a genuine
commutator-function in the Sorkin-Johnston sense. -/
@[zil_level bridge_theorem]
theorem moverCommutatorKernel_isPauliJordan : IsPauliJordan moverCommutatorKernel := by
  intro x y
  unfold moverCommutatorKernel
  rcases eq_or_ne y (x + 1) with h1 | h1
  · subst h1
    rw [if_pos rfl, if_neg (show x ≠ x + 1 + 1 by omega),
      if_pos (show x = x + 1 - 1 by omega)]
    ring
  · rcases eq_or_ne y (x - 1) with h2 | h2
    · subst h2
      rw [if_neg h1, if_pos rfl, if_pos (show x = x - 1 + 1 by omega)]
    · rw [if_neg h1, if_neg h2, if_neg (show x ≠ y + 1 by omega),
        if_neg (show x ≠ y - 1 by omega)]
      ring

/-- **[The evolution preserves the mover symplectic structure]** the lattice shift that implements
one automaton time step on the movers (`moverLeft_step`) leaves the commutator kernel invariant -
the deterministic evolution is a symplectic (Bogoliubov-type) transformation of the mover
algebra. -/
@[zil_level physical_theorem]
theorem moverCommutatorKernel_shift_invariant (x y : ℤ) :
    moverCommutatorKernel (x + 1) (y + 1) = moverCommutatorKernel x y := by
  unfold moverCommutatorKernel
  rcases eq_or_ne y (x + 1) with h1 | h1
  · subst h1
    rw [if_pos rfl, if_pos rfl]
  · rcases eq_or_ne y (x - 1) with h2 | h2
    · subst h2
      rw [if_neg (show (x : ℤ) - 1 + 1 ≠ x + 1 + 1 by omega),
        if_pos (show (x : ℤ) - 1 + 1 = x + 1 - 1 by omega),
        if_neg h1, if_pos rfl]
    · rw [if_neg (show y + 1 ≠ x + 1 + 1 by omega),
        if_neg (show y + 1 ≠ x + 1 - 1 by omega),
        if_neg h1, if_neg h2]

/-- **[Kernel microcausality]** the mover commutator kernel vanishes beyond nearest neighbours:
sites at lattice distance at least two have zero commutator function - the support of the mover
symplectic structure is exactly the causal adjacency of the unit-speed automaton cone. -/
@[zil_level physical_theorem]
theorem moverCommutatorKernel_eq_zero_of_far (x y : ℤ) (h : 2 ≤ |x - y|) :
    moverCommutatorKernel x y = 0 := by
  have h1 : y ≠ x + 1 := by
    intro he
    subst he
    rw [show x - (x + 1) = (-1 : ℤ) from by ring] at h
    norm_num at h
  have h2 : y ≠ x - 1 := by
    intro he
    subst he
    rw [show x - (x - 1) = (1 : ℤ) from by ring] at h
    norm_num at h
  unfold moverCommutatorKernel
  rw [if_neg h1, if_neg h2]

/-- **[Operator microcausality beyond the cone]** any operator pair whose c-number commutator is
the far-site mover kernel necessarily commutes: `star a * b - b * star a = K(x,y) 1` with
`|x - y| >= 2` forces `star a * b = b * star a`. Einstein causality holds in every operator
realization of the mover algebra, from the kernel support alone. -/
@[zil_level bridge_theorem]
theorem mover_cnumber_commutation_of_far {B : Type*} [Ring B] [StarRing B]
    [Algebra ℂ B] (x y : ℤ) (h : 2 ≤ |x - y|) {a b : B}
    (hcnumber : star a * b - b * star a
      = ((moverCommutatorKernel x y : ℝ) : ℂ) • (1 : B)) :
    star a * b = b * star a := by
  rw [moverCommutatorKernel_eq_zero_of_far x y h] at hcnumber
  rw [Complex.ofReal_zero, zero_smul] at hcnumber
  exact sub_eq_zero.mp hcnumber

/-- **[Lightlike-adjacent movers admit no weakly local state]** for a normalized linear state
that is weakly local on an operator pair whose c-number commutator is the nearest-neighbour
mover kernel, the c-number upgrade of the Hadamard local net
(`HadamardLocalNet.weakLocality_cnumber_commutator_zero`) forces the kernel to vanish - but the
adjacent kernel is `1/(2 pi)`, nonzero. Weak locality fails exactly on the causal adjacency:
the nearest-neighbour support of the mover kernel is lightlike, not spacelike, matching the
unit-speed causal cone. -/
@[zil_level bridge_theorem]
theorem mover_adjacent_no_weak_locality {B : Type*} [Ring B] [StarRing B]
    [Algebra ℂ B] (ω : B →ₗ[ℂ] ℂ) (hω : ω 1 = 1) (x : ℤ) {a b : B}
    (hcnumber : star a * b - b * star a
      = ((moverCommutatorKernel x (x + 1) : ℝ) : ℂ) • (1 : B))
    (hweak : ω (star a * b) = ω (b * star a)) : False := by
  have hz := weakLocality_cnumber_commutator_zero ω hω hweak hcnumber
  have hkernel : moverCommutatorKernel x (x + 1) = 1 / (2 * π) := by
    unfold moverCommutatorKernel
    rw [if_pos rfl]
  rw [hkernel] at hz
  have hne : (1 / (2 * π) : ℝ) ≠ 0 := by positivity
  exact hne (by exact_mod_cast hz)

/-- **[The mover algebra carries a Sorkin-Johnston-type state]** any symmetric Hadamard kernel
with non-negative diagonal completes the mover commutator to a two-point function satisfying the
SJ positivity-and-commutator conditions - the algebraic-QFT face of the automaton's boson dual. -/
@[zil_level bridge_theorem]
theorem mover_wightman_isSJState (Had : ℤ → ℤ → ℝ)
    (hH : IsSymmetricKernel Had) (hpos : ∀ x, 0 ≤ Had x x) :
    IsSJState (wightmanTwoPoint Had moverCommutatorKernel) moverCommutatorKernel :=
  wightman_isSJState Had moverCommutatorKernel hH moverCommutatorKernel_isPauliJordan hpos

/-! ## Section H - the duality skeleton, assembled -/

/-- **[The automaton-boson duality skeleton]** the exact discrete content of 't Hooft's duality in
one statement: the update is a bijection; the integer movers transport at exactly the speed of
light in both directions; the homogeneous automaton channel preserves KL divergence (zero Landauer
cost); and the mover commutator kernel is an evolution-invariant Pauli-Jordan structure. -/
@[zil_level physical_theorem]
theorem automaton_boson_duality_skeleton
    (s : AutomatonState) (x : ℤ)
    (μ ν : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Function.Bijective step
      ∧ moverLeft (step s) x = moverLeft s (x + 1)
      ∧ moverRight (step s) x = moverRight s (x - 1)
      ∧ klDiv (μ.compProd (computationKernel homogeneousNatStep))
          (ν.compProd (computationKernel homogeneousNatStep)) = klDiv μ ν
      ∧ IsPauliJordan moverCommutatorKernel
      ∧ moverCommutatorKernel (x + 1) (x + 1 + 1) = moverCommutatorKernel x (x + 1) :=
  ⟨stepEquiv.bijective, moverLeft_step s x, moverRight_step s x,
    automaton_channel_keeps_kl μ ν, moverCommutatorKernel_isPauliJordan,
    moverCommutatorKernel_shift_invariant x (x + 1)⟩

/-! ## Section H - the automaton as a radius-one local rule with a unit-speed cone -/

/-- The integer automaton update packed as a rule on site values `(Q x, P x)`:
the first component is the updated field, the second the updated link
momentum, both read off the radius-one neighbourhood. -/
def packedStep : (ℤ → ℤ × ℤ) → (ℤ → ℤ × ℤ) := fun s x =>
  ((s x).1 + ((s x).2 + (s (x - 1)).1 - 2 * (s x).1 + (s (x + 1)).1),
   (s x).2 + (s (x - 1)).1 - 2 * (s x).1 + (s (x + 1)).1)

/-- The packed rule computes exactly the automaton step through the packing
`x ↦ (Q x, P x)`. -/
theorem packedStep_eq_step (s : AutomatonState) (x : ℤ) :
    packedStep (fun y => (s.Q y, s.P y)) x = ((step s).Q x, (step s).P x) :=
  rfl

/-- **The automaton update is a radius-one local rule**: the updated site
value reads only the site and its two nearest neighbours. -/
@[zil_level bridge_theorem]
theorem packedStep_isLocalRule : IsLocalRule 1 packedStep := by
  intro s t x hagree
  have h0 : s x = t x := hagree x (by simp)
  have hm : s (x - 1) = t (x - 1) := by
    refine hagree (x - 1) ?_
    rw [show x - 1 - x = (-1 : ℤ) from by ring]
    simp
  have hp : s (x + 1) = t (x + 1) := by
    refine hagree (x + 1) ?_
    rw [show x + 1 - x = (1 : ℤ) from by ring]
    simp
  simp only [packedStep, h0, hm, hp]

/-- **The automaton causal cone**: `n` steps of the packed automaton rule
depend only on initial data within distance `n` - an exact unit-speed light
cone, one site per step, by the general causal-cone theorem of
`CellularAutomatonLocality`. -/
@[zil_level bridge_theorem]
theorem packedStep_iterate_isLocalRule (n : ℕ) :
    IsLocalRule n packedStep^[n] := by
  simpa using iterate_isLocalRule packedStep_isLocalRule n

/-- The packing intertwines the packed rule with the automaton step at every
iteration order. -/
theorem packedStep_iterate_eq (s : AutomatonState) (n : ℕ) :
    packedStep^[n] (fun y => (s.Q y, s.P y)) =
      fun y => ((step^[n] s).Q y, (step^[n] s).P y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext y
      exact packedStep_eq_step (step^[n] s) y

/-- **Cone determinism for the integer automaton**: two automaton states that
agree on all sites within distance `n` of `x` have identical field and
momentum at `x` after `n` steps - initial data outside the causal cone cannot
influence its apex. -/
@[zil_level bridge_theorem]
theorem automaton_causal_cone {s t : AutomatonState} (n : ℕ) (x : ℤ)
    (h : ∀ y : ℤ, |y - x| ≤ (n : ℤ) → s.Q y = t.Q y ∧ s.P y = t.P y) :
    (step^[n] s).Q x = (step^[n] t).Q x ∧
      (step^[n] s).P x = (step^[n] t).P x := by
  have hpack := packedStep_iterate_isLocalRule n
    (fun y => (s.Q y, s.P y)) (fun y => (t.Q y, t.P y)) x
    (fun y hy => by
      obtain ⟨h1, h2⟩ := h y hy
      simp [h1, h2])
  rw [packedStep_iterate_eq, packedStep_iterate_eq] at hpack
  simpa [Prod.ext_iff] using hpack

/-! ## Section I - the quantized automaton and its timeless sector -/

/-- **The homogeneous automaton step as a lattice bijection**: the shear
`(Q, P) ↦ (Q + P, P)` of `homogeneousStep`, inverted by
`(Q, P) ↦ (Q - P, P)`. -/
def homogeneousStepEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun := homogeneousStep
  invFun s := (s.1 - s.2, s.2)
  left_inv s := by
    cases s with
    | mk q p => simp [homogeneousStep]
  right_inv s := by
    cases s with
    | mk q p => simp [homogeneousStep]

/-- **The fixed points of the shear are the zero-momentum configurations.** -/
@[zil_level physical_theorem]
theorem homogeneousStepEquiv_fixed_iff (x : ℤ × ℤ) :
    homogeneousStepEquiv x = x ↔ x.2 = 0 := by
  obtain ⟨q, p⟩ := x
  constructor
  · intro h
    have h1 : q + p = q := (Prod.ext_iff.mp h).1
    show p = 0
    omega
  · intro h
    show ((q + p, p) : ℤ × ℤ) = (q, p)
    rw [show p = 0 from h, add_zero]

/-- **The shear orbit in closed form**: `n` steps translate the field by
`n` times the momentum. -/
@[zil_level physical_theorem]
theorem homogeneous_iterate (q p : ℤ) (n : ℕ) :
    (⇑homogeneousStepEquiv)^[n] (q, p) = (q + (n : ℤ) * p, p) := by
  induction n with
  | zero =>
      have h0 : q + ((0 : ℕ) : ℤ) * p = q := by push_cast; ring
      rw [h0]
      exact Function.iterate_zero_apply _ _
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      refine Prod.ext_iff.mpr ⟨?_, rfl⟩
      show q + (m : ℤ) * p + p = q + ((m + 1 : ℕ) : ℤ) * p
      push_cast
      ring

/-- **Zero-momentum support**: the amplitude vanishes on every configuration
with nonzero momentum. -/
def ZeroMomentumSupported (ψ : lp (fun _ : ℤ × ℤ => ℂ) 2) : Prop :=
  ∀ q p : ℤ, p ≠ 0 → ψ (q, p) = 0

/-- **The automaton's timeless constraint**: the Koopman-quantized shear
carries the Page-Wootters constraint with total operator `U - 1` - the
discrete Wheeler-DeWitt operator of the quantized automaton. -/
noncomputable def automatonTimelessConstraint :
    HamiltonianConstraint (lp (fun _ : ℤ × ℤ => ℂ) 2) :=
  koopmanTimelessConstraint homogeneousStepEquiv

/-- **Zero-momentum amplitudes are stationary**: an amplitude supported on the
fixed sector of the shear solves the time-independent Schrodinger condition,
by the general fixed-support theorem of `KoopmanQuantization`. -/
@[zil_level bridge_theorem]
theorem stationary_of_zeroMomentumSupported {ψ : lp (fun _ : ℤ × ℤ => ℂ) 2}
    (h : ZeroMomentumSupported ψ) :
    koopman homogeneousStepEquiv ψ = ψ := by
  refine stationary_of_support_fixed fun y hy => ?_
  obtain ⟨q, p⟩ := y
  have hp : p ≠ 0 := by
    intro hp0
    exact hy ((homogeneousStepEquiv_fixed_iff (q, p)).mpr hp0)
  exact h q p hp

/-- **Moving configurations admit no normalizable stationary amplitude**: at
nonzero momentum the shear orbit is infinite, so the general
infinite-orbit theorem of `KoopmanQuantization` forces the amplitude to
vanish. -/
@[zil_level bridge_theorem]
theorem zeroMomentumSupported_of_stationary {ψ : lp (fun _ : ℤ × ℤ => ℂ) 2}
    (h : koopman homogeneousStepEquiv ψ = ψ) : ZeroMomentumSupported ψ := by
  intro q p hp
  refine stationary_vanishes_on_infinite_orbit h ?_
  intro m n hmn
  have hmn' : (⇑homogeneousStepEquiv)^[m] (q, p)
      = (⇑homogeneousStepEquiv)^[n] (q, p) := hmn
  rw [homogeneous_iterate, homogeneous_iterate] at hmn'
  have h1 : q + (m : ℤ) * p = q + (n : ℤ) * p := (Prod.ext_iff.mp hmn').1
  have h2 : (m : ℤ) * p = (n : ℤ) * p := by linarith
  have h3 : (m : ℤ) = (n : ℤ) := mul_right_cancel₀ hp h2
  exact_mod_cast h3

/-- **The timeless sector is exactly zero momentum**: a normalizable state
satisfies the Page-Wootters constraint of the quantized automaton iff its
amplitude vanishes on every moving configuration - motion is incompatible
with the timeless constraint at normalizable level, and relational time lives
entirely in the moving sector. -/
@[zil_level bridge_theorem]
theorem automaton_physical_iff_zeroMomentum (ψ : lp (fun _ : ℤ × ℤ => ℂ) 2) :
    automatonTimelessConstraint.IsPhysical ψ ↔ ZeroMomentumSupported ψ := by
  unfold automatonTimelessConstraint
  rw [isPhysical_iff_fixed]
  exact ⟨zeroMomentumSupported_of_stationary, stationary_of_zeroMomentumSupported⟩

/-- **The automaton as a measurement-free quantum Turing machine, assembled**:
the Koopman step is an isometry, it shadows the classical automaton on
configuration basis states, its timeless (Page-Wootters physical) states are
exactly the zero-momentum amplitudes, and every all-unitary quantum Turing
trace of the computation-thermodynamics layer has zero Landauer count. -/
@[zil_level bridge_theorem]
theorem automaton_quantum_turing_machine (Us : List 𝐔[Qubit]) :
    (∀ ψ : lp (fun _ : ℤ × ℤ => ℂ) 2, ‖koopman homogeneousStepEquiv ψ‖ = ‖ψ‖)
    ∧ (∀ x : ℤ × ℤ, koopman homogeneousStepEquiv (lp.single 2 x 1)
        = lp.single 2 (homogeneousStep x) 1)
    ∧ (∀ ψ : lp (fun _ : ℤ × ℤ => ℂ) 2,
        automatonTimelessConstraint.IsPhysical ψ ↔ ZeroMomentumSupported ψ)
    ∧ qtmLandauerCount (Us.map QubitStep.unitary) = 0 :=
  ⟨fun ψ => koopman_norm_eq homogeneousStepEquiv ψ,
   fun x => koopman_single homogeneousStepEquiv x 1,
   automaton_physical_iff_zeroMomentum,
   qtmLandauerCount_unitary_only Us⟩

/-! ## Section J - the fermionic edge layer (Eqs. 6.21-6.22, 8.1) -/

/-- **The edge parity character** ('t Hooft Eq. 6.21): the alternating sign
`(-1)^(P+Q)` over a mover pair - the lattice fermion parity, the
configuration whose orthogonality defines the finite-energy sector. -/
noncomputable def edgeSign (s : ℤ × ℤ) : ℂ := (-1 : ℂ) ^ (s.1 + s.2)

/-- The edge sign is unimodular at every pair. -/
lemma edgeSign_norm (s : ℤ × ℤ) : ‖edgeSign s‖ = 1 := by
  unfold edgeSign
  rw [norm_zpow, norm_neg, norm_one, one_zpow]

/-- **[The edge state has infinite energy]** the alternating edge configuration
is not square-summable: it lies outside the amplitude space, by the general
unimodular exclusion of `KoopmanQuantization` - 't Hooft's removal of edge
states from the finite-energy sector. -/
@[zil_level bridge_theorem]
theorem edgeSign_not_memℓp : ¬ Memℓp edgeSign 2 :=
  unimodular_not_memℓp edgeSign edgeSign_norm

/-- **[Every ontological basis state violates the edge constraint]** ('t Hooft
Eq. 8.1, generalized from the vacuum to every basis state): the pairing of a
configuration basis state against the edge sign is the nonzero unimodular
number `(-1)^(P+Q)`. No automaton basis state is orthogonal to the edge
state - the fermionically constrained physical sector contains no classical
configuration, and physical states are necessarily superpositions. -/
@[zil_level bridge_theorem]
theorem ontological_basis_violates_edge_constraint (s : ℤ × ℤ) :
    ∑' t : ℤ × ℤ, edgeSign t * (lp.single 2 s (1 : ℂ) : (ℤ × ℤ) → ℂ) t ≠ 0 := by
  have hval : ∑' t : ℤ × ℤ,
      edgeSign t * (lp.single 2 s (1 : ℂ) : (ℤ × ℤ) → ℂ) t = edgeSign s := by
    rw [tsum_eq_single s]
    · rw [lp.coeFn_single, Pi.single_eq_same, mul_one]
    · intro t ht
      rw [lp.coeFn_single, Pi.single_eq_of_ne ht, mul_zero]
  rw [hval]
  exact zpow_ne_zero (s.1 + s.2) (by norm_num : (-1 : ℂ) ≠ 0)

/-- **[The automaton vacuum is excluded]** ('t Hooft Eq. 8.1): the cellular
ground state - the basis state at the zero configuration - violates the edge
constraint; the bosonic dictionary applies only away from it, or fermions
must be added. -/
@[zil_level physical_theorem]
theorem vacuum_violates_edge_constraint :
    ∑' t : ℤ × ℤ,
      edgeSign t * (lp.single 2 ((0, 0) : ℤ × ℤ) (1 : ℂ) : (ℤ × ℤ) → ℂ) t ≠ 0 :=
  ontological_basis_violates_edge_constraint (0, 0)

/-- **The lattice fermion parity operator**: multiplication by the edge sign -
the grading of the amplitude space by the parity of the mover pair. -/
noncomputable def parityMul (ψ : lp (fun _ : ℤ × ℤ => ℂ) 2) :
    lp (fun _ : ℤ × ℤ => ℂ) 2 :=
  ⟨fun t => edgeSign t * ψ t, by
    refine memℓp_gen ?_
    refine ((lp.memℓp ψ).summable two_toReal_pos).congr fun t => ?_
    rw [norm_mul, edgeSign_norm, one_mul]⟩

@[simp] lemma parityMul_apply (ψ : lp (fun _ : ℤ × ℤ => ℂ) 2) (t : ℤ × ℤ) :
    (parityMul ψ : (ℤ × ℤ) → ℂ) t = edgeSign t * ψ t := rfl

/-- The edge sign squares to one pointwise. -/
lemma edgeSign_mul_self (t : ℤ × ℤ) : edgeSign t * edgeSign t = 1 := by
  unfold edgeSign
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [show (t.1 + t.2) + (t.1 + t.2) = 2 * (t.1 + t.2) from by ring]
  rw [zpow_mul]
  norm_num

/-- **[Parity is an involution]** the lattice fermion parity squares to the
identity on amplitudes - the grading structure whose abstract CAR form is
`fermionParity_involution` of the composite-fermion algebra. -/
@[zil_level bridge_theorem]
theorem parityMul_involution (ψ : lp (fun _ : ℤ × ℤ => ℂ) 2) :
    parityMul (parityMul ψ) = ψ := by
  apply lp.ext
  funext t
  simp only [parityMul_apply]
  rw [← mul_assoc, edgeSign_mul_self, one_mul]

/-- **[Parity is an isometry]** the grading preserves the amplitude norm. -/
@[zil_level physical_theorem]
theorem parityMul_norm_eq (ψ : lp (fun _ : ℤ × ℤ => ℂ) 2) :
    ‖parityMul ψ‖ = ‖ψ‖ := by
  rw [lp.norm_eq_tsum_rpow two_toReal_pos, lp.norm_eq_tsum_rpow two_toReal_pos]
  congr 1
  refine tsum_congr fun t => ?_
  rw [show (parityMul ψ : (ℤ × ℤ) → ℂ) t = edgeSign t * ψ t from rfl,
    norm_mul, edgeSign_norm, one_mul]

/-- **[Basis states are parity eigenvectors]** the ontological basis
diagonalizes the fermionic grading with eigenvalue the edge sign - which is
exactly why no basis state can be orthogonal to the edge state. -/
@[zil_level bridge_theorem]
theorem parityMul_single (s : ℤ × ℤ) :
    parityMul (lp.single 2 s (1 : ℂ)) = edgeSign s • lp.single 2 s (1 : ℂ) := by
  apply lp.ext
  funext t
  simp only [parityMul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne t s with h | h
  · subst h
    rw [lp.coeFn_single, Pi.single_eq_same, mul_one]
  · rw [lp.coeFn_single, Pi.single_eq_of_ne h, mul_zero, mul_zero]

/-- **[The edge pair transports with the automaton]** ('t Hooft Eq. 6.22
covariance): one automaton step carries the mover pair at `x` to the mover
pair at `x + 1`, so the edge-constraint family is evolution-covariant - the
`for any point x` in the exclusion constraint is forced by the dynamics. -/
@[zil_level physical_theorem]
theorem edge_pair_step_covariant (s : AutomatonState) (x : ℤ) :
    (moverLeft (step s) x, moverLeft (step s) (x + 1))
      = (moverLeft s (x + 1), moverLeft s (x + 1 + 1)) := by
  rw [moverLeft_step, moverLeft_step]

/-- **The fermionic edge layer, assembled**: the edge state is excluded from
the amplitude space, every ontological basis state violates the fermionic
edge constraint, the lattice fermion parity is an involutive grading, and the
edge-constraint family is evolution-covariant. -/
@[zil_level bridge_theorem]
theorem automaton_fermionic_edge_exclusion :
    (¬ Memℓp edgeSign 2)
    ∧ (∀ s : ℤ × ℤ, ∑' t : ℤ × ℤ,
        edgeSign t * (lp.single 2 s (1 : ℂ) : (ℤ × ℤ) → ℂ) t ≠ 0)
    ∧ (∀ ψ : lp (fun _ : ℤ × ℤ => ℂ) 2, parityMul (parityMul ψ) = ψ)
    ∧ (∀ (s : AutomatonState) (x : ℤ),
        (moverLeft (step s) x, moverLeft (step s) (x + 1))
          = (moverLeft s (x + 1), moverLeft s (x + 1 + 1))) :=
  ⟨edgeSign_not_memℓp, ontological_basis_violates_edge_constraint,
   parityMul_involution, edge_pair_step_covariant⟩

end Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality

end

open Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality in
#physlib_axiom_clean_all [
  moverLeft_step,
  moverRight_step,
  moverLeft_iterate,
  discrete_wave_equation,
  step_homogeneousState,
  homogeneousNatStep_injective,
  automaton_channel_keeps_kl,
  automaton_entropy_production_zero,
  sawtooth_fourier_coefficient,
  weyl_integer_commutation,
  automaton_weyl_family_in_own_commutant,
  automaton_beable_bicommutant_abelian,
  moverCommutatorKernel_isPauliJordan,
  moverCommutatorKernel_shift_invariant,
  moverCommutatorKernel_eq_zero_of_far,
  mover_cnumber_commutation_of_far,
  mover_adjacent_no_weak_locality,
  mover_wightman_isSJState,
  automaton_boson_duality_skeleton,
  packedStep_eq_step,
  packedStep_isLocalRule,
  packedStep_iterate_isLocalRule,
  packedStep_iterate_eq,
  automaton_causal_cone,
  homogeneousStepEquiv_fixed_iff,
  homogeneous_iterate,
  stationary_of_zeroMomentumSupported,
  zeroMomentumSupported_of_stationary,
  automaton_physical_iff_zeroMomentum,
  automaton_quantum_turing_machine,
  edgeSign_norm,
  edgeSign_not_memℓp,
  ontological_basis_violates_edge_constraint,
  vacuum_violates_edge_constraint,
  edgeSign_mul_self,
  parityMul_involution,
  parityMul_norm_eq,
  parityMul_single,
  edge_pair_step_covariant,
  automaton_fermionic_edge_exclusion ]

open Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality in
#physlib_non_vacuous_all [
  moverLeft_step,
  moverRight_step,
  moverLeft_iterate,
  discrete_wave_equation,
  homogeneousNatStep_injective,
  automaton_channel_keeps_kl,
  automaton_entropy_production_zero,
  sawtooth_fourier_coefficient,
  weyl_integer_commutation,
  automaton_weyl_family_in_own_commutant,
  automaton_beable_bicommutant_abelian,
  moverCommutatorKernel_isPauliJordan,
  moverCommutatorKernel_shift_invariant,
  moverCommutatorKernel_eq_zero_of_far,
  mover_cnumber_commutation_of_far,
  mover_adjacent_no_weak_locality,
  mover_wightman_isSJState,
  automaton_boson_duality_skeleton,
  packedStep_isLocalRule,
  packedStep_iterate_isLocalRule,
  packedStep_iterate_eq,
  automaton_causal_cone,
  homogeneousStepEquiv_fixed_iff,
  homogeneous_iterate,
  stationary_of_zeroMomentumSupported,
  zeroMomentumSupported_of_stationary,
  automaton_physical_iff_zeroMomentum,
  automaton_quantum_turing_machine,
  edgeSign_norm,
  edgeSign_not_memℓp,
  ontological_basis_violates_edge_constraint,
  vacuum_violates_edge_constraint,
  edgeSign_mul_self,
  parityMul_involution,
  parityMul_norm_eq,
  parityMul_single,
  edge_pair_step_covariant,
  automaton_fermionic_edge_exclusion ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverLeft_step where
  formalizes @ "claim:the-hooft-automaton-integer-movers-transport-exactly-one-site-per-step-at-the-speed-of-light",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.discrete_wave_equation where
  formalizes @ "claim:the-hooft-automaton-update-laws-compose-to-the-exact-discrete-dalembert-wave-equation",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_channel_keeps_kl where
  formalizes @ "claim:the-deterministic-automaton-computation-kernel-preserves-kl-divergence-exactly-zero-landauer-cost",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.Thermodynamics.ComputationLandauer.computation_keeps_kl",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1",
  caveat @ "claim:the-kl-preservation-is-the-homogeneous-sector-nat-encoded-channel-not-a-full-field-configuration-space-statement"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.homogeneousNatStep_injective where
  formalizes @ "claim:the-automaton-driver-is-injective-on-the-reversible-side-of-the-carneiro-primitive-basis-split",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.ComputationLandauer.succ_injective"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.sawtooth_fourier_coefficient where
  formalizes @ "claim:the-sawtooth-fourier-coefficient-of-the-hooft-periodic-automaton-hamiltonian-is-two-times-minus-one-to-the-n-minus-one-over-two-pi-n",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1",
  caveat @ "claim:the-coefficient-identity-is-proved-the-operator-series-for-i-log-u-and-its-spectrum-are-not-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.weyl_integer_commutation where
  formalizes @ "claim:weyl-operators-with-two-pi-integer-symplectic-pairing-commute-the-integer-raising-operators-of-the-automaton-mapping",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime.weyl_commutation",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_weyl_family_in_own_commutant where
  formalizes @ "claim:the-automaton-beable-family-lies-in-its-own-commutant",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_beable_bicommutant_abelian where
  formalizes @ "claim:the-beable-bicommutant-algebra-is-abelian-all-centre-maximally-non-factor",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant_triple",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1",
  caveat @ "claim:the-bicommutant-is-algebraic-centralizer-closure-not-an-operator-topology-von-neumann-closure"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverCommutatorKernel_eq_zero_of_far where
  formalizes @ "claim:the-mover-kernel-vanishes-beyond-nearest-neighbours-kernel-microcausality",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.mover_cnumber_commutation_of_far where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverCommutatorKernel_eq_zero_of_far",
  formalizes @ "claim:operators-with-far-site-cnumber-mover-commutator-necessarily-commute",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:einstein-causality-for-realizations-with-the-stated-cnumber-commutator-no-operator-net-is-constructed"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.mover_adjacent_no_weak_locality where
  formalizes @ "claim:no-normalized-state-is-weakly-local-across-lightlike-adjacent-mover-pairs",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.weakLocality_cnumber_commutator_zero"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverCommutatorKernel_isPauliJordan where
  formalizes @ "claim:the-lattice-mover-commutator-is-a-nearest-neighbour-pauli-jordan-kernel",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState.IsPauliJordan",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.mover_wightman_isSJState where
  formalizes @ "claim:the-mover-algebra-completes-to-a-sorkin-johnston-type-state-for-any-positive-symmetric-hadamard-part",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState.wightman_isSJState",
  caveat @ "claim:kernel-level-sj-structure-the-distinguished-hadamard-part-of-the-boson-vacuum-is-not-constructed"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_boson_duality_skeleton where
  formalizes @ "claim:the-hooft-cellular-automaton-is-a-reversible-light-speed-information-transport-with-kl-preserving-channel-and-evolution-invariant-pauli-jordan-mover-structure",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1",
  caveat @ "claim:the-full-hilbert-space-unitary-equivalence-with-eta-operators-phase-function-and-edge-states-is-not-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.packedStep_isLocalRule where
  formalizes @ "claim:the-automaton-update-is-a-radius-one-local-rule",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality.IsLocalRule",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.packedStep_iterate_isLocalRule where
  formalizes @ "claim:the-automaton-generates-an-exact-unit-speed-causal-cone",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality.iterate_isLocalRule"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_causal_cone where
  formalizes @ "claim:automaton-states-agreeing-inside-the-cone-evolve-identically-at-its-apex",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1",
  caveat @ "claim:determinism-inside-the-cone-is-proved-tightness-of-the-cone-is-not-claimed"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.zeroMomentumSupported_of_stationary where
  formalizes @ "claim:moving-configurations-admit-no-normalizable-stationary-amplitude",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.stationary_vanishes_on_infinite_orbit",
  caveat @ "claim:stationarity-is-eigenvalue-one-of-the-step-unitary-no-further-spectral-theory-is-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_physical_iff_zeroMomentum where
  formalizes @ "claim:the-timeless-sector-of-the-quantized-automaton-is-exactly-the-zero-momentum-amplitudes",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint",
  supported_by @ "paper:page-wootters-1983-evolution-without-evolution-dynamics-described-by-stationary-observables",
  caveat @ "claim:relational-time-in-the-moving-sector-is-a-reading-only-the-kernel-characterization-is-proved"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_quantum_turing_machine where
  formalizes @ "claim:the-automaton-upgrades-to-a-measurement-free-thermodynamically-costless-quantum-turing-machine",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.Thermodynamics.Landauer.qtmLandauerCount",
  supported_by @ "paper:deutsch-1985-quantum-theory-the-church-turing-principle-and-the-universal-quantum-computer",
  caveat @ "claim:no-tape-head-state-transition-model-with-local-unitarity-conditions-is-constructed"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.edgeSign_not_memℓp where
  formalizes @ "claim:the-edge-state-has-infinite-energy-and-lies-outside-the-amplitude-space",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.unimodular_not_memℓp",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.ontological_basis_violates_edge_constraint where
  formalizes @ "claim:every-ontological-basis-state-violates-the-fermionic-edge-constraint",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1",
  caveat @ "claim:physical-states-being-superpositions-is-the-reading-only-the-nonorthogonality-is-proved"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.vacuum_violates_edge_constraint where
  formalizes @ "claim:the-automaton-vacuum-violates-the-edge-constraint-forcing-excited-sectors-or-added-fermions",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1",
  caveat @ "claim:the-supersymmetric-resolution-is-deferred-by-the-paper-and-not-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.parityMul_involution where
  formalizes @ "claim:the-lattice-fermion-parity-is-an-involutive-grading-of-the-amplitude-space",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity.fermionParity_involution"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.parityMul_single where
  formalizes @ "claim:ontological-basis-states-are-fermion-parity-eigenvectors",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange.antisymmetrize_self"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.edge_pair_step_covariant where
  formalizes @ "claim:the-edge-constraint-family-is-evolution-covariant-under-the-mover-transport",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1"

zil attach Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_fermionic_edge_exclusion where
  formalizes @ "claim:the-fermionic-edge-layer-excludes-the-edge-state-and-every-classical-configuration-from-the-physical-sector",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:hooft-2012-duality-deterministic-cellular-automaton-bosonic-qft-1plus1",
  caveat @ "claim:the-supersymmetric-boson-plus-fermion-completion-lifting-the-constraint-is-not-formalized"

zil_file_contract physlib.automatonBosonDuality where
  promises "The exact discrete skeleton of the 't Hooft cellular-automaton/bosonic-QFT duality: the reversible integer update as a bijection, the integer left/right movers with exact light-speed transport and the discrete d'Alembert equation, the homogeneous-sector step as an injective KL-preserving computation kernel with zero entropy production, the sawtooth Fourier coefficient of the periodic automaton Hamiltonian, the integer Weyl commutation behind the eta-operator mapping with its beable family inside its own commutant and an abelian all-centre bicommutant, the evolution-invariant nearest-neighbour Pauli-Jordan mover kernel - vanishing beyond the causal adjacency, Einstein-causal in every c-number operator realization, weakly-local-state-free on the lightlike adjacency - completing to a Sorkin-Johnston-type state, the radius-one local-rule instance with its exact unit-speed cone determinism, the Koopman-quantized shear whose Page-Wootters timeless sector is exactly the zero-momentum amplitudes, assembling to a measurement-free zero-Landauer quantum Turing machine, and the fermionic edge layer: the alternating edge state is excluded from the amplitude space, every ontological basis state including the vacuum violates the edge constraint, the lattice fermion parity is an involutive isometric grading diagonalized by the basis states, and the constraint family is evolution-covariant."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.ComputationLandauer.computationKernel",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState.wightmanTwoPoint",
    "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime.WeylSystem",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.weakLocality_cnumber_commutator_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality.iterate_isLocalRule",
    "lean:Physlib.QuantumMechanics.KoopmanQuantization.stationary_vanishes_on_infinite_orbit",
    "lean:Physlib.QuantumMechanics.KoopmanQuantization.unimodular_not_memℓp",
    "lean:Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint",
    "lean:Physlib.Thermodynamics.Landauer.qtmLandauerCount",
    "lean:Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity.fermionParity",
    "lean:Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange.antisymmetrize_self"]
  forbids_substitutes ["the full Hilbert-space unitary equivalence with eta operators and the elliptic-theta phase function of 't Hooft section 6",
    "the QFT-side lattice Hamiltonian kernels and their continuum limit of section 4",
    "the supersymmetric boson-plus-fermion completion lifting the edge constraint, deferred by the paper",
    "a claim that quantum field theory is a deterministic automaton"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverLeft_step,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverRight_step,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverLeft_iterate,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.discrete_wave_equation,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_channel_keeps_kl,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_entropy_production_zero,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.sawtooth_fourier_coefficient,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.weyl_integer_commutation,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_weyl_family_in_own_commutant,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_beable_bicommutant_abelian,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverCommutatorKernel_isPauliJordan,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.moverCommutatorKernel_eq_zero_of_far,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.mover_cnumber_commutation_of_far,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.mover_adjacent_no_weak_locality,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.mover_wightman_isSJState,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_boson_duality_skeleton,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.packedStep_isLocalRule,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.packedStep_iterate_isLocalRule,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_causal_cone,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.zeroMomentumSupported_of_stationary,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_physical_iff_zeroMomentum,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_quantum_turing_machine,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.edgeSign_not_memℓp,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.ontological_basis_violates_edge_constraint,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.vacuum_violates_edge_constraint,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.parityMul_involution,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.parityMul_single,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.edge_pair_step_covariant,
    Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality.automaton_fermionic_edge_exclusion ]

/- ZIL-END -/

#zil_formalization_lint physlib.automatonBosonDuality

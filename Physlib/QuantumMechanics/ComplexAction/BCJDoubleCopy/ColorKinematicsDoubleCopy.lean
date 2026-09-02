/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Mathlib.Algebra.Polynomial.Eval.Defs
meta import Zil

/-!
# BCJ color–kinematics duality and the double copy

Ports the mathematically self-contained core of the Bern–Carrasco–Johansson (BCJ) double-copy construction
from the complex-action/entropic-time integration layer into physlib, and links its **kinematic Jacobi identity** to the repo's
Maxwell–Faraday Bianchi identity.

A tree amplitude is organized into channels, each a `BCJTriple` `(nᵢ, cᵢ, Dᵢ)` (kinematic numerator, color
factor, positive propagator). The gauge amplitude is `A = Σᵢ nᵢcᵢ/Dᵢ`; the **double copy** replaces the
color factors by a second set of kinematic numerators, `M = Σᵢ nᵢñᵢ/Dᵢ` — gravity as "gauge²". BCJ
color–kinematics duality is the statement that the numerators satisfy the *same* Jacobi identities as the
color factors:

  `c_s + c_t + c_u = 0`   (color Jacobi, from the gauge structure constants),
  `n_s + n_t + n_u = 0`   (kinematic Jacobi, the BCJ constraint).

* **§A — amplitude data** (`BCJTriple`, `bcjGaugeAmplitude`, `bcjDoubleCopyAmplitude`,
  `bcjDoubleCopy_diagonal_nonneg`). The diagonal double copy `nᵢ²/Dᵢ ≥ 0` — each squared-gauge channel
  contributes nonnegatively to gravity.
* **§B — color–kinematics duality** (`BCJColorKinematicsDuality`, `trivialBCJDuality`,
  `bcj_gauge_amplitude_single_vanishing`).
* **§C — the kinematic Jacobi *is* the Maxwell Bianchi identity** (`faradayBCJDuality`). The cyclic sum
  `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` of `PTSymmetricQFT.MaxwellFaraday.faraday_bianchi` (the
  homogeneous Maxwell equation `dF = 0`, an identity because `F = dA` and `d² = 0`) is exactly the BCJ
  kinematic Jacobi `n_s + n_t + n_u = 0`: both say the antisymmetrized derivative of a potential vanishes.
* **§D — the entropic/Feynman–Kac factorization shadow** (`bcj_doublecopy_fk_factorization`). With
  numerators identified as imaginary/entropic actions
  `nᵢ = S_I`, the path-integral weight of the product theory factorizes,
  `exp(−(S₁+S₂)) = exp(−S₁)·exp(−S₂)`. This exponential identity is not by itself the
  denominated amplitude formula; §A/§E carry that independent BCJ content.
* **§E — finite cubic graph and DDM propagator-matrix algebra** from Ben-Shahar–Garozzo–Johansson
  (JHEP 08 (2023) 222, arXiv:2301.00233): the general cubic-graph amplitude, the double copy as color
  replacement, and generalized-gauge freedom as a propagator-matrix kernel statement.
* **§F — Jacobi rows, generalized-gauge equivalence, and auxiliary fields**: kernel negation/subtraction,
  equivalence laws, the three-channel Jacobi row, the kinematic commutator Jacobi identity, and scalar
  auxiliary-field elimination by completing the square.
* **§G — Lie-Jacobi numerator carriers**: any real coefficient projection of a Lie-Jacobi triple lies in
  the same BCJ Jacobi-row kernel. This is the shared carrier for color and kinematic numerator relations.
* **§H — weighted bilinear double copy**: the finite double-copy amplitude is a weighted bilinear pairing,
  symmetric in the two numerator copies, and invariant under shifts orthogonal to the opposite copy.
* **§I — finite auxiliary-field elimination**: indexed auxiliary fields eliminate to `Σᵢ -Jᵢ²/Kᵢ`, the
  algebraic core of integrating in auxiliary fields to cubicize higher interactions.
* **§J — Mizera's residue construction**: the remaining four-punctured sphere is represented by its
  explicit rational one-form. Its three finite simple-pole coefficients are the `(s,t,u)` numerators,
  the residue at infinity is the negative quadratic coefficient of the common numerator, and regularity
  at infinity derives both the color and kinematic Jacobi identities instead of storing them as inputs.
* **§K — twisted cohomology**: a totalized form complex carries `d` and `dW∧`, their nilpotence and
  anticommutation. Hence `d ± dW∧` squares to zero, Eq. (10) is an actual quotient relation, twisted-exact
  forms are closed, and residue functionals annihilating exact shifts descend to the quotient.
* **§L — intersection localization and four-point amplitudes**: the leading intersection pairing is the
  existing weighted BCJ bilinear and therefore the normalized cubic double copy. Its `Fin 3`
  specialization and the existing cubic graph carrier give Eqs. (4), (17), and (18).

This is a port of `reference tree.Integration.BCJBridge`'s self-contained content; the complex-action/entropic-time plugin-slot and
Gravitas dependencies are not carried over — only the BCJ amplitude/duality algebra and its link to the
repo's Maxwell sector.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, *New Relations for Gauge-Theory Amplitudes*,
  Phys. Rev. D 78 (2008) 085011, arXiv:0805.3993 (color–kinematics duality and the double copy).
* M. Ben-Shahar, L. Garozzo, H. Johansson, *Lagrangians manifesting color-kinematics duality in the
  NMHV sector of Yang-Mills*, JHEP 08 (2023) 222, arXiv:2301.00233 (DDM kernels, kinematic Lie brackets,
  and auxiliary-field cubicization).
* S. Mizera, *Kinematic Jacobi Identity is a Residue Theorem: Geometry of Color-Kinematics Duality for
  Gauge and Gravity Amplitudes*, Phys. Rev. Lett. 124 (2020) 141601, arXiv:1912.03397.
* Repo carrier: `PTSymmetricQFT.MaxwellFaraday.faraday_bianchi` (the homogeneous Maxwell / Bianchi identity).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open scoped BigOperators
open Polynomial


/-- A single BCJ amplitude channel: kinematic numerator `nᵢ`, color factor `cᵢ`, and positive propagator
denominator `Dᵢ`. -/
structure BCJTriple where
  /-- Kinematic numerator `nᵢ`. -/
  numerator : ℝ
  /-- Color factor `cᵢ` (from the gauge structure constants). -/
  color : ℝ
  /-- Propagator denominator `Dᵢ`. -/
  propagator : ℝ
  /-- Positivity of the propagator. -/
  prop_pos : 0 < propagator

/-- **Tree-level gauge amplitude** `A = Σᵢ nᵢcᵢ/Dᵢ`. -/
noncomputable def bcjGaugeAmplitude (ts : List BCJTriple) : ℝ :=
  ts.foldl (fun acc t => acc + t.numerator * t.color / t.propagator) 0

/-- **Tree-level double-copy (gravity) amplitude** `M = Σᵢ nᵢñᵢ/Dᵢ` — the color factors of the gauge
amplitude replaced by a second set of kinematic numerators (gravity as "gauge²"). -/
noncomputable def bcjDoubleCopyAmplitude (ts₁ ts₂ : List BCJTriple) : ℝ :=
  (ts₁.zip ts₂).foldl (fun acc p => acc + p.1.numerator * p.2.numerator / p.1.propagator) 0

/-- **The diagonal double copy is nonnegative per channel** `nᵢ²/Dᵢ ≥ 0` — squaring a single gauge channel
contributes nonnegatively to the gravity amplitude (the propagator is positive). -/
lemma bcjDoubleCopy_diagonal_nonneg (t : BCJTriple) :
    0 ≤ t.numerator ^ 2 / t.propagator :=
  div_nonneg (sq_nonneg _) t.prop_pos.le


/-- **BCJ color–kinematics duality** for a three-channel `(s, t, u)` amplitude: the kinematic numerators
satisfy the *same* Jacobi identity `n_s + n_t + n_u = 0` as the color factors `c_s + c_t + c_u = 0`. -/
structure BCJColorKinematicsDuality where
  /-- Color factor, `s`-channel. -/
  c_s : ℝ
  /-- Color factor, `t`-channel. -/
  c_t : ℝ
  /-- Color factor, `u`-channel. -/
  c_u : ℝ
  /-- Kinematic numerator, `s`-channel. -/
  n_s : ℝ
  /-- Kinematic numerator, `t`-channel. -/
  n_t : ℝ
  /-- Kinematic numerator, `u`-channel. -/
  n_u : ℝ
  /-- Jacobi identity for the color factors. -/
  color_jacobi : c_s + c_t + c_u = 0
  /-- Kinematic Jacobi identity — the BCJ duality condition. -/
  kinematic_jacobi : n_s + n_t + n_u = 0

/-- The trivial duality (all channels zero). -/
def trivialBCJDuality : BCJColorKinematicsDuality where
  c_s := 0; c_t := 0; c_u := 0; n_s := 0; n_t := 0; n_u := 0
  color_jacobi := by ring
  kinematic_jacobi := by ring

/-- **Single-propagator gauge amplitude collects over a common denominator**
`Σ_channels cᵢnᵢ/D = (Σ cᵢnᵢ)/D`. -/
lemma bcj_gauge_amplitude_single_vanishing
    (d : BCJColorKinematicsDuality) (D : ℝ) (hD : 0 < D) :
    d.c_s * d.n_s / D + d.c_t * d.n_t / D + d.c_u * d.n_u / D =
      (d.c_s * d.n_s + d.c_t * d.n_t + d.c_u * d.n_u) / D := by
  field_simp


/-- **[Link] The Maxwell–Faraday Bianchi identity is a BCJ kinematic Jacobi.** The three cyclic terms of the
homogeneous Maxwell equation `dF = 0` for `F = dA` — `k_λ F_{μν}`, `k_μ F_{νλ}`, `k_ν F_{λμ}` — are the
`(s, t, u)` kinematic numerators of a `BCJColorKinematicsDuality`; their sum vanishes by
`PTSymmetricQFT.MaxwellFaraday.faraday_bianchi` (which holds because `d² = 0`). Both the Bianchi identity and
the BCJ kinematic Jacobi say: *the antisymmetrized derivative of a potential vanishes*. The color factors
are supplied with their own gauge Jacobi `c_s + c_t + c_u = 0`. -/
noncomputable def faradayBCJDuality (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (c_s c_t c_u : ℝ) (hcolor : c_s + c_t + c_u = 0) : BCJColorKinematicsDuality where
  c_s := c_s
  c_t := c_t
  c_u := c_u
  n_s := k lam * faraday k A μ ν
  n_t := k μ * faraday k A ν lam
  n_u := k ν * faraday k A lam μ
  color_jacobi := hcolor
  kinematic_jacobi := faraday_bianchi k A lam μ ν


/-- **[Entropic path-weight factorization]** Identifying model numerators with imaginary/entropic
actions `nᵢ = S_I`, the path-integral (Feynman–Kac) weight of the product theory factorizes:
`exp(−(S₁+S₂)) = exp(−S₁)·exp(−S₂)`. The proof is `exp_add`; connecting a concrete model to
the BCJ channel amplitude requires a separate numerator/denominator adapter. -/
lemma bcj_doublecopy_fk_factorization (S₁ S₂ : ℝ) :
    Real.exp (-(S₁ + S₂)) = Real.exp (-S₁) * Real.exp (-S₂) := by
  rw [show -(S₁ + S₂) = -S₁ + -S₂ by ring, Real.exp_add]


/-- Finite cubic-graph amplitude data: color factors `C_Γ`, numerators `N_Γ`, and propagator products
`D_Γ`. This is the finite-type version of the paper's tree formula
`Aₙ = g^(n-2) ∑_{Γ∈Gₙ} C_Γ N_Γ / D_Γ`. -/
structure CubicGraphAmplitudeData (Γ : Type*) where
  /-- Cubic-graph color factor `C_Γ`. -/
  color : Γ → ℝ
  /-- Cubic-graph kinematic numerator `N_Γ`. -/
  numerator : Γ → ℝ
  /-- Product of propagators `D_Γ`. -/
  denominator : Γ → ℝ

/-- General finite cubic-graph Yang-Mills tree amplitude
`Aₙ = g^(n-2) ∑_Γ C_Γ N_Γ / D_Γ`. -/
noncomputable def cubicGraphAmplitude {Γ : Type*} [Fintype Γ]
    (g : ℝ) (n : ℕ) (data : CubicGraphAmplitudeData Γ) : ℝ :=
  g ^ (n - 2) * ∑ γ : Γ, data.color γ * data.numerator γ / data.denominator γ

/-- Finite double-copy amplitude
`Mₙ = (κ/2)^(n-2) ∑_Γ N_Γ Ñ_Γ / D_Γ`. -/
noncomputable def cubicDoubleCopyAmplitudeFinite {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (numerator numeratorTilde denominator : Γ → ℝ) : ℝ :=
  (κ / 2) ^ (n - 2) *
    ∑ γ : Γ, numerator γ * numeratorTilde γ / denominator γ

/-- The finite double copy is exactly the cubic Yang-Mills amplitude with the color factor replaced by a
second numerator. This is the algebraic content of the paper's replacement `C_Γ → Ñ_Γ`. -/
lemma cubicDoubleCopy_eq_cubicAmplitude_colorReplacement {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (N Ñ D : Γ → ℝ) :
    cubicDoubleCopyAmplitudeFinite κ n N Ñ D =
      cubicGraphAmplitude (κ / 2) n
        { color := Ñ, numerator := N, denominator := D } := by
  unfold cubicDoubleCopyAmplitudeFinite cubicGraphAmplitude
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  ring

/-- DDM propagator matrix action on a numerator vector:
`A(σ) = ∑_ρ m(σ | ρ) N(ρ)`. -/
noncomputable def partialAmplitudeFromPropagatorMatrix {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) (N : ρ → ℝ) (s : σ) : ℝ :=
  ∑ r : ρ, m s r * N r

/-- A generalized-gauge numerator deformation lies in the kernel of the DDM propagator matrix:
`∀ σ, ∑_ρ m(σ | ρ) G(ρ) = 0`. -/
def InPropagatorKernel {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) (G : ρ → ℝ) : Prop :=
  ∀ s : σ, partialAmplitudeFromPropagatorMatrix m G s = 0

/-- The zero numerator deformation is always a generalized-gauge deformation. -/
lemma propagatorKernel_zero {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) : InPropagatorKernel m (fun _ => 0) := by
  intro s
  unfold partialAmplitudeFromPropagatorMatrix
  simp

/-- Generalized-gauge deformations form an additive kernel. -/
lemma propagatorKernel_add {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {G H : ρ → ℝ}
    (hG : InPropagatorKernel m G) (hH : InPropagatorKernel m H) :
    InPropagatorKernel m (fun r => G r + H r) := by
  intro s
  have hGs : (∑ r : ρ, m s r * G r) = 0 := by
    simpa [partialAmplitudeFromPropagatorMatrix] using hG s
  have hHs : (∑ r : ρ, m s r * H r) = 0 := by
    simpa [partialAmplitudeFromPropagatorMatrix] using hH s
  unfold partialAmplitudeFromPropagatorMatrix
  calc
    ∑ r : ρ, m s r * (G r + H r)
        = ∑ r : ρ, (m s r * G r + m s r * H r) := by
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = (∑ r : ρ, m s r * G r) + ∑ r : ρ, m s r * H r := by
          rw [Finset.sum_add_distrib]
    _ = 0 := by rw [hGs, hHs, add_zero]

/-- Shifting numerators by a propagator-matrix kernel vector leaves every color-ordered partial amplitude
unchanged. This formalizes the paper's generalized-gauge freedom in the DDM representation. -/
lemma partialAmplitude_shift_by_kernel {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) (N G : ρ → ℝ) (hG : InPropagatorKernel m G) (s : σ) :
    partialAmplitudeFromPropagatorMatrix m (fun r => N r + G r) s =
      partialAmplitudeFromPropagatorMatrix m N s := by
  have hGs : (∑ r : ρ, m s r * G r) = 0 := by
    simpa [partialAmplitudeFromPropagatorMatrix] using hG s
  unfold partialAmplitudeFromPropagatorMatrix
  calc
    ∑ r : ρ, m s r * (N r + G r)
        = ∑ r : ρ, (m s r * N r + m s r * G r) := by
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = (∑ r : ρ, m s r * N r) + ∑ r : ρ, m s r * G r := by
          rw [Finset.sum_add_distrib]
    _ = ∑ r : ρ, m s r * N r := by rw [hGs, add_zero]

/-- Pointwise form: a generalized-gauge shift preserves the full vector of partial amplitudes. -/
lemma partialAmplitude_shift_by_kernel_ext {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) (N G : ρ → ℝ) (hG : InPropagatorKernel m G) :
    (fun s : σ => partialAmplitudeFromPropagatorMatrix m (fun r => N r + G r) s) =
      fun s : σ => partialAmplitudeFromPropagatorMatrix m N s := by
  funext s
  exact partialAmplitude_shift_by_kernel m N G hG s

/-- Two numerator vectors are generalized-gauge equivalent when they differ by a propagator-kernel vector. -/
def BCJGeneralizedGaugeEquivalent {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) (N N' : ρ → ℝ) : Prop :=
  ∃ G : ρ → ℝ, InPropagatorKernel m G ∧ N' = fun r => N r + G r

/-- Generalized-gauge-equivalent numerators give identical DDM partial amplitudes. -/
lemma generalizedGaugeEquivalent_preserves_partialAmplitude {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {N N' : ρ → ℝ}
    (h : BCJGeneralizedGaugeEquivalent m N N') (s : σ) :
    partialAmplitudeFromPropagatorMatrix m N' s =
      partialAmplitudeFromPropagatorMatrix m N s := by
  rcases h with ⟨G, hG, rfl⟩
  exact partialAmplitude_shift_by_kernel m N G hG s


/-- The negative of a propagator-kernel numerator deformation is again in the kernel. -/
lemma propagatorKernel_neg {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {G : ρ → ℝ} (hG : InPropagatorKernel m G) :
    InPropagatorKernel m (fun r => -G r) := by
  intro s
  have hGs : (∑ r : ρ, m s r * G r) = 0 := by
    simpa [partialAmplitudeFromPropagatorMatrix] using hG s
  unfold partialAmplitudeFromPropagatorMatrix
  calc
    ∑ r : ρ, m s r * (-G r)
        = -(∑ r : ρ, m s r * G r) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = 0 := by rw [hGs, neg_zero]

/-- Difference of two propagator-kernel deformations is again in the kernel. -/
lemma propagatorKernel_sub {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {G H : ρ → ℝ}
    (hG : InPropagatorKernel m G) (hH : InPropagatorKernel m H) :
    InPropagatorKernel m (fun r => G r - H r) := by
  simpa [sub_eq_add_neg] using propagatorKernel_add m hG (propagatorKernel_neg m hH)

/-- Generalized-gauge equivalence is reflexive. -/
lemma generalizedGaugeEquivalent_refl {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) (N : ρ → ℝ) :
    BCJGeneralizedGaugeEquivalent m N N := by
  refine ⟨fun _ => 0, propagatorKernel_zero m, ?_⟩
  funext r
  ring

/-- Generalized-gauge equivalence is symmetric. -/
lemma generalizedGaugeEquivalent_symm {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {N N' : ρ → ℝ}
    (h : BCJGeneralizedGaugeEquivalent m N N') :
    BCJGeneralizedGaugeEquivalent m N' N := by
  rcases h with ⟨G, hG, rfl⟩
  refine ⟨fun r => -G r, propagatorKernel_neg m hG, ?_⟩
  funext r
  ring

/-- Generalized-gauge equivalence is transitive. -/
lemma generalizedGaugeEquivalent_trans {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {N₁ N₂ N₃ : ρ → ℝ}
    (h₁₂ : BCJGeneralizedGaugeEquivalent m N₁ N₂)
    (h₂₃ : BCJGeneralizedGaugeEquivalent m N₂ N₃) :
    BCJGeneralizedGaugeEquivalent m N₁ N₃ := by
  rcases h₁₂ with ⟨G, hG, rfl⟩
  rcases h₂₃ with ⟨H, hH, rfl⟩
  refine ⟨fun r => G r + H r, propagatorKernel_add m hG hH, ?_⟩
  funext r
  ring

/-- Extensional form: generalized-gauge-equivalent numerator vectors define the same full vector of
DDM partial amplitudes. -/
lemma generalizedGaugeEquivalent_preserves_partialAmplitude_ext {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {N N' : ρ → ℝ}
    (h : BCJGeneralizedGaugeEquivalent m N N') :
    (fun s : σ => partialAmplitudeFromPropagatorMatrix m N' s) =
      fun s : σ => partialAmplitudeFromPropagatorMatrix m N s := by
  funext s
  exact generalizedGaugeEquivalent_preserves_partialAmplitude m h s

/-- A three-channel numerator vector `(s,t,u)`. -/
noncomputable def threeChannelNumerator (a b c : ℝ) : Fin 3 → ℝ
  | 0 => a
  | 1 => b
  | 2 => c

/-- The one-row Jacobi matrix imposing the three-channel relation `x_s + x_t + x_u = 0`. -/
def bcjJacobiRow : PUnit → Fin 3 → ℝ :=
  fun _ _ => 1

/-- Membership in the three-channel Jacobi-row kernel is exactly the BCJ Jacobi identity. -/
lemma threeChannelNumerator_in_jacobiKernel_iff (a b c : ℝ) :
    InPropagatorKernel bcjJacobiRow (threeChannelNumerator a b c) ↔ a + b + c = 0 := by
  constructor
  · intro h
    simpa [InPropagatorKernel, partialAmplitudeFromPropagatorMatrix, bcjJacobiRow,
      threeChannelNumerator, Fin.sum_univ_three] using h PUnit.unit
  · intro h s
    cases s
    simpa [partialAmplitudeFromPropagatorMatrix, bcjJacobiRow, threeChannelNumerator,
      Fin.sum_univ_three] using h

/-- The kinematic numerators of a BCJ-dual triple are in the Jacobi-row kernel. -/
lemma bcjDuality_kinematicNumerator_in_jacobiKernel (d : BCJColorKinematicsDuality) :
    InPropagatorKernel bcjJacobiRow (threeChannelNumerator d.n_s d.n_t d.n_u) := by
  rw [threeChannelNumerator_in_jacobiKernel_iff]
  exact d.kinematic_jacobi

/-- The color numerators of a BCJ-dual triple are in the same Jacobi-row kernel. -/
lemma bcjDuality_colorNumerator_in_jacobiKernel (d : BCJColorKinematicsDuality) :
    InPropagatorKernel bcjJacobiRow (threeChannelNumerator d.c_s d.c_t d.c_u) := by
  rw [threeChannelNumerator_in_jacobiKernel_iff]
  exact d.color_jacobi

/-- The kinematic commutator bracket used for the paper's wavy-line Lie algebra. For concrete vector-field
or plane-wave realizations, this is the associative commutator in the selected representation. -/
def kinematicCommutator {A : Type*} [Ring A] (x y : A) : A :=
  ⁅x, y⁆

/-- The kinematic commutator is the ordinary associative commutator. -/
lemma kinematicCommutator_eq_commutator {A : Type*} [Ring A] (x y : A) :
    kinematicCommutator x y = x * y - y * x :=
  Ring.lie_def x y

/-- The kinematic commutator is antisymmetric. -/
lemma kinematicCommutator_antisymm {A : Type*} [Ring A] (x y : A) :
    kinematicCommutator x y = -kinematicCommutator y x := by
  simp only [kinematicCommutator, Ring.lie_def]
  noncomm_ring

/-- The self-commutator vanishes. -/
lemma kinematicCommutator_self {A : Type*} [Ring A] (x : A) :
    kinematicCommutator x x = 0 := by
  simp only [kinematicCommutator, Ring.lie_def]
  noncomm_ring

/-- Jacobi identity for the kinematic commutator. This is the algebraic core behind replacing color
structure constants by kinematic numerators satisfying the same Jacobi relations. -/
lemma kinematicCommutator_jacobi {A : Type*} [Ring A] (x y z : A) :
    kinematicCommutator x (kinematicCommutator y z)
      + kinematicCommutator y (kinematicCommutator z x)
      + kinematicCommutator z (kinematicCommutator x y) = 0 := by
  unfold kinematicCommutator
  simp only [Ring.lie_def]
  noncomm_ring

/-- Algebraic auxiliary-field action `K B² + 2 J B`. In the paper this is the local algebraic pattern used
when integrating in auxiliary fields so that higher interactions are represented by cubic ones. -/
noncomputable def auxiliaryQuadraticAction (K B J : ℝ) : ℝ :=
  K * B ^ 2 + 2 * J * B

/-- The stationary equation for the auxiliary field is `B = -J/K`, when the quadratic coefficient is
invertible. -/
lemma auxiliaryQuadraticAction_stationary_iff (K J B : ℝ) (hK : K ≠ 0) :
    2 * K * B + 2 * J = 0 ↔ B = -J / K := by
  constructor
  · intro h
    field_simp [hK] at h ⊢
    linarith
  · intro h
    subst B
    field_simp [hK]
    ring

/-- Eliminating the stationary auxiliary field produces the effective source term `-J²/K`. -/
lemma auxiliaryQuadraticAction_eliminates (K J B : ℝ) (hK : K ≠ 0)
    (hB : B = -J / K) :
    auxiliaryQuadraticAction K B J = -J ^ 2 / K := by
  subst B
  unfold auxiliaryQuadraticAction
  field_simp [hK]
  ring

/-- Completing the square for the auxiliary-field action. -/
lemma auxiliaryQuadraticAction_completedSquare (K J B : ℝ) (hK : K ≠ 0) :
    auxiliaryQuadraticAction K B J =
      K * (B + J / K) ^ 2 - J ^ 2 / K := by
  unfold auxiliaryQuadraticAction
  field_simp [hK]
  ring


/-- Coefficients of the three nested-bracket channels in a Lie algebra. The additive map `χ` represents
taking a real coefficient, color component, or kinematic component of the bracket expression. -/
noncomputable def lieJacobiChannelNumerator {A : Type*} [LieRing A]
    (χ : A →+ ℝ) (x y z : A) : Fin 3 → ℝ
  | 0 => χ ⁅x, ⁅y, z⁆⁆
  | 1 => χ ⁅y, ⁅z, x⁆⁆
  | 2 => χ ⁅z, ⁅x, y⁆⁆

/-- The coefficient vector of any Lie-Jacobi triple lies in the BCJ Jacobi-row kernel. This is the
standard algebraic reason that both color factors and kinematic numerators can be organized by the same
Jacobi row. -/
lemma lieJacobiChannelNumerator_in_jacobiKernel {A : Type*} [LieRing A]
    (χ : A →+ ℝ) (x y z : A) :
    InPropagatorKernel bcjJacobiRow (lieJacobiChannelNumerator χ x y z) := by
  change InPropagatorKernel bcjJacobiRow
    (threeChannelNumerator (χ ⁅x, ⁅y, z⁆⁆) (χ ⁅y, ⁅z, x⁆⁆) (χ ⁅z, ⁅x, y⁆⁆))
  rw [threeChannelNumerator_in_jacobiKernel_iff]
  have h := congrArg χ (lie_jacobi x y z)
  simpa [map_add] using h


/-- Weighted bilinear pairing over cubic graphs. With weight
`W_Γ = (κ/2)^(n-2)/D_Γ`, this is the finite double-copy amplitude. -/
noncomputable def weightedBilinearAmplitude {Γ : Type*} [Fintype Γ]
    (W N Ñ : Γ → ℝ) : ℝ :=
  ∑ γ : Γ, W γ * N γ * Ñ γ

/-- A shift of the left numerator copy leaves the weighted bilinear amplitude unchanged when the shift is
orthogonal to the right numerator copy under the propagator weight. -/
lemma weightedBilinear_shift_left_of_orthogonal {Γ : Type*} [Fintype Γ]
    (W N Ñ G : Γ → ℝ)
    (hG : weightedBilinearAmplitude W G Ñ = 0) :
    weightedBilinearAmplitude W (fun γ => N γ + G γ) Ñ =
      weightedBilinearAmplitude W N Ñ := by
  unfold weightedBilinearAmplitude at hG ⊢
  calc
    ∑ γ : Γ, W γ * (N γ + G γ) * Ñ γ
        = ∑ γ : Γ, (W γ * N γ * Ñ γ + W γ * G γ * Ñ γ) := by
          apply Finset.sum_congr rfl
          intro γ _
          ring
    _ = (∑ γ : Γ, W γ * N γ * Ñ γ) + ∑ γ : Γ, W γ * G γ * Ñ γ := by
          rw [Finset.sum_add_distrib]
    _ = ∑ γ : Γ, W γ * N γ * Ñ γ := by
          rw [hG, add_zero]

/-- A shift of the right numerator copy leaves the weighted bilinear amplitude unchanged when the shift is
orthogonal to the left numerator copy under the propagator weight. -/
lemma weightedBilinear_shift_right_of_orthogonal {Γ : Type*} [Fintype Γ]
    (W N Ñ G : Γ → ℝ)
    (hG : weightedBilinearAmplitude W N G = 0) :
    weightedBilinearAmplitude W N (fun γ => Ñ γ + G γ) =
      weightedBilinearAmplitude W N Ñ := by
  unfold weightedBilinearAmplitude at hG ⊢
  calc
    ∑ γ : Γ, W γ * N γ * (Ñ γ + G γ)
        = ∑ γ : Γ, (W γ * N γ * Ñ γ + W γ * N γ * G γ) := by
          apply Finset.sum_congr rfl
          intro γ _
          ring
    _ = (∑ γ : Γ, W γ * N γ * Ñ γ) + ∑ γ : Γ, W γ * N γ * G γ := by
          rw [Finset.sum_add_distrib]
    _ = ∑ γ : Γ, W γ * N γ * Ñ γ := by
          rw [hG, add_zero]

/-- The weighted double-copy bilinear form is symmetric in the two numerator copies. -/
lemma weightedBilinear_comm {Γ : Type*} [Fintype Γ]
    (W N Ñ : Γ → ℝ) :
    weightedBilinearAmplitude W N Ñ = weightedBilinearAmplitude W Ñ N := by
  unfold weightedBilinearAmplitude
  apply Finset.sum_congr rfl
  intro γ _
  ring

/-- The finite double-copy amplitude is the weighted bilinear pairing with propagator weight
`(κ/2)^(n-2)/D_Γ`. -/
lemma cubicDoubleCopy_eq_weightedBilinear {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (N Ñ D : Γ → ℝ) :
    cubicDoubleCopyAmplitudeFinite κ n N Ñ D =
      weightedBilinearAmplitude (fun γ => (κ / 2) ^ (n - 2) / D γ) N Ñ := by
  unfold cubicDoubleCopyAmplitudeFinite weightedBilinearAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  ring

/-- Double-copy symmetry: exchanging the two gauge-theory numerator copies leaves the finite amplitude
unchanged. -/
lemma cubicDoubleCopyAmplitudeFinite_comm {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (N Ñ D : Γ → ℝ) :
    cubicDoubleCopyAmplitudeFinite κ n N Ñ D =
      cubicDoubleCopyAmplitudeFinite κ n Ñ N D := by
  rw [cubicDoubleCopy_eq_weightedBilinear, cubicDoubleCopy_eq_weightedBilinear]
  exact weightedBilinear_comm (fun γ => (κ / 2) ^ (n - 2) / D γ) N Ñ

/-- Left-copy generalized-gauge invariance of the finite double copy, stated as the exact weighted
orthogonality condition needed for the shifted numerator to drop out of the bilinear amplitude. -/
lemma cubicDoubleCopy_shift_left_of_orthogonal {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (N Ñ D G : Γ → ℝ)
    (hG : weightedBilinearAmplitude (fun γ => (κ / 2) ^ (n - 2) / D γ) G Ñ = 0) :
    cubicDoubleCopyAmplitudeFinite κ n (fun γ => N γ + G γ) Ñ D =
      cubicDoubleCopyAmplitudeFinite κ n N Ñ D := by
  rw [cubicDoubleCopy_eq_weightedBilinear, cubicDoubleCopy_eq_weightedBilinear]
  exact weightedBilinear_shift_left_of_orthogonal
    (fun γ => (κ / 2) ^ (n - 2) / D γ) N Ñ G hG

/-- Right-copy generalized-gauge invariance of the finite double copy, with the corresponding weighted
orthogonality condition. -/
lemma cubicDoubleCopy_shift_right_of_orthogonal {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (N Ñ D G : Γ → ℝ)
    (hG : weightedBilinearAmplitude (fun γ => (κ / 2) ^ (n - 2) / D γ) N G = 0) :
    cubicDoubleCopyAmplitudeFinite κ n N (fun γ => Ñ γ + G γ) D =
      cubicDoubleCopyAmplitudeFinite κ n N Ñ D := by
  rw [cubicDoubleCopy_eq_weightedBilinear, cubicDoubleCopy_eq_weightedBilinear]
  exact weightedBilinear_shift_right_of_orthogonal
    (fun γ => (κ / 2) ^ (n - 2) / D γ) N Ñ G hG


/-- Finite family of algebraic auxiliary fields. This is the indexed version of the completing-square
pattern used to replace higher interaction terms by cubic interactions plus auxiliary fields. -/
noncomputable def auxiliaryQuadraticActionFinite {ι : Type*} [Fintype ι]
    (K B J : ι → ℝ) : ℝ :=
  ∑ i : ι, auxiliaryQuadraticAction (K i) (B i) (J i)

/-- Eliminating a finite family of stationary auxiliary fields gives the sum of effective source terms
`-Jᵢ²/Kᵢ`. -/
lemma auxiliaryQuadraticActionFinite_eliminates {ι : Type*} [Fintype ι]
    (K B J : ι → ℝ) (hK : ∀ i, K i ≠ 0)
    (hB : ∀ i, B i = -J i / K i) :
    auxiliaryQuadraticActionFinite K B J = ∑ i : ι, -J i ^ 2 / K i := by
  unfold auxiliaryQuadraticActionFinite
  apply Finset.sum_congr rfl
  intro i _
  exact auxiliaryQuadraticAction_eliminates (K i) (J i) (B i) (hK i) (hB i)

/-- Completing the square for a finite family of auxiliary fields. -/
lemma auxiliaryQuadraticActionFinite_completedSquare {ι : Type*} [Fintype ι]
    (K B J : ι → ℝ) (hK : ∀ i, K i ≠ 0) :
    auxiliaryQuadraticActionFinite K B J =
      ∑ i : ι, (K i * (B i + J i / K i) ^ 2 - J i ^ 2 / K i) := by
  unfold auxiliaryQuadraticActionFinite
  apply Finset.sum_congr rfl
  intro i _
  exact auxiliaryQuadraticAction_completedSquare (K i) (J i) (B i) (hK i)


/-! ## J. Mizera: the kinematic Jacobi identity as a residue theorem -/

/-- The common numerator of the rational one-form on the final four-punctured
sphere in Mizera's construction.  Written before collecting denominators,
the one-form coefficient is

`nₛ/(z-zₛ) + nₜ/(z-zₜ) + nᵤ/(z-zᵤ)`.

Putting these three terms over their common cubic denominator gives precisely
this polynomial. -/
noncomputable def mizeraMiddleSphereNumerator
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ) : Polynomial ℂ :=
  C nₛ * (X - C zₜ) * (X - C zᵤ) +
  C nₜ * (X - C zᵤ) * (X - C zₛ) +
  C nᵤ * (X - C zₛ) * (X - C zₜ)

/-- Algebraic simple-pole coefficient of `N(z) /
((z-p)(z-a)(z-b))` at the pole `p`. This is the finite residue
used in Eq. (8) of Mizera's four-puncture reduction. -/
noncomputable def mizeraFiniteResidue
    (N : Polynomial ℂ) (p a b : ℂ) : ℂ :=
  N.eval p / ((p - a) * (p - b))

/-- The quadratic coefficient of the collected middle-sphere numerator is
the sum of its three finite residue labels. -/
lemma mizeraMiddleSphereNumerator_coeff_two
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ) :
    (mizeraMiddleSphereNumerator nₛ nₜ nᵤ zₛ zₜ zᵤ).coeff 2 =
      nₛ + nₜ + nᵤ := by
  simp only [mizeraMiddleSphereNumerator]
  ring_nf
  simp [Polynomial.coeff_X, Polynomial.coeff_C]

/-- The `s`-boundary simple-pole coefficient is exactly `nₛ`. -/
lemma mizeraFiniteResidue_s
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ)
    (hst : zₛ ≠ zₜ) (hsu : zₛ ≠ zᵤ) :
    mizeraFiniteResidue
        (mizeraMiddleSphereNumerator nₛ nₜ nᵤ zₛ zₜ zᵤ)
        zₛ zₜ zᵤ = nₛ := by
  simp [mizeraFiniteResidue, mizeraMiddleSphereNumerator]
  field_simp [sub_ne_zero.mpr hst, sub_ne_zero.mpr hsu]

/-- The `t`-boundary simple-pole coefficient is exactly `nₜ`. -/
lemma mizeraFiniteResidue_t
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ)
    (hts : zₜ ≠ zₛ) (htu : zₜ ≠ zᵤ) :
    mizeraFiniteResidue
        (mizeraMiddleSphereNumerator nₛ nₜ nᵤ zₛ zₜ zᵤ)
        zₜ zᵤ zₛ = nₜ := by
  simp [mizeraFiniteResidue, mizeraMiddleSphereNumerator]
  field_simp [sub_ne_zero.mpr hts, sub_ne_zero.mpr htu]

/-- The `u`-boundary simple-pole coefficient is exactly `nᵤ`. -/
lemma mizeraFiniteResidue_u
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ)
    (hus : zᵤ ≠ zₛ) (hut : zᵤ ≠ zₜ) :
    mizeraFiniteResidue
        (mizeraMiddleSphereNumerator nₛ nₜ nᵤ zₛ zₜ zᵤ)
        zᵤ zₛ zₜ = nᵤ := by
  simp [mizeraFiniteResidue, mizeraMiddleSphereNumerator]
  field_simp [sub_ne_zero.mpr hus, sub_ne_zero.mpr hut]

/-- Equation (8) for the explicit middle-sphere form: its three distinct
boundary residues are exactly the channel numerators. -/
theorem mizera_middleSphere_finite_residues
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ)
    (hst : zₛ ≠ zₜ) (htu : zₜ ≠ zᵤ) (hsu : zₛ ≠ zᵤ) :
    mizeraFiniteResidue
        (mizeraMiddleSphereNumerator nₛ nₜ nᵤ zₛ zₜ zᵤ)
        zₛ zₜ zᵤ = nₛ ∧
    mizeraFiniteResidue
        (mizeraMiddleSphereNumerator nₛ nₜ nᵤ zₛ zₜ zᵤ)
        zₜ zᵤ zₛ = nₜ ∧
    mizeraFiniteResidue
        (mizeraMiddleSphereNumerator nₛ nₜ nᵤ zₛ zₜ zᵤ)
        zᵤ zₛ zₜ = nᵤ :=
  ⟨mizeraFiniteResidue_s nₛ nₜ nᵤ zₛ zₜ zᵤ hst hsu,
    mizeraFiniteResidue_t nₛ nₜ nᵤ zₛ zₜ zᵤ hst.symm htu,
    mizeraFiniteResidue_u nₛ nₜ nᵤ zₛ zₜ zᵤ hsu.symm htu.symm⟩

/-- The residue at infinity of the explicit rational one-form.  Its common
denominator is monic cubic, so the coefficient of `z⁻¹` at infinity is the
quadratic coefficient of the numerator, with the usual opposite orientation. -/
noncomputable def mizeraResidueAtInfinity
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ) : ℂ :=
  -(mizeraMiddleSphereNumerator nₛ nₜ nᵤ zₛ zₜ zᵤ).coeff 2

/-- The global residue theorem for the explicit middle-sphere rational
one-form: the three finite residues plus the residue at infinity vanish. -/
theorem mizera_global_residue_theorem
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ) :
    nₛ + nₜ + nᵤ +
      mizeraResidueAtInfinity nₛ nₜ nᵤ zₛ zₜ zᵤ = 0 := by
  rw [mizeraResidueAtInfinity, mizeraMiddleSphereNumerator_coeff_two]
  ring

/-- Regularity of the explicit middle-sphere differential at infinity. For
this cubic-denominator/quadratic-numerator form it says that its only possible
`z⁻¹` coefficient at infinity vanishes. -/
def MizeraNoPoleAtInfinity
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ) : Prop :=
  mizeraResidueAtInfinity nₛ nₜ nᵤ zₛ zₜ zᵤ = 0

/-- **Mizera's kinematic Jacobi identity is a residue theorem.**
If the final four-punctured-sphere differential has no pole at infinity, its
three finite residues obey `nₛ+nₜ+nᵤ=0`. This is Eq. (9), now derived from the
explicit global-residue identity rather than accepted as a BCJ structure
field. -/
theorem mizera_kinematic_jacobi_of_residue_theorem
    (nₛ nₜ nᵤ zₛ zₜ zᵤ : ℂ)
    (hregular : MizeraNoPoleAtInfinity nₛ nₜ nᵤ zₛ zₜ zᵤ) :
    nₛ + nₜ + nᵤ = 0 := by
  have hglobal :=
    mizera_global_residue_theorem nₛ nₜ nᵤ zₛ zₜ zᵤ
  rw [hregular] at hglobal
  simpa using hglobal

/-- A real Jacobi triple gives a middle-sphere differential regular at
infinity. This is the reverse adapter used for Lie-algebra color factors. -/
lemma mizera_noPoleAtInfinity_of_real_jacobi
    (nₛ nₜ nᵤ : ℝ) (zₛ zₜ zᵤ : ℂ)
    (hjacobi : nₛ + nₜ + nᵤ = 0) :
    MizeraNoPoleAtInfinity
      (nₛ : ℂ) (nₜ : ℂ) (nᵤ : ℂ) zₛ zₜ zᵤ := by
  unfold MizeraNoPoleAtInfinity
  rw [mizeraResidueAtInfinity, mizeraMiddleSphereNumerator_coeff_two]
  exact_mod_cast (neg_eq_zero.mpr hjacobi)

/-- QCD/Yang-Mills color factors obtained by applying a real component to a
Lie-Jacobi triple define a middle-sphere differential with no pole at
infinity. Thus the color Jacobi relation in Eq. (19) and the kinematic Jacobi
relation have the same residue-theorem carrier. -/
theorem mizeraLieColor_noPoleAtInfinity
    {A : Type*} [LieRing A]
    (χ : A →+ ℝ) (x y z : A) (zₛ zₜ zᵤ : ℂ) :
    MizeraNoPoleAtInfinity
      (χ ⁅x, ⁅y, z⁆⁆ : ℂ)
      (χ ⁅y, ⁅z, x⁆⁆ : ℂ)
      (χ ⁅z, ⁅x, y⁆⁆ : ℂ)
      zₛ zₜ zᵤ := by
  apply mizera_noPoleAtInfinity_of_real_jacobi
  have h := congrArg χ (lie_jacobi x y z)
  simpa [map_add] using h

/-- Construct a BCJ color-kinematics duality from two explicit middle-sphere
forms regular at infinity. Both Jacobi fields are derived by the residue
theorem: one for the Lie/color form and one for the kinematic form. -/
noncomputable def mizeraResidueBCJDuality
    (cₛ cₜ cᵤ nₛ nₜ nᵤ : ℝ) (zₛ zₜ zᵤ : ℂ)
    (hcolor : MizeraNoPoleAtInfinity
      (cₛ : ℂ) (cₜ : ℂ) (cᵤ : ℂ) zₛ zₜ zᵤ)
    (hkinematic : MizeraNoPoleAtInfinity
      (nₛ : ℂ) (nₜ : ℂ) (nᵤ : ℂ) zₛ zₜ zᵤ) :
    BCJColorKinematicsDuality where
  c_s := cₛ
  c_t := cₜ
  c_u := cᵤ
  n_s := nₛ
  n_t := nₜ
  n_u := nᵤ
  color_jacobi := by
    exact_mod_cast mizera_kinematic_jacobi_of_residue_theorem
      (cₛ : ℂ) (cₜ : ℂ) (cᵤ : ℂ) zₛ zₜ zᵤ hcolor
  kinematic_jacobi := by
    exact_mod_cast mizera_kinematic_jacobi_of_residue_theorem
      (nₛ : ℂ) (nₜ : ℂ) (nᵤ : ℂ) zₛ zₜ zᵤ hkinematic

/-- The residue-derived color and kinematic vectors land in the repository's
shared Jacobi-row kernel, so all existing cubic-graph gauge and double-copy
amplitude APIs can consume the construction directly. -/
theorem mizeraResidueBCJDuality_in_jacobiKernels
    (cₛ cₜ cᵤ nₛ nₜ nᵤ : ℝ) (zₛ zₜ zᵤ : ℂ)
    (hcolor : MizeraNoPoleAtInfinity
      (cₛ : ℂ) (cₜ : ℂ) (cᵤ : ℂ) zₛ zₜ zᵤ)
    (hkinematic : MizeraNoPoleAtInfinity
      (nₛ : ℂ) (nₜ : ℂ) (nᵤ : ℂ) zₛ zₜ zᵤ) :
    InPropagatorKernel bcjJacobiRow
        (threeChannelNumerator nₛ nₜ nᵤ) ∧
      InPropagatorKernel bcjJacobiRow
        (threeChannelNumerator cₛ cₜ cᵤ) := by
  let d :=
    mizeraResidueBCJDuality
      cₛ cₜ cᵤ nₛ nₜ nᵤ zₛ zₜ zᵤ hcolor hkinematic
  exact ⟨bcjDuality_kinematicNumerator_in_jacobiKernel d,
    bcjDuality_colorNumerator_in_jacobiKernel d⟩

/-- The pointwise all-triples form of Mizera's argument.  An arbitrary
family of graph triples may arise from earlier iterated boundary residues;
once every final `M₀,₄` form is regular at infinity, every corresponding
three-channel numerator vector lies in the BCJ Jacobi-row kernel. -/
theorem mizera_residue_family_in_jacobiKernel
    {ι : Type*} (numerator : ι → Fin 3 → ℝ)
    (zₛ zₜ zᵤ : ι → ℂ)
    (hregular : ∀ i,
      MizeraNoPoleAtInfinity
        (numerator i 0 : ℂ)
        (numerator i 1 : ℂ)
        (numerator i 2 : ℂ)
        (zₛ i) (zₜ i) (zᵤ i)) :
    ∀ i, InPropagatorKernel bcjJacobiRow (numerator i) := by
  intro i
  have hcoordinates :
      numerator i =
        threeChannelNumerator
          (numerator i 0) (numerator i 1) (numerator i 2) := by
    funext j
    fin_cases j <;> rfl
  rw [hcoordinates, threeChannelNumerator_in_jacobiKernel_iff]
  exact_mod_cast mizera_kinematic_jacobi_of_residue_theorem
    (numerator i 0 : ℂ)
    (numerator i 1 : ℂ)
    (numerator i 2 : ℂ)
    (zₛ i) (zₜ i) (zᵤ i) (hregular i)


/-! ## K. Mizera twisted cohomology -/

/-- Algebraic data for the totalized twisted-form complex in Eq. (10).
`dWWedge` represents wedge multiplication by `dW`.  The three laws are the
precise conditions under which `d + ε dW∧` is nilpotent.  The cohomological
degree is intentionally totalized into `V`; concrete graded form models may
forget degree into this carrier. -/
structure MizeraTwistedDifferentialData
    (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- Ordinary exterior differential `d`. -/
  d : V →ₗ[ℂ] V
  /-- Wedge multiplication by the potential one-form `dW`. -/
  dWWedge : V →ₗ[ℂ] V
  /-- Exterior nilpotence `d²=0`. -/
  d_sq : ∀ φ, d (d φ) = 0
  /-- Odd one-form nilpotence `(dW∧)²=0`. -/
  dWWedge_sq : ∀ φ, dWWedge (dWWedge φ) = 0
  /-- Graded anticommutation `d(dW∧)+(dW∧)d=0`. -/
  anticommute : ∀ φ, d (dWWedge φ) + dWWedge (d φ) = 0

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The twisted differential `d + ε dW∧`.  Mizera's two cohomology signs are
the specializations `ε=1` and `ε=-1`. -/
def MizeraTwistedDifferentialData.twistedDifferential
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) : V →ₗ[ℂ] V :=
  D.d + ε • D.dWWedge

@[simp] lemma MizeraTwistedDifferentialData.twistedDifferential_apply
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) (φ : V) :
    D.twistedDifferential ε φ =
      D.d φ + ε • D.dWWedge φ := rfl

/-- Nilpotence of the full twisted differential.  In particular this proves
both `(d+dW∧)²=0` and `(d-dW∧)²=0`. -/
theorem MizeraTwistedDifferentialData.twistedDifferential_sq
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) (φ : V) :
    D.twistedDifferential ε (D.twistedDifferential ε φ) = 0 := by
  simp only [MizeraTwistedDifferentialData.twistedDifferential_apply,
    map_add, map_smul]
  rw [D.d_sq, D.dWWedge_sq, smul_zero, add_zero, zero_add]
  rw [← smul_add, add_comm, D.anticommute, smul_zero]

/-- Mizera's twisted-cohomology relation
`ψ = φ + (d + ε dW∧)ξ`. -/
def MizeraTwistedCohomologous
    (D : MizeraTwistedDifferentialData V)
    (ε : ℂ) (φ ψ : V) : Prop :=
  ∃ ξ, ψ = φ + D.twistedDifferential ε ξ

lemma mizeraTwistedCohomologous_refl
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) (φ : V) :
    MizeraTwistedCohomologous D ε φ φ := by
  refine ⟨0, ?_⟩
  simp

lemma mizeraTwistedCohomologous_symm
    (D : MizeraTwistedDifferentialData V) (ε : ℂ)
    {φ ψ : V} (h : MizeraTwistedCohomologous D ε φ ψ) :
    MizeraTwistedCohomologous D ε ψ φ := by
  rcases h with ⟨ξ, hξ⟩
  refine ⟨-ξ, ?_⟩
  rw [map_neg, hξ]
  abel

lemma mizeraTwistedCohomologous_trans
    (D : MizeraTwistedDifferentialData V) (ε : ℂ)
    {φ ψ χ : V}
    (hφψ : MizeraTwistedCohomologous D ε φ ψ)
    (hψχ : MizeraTwistedCohomologous D ε ψ χ) :
    MizeraTwistedCohomologous D ε φ χ := by
  rcases hφψ with ⟨ξ, hξ⟩
  rcases hψχ with ⟨η, hη⟩
  refine ⟨ξ + η, ?_⟩
  rw [map_add, hη, hξ]
  abel

/-- The setoid of twisted-cohomologous forms. -/
def mizeraTwistedSetoid
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) : Setoid V where
  r := MizeraTwistedCohomologous D ε
  iseqv := ⟨mizeraTwistedCohomologous_refl D ε,
    mizeraTwistedCohomologous_symm D ε,
    mizeraTwistedCohomologous_trans D ε⟩

/-- The actual quotient of totalized forms by Mizera's Eq. (10) exact shifts. -/
abbrev MizeraTwistedCohomology
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) :=
  Quotient (mizeraTwistedSetoid D ε)

/-- The twisted-cohomology class of a form. -/
def mizeraTwistedClass
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) (φ : V) :
    MizeraTwistedCohomology D ε :=
  Quotient.mk _ φ

/-- **Mizera Eq. (10).** Adding `(d+ε dW∧)ξ` does not change
the twisted-cohomology class. -/
theorem mizeraTwistedClass_add_exact
    (D : MizeraTwistedDifferentialData V)
    (ε : ℂ) (φ ξ : V) :
    mizeraTwistedClass D ε φ =
      mizeraTwistedClass D ε
        (φ + D.twistedDifferential ε ξ) :=
  Quotient.sound ⟨ξ, rfl⟩

/-- A form is closed for the selected twisted differential. -/
def MizeraIsTwistedClosed
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) (φ : V) : Prop :=
  D.twistedDifferential ε φ = 0

/-- A form is exact for the selected twisted differential. -/
def MizeraIsTwistedExact
    (D : MizeraTwistedDifferentialData V) (ε : ℂ) (φ : V) : Prop :=
  ∃ ξ, φ = D.twistedDifferential ε ξ

/-- Every twisted-exact form is twisted-closed. -/
theorem mizeraTwistedExact_isClosed
    (D : MizeraTwistedDifferentialData V) (ε : ℂ)
    {φ : V} (h : MizeraIsTwistedExact D ε φ) :
    MizeraIsTwistedClosed D ε φ := by
  rcases h with ⟨ξ, rfl⟩
  exact D.twistedDifferential_sq ε ξ

/-- A residue functional which annihilates twisted-exact forms is
well-defined on twisted cohomology. -/
theorem mizeraResidue_eq_of_twistedCohomologous
    (D : MizeraTwistedDifferentialData V) (ε : ℂ)
    (R : V →ₗ[ℂ] ℂ)
    (hR : ∀ ξ, R (D.twistedDifferential ε ξ) = 0)
    {φ ψ : V} (h : MizeraTwistedCohomologous D ε φ ψ) :
    R φ = R ψ := by
  rcases h with ⟨ξ, rfl⟩
  calc
    R φ = R φ + 0 := by rw [add_zero]
    _ = R φ + R (D.twistedDifferential ε ξ) := by rw [hR]
    _ = R (φ + D.twistedDifferential ε ξ) :=
      (map_add R _ _).symm

/-- All three channel residues, and hence the BCJ numerator vector, are
unchanged under a twisted-exact representative change when each residue
annihilates exact forms. -/
theorem mizeraChannelResidues_eq_of_twistedCohomologous
    (D : MizeraTwistedDifferentialData V) (ε : ℂ)
    (R : Fin 3 → V →ₗ[ℂ] ℂ)
    (hR : ∀ i ξ, R i (D.twistedDifferential ε ξ) = 0)
    {φ ψ : V} (h : MizeraTwistedCohomologous D ε φ ψ) :
    (fun i => R i φ) = fun i => R i ψ := by
  funext i
  exact mizeraResidue_eq_of_twistedCohomologous
    D ε (R i) (hR i) h


/-! ## L. Intersection localization and the four-point amplitude -/

/-- The real three-channel cubic-graph data of Mizera's Eq. (18).  Signed
Mandelstam denominators are accepted here; positivity is not imposed. -/
noncomputable def mizeraFourPointCubicData
    (d : BCJColorKinematicsDuality) (s t u : ℝ) :
    CubicGraphAmplitudeData (Fin 3) where
  color := threeChannelNumerator d.c_s d.c_t d.c_u
  numerator := threeChannelNumerator d.n_s d.n_t d.n_u
  denominator := threeChannelNumerator s t u

/-- **Mizera Eq. (18).** The repository's cubic-graph amplitude specialized
to the single four-point `(s,t,u)` triple is
`nₛcₛ/s+nₜcₜ/t+nᵤcᵤ/u`. -/
theorem mizera_fourPoint_gauge_amplitude
    (d : BCJColorKinematicsDuality) (s t u : ℝ) :
    cubicGraphAmplitude 1 4 (mizeraFourPointCubicData d s t u) =
      d.n_s * d.c_s / s + d.n_t * d.c_t / t +
        d.n_u * d.c_u / u := by
  simp [cubicGraphAmplitude, mizeraFourPointCubicData,
    Fin.sum_univ_three, threeChannelNumerator]
  ring

/-- The leading low-energy intersection-number localization in Eqs. (4)
and (17), expressed without duplicating the repository's weighted BCJ
bilinear. -/
noncomputable def mizeraIntersectionLeadingTerm
    {Γ : Type*} [Fintype Γ]
    (resMinus resPlus denominator : Γ → ℝ) : ℝ :=
  weightedBilinearAmplitude
    (fun γ => 1 / denominator γ) resMinus resPlus

/-- The leading intersection-number localization is exactly the normalized
finite cubic double copy already implemented in this module.  Choosing
`κ=2` removes the conventional overall coupling factor. -/
theorem mizera_intersectionLeadingTerm_eq_doubleCopy
    {Γ : Type*} [Fintype Γ] (n : ℕ)
    (resMinus resPlus denominator : Γ → ℝ) :
    mizeraIntersectionLeadingTerm resMinus resPlus denominator =
      cubicDoubleCopyAmplitudeFinite
        2 n resMinus resPlus denominator := by
  unfold mizeraIntersectionLeadingTerm
  rw [cubicDoubleCopy_eq_weightedBilinear]
  congr 1
  funext γ
  simp

/-- The `Fin 3` specialization of the intersection localization:
the paired boundary residues are summed over the three propagator channels,
which is the explicit four-point form of Eq. (4). -/
theorem mizera_intersectionLeadingTerm_fin3
    (aₛ aₜ aᵤ bₛ bₜ bᵤ s t u : ℝ) :
    mizeraIntersectionLeadingTerm
        (threeChannelNumerator aₛ aₜ aᵤ)
        (threeChannelNumerator bₛ bₜ bᵤ)
        (threeChannelNumerator s t u) =
      aₛ * bₛ / s + aₜ * bₜ / t +
        aᵤ * bᵤ / u := by
  simp [mizeraIntersectionLeadingTerm, weightedBilinearAmplitude,
    Fin.sum_univ_three, threeChannelNumerator]
  ring

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcjDoubleCopy_diagonal_nonneg where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  formalizes @ "claim:the-diagonal-bcj-double-copy-contribution-numerator-squared-over-propagator-is-non-negative-a-positive-graviton-mode-weight"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_gauge_amplitude_single_vanishing where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday_bianchi",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:a-single-propagator-gauge-amplitude-collects-over-a-common-denominator-the-sum-of-color-times-numerator-over-the-propagator-equals-the-sum-of-color-times-numerator-all-over-the-propagator"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement where
  formalizes @ "claim:the-bcj-cubic-double-copy-amplitude-equals-the-cubic-graph-amplitude-with-the-color-factor-replaced-by-the-second-kinematic-numerator-gravity-equals-gauge-squared-by-color-numerator-replacement",
  supported_by @ "paper:bern-carrasco-johansson-perturbative-quantum-gravity-as-a-double-copy-of-gauge-theory"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_doublecopy_fk_factorization where
  formalizes @ "claim:the-exponential-of-a-sum-of-two-imaginary-entropic-actions-factorizes-as-the-product-of-the-two-damping-weights",
  epistemic_status @ "consistency-identity",
  caveat @ "scope:this-is-exp-add-after-a-model-identification-not-by-itself-the-denominated-bcj-amplitude-or-a-construction-of-yang-mills-numerators"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_middleSphere_finite_residues where
  formalizes @ "claim:the-three-boundary-residues-of-the-explicit-final-four-puncture-rational-form-are-exactly-the-s-t-u-channel-numerators",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:this-is-the-explicit-final-M0-4-rational-form-not-a-construction-of-the-full-Deligne-Mumford-compactification-or-twisted-intersection-pairing"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_global_residue_theorem where
  formalizes @ "claim:for-the-explicit-middle-sphere-one-form-the-three-finite-residues-plus-the-residue-at-infinity-vanish",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:the-residue-at-infinity-is-computed-from-the-common-rational-numerator-and-monic-cubic-denominator"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_kinematic_jacobi_of_residue_theorem where
  formalizes @ "claim:regularity-at-infinity-of-the-final-four-puncture-form-derives-the-kinematic-jacobi-identity-n-s-plus-n-t-plus-n-u-equals-zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_global_residue_theorem",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:regularity-at-infinity-is-an-explicit-premise-selected-physical-twisted-forms-and-their-locality-are-not-inferred-from-arbitrary-rational-data"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraLieColor_noPoleAtInfinity where
  formalizes @ "claim:a-real-component-of-a-Lie-Jacobi-color-triple-defines-a-middle-sphere-form-regular-at-infinity-the-QCD-color-and-kinematic-Jacobi-relations-share-the-residue-carrier",
  supported_by @ "lean:lie_jacobi",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:this-is-the-Lie-color-algebra-layer-not-a-choice-of-SU3-representation-running-coupling-or-QCD-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraResidueBCJDuality_in_jacobiKernels where
  formalizes @ "claim:two-regular-middle-sphere-forms-construct-color-and-kinematic-numerators-in-the-same-BCJ-Jacobi-row-kernel-ready-for-the-existing-cubic-graph-double-copy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_kinematic_jacobi_of_residue_theorem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcjDuality_kinematicNumerator_in_jacobiKernel",
  caveat @ "scope:this-constructs-the-final-three-channel-Jacobi-data-not-the-paper's-full-all-multiplicity-twisted-cohomology-catalog"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_residue_family_in_jacobiKernel where
  formalizes @ "claim:any-indexed-family-of-final-four-puncture-forms-regular-at-infinity-gives-a-pointwise-family-of-BCJ-Jacobi-kernel-numerators",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_kinematic_jacobi_of_residue_theorem",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:the-family-theorem-consumes-the-final-M0-4-forms-it-does-not-construct-the-earlier-iterated-residue-map-from-the-full-moduli-space"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.MizeraTwistedDifferentialData.twistedDifferential_sq where
  formalizes @ "claim:mizera's-d-plus-or-minus-dW-wedge-twisted-differential-squares-to-zero",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:the-graded-form-complex-is-totalized-and-the-dW-wedge-map-with-its-nilpotence-and-anticommutation-laws-is-explicit-data-not-a-constructed-CHY-form"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraTwistedClass_add_exact where
  formalizes @ "claim:mizera-equation-10-identifies-forms-related-by-a-d-plus-or-minus-dW-wedge-exact-shift-in-the-twisted-cohomology-quotient",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.MizeraTwistedDifferentialData.twistedDifferential_sq",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:this-constructs-the-algebraic-totalized-quotient-not-the-analytic-Deligne-Mumford-twisted-de-Rham-complex"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraChannelResidues_eq_of_twistedCohomologous where
  formalizes @ "claim:channel-residue-functionals-annihilating-twisted-exact-forms-descend-to-the-twisted-cohomology-quotient",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraTwistedClass_add_exact",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:annihilation-of-exact-shifts-is-an-explicit-premise-for-the-selected-residue-functionals"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_fourPoint_gauge_amplitude where
  formalizes @ "claim:mizera-equation-18-the-four-point-cubic-gauge-amplitude-is-ns-cs-over-s-plus-nt-ct-over-t-plus-nu-cu-over-u",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicGraphAmplitude",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:this-is-the-real-three-channel-carrier-with-signed-denominators-not-the-explicit-CHY-reduced-Pfaffian-numerator-formula"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_intersectionLeadingTerm_eq_doubleCopy where
  formalizes @ "claim:the-leading-low-energy-intersection-residue-pairing-is-the-normalized-existing-finite-cubic-double-copy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_weightedBilinear",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:this-is-the-leading-Lambda-zero-localization-not-the-O-Lambda-minus-two-higher-residue-expansion"

zil attach Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_intersectionLeadingTerm_fin3 where
  formalizes @ "claim:at-four-points-the-leading-intersection-localization-is-the-three-channel-residue-pairing-as-over-s-plus-at-bt-over-t-plus-au-bu-over-u",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_intersectionLeadingTerm_eq_doubleCopy",
  supported_by @ "paper:mizera-2020-kinematic-jacobi-residue-theorem",
  caveat @ "scope:the-residue-vectors-and-three-channel-propagators-are-explicit-inputs-the-full-moduli-space-localization-map-is-not-constructed"

zil_file_contract physlib.colorKinematicsDoubleCopy where
  promises "The Bern-Carrasco-Johansson (BCJ) color-kinematics duality and double copy. Beyond storing Jacobi-compliant data, Mizera's final four-punctured-sphere rational form is explicit: its three finite residues are the channel numerators, its infinity residue is computed from the common numerator, and regularity at infinity derives both the kinematic Jacobi identity and the Lie/QCD color Jacobi identity in the shared propagator-matrix kernel. Mizera's Eq. (10) is represented by an actual totalized twisted-complex quotient, and residue functionals that annihilate exact shifts descend to it. Eq. (18) is the repository's exact three-channel gauge amplitude, while the leading low-energy intersection localization is identified with its existing finite cubic double-copy carrier. A single-propagator gauge amplitude collects over a common denominator. The BCJ cubic double-copy amplitude equals the cubic-graph amplitude with the color factor replaced by a second kinematic numerator, with non-negative diagonal channel weights. Separately, the scalar Feynman-Kac exponential obeys exp-add factorization, and Maxwell-Faraday supplies another concrete kinematic-Jacobi realization."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.BCJColorKinematicsDuality",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.faradayBCJDuality",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraMiddleSphereNumerator",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.MizeraNoPoleAtInfinity",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.MizeraTwistedDifferentialData",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraIntersectionLeadingTerm"]
  forbids_substitutes ["the loop-level generalization of the double copy and the existence of BCJ-satisfying numerators at all multiplicities, which are the cited scattering-amplitudes infrastructure",
    "any claim of perturbative-gravity finiteness, only the tree-level color-kinematics algebra and the factorization identity are carried",
    "calling exp-add alone a denominated amplitude-level double copy",
    "claiming every BCJ kinematic Jacobi is definitionally a Maxwell-Faraday Bianchi identity",
    "claiming the totalized twisted-cohomology quotient and leading residue pairing construct the full Deligne-Mumford compactification, graded analytic wedge complex, CHY/Pfaffian gauge form, higher-residue corrections, or all-multiplicity numerator catalog"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcjDoubleCopy_diagonal_nonneg,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_gauge_amplitude_single_vanishing,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_doublecopy_fk_factorization,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_middleSphere_finite_residues,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_global_residue_theorem,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_kinematic_jacobi_of_residue_theorem,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraLieColor_noPoleAtInfinity,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraResidueBCJDuality_in_jacobiKernels,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_residue_family_in_jacobiKernel,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.MizeraTwistedDifferentialData.twistedDifferential_sq,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraTwistedClass_add_exact,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizeraChannelResidues_eq_of_twistedCohomologous,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_fourPoint_gauge_amplitude,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_intersectionLeadingTerm_eq_doubleCopy,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.mizera_intersectionLeadingTerm_fin3]

/- ZIL-END -/

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

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
* **§D — the double copy as a Feynman–Kac factorization** (`bcj_doublecopy_fk_factorization`). With
  numerators identified as imaginary/entropic actions
  `nᵢ = S_I`, the path-integral weight of the product theory factorizes,
  `exp(−(S₁+S₂)) = exp(−S₁)·exp(−S₂)` — the path-integral form of `M = A₁·A₂`.
* **§E — finite cubic graph and DDM propagator-matrix algebra** from Ben-Shahar–Garozzo–Johansson
  (JHEP 08 (2023) 222, arXiv:2301.00233): the general cubic-graph amplitude, the double copy as color
  replacement, and generalized-gauge freedom as a propagator-matrix kernel statement.
* **§F — Jacobi rows, generalized-gauge equivalence, and auxiliary fields**: kernel negation/subtraction,
  equivalence laws, the three-channel Jacobi row, the kinematic commutator Jacobi identity, and scalar
  auxiliary-field elimination by completing the square.
* **§G — Lie-Jacobi numerator structures**: any real coefficient projection of a Lie-Jacobi triple lies in
  the same BCJ Jacobi-row kernel. This is the shared representative for color and kinematic numerator relations.
* **§H — weighted bilinear double copy**: the finite double-copy amplitude is a weighted bilinear pairing,
  symmetric in the two numerator copies, and invariant under shifts orthogonal to the opposite copy.
* **§I — finite auxiliary-field elimination**: indexed auxiliary fields eliminate to `Σᵢ -Jᵢ²/Kᵢ`, the
  algebraic core of integrating in auxiliary fields to cubicize higher interactions.

This is a port of `reference tree.Integration.BCJBridge`'s self-contained content; the complex-action/entropic-time plugin-slot and
Gravitas dependencies are not imported — only the BCJ amplitude/duality algebra and its link to the
repo's Maxwell sector.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, *New Relations for Gauge-Theory Amplitudes*,
  Phys. Rev. D 78 (2008) 085011, arXiv:0805.3993 (color–kinematics duality and the double copy).
* M. Ben-Shahar, L. Garozzo, H. Johansson, *Lagrangians manifesting color-kinematics duality in the
  NMHV sector of Yang-Mills*, JHEP 08 (2023) 222, arXiv:2301.00233 (DDM kernels, kinematic Lie brackets,
  and auxiliary-field cubicization).
* Repo structure: `PTSymmetricQFT.MaxwellFaraday.faraday_bianchi` (the homogeneous Maxwell / Bianchi identity).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open scoped BigOperators

/-! ## §A — BCJ amplitude data -/

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
theorem bcjDoubleCopy_diagonal_nonneg (t : BCJTriple) :
    0 ≤ t.numerator ^ 2 / t.propagator :=
  div_nonneg (sq_nonneg _) t.prop_pos.le

/-! ## §B — color–kinematics duality -/

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
theorem bcj_gauge_amplitude_single_vanishing
    (d : BCJColorKinematicsDuality) (D : ℝ) (hD : 0 < D) :
    d.c_s * d.n_s / D + d.c_t * d.n_t / D + d.c_u * d.n_u / D =
      (d.c_s * d.n_s + d.c_t * d.n_t + d.c_u * d.n_u) / D := by
  field_simp

/-! ## §C — the kinematic Jacobi is the Maxwell–Bianchi identity -/

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

/-! ## §D — the double copy as a Feynman–Kac factorization -/

/-- **[Double copy = path-integral factorization]** Identifying the BCJ numerators with imaginary/entropic
actions `nᵢ = S_I`, the path-integral (Feynman–Kac) weight of the product theory factorizes:
`exp(−(S₁+S₂)) = exp(−S₁)·exp(−S₂)` — the path-integral realization of `M = A₁·A₂`. -/
theorem bcj_doublecopy_fk_factorization (S₁ S₂ : ℝ) :
    Real.exp (-(S₁ + S₂)) = Real.exp (-S₁) * Real.exp (-S₂) := by
  rw [show -(S₁ + S₂) = -S₁ + -S₂ by ring, Real.exp_add]

/-! ## §E — cubic graphs, DDM propagator matrices, and generalized gauge freedom -/

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
theorem cubicDoubleCopy_eq_cubicAmplitude_colorReplacement {Γ : Type*} [Fintype Γ]
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
theorem propagatorKernel_zero {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) : InPropagatorKernel m (fun _ => 0) := by
  intro s
  unfold partialAmplitudeFromPropagatorMatrix
  simp

/-- Generalized-gauge deformations form an additive kernel. -/
theorem propagatorKernel_add {σ ρ : Type*} [Fintype ρ]
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
theorem partialAmplitude_shift_by_kernel {σ ρ : Type*} [Fintype ρ]
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
theorem partialAmplitude_shift_by_kernel_ext {σ ρ : Type*} [Fintype ρ]
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
theorem generalizedGaugeEquivalent_preserves_partialAmplitude {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {N N' : ρ → ℝ}
    (h : BCJGeneralizedGaugeEquivalent m N N') (s : σ) :
    partialAmplitudeFromPropagatorMatrix m N' s =
      partialAmplitudeFromPropagatorMatrix m N s := by
  rcases h with ⟨G, hG, rfl⟩
  exact partialAmplitude_shift_by_kernel m N G hG s

/-! ## §F — Jacobi rows, generalized-gauge equivalence, and auxiliary fields -/

/-- The negative of a propagator-kernel numerator deformation is again in the kernel. -/
theorem propagatorKernel_neg {σ ρ : Type*} [Fintype ρ]
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
theorem propagatorKernel_sub {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {G H : ρ → ℝ}
    (hG : InPropagatorKernel m G) (hH : InPropagatorKernel m H) :
    InPropagatorKernel m (fun r => G r - H r) := by
  simpa [sub_eq_add_neg] using propagatorKernel_add m hG (propagatorKernel_neg m hH)

/-- Generalized-gauge equivalence is reflexive. -/
theorem generalizedGaugeEquivalent_refl {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) (N : ρ → ℝ) :
    BCJGeneralizedGaugeEquivalent m N N := by
  refine ⟨fun _ => 0, propagatorKernel_zero m, ?_⟩
  funext r
  ring

/-- Generalized-gauge equivalence is symmetric. -/
theorem generalizedGaugeEquivalent_symm {σ ρ : Type*} [Fintype ρ]
    (m : σ → ρ → ℝ) {N N' : ρ → ℝ}
    (h : BCJGeneralizedGaugeEquivalent m N N') :
    BCJGeneralizedGaugeEquivalent m N' N := by
  rcases h with ⟨G, hG, rfl⟩
  refine ⟨fun r => -G r, propagatorKernel_neg m hG, ?_⟩
  funext r
  ring

/-- Generalized-gauge equivalence is transitive. -/
theorem generalizedGaugeEquivalent_trans {σ ρ : Type*} [Fintype ρ]
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
theorem generalizedGaugeEquivalent_preserves_partialAmplitude_ext {σ ρ : Type*} [Fintype ρ]
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
theorem threeChannelNumerator_in_jacobiKernel_iff (a b c : ℝ) :
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
theorem bcjDuality_kinematicNumerator_in_jacobiKernel (d : BCJColorKinematicsDuality) :
    InPropagatorKernel bcjJacobiRow (threeChannelNumerator d.n_s d.n_t d.n_u) := by
  rw [threeChannelNumerator_in_jacobiKernel_iff]
  exact d.kinematic_jacobi

/-- The color numerators of a BCJ-dual triple are in the same Jacobi-row kernel. -/
theorem bcjDuality_colorNumerator_in_jacobiKernel (d : BCJColorKinematicsDuality) :
    InPropagatorKernel bcjJacobiRow (threeChannelNumerator d.c_s d.c_t d.c_u) := by
  rw [threeChannelNumerator_in_jacobiKernel_iff]
  exact d.color_jacobi

/-- The kinematic commutator bracket used for the paper's wavy-line Lie algebra. For concrete vector-field
or plane-wave realizations, this is the associative commutator in the selected representation. -/
def kinematicCommutator {A : Type*} [Ring A] (x y : A) : A :=
  ⁅x, y⁆

/-- The kinematic commutator is the ordinary associative commutator. -/
theorem kinematicCommutator_eq_commutator {A : Type*} [Ring A] (x y : A) :
    kinematicCommutator x y = x * y - y * x :=
  Ring.lie_def x y

/-- The kinematic commutator is antisymmetric. -/
theorem kinematicCommutator_antisymm {A : Type*} [Ring A] (x y : A) :
    kinematicCommutator x y = -kinematicCommutator y x := by
  simp only [kinematicCommutator, Ring.lie_def]
  noncomm_ring

/-- The self-commutator vanishes. -/
theorem kinematicCommutator_self {A : Type*} [Ring A] (x : A) :
    kinematicCommutator x x = 0 := by
  simp only [kinematicCommutator, Ring.lie_def]
  noncomm_ring

/-- Jacobi identity for the kinematic commutator. This is the algebraic core behind replacing color
structure constants by kinematic numerators satisfying the same Jacobi relations. -/
theorem kinematicCommutator_jacobi {A : Type*} [Ring A] (x y z : A) :
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
theorem auxiliaryQuadraticAction_stationary_iff (K J B : ℝ) (hK : K ≠ 0) :
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
theorem auxiliaryQuadraticAction_eliminates (K J B : ℝ) (hK : K ≠ 0)
    (hB : B = -J / K) :
    auxiliaryQuadraticAction K B J = -J ^ 2 / K := by
  subst B
  unfold auxiliaryQuadraticAction
  field_simp [hK]
  ring

/-- Completing the square for the auxiliary-field action. -/
theorem auxiliaryQuadraticAction_completedSquare (K J B : ℝ) (hK : K ≠ 0) :
    auxiliaryQuadraticAction K B J =
      K * (B + J / K) ^ 2 - J ^ 2 / K := by
  unfold auxiliaryQuadraticAction
  field_simp [hK]
  ring

/-! ## §G — Lie-Jacobi numerator structures -/

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
theorem lieJacobiChannelNumerator_in_jacobiKernel {A : Type*} [LieRing A]
    (χ : A →+ ℝ) (x y z : A) :
    InPropagatorKernel bcjJacobiRow (lieJacobiChannelNumerator χ x y z) := by
  change InPropagatorKernel bcjJacobiRow
    (threeChannelNumerator (χ ⁅x, ⁅y, z⁆⁆) (χ ⁅y, ⁅z, x⁆⁆) (χ ⁅z, ⁅x, y⁆⁆))
  rw [threeChannelNumerator_in_jacobiKernel_iff]
  have h := congrArg χ (lie_jacobi x y z)
  simpa [map_add] using h

/-! ## §H — weighted bilinear form of the double copy -/

/-- Weighted bilinear pairing over cubic graphs. With weight
`W_Γ = (κ/2)^(n-2)/D_Γ`, this is the finite double-copy amplitude. -/
noncomputable def weightedBilinearAmplitude {Γ : Type*} [Fintype Γ]
    (W N Ñ : Γ → ℝ) : ℝ :=
  ∑ γ : Γ, W γ * N γ * Ñ γ

/-- A shift of the left numerator copy leaves the weighted bilinear amplitude unchanged when the shift is
orthogonal to the right numerator copy under the propagator weight. -/
theorem weightedBilinear_shift_left_of_orthogonal {Γ : Type*} [Fintype Γ]
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
theorem weightedBilinear_shift_right_of_orthogonal {Γ : Type*} [Fintype Γ]
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
theorem weightedBilinear_comm {Γ : Type*} [Fintype Γ]
    (W N Ñ : Γ → ℝ) :
    weightedBilinearAmplitude W N Ñ = weightedBilinearAmplitude W Ñ N := by
  unfold weightedBilinearAmplitude
  apply Finset.sum_congr rfl
  intro γ _
  ring

/-- The finite double-copy amplitude is the weighted bilinear pairing with propagator weight
`(κ/2)^(n-2)/D_Γ`. -/
theorem cubicDoubleCopy_eq_weightedBilinear {Γ : Type*} [Fintype Γ]
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
theorem cubicDoubleCopyAmplitudeFinite_comm {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (N Ñ D : Γ → ℝ) :
    cubicDoubleCopyAmplitudeFinite κ n N Ñ D =
      cubicDoubleCopyAmplitudeFinite κ n Ñ N D := by
  rw [cubicDoubleCopy_eq_weightedBilinear, cubicDoubleCopy_eq_weightedBilinear]
  exact weightedBilinear_comm (fun γ => (κ / 2) ^ (n - 2) / D γ) N Ñ

/-- Left-copy generalized-gauge invariance of the finite double copy, stated as the exact weighted
orthogonality condition needed for the shifted numerator to drop out of the bilinear amplitude. -/
theorem cubicDoubleCopy_shift_left_of_orthogonal {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (N Ñ D G : Γ → ℝ)
    (hG : weightedBilinearAmplitude (fun γ => (κ / 2) ^ (n - 2) / D γ) G Ñ = 0) :
    cubicDoubleCopyAmplitudeFinite κ n (fun γ => N γ + G γ) Ñ D =
      cubicDoubleCopyAmplitudeFinite κ n N Ñ D := by
  rw [cubicDoubleCopy_eq_weightedBilinear, cubicDoubleCopy_eq_weightedBilinear]
  exact weightedBilinear_shift_left_of_orthogonal
    (fun γ => (κ / 2) ^ (n - 2) / D γ) N Ñ G hG

/-- Right-copy generalized-gauge invariance of the finite double copy, with the corresponding weighted
orthogonality condition. -/
theorem cubicDoubleCopy_shift_right_of_orthogonal {Γ : Type*} [Fintype Γ]
    (κ : ℝ) (n : ℕ) (N Ñ D G : Γ → ℝ)
    (hG : weightedBilinearAmplitude (fun γ => (κ / 2) ^ (n - 2) / D γ) N G = 0) :
    cubicDoubleCopyAmplitudeFinite κ n N (fun γ => Ñ γ + G γ) D =
      cubicDoubleCopyAmplitudeFinite κ n N Ñ D := by
  rw [cubicDoubleCopy_eq_weightedBilinear, cubicDoubleCopy_eq_weightedBilinear]
  exact weightedBilinear_shift_right_of_orthogonal
    (fun γ => (κ / 2) ^ (n - 2) / D γ) N Ñ G hG

/-! ## §I — finite auxiliary-field elimination -/

/-- Finite family of algebraic auxiliary fields. This is the indexed version of the completing-square
pattern used to replace higher interaction terms by cubic interactions plus auxiliary fields. -/
noncomputable def auxiliaryQuadraticActionFinite {ι : Type*} [Fintype ι]
    (K B J : ι → ℝ) : ℝ :=
  ∑ i : ι, auxiliaryQuadraticAction (K i) (B i) (J i)

/-- Eliminating a finite family of stationary auxiliary fields gives the sum of effective source terms
`-Jᵢ²/Kᵢ`. -/
theorem auxiliaryQuadraticActionFinite_eliminates {ι : Type*} [Fintype ι]
    (K B J : ι → ℝ) (hK : ∀ i, K i ≠ 0)
    (hB : ∀ i, B i = -J i / K i) :
    auxiliaryQuadraticActionFinite K B J = ∑ i : ι, -J i ^ 2 / K i := by
  unfold auxiliaryQuadraticActionFinite
  apply Finset.sum_congr rfl
  intro i _
  exact auxiliaryQuadraticAction_eliminates (K i) (J i) (B i) (hK i) (hB i)

/-- Completing the square for a finite family of auxiliary fields. -/
theorem auxiliaryQuadraticActionFinite_completedSquare {ι : Type*} [Fintype ι]
    (K B J : ι → ℝ) (hK : ∀ i, K i ≠ 0) :
    auxiliaryQuadraticActionFinite K B J =
      ∑ i : ι, (K i * (B i + J i / K i) ^ 2 - J i ^ 2 / K i) := by
  unfold auxiliaryQuadraticActionFinite
  apply Finset.sum_congr rfl
  intro i _
  exact auxiliaryQuadraticAction_completedSquare (K i) (J i) (B i) (hK i)

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy

end

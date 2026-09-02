/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HarperFermiPicardFuchs
public import Mathlib.Tactic

/-!
# Algebraic geometry of Harper operators

Lean-checkable core of Dan Li, *The algebraic geometry of Harper operators*
(arXiv:1102.4136v2).

The paper has two different algebraic outcomes.

* In dimension two, every Harper Bloch component has magnetic phases, but
  the phase change `xi = A xi_1`, `eta = B xi_2` identifies it with the
  single normalized Fermi curve
  `xi + xi^{-1} + eta + eta^{-1} = lambda`.  Thus the density-of-states
  period is parameter-independent after normalization.
* In the one-dimensional almost-Mathieu degeneration, the Fermi fibers are
  points.  The parameter remains in the point equation
  `2 cos(2 pi k) + 2 cos(2 pi alpha site) = lambda`, hence in the density
  denominator.

The global ind-pro-variety construction and analytic period existence are
not asserted as hidden theorems.  They are represented by explicit finite
component/index carriers; the file proves the component algebra, phase
normalization, two-dimensional parameter erasure, one-dimensional
parameter-dependent density denominator, and the parity cancellation behind
the zeta-function symmetry.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.HarperAlgebraicGeometry

open Physlib.QuantumMechanics.ComplexAction.HarperFermiPicardFuchs
open Physlib.QuantumMechanics.ComplexAction.IntegerQuantumHallBulkEdge


/-- The unit magnetic phase `exp(i 2 pi theta)`. -/
def magneticPhase (theta : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * theta : ℝ) : ℂ))

/-- Magnetic phases are nonzero, so the Bloch phase change is valid on
`(C*)^2`. -/
lemma magneticPhase_ne_zero (theta : ℝ) : magneticPhase theta ≠ 0 := by
  unfold magneticPhase
  exact Complex.exp_ne_zero _

/-- The `xi_1` phase in the component `B_{m,n}^{k,l}` of the two-dimensional
Harper Bloch variety. -/
def harperPhaseXi (alpha : ℝ) (n l b : ℤ) : ℂ :=
  magneticPhase (alpha * ((n + l * b : ℤ) : ℝ))

/-- The `xi_2` phase in the component `B_{m,n}^{k,l}` of the two-dimensional
Harper Bloch variety. -/
def harperPhaseEta (beta : ℝ) (m k a : ℤ) : ℂ :=
  magneticPhase (beta * ((m + k * a : ℤ) : ℝ))

lemma harperPhaseXi_ne_zero (alpha : ℝ) (n l b : ℤ) :
    harperPhaseXi alpha n l b ≠ 0 :=
  magneticPhase_ne_zero _

lemma harperPhaseEta_ne_zero (beta : ℝ) (m k a : ℤ) :
    harperPhaseEta beta m k a ≠ 0 :=
  magneticPhase_ne_zero _

/-- Li Eq. (17)-style component symbol for the two-dimensional Harper Bloch
variety:
`A xi + A^{-1} xi^{-1} + B eta + B^{-1} eta^{-1}`. -/
def harperComponentSymbol
    (alpha beta : ℝ) (m n k l a b : ℤ) (xi eta : ℂ) : ℂ :=
  harperBlochSymbol
    (harperPhaseXi alpha n l b)
    (harperPhaseEta beta m k a)
    xi eta

/-- Every component of the two-dimensional Harper Bloch variety is carried to
the same normalized Fermi symbol by the phase change. -/
lemma harperComponentSymbol_eq_normalized
    {alpha beta : ℝ} {m n k l a b : ℤ} {xi eta : ℂ}
    (hxi : xi ≠ 0) (heta : eta ≠ 0) :
    harperComponentSymbol alpha beta m n k l a b xi eta =
      normalizedFermiSymbol
        (harperPhaseXi alpha n l b * xi)
        (harperPhaseEta beta m k a * eta) := by
  unfold harperComponentSymbol
  simpa using harperBlochSymbol_eq_normalized
    (harperPhaseXi_ne_zero alpha n l b)
    (harperPhaseEta_ne_zero beta m k a)
    hxi heta

/-- Componentwise algebraic-geometric normalization: the component equation is
equivalent to the same quadratic Fermi curve after the phase change. -/
lemma harperComponentEquation_iff_normalizedQuadratic
    {alpha beta : ℝ} {m n k l a b : ℤ} {xi eta lam : ℂ}
    (hxi : xi ≠ 0) (heta : eta ≠ 0) :
    harperComponentSymbol alpha beta m n k l a b xi eta = lam ↔
      fermiQuadraticPolynomial
        (harperPhaseXi alpha n l b * xi)
        (harperPhaseEta beta m k a * eta)
        lam = 0 := by
  rw [harperComponentSymbol_eq_normalized hxi heta]
  exact normalizedFermiEquation_iff_quadratic
    (mul_ne_zero (harperPhaseXi_ne_zero alpha n l b) hxi)
    (mul_ne_zero (harperPhaseEta_ne_zero beta m k a) heta)


/-- Phase-form fiber equation used in Li Eq. (16)-(17):
`A z_1 + A^{-1}z_1^{-1} + B z_2 + B^{-1}z_2^{-1} - lambda`. -/
def phaseFiberSymbol (A B z1 z2 lam : ℂ) : ℂ :=
  harperBlochSymbol A B z1 z2 - lam

/-- Formal partial derivative of the phase-form fiber with respect to `z_1`. -/
def phaseFiberPartialZ1 (A z1 : ℂ) : ℂ :=
  A - A⁻¹ * z1 ^ (-2 : ℤ)

/-- Formal partial derivative of the phase-form fiber with respect to `z_2`. -/
def phaseFiberPartialZ2 (B z2 : ℂ) : ℂ :=
  B - B⁻¹ * z2 ^ (-2 : ℤ)

/-- The phase-form fiber is the normalized Fermi symbol after Li's phase
change, minus the same energy. -/
lemma phaseFiberSymbol_eq_normalized_sub
    {A B z1 z2 lam : ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) :
    phaseFiberSymbol A B z1 z2 lam =
      normalizedFermiSymbol (A * z1) (B * z2) - lam := by
  unfold phaseFiberSymbol
  rw [harperBlochSymbol_eq_normalized hA hB hz1 hz2]

/-- Li Eq. (18), in phase coordinates: at `lambda = 0`, the fiber is the
union of the two normalized components pulled back by the phase change. -/
lemma phaseFiber_zero_split_iff
    {A B z1 z2 : ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) :
    phaseFiberSymbol A B z1 z2 0 = 0 ↔
      (A * z1) * (B * z2) + 1 = 0 ∨ (A * z1) + (B * z2) = 0 := by
  rw [phaseFiberSymbol_eq_normalized_sub hA hB hz1 hz2]
  simp
  rw [normalizedFermiEquation_iff_quadratic
    (mul_ne_zero hA hz1) (mul_ne_zero hB hz2)]
  exact fermiQuadraticPolynomial_zero_iff (A * z1) (B * z2)


/-- A finite rational approximant has finitely many residue components. -/
abbrev HarperRationalComponentIndex (a b : ℕ) :=
  Fin a × Fin b

/-- The irrational two-dimensional component family has countably many
translation components. -/
abbrev HarperIrrationalTranslationIndex :=
  ℤ × ℤ

/-- The finite rational residue index is an ordinary finite type. -/
instance rationalComponentIndex_fintype (a b : ℕ) :
    Fintype (HarperRationalComponentIndex a b) :=
  inferInstance

/-- The irrational translation index is infinite, matching the paper's
ind-family of components. -/
instance irrationalTranslationIndex_infinite :
    Infinite HarperIrrationalTranslationIndex :=
  inferInstance


/-- A concrete root of unity carrier for the finite covering group `mu_N`. -/
structure HarperRootOfUnity (N : ℕ) where
  val : ℂ
  pow_eq_one : val ^ N = 1

/-- Point of the lifted covering space
`C* × C* × C -> C* × C* × C`, with the nonzero condition kept outside the
carrier so algebraic equalities can be stated directly. -/
structure HarperCoverPoint where
  xi : ℂ
  eta : ℂ
  lam : ℂ

/-- Li's covering map `(z_1,z_2,lambda) ↦ (z_1^a,z_2^b,lambda)`. -/
def harperCover (a b : ℕ) (z1 z2 lam : ℂ) : HarperCoverPoint where
  xi := z1 ^ a
  eta := z2 ^ b
  lam := lam

/-- Multiplying by an `N`-th root of unity does not change the `N`-th power. -/
lemma harperRootAction_power {N : ℕ} (rho : HarperRootOfUnity N) (z : ℂ) :
    (rho.val * z) ^ N = z ^ N := by
  rw [mul_pow, rho.pow_eq_one, one_mul]

/-- The `mu_a × mu_b` action is fiberwise over Li's covering map. -/
lemma harperCover_rootAction_invariant
    {a b : ℕ} (rho : HarperRootOfUnity a) (sigma : HarperRootOfUnity b)
    (z1 z2 lam : ℂ) :
    harperCover a b (rho.val * z1) (sigma.val * z2) lam =
      harperCover a b z1 z2 lam := by
  cases rho with
  | mk rho hrho =>
      cases sigma with
      | mk sigma hsigma =>
          simp [harperCover, mul_pow, hrho, hsigma]

/-- Lifted residue data `(m,n,p,q)` indexing Li's nonsingular lifted
components for fixed `(k,l)`: residues in `Z_a × Z_b` and roots in
`mu_a × mu_b`. -/
abbrev LiftedRootResidueIndex (a b : ℕ) :=
  Fin a × Fin b × Fin a × Fin b

/-- The finite lifted component multiplicity for fixed `(k,l)` is
`a b a b`, before the countable translation indices are added. -/
lemma liftedRootResidueIndex_card (a b : ℕ) :
    Fintype.card (LiftedRootResidueIndex a b) = a * b * a * b := by
  unfold LiftedRootResidueIndex
  simp [Fintype.card_prod]
  ring


/-- A Lean carrier for Li Definition 2.6.  It records only the checked
compatibility datum: horizontal inclusions, vertical projections, and
commuting Cartesian squares.  The geometric hypotheses that the maps are
closed embeddings/surjections/fiber products remain external obligations. -/
structure IndProTypeSystem where
  X : ℕ → ℕ → Type*
  horiz : ∀ i n, X i n → X i (n + 1)
  vert : ∀ i n, X (i + 1) n → X i n
  square_commutes :
    ∀ i n (x : X (i + 1) n),
      vert i (n + 1) (horiz (i + 1) n x) =
        horiz i n (vert i n x)

/-- The defining square of an ind-pro type system commutes on every element. -/
lemma indPro_square_commutes_apply
    (S : IndProTypeSystem) (i n : ℕ) (x : S.X (i + 1) n) :
    S.vert i (n + 1) (S.horiz (i + 1) n x) =
      S.horiz i n (S.vert i n x) :=
  S.square_commutes i n x

/-- The paper's stated line-count formula for the `i`-th blowup stage:
`2(2i+1)ab`.  This is a finite arithmetic carrier, not a proof of analytic
resolution. -/
def harperBlowupLineCount (i a b : ℕ) : ℕ :=
  2 * (2 * i + 1) * a * b

/-- Increasing the symmetric translation window by one raises Li's stated
line count by `4ab`. -/
lemma harperBlowupLineCount_succ (i a b : ℕ) :
    harperBlowupLineCount (i + 1) a b =
      harperBlowupLineCount i a b + 4 * a * b := by
  unfold harperBlowupLineCount
  ring


/-- The two-dimensional Harper density of states obtained from the normalized
Fermi period.  The magnetic parameters are arguments only to state the paper's
parameter-erasure theorem; after normalization the formula is the same
`dosFromQuarterPeriod` from `HarperFermiPicardFuchs`. -/
def twoDimensionalHarperDOS
    (a b _alpha _beta k K : ℝ) : ℝ :=
  dosFromQuarterPeriod a b k K

/-- Substituting the normalized period formula gives
`2 pi^2 a b DOS = (1+k)K(k)`. -/
lemma normalized_twoDimensionalHarperDOS
    {a b alpha beta k K : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    normalizedDOS a b (twoDimensionalHarperDOS a b alpha beta k K) =
      (1 + k) * K := by
  unfold twoDimensionalHarperDOS
  exact normalizedDOS_dosFromQuarterPeriod ha hb

/-- The two-dimensional Harper DOS period is independent of the magnetic
phases after the component normalization. -/
lemma twoDimensionalHarperDOS_parameter_independent
    (a b alpha beta alpha' beta' k K : ℝ) :
    twoDimensionalHarperDOS a b alpha beta k K =
      twoDimensionalHarperDOS a b alpha' beta' k K :=
  rfl

/-- One checked package for the paper's dimension-two point: a component
Bloch equation is normalized to the phase-free Fermi curve and the resulting
DOS formula contains no magnetic phase parameter. -/
lemma harperComponent_normalization_and_DOS
    {alpha beta : ℝ} {m n k l a b : ℤ} {xi eta lam : ℂ}
    {cellA cellB modulus K : ℝ}
    (hxi : xi ≠ 0) (heta : eta ≠ 0)
    (hcellA : cellA ≠ 0) (hcellB : cellB ≠ 0)
    (hcomponent : harperComponentSymbol alpha beta m n k l a b xi eta = lam) :
    normalizedFermiSymbol
        (harperPhaseXi alpha n l b * xi)
        (harperPhaseEta beta m k a * eta) = lam
      ∧ normalizedDOS cellA cellB
          (twoDimensionalHarperDOS cellA cellB alpha beta modulus K)
        = (1 + modulus) * K := by
  constructor
  · simpa [harperComponentSymbol_eq_normalized hxi heta] using hcomponent
  · exact normalized_twoDimensionalHarperDOS hcellA hcellB


/-- Li's elliptic modulus `k = (4 - |lambda|)/(4 + |lambda|)`. -/
def harperEllipticModulus (lambda : ℝ) : ℝ :=
  (4 - |lambda|) / (4 + |lambda|)

/-- The per-component DOS formula of Li Theorem 2.12, expressed through the
already-existing normalized quarter-period carrier. -/
def harperPerComponentDOS (a b lambda K : ℝ) : ℝ :=
  dosFromQuarterPeriod a b (harperEllipticModulus lambda) K

/-- Li Theorem 2.12 in normalized form:
`2 pi^2 a b DOS = (1+k)K(k)` with `k=(4-|lambda|)/(4+|lambda|)`. -/
lemma normalized_harperPerComponentDOS
    {a b lambda K : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    normalizedDOS a b (harperPerComponentDOS a b lambda K) =
      (1 + harperEllipticModulus lambda) * K := by
  unfold harperPerComponentDOS
  exact normalizedDOS_dosFromQuarterPeriod ha hb

/-- Li's second Theorem 2.12 expression uses the Landen modulus
`2 sqrt(k)/(1+k)`.  The repo stores it as `landenModulusFromRoot`. -/
def harperLandenModulusFromRoot (root lambda : ℝ) : ℝ :=
  landenModulusFromRoot root (harperEllipticModulus lambda)

/-- The Harper elliptic modulus plugs into the Picard-Fuchs/Landen identity
already formalized in the Fermi-curve file. -/
lemma harper_landen_square_sum
    {root lambda : ℝ}
    (hroot : root ^ 2 = harperEllipticModulus lambda)
    (hden : 1 + harperEllipticModulus lambda ≠ 0) :
    (harperLandenModulusFromRoot root lambda) ^ 2
      + (landenComplement (harperEllipticModulus lambda)) ^ 2 = 1 := by
  unfold harperLandenModulusFromRoot
  exact landen_square_sum hroot hden


/-- The site-dependent almost-Mathieu potential `2 cos(2 pi alpha site)`. -/
def almostMathieuPotential (alpha : ℝ) (site : ℤ) : ℝ :=
  2 * Real.cos (2 * Real.pi * alpha * (site : ℝ))

/-- The one-dimensional almost-Mathieu Bloch symbol
`xi + xi^{-1} + 2 cos(2 pi alpha site)`. -/
def almostMathieuBlochSymbol (alpha : ℝ) (site : ℤ) (xi : ℂ) : ℂ :=
  xi + xi⁻¹ + (almostMathieuPotential alpha site : ℂ)

/-- Polynomial form of the almost-Mathieu point Fermi equation after
multiplying by `xi`. -/
def almostMathieuQuadratic (alpha : ℝ) (site : ℤ) (xi lam : ℂ) : ℂ :=
  xi ^ 2 + ((almostMathieuPotential alpha site : ℂ) - lam) * xi + 1

/-- The almost-Mathieu Fermi fiber equation is a quadratic point equation on
`C*`, not a two-dimensional curve. -/
lemma almostMathieuBlochEquation_iff_quadratic
    {alpha : ℝ} {site : ℤ} {xi lam : ℂ} (hxi : xi ≠ 0) :
    almostMathieuBlochSymbol alpha site xi = lam ↔
      almostMathieuQuadratic alpha site xi lam = 0 := by
  constructor
  · intro h
    unfold almostMathieuBlochSymbol at h
    unfold almostMathieuQuadratic
    field_simp [hxi] at h ⊢
    ring_nf at h ⊢
    linear_combination h
  · intro h
    unfold almostMathieuQuadratic at h
    unfold almostMathieuBlochSymbol
    field_simp [hxi] at h ⊢
    ring_nf at h ⊢
    linear_combination h

/-- The real almost-Mathieu band function
`E_site(k) = 2 cos(2 pi k) + 2 cos(2 pi alpha site)`. -/
def almostMathieuBandEnergy (alpha : ℝ) (site : ℤ) (k : ℝ) : ℝ :=
  2 * Real.cos (2 * Real.pi * k)
    + 2 * Real.cos (2 * Real.pi * alpha * (site : ℝ))

/-- The parameter-dependent square-root kernel appearing in the almost-Mathieu
density denominator. -/
def almostMathieuDensityKernel (alpha lambda : ℝ) (site : ℤ) : ℝ :=
  1 - (lambda / 2 - Real.cos (2 * Real.pi * alpha * (site : ℝ))) ^ 2

/-- If `k` is a point of the almost-Mathieu Fermi fiber, then the square of
the velocity denominator is exactly the parameter-dependent density kernel.
This is the checked algebra behind Li Eq. (59)-(60). -/
lemma almostMathieu_density_denominator_sq
    {alpha lambda k : ℝ} {site : ℤ}
    (h : almostMathieuBandEnergy alpha site k = lambda) :
    (4 * Real.pi * Real.sin (2 * Real.pi * k)) ^ 2 =
      16 * Real.pi ^ 2 * almostMathieuDensityKernel alpha lambda site := by
  have hcos :
      Real.cos (2 * Real.pi * k) =
        lambda / 2 - Real.cos (2 * Real.pi * alpha * (site : ℝ)) := by
    unfold almostMathieuBandEnergy at h
    nlinarith
  have hsin :
      Real.sin (2 * Real.pi * k) ^ 2 =
        1 - Real.cos (2 * Real.pi * k) ^ 2 := by
    have htrig := Real.sin_sq_add_cos_sq (2 * Real.pi * k)
    nlinarith
  unfold almostMathieuDensityKernel
  calc
    (4 * Real.pi * Real.sin (2 * Real.pi * k)) ^ 2
        = 16 * Real.pi ^ 2 * Real.sin (2 * Real.pi * k) ^ 2 := by ring
    _ = 16 * Real.pi ^ 2 * (1 - Real.cos (2 * Real.pi * k) ^ 2) := by rw [hsin]
    _ = 16 * Real.pi ^ 2 *
          (1 - (lambda / 2 - Real.cos (2 * Real.pi * alpha * (site : ℝ))) ^ 2) := by
        rw [hcos]


/-- Laurent exponent `k_1-k_2` in Li Eq. (61). -/
def almostMathieuLaurentExponent (k1 k2 : ℕ) : ℤ :=
  (k1 : ℤ) - (k2 : ℤ)

/-- The residue case `k_1-k_2=0` is exactly `k_1=k_2`. -/
lemma almostMathieuLaurentExponent_eq_zero_iff (k1 k2 : ℕ) :
    almostMathieuLaurentExponent k1 k2 = 0 ↔ k1 = k2 := by
  unfold almostMathieuLaurentExponent
  omega

/-- The residue case `k_1-k_2=1` is exactly `k_1=k_2+1`. -/
lemma almostMathieuLaurentExponent_eq_one_iff (k1 k2 : ℕ) :
    almostMathieuLaurentExponent k1 k2 = 1 ↔ k1 = k2 + 1 := by
  unfold almostMathieuLaurentExponent
  omega

/-- Li Eq. (61): only the two residue exponents `0` and `1` contribute. -/
def almostMathieuResidueSurvives (k1 k2 : ℕ) : Prop :=
  almostMathieuLaurentExponent k1 k2 = 0
    ∨ almostMathieuLaurentExponent k1 k2 = 1

/-- The two surviving almost-Mathieu residue cases are precisely the paper's
`k_1-k_2=0` and `k_1-k_2=1` alternatives. -/
lemma almostMathieuResidueSurvives_iff (k1 k2 : ℕ) :
    almostMathieuResidueSurvives k1 k2 ↔
      k1 = k2 ∨ k1 = k2 + 1 := by
  unfold almostMathieuResidueSurvives
  rw [almostMathieuLaurentExponent_eq_zero_iff,
    almostMathieuLaurentExponent_eq_one_iff]

/-- In the `k_1=k_2` residue case, the total multinomial degree has the
even-pair form used in the first sum after Li Eq. (61). -/
lemma almostMathieuResidue_degree_zero
    {n k1 k2 k3 : ℕ} (hpair : k1 = k2) (hdeg : k1 + k2 + k3 = n) :
    n = 2 * k2 + k3 := by
  omega

/-- In the `k_1=k_2+1` residue case, the total multinomial degree has the
odd-pair form used in the second sum after Li Eq. (61). -/
lemma almostMathieuResidue_degree_one
    {n k1 k2 k3 : ℕ} (hpair : k1 = k2 + 1) (hdeg : k1 + k2 + k3 = n) :
    n = 2 * k2 + 1 + k3 := by
  omega


/-- Odd powers cancel between the symmetric energies `lambda` and `-lambda`,
which is the algebraic reason the two-dimensional Harper zeta contribution
vanishes at odd positive integers. -/
lemma odd_power_pair_cancel (lambda : ℝ) (r : ℕ) :
    lambda ^ (2 * r + 1) + (-lambda) ^ (2 * r + 1) = 0 := by
  have hodd : Odd (2 * r + 1) := by
    exact ⟨r, by ring⟩
  rw [hodd.neg_pow]
  ring

/-- Even powers double between the symmetric energies `lambda` and `-lambda`. -/
lemma even_power_pair_double (lambda : ℝ) (r : ℕ) :
    lambda ^ (2 * r) + (-lambda) ^ (2 * r) = 2 * lambda ^ (2 * r) := by
  have heven : Even (2 * r) := by
    exact ⟨r, by ring⟩
  rw [heven.neg_pow]
  ring

/-- Finite formal partition-function truncation from zeta coefficients.  This
is the finite Lean carrier for Li's formal series before passing to the
component limit. -/
def formalPartitionTruncation (zeta : ℕ → ℝ) (t : ℝ) (N : ℕ) : ℝ :=
  ∑ n : Fin N, zeta n * (-t) ^ n.val / (n.val.factorial : ℝ)

/-- If two zeta coefficient functions agree through a truncation, their finite
formal partition truncations agree. -/
lemma formalPartitionTruncation_congr
    {zeta zeta' : ℕ → ℝ} {t : ℝ} {N : ℕ}
    (h : ∀ n : Fin N, zeta n.val = zeta' n.val) :
    formalPartitionTruncation zeta t N =
      formalPartitionTruncation zeta' t N := by
  unfold formalPartitionTruncation
  exact Finset.sum_congr rfl fun n _ => by rw [h n]

end Physlib.QuantumMechanics.ComplexAction.HarperAlgebraicGeometry

end

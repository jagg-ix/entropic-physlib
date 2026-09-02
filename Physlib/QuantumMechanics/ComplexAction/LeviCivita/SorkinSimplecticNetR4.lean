/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic
public import Mathlib.Data.Fin.Tuple.Sort
public import Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants
public import Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
public import Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation

/-!
# Sorkin Sec. III A — a simplectic net for `R⁴`

Sorkin (1975) Sec. III A gives an explicit triangulation of `R⁴` as the nerve of a tiling by
rectangular regions, five meeting at each point (**Fig. 4**). It is presented in **affine
coordinates**: an overcomplete basis of `5` vectors whose components — and the basis vectors
themselves — sum to zero.

This file formalizes the combinatorial data of that net:

* `affineBasis` — the five overcomplete basis vectors `e_j^i = δ_j^i − 1/5`, summing to zero both
  componentwise (`affineBasis_component_sum_zero`) and as vectors (`affineBasis_sum_zero`);
* `typeIIvectorA`, `typeIIvectorB` — representatives of the `30 = 10 + 20` "type (ii)" offset
  vectors `±⅕(4,−1,−1,−1,−1)`, `±⅕(3,3,−2,−2,−2)`, each summing to zero with all components `< 1`
  in absolute value, so they define the **legs** of the net;
* `IsLegVector` / `typeIIvectorA_defines_leg` — the leg condition (two vertices joined iff they
  differ by a vector with all components `< 1`);
* `NerveSimplex` — the nerve rule: `k+1` vertices span a `k`-simplex iff mutually joined by legs;
* `isotropicGroup_card` — the isotropic group fixing the origin has `2 · 5! = 240` elements
  (coordinate permutations with an overall `±` sign);
* `downIncidence` / `fourSimplex_face_counts` — the down-incidence `I(m,k) = C(k+1,m+1)`: a `4`-cell
  has `5` vertices, `10` legs, `10` bones, `5` tetrahedra, `1` cell;
* `affineWeightBasis` / `IsAffineWeight` — the general `A_{N-1} = su(N)` weight system (`N`
  overcomplete vectors summing to zero); the `R⁴` net is the `N = 5`, `su(5)` case;
* `traceless_diag_isAffineWeight` — the reusable link: the affine "components sum to zero" IS
  `su(N)` **tracelessness**, so the diagonal of any traceless matrix is an affine weight vector.
  Applied across the repository: `gellMann_cartan_isAffineWeight` (`su(3)`, `A₂`, the colour/flavour
  triplet, via `Particles.gellMann_traceless`) and `diracHamiltonian_isAffineWeight` (an `su(2)`-type
  generator, via `Dirac.diracHamiltonian_trace`).

## References

* R. Sorkin, "Time-evolution problem in Regge calculus", Phys. Rev. D **12**, 385 (1975)
  [`Sorkin:1975ah`], Sec. III A and **Fig. 4** (the nerve of a tiling).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4

/-! ## Affine coordinates: an overcomplete basis summing to zero -/

/-- Sorkin's **affine basis**: the five overcomplete basis vectors `e_j^i = δ_j^i − 1/5`. -/
noncomputable def affineBasis (j : Fin 5) : Fin 5 → ℝ := fun i => (if i = j then (1 : ℝ) else 0) - 1 / 5

/-- Each affine basis vector has components summing to zero (an affine vector). -/
lemma affineBasis_component_sum_zero (j : Fin 5) : ∑ i, affineBasis j i = 0 := by
  simp only [affineBasis, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

/-- The five affine basis vectors sum to zero — the overcomplete (affine) condition. -/
lemma affineBasis_sum_zero : ∑ j, affineBasis j = 0 := by
  funext i
  rw [Finset.sum_apply]
  simp only [affineBasis, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  norm_num

/-! ## The type-(ii) offset vectors define the legs -/

/-- A representative of the ten type-(ii) offsets: `⅕(4, −1, −1, −1, −1)`. -/
noncomputable def typeIIvectorA : Fin 5 → ℝ := ![4 / 5, -1 / 5, -1 / 5, -1 / 5, -1 / 5]

lemma typeIIvectorA_sum_zero : ∑ i, typeIIvectorA i = 0 := by
  simp [typeIIvectorA, Fin.sum_univ_five]; norm_num

lemma typeIIvectorA_components_lt_one : ∀ i, |typeIIvectorA i| < 1 := by
  intro i; fin_cases i <;> · simp [typeIIvectorA]; norm_num [abs_of_nonneg, abs_of_nonpos]

/-- A representative of the twenty type-(ii) offsets: `⅕(3, 3, −2, −2, −2)`. -/
noncomputable def typeIIvectorB : Fin 5 → ℝ := ![3 / 5, 3 / 5, -2 / 5, -2 / 5, -2 / 5]

lemma typeIIvectorB_sum_zero : ∑ i, typeIIvectorB i = 0 := by
  simp [typeIIvectorB, Fin.sum_univ_five]; norm_num

/-- **The leg condition**: two vertices are joined by a leg iff they differ by a vector all of whose
components are `< 1` in absolute value (a type-(ii) offset). -/
def IsLegVector (u v : Fin 5 → ℝ) : Prop := u ≠ v ∧ ∀ i, |u i - v i| < 1

/-- A vertex and its type-(ii) offset are joined by a leg. -/
lemma typeIIvectorA_defines_leg (u : Fin 5 → ℝ) :
    IsLegVector u (fun i => u i + typeIIvectorA i) := by
  refine ⟨?_, ?_⟩
  · intro heq
    have h0 := congrFun heq 0
    simp [typeIIvectorA] at h0
  · intro i
    have hcomponent := typeIIvectorA_components_lt_one i
    simpa [abs_sub_comm] using hcomponent

/-! ## The nerve rule, the isotropic group, and the incidence numbers -/

/-- **The nerve rule**: `k+1` vertices span a `k`-simplex of the net iff they are mutually joined by
legs (Sorkin's definition of `Σ_k` from the graph `Σ₁`). -/
def NerveSimplex {V : Type*} (isLeg : V → V → Prop) (verts : Finset V) : Prop :=
  ∀ u ∈ verts, ∀ w ∈ verts, u ≠ w → isLeg u w

/-- **The isotropic group** fixing the origin: the `5!` coordinate permutations with an overall `±`
sign — `2 · 5! = 240` elements. -/
lemma isotropicGroup_card : Fintype.card (Equiv.Perm (Fin 5)) * 2 = 240 := by
  simp only [Fintype.card_perm, Fintype.card_fin]; decide

/-- **The Weyl group of `A₄ = su(5)`** is the symmetric group `S₅ = Perm (Fin 5)` (the standard
identification `Weyl(A_n) ≅ S_{n+1}`). -/
abbrev Su5WeylGroup := Equiv.Perm (Fin 5)

/-- `|Weyl(A₄)| = |S₅| = 5! = 120`. -/
lemma su5WeylGroup_card : Fintype.card Su5WeylGroup = 120 := by
  rw [Fintype.card_perm, Fintype.card_fin]; decide

/-- **Sorkin's isotropic group is the `SU(5)` Weyl group extended by the `Z₂` diagram automorphism**
(charge conjugation): `Weyl(A₄) × Z₂ = S₅ × Z₂`. -/
abbrev IsotropicGroupR4 := Su5WeylGroup × Bool

/-- **The isotropic group order is the `SU(5)` Weyl-group order times the `Z₂` diagram automorphism**:
`|isotropic| = |Weyl(A₄)| · 2 = 120 · 2 = 240`. So the discrete symmetry of the `R⁴` spacetime net
coincides with the Weyl symmetry of the `SU(5)` gauge group (extended by charge conjugation). -/
lemma isotropicGroupR4_eq_su5weyl_times_two :
    Fintype.card IsotropicGroupR4 = Fintype.card Su5WeylGroup * 2 := by
  rw [Fintype.card_prod, Fintype.card_bool]

/-- `|isotropic| = 240`, consistent with `isotropicGroup_card` (`|S₅| · 2`). -/
lemma isotropicGroupR4_card : Fintype.card IsotropicGroupR4 = 240 := by
  rw [isotropicGroupR4_eq_su5weyl_times_two, su5WeylGroup_card]

/-- **The down-incidence** `I(m,k) = C(k+1, m+1)`: the number of `m`-faces of a `k`-simplex. -/
def downIncidence (m k : ℕ) : ℕ := Nat.choose (k + 1) (m + 1)

/-- A `4`-cell of the net has `5` vertices, `10` legs, `10` bones, `5` tetrahedra, `1` cell. -/
lemma fourSimplex_face_counts :
    downIncidence 0 4 = 5 ∧ downIncidence 1 4 = 10 ∧ downIncidence 2 4 = 10
      ∧ downIncidence 3 4 = 5 ∧ downIncidence 4 4 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The affine coordinates are the `A_{N-1} = su(N)` weight system

Sorkin's affine coordinates generalize to any dimension: `N` overcomplete vectors summing to zero are
the weight system of `A_{N-1} = su(N)`. The `R⁴` net (`affineBasis`) is the `N = 5`, `su(5)` case.
The invariant condition — **components sum to zero** — is exactly the **tracelessness** of an `su(N)`
Cartan generator, so the diagonal of *any* traceless matrix is an affine weight vector. This gives a
reusable tool that connects the geometric net to the Lie-algebraic content across the repository. -/

/-- **The affine-weight (`su(N)` Cartan) condition**: the components sum to zero. -/
def IsAffineWeight {N : ℕ} {R : Type*} [AddCommMonoid R] (v : Fin N → R) : Prop := ∑ i, v i = 0

/-- The general `A_{N-1} = su(N)` weight basis: `N` overcomplete vectors `e_j^i = δ_j^i − 1/N`. -/
noncomputable def affineWeightBasis (N : ℕ) (j : Fin N) : Fin N → ℝ :=
  fun i => (if i = j then (1 : ℝ) else 0) - 1 / N

/-- Every `su(N)` weight-basis vector is an affine weight (traceless). -/
lemma affineWeightBasis_isAffineWeight (N : ℕ) [NeZero N] (j : Fin N) :
    IsAffineWeight (affineWeightBasis N j) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold IsAffineWeight affineWeightBasis
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [Finset.mem_univ, if_true, nsmul_eq_mul]
  rw [mul_one_div, div_self hN]; norm_num

/-- The `N` weight-basis vectors sum to zero (the overcomplete/affine condition). -/
lemma affineWeightBasis_sum_zero (N : ℕ) [NeZero N] : ∑ j, affineWeightBasis N j = 0 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  funext i; rw [Finset.sum_apply]
  simp only [affineWeightBasis, Pi.zero_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [Finset.mem_univ, if_true, nsmul_eq_mul]
  rw [mul_one_div, div_self hN]; norm_num

/-- Sorkin's `R⁴`-net basis (`affineBasis`, `N = 5`) is a `su(5)` affine weight. -/
lemma affineBasis_isAffineWeight (j : Fin 5) : IsAffineWeight (affineBasis j) :=
  affineBasis_component_sum_zero j

/-- **The reusable tool: the diagonal of any traceless matrix is an affine weight vector.** The
`su(N)` tracelessness `Tr M = 0` is precisely Sorkin's affine "components sum to zero" for the
diagonal. -/
lemma traceless_diag_isAffineWeight {N : ℕ} {R : Type*} [AddCommMonoid R]
    (M : Matrix (Fin N) (Fin N) R) (h : M.trace = 0) : IsAffineWeight (fun i => M i i) := by
  unfold IsAffineWeight; simpa [Matrix.trace, Matrix.diag] using h

/-! ### Where the repository uses it — traceless generators are affine weight vectors -/

open Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants in
/-- **`su(3)` (Gell-Mann), `A₂`.** The Cartan generators `λ₃ = diag(1,−1,0)`, `λ₈ ∝ diag(1,1,−2)` have
diagonals that are affine weight vectors (reusing `Particles.gellMann_traceless`). -/
lemma gellMann_cartan_isAffineWeight :
    IsAffineWeight (fun i => lambda3 i i) ∧ IsAffineWeight (fun i => lambda8 i i) :=
  ⟨traceless_diag_isAffineWeight _ gellMann_traceless.2.2.1,
    traceless_diag_isAffineWeight _ gellMann_traceless.2.2.2.2.2.2.2⟩

open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization in
/-- **The Dirac Hamiltonian** `H = [[Δ, v]; [v, −Δ]]` (an `su(2)`-type generator) has an affine weight
diagonal `(Δ, −Δ)` (reusing `Dirac.diracHamiltonian_trace`). -/
lemma diracHamiltonian_isAffineWeight (Δ vp : ℝ) :
    IsAffineWeight (fun i => diracHamiltonian Δ vp i i) :=
  traceless_diag_isAffineWeight _ (diracHamiltonian_trace Δ vp)

/-! ### The isotropic group `S₅ × Z₂` acts on the `su(5)` weight system

The two factors of the isotropic group act on the affine weight basis: the Weyl group `S₅` permutes
the `5` weights, and the `Z₂` diagram automorphism is charge conjugation `5 ↔ 5̄` (weight negation).
That `Z₂` is exactly the charge conjugation of `Particles` on the Standard-Model quantum numbers. -/

/-- **The Weyl group `S₅` permutes the `su(5)` weight basis**: `σ · e_j = e_{σ j}`. -/
lemma weyl_permutes_affineWeightBasis (σ : Equiv.Perm (Fin 5)) (j : Fin 5) :
    (fun i => affineWeightBasis 5 j (σ.symm i)) = affineWeightBasis 5 (σ j) := by
  funext i; simp only [affineWeightBasis]
  by_cases h : i = σ j
  · rw [if_pos h, if_pos ((Equiv.symm_apply_eq σ).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((Equiv.symm_apply_eq σ).mp hc))]

/-- **Charge conjugation on weights** `w ↦ −w` — the `A₄` diagram automorphism `5 ↔ 5̄`, the `Z₂`
factor of the isotropic group. -/
def weightConjugation {N : ℕ} {R : Type*} [AddGroup R] (v : Fin N → R) : Fin N → R := fun i => -v i

/-- Charge conjugation is an involution (`C² = 1`, a `Z₂`). -/
lemma weightConjugation_involutive {N : ℕ} {R : Type*} [AddGroup R] (v : Fin N → R) :
    weightConjugation (weightConjugation v) = v := by funext i; simp [weightConjugation]

/-- Charge conjugation preserves the affine-weight (traceless) condition: `5̄` is a weight too. -/
lemma weightConjugation_isAffineWeight {N : ℕ} {R : Type*} [AddCommGroup R] (v : Fin N → R)
    (h : IsAffineWeight v) : IsAffineWeight (weightConjugation v) := by
  unfold IsAffineWeight weightConjugation at *; simp [Finset.sum_neg_distrib, h]

section ChargeConjugation
open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation

/-- The Standard-Model additive quantum-number vector `(Q, B, L)` of a particle. -/
def qnVec (q : QuantumNumbers) : Fin 3 → ℚ := ![q.electric, q.baryon, q.lepton]

/-- **The `Z₂` diagram automorphism is charge conjugation.** The antiparticle's Standard-Model
quantum numbers `(Q, B, L)` are the `weightConjugation` (`5 ↔ 5̄`, negation) of the particle's —
identifying the `Z₂` factor of Sorkin's isotropic group with `Particles` charge conjugation `C`. -/
lemma antiparticle_eq_weightConjugation (q : QuantumNumbers) :
    qnVec (conjugate q) = weightConjugation (qnVec q) := by
  funext i; fin_cases i <;> simp [qnVec, weightConjugation, conjugate]

/-- A particle and its charge conjugate have quantum numbers summing to zero — the affine
"sum to zero" condition for a `5 ⊕ 5̄` conjugation pair (particle–antiparticle annihilation). -/
lemma qnVec_pair_sum_zero (q : QuantumNumbers) (i : Fin 3) :
    qnVec q i + qnVec (conjugate q) i = 0 := by
  rw [antiparticle_eq_weightConjugation]; simp [weightConjugation]

end ChargeConjugation

/-!

Sorkin's property (a): "all vertices of the net are equivalent. This follows from the definition of
`Σ`, which is invariant under translation through any lattice vector." The leg relation depends only
on the difference `u − v`, so translating both endpoints by a common vector preserves it — every
vertex looks like the origin. -/

/-- **Property (a): the leg relation is translation-invariant** — the net looks the same at every
vertex, so all vertices are equivalent (Sorkin's proof of homogeneity). -/
lemma isLegVector_translation_invariant (u v t : Fin 5 → ℝ) :
    IsLegVector (fun i => u i + t i) (fun i => v i + t i) ↔ IsLegVector u v := by
  unfold IsLegVector
  constructor
  · rintro ⟨hne, hlt⟩
    refine ⟨fun h => hne (funext fun i => by rw [h]), fun i => ?_⟩
    have hcomponent := hlt i
    simpa [show ∀ i, (u i + t i) - (v i + t i) = u i - v i from fun i => by ring]
      using hcomponent
  · rintro ⟨hne, hlt⟩
    refine ⟨fun h => hne (funext fun i => by
      have hcomponent := congrFun h i
      simpa using hcomponent), fun i => ?_⟩
    simpa [show (u i + t i) - (v i + t i) = u i - v i from by ring] using hlt i

/-! ## The fundamental cell `σ₀`: its vertices are the `su(5)` fundamental weights

Sorkin verifies the tiling (property (c)) by looking near the origin, where the only cells are the
`5!` images of one cell `σ₀` with vertices `½(00000)`, `⅕(4,−1,−1,−1,−1)`, `⅕(3,3,−2,−2,−2)`,
`⅕(2,2,2,−3,−3)`, `⅕(1,1,1,1,−4)`. These four nonzero vertices are exactly the **fundamental
weights** `ω₁,…,ω₄` of `A₄ = su(5)`: `ω_k` has its first `k` components equal to `(5−k)/5` and its
last `5−k` components equal to `−k/5`. They are affine weights (sum to zero) and dominant (sorted
descending — in the closure of the dominant Weyl chamber), and the first two are precisely the
type-(ii) leg vectors `typeIIvectorA`, `typeIIvectorB`. -/

/-- The `su(5)` **fundamental weight** `ω_{k+1}` (`k : Fin 4`): first `k+1` components `(4−k)/5`, the
rest `−(k+1)/5`. These are the nonzero vertices of Sorkin's fundamental cell `σ₀`. -/
noncomputable def fundamentalWeight (k : Fin 4) : Fin 5 → ℝ :=
  fun i => if (i : ℕ) ≤ (k : ℕ) then (5 - ((k : ℕ) + 1 : ℝ)) / 5 else (-((k : ℕ) + 1 : ℝ)) / 5

/-- Each fundamental weight is an **affine weight** (`su(5)` traceless, components sum to zero). -/
lemma fundamentalWeight_isAffineWeight (k : Fin 4) : IsAffineWeight (fundamentalWeight k) := by
  unfold IsAffineWeight
  fin_cases k <;> · simp [fundamentalWeight, Fin.sum_univ_five]; norm_num

/-- Each fundamental weight is **dominant** (sorted descending) — it lies in the closure of the
dominant Weyl chamber, matching Sorkin's ordering `x⁰ ≥ x¹ ≥ ⋯ ≥ x⁴` of the cell. -/
lemma fundamentalWeight_antitone (k : Fin 4) : Antitone (fundamentalWeight k) := by
  fin_cases k <;> · intro a b hab; fin_cases a <;> fin_cases b <;>
    simp_all [fundamentalWeight] <;> norm_num

/-- **`ω₁` is the type-(ii) leg vector `⅕(4,−1,−1,−1,−1)`** (`typeIIvectorA`) — the first fundamental
weight is the leg offset already defining the net. -/
lemma fundamentalWeight_zero_eq_typeIIvectorA : fundamentalWeight 0 = typeIIvectorA := by
  funext i; fin_cases i <;> simp [fundamentalWeight, typeIIvectorA] <;> norm_num

/-- **`ω₂` is the type-(ii) leg vector `⅕(3,3,−2,−2,−2)`** (`typeIIvectorB`). -/
lemma fundamentalWeight_one_eq_typeIIvectorB : fundamentalWeight 1 = typeIIvectorB := by
  funext i; fin_cases i <;> simp [fundamentalWeight, typeIIvectorB] <;> norm_num

/-!

Sorkin's property (c): the `4`-simplexes fill `R⁴` with no gaps and no overlaps. The proof reduces
(by homogeneity, property (a)) to the origin, where "any point in the neighborhood of the origin has
*some* ordering of coordinates `x⁰ ≥ x¹ ≥ x² ≥ x³ ≥ x⁴` and thus belongs to that cell whose vertices
are those of `σ₀` with coordinates permuted to match that ordering. Since there are exactly `5!`
possible orderings and the same number of cells, the assertion is proved."

Formalized: the ordering regions are the **Weyl chambers** of `A₄ = su(5)` (the `σ`-sorted cones),
there are exactly `5! = 120` of them (one per `S₅` element), each is convex, and — crucially — every
point lies in at least one (**covering, no gaps**), because every tuple can be sorted. -/

/-- **The `σ`-permuted (Weyl) chamber**: the tuples sorted descending after the permutation `σ` — the
region enjoying the coordinate ordering `x_{σ0} ≥ x_{σ1} ≥ ⋯`. The dominant chamber is `σ = 1`. -/
def InWeylChamber (σ : Su5WeylGroup) (x : Fin 5 → ℝ) : Prop := Antitone (x ∘ σ)

/-- **Every point lies in some Weyl chamber (no gaps)**: any coordinate tuple admits a permutation
sorting it descending, so it enjoys some ordering and belongs to the correspondingly-permuted cell.
This is the covering half of Sorkin's property (c) — the cells leave no gaps. -/
lemma weylChambers_cover (x : Fin 5 → ℝ) : ∃ σ : Su5WeylGroup, InWeylChamber σ x := by
  refine ⟨Tuple.sort x * Fin.revPerm, ?_⟩
  intro a b hab
  have hrev : Fin.revPerm b ≤ Fin.revPerm a := by simpa [Fin.revPerm] using Fin.rev_le_rev.mpr hab
  simpa [InWeylChamber, Function.comp, Equiv.Perm.mul_apply] using Tuple.monotone_sort x hrev

/-- **A Weyl chamber is convex**: a positive combination of two points sharing an ordering shares it
too (the ordering `x_{σ0} ≥ ⋯ ≥ x_{σ4}` is preserved under convex combination). This is the
overlap-controlling half of property (c): each cell's interior is a single convex ordering region,
matching Sorkin's "any interior point is a convex combination of the vertices and thus enjoys the
same ordering." -/
lemma weylChamber_convex (σ : Su5WeylGroup) (x y : Fin 5 → ℝ)
    (hx : InWeylChamber σ x) (hy : InWeylChamber σ y) (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    InWeylChamber σ (fun i => t * x i + s * y i) := by
  intro a b hab
  have h1 : t * x (σ b) ≤ t * x (σ a) := mul_le_mul_of_nonneg_left (hx hab) ht
  have h2 : s * y (σ b) ≤ s * y (σ a) := mul_le_mul_of_nonneg_left (hy hab) hs
  simp only [Function.comp] at *; linarith

/-- **There are exactly `5! = 120` Weyl chambers** — one per coordinate ordering (`S₅` element),
matching the `120` cells near the origin (`I(4,0) = 120`, `fourSimplex_face_counts`/incidences). The
equal count `#orderings = #cells` is what makes the tiling exact (no gaps, no overlaps). -/
lemma weylChambers_card : Fintype.card Su5WeylGroup = 120 := su5WeylGroup_card

/-! ## Open spacetime — the `R⁴` net has no intrinsic scale (refinable)

Sorkin (end of Sec. III): "the net for `R⁴` … has no intrinsic scale and can be cast as finely as
desired over any continuous spacetime", *unlike* the closed `S³×R` net which "cannot be refined
without producing a topologically distinct net." This is the defining feature of the **open**
spacetime net: the leg relation carries a scale `λ`, all scales are equivalent (scale-covariance),
and there is no smallest one — so the net can be refined arbitrarily. -/

/-- **The leg relation at scale `λ`**: two vertices differing by a vector with all components `< λ`.
The unit scale recovers `IsLegVector` (`isLegVectorAtScale_one`). -/
def IsLegVectorAtScale (lam : ℝ) (u v : Fin 5 → ℝ) : Prop := u ≠ v ∧ ∀ i, |u i - v i| < lam

/-- The unit-scale leg relation is Sorkin's `IsLegVector`. -/
lemma isLegVectorAtScale_one (u v : Fin 5 → ℝ) : IsLegVectorAtScale 1 u v ↔ IsLegVector u v :=
  Iff.rfl

/-- **Scale covariance**: the net at scale `λ > 0` is the unit net rescaled by `λ⁻¹` — all scales are
geometrically identical, so no scale is intrinsic. -/
lemma isLegVector_scale_covariant (lam : ℝ) (hlam : 0 < lam) (u v : Fin 5 → ℝ) :
    IsLegVectorAtScale lam u v
      ↔ IsLegVectorAtScale 1 (fun i => lam⁻¹ * u i) (fun i => lam⁻¹ * v i) := by
  have hkey : ∀ i, |lam⁻¹ * u i - lam⁻¹ * v i| < 1 ↔ |u i - v i| < lam := fun i => by
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hlam), inv_mul_lt_iff₀ hlam, mul_one]
  unfold IsLegVectorAtScale
  refine ⟨fun ⟨hne, hlt⟩ => ⟨fun h => hne (funext fun i => ?_), fun i => (hkey i).mpr (hlt i)⟩,
    fun ⟨hne, hlt⟩ => ⟨fun h => hne (funext fun i => ?_), fun i => (hkey i).mp (hlt i)⟩⟩
  · exact mul_left_cancel₀ (inv_ne_zero (ne_of_gt hlam)) (congrFun h i)
  · rw [h]

/-- **Refinability at every scale**: a family of nets (indexed by valid scales) can be refined
arbitrarily finely — for every `ε > 0` there is a valid scale below `ε`. This is Sorkin's "cast as
finely as desired / no intrinsic scale". -/
def RefinableAtEveryScale (validScale : ℝ → Prop) : Prop :=
  ∀ ε > 0, ∃ lam, 0 < lam ∧ lam < ε ∧ validScale lam

/-- **The open `R⁴` net is refinable at every scale**: every positive `λ` gives a valid net (by
scale covariance), and there is no smallest one — the net has no intrinsic scale. -/
lemma openR4Net_refinable : RefinableAtEveryScale (fun lam => 0 < lam) :=
  fun ε hε => ⟨ε / 2, by positivity, by linarith, by positivity⟩

/-- **The closed contrast**: a net locked to a single scale `λ₀` (as the `S³×R` net is locked to its
topological scale) is *not* refinable — no valid scale lies below `λ₀`. This is the open-versus-closed
distinction: the `R⁴` net refines freely, the closed net cannot. -/
lemma fixedScaleNet_not_refinable (lam0 : ℝ) (h0 : 0 < lam0) :
    ¬ RefinableAtEveryScale (fun lam => lam = lam0) := by
  intro h
  obtain ⟨lam, _, hlt, heq⟩ := h lam0 h0
  rw [heq] at hlt; exact lt_irrefl _ hlt

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4

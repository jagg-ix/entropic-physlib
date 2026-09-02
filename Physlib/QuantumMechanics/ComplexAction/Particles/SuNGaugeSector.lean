/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Complex.Basic
meta import Zil

/-!
# The `SU(N)` gauge sector: dimensions, Casimirs, index relation, tensor decompositions

The whole-gauge-sector layer in two namespaces (each formerly its own module):

* **Part I — `SuNGaugeSector`.** The `SU(N)` gauge invariants across weak `SU(2)`, colour `SU(3)`,
  and GUT `SU(5)`: the adjoint dimension `N²−1` (gauge-boson counts `3, 8, 24`), the Casimir index
  relation `C₂(fund)·dim(fund) = T_F·dim(adj)` (`casimir_index_relation`), the per-group Casimirs
  (`su2_fund_casimir = 3/4`, `su5_fund_casimir = 12/5`), and universal pure-gauge asymptotic freedom
  (`pure_gauge_asymptotically_free`).
* **Part II — `SuNTensorDecomposition`.** The `SU(N)` Clebsch–Gordan bookkeeping: the meson
  `N⊗N̄ = 1⊕adj` (`meson_decomp_N`, evaluated at `N = 2, 3, 5`), the baryon singlet
  `⋀ᴺ(ℂᴺ) = C(N,N) = 1` (`sun_baryon_singlet`), the `SL(2)`-invariant `ε`-bilinear
  (`su2_singlet_bilinear_invariant`, the Mathur prepotential singlet), and the Jones–Kogut–Sinclair
  composite-baryon canonicity: the `ε`-composite is the ordered product
  (`epsilon_composite_eq_ordered`), obeys Pauli exclusion (`composite_pauli`), and its anticommutator
  reduces to number-operator form (`composite_car_number_form`), collapsing to `{X,X†} = 1` on the
  colour-saturated sector (`composite_car_saturated`) — the three-quark composite is a canonical
  fermion.

**Honest layering.** Exact: the dimensions, the index relation, the per-group evaluations, the
asymptotic-freedom sign, the dimension identities, and the composite-fermion algebra (CAR taken as
hypotheses in `{·,·} = 0` form). The Casimir formulas are the standard `su(N)` results from
`Su3WeylDimensionCasimir`; the physical readings (confinement of nonsinglets, the fluxless sector)
are the cited lattice results.

## References

* `su(N)` Casimirs and the index relation `C₂(R)dim(R) = T(R)dim(G)`; `SU(N)` Clebsch–Gordan;
  Mathur hep-lat/0405008 (prepotential singlets); Jones–Kogut–Sinclair (1979), Eqs. 2.4b/2.5. Built
  on `Particles.Su3ConfinementPotential` (including its `Su3AsymptoticFreedom` part) and
  `Particles.StrongInteractionColorOctet`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector

open Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir
open Physlib.QuantumMechanics.ComplexAction.Particles.Su3AsymptoticFreedom


/-- The **adjoint dimension of `SU(N)`** `N² − 1` — the number of gauge bosons (`3` weak, `8` gluons, `24`
`SU(5)`). -/
def sunAdjointDim (N : ℕ) : ℕ := N ^ 2 - 1

/-- The **fundamental dimension of `SU(N)`** `= N` (the number of colours). -/
def sunFundamentalDim (N : ℕ) : ℕ := N


/-- **The Casimir index relation** `C₂(fund) · dim(fund) = T_F · dim(adj)`, i.e.
`(N²−1)/2N · N = ½(N²−1)` (`T_F = 1/2`): the fundamental Casimir times the fundamental dimension equals the
Dynkin index times the adjoint dimension. -/
lemma casimir_index_relation (N : ℚ) (hN : N ≠ 0) :
    fundamentalCasimirN N * N = 1 / 2 * (N ^ 2 - 1) := by
  unfold fundamentalCasimirN; field_simp

/-- **The adjoint Casimir is the adjoint Dynkin index** `C₂(adj) = T_A = N`. -/
lemma adjoint_casimir_eq_dynkin (N : ℚ) : adjointCasimirN N = N := rfl


/-- **Weak `SU(2)`: three gauge bosons** `W¹, W², W³` (`= 2² − 1`). -/
lemma su2_adjoint : sunAdjointDim 2 = 3 := by decide

/-- **Weak `SU(2)` fundamental Casimir** `C_F = 3/4`. -/
lemma su2_fund_casimir : fundamentalCasimirN 2 = 3 / 4 := by norm_num [fundamentalCasimirN]

/-- **Colour `SU(3)`: eight gluons** `= 3² − 1` (`StrongInteractionColorOctet.gluon_count`). -/
lemma su3_adjoint_eq_gluonCount : sunAdjointDim 3 = 8 :=
  Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet.gluon_count

/-- **GUT `SU(5)`: twenty-four gauge bosons** `= 5² − 1 = dim SU(5)` (matching `|2T| = 24`). -/
lemma su5_adjoint : sunAdjointDim 5 = 24 := by decide

/-- **GUT `SU(5)` fundamental Casimir** `C_F = 12/5`. -/
lemma su5_fund_casimir : fundamentalCasimirN 5 = 12 / 5 := by norm_num [fundamentalCasimirN]


/-- **Every pure `SU(N)` Yang–Mills theory is asymptotically free** `0 < betaZero N 0` for `N > 0`: with no
quarks to screen, gluon antiscreening `(11/3) N` always wins. -/
lemma pure_gauge_asymptotically_free (N : ℚ) (hN : 0 < N) : 0 < betaZero N 0 := by
  unfold betaZero; nlinarith

end Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector

/-! ## Part II — general `SU(N)` tensor decompositions and the composite baryon -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.SuNTensorDecomposition

open Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector


/-- **The `SU(N)` meson `N ⊗ N̄ = 1 ⊕ adjoint`** `N² = 1 + (N²−1)`: a fundamental ⊗ anti-fundamental is the
singlet plus the adjoint (the `N²−1` gauge bosons, `sunAdjointDim N`). -/
lemma meson_decomp_N (N : ℕ) (hN : 1 ≤ N) : N * N = 1 + sunAdjointDim N := by
  have h : 1 ≤ N ^ 2 := Nat.one_le_pow 2 N (by omega)
  rw [sunAdjointDim, ← pow_two]; omega


/-- **The `SU(N)` baryon singlet** `⋀ᴺ(ℂᴺ) = C(N,N) = 1`: the totally antisymmetric combination of `N`
fundamentals is the one-dimensional singlet — the `ε_{a₁…aN}` determinant, the `SU(N)` generalization of the
colour-singlet baryon `ColorSingletBaryon.baryonColor` (`N = 3`). -/
lemma sun_baryon_singlet (N : ℕ) : Nat.choose N N = 1 := Nat.choose_self N


/-- Weak `SU(2)` meson `2 ⊗ 2̄ = 1 ⊕ 3` (`4 = 1 + 3`). -/
lemma su2_meson : 2 * 2 = 1 + sunAdjointDim 2 := by decide

/-- Colour `SU(3)` meson `3 ⊗ 3̄ = 1 ⊕ 8` (`9 = 1 + 8`). -/
lemma su3_meson : 3 * 3 = 1 + sunAdjointDim 3 := by decide

/-- GUT `SU(5)` meson `5 ⊗ 5̄ = 1 ⊕ 24` (`25 = 1 + 24`). -/
lemma su5_meson : 5 * 5 = 1 + sunAdjointDim 5 := by decide

/-- **[The SU(2) singlet bilinear is the `ε`-determinant]** for any `V` with `det V = 1` acting on
two doublets `x, y` over a commutative ring, `ε_{αβ}(Vx)_α(Vy)_β = ε_{αβ}x_α y_β`: the antisymmetric
pairing of two fundamentals is `SL(2)`-invariant because it *is* the `2×2` determinant — the `N = 2`
case of the `ε_{a₁…aN}` baryon singlet above. This is the invariance of the prepotential singlet
creation operator `a†·b̃† = a†₁b†₂ − a†₂b†₁` of SU(2) lattice gauge theory (Mathur hep-lat/0405008
Eq. 9, realized on the Bargmann carrier as `BargmannFockCCR.singletCre`), whose powers generate the
`d = 1` physical Hilbert space (his Eq. 24); commuting entries are honest since creation operators
mutually commute. -/
theorem su2_singlet_bilinear_invariant {R : Type*} [CommRing R]
    (V : Matrix (Fin 2) (Fin 2) R) (hV : V.det = 1) (x y : Fin 2 → R) :
    V.mulVec x 0 * V.mulVec y 1 - V.mulVec x 1 * V.mulVec y 0
      = x 0 * y 1 - x 1 * y 0 := by
  rw [Matrix.det_fin_two] at hV
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (x 0 * y 1 - x 1 * y 0) * hV

/-! ### The composite baryon is a canonical fermion (Jones–Kogut–Sinclair 1979, Eqs. 2.4b/2.5)

In the strong-coupling lattice QCD of Jones–Kogut–Sinclair, the nucleon is the colour-singlet
composite `X = ⅙ε_{ijk}χᵢχⱼχₖ` of the three quark colours, and the whole effective-Hamiltonian
construction rests on their Eq. 2.5: *`X` and `X*` can be treated as canonical fermion fields*.
Below, on an abstract ring with three fermionic modes `c i` and their conjugates `d i` (CAR taken
as hypotheses in the `{·,·} = 0` form): the `ε`-composite *is* the ordered product `c₀c₁c₂`
(`epsilon_composite_eq_ordered` — the six signed orderings coincide); the composite obeys Pauli
exclusion `X² = 0` (`composite_pauli`); and the anticommutator reduces *exactly* to number
operators, `{X, X†} = (c₀d₀)(c₁d₁)(c₂d₂) + (d₂c₂)(d₁c₁)(d₀c₀)` (`composite_car_number_form`) —
no diagonal CAR needed. On the colour-saturated sector, where each `dᵢcᵢ` is one and the same
projector `P` (`0` or `3` quarks per site — exactly the fluxless states the paper perturbs
around), this collapses to `{X, X†} = (1−P)³ + P³ = 1` (`composite_car_saturated`): the baryon
composite of three fermions is again a canonical fermion, which is what lets the effective
Hamiltonian of their Eq. 2.3 be a *fermion* hopping Hamiltonian for nucleons. -/

section CompositeBaryon

variable {A : Type*} [Ring A] [Module ℂ A] (c d : Fin 3 → A)

/-- **[The `ε`-composite is the ordered product]** with anticommuting quark modes, the six signed
orderings of `⅙ε_{ijk}cᵢcⱼcₖ` all equal `c₀c₁c₂`, so the composite is the plain ordered product
(their Eq. 2.4b, normalization included). -/
theorem epsilon_composite_eq_ordered
    (hcc : ∀ i j, c i * c j + c j * c i = 0) :
    ((6 : ℂ)⁻¹) • (c 0 * c 1 * c 2 - c 0 * c 2 * c 1 - c 1 * c 0 * c 2
        + c 1 * c 2 * c 0 + c 2 * c 0 * c 1 - c 2 * c 1 * c 0)
      = c 0 * c 1 * c 2 := by
  have swap : ∀ i j, c i * c j = -(c j * c i) := fun i j =>
    eq_neg_of_add_eq_zero_left (hcc i j)
  have h1 : c 0 * c 2 * c 1 = -(c 0 * c 1 * c 2) := by
    rw [mul_assoc, swap 2 1, mul_neg, mul_assoc]
  have h2 : c 1 * c 0 * c 2 = -(c 0 * c 1 * c 2) := by
    rw [swap 1 0, neg_mul]
  have h3 : c 1 * c 2 * c 0 = c 0 * c 1 * c 2 := by
    rw [mul_assoc, swap 2 0, mul_neg, ← mul_assoc, swap 1 0, neg_mul, neg_neg]
  have h4 : c 2 * c 0 * c 1 = c 0 * c 1 * c 2 := by
    rw [swap 2 0, neg_mul, mul_assoc, swap 2 1, mul_neg, mul_assoc, neg_neg]
  have h5 : c 2 * c 1 * c 0 = -(c 0 * c 1 * c 2) := by
    rw [mul_assoc, swap 1 0, mul_neg, ← mul_assoc, h4]
  rw [h1, h2, h3, h4, h5]
  have hsix : (c 0 * c 1 * c 2 : A) - -(c 0 * c 1 * c 2) - -(c 0 * c 1 * c 2)
      + c 0 * c 1 * c 2 + c 0 * c 1 * c 2 - -(c 0 * c 1 * c 2)
      = (6 : ℂ) • (c 0 * c 1 * c 2) := by
    module
  rw [hsix, smul_smul]
  norm_num

/-- **[Pauli exclusion for the composite]** `X² = 0`: two baryons cannot occupy the same site —
inherited from `c₀² = 0` through the anticommutation moves. -/
theorem composite_pauli (hcc : ∀ i j, c i * c j + c j * c i = 0) :
    (c 0 * c 1 * c 2) * (c 0 * c 1 * c 2) = 0 := by
  have hsq : c 0 * c 0 = 0 := by
    have h := hcc 0 0
    have h2 : (2 : ℂ) • (c 0 * c 0) = 0 := by rw [two_smul]; exact h
    have hcg := congrArg (fun z => ((2 : ℂ)⁻¹) • z) h2
    simpa [smul_smul] using hcg
  have swap : ∀ i j, c i * c j = -(c j * c i) := fun i j =>
    eq_neg_of_add_eq_zero_left (hcc i j)
  calc (c 0 * c 1 * c 2) * (c 0 * c 1 * c 2)
      = c 0 * c 1 * (c 2 * c 0) * (c 1 * c 2) := by noncomm_ring
    _ = -(c 0 * c 1 * (c 0 * c 2) * (c 1 * c 2)) := by rw [swap 2 0]; noncomm_ring
    _ = -(c 0 * (c 1 * c 0) * c 2 * (c 1 * c 2)) := by noncomm_ring
    _ = c 0 * (c 0 * c 1) * c 2 * (c 1 * c 2) := by rw [swap 1 0]; noncomm_ring
    _ = (c 0 * c 0) * (c 1 * c 2 * c 1 * c 2) := by noncomm_ring
    _ = 0 := by rw [hsq, zero_mul]

omit [Module ℂ A] in
/-- **[The composite anticommutator in number-operator form]** using only the *off-diagonal* CAR
(distinct modes anticommute), the baryon anticommutator reduces exactly to
`{X, X†} = (c₀d₀)(c₁d₁)(c₂d₂) + (d₂c₂)(d₁c₁)(d₀c₀)` — hole numbers times hole numbers plus
occupations times occupations. -/
theorem composite_car_number_form
    (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hdd : ∀ i j, d i * d j + d j * d i = 0)
    (hcd : ∀ i j, i ≠ j → c i * d j + d j * c i = 0) :
    (c 0 * c 1 * c 2) * (d 2 * d 1 * d 0) + (d 2 * d 1 * d 0) * (c 0 * c 1 * c 2)
      = (c 0 * d 0) * ((c 1 * d 1) * (c 2 * d 2))
        + (d 2 * c 2) * ((d 1 * c 1) * (d 0 * c 0)) := by
  have swapc : ∀ i j, c i * c j = -(c j * c i) := fun i j =>
    eq_neg_of_add_eq_zero_left (hcc i j)
  have swapd : ∀ i j, d i * d j = -(d j * d i) := fun i j =>
    eq_neg_of_add_eq_zero_left (hdd i j)
  have swapm : ∀ i j, i ≠ j → c i * d j = -(d j * c i) := fun i j h =>
    eq_neg_of_add_eq_zero_left (hcd i j h)
  have swapm' : ∀ i j, i ≠ j → d j * c i = -(c i * d j) := fun i j h =>
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hcd i j h)
  -- the "number" c i * d i (and d i * c i) commutes with every other mode
  have hm_c : ∀ i j, i ≠ j → (c i * d i) * d j = d j * (c i * d i) := by
    intro i j h
    calc (c i * d i) * d j = c i * (d i * d j) := by rw [mul_assoc]
      _ = c i * -(d j * d i) := by rw [swapd i j]
      _ = -(c i * d j * d i) := by rw [mul_neg, ← mul_assoc]
      _ = -(-(d j * c i) * d i) := by rw [swapm i j h]
      _ = d j * (c i * d i) := by noncomm_ring
  have hn_c : ∀ i j, i ≠ j → (d i * c i) * c j = c j * (d i * c i) := by
    intro i j h
    calc (d i * c i) * c j = d i * (c i * c j) := by rw [mul_assoc]
      _ = d i * -(c j * c i) := by rw [swapc i j]
      _ = -(d i * c j * c i) := by rw [mul_neg, ← mul_assoc]
      _ = -(-(c j * d i) * c i) := by rw [swapm' j i (Ne.symm h)]
      _ = c j * (d i * c i) := by noncomm_ring
  -- X X† = (c₀d₀)(c₁d₁)(c₂d₂)
  have hXXd : (c 0 * c 1 * c 2) * (d 2 * d 1 * d 0)
      = (c 0 * d 0) * ((c 1 * d 1) * (c 2 * d 2)) := by
    calc (c 0 * c 1 * c 2) * (d 2 * d 1 * d 0)
        = c 0 * c 1 * ((c 2 * d 2) * d 1) * d 0 := by noncomm_ring
      _ = c 0 * c 1 * (d 1 * (c 2 * d 2)) * d 0 := by rw [hm_c 2 1 (by decide)]
      _ = c 0 * ((c 1 * d 1) * (c 2 * d 2) * d 0) := by noncomm_ring
      _ = c 0 * ((c 1 * d 1) * ((c 2 * d 2) * d 0)) := by rw [mul_assoc (c 1 * d 1)]
      _ = c 0 * ((c 1 * d 1) * (d 0 * (c 2 * d 2))) := by rw [hm_c 2 0 (by decide)]
      _ = c 0 * ((c 1 * d 1) * d 0) * (c 2 * d 2) := by noncomm_ring
      _ = c 0 * (d 0 * (c 1 * d 1)) * (c 2 * d 2) := by rw [hm_c 1 0 (by decide)]
      _ = (c 0 * d 0) * ((c 1 * d 1) * (c 2 * d 2)) := by noncomm_ring
  -- X† X = (d₂c₂)(d₁c₁)(d₀c₀)
  have hXdX : (d 2 * d 1 * d 0) * (c 0 * c 1 * c 2)
      = (d 2 * c 2) * ((d 1 * c 1) * (d 0 * c 0)) := by
    calc (d 2 * d 1 * d 0) * (c 0 * c 1 * c 2)
        = d 2 * d 1 * ((d 0 * c 0) * c 1) * c 2 := by noncomm_ring
      _ = d 2 * d 1 * (c 1 * (d 0 * c 0)) * c 2 := by rw [hn_c 0 1 (by decide)]
      _ = d 2 * ((d 1 * c 1) * (d 0 * c 0) * c 2) := by noncomm_ring
      _ = d 2 * ((d 1 * c 1) * ((d 0 * c 0) * c 2)) := by rw [mul_assoc (d 1 * c 1)]
      _ = d 2 * ((d 1 * c 1) * (c 2 * (d 0 * c 0))) := by rw [hn_c 0 2 (by decide)]
      _ = d 2 * ((d 1 * c 1) * c 2) * (d 0 * c 0) := by noncomm_ring
      _ = d 2 * (c 2 * (d 1 * c 1)) * (d 0 * c 0) := by rw [hn_c 1 2 (by decide)]
      _ = (d 2 * c 2) * ((d 1 * c 1) * (d 0 * c 0)) := by noncomm_ring
  rw [hXXd, hXdX]

omit [Module ℂ A] in
/-- **[On the colour-saturated sector the composite is canonical]** if each mode's occupation
`dᵢcᵢ` is one and the same projector `P` (each site holds `0` or `3` quarks — the fluxless states)
and the diagonal CAR `cᵢdᵢ = 1 − dᵢcᵢ` holds, then `{X, X†} = (1−P)³ + P³ = 1`: the paper's
Eq. 2.5 — the three-quark composite is a canonical fermion. -/
theorem composite_car_saturated (P : A) (hP : P * P = P)
    (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hdd : ∀ i j, d i * d j + d j * d i = 0)
    (hcd : ∀ i j, i ≠ j → c i * d j + d j * c i = 0)
    (hdiag : ∀ i, c i * d i = 1 - d i * c i)
    (hocc : ∀ i, d i * c i = P) :
    (c 0 * c 1 * c 2) * (d 2 * d 1 * d 0) + (d 2 * d 1 * d 0) * (c 0 * c 1 * c 2) = 1 := by
  rw [composite_car_number_form c d hcc hdd hcd]
  simp only [hdiag, hocc]
  calc (1 - P) * ((1 - P) * (1 - P)) + P * (P * P)
      = 1 - 3 * P + 3 * (P * P) - P * (P * P) + P * (P * P) := by noncomm_ring
    _ = 1 := by rw [hP]; noncomm_ring

end CompositeBaryon

end Physlib.QuantumMechanics.ComplexAction.Particles.SuNTensorDecomposition

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector.casimir_index_relation where
  formalizes @ "claim:sun-casimir-index-relation-CF-times-dimfund-equals-TF-times-dimadj",
  supported_by @ "paper:gell-mann-1962-symmetries-of-baryons-and-mesons"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector.pure_gauge_asymptotically_free where
  formalizes @ "claim:every-pure-sun-yang-mills-is-asymptotically-free",
  requires @ "claim:sun-casimir-index-relation-CF-times-dimfund-equals-TF-times-dimadj",
  supported_by @ "paper:gross-wilczek-politzer-1973-asymptotic-freedom"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.SuNTensorDecomposition.sun_baryon_singlet where
  formalizes @ "claim:sun-baryon-is-the-totally-antisymmetric-one-dimensional-singlet",
  caveat @ "claim:combinatorial-dimension-of-the-antisymmetric-subspace-realized-as-epsilon-determinant-at-N-three"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.SuNTensorDecomposition.composite_car_saturated where
  formalizes @ "claim:the-three-quark-colour-singlet-composite-is-a-canonical-fermion-on-the-saturated-sector",
  requires @ "claim:sun-baryon-is-the-totally-antisymmetric-one-dimensional-singlet",
  supported_by @ "paper:jones-kogut-sinclair-1979-strong-coupling-lattice-qcd",
  caveat @ "claim:CAR-taken-as-hypotheses-and-fluxless-saturated-sector-is-the-paper-perturbation-point"

zil_file_contract physlib.suNGaugeSector where
  promises "The SU(N) gauge sector: the Casimir index relation across the weak, colour and grand-unified groups, universal pure-gauge asymptotic freedom, the totally antisymmetric baryon singlet, and the Jones-Kogut-Sinclair result that the three-quark colour-singlet composite is a canonical fermion on the colour-saturated sector."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector.sunAdjointDim",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.fundamentalCasimirN"]
  forbids_substitutes ["a derivation of the CAR, taken here as hypotheses in the anticommutator-zero form",
    "the running-coupling dynamics, ordered here only by the one-loop beta-function sign"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector.casimir_index_relation,
    Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector.pure_gauge_asymptotically_free,
    Physlib.QuantumMechanics.ComplexAction.Particles.SuNTensorDecomposition.sun_baryon_singlet,
    Physlib.QuantumMechanics.ComplexAction.Particles.SuNTensorDecomposition.composite_car_saturated]

/- ZIL-END -/

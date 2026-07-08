/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Lovelock's theorem: the dimension-dependent termination of the generalized Einstein tensors

D. Lovelock, *The Einstein Tensor and Its Generalizations* (J. Math. Phys. **12** (1971) 498): the most
general symmetric, divergence-free tensor `A^{ij}(g, ∂g, ∂²g)` is a dimension-dependent sum of the
**generalized Einstein (Lovelock) tensors** — and *"the number of independent tensors of this type
depends crucially on the dimension of the space."* In four dimensions the only such tensor is
`A^{ij} = aG^{ij} + bg^{ij}` (the Corollary), so the linearity in `∂²g` usually *assumed* is in fact a
consequence.

The whole dimension-dependence rests on one algebraic fact — the **generalized Kronecker delta** (a
determinant of `δ`'s, Lovelock's Eq. 2.1) is totally antisymmetric, so it **vanishes when it records
more indices than the dimension** (Eq. 2.6): `δ^{j₁…j_N}_{j₁…j_N} = 0` if `n < N`. Its fully-contracted
value is the number of ordered `N`-tuples of distinct indices, `n·(n−1)⋯(n−N+1) = n!/(n−N)!` — the
falling factorial `Nat.descFactorial n N`, equal to the number of injections `Fin N ↪ Fin n`.

Because a Lovelock **tensor** term of order `p` records `2p+1` free indices while the corresponding
**Lagrangian** term records `2p`, this one fact fixes exactly which terms survive in each dimension.

* **§A — the generalized Kronecker delta and Eq. 2.6.** `genKroneckerTrace n N = n!/(n−N)!`
 (`= |Fin N ↪ Fin n|`, `genKroneckerTrace_eq_card_embeddings`); `genKroneckerTrace_eq_zero_iff` (`= 0 ↔
 n < N`) and `genKroneckerTrace_pos_iff` (`0 < · ↔ N ≤ n`).
* **§B — the Lovelock tensor series (Eq. 2.5).** The order-`p` tensor term (`2p+1` indices) is nonzero
 iff `2p+1 ≤ n` (`lovelockTensorTerm_pos_iff`).
* **§C — the Lovelock Lagrangian series (Eq. 3.1).** The order-`p` Lagrangian term (`2p` indices) is
 nonzero iff `2p ≤ n` (`lovelockLagrangianTerm_pos_iff`).
* **§D — four dimensions.** `lovelock_dim4_tensor_terminates` (the tensor keeps only `p ≤ 1`: the
 cosmological `bg` and the Einstein `aG` — the Corollary `A = aG + bg`); `lovelock_dim4_gaussBonnet`
 (Gauss–Bonnet, `p = 2`, survives in the **Lagrangian** but its **tensor** vanishes — topological in 4D).
* **§E — the dimension-by-dimension classification.** `lovelock_dim2_einstein_trivial` (the Einstein
 tensor `G_{μν} ≡ 0` in two dimensions); `lovelock_dim3` (Einstein exists, no Gauss–Bonnet);
 `lovelock_dim5_gaussBonnet_dynamical` (Gauss–Bonnet becomes **dynamical** in `D ≥ 5`).
* **§F — counting the invariants.** `lovelockTensorCount n` (orders with `2p+1 ≤ n`) grows as `⌊(n+1)/2⌋`
 (`lovelockTensorCount_examples`) — the quantitative form of "depends crucially on the dimension."

Proven: the falling-factorial value of the fully-contracted generalized Kronecker
delta, its dimension-vanishing (Eq. 2.6), and the resulting survival conditions `2p+1 ≤ n` (tensor) and
`2p ≤ n` (Lagrangian), specialized to `n = 4`. Interpretive: identifying the `p = 0, 1` surviving tensor
terms with `bg^{ij}` and `aG^{ij}` (the Corollary) and the `p = 2` Lagrangian term with the Gauss–Bonnet
density is the tensor-calculus content of Lovelock's proof (not performed here — only the exact
index-counting that makes the series terminate with the dimension).

## References

* D. Lovelock, J. Math. Phys. **12** (1971) 498 (Eqs. 2.1, 2.5, 2.6, 3.1; Theorem 1 and its Corollary).
 Uses Mathlib `Nat.descFactorial_eq_zero_iff_lt` (= Eq. 2.6) and `Fintype.card_embedding_eq`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination

/-! ## §A — the generalized Kronecker delta and its dimension-vanishing (Eq. 2.6) -/

/-- **The fully-contracted generalized Kronecker delta** `δ^{j₁…j_N}_{j₁…j_N}` in `n` dimensions: the
number of ordered `N`-tuples of distinct indices from `{1,…,n}`, `n·(n−1)⋯(n−N+1) = n!/(n−N)!`, i.e. the
falling factorial. -/
def genKroneckerTrace (n N : ℕ) : ℕ := n.descFactorial N

/-- **The trace counts injections** `δ^{j₁…j_N}_{j₁…j_N} = |Fin N ↪ Fin n|`: the nonzero components of
the totally antisymmetric generalized Kronecker delta are the injective index assignments. -/
theorem genKroneckerTrace_eq_card_embeddings (n N : ℕ) :
    genKroneckerTrace n N = Fintype.card (Fin N ↪ Fin n) := by
  unfold genKroneckerTrace
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-- **Lovelock's Eq. 2.6** `δ^{j₁…j_N}_{j₁…j_N} = 0 ↔ n < N`: the generalized Kronecker delta vanishes
identically when it records more indices than the dimension. -/
theorem genKroneckerTrace_eq_zero_iff (n N : ℕ) : genKroneckerTrace n N = 0 ↔ n < N :=
  Nat.descFactorial_eq_zero_iff_lt

/-- **The trace is positive exactly when `N ≤ n`**: a generalized Kronecker delta with at most `n`
indices is nonzero. -/
theorem genKroneckerTrace_pos_iff (n N : ℕ) : 0 < genKroneckerTrace n N ↔ N ≤ n := by
  rw [Nat.pos_iff_ne_zero, ne_eq, genKroneckerTrace_eq_zero_iff, not_lt]

/-! ## §B — the Lovelock tensor series (Eq. 2.5): order-`p` term has `2p+1` indices -/

/-- **A Lovelock tensor term survives iff `2p+1 ≤ n`**: the order-`p` term of `A^{ij}` (Eq. 2.5) records
a generalized Kronecker delta with `2p+1` upper indices, so it is nonzero exactly when `2p+1 ≤ n`. -/
theorem lovelockTensorTerm_pos_iff (p n : ℕ) :
    0 < genKroneckerTrace n (2 * p + 1) ↔ 2 * p + 1 ≤ n :=
  genKroneckerTrace_pos_iff n (2 * p + 1)

/-- **A Lovelock tensor term vanishes iff `n < 2p+1`.** -/
theorem lovelockTensorTerm_eq_zero_iff (p n : ℕ) :
    genKroneckerTrace n (2 * p + 1) = 0 ↔ n < 2 * p + 1 :=
  genKroneckerTrace_eq_zero_iff n (2 * p + 1)

/-! ## §C — the Lovelock Lagrangian series (Eq. 3.1): order-`p` term has `2p` indices -/

/-- **A Lovelock Lagrangian term survives iff `2p ≤ n`** (equivalently `p ≤ ⌊n/2⌋ = m`): the order-`p`
Euler-density term of `L` (Eq. 3.1) has a generalized Kronecker delta with `2p` indices. -/
theorem lovelockLagrangianTerm_pos_iff (p n : ℕ) :
    0 < genKroneckerTrace n (2 * p) ↔ 2 * p ≤ n :=
  genKroneckerTrace_pos_iff n (2 * p)

/-- **The Lovelock Lagrangian top order is `m = ⌊n/2⌋`**: `2p ≤ n ↔ p ≤ n/2`. -/
theorem lovelockLagrangian_top_order (p n : ℕ) :
    0 < genKroneckerTrace n (2 * p) ↔ p ≤ n / 2 := by
  rw [lovelockLagrangianTerm_pos_iff]; omega

/-! ## §D — four dimensions: the Corollary and the Gauss–Bonnet topological term -/

/-- **The `4`D Lovelock tensor terminates at `p = 1`**: every tensor term of order `p ≥ 2` vanishes
(`2p+1 ≥ 5 > 4`), so `A^{ij}` keeps only the cosmological (`p = 0`) and Einstein (`p = 1`) terms — this
is Lovelock's Corollary `A^{ij} = aG^{ij} + bg^{ij}`. -/
theorem lovelock_dim4_tensor_terminates (p : ℕ) (hp : 2 ≤ p) :
    genKroneckerTrace 4 (2 * p + 1) = 0 := by
  rw [genKroneckerTrace_eq_zero_iff]; omega

/-- **The cosmological (`p = 0`) and Einstein (`p = 1`) tensor terms survive in `4`D.** -/
theorem lovelock_dim4_tensor_surviving :
    0 < genKroneckerTrace 4 (2 * 0 + 1) ∧ 0 < genKroneckerTrace 4 (2 * 1 + 1) := by
  rw [genKroneckerTrace_pos_iff, genKroneckerTrace_pos_iff]; omega

/-- **Gauss–Bonnet is topological in `4`D**: the `p = 2` term survives in the **Lagrangian**
(`2·2 = 4 ≤ 4`, `0 < ·`) but its **tensor** vanishes (`2·2+1 = 5 > 4`, `= 0`) — the Gauss–Bonnet density
is a total derivative in four dimensions, contributing nothing to the field equations. -/
theorem lovelock_dim4_gaussBonnet :
    0 < genKroneckerTrace 4 (2 * 2) ∧ genKroneckerTrace 4 (2 * 2 + 1) = 0 := by
  rw [genKroneckerTrace_pos_iff, genKroneckerTrace_eq_zero_iff]; omega

/-- **The `4`D Lagrangian terminates at `p = 2`** (Gauss–Bonnet): every Lagrangian term of order `p ≥ 3`
vanishes (`2p ≥ 6 > 4`). -/
theorem lovelock_dim4_lagrangian_terminates (p : ℕ) (hp : 3 ≤ p) :
    genKroneckerTrace 4 (2 * p) = 0 := by
  rw [genKroneckerTrace_eq_zero_iff]; omega

/-! ## §E — the dimension-by-dimension classification (Lovelock's central point) -/

/-- **Two dimensions: the Einstein tensor is trivial** — the Einstein-tensor Lovelock term (`p = 1`,
`2·1+1 = 3 > 2`) vanishes identically, so `G_{μν} ≡ 0` in two dimensions and the only divergence-free
symmetric metric concomitant is the metric itself (the cosmological term). -/
theorem lovelock_dim2_einstein_trivial : genKroneckerTrace 2 (2 * 1 + 1) = 0 := by
  rw [genKroneckerTrace_eq_zero_iff]; omega

/-- **Two dimensions: only the cosmological (`p = 0`) term survives.** -/
theorem lovelock_dim2_only_cosmological :
    0 < genKroneckerTrace 2 (2 * 0 + 1) ∧ genKroneckerTrace 2 (2 * 1 + 1) = 0 := by
  rw [genKroneckerTrace_pos_iff, genKroneckerTrace_eq_zero_iff]; omega

/-- **Three dimensions: the Einstein tensor exists, Gauss–Bonnet does not** — the Einstein-tensor term
(`p = 1`) survives, but the Gauss–Bonnet Lagrangian term (`p = 2`, `2·2 = 4 > 3`) vanishes. -/
theorem lovelock_dim3 :
    0 < genKroneckerTrace 3 (2 * 1 + 1) ∧ genKroneckerTrace 3 (2 * 2) = 0 := by
  rw [genKroneckerTrace_pos_iff, genKroneckerTrace_eq_zero_iff]; omega

/-- **Five dimensions: Gauss–Bonnet becomes dynamical** — unlike the topological four-dimensional case,
in `n = 5` the Gauss–Bonnet **tensor** term (`p = 2`, `2·2+1 = 5 ≤ 5`) survives, so Gauss–Bonnet gravity
has nontrivial field equations in `D ≥ 5`. -/
theorem lovelock_dim5_gaussBonnet_dynamical : 0 < genKroneckerTrace 5 (2 * 2 + 1) := by
  rw [genKroneckerTrace_pos_iff]

/-! ## §F — counting the independent Lovelock invariants -/

/-- **The number of Lovelock tensor terms in `n` dimensions**: the orders `p` with `2p+1 ≤ n` (each an
independent divergence-free contribution to the gravitational field equations). -/
def lovelockTensorCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => 2 * p + 1 ≤ n)).card

/-- **The count grows as `⌊(n+1)/2⌋`**: one term in `2`D (cosmological only), two in `3`D and `4`D
(add Einstein), three in `5`D and `6`D (add Gauss–Bonnet) — "the number ... depends crucially on the
dimension of the space." -/
theorem lovelockTensorCount_examples :
    lovelockTensorCount 2 = 1 ∧ lovelockTensorCount 3 = 2 ∧ lovelockTensorCount 4 = 2 ∧
      lovelockTensorCount 5 = 3 ∧ lovelockTensorCount 6 = 3 := by
  decide

end Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Complex.Basic

/-!
# The periodic table's spin tower: Madelung period doubling and the `so(4,4)` split

Formalizes the exact mathematics of Varlamov, *The Periodic Table and the Group SO(4,4):
II. Double SO(4,2)-tower* (arXiv:2607.08105): the group-theoretic layer on top of the
repository's `PeriodicTableAufbauStructure` — which already carries the Madelung *ordering*
(`madelungKey` is exactly the paper's `(n+l, n)` rule; `aufbau_madelung_sorted` is Eq. (2);
`noble_gas_numbers` the period closures) — so this module adds only what is new:

* **§A — Madelung shells and period doubling** (§2 of the paper).  The `N = n+l` Madelung
  shell has dimension `Σ_{2l<N} 2(2l+1) = 2·⌈N/2⌉²` (`madelungShellDim_eq`), which equals the
  Aufbau `n`-shell dimension `2n²` at `n = ⌈N/2⌉` (`aufbauShellDim_eq`,
  `madelungShellDim_eq_aufbauShellDim`): *the same dimensions appear for `n`- and
  `(n+l)`-shells, but each occurs twice* — the period-doubling sequence 2,2,8,8,18,18,32,32
  (`madelung_period_doubling`), with the eight-shell double tower closing at `Z = 120`
  (`madelung_tower_closure`), the paper's Ubn endpoint (two beyond the Aufbau list's
  `Z = 118` = Og closure).
* **§B — the `so(4,4)` generators and the spin split** (§3).  On the defining `8×8`
  representation with neutral metric `η = diag(1⁴,−1⁴)`, the generators
  `L_{αβ} = i(η_α E_{αβ} − η_β E_{βα})` satisfy: disjoint index pairs commute
  (`so44Gen_commute_disjoint` — the four Kronecker deltas of the paper's Eq. (5) all vanish),
  hence the four Cartan generators `L₁₂, L₃₄, L₅₆, L₇₈` pairwise commute (`cartan_commute` —
  rank four, one Cartan eigenvalue per quantum number `n, l, m, s`), and the **spin
  generator** `L₇₈` commutes with every generator on the first six indices
  (`spinGen_commutes_conformal`) — the mechanism that splits the Cartan–Weyl basis into two
  structurally identical `so(4,2)` copies.  One overlapping-index instance
  (`so44Gen_overlap_instance`, `[L₀₁, L₁₂] = i·L₀₂`) witnesses Eq. (5) nontrivially — the
  algebra is not abelian, the vanishing above is the *disjointness* mechanism.
* **§C — the 24-cell root split** (§3, Eqs. (10)–(11)).  The `so(4,4)` roots `±e_i ± e_j`
  (`d4Root`) are indexed by `24 = 6·4` sign–pair choices (`d4_root_count`), each of squared
  length two (`d4Root_normSq`), and the spin axis splits them `24 = 12 + 12`
  (`d4_root_split`): twelve roots avoid the spin axis — the `so(4,2)` (cuboctahedron) root
  subsystem — and twelve carry spin charge, the paper's projection of the 24-cell onto two
  cuboctahedra.

**Honest layering.**  Exact combinatorics, matrix algebra on `Matrix.single`, and decidable
root counting.  The full Eq. (5) commutator in all index cases, the 24-cell's self-duality
and its `F₄` symmetry of order 1152, the Yao-basis isomorphism `so(4,2) ≃ su(2,2)`, and the
identification of chemical elements with weight-diagram nodes (Table 1) are the paper's
representation-theoretic layer, cited not re-proven; the element-by-element data already
lives in `aufbauList`.  The antimatter anti-table (§8) is the negative-weight reflection,
not modelled here.

## References

* V. V. Varlamov, *The Periodic Table and the Group SO(4,4): II. Double SO(4,2)-tower*,
  arXiv:2607.08105.
* Carrier reuse: `PeriodicTableAufbauStructure` (`madelungKey`, `subshellCapacity`,
  `aufbauList`, `noble_gas_numbers`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower

/-! ## §A — Madelung shells and period doubling -/

/-- **The Madelung shell dimension**: the total Pauli capacity of the subshells with
`n + l = N` — the valid `(n, l)` have `l ≤ ⌊(N−1)/2⌋`, i.e. `l < ⌈N/2⌉`, so the shell is
`Σ_{l < ⌈N/2⌉} 2(2l+1)`, built from the Aufbau carrier's `subshellCapacity`. -/
def madelungShellDim (N : ℕ) : ℕ :=
  ∑ l ∈ Finset.range ((N + 1) / 2), subshellCapacity (N - l, l)

/-- **The Aufbau shell dimension**: the total capacity of the `n`-shell,
`Σ_{l < n} 2(2l+1)`. -/
def aufbauShellDim (n : ℕ) : ℕ :=
  ∑ l ∈ Finset.range n, subshellCapacity (n, l)

/-- The odd-sum square: `Σ_{l < k} 2(2l+1) = 2k²` — the capacity kernel both shell notions
share. -/
lemma sum_capacity_range (k : ℕ) (n : ℕ → ℕ) :
    ∑ l ∈ Finset.range k, subshellCapacity (n l, l) = 2 * k ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [subshellCapacity]
      ring

/-- **The Aufbau `n`-shell has dimension `2n²`** — the hydrogen-like shell degeneracy. -/
theorem aufbauShellDim_eq (n : ℕ) : aufbauShellDim n = 2 * n ^ 2 :=
  sum_capacity_range n _

/-- **The Madelung `N`-shell has dimension `2·⌈N/2⌉²`** — the paper's sequence
2, 2, 8, 8, 18, 18, 32, 32, … -/
theorem madelungShellDim_eq (N : ℕ) : madelungShellDim N = 2 * ((N + 1) / 2) ^ 2 :=
  sum_capacity_range _ _

/-- **Madelung shells repeat the Aufbau dimensions**: the `N`-shell of the Madelung tower
has exactly the dimension of the Aufbau `⌈N/2⌉`-shell — the same dimensions appear for `n`-
and `(n+l)`-shells. -/
theorem madelungShellDim_eq_aufbauShellDim (N : ℕ) :
    madelungShellDim N = aufbauShellDim ((N + 1) / 2) := by
  rw [madelungShellDim_eq, aufbauShellDim_eq]

/-- **Period doubling**: consecutive odd/even Madelung shells have equal dimension,
`dim(2k+1) = dim(2k+2) = 2(k+1)²` — each Aufbau dimension occurs twice in the double
tower, the action of the fourth (spin) Cartan generator. -/
theorem madelung_period_doubling (k : ℕ) :
    madelungShellDim (2 * k + 1) = madelungShellDim (2 * k + 2) := by
  rw [madelungShellDim_eq, madelungShellDim_eq]
  congr 2
  omega

/-- **The eight-shell double tower closes at `Z = 120`** (Ubn, the paper's endpoint):
`Σ_{N=1}^{8} madelungShellDim N = 2·(1+1+4+4+9+9+16+16) = 120` — two elements past the
Aufbau list's `Z = 118` (Og) closure recorded in `noble_gas_numbers`. -/
theorem madelung_tower_closure :
    ∑ N ∈ Finset.range 8, madelungShellDim (N + 1) = 120 := by
  decide

/-! ## §B — the `so(4,4)` generators and the spin split -/

/-- The neutral `(4,4)` metric signs `η = diag(1,1,1,1,−1,−1,−1,−1)`. -/
def eta (i : Fin 8) : ℂ := if (i : ℕ) < 4 then 1 else -1

/-- **The `so(4,4)` generator** `L_{αβ} = i(η_α E_{αβ} − η_β E_{βα})` on the defining
eight-dimensional representation. -/
noncomputable def so44Gen (α β : Fin 8) : Matrix (Fin 8) (Fin 8) ℂ :=
  Complex.I • (eta α • Matrix.single α β 1 - eta β • Matrix.single β α 1)

/-- **Disjoint index pairs commute**: when `{α,β} ∩ {γ,δ} = ∅`, all four Kronecker deltas
of the paper's Eq. (5) vanish and `[L_{αβ}, L_{γδ}] = 0` — every `Matrix.single` product
has mismatched middle indices. -/
theorem so44Gen_commute_disjoint {α β γ d : Fin 8}
    (hαγ : α ≠ γ) (hαd : α ≠ d) (hβγ : β ≠ γ) (hβd : β ≠ d) :
    so44Gen α β * so44Gen γ d = so44Gen γ d * so44Gen α β := by
  have e1 : Matrix.single α β (1 : ℂ) * Matrix.single γ d 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hβγ)]
  have e2 : Matrix.single α β (1 : ℂ) * Matrix.single d γ 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hβd)]
  have e3 : Matrix.single β α (1 : ℂ) * Matrix.single γ d 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hαγ)]
  have e4 : Matrix.single β α (1 : ℂ) * Matrix.single d γ 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hαd)]
  have f1 : Matrix.single γ d (1 : ℂ) * Matrix.single α β 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hαd.symm)]
  have f2 : Matrix.single γ d (1 : ℂ) * Matrix.single β α 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hβd.symm)]
  have f3 : Matrix.single d γ (1 : ℂ) * Matrix.single α β 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hαγ.symm)]
  have f4 : Matrix.single d γ (1 : ℂ) * Matrix.single β α 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hβγ.symm)]
  unfold so44Gen
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub,
    e1, e2, e3, e4, f1, f2, f3, f4, smul_zero, sub_self]

/-- The four Cartan generators of the paper's Eq. (6). -/
noncomputable def cartanL12 : Matrix (Fin 8) (Fin 8) ℂ := so44Gen 0 1
/-- The second Cartan generator `L₃₄`. -/
noncomputable def cartanL34 : Matrix (Fin 8) (Fin 8) ℂ := so44Gen 2 3
/-- The third (radial) Cartan generator `L₅₆`. -/
noncomputable def cartanL56 : Matrix (Fin 8) (Fin 8) ℂ := so44Gen 4 5
/-- **The spin generator** `L₇₈` — the fourth Cartan generator, whose eigenvalue is the
fourth quantum number `s`. -/
noncomputable def spinGen : Matrix (Fin 8) (Fin 8) ℂ := so44Gen 6 7

/-- **The Cartan subalgebra is abelian and of rank four**: `L₁₂, L₃₄, L₅₆, L₇₈` pairwise
commute — one Cartan eigenvalue for each of the four quantum numbers `n, l, m, s`, the
paper's reason for passing from the rank-three `so(4,2)` to `so(4,4)`. -/
theorem cartan_commute :
    (cartanL12 * cartanL34 = cartanL34 * cartanL12) ∧
    (cartanL12 * cartanL56 = cartanL56 * cartanL12) ∧
    (cartanL12 * spinGen = spinGen * cartanL12) ∧
    (cartanL34 * cartanL56 = cartanL56 * cartanL34) ∧
    (cartanL34 * spinGen = spinGen * cartanL34) ∧
    (cartanL56 * spinGen = spinGen * cartanL56) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact so44Gen_commute_disjoint (by decide) (by decide) (by decide) (by decide)

/-- **The spin generator commutes with the conformal block**: `L₇₈` commutes with every
generator `L_{αβ}` on the first six indices — the fifteen generators of `so(4,2)`.  This is
the splitting mechanism: the Cartan–Weyl basis of `so(4,4)` breaks into two structurally
identical `so(4,2)` copies labelled by the spin eigenvalue (two-valuedness). -/
theorem spinGen_commutes_conformal {α β : Fin 8}
    (hα : (α : ℕ) < 6) (hβ : (β : ℕ) < 6) :
    so44Gen α β * spinGen = spinGen * so44Gen α β := by
  unfold spinGen
  exact so44Gen_commute_disjoint
    (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
    (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))

/-- **A nontrivial Eq. (5) instance**: `[L₀₁, L₁₂] = i·L₀₂` — overlapping index pairs do
not commute; the vanishing in `so44Gen_commute_disjoint` is the disjointness mechanism, not
abelianness. -/
theorem so44Gen_overlap_instance :
    so44Gen 0 1 * so44Gen 1 2 - so44Gen 1 2 * so44Gen 0 1
      = Complex.I • so44Gen 0 2 := by
  have h1 : Matrix.single (0 : Fin 8) (1 : Fin 8) (1 : ℂ) * Matrix.single (1 : Fin 8) (2 : Fin 8) (1 : ℂ)
      = Matrix.single (0 : Fin 8) (2 : Fin 8) (1 : ℂ) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have h2 : Matrix.single (2 : Fin 8) (1 : Fin 8) (1 : ℂ) * Matrix.single (1 : Fin 8) (0 : Fin 8) (1 : ℂ)
      = Matrix.single (2 : Fin 8) (0 : Fin 8) (1 : ℂ) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have z1 : Matrix.single (0 : Fin 8) (1 : Fin 8) (1 : ℂ) * Matrix.single (2 : Fin 8) (1 : Fin 8) (1 : ℂ) = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := by decide)]
  have z2 : Matrix.single (1 : Fin 8) (0 : Fin 8) (1 : ℂ) * Matrix.single (1 : Fin 8) (2 : Fin 8) (1 : ℂ) = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := by decide)]
  have z3 : Matrix.single (1 : Fin 8) (0 : Fin 8) (1 : ℂ) * Matrix.single (2 : Fin 8) (1 : Fin 8) (1 : ℂ) = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := by decide)]
  have z4 : Matrix.single (1 : Fin 8) (2 : Fin 8) (1 : ℂ) * Matrix.single (0 : Fin 8) (1 : Fin 8) (1 : ℂ) = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := by decide)]
  have z5 : Matrix.single (1 : Fin 8) (2 : Fin 8) (1 : ℂ) * Matrix.single (1 : Fin 8) (0 : Fin 8) (1 : ℂ) = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := by decide)]
  have z6 : Matrix.single (2 : Fin 8) (1 : Fin 8) (1 : ℂ) * Matrix.single (0 : Fin 8) (1 : Fin 8) (1 : ℂ) = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := by decide)]
  unfold so44Gen eta
  simp only [show ((0 : Fin 8) : ℕ) < 4 from by decide, if_pos,
    show ((1 : Fin 8) : ℕ) < 4 from by decide,
    show ((2 : Fin 8) : ℕ) < 4 from by decide, one_smul,
    smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul,
    h1, h2, z1, z2, z3, z4, z5, z6, smul_zero, sub_zero, zero_sub]
  module

/-! ## §C — the 24-cell root split -/

/-- **A `so(4,4)` root vector** `s·e_i + t·e_j` with signs `s, t ∈ {±1}` — the `D₄` root
system, whose 24 vectors are the vertices of the 24-cell. -/
def d4Root (i j : Fin 4) (s t : Bool) : Fin 4 → ℤ :=
  fun k => (if k = i then (if s then 1 else -1) else 0)
    + (if k = j then (if t then 1 else -1) else 0)

/-- **There are 24 roots**: six index pairs `i < j` times four sign choices. -/
theorem d4_root_count :
    (Finset.univ.filter
      (fun p : (Fin 4 × Fin 4) × Bool × Bool => p.1.1 < p.1.2)).card = 24 := by
  decide

/-- **Every root has squared length two**: `‖±e_i ± e_j‖² = 2` for `i < j`. -/
theorem d4Root_normSq (i j : Fin 4) (s t : Bool) (hij : i < j) :
    ∑ k, (d4Root i j s t k) ^ 2 = 2 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> cases s <;> cases t <;> decide

/-- **The spin axis splits the 24-cell `24 = 12 + 12`**: twelve roots avoid the fourth
(spin) axis — the cuboctahedral root subsystem of `so(4,2)`, whose generators commute with
`L₇₈` — and twelve carry spin charge; the paper's projection of the four-dimensional
24-cell onto two three-dimensional cuboctahedra (Eqs. (10)–(11)). -/
theorem d4_root_split :
    (Finset.univ.filter
      (fun p : (Fin 4 × Fin 4) × Bool × Bool =>
        p.1.1 < p.1.2 ∧ p.1.1 ≠ 3 ∧ p.1.2 ≠ 3)).card = 12 ∧
    (Finset.univ.filter
      (fun p : (Fin 4 × Fin 4) × Bool × Bool =>
        p.1.1 < p.1.2 ∧ (p.1.1 = 3 ∨ p.1.2 = 3))).card = 12 := by
  constructor <;> decide

/-! ## §D — the floor structure: SO(4) Fock diagrams and the Rydberg doubling (paper §4)

Each floor `n` of an SO(4,2)-tower realizes the Fock `(j,j)`-representation of the subgroup
`SO(4) ≃ SU(2)×SU(2)` with `n = 2j+1`, of dimension `(2j+1)² = n²`; its decomposition into
Haenzel rings (the `l`-subshells, the diagonal-`SO(3)` branching `(j,j) = ⊕_{l≤2j} D_l`) is
the odd-sum identity below.  The combined tower doubles each node by spin — Sommerfeld's
"cabalistic" Rydberg sequence `2n² = 2, 8, 18, 32, …` (Eq. (12), the *horizontal* or *spin*
doubling), distinct from the *vertical* period doubling of `madelung_period_doubling`
(Eq. (13)). -/

/-- **The SO(4) Fock dimension of the `n`-th floor**: `n²`, the dimension of the
`(j,j)`-representation at `n = 2j+1`. -/
def so4FockDim (n : ℕ) : ℕ := n ^ 2

/-- **The floor decomposes into Haenzel rings**: `Σ_{l<n} (2l+1) = n²` — the diagonal-`SO(3)`
branching of the `(j,j)`-diagram into the `l`-subshell rings fills the floor exactly. -/
theorem floor_ring_decomposition (n : ℕ) :
    ∑ l ∈ Finset.range n, (2 * l + 1) = so4FockDim n := by
  unfold so4FockDim
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- **The Rydberg (horizontal/spin) doubling** (Eq. (12)): the Aufbau shell is the
spin-doubled SO(4) floor, `2n²` — the `2` is the action of the fourth Cartan generator on
each node, the doubling *within* a floor, distinct from the vertical doubling *between*
Madelung shells. -/
theorem rydberg_spin_doubling (n : ℕ) :
    aufbauShellDim n = 2 * so4FockDim n := by
  rw [aufbauShellDim_eq, so4FockDim]

/-- **Sommerfeld's sequence** `2, 8, 18, 32` — the first four floors of Eq. (12). -/
theorem rydberg_sequence :
    aufbauShellDim 1 = 2 ∧ aufbauShellDim 2 = 8 ∧
    aufbauShellDim 3 = 18 ∧ aufbauShellDim 4 = 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §E — the Seaborg tower and the 10-periodic extension (paper §§5–6)

The double tower continues past `Z = 120`: the eighth period fills the empty outer rings
with 50 elements (`Z = 119 … 168`, ending at the inert gas Uho), its ninth-period double
likewise, and the 10-periodic extension continues with 72.  The closures follow from a
single closed form for the double tower. -/

/-- **The double-tower closure in closed form**: through `2k` Madelung shells,
`3·Σ_{N=1}^{2k} dim(N) = 2k(k+1)(2k+1)` — the shells pair into doubles `2·2j²`, and the
cumulative total is four times a square pyramidal number. -/
theorem madelung_tower_closure_general (k : ℕ) :
    3 * ∑ N ∈ Finset.range (2 * k), madelungShellDim (N + 1)
      = 2 * k * (k + 1) * (2 * k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, Nat.mul_add, Nat.mul_add, ih,
        madelungShellDim_eq, madelungShellDim_eq]
      have h1 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
      have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      rw [h1, h2]
      ring

/-- **The eighth period has fifty elements** (`Z = 119 … 168`): the ninth Madelung shell
carries `2·5² = 50` states — the Seaborg extension's first new period. -/
theorem eighth_period_length : madelungShellDim 9 = 50 := by
  decide

/-- **The Seaborg tower closes at `Z = 220`**: ten Madelung shells,
`120 + 50 + 50 = 220`. -/
theorem seaborg_tower_closure :
    ∑ N ∈ Finset.range 10, madelungShellDim (N + 1) = 220 := by
  decide

/-- **The 10-periodic extension closes at `Z = 364`**: twelve Madelung shells,
`220 + 72 + 72 = 364`. -/
theorem ten_periodic_tower_closure :
    ∑ N ∈ Finset.range 12, madelungShellDim (N + 1) = 364 := by
  decide

/-! ## §F — the antimatter reflection (paper §8)

The Mendeleev anti-table (antihydrogen, antihelium, …) sits in the same weight diagram as
the negative-weight reflection of the matter tower: on the root side, negation is an
involution of the 24-cell that only flips the sign choices, fixing the index pair — so it
preserves the spin-axis split and the whole period structure descends unchanged to the
anti-tower. -/

/-- **Root negation flips only the signs**: `−(±e_i ± e_j)` is the root with both sign
choices inverted and the *same* index pair — charge conjugation on the 24-cell. -/
theorem d4Root_neg (i j : Fin 4) (s t : Bool) :
    (fun k => -(d4Root i j s t k)) = d4Root i j (!s) (!t) := by
  funext k
  unfold d4Root
  cases s <;> cases t <;>
    by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hij : i = j <;>
      simp [hki, hkj, hij, @eq_comm _ j i]

/-- **Negation is an involution on the root indices**: double sign-flip is the identity —
the anti-table of the anti-table is the matter table. -/
theorem d4Root_neg_involutive (i j : Fin 4) (s t : Bool) :
    d4Root i j (!(!s)) (!(!t)) = d4Root i j s t := by
  simp

/-! ## §G — the Fet scheme carries no extra states (paper §7)

The Ostrovsky–Fet description introduces a fifth quantum number `s′` (basis Eq. (14):
`λ = 0…ν−1`, `μ = −λ…λ`, `s, s′ = ±½`), which the paper shows to be redundant: the higher
symmetry of `SO(4,4)` lets the single spin generator `L₇₈` absorb the two Cartans `τ₃, τ₃′`.
The exact counting face of that absorption: the `ν`-th Fet multiplet carries `4ν²` states —
exactly the two spin-towers' `ν`-th floors, `2·(2ν²)`, with no fifth degree of freedom. -/

/-- **The `ν`-th Fet multiplet count**: `Σ_{λ<ν} (2λ+1)·4 = 4ν²` — the basis ranges of the
paper's Eq. (14). -/
def fetShellCount (ν : ℕ) : ℕ :=
  ∑ lam ∈ Finset.range ν, 4 * (2 * lam + 1)

/-- The Fet multiplet closes to `4ν²`. -/
theorem fetShellCount_eq (ν : ℕ) : fetShellCount ν = 4 * ν ^ 2 := by
  unfold fetShellCount
  induction ν with
  | zero => simp
  | succ ν ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- **The fifth quantum number is redundant**: the `ν`-th Fet multiplet has exactly the
state count of the *two* spin towers' `ν`-th floors, `4ν² = 2·(2ν²)` — the `SO(4,4)` spin
generator absorbs `τ₃, τ₃′`, and the four quantum numbers `n, l, m, s` already carry
everything the five-label scheme describes. -/
theorem fet_count_eq_double_tower (ν : ℕ) :
    fetShellCount ν = 2 * aufbauShellDim ν := by
  rw [fetShellCount_eq, aufbauShellDim_eq]
  ring

/-! ## §H — the two-valuedness of the spin generator

The paper's premise is that the fourth quantum number `s` is the eigenvalue of the fourth
Cartan generator.  On the defining representation this is literal: `L₇₈` acts on its support
plane `span{e₆, e₇}` with exactly the two eigenvalues `±1` — spin two-valuedness as a
spectral fact, the doubling that generates both the left/right towers of §B and the
horizontal doubling of §D. -/

/-- The `+1` eigenvector `e₆ + i·e₇` of the spin generator. -/
noncomputable def spinUp : Fin 8 → ℂ :=
  fun k => if k = 6 then 1 else if k = 7 then Complex.I else 0

/-- The `−1` eigenvector `e₆ − i·e₇` of the spin generator. -/
noncomputable def spinDown : Fin 8 → ℂ :=
  fun k => if k = 6 then 1 else if k = 7 then -Complex.I else 0

/-- **Spin up**: `L₇₈ (e₆ + i e₇) = +1 · (e₆ + i e₇)`. -/
theorem spinGen_spinUp : spinGen.mulVec spinUp = (1 : ℂ) • spinUp := by
  funext k
  simp only [spinGen, so44Gen, eta, Matrix.mulVec, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.single_apply, spinUp, dotProduct, Fin.sum_univ_eight]
  fin_cases k <;> simp [spinUp]

/-- **Spin down**: `L₇₈ (e₆ − i e₇) = −1 · (e₆ − i e₇)` — together with `spinGen_spinUp`,
the spin generator is two-valued on its support plane: the spectral origin of the fourth
quantum number `s = ±½` and of the two towers. -/
theorem spinGen_spinDown : spinGen.mulVec spinDown = (-1 : ℂ) • spinDown := by
  funext k
  simp only [spinGen, so44Gen, eta, Matrix.mulVec, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.single_apply, spinDown, dotProduct, Fin.sum_univ_eight]
  fin_cases k <;> simp [spinDown]

end Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower

end

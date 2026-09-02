/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower
public import Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity

/-!
# The periodic table as pairs of squares: the gnomon layout

Formalizes the exact combinatorial content of Levin, *"Pairs of Squares" Periodic Table*
(arXiv:2506.11247): the number of orbitals at each Madelung energy level is a perfect
square, and the square decomposes into nested Π-shaped stripes — the classical **gnomons**
`(l+1)² − l² = 2l+1` — one per subshell, all sharing the *staple* corner.  Spin doubling
renders each level as a **pair** of congruent squares.  The counting facts are already in
the repository (`Particles.PeriodicTableShellCapacity.sum_odd`,
`PeriodicTableMadelungSpinTower.madelungShellDim_eq`); what this module adds is the
*layout*: the uniform rendering is an actual bijection, not just an equality of counts.

* `squareGrid`, `gnomon`, `stripePlace` — the `k×k` cell square, its `max`-level sets
  (the Π-stripes), and the explicit enumeration of the `l`-th stripe by `2l+1` positions;
* `gnomon_card`, `squareGrid_eq_biUnion` — each stripe has odd size `2l+1`
  (= `spatialDegeneracy`, the subshell weld) and the stripes partition the square:
  the geometric face of `sum_odd`;
* `squareGrid_one`, `squareGrid_mono` — the nested subsquares share the staple corner
  `(0,0)`: Levin's "nested subsquares, sharing the staple point";
* `shellOrbitals_image`, `shellOrbitals_injOn`, `subshell_fills_gnomon` — **the layout
  theorem**: the orbitals `(l, m)` of a `k`-square (shell `n` at `k = n`, Madelung level
  `N` at `k = (N+1)/2`) map bijectively onto the square, subshell `l` landing exactly on
  the `l`-th gnomon;
* `shellOrbitals_card`, `madelungLevel_spatial_capacity` — the square is filled exactly:
  `k²` orbitals by the bijection, `((N+1)/2)²` by
  `Particles.PeriodicTableShellCapacity.sum_odd`;
* `tableReading` with `tableReading_tableLayout` / `tableLayout_tableReading` — the
  explicit two-sided inverse: a cell names the same subshell in every stapled layer,
  Levin's "similar elements fall at the same place in the respective layers";
* `pairs_of_squares`, `shell_pairs_of_squares` — spin doubling: the `Bool ×` pair of
  squares carries exactly `madelungShellDim N` (resp. `aufbauShellDim n`,
  `shellCapacity n`) element cells;
* `blockWidth_eq_gnomon_pair` — footnote 1: the s, p, d, f blocks of the standard table
  are congruent Π-shaped stripes, the spin pair of their gnomon;
* `aufbau_subshells_land` — all 19 physical aufbau subshells (`aufbauList`, Z ≤ 118)
  land inside their level's square.

**Honest layering.**  Pure finite combinatorics on the repository's periodic-table
carriers; every statement is an exact bijection or count.  The paper's page geometry
(colors, stripe orientation Π vs C, the H/He placement footnote) is presentation, not
mathematics, and is not formalized.  Consecutive periods `2k−1, 2k` filling *congruent*
pairs of squares is the existing `madelung_period_doubling`; the square itself is the
`so4FockDim` floor of the Varlamov tower (`squareGrid_card_eq_so4FockDim`).

## References

* L. A. Levin, *"Pairs of Squares" Periodic Table*, arXiv:2506.11247.
* Carrier reuse: `PeriodicTableAufbauStructure` (subshells, `spatialDegeneracy`,
  `aufbauList`), `PeriodicTableMadelungSpinTower` (`madelungShellDim`, `aufbauShellDim`,
  `so4FockDim`), `Particles.PeriodicTableShellCapacity` (`sum_odd`, `shellCapacity`,
  `shellMagneticCount`), `Particles.PeriodicTableBlocks` (`Block`, `blockWidth`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure
open Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableBlocks

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PeriodicTableGnomonSquares

/-! ## §A — the square, its gnomons, and the staple corner -/

/-- The `k×k` square of cells. -/
def squareGrid (k : ℕ) : Finset (ℕ × ℕ) := Finset.range k ×ˢ Finset.range k

/-- The `l`-th **gnomon** (Levin's Π-shaped stripe): the cells at `max`-distance exactly
`l` from the staple corner `(0,0)` — the difference of the nested subsquares
`(l+1)×(l+1)` and `l×l`. -/
def gnomon (l : ℕ) : Finset (ℕ × ℕ) :=
  (squareGrid (l + 1)).filter (fun p => max p.1 p.2 = l)

/-- Position `j` along the `l`-th gnomon: down the last column, then back along the last
row — `(j, l)` for `j ≤ l`, then `(l, 2l − j)`. -/
def stripePlace (l j : ℕ) : ℕ × ℕ := if j ≤ l then (j, l) else (l, 2 * l - j)

lemma mem_squareGrid {k : ℕ} {p : ℕ × ℕ} : p ∈ squareGrid k ↔ p.1 < k ∧ p.2 < k := by
  simp [squareGrid]

lemma mem_squareGrid_iff_max {k : ℕ} {p : ℕ × ℕ} :
    p ∈ squareGrid k ↔ max p.1 p.2 < k := by
  simp [mem_squareGrid]

lemma mem_gnomon {l : ℕ} {p : ℕ × ℕ} : p ∈ gnomon l ↔ max p.1 p.2 = l := by
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    exact Finset.mem_filter.mpr ⟨mem_squareGrid_iff_max.mpr (by omega), hp⟩

/-- The subsquares are nested. -/
theorem squareGrid_mono {j k : ℕ} (h : j ≤ k) : squareGrid j ⊆ squareGrid k := by
  intro p hp
  rw [mem_squareGrid] at hp ⊢
  omega

/-- The innermost subsquare is the **staple point** alone: the corner `(0,0)` shared by
all the nested subsquares of Levin's rendering. -/
theorem squareGrid_one : squareGrid 1 = {(0, 0)} := by
  ext p
  simp [mem_squareGrid, Prod.ext_iff]

/-- The staple corner lies in every nonempty subsquare. -/
theorem staple_mem {k : ℕ} (hk : 0 < k) : ((0, 0) : ℕ × ℕ) ∈ squareGrid k :=
  squareGrid_mono hk (by rw [squareGrid_one]; exact Finset.mem_singleton_self _)

/-! ## §B — each gnomon is a subshell: odd size `2l+1` -/

theorem stripePlace_max (l j : ℕ) (hj : j < 2 * l + 1) :
    max (stripePlace l j).1 (stripePlace l j).2 = l := by
  unfold stripePlace
  split_ifs with h
  · exact max_eq_right h
  · exact max_eq_left (by omega)

theorem stripePlace_mem_gnomon (l j : ℕ) (hj : j < 2 * l + 1) :
    stripePlace l j ∈ gnomon l :=
  mem_gnomon.mpr (stripePlace_max l j hj)

theorem stripePlace_injOn (l : ℕ) :
    Set.InjOn (stripePlace l) (Finset.range (2 * l + 1)) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_range] at ha hb
  unfold stripePlace at hab
  split_ifs at hab <;> rw [Prod.mk.injEq] at hab <;> omega

/-- **The gnomon is exactly the stripe enumeration**: every cell at `max`-level `l` is
`stripePlace l j` for a unique `j < 2l+1`. -/
theorem gnomon_eq_image (l : ℕ) :
    gnomon l = (Finset.range (2 * l + 1)).image (stripePlace l) := by
  apply Finset.Subset.antisymm
  · intro p hp
    rw [mem_gnomon] at hp
    have h1 : p.1 ≤ l := hp ▸ le_max_left p.1 p.2
    have h2 : p.2 ≤ l := hp ▸ le_max_right p.1 p.2
    rcases eq_or_lt_of_le h2 with h2e | h2lt
    · refine Finset.mem_image.mpr ⟨p.1, Finset.mem_range.mpr (by omega), ?_⟩
      unfold stripePlace
      rw [if_pos h1, ← h2e]
    · have h1e : p.1 = l := by
        rcases max_eq_iff.mp hp with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · omega
      refine Finset.mem_image.mpr ⟨2 * l - p.2, Finset.mem_range.mpr (by omega), ?_⟩
      unfold stripePlace
      rw [if_neg (by omega), ← h1e]
      exact congrArg _ (by omega)
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    exact stripePlace_mem_gnomon l j (Finset.mem_range.mp hj)

/-- **Each Π-stripe has odd size** `2l+1` — the gnomon identity `(l+1)² − l² = 2l+1`. -/
theorem gnomon_card (l : ℕ) : (gnomon l).card = 2 * l + 1 := by
  rw [gnomon_eq_image, Finset.card_image_of_injOn (stripePlace_injOn l),
    Finset.card_range]

/-- **The stripe size is the subshell degeneracy**: the `l`-th gnomon holds exactly the
`2l+1` orbitals of an `l`-subshell — Levin's "numbers of orbitals on the respective
subshells", welded to `PeriodicTableAufbauStructure.spatialDegeneracy`. -/
theorem gnomon_card_eq_spatialDegeneracy (n l : ℕ) :
    (gnomon l).card = spatialDegeneracy (n, l) :=
  gnomon_card l

/-! ## §C — the gnomons partition the square -/

theorem gnomon_disjoint {a b : ℕ} (h : a ≠ b) : Disjoint (gnomon a) (gnomon b) := by
  rw [Finset.disjoint_left]
  intro p hpa hpb
  rw [mem_gnomon] at hpa hpb
  exact h (hpa ▸ hpb)

/-- **The Π-stripes tile the square**: the `k×k` square is the disjoint union of its
first `k` gnomons — the geometric face of `sum_odd : Σ_{l<k} (2l+1) = k²`. -/
theorem squareGrid_eq_biUnion (k : ℕ) :
    squareGrid k = (Finset.range k).biUnion gnomon := by
  ext p
  rw [mem_squareGrid_iff_max, Finset.mem_biUnion]
  constructor
  · intro h
    exact ⟨max p.1 p.2, Finset.mem_range.mpr h, mem_gnomon.mpr rfl⟩
  · rintro ⟨l, hl, hp⟩
    rw [mem_gnomon] at hp
    exact hp ▸ Finset.mem_range.mp hl

theorem squareGrid_card (k : ℕ) : (squareGrid k).card = k ^ 2 := by
  rw [squareGrid, Finset.card_product, Finset.card_range, sq]

/-- The stripe cardinalities sum to the square — `sum_odd` recovered by tiling. -/
theorem sum_gnomon_card (k : ℕ) :
    ∑ l ∈ Finset.range k, (gnomon l).card = (squareGrid k).card := by
  rw [squareGrid_eq_biUnion,
    Finset.card_biUnion (fun a _ b _ hab => gnomon_disjoint hab)]

/-- The square a Madelung level fills is the SO(4) Fock floor of the Varlamov tower. -/
theorem squareGrid_card_eq_so4FockDim (k : ℕ) :
    (squareGrid k).card = so4FockDim k :=
  squareGrid_card k

/-- The square is also the shell magnetic count of `PeriodicTableShellCapacity`. -/
theorem squareGrid_card_eq_shellMagneticCount (k : ℕ) :
    (squareGrid k).card = shellMagneticCount k := by
  rw [squareGrid_card, shellMagneticCount_eq_nSq]

/-! ## §D — the Madelung level and its layout onto the square -/

/-- The subshells `(n, l)` of the `N`-th Madelung level: `n + l = N` with `l < n`,
i.e. `l < (N+1)/2`. -/
def madelungLevelSubshells (N : ℕ) : Finset Subshell :=
  (Finset.range ((N + 1) / 2)).image (fun l => (N - l, l))

theorem madelungLevelSubshells_sum {N : ℕ} :
    ∀ s ∈ madelungLevelSubshells N, s.1 + s.2 = N := by
  intro s hs
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hs
  rw [Finset.mem_range] at hl
  simp only
  omega

/-- The level's subshells are physical: `l < n` (bound-state constraint). -/
theorem madelungLevelSubshells_physical {N : ℕ} :
    ∀ s ∈ madelungLevelSubshells N, s.2 < s.1 := by
  intro s hs
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hs
  rw [Finset.mem_range] at hl
  simp only
  omega

/-- **The Madelung level's orbital count is a perfect square** `((N+1)/2)²` — Levin's
central numeric pattern, by `Particles.PeriodicTableShellCapacity.sum_odd`. -/
theorem madelungLevel_spatial_capacity (N : ℕ) :
    ∑ s ∈ madelungLevelSubshells N, spatialDegeneracy s = ((N + 1) / 2) ^ 2 := by
  rw [madelungLevelSubshells,
    Finset.sum_image (fun a _ b _ h => by simpa using (Prod.mk.injEq _ _ _ _).mp h |>.2)]
  simpa [spatialDegeneracy] using sum_odd ((N + 1) / 2)

/-- The orbitals `(l, m)` filling a `k`-square: subshell `l < k`, magnetic position
`m < 2l+1`.  At `k = n` these are the orbitals of electron shell `n`; at `k = (N+1)/2`
those of the `N`-th Madelung level — Levin's two faces of the same square. -/
def shellOrbitals (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range k).biUnion (fun l => {l} ×ˢ Finset.range (2 * l + 1))

/-- The table layout: orbital `(l, m)` is drawn at position `m` along the `l`-th
Π-stripe. -/
def tableLayout (p : ℕ × ℕ) : ℕ × ℕ := stripePlace p.1 p.2

/-- **Each subshell fills its gnomon**: the layout carries the `2l+1` orbitals of
subshell `l` exactly onto the `l`-th Π-stripe. -/
theorem subshell_fills_gnomon (l : ℕ) :
    ({l} ×ˢ Finset.range (2 * l + 1)).image tableLayout = gnomon l := by
  rw [Finset.singleton_product, Finset.map_eq_image, Finset.image_image, gnomon_eq_image]
  rfl

/-- **The layout covers the square**: the `k`-square's orbitals map onto the whole
`k × k` square. -/
theorem shellOrbitals_image (k : ℕ) :
    (shellOrbitals k).image tableLayout = squareGrid k := by
  rw [shellOrbitals, Finset.biUnion_image, squareGrid_eq_biUnion]
  exact Finset.biUnion_congr rfl (fun l _ => subshell_fills_gnomon l)

/-- **The layout is injective**: distinct orbitals get distinct cells — Levin's rendering
is a genuine bijection, "completely uniform". -/
theorem shellOrbitals_injOn (k : ℕ) :
    Set.InjOn tableLayout (shellOrbitals k) := by
  intro p hp q hq hpq
  rw [Finset.mem_coe, shellOrbitals, Finset.mem_biUnion] at hp hq
  obtain ⟨lp, _, hp⟩ := hp
  obtain ⟨lq, _, hq⟩ := hq
  rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hp hq
  have hmp : p.2 < 2 * p.1 + 1 := by omega
  have hmq : q.2 < 2 * q.1 + 1 := by omega
  have hp1 := stripePlace_max p.1 p.2 hmp
  have hq1 := stripePlace_max q.1 q.2 hmq
  unfold tableLayout at hpq
  have hcomp := Prod.ext_iff.mp hpq
  have h1 : p.1 = q.1 := by omega
  have h2 : p.2 = q.2 := by
    apply stripePlace_injOn p.1 (by simpa using hmp) (by simpa [h1] using hmq)
    rw [hpq, h1]
  exact Prod.ext h1 h2

/-- The orbitals fill the square exactly: `k²` of them, now by the bijection.  At
`k = (N+1)/2` this is the Madelung level's orbital count; at `k = n` the shell's. -/
theorem shellOrbitals_card (k : ℕ) :
    (shellOrbitals k).card = k ^ 2 := by
  rw [← Finset.card_image_of_injOn (shellOrbitals_injOn k), shellOrbitals_image,
    squareGrid_card]

/-! ## §E — pairs of squares and the physical table -/

/-- **Pairs of squares**: with the two spin states, each Madelung level fills exactly a
*pair* of `(N+1)/2`-squares of element cells — the title of the rendering, welded to
`madelungShellDim_eq`.  Consecutive periods fill *congruent* pairs by the existing
`madelung_period_doubling`. -/
theorem pairs_of_squares (N : ℕ) :
    ((Finset.univ : Finset Bool) ×ˢ squareGrid ((N + 1) / 2)).card =
      madelungShellDim N := by
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, squareGrid_card,
    madelungShellDim_eq]

/-- **Shells are pairs of squares too** — Levin's opening pattern ("the number of
orbitals in each electron shell is a whole square"), spin-doubled: shell `n` fills a pair
of `n`-squares of element cells, the Rydberg count `aufbauShellDim n = 2n²`. -/
theorem shell_pairs_of_squares (n : ℕ) :
    ((Finset.univ : Finset Bool) ×ˢ squareGrid n).card = aufbauShellDim n := by
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, squareGrid_card,
    aufbauShellDim_eq]

/-- The same pair of squares carries `shellCapacity n` — the
`Particles.PeriodicTableShellCapacity` face of the shell weld. -/
theorem shell_pairs_of_squares_capacity (n : ℕ) :
    ((Finset.univ : Finset Bool) ×ˢ squareGrid n).card = shellCapacity n := by
  rw [shell_pairs_of_squares, aufbauShellDim_eq, shellCapacity_eq_two_nSq]

/-- **The physical table lands in its squares**: every one of the 19 aufbau subshells
(`aufbauList`, covering Z ≤ 118) belongs to the Madelung level of its quantum-number
sum — so the whole table is rendered by the gnomon layout. -/
theorem aufbau_subshells_land :
    ∀ s ∈ aufbauList, s ∈ madelungLevelSubshells (s.1 + s.2) := by decide

/-- **Element blocks are congruent Π-shaped stripes** (Levin's footnote 1): the width of
each block of the standard table — s, p, d, f — is exactly the element-cell count of the
spin pair of its gnomon, the *same* stripe in every period where the block occurs. -/
theorem blockWidth_eq_gnomon_pair (b : Block) :
    blockWidth b = ((Finset.univ : Finset Bool) ×ˢ gnomon (blockAzimuthal b)).card := by
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, gnomon_card]
  cases b <;> rfl

/-! ## §F — reading the table back: the layout is invertible layer by layer

Levin: "if squares are cut out and stapled together instead, similar elements fall at
the same place in the respective layers."  The reading map below recovers the subshell
and magnetic position from a cell alone — it does not depend on the level `k`, so a cell
names the *same* subshell in every stapled layer: that is the group alignment of the
rendering. -/

/-- The reading map: a cell's subshell is its `max`-level (which gnomon), its magnetic
position the place along that gnomon. -/
def tableReading (c : ℕ × ℕ) : ℕ × ℕ :=
  (max c.1 c.2, if c.2 = max c.1 c.2 then c.1 else 2 * max c.1 c.2 - c.2)

/-- Reading inverts drawing: `tableReading ∘ tableLayout = id` on orbitals. -/
theorem tableReading_tableLayout (l j : ℕ) (hj : j < 2 * l + 1) :
    tableReading (tableLayout (l, j)) = (l, j) := by
  simp only [tableLayout, tableReading, stripePlace]
  split_ifs <;> rw [Prod.ext_iff] <;> constructor <;> simp <;> omega

/-- Drawing inverts reading: `tableLayout ∘ tableReading = id` on every cell. -/
theorem tableLayout_tableReading (c : ℕ × ℕ) :
    tableLayout (tableReading c) = c := by
  simp only [tableLayout, tableReading, stripePlace]
  split_ifs <;> rw [Prod.ext_iff] <;> constructor <;> simp <;> omega

/-- The reading of a `k`-square cell is a `k`-square orbital: the two-sided inverse of
the layout bijection lands where it should. -/
theorem tableReading_mem_shellOrbitals {k : ℕ} {c : ℕ × ℕ} (hc : c ∈ squareGrid k) :
    tableReading c ∈ shellOrbitals k := by
  rw [mem_squareGrid] at hc
  rw [shellOrbitals, Finset.mem_biUnion]
  refine ⟨max c.1 c.2, Finset.mem_range.mpr (by omega), ?_⟩
  rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
  unfold tableReading
  exact ⟨rfl, by split_ifs <;> omega⟩

end Physlib.QuantumMechanics.ComplexAction.PeriodicTableGnomonSquares

end

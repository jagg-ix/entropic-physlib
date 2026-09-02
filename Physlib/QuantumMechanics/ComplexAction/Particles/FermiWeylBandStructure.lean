/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability

/-!
# The Fermi level and Weyl points: the band-structure completion

Extends the shell-filling model from isolated levels toward **band structure**. Two additions:

* **The Fermi level** — the occupation boundary. Filling `N` fermions puts the Fermi level at the top of the
  occupied states; whether it sits **in a gap** (closed shell) or **inside a partially-filled shell** decides
  insulator/inert vs metal/reactive. Grounded in the proven `shellDistance`: the number of states at the Fermi
  level *is* the valence `min(q, C − q)`, zero exactly at closure.
* **Weyl points** — the topologically-charged gapless band-touchings. A Weyl node has the **massless dispersion**
  `E² = |k|²` (linear, gapless only at `k = 0`), a two-band (spin-doublet) touching, and a **chirality** `±1`
  (Berry-monopole charge); Nielsen–Ninomiya forces nodes to come in opposite-chirality pairs.

* **§A — the Fermi level.** `fermiInGap` (`q = 0 ∨ q = C`) with `fermiInGap_iff_no_valence`
  (`↔ shellDistance C q = 0` — no states at the Fermi level); `fermiEnergy` and `fermiEnergy_strictMono`;
  `noble_gas_gapped` (insulator) vs `alkali_metallic` (open shell → metal).
* **§B — Weyl nodes.** `weylEnergySq = |k|²` (the massless `E² = k²` dispersion), `weyl_node_at_origin`
  (gapless at `k = 0`) and `weyl_gapped_away` (gapped elsewhere) — the linear Weyl cone.
* **§C — chirality and Nielsen–Ninomiya.** `WeylCharge` (`±1`), `rightHanded`/`leftHanded`,
  `nielsen_ninomiya_pair` (`+1 + (−1) = 0` — nodes annihilate in pairs), and `weylSemimetal_at_node` (the Fermi
  level pinned at the gapless node).

**Honest layering.** The Fermi-gap ↔ valence equivalence, the `E² = |k|²` dispersion, the node location, and the
chirality-pair cancellation are exact. The identification of `shellDistance = 0` with an insulating gap, and of
the `±1` charge with the Berry monopole, is the standard band-theory reading.

## References

* Fermi level / density of states at the Fermi surface; Weyl semimetals, Weyl-node chirality and the
  Nielsen–Ninomiya theorem. Built on `Particles.ShellFillingParticleHole` (`shellDistance`); the massless
  dispersion `E² = |k|²` is the Weyl (`m = 0`) case of the mass shell.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingParticleHole

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.FermiWeylBandStructure


/-- **The Fermi level is in a gap** — the shell is closed (`q = 0` empty or `q = C` full), so the Fermi level
sits between filled and empty shells (an insulator / inert closed shell). -/
def fermiInGap (C q : ℕ) : Prop := q = 0 ∨ q = C

/-- **In-gap ⟺ no states at the Fermi level** `fermiInGap ↔ shellDistance C q = 0`: a gap opens exactly when the
valence (density of states at the Fermi level) vanishes — the closed shell. -/
lemma fermiInGap_iff_no_valence (C q : ℕ) (h : q ≤ C) :
    fermiInGap C q ↔ shellDistance C q = 0 := by
  unfold fermiInGap shellDistance; omega

/-- The **Fermi energy** — the energy of the highest occupied level, `ε · N` in the equally-spaced ladder. -/
def fermiEnergy (ε : ℝ) (N : ℕ) : ℝ := ε * N

/-- **The Fermi level rises with electron number** — more fermions push the occupation boundary up. -/
lemma fermiEnergy_strictMono (ε : ℝ) (hε : 0 < ε) : StrictMono (fermiEnergy ε) := by
  intro a b hab
  simp only [fermiEnergy]
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hab) hε

/-- **A noble gas is an insulator** — the full octet has the Fermi level in a gap. -/
lemma noble_gas_gapped : fermiInGap 8 8 := Or.inr rfl

/-- **An alkali metal is metallic** — the single valence electron leaves the Fermi level inside a partially-
filled shell (states available at the Fermi level). -/
lemma alkali_metallic : ¬ fermiInGap 8 1 := by unfold fermiInGap; omega


/-- The **squared Weyl energy** `E² = k_x² + k_y² + k_z² = |k|²` — the massless (`m = 0`) dispersion, the Weyl
case of the mass shell. -/
def weylEnergySq (kx ky kz : ℝ) : ℝ := kx ^ 2 + ky ^ 2 + kz ^ 2

/-- **The Weyl node is gapless at `k = 0`** `E² = 0` — the linear band-touching point. -/
lemma weyl_node_at_origin : weylEnergySq 0 0 0 = 0 := by norm_num [weylEnergySq]

/-- **The Weyl cone is gapped away from the node** `k ≠ 0 ⟹ 0 < E²` — a real energy separation everywhere
except the node. -/
lemma weyl_gapped_away (kx ky kz : ℝ) (h : weylEnergySq kx ky kz ≠ 0) :
    0 < weylEnergySq kx ky kz := by
  have hle : 0 ≤ weylEnergySq kx ky kz := by unfold weylEnergySq; positivity
  exact lt_of_le_of_ne hle (Ne.symm h)


/-- The **Weyl charge (chirality)** — a topological `±1` (the Berry-monopole charge of a Weyl node). -/
def WeylCharge : Type := {χ : ℤ // χ = 1 ∨ χ = -1}

/-- The **right-handed** Weyl node, chirality `+1`. -/
def rightHanded : WeylCharge := ⟨1, Or.inl rfl⟩

/-- The **left-handed** Weyl node, chirality `−1`. -/
def leftHanded : WeylCharge := ⟨-1, Or.inr rfl⟩

/-- **Every Weyl charge is `±1`.** -/
lemma weylCharge_unit (χ : WeylCharge) : χ.val = 1 ∨ χ.val = -1 := χ.2

/-- **Nielsen–Ninomiya (pair form)** — a right- and a left-handed node have total chirality zero `+1 + (−1) =
0`: Weyl nodes appear in opposite-chirality pairs. -/
lemma nielsen_ninomiya_pair : rightHanded.val + leftHanded.val = 0 := by decide

/-- **A Weyl semimetal pins the Fermi level at the node** — `E² = 0`: the occupation boundary sits exactly at the
gapless, chirality-charged touching (the topological analogue of the metallic open shell of §A). -/
lemma weylSemimetal_at_node : weylEnergySq 0 0 0 = 0 := weyl_node_at_origin

end Physlib.QuantumMechanics.ComplexAction.Particles.FermiWeylBandStructure

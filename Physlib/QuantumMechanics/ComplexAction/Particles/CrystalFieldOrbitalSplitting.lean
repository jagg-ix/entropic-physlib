/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OctahedralRotationalReduction
public import Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIrrepDecomposition
public import Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet

/-!
# Crystal-field orbital splitting: `SO(3) ↓ G` reduction of atomic orbitals

Leverages the molecular character-reduction machinery (Bunker–Jensen) for the **periodic table**: an atomic
orbital of angular momentum `l` is the `(2l+1)`-dimensional `SO(3)` multiplet `D^l`, and in a point-group ligand
field it splits by the *same* `SO(3) ↓ G` reduction, evaluated at `J = l`. The rotational-level reductions
already proved are therefore the crystal-field orbital splittings (with orbital parity `(−1)^l`, giving the
`g`/`u` label).

* **§A — octahedral splitting.** `s_splits` (`A₁g`), `p_splits` (`T₁u`), **`d_splits`** (`E_g ⊕ T₂g` — the
  classic transition-metal `d`-orbital splitting), `f_splits` (`A₂u ⊕ T₁u ⊕ T₂u`). `d_two_levels` (the `d` shell
  splits into exactly two levels).
* **§B — icosahedral splitting: `d` stays degenerate.** **`d_icosahedral_Hg`** (`d ↓ I_h = H_g`, one 5-fold
  level — no splitting), the distinctive feature of icosahedral coordination; contrast `d_octahedral_split`.
* **§C — the `d⁵` high-spin count.** `d5_high_spin` — the split `t₂g³ e_g²` filling has five unpaired electrons
  (reusing `AtomicHundMagnetism.d5_half_filled`), the maximal-spin transition-metal configuration.

**Honest layering.** The orbital splittings are the `SO(3) ↓ G` reductions at `J = l` (proved in
`OctahedralRotationalReduction` / `IcosahedralRotationalIrrepDecomposition`), reinterpreted with the orbital
parity `(−1)^l`. The identification with crystal/ligand-field theory is the standard reading; the energetic
ordering of the split levels is not modelled.

## References

* Crystal/ligand-field splitting of atomic orbitals (Bethe, 1929). Built on
  `ComplexAction.OctahedralRotationalReduction` and `IcosahedralRotationalIrrepDecomposition`;
  `Particles.AtomicHundMagnetism` (`d5_half_filled`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction
open Physlib.QuantumMechanics.ComplexAction.OctahedralRotationalReduction
open Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIrrepDecomposition
open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicHundMagnetism

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.CrystalFieldOrbitalSplitting


/-- **The `s` orbital (`l=0`) is unsplit** — `A₁g` (a single level). -/
lemma s_splits :
    aA1_24 0 = 24 ∧ aA2_24 0 = 0 ∧ aE_24 0 = 0 ∧ aT1_24 0 = 0 ∧ aT2_24 0 = 0 := by decide

/-- **The `p` orbital (`l=1`) is unsplit** — `T₁u` (a single 3-fold level; parity `u`). -/
lemma p_splits :
    aA1_24 1 = 0 ∧ aA2_24 1 = 0 ∧ aE_24 1 = 0 ∧ aT1_24 1 = 24 ∧ aT2_24 1 = 0 := by decide

/-- **The `d` orbital (`l=2`) splits as `E_g ⊕ T₂g`** — the classic transition-metal crystal-field splitting
into a 2-fold `e_g` and a 3-fold `t₂g` level. -/
lemma d_splits :
    aA1_24 2 = 0 ∧ aA2_24 2 = 0 ∧ aE_24 2 = 24 ∧ aT1_24 2 = 0 ∧ aT2_24 2 = 24 := by decide

/-- **The `f` orbital (`l=3`) splits as `A₂u ⊕ T₁u ⊕ T₂u`** — three levels (parity `u`). -/
lemma f_splits :
    aA1_24 3 = 0 ∧ aA2_24 3 = 24 ∧ aE_24 3 = 0 ∧ aT1_24 3 = 24 ∧ aT2_24 3 = 24 := by decide

/-- **The `d` shell splits into exactly two crystal-field levels** `e_g` (dim 2) and `t₂g` (dim 3), summing to
the five `d` orbitals `2 + 3 = 5`. -/
lemma d_two_levels : aE_24 2 / 24 * 2 + aT2_24 2 / 24 * 3 = 5 := by decide


/-- **The `d` orbital is *unsplit* under icosahedral symmetry** — `d ↓ I_h = H_g`, a single 5-fold level
(`H` is the icosahedral 5-dimensional irrep). Icosahedral coordination uniquely preserves the full `d`
degeneracy. -/
lemma d_icosahedral_Hg :
    agMultTimes60 2 = 0 ∧ aT160 2 = 0 ∧ aT260 2 = 0 ∧ aG60 2 = 0 ∧ aH60 2 = 60 := by decide

/-- **Octahedral splits `d`, icosahedral does not** — under `O_h` the `d` shell breaks into two levels
(`aE_24 2 = aT2_24 2 = 24`), whereas under `I_h` it remains one 5-fold level (`aH60 2 = 60`). -/
lemma d_octahedral_split : aE_24 2 = 24 ∧ aT2_24 2 = 24 ∧ aH60 2 = 60 := by decide


/-- **High-spin `d⁵` has five unpaired electrons** — the octahedral `t₂g³ e_g²` filling maximizes spin
(`unpairedElectrons 2 5 = 5`, reusing `AtomicHundMagnetism.d5_half_filled`): `Mn²⁺`/`Fe³⁺`. -/
lemma d5_high_spin : unpairedElectrons 2 5 = 5 := d5_half_filled

end Physlib.QuantumMechanics.ComplexAction.Particles.CrystalFieldOrbitalSplitting

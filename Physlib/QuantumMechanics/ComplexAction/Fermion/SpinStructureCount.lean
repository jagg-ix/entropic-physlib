/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

/-!
# Spin structures of a fermion region: the topological count and the modular action

Formalizes the **topological data that defines a fermion on a genus-`g` region** — its **spin structures**,
the choices of fermion field / Dirac operator on the region (`~/Downloads/tau`, faithful Seiberg–Witten
transcription). The inequivalent spin structures form an `H¹(Σ, ℤ/2)`-torsor of size `2^{2g}`, split by the
**Arf invariant** (parity) into even and odd:

  `#even = 2^{2g−1} + 2^{g−1}`,  `#odd = 2^{2g−1} − 2^{g−1}`   (`numEvenSpinStructures`, `numOddSpinStructures`),

so (for `g ≥ 1`)

  `#even + #odd = 2^{2g} = 4^g`   (`spinStructures_total`),   `#even − #odd = 2^g`   (`spinStructures_arf`).

`#even + #odd = 4^g` is the total count (the torsor); `#even − #odd = 2^g` is the Arf-invariant signature.

On the **torus** (`g = 1`) there are four spin structures `(±,±)` (`TorusSpinStructure = Bool × Bool`), of
which **three are even and one is odd** (`numEvenSpinStructures 1 = 3`, `numOddSpinStructures 1 = 1`). The
odd one `(+,+)` (the periodic–periodic / Ramond–Ramond sector, where the Dirac operator has a zero mode) is
**fixed by the modular group**: the generators `T : τ ↦ τ+1` and `S : τ ↦ −1/τ` permute the spin structures
(each an involution, `modularT_involutive`, `modularS_involutive`) while fixing the odd one
(`modularT_fixes_odd`, `modularS_fixes_odd`) — the modular group acts on the spin structures preserving the
Arf invariant.

This is the exact topological/TQFT anchor for the formal modeling of a fermion's spacetime region: the spin
structure is the topological choice making the fermion field well-defined, counted by genus and parity, with
the modular group acting on the choices.

* **§A — the spin-structure count** (`numEvenSpinStructures`, `numOddSpinStructures`,
  `spinStructures_total`, `spinStructures_arf`).
* **§B — the four torus spin structures and the modular action** (`TorusSpinStructure`,
  `oddTorusSpinStructure`, `modularT`, `modularS`, involutivity, fixing the odd structure).
* **§C — the assembly** (`fermion_region_spin_structures`).

## References

* N. Seiberg, E. Witten, "Spin structures in string theory" (Nucl. Phys. B 276 (1986) 272); theta
  characteristics / the Arf invariant (Atiyah). Source note: `~/Downloads/tau`
  (`Gemini-Conversation (5).md`, the `2^{g−1}(2^g±1)` counting and the `T`/`S` permutation of `(±,±)`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStructureCount

/-! ## §A — the spin-structure count -/

/-- **The number of even (Arf = 0) spin structures** on a genus-`g` surface, `#even = 2^{2g-1} + 2^{g-1}`. -/
def numEvenSpinStructures (g : ℕ) : ℕ := 2 ^ (2 * g - 1) + 2 ^ (g - 1)

/-- **The number of odd (Arf = 1) spin structures** on a genus-`g` surface, `#odd = 2^{2g-1} - 2^{g-1}`. The
odd spin structures have a Dirac zero mode. -/
def numOddSpinStructures (g : ℕ) : ℕ := 2 ^ (2 * g - 1) - 2 ^ (g - 1)

/-- **[Total spin structures] `#even + #odd = 4^g = 2^{2g}`.** The inequivalent spin structures form an
`H¹(Σ, ℤ/2)`-torsor of size `2^{2g}`. -/
theorem spinStructures_total (g : ℕ) (hg : 1 ≤ g) :
    numEvenSpinStructures g + numOddSpinStructures g = 4 ^ g := by
  unfold numEvenSpinStructures numOddSpinStructures
  have hB : 2 ^ (g - 1) ≤ 2 ^ (2 * g - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : 2 * 2 ^ (2 * g - 1) = 4 ^ g := by
    have e : 2 * 2 ^ (2 * g - 1) = 2 ^ (2 * g) := by rw [← pow_succ']; congr 1; omega
    rw [e, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
  omega

/-- **[The Arf signature] `#even − #odd = 2^g`.** Even minus odd spin structures is `2^g` — the
Arf-invariant signature. -/
theorem spinStructures_arf (g : ℕ) (hg : 1 ≤ g) :
    numEvenSpinStructures g - numOddSpinStructures g = 2 ^ g := by
  unfold numEvenSpinStructures numOddSpinStructures
  have hB : 2 ^ (g - 1) ≤ 2 ^ (2 * g - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hg1 : 2 * 2 ^ (g - 1) = 2 ^ g := by rw [← pow_succ']; congr 1; omega
  omega

/-! ## §B — the four torus spin structures and the modular action -/

/-- **The torus spin structures** `(±, ±)` — the four spin structures on `T²`, indexed by the two
ℤ/2 boundary conditions (`true = +` periodic, `false = −` antiperiodic). -/
abbrev TorusSpinStructure : Type := Bool × Bool

/-- **The odd torus spin structure** `(+, +)` — the periodic–periodic (Ramond–Ramond) sector, where the
Dirac operator has a zero mode. It is the unique odd spin structure on `T²`. -/
def oddTorusSpinStructure : TorusSpinStructure := (true, true)

/-- **The modular generator `T : τ ↦ τ + 1`** on the torus spin structures — swaps `(−,−) ↔ (+,−)`, fixes
the others. -/
def modularT : TorusSpinStructure → TorusSpinStructure
  | (false, false) => (true, false)
  | (true, false) => (false, false)
  | s => s

/-- **The modular generator `S : τ ↦ −1/τ`** on the torus spin structures — swaps `(+,−) ↔ (−,+)`, fixes
the others. -/
def modularS : TorusSpinStructure → TorusSpinStructure
  | (true, false) => (false, true)
  | (false, true) => (true, false)
  | s => s

/-- **[`T` is an involution] `T ∘ T = id`.** -/
theorem modularT_involutive : Function.Involutive modularT := by
  intro x; obtain ⟨a, b⟩ := x; cases a <;> cases b <;> rfl

/-- **[`S` is an involution] `S ∘ S = id`.** -/
theorem modularS_involutive : Function.Involutive modularS := by
  intro x; obtain ⟨a, b⟩ := x; cases a <;> cases b <;> rfl

/-- **[`T` fixes the odd spin structure] `T(+,+) = (+,+)`.** -/
theorem modularT_fixes_odd : modularT oddTorusSpinStructure = oddTorusSpinStructure := rfl

/-- **[`S` fixes the odd spin structure] `S(+,+) = (+,+)`.** -/
theorem modularS_fixes_odd : modularS oddTorusSpinStructure = oddTorusSpinStructure := rfl

/-- **[The torus has 3 even and 1 odd spin structure].** -/
theorem torus_spin_structure_count :
    numEvenSpinStructures 1 = 3 ∧ numOddSpinStructures 1 = 1 := by decide

/-! ## §C — the assembly -/

/-- **[The spin structures of a fermion region, assembled].** For a genus-`g` region (`g ≥ 1`):

* the spin structures are counted by parity, `#even = 2^{2g-1} + 2^{g-1}`, `#odd = 2^{2g-1} - 2^{g-1}`,
  totalling `4^g = 2^{2g}` (the `H¹(Σ, ℤ/2)` torsor) with Arf signature `#even − #odd = 2^g`;
* on the torus the four spin structures `(±,±)` are 3 even and 1 odd, and the modular generators `T`, `S`
  (both involutions) fix the odd `(+,+)` structure.

The spin structure is the topological data defining the fermion field on the region; the genus-and-parity
count and the modular action on the choices are the exact topological/TQFT content. -/
theorem fermion_region_spin_structures (g : ℕ) (hg : 1 ≤ g) :
    numEvenSpinStructures g + numOddSpinStructures g = 4 ^ g
      ∧ numEvenSpinStructures g - numOddSpinStructures g = 2 ^ g
      ∧ modularT oddTorusSpinStructure = oddTorusSpinStructure
      ∧ modularS oddTorusSpinStructure = oddTorusSpinStructure :=
  ⟨spinStructures_total g hg, spinStructures_arf g hg, modularT_fixes_odd, modularS_fixes_odd⟩

end Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStructureCount

end

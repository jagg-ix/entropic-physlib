/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson

/-!
# The Wigner–Dunkl oscillator as a Nagao–Nielsen complex oscillator

Bridge connecting the Wigner–Dunkl oscillator (`Dunkl.Oscillator`, from Junker arXiv:2312.12895) to the
Nagao–Nielsen complex harmonic oscillator (`ComplexOscillator.ComplexHarmonicOscillatorBoson`). Both deform the canonical
oscillator; this file shows they are the *same* oscillator viewed through two deformations — a reflection
deformation (`ν`) and a complex frequency (`ω ∈ ℂ`) — that act on orthogonal data (the zero-point energy
vs. the convergence of the path integral).

**Spectrum.** Diagonalizing `H = ½(x² − D_ν²)` with the ladder `a = (x + D_ν)/√2`, `a† = (x − D_ν)/√2`
gives `H = a†a + ½(1 + 2νR)` and `[H, a†] = a†`, hence the Wigner–Dunkl spectrum `E_n = ℏω(n + ν + ½)`.
This is the Nagao–Nielsen complex spectrum `oscillatorEnergy = ℏω(n + ½)` shifted by the **reflection
zero-point** `ℏων`:

* `dunklOscE_eq_nn_shift` — `E_n^{Dunkl} = oscillatorEnergy ℏ ω n + ℏων`.
* `dunklOscE_zero_param` — at `ν = 0` the Dunkl spectrum *is* the Nagao–Nielsen spectrum.
* `dunklOscE_succ_sub` — the level spacing is `ℏω`, identical to `oscillatorEnergy_succ_sub`: the
  reflection deformation moves only the ground state, never the spacing.
* `dunklOscE_zero` — the deformed zero-point energy `E_0 = ℏω(ν + ½)`.

**Algebra.** In Saveliev's `collisionStar` (`ad`) calculus (shared with the Nagao–Nielsen Heisenberg
formalization): the symmetric (parabose) ordering `½(aa† + a†a) = a†a + ½(1 + 2νR)` (`parabose_symHam`)
is exactly the relation that produces the `νR` zero-point shift, from the deformed ladder commutator
`[a, a†] = 1 + 2νR` (`Dunkl.Oscillator`, §D–E). At `ν = 0` it is the canonical oscillator
`½(aa† + a†a) = a†a + ½`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.NagaoNielsenOscillator

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

/-! ## §A — the spectral bridge: the Wigner–Dunkl spectrum is the NN spectrum shifted by `ℏων` -/

/-- **The Wigner–Dunkl oscillator spectrum** `E_n = ℏω(n + ν + ½)` (complex frequency `ω`, as for the
Nagao–Nielsen complex oscillator). Derived from `H = a†a + ½(1 + 2νR)` and `[H, a†] = a†`. -/
noncomputable def dunklOscillatorEnergy (ℏ : ℝ) (ω : ℂ) (ν : ℝ) (n : ℕ) : ℂ :=
  (ℏ : ℂ) * ω * ((n : ℂ) + (ν : ℂ) + 1 / 2)

/-- **[Bridge] The Wigner–Dunkl spectrum is the Nagao–Nielsen spectrum plus the reflection zero-point.**
`E_n^{Dunkl} = oscillatorEnergy ℏ ω n + ℏων` — the reflection deformation `2νR` contributes a rigid shift
`ℏων` of every level on top of the complex Nagao–Nielsen spectrum `ℏω(n + ½)`. -/
theorem dunklOscE_eq_nn_shift (ℏ : ℝ) (ω : ℂ) (ν : ℝ) (n : ℕ) :
    dunklOscillatorEnergy ℏ ω ν n = oscillatorEnergy ℏ ω n + (ℏ : ℂ) * ω * (ν : ℂ) := by
  unfold dunklOscillatorEnergy oscillatorEnergy; ring

/-- **[Bridge] At `ν = 0` the Wigner–Dunkl oscillator is the Nagao–Nielsen complex oscillator**: the
spectra coincide exactly, `E_n^{Dunkl}|_{ν=0} = oscillatorEnergy ℏ ω n`. -/
theorem dunklOscE_zero_param (ℏ : ℝ) (ω : ℂ) (n : ℕ) :
    dunklOscillatorEnergy ℏ ω 0 n = oscillatorEnergy ℏ ω n := by
  unfold dunklOscillatorEnergy oscillatorEnergy; push_cast; ring

/-- **[Bridge] The level spacing is `ℏω`, identical to `oscillatorEnergy_succ_sub`.** The reflection
deformation shifts the whole ladder rigidly and never changes the spacing — so the Wigner–Dunkl oscillator
includes the *same* energy quantum `ℏω` as the Nagao–Nielsen complex oscillator. -/
theorem dunklOscE_succ_sub (ℏ : ℝ) (ω : ℂ) (ν : ℝ) (n : ℕ) :
    dunklOscillatorEnergy ℏ ω ν (n + 1) - dunklOscillatorEnergy ℏ ω ν n = (ℏ : ℂ) * ω := by
  unfold dunklOscillatorEnergy; push_cast; ring

/-- **The deformed zero-point energy** `E_0 = ℏω(ν + ½)` — the Nagao–Nielsen zero-point `ℏω/2` lifted by
the reflection contribution `ℏων`. -/
theorem dunklOscE_zero (ℏ : ℝ) (ω : ℂ) (ν : ℝ) :
    dunklOscillatorEnergy ℏ ω ν 0 = (ℏ : ℂ) * ω * ((ν : ℂ) + 1 / 2) := by
  unfold dunklOscillatorEnergy; push_cast; ring

/-! ## §B — the algebraic bridge: the symmetric (parabose) ordering produces the `νR` zero-point -/

variable {R : Type*} [Ring R]

/-- **[Bridge] The symmetric (parabose) Hamiltonian ordering.** Given the deformed ladder commutator
`[a, a†] = 1 + w` (with `w = 2νR` the reflection term of the Wigner–Dunkl algebra, `Dunkl.Oscillator`
§D–E), the symmetric product is `aa† + a†a = 2·a†a + (1 + w)`. So the normal-ordered Hamiltonian
`½(aa† + a†a) = a†a + ½(1 + w) = a†a + ½ + νR` includes the deformed zero-point `½(1 + 2νR)` — the algebraic
origin of the `ℏων` spectral shift in §A. At `w = 0` (`ν = 0`) this is the canonical oscillator
`½(aa† + a†a) = a†a + ½`. Written in Saveliev's `collisionStar` calculus, shared with the Nagao–Nielsen
Heisenberg/`ad` formalization. -/
theorem parabose_symHam (a adag w : R) (h : collisionStar a adag = 1 + w) :
    a * adag + adag * a = 2 * (adag * a) + (1 + w) := by
  have hh : a * adag - adag * a = 1 + w := h
  rw [sub_eq_iff_eq_add] at hh; rw [hh]; noncomm_ring

/-- **The undeformed (`w = 0`) symmetric ordering** `aa† + a†a = 2·a†a + 1` — the canonical oscillator's
zero-point `½`, recovered from the Wigner–Dunkl algebra at `ν = 0` (the Nagao–Nielsen oscillator limit). -/
theorem parabose_symHam_canonical (a adag : R) (h : collisionStar a adag = 1) :
    a * adag + adag * a = 2 * (adag * a) + 1 := by
  have := parabose_symHam a adag 0 (by rw [h, add_zero]); simpa using this

end Physlib.QuantumMechanics.ComplexAction.Dunkl.NagaoNielsenOscillator

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Verlinde entropic force and Newton's second law derivation

Port of the entropic-force content from
`/Users/macbookpro/Downloads/tau/ChatGPT-Minimal Game Universe
Refinement.md` Replies 21, 24, 26.  The portable substance: the
algebraic **Verlinde formula** and its specialisation to recover
**Newton's second law** from Verlinde's displacement-entropy
ansatz combined with the Unruh temperature.

## The entropic-force formula (Verlinde 2011)

The basic Verlinde claim:

  `F · Δx = T · ΔS`

i.e. the work done by an "entropic force" `F` across a displacement
`Δx` equals the local temperature `T` times the entropy change `ΔS`
of the relevant holographic screen.  Solving for `F`:

  `F = T · ΔS / Δx`

The remarkable specialisation: when `T` is the **Unruh temperature**
`T_U = ℏ·a/(2π·k_B·c)` (for an observer of proper acceleration `a`)
and `ΔS` is the **Verlinde displacement entropy**
`ΔS_V = 2π·k_B·m·c·Δx/ℏ` (a coarse-grained entropy assigned to
displacement of a mass `m` by `Δx`), then the entropic force becomes

  `F = T_U · ΔS_V / Δx = (ℏ·a/(2π·k_B·c)) · (2π·k_B·m·c·Δx/ℏ) / Δx
      = m · a`.

**This is Newton's second law `F = m·a`** recovered from
information-theoretic / thermodynamic primitives.  Verlinde 2011
proposed this as the origin of inertia and gravity at the classical
limit.

## Contents

### §1 — Verlinde entropic force

* `verlindeEntropicForce T ΔS Δx := T · ΔS / Δx`.
* `verlindeEntropicForce_def` and positivity at positive inputs.
* `verlindeEntropicForce_work_identity` — `F · Δx = T · ΔS`.

### §2 — Verlinde displacement entropy

* `verlindeDisplacementEntropy ℏ kB m c Δx := 2π·kB·m·c·Δx/ℏ`.
* Positivity at positive inputs.

### §3 — Newton's second law from Verlinde + Unruh

* `unruhTemperature ℏ kB c a := ℏ·a/(2π·kB·c)` (same form as
  physlib's existing `SemiClassical.hawkingTemperature` with `κ = a`).
* **`newton_second_law_from_verlinde_unruh`** — main theorem:
  combining Verlinde force with Unruh temperature and Verlinde
  displacement entropy gives `F = m·a`.

### Bridge to existing physlib infrastructure

* The Landauer cost `landauerCost T = k_B·T·log 2` from
  `Physlib/Thermodynamics/Landauer.lean` gives the single-bit case of
  the Verlinde force: at `ΔS = k_B·log 2` (one bit), `F·Δx = landauerCost T`.


## References

* Verlinde 2011 *On the Origin of Gravity and the Laws of Newton*,
  JHEP 04, 029, arXiv:1001.0785.
* Unruh 1976 — Unruh temperature.
* `Downloads/tau/ChatGPT-Minimal Game Universe Refinement.md`
  Replies 21, 24, 26 — conceptual source for this port.
* Bekenstein 1973 — entropy of holographic screens (the prior).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics

/-! ## §1 — Verlinde entropic force -/

/-- **Verlinde entropic force** `F = T·ΔS/Δx`.

The entropic force across a displacement `Δx` at local temperature
`T` with entropy change `ΔS`.  Verlinde 2011's central
information-theoretic claim: macroscopic forces arise from entropy
gradients on holographic screens. -/
def verlindeEntropicForce (T ΔS Δx : ℝ) : ℝ := T * ΔS / Δx

/-- Definitional unfolding. -/
@[simp] theorem verlindeEntropicForce_def (T ΔS Δx : ℝ) :
    verlindeEntropicForce T ΔS Δx = T * ΔS / Δx := rfl

/-- **Positivity** at positive temperature, entropy change, and
displacement. -/
theorem verlindeEntropicForce_pos
    {T ΔS Δx : ℝ} (hT : 0 < T) (hΔS : 0 < ΔS) (hΔx : 0 < Δx) :
    0 < verlindeEntropicForce T ΔS Δx := by
  unfold verlindeEntropicForce
  exact div_pos (mul_pos hT hΔS) hΔx

/-- **Verlinde work identity** `F · Δx = T · ΔS`.  Solving for `F`
gives the entropic-force formula. -/
theorem verlindeEntropicForce_work_identity
    {T ΔS Δx : ℝ} (hΔx : Δx ≠ 0) :
    verlindeEntropicForce T ΔS Δx * Δx = T * ΔS := by
  unfold verlindeEntropicForce
  field_simp

/-! ## §2 — Verlinde displacement entropy -/

/-- **Verlinde displacement entropy** `ΔS_V = 2π·k_B·m·c·Δx/ℏ`.

The coarse-grained entropy assigned to displacement of a mass `m`
by `Δx` (Verlinde 2011, Eq. 3.5).  Linear in displacement: each
Compton wavelength `λ_C = ℏ/(mc)` of displacement contributes
`2π·k_B` of entropy. -/
def verlindeDisplacementEntropy (ℏ kB m c Δx : ℝ) : ℝ :=
  2 * Real.pi * kB * m * c * Δx / ℏ

/-- **Positivity** at positive `ℏ, k_B, m, c, Δx`. -/
theorem verlindeDisplacementEntropy_pos
    {ℏ kB m c Δx : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hm : 0 < m) (hc : 0 < c) (hΔx : 0 < Δx) :
    0 < verlindeDisplacementEntropy ℏ kB m c Δx := by
  unfold verlindeDisplacementEntropy
  apply div_pos _ hℏ
  positivity

/-! ## §3 — Unruh temperature (local form for this file) -/

/-- **Unruh temperature** at proper acceleration `a`:
`T_U = ℏ·a/(2π·k_B·c)`.

Local definition for this file's derivations; the more general
`hawkingTemperature` form is in
`Physlib/Relativity/SemiClassical/HawkingTemperature.lean` with
`κ = a` (Schwarzschild horizon-style surface gravity). -/
def unruhTemperature (ℏ kB c a : ℝ) : ℝ :=
  ℏ * a / (2 * Real.pi * kB * c)

/-- Definitional unfolding. -/
@[simp] theorem unruhTemperature_def (ℏ kB c a : ℝ) :
    unruhTemperature ℏ kB c a = ℏ * a / (2 * Real.pi * kB * c) := rfl

/-! ## §4 — Newton's second law from Verlinde + Unruh -/

/-- **:Newton's second law `F = m·a` from Verlinde + Unruh**.

Substituting:

* `T := unruhTemperature ℏ kB c a` (Unruh temperature for proper
  acceleration `a`),
* `ΔS := verlindeDisplacementEntropy ℏ kB m c Δx` (Verlinde
  displacement entropy for mass `m` over displacement `Δx`),

into the entropic-force formula `F = T · ΔS / Δx`, the `ℏ`, `kB`,
`c`, and `Δx` factors cancel, leaving:

  `F = m · a`.

This is the central Verlinde 2011 claim: **Newton's second law
emerges from the holographic / entropic structure** of spacetime
plus the Unruh effect, with no other assumptions.

It is also the precise sense in which Newton's second law is
*derivable* from information-theoretic primitives at the classical
limit — the QIF program's pre-Newton-first-law chain
(`QIFClassicalReduction.lean`, commit `fed131ca`) reduces inertial
motion to a geometric/quantum statement; this theorem closes the
loop by deriving the dynamics (`F = m·a`) from thermodynamics. -/
theorem newton_second_law_from_verlinde_unruh
    {ℏ kB m c Δx a : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hm : 0 < m) (hc : 0 < c)
    (hΔx : 0 < Δx) :
    verlindeEntropicForce
        (unruhTemperature ℏ kB c a)
        (verlindeDisplacementEntropy ℏ kB m c Δx)
        Δx
      = m * a := by
  unfold verlindeEntropicForce unruhTemperature verlindeDisplacementEntropy
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hΔx_ne : Δx ≠ 0 := ne_of_gt hΔx
  have hπ_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## §5 — Bridge to Landauer (single-bit case) -/

/-- **Single-bit Verlinde force ↔ Landauer cost per displacement**.

At a single-bit entropy change `ΔS = k_B · log 2` (one bit erased),
the Verlinde work `F · Δx = T · k_B · log 2` is exactly the
Landauer cost `landauerCost T = k_B · T · log 2` (cf.
`Physlib/Thermodynamics/Landauer.lean`).

This identifies the **Landauer per-bit energy** with the
**Verlinde work for one bit of entropy change** — the same physical
quantity from two angles (information erasure vs entropic
gradient).  Consumer supplies the value of `k_B`. -/
theorem verlindeEntropicForce_single_bit_work
    (T kB Δx : ℝ) (hΔx : Δx ≠ 0) :
    verlindeEntropicForce T (kB * Real.log 2) Δx * Δx =
      T * (kB * Real.log 2) :=
  verlindeEntropicForce_work_identity hΔx

end Physlib.Thermodynamics

end

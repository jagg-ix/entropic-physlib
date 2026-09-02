/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-!
# MIW barrier tunneling: mutual repulsion (Hall–Deckert–Wiseman 1402.6144, §IV.C)

The last of the HDW "quantum phenomena as generic MIW effects" (Ehrenfest, zero-point energy, Heisenberg, and
wavepacket spreading are already formalized).  For `N = 2` worlds approaching a barrier `V₀`, the mutual
repulsion `ℏ²/(4m(x₁−x₂)²)` boosts the **leading** world and slows the **trailing** one, reproducing
quantum-like tunneling and reflection.  In relative/centre-of-mass coordinates (`q = x₂−x₁`), the relative
motion integrates (Eq. cons) to

`q(t)² = q₀² + (ℏt/(mq₀))²`,  with asymptotic separation speed `q̇_∞ = ℏ/(mq₀)`.

* `separationSq_zero`, `separationSq_quadratic` — the squared separation is `q₀² + (ℏ/(mq₀))²·t²` — **quadratic
  in time**, the same inverse-square-driven spreading as `SciamaAdSCPTMiwWavepacketSpreading` (with variance
  `𝒱 = q²/4`).
* `boostedSpeed_gt_v0` — the leading world's speed at the barrier, `v₀ + ℏ/(2mq₀)`, exceeds `v₀`: mutual
  repulsion **boosts** it.
* **`nonclassical_transmission`** — the boosted kinetic energy `½m(v₀+ℏ/2mq₀)²` strictly exceeds the classical
  `½mv₀²`, so the leading world can pass a barrier `V₀` with `½mv₀² < V₀ < ½m(v₀+ℏ/2mq₀)²` — tunneling that is
  classically forbidden.
* `trailingSpeed_lt_v0`, `nonclassical_reflection` — the trailing world's speed `v₀ − ℏ/(2mq₀)` is below `v₀`,
  its kinetic energy below the classical value, so it can be reflected even when `½mv₀² > V₀` — reflection that
  is classically forbidden.

So both nonclassical transmission and reflection arise, for `N = 2`, purely from the inverse-square mutual
repulsion between worlds — no wave function.

Honest scope: the separation solution's quadratic form, the repulsion boost/slowing of the two worlds, and the
kinetic-energy inequalities that make transmission/reflection possible.  The full equations of motion, the
`√(2V₀/m)` classical threshold, and the reflection/transmission probabilities are the paper's dynamical content
(the kinetic-energy form is used to stay import-light, avoiding `√`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwBarrierTunneling

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-! ## A. The separation grows quadratically (spreading) -/

/-- The squared world separation `q(t)² = q₀² + (ℏt/(mq₀))²` (Eq. cons), driven by the inverse-square repulsion. -/
def separationSq (q0 hbar m t : ℝ) : ℝ := q0 ^ 2 + (hbar * t / (m * q0)) ^ 2

/-- **[Initial separation] `q(0)² = q₀²`.** -/
theorem separationSq_zero (q0 hbar m : ℝ) : separationSq q0 hbar m 0 = q0 ^ 2 := by
  unfold separationSq; ring

/-- **[Quadratic separation] `q(t)² = q₀² + (ℏ/(mq₀))²·t²`.**  The squared separation grows quadratically in
time — the same inverse-square-driven spreading, with variance `𝒱 = q²/4`. -/
theorem separationSq_quadratic (q0 hbar m t : ℝ) :
    separationSq q0 hbar m t = q0 ^ 2 + (hbar / (m * q0)) ^ 2 * t ^ 2 := by
  unfold separationSq; ring

/-- The asymptotic separation speed `q̇_∞ = ℏ/(mq₀)`. -/
def maxSeparationSpeed (q0 hbar m : ℝ) : ℝ := hbar / (m * q0)

/-! ## B. Nonclassical transmission: the leading world is boosted -/

/-- The leading world's speed at the barrier: `v₀ + ℏ/(2mq₀)` (half the max separation speed added by
repulsion). -/
def boostedSpeed (v0 q0 hbar m : ℝ) : ℝ := v0 + hbar / (2 * m * q0)

/-- **[Mutual repulsion boosts the leading world] `v₀ < boostedSpeed`.** -/
theorem boostedSpeed_gt_v0 {q0 hbar m : ℝ} (hq : 0 < q0) (hh : 0 < hbar) (hm : 0 < m) (v0 : ℝ) :
    v0 < boostedSpeed v0 q0 hbar m := by
  unfold boostedSpeed
  have : 0 < hbar / (2 * m * q0) := by positivity
  linarith

/-- **[Nonclassical transmission] the boosted kinetic energy exceeds the classical one.**  `½m·boostedSpeed² >
½mv₀²` (for `v₀ ≥ 0`), so the leading world tunnels through any barrier `½mv₀² < V₀ < ½m·boostedSpeed²` —
classically forbidden. -/
theorem nonclassical_transmission {v0 q0 hbar m : ℝ} (hv : 0 ≤ v0) (hq : 0 < q0) (hh : 0 < hbar) (hm : 0 < m) :
    1 / 2 * m * v0 ^ 2 < 1 / 2 * m * boostedSpeed v0 q0 hbar m ^ 2 := by
  unfold boostedSpeed
  have hδ : 0 < hbar / (2 * m * q0) := by positivity
  nlinarith [hδ, hv, hm, mul_pos hm (mul_pos hδ hδ), mul_nonneg (mul_nonneg hm.le hv) hδ.le]

/-! ## C. Nonclassical reflection: the trailing world is slowed -/

/-- The trailing world's speed at the barrier: `v₀ − ℏ/(2mq₀)` (slowed by repulsion). -/
def trailingSpeed (v0 q0 hbar m : ℝ) : ℝ := v0 - hbar / (2 * m * q0)

/-- **[Mutual repulsion slows the trailing world] `trailingSpeed < v₀`.** -/
theorem trailingSpeed_lt_v0 {q0 hbar m : ℝ} (hq : 0 < q0) (hh : 0 < hbar) (hm : 0 < m) (v0 : ℝ) :
    trailingSpeed v0 q0 hbar m < v0 := by
  unfold trailingSpeed
  have : 0 < hbar / (2 * m * q0) := by positivity
  linarith

/-- **[Nonclassical reflection] the trailing world's kinetic energy is below the classical one.**  `½m·
trailingSpeed² < ½mv₀²` (for `trailingSpeed ≥ 0`), so it can be reflected by a barrier `½m·trailingSpeed² < V₀ <
½mv₀²` even when `v₀` alone would classically pass. -/
theorem nonclassical_reflection {v0 q0 hbar m : ℝ} (hq : 0 < q0) (hh : 0 < hbar) (hm : 0 < m)
    (htrail : 0 ≤ trailingSpeed v0 q0 hbar m) :
    1 / 2 * m * trailingSpeed v0 q0 hbar m ^ 2 < 1 / 2 * m * v0 ^ 2 := by
  have hlt : trailingSpeed v0 q0 hbar m < v0 := trailingSpeed_lt_v0 hq hh hm v0
  have hprod : 0 < (v0 - trailingSpeed v0 q0 hbar m) * (v0 + trailingSpeed v0 q0 hbar m) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [hm, hprod, mul_pos hm hprod]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwBarrierTunneling

end

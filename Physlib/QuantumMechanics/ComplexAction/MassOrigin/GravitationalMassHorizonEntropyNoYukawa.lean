/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

/-!
# Mass and decoherence from the gravitational horizon entropy — without a Yukawa coupling

Can the inertial mass be sourced by a **gravity interaction** (Verlinde / holographic entropic gravity)
instead of a Higgs–Yukawa coupling, compatibly with the Nagao–Nielsen complex action `S = S_R + iS_I`? The
material supplies the bridge: the **imaginary action is the Bekenstein–Hawking horizon entropy**
`S_I = (c³/4G) A_H` (the Verlinde `S = A/4G` law, derived "from Regge area tensors"), so the
entropy-production rate is the horizon area growth `Ṡ_I = (c³/4G) Adot_H`, and the mass–entropy duality reads
`m = Ṡ_I/c²`.

This chain is **dimensionally clean** (unlike `m ↔ Θ̇`): `c³/4G` is `[kg/s]`, so `S_I` is an action, `Ṡ_I` an
energy `= −Im E`, and `Ṡ_I/c²` a mass. This file formalizes it and shows it needs **no Higgs VEV `v` and no
Yukawa coupling `y_f`** — only `G`, `c`, and the per-particle horizon area growth `Adot_H`.

* `gravitationalMass G c Adot = (c/4G) Adot_H` — mass from the horizon area growth rate.
* `gravitationalWidth_eq`: the decoherence width is `widthFromRate (Ṡ_I) = (c³/2G) Adot_H` — both mass and width
 come from the *single* gravitational input `Adot_H`, paralleling the Yukawa double role but with `G` (the
 holographic `1/4` fixed by gravity) in place of the free `y_f`.
* `gravitationalWidth_div_mass = 2c²` — the width/mass ratio is **universal** (independent of `G`, `Adot_H`, and
 of any Higgs coupling); the mass scale is gravitational, not Higgsian.
* `norm_nnPathWeight_horizon`: the Nagao–Nielsen path weight is damped by the horizon entropy,
 `‖e^{iS/ℏ}‖ = e^{−(c³/4G)A_H/ℏ}` — the complex-action / Verlinde compatibility (`S_I = horizon entropy`).
* `horizon_static_massless`: a static horizon (`Adot_H = 0`) gives `m = Γ = S_I = 0` — massless ⟺ no horizon
 growth (the reversible limit).

**Scope.** This does *not* derive the mass: the per-particle `Adot_H` is the input that replaces `y_f`
(same parameter count, geometrized). What it genuinely buys is (i) the *coefficient* is fixed by gravity
(`c³/4G`, the holographic `1/4`) rather than a free Higgs VEV, and (ii) the construction is manifestly
gravitational and complex-action-compatible — no Higgs sector is needed for mass or decoherence.

## References

* E. Verlinde, *On the origin of gravity and the laws of Newton* (2011); Bekenstein–Hawking `S = A/4G`.
 N. Nagao, H. B. Nielsen, complex action `S = S_R + iS_I`. `Physlib` (`BenderIdentity`,
 `NonHermitianComplexAction.EntropicDampingEquivalence`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

/-- **The imaginary action = Bekenstein–Hawking horizon entropy** `S_I = (c³/4G) A_H` (Verlinde `S = A/4G`,
the holographic identification of the Nagao–Nielsen imaginary action). -/
noncomputable def horizonImaginaryAction (G c A : ℝ) : ℝ := c ^ 3 / (4 * G) * A

/-- **The entropy-production rate = horizon area growth** `Ṡ_I = (c³/4G) Adot_H` (energy `= −Im E`). -/
noncomputable def horizonEntropyRate (G c Adot : ℝ) : ℝ := c ^ 3 / (4 * G) * Adot

/-- **The gravitational (Higgs-free) mass** `m = Ṡ_I/c²` (mass–entropy duality). -/
noncomputable def gravitationalMass (G c Adot : ℝ) : ℝ := horizonEntropyRate G c Adot / c ^ 2

/-- **[Gravitational mass `= (c/4G) Adot_H`]** the inertial mass is the horizon area growth rate scaled by
`c/4G` — sourced by gravity, with **no Higgs VEV and no Yukawa coupling** in sight. -/
theorem gravitationalMass_eq (G c Adot : ℝ) (hc : c ≠ 0) :
    gravitationalMass G c Adot = c / (4 * G) * Adot := by
  unfold gravitationalMass horizonEntropyRate
  field_simp

/-- **[The decoherence width from the same horizon growth]** `Γ = widthFromRate Ṡ_I = (c³/2G) Adot_H`: the
*single* gravitational input `Adot_H` sources both mass and width (the gravitational analogue of the Yukawa
double role, with `G` replacing the free `y_f`). -/
theorem gravitationalWidth_eq (G c Adot : ℝ) :
    widthFromRate (horizonEntropyRate G c Adot) = c ^ 3 / (2 * G) * Adot := by
  unfold widthFromRate horizonEntropyRate
  ring

/-- **[Universal width/mass ratio `= 2c²`]** the ratio of the gravitational decoherence width to the
gravitational mass is `2c²` — independent of `G`, of `Adot_H`, and of any Higgs coupling. The mass scale is
gravitational, not Higgsian. -/
theorem gravitationalWidth_div_mass (G c Adot : ℝ) (hc : c ≠ 0) (hG : G ≠ 0) (hAdot : Adot ≠ 0) :
    widthFromRate (horizonEntropyRate G c Adot) / gravitationalMass G c Adot = 2 * c ^ 2 := by
  unfold widthFromRate gravitationalMass horizonEntropyRate
  field_simp

/-- **[Nagao–Nielsen × Verlinde compatibility]** the complex-action path weight is damped by the horizon
entropy: `‖e^{iS/ℏ}‖ = e^{−(c³/4G)A_H/ℏ}`. The imaginary action *is* the Bekenstein–Hawking entropy, so the
gravitational suppression is the Nagao–Nielsen weight modulus. -/
theorem norm_nnPathWeight_horizon (S_R G c A ℏ : ℝ) :
    ‖nnPathWeight S_R (horizonImaginaryAction G c A) ℏ‖
      = Real.exp (-(c ^ 3 / (4 * G) * A / ℏ)) := by
  rw [norm_nnPathWeight]; simp only [horizonImaginaryAction]

/-- **[Static horizon ⟹ massless, reversible]** with no horizon growth (`Adot_H = 0`) the mass, decoherence
width, and imaginary-action rate all vanish — the massless/reversible limit (no Higgs needed to make a
particle massless either). -/
@[simp] theorem horizon_static_massless (G c : ℝ) :
    gravitationalMass G c 0 = 0 ∧ horizonEntropyRate G c 0 = 0
      ∧ widthFromRate (horizonEntropyRate G c 0) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [gravitationalMass, horizonEntropyRate, widthFromRate]

end Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

end

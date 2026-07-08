/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum

/-!
# A Regge resonance's width is the entropy-production rate

Two faces of the same complexification are already formalized separately:

* `BenderIdentity` — the complex-action / entropic side: an entropy-production rate `Ṡ_I` gives a resonance
  width `Γ = widthFromRate Ṡ_I = 2 Ṡ_I`, imaginary energy `Im E = −Ṡ_I` (`complexEnergyOfRate`), and lifetime
  `τ = ℏ/Γ` with `τ·Γ = ℏ` (`lifetime_mul_width`).
* `BetheSalpeter.SwiftLeeComplexAngularMomentum` — the Regge side: continuing angular momentum into the complex `J`-plane,
  the signature factor `e^{iπJ}` has modulus `‖e^{iπJ}‖ = e^{−π J_I}` (`norm_reggeSignature`), an entropic
  damping by the imaginary angular momentum `J_I = Im J`.

This file bridges them. On a (locally linear) Regge trajectory `α(s)` with slope `α'`, a resonance of mass
`M` and width `Γ` sits where `Re α(M²)` is the physical spin, and the trajectory's imaginary part is
`Im α(M²) = α' M Γ` — the standard narrow-resonance relation. Inverting, `Γ = Im α/(α' M)`
(`reggeResonanceWidth`). The bridge results:

* `reggeResonanceWidth_eq_widthFromRate_iff`: `Γ_Regge = widthFromRate Ṡ_I ⟺ Im α = 2 α' M Ṡ_I` — the
  **imaginary part of the Regge trajectory is the entropy-production rate** (up to the kinematic factor
  `2α'M`). The Regge width and the entropic width are the same width.
* `reggeResonanceLifetime_eq_lifetimeFromRate` and `reggeResonance_lifetime_mul_width` (`τ·Γ = ℏ`).
* `complexEnergyOfRate_im_eq_negHalf_reggeResonanceWidth`: the Bender resonance complex energy has
  `Im E = −Γ_Regge/2`, the standard `E = E_R − iΓ/2`.
* `norm_reggeSignature_eq_entropicWeight`: `‖e^{iπJ}‖ = e^{−S_I/ℏ}` with imaginary action
  `S_I = reggeSignatureImaginaryAction = π ℏ J_I` — the Regge signature damping is literally the entropic
  Born weight, the imaginary angular momentum sourcing an entropic action.

So "Regge poles are entropic saddles" reduces to the one confirmed identity **decay width = entropy
production** (`Γ = 2 Ṡ_I`, Gamow `τ = ℏ/Γ`): the imaginary angular momentum and the imaginary energy are
the same complexification read on two axes.

## References

* A. R. Swift, B. W. Lee, *Complex Angular Momentum in Spinor Bethe–Salpeter Equation*, Phys. Rev. **131**
  (1963). Regge, *Nuovo Cimento* **14** (1959). `Physlib` (`BenderIdentity`, `BetheSalpeter.SwiftLeeComplexAngularMomentum`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ReggeWidthEntropyProduction

/-! ## §A — the Regge resonance width from the trajectory's imaginary part -/

/-- **The resonance width read off a Regge trajectory** `Γ = Im α/(α' M)` (narrow-resonance, locally linear
trajectory: `Im α(M²) = α' M Γ`). -/
noncomputable def reggeResonanceWidth (imAlpha alphaPrime M : ℝ) : ℝ := imAlpha / (alphaPrime * M)

/-- **The resonance lifetime** `τ = ℏ/Γ` from the Regge width. -/
noncomputable def reggeResonanceLifetime (ℏ imAlpha alphaPrime M : ℝ) : ℝ :=
  ℏ / reggeResonanceWidth imAlpha alphaPrime M

/-- **[Regge width = entropy-production width]** `Γ_Regge = widthFromRate Ṡ_I ⟺ Im α = 2 α' M Ṡ_I`: the
imaginary part of the Regge trajectory equals the Bender entropy-production rate (up to the kinematic factor
`2α'M`). The resonance width computed from the trajectory and the width `2Ṡ_I` from entropy production are
one quantity. -/
theorem reggeResonanceWidth_eq_widthFromRate_iff (imAlpha dSI alphaPrime M : ℝ)
    (hαM : alphaPrime * M ≠ 0) :
    reggeResonanceWidth imAlpha alphaPrime M = widthFromRate dSI
      ↔ imAlpha = 2 * alphaPrime * M * dSI := by
  unfold reggeResonanceWidth widthFromRate
  rw [div_eq_iff hαM]
  constructor <;> intro h <;> (rw [h]; ring)

/-- **[The entropy rate sets the Regge width]** when the trajectory's imaginary part is entropy-sourced,
`Im α = 2 α' M Ṡ_I`, the Regge resonance width is exactly `widthFromRate Ṡ_I = 2 Ṡ_I`. -/
theorem reggeResonanceWidth_of_entropyRate (dSI alphaPrime M : ℝ) (hαM : alphaPrime * M ≠ 0) :
    reggeResonanceWidth (2 * alphaPrime * M * dSI) alphaPrime M = widthFromRate dSI :=
  (reggeResonanceWidth_eq_widthFromRate_iff _ dSI alphaPrime M hαM).mpr rfl

/-! ## §B — lifetime and the Bender resonance energy -/

/-- **[Regge lifetime = entropic lifetime]** with the entropy-sourced trajectory, `τ_Regge = ℏ/(2 Ṡ_I) =
lifetimeFromRate ℏ Ṡ_I`. -/
theorem reggeResonanceLifetime_eq_lifetimeFromRate (ℏ dSI alphaPrime M : ℝ)
    (hαM : alphaPrime * M ≠ 0) :
    reggeResonanceLifetime ℏ (2 * alphaPrime * M * dSI) alphaPrime M = lifetimeFromRate ℏ dSI := by
  unfold reggeResonanceLifetime
  rw [reggeResonanceWidth_of_entropyRate dSI alphaPrime M hαM]
  unfold lifetimeFromRate widthFromRate
  rfl

/-- **[Width–lifetime duality for the Regge resonance]** `τ · Γ = ℏ` (Heisenberg time–energy), the Regge
incarnation of `lifetime_mul_width`. -/
theorem reggeResonance_lifetime_mul_width (ℏ imAlpha alphaPrime M : ℝ)
    (h : reggeResonanceWidth imAlpha alphaPrime M ≠ 0) :
    reggeResonanceLifetime ℏ imAlpha alphaPrime M * reggeResonanceWidth imAlpha alphaPrime M = ℏ := by
  unfold reggeResonanceLifetime
  field_simp

/-- **[The Bender resonance energy is `E_R − iΓ/2`]** with the entropy-sourced trajectory, the imaginary
part of the complex energy is minus half the Regge width: `Im E = −Γ_Regge/2`, the standard resonance pole
`E = E_R − iΓ/2`. -/
theorem complexEnergyOfRate_im_eq_negHalf_reggeResonanceWidth (E_R dSI alphaPrime M : ℝ)
    (hαM : alphaPrime * M ≠ 0) :
    (complexEnergyOfRate E_R dSI).im
      = -(reggeResonanceWidth (2 * alphaPrime * M * dSI) alphaPrime M) / 2 := by
  rw [reggeResonanceWidth_of_entropyRate dSI alphaPrime M hαM, complexEnergyOfRate_im,
    imaginaryEnergyOfRate]
  unfold widthFromRate
  ring

/-! ## §C — the Regge signature damping is the entropic Born weight -/

/-- **The imaginary action encoded in the Regge signature**, `S_I = π ℏ J_I` (`J_I = Im J`): the entropic
action whose Born weight `e^{−S_I/ℏ}` is the signature modulus. -/
noncomputable def reggeSignatureImaginaryAction (ℏ J_im : ℝ) : ℝ := Real.pi * ℏ * J_im

/-- **[Regge signature damping = entropic Born weight]** `‖e^{iπJ}‖ = e^{−S_I/ℏ}` with
`S_I = reggeSignatureImaginaryAction ℏ J_I = π ℏ J_I`. The imaginary angular momentum sources an entropic
action exactly as the imaginary action does for the path-integral weight (`norm_nnPathWeight`). -/
theorem norm_reggeSignature_eq_entropicWeight (ℏ : ℝ) (hℏ : ℏ ≠ 0) (J : ℂ) :
    ‖reggeSignature J‖ = Real.exp (-(reggeSignatureImaginaryAction ℏ J.im) / ℏ) := by
  rw [norm_reggeSignature]
  congr 1
  unfold reggeSignatureImaginaryAction
  field_simp

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ReggeWidthEntropyProduction

end

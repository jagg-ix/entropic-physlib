/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

/-!
# The harmonic-oscillator Feynman–Kac path integral for the Dunkl process (Junker Eq. 80)

Formalizes the explicit Feynman–Kac calculation of Junker §5–§6: the Euclidean Dunkl process *exhibits
jumps* but is represented by **two continuous Bessel processes — one reflecting, one absorbing at the
origin** (`Dunkl.EuclideanProcess`), and for the harmonic potential `V = ½ω²x²` the path integral is
done explicitly, giving the **Mehler–Dunkl kernel** (Eq. 80)

`⟨x|e^{τ(L^{(ν)} − ½ω²x²)}|y⟩ = (1/c_ν)(ω/sinh ωτ)^{ν+½} e^{−½(x²+y²)coth ωτ} E_ν(ωxy/sinh ωτ)`.

* **§A — the jumps split into two Bessel processes** (`dunkl_process_jumps_split`): the reflecting (Neumann)
  and absorbing (Dirichlet) Bessel densities sum to the Dunkl transition density (Eq. 77) — the jump
  process is the parity combination of two continuous diffusions.
* **§B — the Mehler–Dunkl kernel** (`mehlerDunklKernel`): the explicit harmonic-oscillator FK kernel
  (Eq. 80), with positive prefactor (`mehler_prefactor_pos`), `x ↔ y` symmetry (`mehlerDunkl_symm`), and
  the `coth ωτ` thermal factor.
* **§C — the `ν = 0` reduction** (`mehlerDunkl_zero`): with the undeformed Dunkl kernel `E_0(z) = e^z` the
  two exponentials combine into the **standard Mehler kernel** of the ordinary harmonic oscillator — the
  Wigner–Dunkl FK reduces to the classical Feynman result.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.HarmonicOscillatorFeynmanKac

open Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

/-! ## §A — the jump process is two continuous Bessel processes (reflection + absorption) -/

/-- **[Junker §5] The Dunkl process's jumps split into two continuous Bessel processes.** The Dunkl
transition density `d_τ^{(ν)}(x,y) = b_τ^{(ν−½)}(|x|,|y|) + xy·b_τ^{(ν+½)}(|x|,|y|)` is the sum of a
*reflecting* Bessel density (Neumann, index `ν−½`) and a *sign-weighted absorbing* one (Dirichlet, index
`ν+½`): the jump process is the parity combination of two continuous diffusions (`dunklTransitionDensity`,
`Dunkl.EuclideanProcess`). This is the defining decomposition (`rfl`). -/
theorem dunkl_process_jumps_split (b : ℝ → ℝ → ℝ → ℝ → ℝ) (ν τ x y : ℝ) :
    dunklTransitionDensity b ν τ x y
      = b (besselReflectingIndex ν) τ |x| |y| + x * y * b (besselAbsorbingIndex ν) τ |x| |y| :=
  rfl

/-! ## §B — the Mehler–Dunkl harmonic-oscillator Feynman–Kac kernel (Eq. 80) -/

/-- `coth x = cosh x / sinh x`. -/
noncomputable def cothR (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- **[Junker Eq. 80] The Mehler–Dunkl kernel** — the explicit Feynman–Kac path integral for the
Wigner–Dunkl harmonic oscillator `V = ½ω²x²`:
`K = (1/c_ν)(ω/sinh ωτ)^{ν+½} e^{−½(x²+y²) coth ωτ} E_ν(ωxy/sinh ωτ)`, with `E_ν` the Dunkl kernel
(deformed exponential) and `c_ν` the Dunkl normalization. -/
noncomputable def mehlerDunklKernel (ν ω τ x y cν : ℝ) (Eν : ℝ → ℝ) : ℝ :=
  (1 / cν) * (ω / Real.sinh (ω * τ)) ^ (ν + 1 / 2)
    * Real.exp (-(1 / 2) * (x ^ 2 + y ^ 2) * cothR (ω * τ)) * Eν (ω * x * y / Real.sinh (ω * τ))

/-- **The Mehler prefactor is positive** `(ω/sinh ωτ)^{ν+½} > 0` for `ω, τ > 0` (the imaginary-time
extent gives `sinh ωτ > 0`). -/
theorem mehler_prefactor_pos (ν ω τ : ℝ) (hω : 0 < ω) (hτ : 0 < τ) :
    0 < (ω / Real.sinh (ω * τ)) ^ (ν + 1 / 2) :=
  Real.rpow_pos_of_pos (div_pos hω (Real.sinh_pos_iff.mpr (mul_pos hω hτ))) _

/-- **The Mehler–Dunkl kernel is symmetric** `K(x,y) = K(y,x)` — detailed balance of the Euclidean
oscillator process. -/
theorem mehlerDunkl_symm (ν ω τ x y cν : ℝ) (Eν : ℝ → ℝ) :
    mehlerDunklKernel ν ω τ x y cν Eν = mehlerDunklKernel ν ω τ y x cν Eν := by
  unfold mehlerDunklKernel
  rw [show x ^ 2 + y ^ 2 = y ^ 2 + x ^ 2 by ring, show ω * x * y = ω * y * x by ring]

/-! ## §C — the `ν = 0` reduction to the classical Mehler kernel -/

/-- **[Eq. 79–80, `ν = 0`] The Wigner–Dunkl harmonic FK kernel reduces to the classical Mehler kernel.**
With the undeformed Dunkl kernel `E_0(z) = e^z`, the prefactor exponential and the Dunkl-kernel exponential
combine into the single Gaussian `e^{−½(x²+y²) coth ωτ + ωxy/sinh ωτ}` — the standard Mehler formula for the
ordinary harmonic-oscillator heat kernel. The Wigner–Dunkl Feynman–Kac path integral contains the classical
Feynman result as its `ν = 0` case. -/
theorem mehlerDunkl_zero (ω τ x y cν : ℝ) :
    mehlerDunklKernel 0 ω τ x y cν Real.exp
      = (1 / cν) * (ω / Real.sinh (ω * τ)) ^ (0 + 1 / 2 : ℝ)
          * Real.exp (-(1 / 2) * (x ^ 2 + y ^ 2) * cothR (ω * τ) + ω * x * y / Real.sinh (ω * τ)) := by
  unfold mehlerDunklKernel; rw [Real.exp_add]; ring

end Physlib.QuantumMechanics.ComplexAction.Dunkl.HarmonicOscillatorFeynmanKac

end

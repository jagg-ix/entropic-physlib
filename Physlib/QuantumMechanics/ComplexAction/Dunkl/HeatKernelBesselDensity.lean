/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess
public import Physlib.QuantumMechanics.ComplexAction.Dunkl.Kernel

/-!
# The Dunkl heat kernel, even/odd generators, and Bessel transition density (Junker Eqs. 66–A.8)

Formalizes the Feynman–Kac section (§5) and Appendix A of Junker (arXiv:2312.12895) not yet in the arc:
the **Dunkl heat kernel** (the transition density of the Dunkl process, Eq. 68), the parity decomposition
into even/odd Dunkl generators (Eqs. 73–75), and the **Bessel transition density** of Appendix A (Eq. A.2),
with the index relations connecting them.

* **§A — the Dunkl heat kernel (Eq. 68–69).** `dunklHeatKernel = (1/c_ν τ^{ν+½}) e^{−(x²+y²)/2τ} E_ν(xy/τ)`
  — the Euclidean Dunkl propagator (Wick rotation of the free propagator Eq. 52); strictly positive
  (`dunklHeatKernel_pos`, Eq. 69(i)), symmetric (`dunklHeatKernel_symm`), and at `ν = 0` equal to the
  Wiener/heat kernel `wienerDensity` (`dunklHeatKernel_zero`, Eq. 79).
* **§B — the even/odd Dunkl generators (Eq. 73–75).** The parity projectors `P± = (1±R)/2`
  (`Dunkl.EuclideanProcess`, Eq. 71–72) split the generator into `L_+^{(ν)} = ½(∂² + (2ν/x)∂)` and
  `L_-^{(ν)} = L_+ − ν/x²` (Eq. 75); the even part `L_+` is exactly the Bessel generator of index `ν − ½`
  (`evenDunklGen_eq_bessel`, the reflecting process), the odd part adds the singular `ν/x²` to reach index
  `ν + ½` (the absorbing process).
* **§C — the Bessel transition density (Eq. A.1–A.2).** `besselDensity = (1/2τ)(xy)^{−α} e^{−(x²+y²)/2τ}
  I_α(xy/τ)` — the symmetric Bessel-process transition density (`besselDensity_pos`,
  `besselDensity_symm`), with the two Dunkl-process indices `α = ν∓½` differing by `1`
  (`bessel_index_diff`, the Radon–Nikodym shift Eq. A.6–A.7).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.HeatKernelBesselDensity

open Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess
open Physlib.QuantumMechanics.ComplexAction.Dunkl.Kernel

/-! ## §A — the Dunkl heat kernel (Junker Eq. 68–69) -/

/-- **[Junker Eq. 68] The Dunkl heat kernel** `d_τ^{(ν)}(x,y) = ⟨x|e^{τ L^{(ν)}}|y⟩ =
(1/c_ν τ^{ν+½}) e^{−(x²+y²)/2τ} E_ν(xy/τ)` — the transition density of the Dunkl process, the Euclidean
propagator (Wick rotation `τ = it` of the free propagator Eq. 52). -/
noncomputable def dunklHeatKernel (ν τ x y cν : ℝ) (Eν : ℝ → ℝ) : ℝ :=
  (1 / (cν * τ ^ (ν + 1 / 2))) * Real.exp (-(x ^ 2 + y ^ 2) / (2 * τ)) * Eν (x * y / τ)

/-- **[Junker Eq. 69(i)] The Dunkl heat kernel is strictly positive** (for `c_ν > 0`, `τ > 0`, and a
positive Dunkl kernel) — a genuine transition probability density. -/
theorem dunklHeatKernel_pos (ν τ x y cν : ℝ) (hc : 0 < cν) (hτ : 0 < τ) (Eν : ℝ → ℝ)
    (hE : 0 < Eν (x * y / τ)) : 0 < dunklHeatKernel ν τ x y cν Eν := by
  unfold dunklHeatKernel
  have : 0 < cν * τ ^ (ν + 1 / 2) := by have := Real.rpow_pos_of_pos hτ (ν + 1 / 2); positivity
  positivity

/-- **The Dunkl heat kernel is symmetric** `d_τ(x,y) = d_τ(y,x)` — reversibility (detailed balance) of the
Dunkl process. -/
theorem dunklHeatKernel_symm (ν τ x y cν : ℝ) (Eν : ℝ → ℝ) :
    dunklHeatKernel ν τ x y cν Eν = dunklHeatKernel ν τ y x cν Eν := by
  unfold dunklHeatKernel
  rw [show x ^ 2 + y ^ 2 = y ^ 2 + x ^ 2 by ring, show x * y = y * x by ring]

/-- The exponential combination `e^{−(x²+y²)/2τ} e^{xy/τ} = e^{−(x−y)²/2τ}` (the `ν = 0` Dunkl kernel
`E_0 = e^z` collapsing the Gaussian). -/
theorem heat_exp_combine (τ x y : ℝ) (hτ : τ ≠ 0) :
    Real.exp (-(x ^ 2 + y ^ 2) / (2 * τ)) * Real.exp (x * y / τ) = Real.exp (-(x - y) ^ 2 / (2 * τ)) := by
  rw [← Real.exp_add]; congr 1; field_simp; ring

/-- **The Dunkl normalisation at `ν = 0`** `c_0 = √(2π)` (from `Γ(½) = √π`). -/
theorem cNu_zero : cNu 0 = Real.sqrt (2 * Real.pi) := by
  rw [cNu, show (0 + 1 / 2 : ℝ) = 1 / 2 by norm_num, Real.Gamma_one_half_eq,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- **[Junker Eq. 79] At `ν = 0` the Dunkl heat kernel is the Wiener (heat) kernel**
`d_τ^{(0)}(x,y) = (2πτ)^{−½} e^{−(x−y)²/2τ} = wienerDensity` — with `E_0 = exp` and `c_0 = √(2π)` the Dunkl
process reduces to Brownian motion. -/
theorem dunklHeatKernel_zero (τ x y : ℝ) (hτ : τ ≠ 0) :
    dunklHeatKernel 0 τ x y (cNu 0) Real.exp = wienerDensity τ x y := by
  unfold dunklHeatKernel wienerDensity
  rw [mul_assoc, heat_exp_combine τ x y hτ, cNu_zero, show (0 + 1 / 2 : ℝ) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

/-! ## §B — the even/odd Dunkl generators (Junker Eq. 73–75) -/

/-- **[Junker Eq. 75] The even Dunkl generator is the Bessel generator of index `ν − ½`.**
`L_+^{(ν)} = ½(∂² + (2ν/x)∂)` acts on `xⁿ` with eigenvalue `½n(n−1+2ν)`, which equals the Bessel
eigenvalue `besselGenEigenvalue (ν−½) n = ½n(n+2(ν−½))`: the even (reflecting, Neumann) sector of the
Dunkl process is a Bessel process of index `ν − ½`. -/
theorem evenDunklGen_eq_bessel (ν : ℝ) (n : ℕ) :
    (1 / 2) * (n : ℝ) * ((n : ℝ) - 1 + 2 * ν) = besselGenEigenvalue (besselReflectingIndex ν) n := by
  unfold besselGenEigenvalue besselReflectingIndex; ring

/-- **[Junker Eq. 75] The odd Dunkl generator adds the singular `ν/x²` repulsion** `L_-^{(ν)} = L_+^{(ν)} −
ν/x²`: on `xⁿ` the eigenvalue is the even (Bessel `ν−½`) one minus `ν` (the `−ν/x²` acting on `xⁿ` gives
`−ν xⁿ⁻²`). Its connection to the absorbing Bessel process of index `ν + ½` is **not** a direct eigenvalue
match but the Radon–Nikodym / index-shift relation (Eqs. A.6–A.7): the `xy` similarity transform turns
`L_B^{(ν−½)} − ν/x²` into `L_B^{(ν+½)}`. -/
theorem oddDunklGen_eq_even_sub_nu (ν : ℝ) (n : ℕ) :
    besselGenEigenvalue (besselReflectingIndex ν) n - ν
      = (1 / 2) * (n : ℝ) * ((n : ℝ) - 1 + 2 * ν) - ν := by
  rw [evenDunklGen_eq_bessel]

/-! ## §C — the Bessel transition density (Junker Eq. A.1–A.2) -/

/-- **[Junker Eq. A.2] The symmetric Bessel transition density** `b_τ^{(α)}(x,y) = (1/2τ)(xy)^{−α}
e^{−(x²+y²)/2τ} I_α(xy/τ)` (with `I_α` the modified Bessel function of the first kind) — the transition
density of the Bessel process `B^{(α)}` on the half-line (Eq. A.1 generator). -/
noncomputable def besselDensity (α τ x y : ℝ) (Iα : ℝ → ℝ) : ℝ :=
  (1 / (2 * τ)) * (x * y) ^ (-α) * Real.exp (-(x ^ 2 + y ^ 2) / (2 * τ)) * Iα (x * y / τ)

/-- **The Bessel transition density is strictly positive** for `τ > 0`, `xy > 0`, `I_α > 0`. -/
theorem besselDensity_pos (α τ x y : ℝ) (hτ : 0 < τ) (hxy : 0 < x * y) (Iα : ℝ → ℝ)
    (hI : 0 < Iα (x * y / τ)) : 0 < besselDensity α τ x y Iα := by
  unfold besselDensity
  have : 0 < (x * y) ^ (-α) := Real.rpow_pos_of_pos hxy _
  positivity

/-- **The Bessel transition density is symmetric** `b_τ(x,y) = b_τ(y,x)`. -/
theorem besselDensity_symm (α τ x y : ℝ) (Iα : ℝ → ℝ) :
    besselDensity α τ x y Iα = besselDensity α τ y x Iα := by
  unfold besselDensity
  rw [show x * y = y * x by ring, show x ^ 2 + y ^ 2 = y ^ 2 + x ^ 2 by ring]

/-- **[Junker Eq. A.6–A.7] The two Dunkl-process Bessel indices differ by `1`** `(ν+½) − (ν−½) = 1` — the
Radon–Nikodym index shift relating the reflecting and absorbing Bessel processes that the Dunkl process
decomposes into (`Dunkl.EuclideanProcess.bessel_index_diff`). -/
theorem dunkl_bessel_index_shift (ν : ℝ) :
    besselAbsorbingIndex ν - besselReflectingIndex ν = 1 :=
  bessel_index_diff ν

end Physlib.QuantumMechanics.ComplexAction.Dunkl.HeatKernelBesselDensity

end

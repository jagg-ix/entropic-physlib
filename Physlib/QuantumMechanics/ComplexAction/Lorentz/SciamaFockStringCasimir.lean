/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNagaoNielsenZeta
public import Physlib.QuantumMechanics.ComplexAction.AffineKacMoodyConformalAlgebra

/-!
# The bosonic string as a tower of Fock oscillators: Casimir energy, critical dimension, current algebra

The bosonic string is an infinite **tower of the Fock oscillators** of the Sciama arc — one per worldsheet mode
`n = 1, 2, 3, …` per transverse direction — and its whole spectral data is the ζ-regularization machinery
already built (`SciamaFockNagaoNielsenZeta`, `OperatorAlgebra.HurwitzZetaRegularization`):

* `stringMode_spectralZeta_eq_riemann` — the transverse mode tower `n ≥ 1` has spectral zeta
  `Σₙ (n)^{−s} = ζ(s)` (the **Riemann** zeta, `hurwitzZetaSeries s 1`).  Its analytic continuation to `s = −1`
  is `ζ(−1) = −1/12`, so the ζ-regularized zero-point energy `½ Σₙ n = ½ ζ(−1) = −1/24` per transverse boson.
* `stringMode_oscillator_spectralZeta` — with the frequency scale, `Σₙ (ωn)^{−s} = ω^{−s} ζ(s)`.
* `stringIntercept`, `stringIntercept_critical`, `stringIntercept_eq_one_iff` — the Casimir gives the mass-shell
  **intercept** `a = (D−2)/24` (from `−(D−2)/24 = (D−2)·½·ζ(−1)`), and the massless level-1 vector (`a = 1`)
  forces the **critical dimension `D = 26`**.
* `stringOscillator_centralTerm` — the transverse oscillator algebra `[α^X_m, α^Y_{−m}] = m·κ(X, Y)` is exactly
  the **Kac–Moody 2-cocycle** `AffineKacMoodyConformalAlgebra.centralCharge` at `n = −m`: the string current
  algebra's central extension (the `c = D` Virasoro/Heisenberg structure of the worldsheet CFT).

The moding is the Nagao–Nielsen / Wigner–Dunkl `a`-shift of `SciamaFockNagaoNielsenZeta`: integer bosonic modes
give `ζ(s, 1)` (Riemann), the half-integer Neveu–Schwarz modes give `ζ(s, ½)` (`oscillatorEnergyReal`), so the
sector-dependent zero-point is the Hurwitz zeta at the offset `a` set by the boundary conditions.

Honest scope: the mode-tower spectral-zeta identities, the intercept/critical-dimension arithmetic (given the
standard continuation `ζ(−1) = −1/12`, which the convergent `hurwitzZetaSeries` does not itself compute), and
the Kac–Moody central term of the oscillator algebra.  The Virasoro algebra, the no-ghost theorem, and the
analytic continuation of `ζ` to `s = −1` are contextualized, not carried out here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockStringCasimir

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNagaoNielsenZeta

/-- **[String transverse modes = Riemann zeta] `Σₙ (n)^{−s} = ζ(s)`.**  The bosonic string's transverse
oscillator tower `n = 1, 2, …` (each a Fock oscillator) has spectral zeta the Riemann zeta; its continuation
`ζ(−1) = −1/12` is the ζ-regularized `Σₙ n`. -/
theorem stringMode_spectralZeta_eq_riemann (s : ℝ) :
    spectralZeta (fun n => (n : ℝ) + 1) s = riemannZetaSeries s := by
  rw [spectralZeta_linear_eq_hurwitz 1 s (by norm_num)]
  exact (riemannZeta_eq_hurwitz_one s).symm

/-- **[String Casimir zeta with frequency] `Σₙ (ωn)^{−s} = ω^{−s} ζ(s)`.**  The frequency-scaled transverse
mode tower; at `s = −1` its continuation is the Casimir zero-point `−ω/12` (per transverse boson, `×½`). -/
theorem stringMode_oscillator_spectralZeta (ω s : ℝ) (hω : 0 < ω) :
    spectralZeta (fun n => ω * ((n : ℝ) + 1)) s = ω ^ (-s) * riemannZetaSeries s := by
  rw [linear_spectralZeta_eq_hurwitz ω 1 s hω (by norm_num)]
  rw [← riemannZeta_eq_hurwitz_one]

/-- **The Regge/mass-shell intercept** `a = (D−2)/24` — from the ζ-regularized transverse Casimir energy
`−(D−2)/24 = (D−2)·½·ζ(−1)`, `ζ(−1) = −1/12`. -/
def stringIntercept (D : ℝ) : ℝ := (D - 2) / 24

/-- **[Critical dimension] the intercept is `1` in `D = 26`.**  The massless level-1 vector (`a = 1`) fixes the
critical dimension of the bosonic string. -/
theorem stringIntercept_critical : stringIntercept 26 = 1 := by
  rw [stringIntercept]; norm_num

/-- **[Critical dimension, iff] `a = 1 ⟺ D = 26`.**  The intercept equals unity exactly at the critical
dimension. -/
theorem stringIntercept_eq_one_iff (D : ℝ) : stringIntercept D = 1 ↔ D = 26 := by
  rw [stringIntercept, div_eq_iff (by norm_num : (24 : ℝ) ≠ 0)]
  constructor <;> intro h <;> linarith

section CurrentAlgebra

variable {g : Type*} [LieRing g]

open Physlib.QuantumMechanics.ComplexAction.AffineKacMoodyConformalAlgebra

omit [LieRing g] in
/-- **[String oscillators = Kac–Moody central extension] `[α^X_m, α^Y_{−m}] = m·κ(X, Y)`.**  The transverse
string oscillator commutator is exactly the affine Kac–Moody 2-cocycle `centralCharge` evaluated at
`n = −m` — the worldsheet current algebra's central term. -/
theorem stringOscillator_centralTerm (κ : g → g → ℝ) (X Y : g) (m : ℤ) :
    centralCharge κ (X, m) (Y, -m) = (m : ℝ) * κ X Y := by
  unfold centralCharge
  simp

end CurrentAlgebra

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockStringCasimir

end

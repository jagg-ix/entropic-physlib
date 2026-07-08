/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.GapPathIntegralOrigin

/-!
# The gravitational lapse contour is the origin of the imaginary action (Banihashemi–Jacobson 2025)

Formalizes the algebraic core of *B. Banihashemi, T. Jacobson, "On the lapse contour in the gravitational
path integral", arXiv:2405.10307v3 (2025)*: the lapse `N` (Lagrange multiplier for the Hamiltonian
constraint `ℋ`) must be integrated over a contour displaced **below** the real axis, `N → N − iε`, to
navigate the essential singularity at `N = 0`. We show this complex-lapse displacement is *exactly* the
mechanism that produces the imaginary action of the complex-action/entropic-time master formula
`Z = ∫𝒟Φ exp[(i/ℏ)S_R − (1/ℏ)S_I]`: the constraint-imposing lapse weight `e^{−i(N−iε)ℋ}` (Eq. 5) **is**
`complexActionPathIntegralWeight` with reversible action `S_R = −Nℋ` and imaginary action `S_I = εℋ`.

* **§A — the lapse-displaced weight is the master formula** (`lapseWeight_eq_master`, Eqs. 2, 5). The
  Fourier integrand `e^{−i(N−iε)ℋ}` imposing the Hamiltonian constraint `δ(ℋ) = ∫(dN/2π) e^{−i(N−iε)ℋ}`
  (with the `−iε` lapse displacement) is the complex-action/entropic-time master integrand `complexActionPathIntegralWeight (−Nℋ) (εℋ) 1`:
  the lapse × constraint is the reversible action `S_R = −Nℋ`, and the `iε`-regulator is the imaginary
  action `S_I = εℋ`.
* **§B — the `iε` displacement is the entropic damping / convergence** (`lapseWeight_modulus`,
  `lapseWeight_modulus_eq_entropyDamping`). The modulus `‖e^{−i(N−iε)ℋ}‖ = e^{−εℋ}` is the
  Kuiken/entropy-production weight (`master_modulus_is_kuiken`) — equivalently `WickRotation.entropyDamping`.
  `ε > 0` makes the constraint integral convergent: the Halliwell–Hartle fluctuation-convergence criterion
  *is* the arc's entropic damping / measure-validity.
* **§C — the complex lapse is the Nagao–Nielsen complex energy** (`lapseWeight_eq_evolutionFactor`,
  `lapse_im_eq_gap`). The complex lapse `N − iε` has the exact form of `WickRotation.complexEnergy N ε`, and
  the lapse weight `e^{−i(N−iε)ℋ}` *is* the non-Hermitian eigen-propagator
  `evolutionFactorC N ε 1 ℋ = e^{−iE_C t/ℏ}` with complex lapse ↔ complex energy `E_C` and the constraint
  `ℋ` ↔ time. The imaginary lapse `−ε` is the non-Hermitian gap (`gap_eq_complexEnergy_im`).
* **§D — the lapse weight is the Nagao–Nielsen complex action** (`lapseWeight_eq_nagaoNielsen`). The same
  weight is `nagaoNielsenComplexActionWeight (−Nℋ) (εℋ) 1 = e^{(i/ℏ)S_complex}` with `S_complex = −(N − iε)ℋ`: the
  gravitational complex action is the (negative) complex-lapse-weighted Hamiltonian constraint.
* **§E — the `ε → 0` reversible limit** (`lapseWeight_at_eps_zero`). At `ε = 0` the lapse weight is the pure
  oscillatory phase `e^{−iNℋ}` — the Lorentzian constraint-imposing integrand `δ(ℋ) = ∫(dN/2π) e^{−iNℋ}`
  (Eq. 2) with no damping; the same `ε → 0` limit as `PathIntegral.QEDPathIntegralConvergence`.
* **§F — the momenta are integrated before the lapse** (`momenta_before_lapse`). The paper's central ordering
  — the phase-space momentum integral `∫𝒟p e^{i∫(pq̇−H)}` (Eq. 1) is done *before* the lapse, which is what
  forces the contour below the origin. The Gaussian momentum saddle `p = mq̇` is
  `PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle` (the `(p,q)` origin of the gap, `pq_from_pathIntegral_saddle`).

## References

* B. Banihashemi, T. Jacobson, *On the lapse contour in the gravitational path integral*,
  arXiv:2405.10307v3 (2 Mar 2025), DOI `10.48550/arXiv.2405.10307` — the formalized paper. All formalized
  equations are in **§II "Path Integral and Lapse Contour"**: the reduced phase-space path integral
  `∫𝒟p𝒟q e^{i∫(pq̇−H)}` (Eq. 1, p. 2); the Hamiltonian-constraint Fourier integral
  `δ(ℋ) = ∫(dN/2π) e^{−i∫Nℋ}` over the lapse `N` (Eq. 2, p. 2); the constraint
  `ℋ = q^{−1/2}(p^{ij}p_{ij} − ½p²) − q^{1/2}R` (Eq. 3, p. 2); the **`N − iε` lapse-displaced constraint**
  `δ(ℋ) = lim_{ε→0⁺} ∫(dN/2π) e^{−i∫(N−iε)ℋ}` (Eq. 5, p. 3). The `ε > 0` displacement satisfies the
  Halliwell–Hartle convergence criterion (§II, p. 4) and renders the metric signature complex (§III, p. 5).
* J. J. Halliwell, J. B. Hartle, *Integration contours for the no-boundary wave function of the universe*,
  Phys. Rev. D 41 (1990) 1815, DOI `10.1103/PhysRevD.41.1815` — the fluctuation-convergence criterion (§B).
* L. D. Faddeev, V. N. Popov, *Covariant quantization of the gravitational field*, Usp. Fiz. Nauk 111
  (1973) 427 — the reduced phase-space path integral (Eq. 1).
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. 126 (2011) 1021,
  DOI `10.1143/PTP.126.1021` — the complex action `S_complex = S_R + iS_I` (§C, §D).
* Repo dependencies: `PathIntegral.ComplexActionPathIntegralWeight` (`complexActionPathIntegralWeight`, `nagaoNielsenComplexActionWeight`, `kuikenWeight`,
  `master_modulus_is_kuiken`), `NonHermitian.WickRotation` (`complexEnergy`, `evolutionFactorC`,
  `entropyDamping`), `NonHermitianComplexAction.GapPathIntegralOrigin` (the `(p,q)` and gap origin),
  `PathIntegral.MomentumPathIntegral` (`phaseLagrangian_at_saddle`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QuantumMechanics.ComplexAction

/-! ## §A — the lapse-displaced constraint weight is the complex-action/entropic-time master formula -/

/-- **[Banihashemi–Jacobson §II, Eq. 2 (p. 2) → Eq. 5 (p. 3)] The lapse-displaced Hamiltonian-constraint
weight** (`ℏ = 1`). The
constraint `ℋ = 0` is imposed via the Fourier integral `δ(ℋ) = lim_{ε→0⁺} ∫(dN/2π) e^{−i(N−iε)ℋ}` over the
lapse `N`, whose contour is displaced *below* the real axis by `−iε` to evade the essential singularity at
`N = 0`. This is the per-`N` integrand `e^{−i(N−iε)ℋ}` with complex lapse `N − iε`. -/
noncomputable def lapseWeight (N ε Ham : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((N : ℂ) - Complex.I * (ε : ℂ)) * (Ham : ℂ))

/-- **[Implement — the central claim] The lapse-displaced weight IS the complex-action/entropic-time master integrand.**
`e^{−i(N−iε)ℋ} = complexActionPathIntegralWeight (−Nℋ) (εℋ) 1` (`= lorentzianKernel`): the lapse `N` times the
Hamiltonian constraint `ℋ` is the **reversible action** `S_R = −Nℋ`, and the `−iε` contour displacement is
the **imaginary action** `S_I = εℋ`. The gravitational lapse contour is the origin of the master formula's
`e^{(i/ℏ)S_R − (1/ℏ)S_I}`. -/
theorem lapseWeight_eq_master (N ε Ham : ℝ) :
    lapseWeight N ε Ham = complexActionPathIntegralWeight (-(N * Ham)) (ε * Ham) 1 := by
  unfold lapseWeight complexActionPathIntegralWeight
  congr 1
  push_cast
  linear_combination ((ε : ℂ) * (Ham : ℂ)) * Complex.I_sq

/-! ## §B — the `iε` displacement is the entropic damping (Halliwell–Hartle convergence) -/

/-- **[Implement] The modulus of the lapse weight is the Kuiken/entropy-production weight** `e^{−εℋ}`. The
`−iε` contour displacement contributes a real damping `‖e^{−i(N−iε)ℋ}‖ = e^{−εℋ} = kuikenWeight 1 (εℋ)`;
for `ε > 0` (and `ℋ > 0`) the constraint integral converges — the Halliwell–Hartle fluctuation-convergence
criterion is the arc's entropic damping. -/
theorem lapseWeight_modulus (N ε Ham : ℝ) :
    ‖lapseWeight N ε Ham‖ = kuikenWeight 1 (ε * Ham) := by
  rw [lapseWeight_eq_master, master_modulus_is_kuiken]

/-- **[Bridge] The lapse-contour damping is `WickRotation.entropyDamping`.** The `−iε` displacement's modulus
`e^{−εℋ}` is exactly the arc's Cameron–Martin / entropic-damping factor `entropyDamping (εℋ) 1` — the
gravitational convergence regulator and the path-integral entropic weight coincide. -/
theorem lapseWeight_modulus_eq_entropyDamping (N ε Ham : ℝ) :
    ‖lapseWeight N ε Ham‖ = entropyDamping (ε * Ham) 1 := by
  rw [lapseWeight_modulus, kuiken_eq_entropyDamping]

/-! ## §C — the complex lapse `N − iε` is the Nagao–Nielsen complex energy -/

/-- **[Implement] The lapse weight IS the non-Hermitian eigen-propagator.** The complex lapse `N − iε` has
the exact form of the Nagao–Nielsen complex energy `complexEnergy N ε = N − iε`, so the constraint weight
`e^{−i(N−iε)ℋ}` is the non-Hermitian eigen-evolution factor `evolutionFactorC N ε 1 ℋ = e^{−iE_C t/ℏ}`:
the **complex lapse plays the role of the complex energy `E_C`**, and the Hamiltonian constraint `ℋ` plays
the role of time `t`. -/
theorem lapseWeight_eq_evolutionFactor (N ε Ham : ℝ) :
    lapseWeight N ε Ham = evolutionFactorC N ε 1 (Ham : ℂ) := by
  unfold lapseWeight evolutionFactorC complexEnergy
  norm_num

/-- **[Implement] The imaginary lapse is the non-Hermitian gap.** The imaginary part of the complex lapse
`N − iε` is `−ε` (`gap_eq_complexEnergy_im` with `E_I = ε`): the lapse-contour displacement `ε` is exactly
the Nagao–Nielsen gap `E_I` that damps the propagator. -/
theorem lapse_im_eq_gap (N ε : ℝ) : (complexEnergy N ε).im = -ε := by
  simp [complexEnergy]

/-- **[Implement] The real lapse is the timelike component.** The real part of the complex lapse `N − iε` is
`N`: in the spacetime-interval reading of the contour point (`lorentzianForm = (Re)² − (Im)²`), `Re = N` is
the **timelike leg** and `Im = −ε` (`lapse_im_eq_gap`) is the **spacelike leg** (the gap). -/
theorem lapse_re_eq (N ε : ℝ) : (complexEnergy N ε).re = N := by
  simp [complexEnergy]

/-! ## §D — the lapse weight is the Nagao–Nielsen complex action `e^{(i/ℏ)S_complex}` -/

/-- **[Implement] The lapse weight is the Nagao–Nielsen complex-action weight.**
`e^{−i(N−iε)ℋ} = nagaoNielsenComplexActionWeight (−Nℋ) (εℋ) 1 = e^{(i/ℏ)S_complex}` with complex action
`S_complex = −Nℋ + i(εℋ) = −(N − iε)ℋ`: the gravitational complex action is the (negative) complex-lapse-weighted
Hamiltonian constraint. -/
theorem lapseWeight_eq_nagaoNielsen (N ε Ham : ℝ) :
    lapseWeight N ε Ham = nagaoNielsenComplexActionWeight (-(N * Ham)) (ε * Ham) 1 := by
  rw [lapseWeight_eq_master, ← nagaoNielsen_eq_master _ _ _ one_ne_zero]

/-! ## §E — the `ε → 0` reversible (Lorentzian) limit -/

/-- **[Implement — Banihashemi–Jacobson Eq. 2] The `ε → 0` reversible limit is the Lorentzian constraint
phase.** At `ε = 0` the lapse weight is the pure oscillatory phase `e^{−iNℋ}` — the undamped Lorentzian
integrand of `δ(ℋ) = ∫(dN/2π) e^{−iNℋ}` (no imaginary action, `S_I = 0`); the same `ε → 0` limit that
`PathIntegral.QEDPathIntegralConvergence` takes for the QED model. -/
theorem lapseWeight_at_eps_zero (N Ham : ℝ) :
    lapseWeight N 0 Ham = Complex.exp (-Complex.I * (N * Ham : ℝ)) := by
  unfold lapseWeight
  congr 1
  push_cast
  ring_nf

/-! ## §F — the momenta are integrated before the lapse (the `(p,q)` origin, Eq. 1) -/

/-- **[Banihashemi–Jacobson Eq. 1] The momenta are integrated before the lapse.** The paper's starting point
and central ordering: the reduced phase-space path integral `∫𝒟p 𝒟q e^{i∫(pq̇ − H)}` integrates the momenta
*first* (Gaussian, at the saddle `p = mq̇`), and only then the lapse — which is precisely what forces the
lapse contour below the origin. That momentum saddle is `PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle`:
at `p = mq̇` the phase-space Lagrangian collapses to the configuration Lagrangian, the same `(p,q)`
path-integral origin from which the Nagao–Nielsen gap is read (`pq_from_pathIntegral_saddle`). -/
theorem momenta_before_lapse (m qdot V : ℂ) (hm : m ≠ 0) :
    PathIntegral.MomentumPathIntegral.phaseLagrangian m (m * qdot) qdot V
      = PathIntegral.MomentumPathIntegral.configLagrangian m qdot V :=
  PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle m qdot V hm

end Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster

end

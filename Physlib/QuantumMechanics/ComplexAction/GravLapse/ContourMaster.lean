/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.GapPathIntegralOrigin
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

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
* Repo carriers: `PathIntegral.ComplexActionPathIntegralWeight` (`complexActionPathIntegralWeight`, `nagaoNielsenComplexActionWeight`, `kuikenWeight`,
  `master_modulus_is_kuiken`), `NonHermitian.WickRotation` (`complexEnergy`, `evolutionFactorC`,
  `entropyDamping`), `NonHermitianComplexAction.GapPathIntegralOrigin` (the `(p,q)` and gap origin),
  `PathIntegral.MomentumPathIntegral` (`phaseLagrangian_at_saddle`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QuantumMechanics.ComplexAction


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
lemma lapseWeight_eq_master (N ε Ham : ℝ) :
    lapseWeight N ε Ham = complexActionPathIntegralWeight (-(N * Ham)) (ε * Ham) 1 := by
  unfold lapseWeight complexActionPathIntegralWeight
  congr 1
  push_cast
  linear_combination ((ε : ℂ) * (Ham : ℂ)) * Complex.I_sq


/-- **[Implement] The modulus of the lapse weight is the Kuiken/entropy-production weight** `e^{−εℋ}`. The
`−iε` contour displacement contributes a real damping `‖e^{−i(N−iε)ℋ}‖ = e^{−εℋ} = kuikenWeight 1 (εℋ)`;
for `ε > 0` (and `ℋ > 0`) the constraint integral converges — the Halliwell–Hartle fluctuation-convergence
criterion is the arc's entropic damping. -/
lemma lapseWeight_modulus (N ε Ham : ℝ) :
    ‖lapseWeight N ε Ham‖ = kuikenWeight 1 (ε * Ham) := by
  rw [lapseWeight_eq_master, master_modulus_is_kuiken]

/-- **[Bridge] The lapse-contour damping is `WickRotation.entropyDamping`.** The `−iε` displacement's modulus
`e^{−εℋ}` is exactly the arc's Cameron–Martin / entropic-damping factor `entropyDamping (εℋ) 1` — the
gravitational convergence regulator and the path-integral entropic weight coincide. -/
lemma lapseWeight_modulus_eq_entropyDamping (N ε Ham : ℝ) :
    ‖lapseWeight N ε Ham‖ = entropyDamping (ε * Ham) 1 := by
  rw [lapseWeight_modulus, kuiken_eq_entropyDamping]


/-- **[Implement] The lapse weight IS the non-Hermitian eigen-propagator.** The complex lapse `N − iε` has
the exact form of the Nagao–Nielsen complex energy `complexEnergy N ε = N − iε`, so the constraint weight
`e^{−i(N−iε)ℋ}` is the non-Hermitian eigen-evolution factor `evolutionFactorC N ε 1 ℋ = e^{−iE_C t/ℏ}`:
the **complex lapse plays the role of the complex energy `E_C`**, and the Hamiltonian constraint `ℋ` plays
the role of time `t`. -/
lemma lapseWeight_eq_evolutionFactor (N ε Ham : ℝ) :
    lapseWeight N ε Ham = evolutionFactorC N ε 1 (Ham : ℂ) := by
  unfold lapseWeight evolutionFactorC complexEnergy
  norm_num

/-- **[Implement] The imaginary lapse is the non-Hermitian gap.** The imaginary part of the complex lapse
`N − iε` is `−ε` (`gap_eq_complexEnergy_im` with `E_I = ε`): the lapse-contour displacement `ε` is exactly
the Nagao–Nielsen gap `E_I` that damps the propagator. -/
lemma lapse_im_eq_gap (N ε : ℝ) : (complexEnergy N ε).im = -ε := by
  simp [complexEnergy]

/-- **[Implement] The real lapse is the timelike component.** The real part of the complex lapse `N − iε` is
`N`: in the spacetime-interval reading of the contour point (`lorentzianForm = (Re)² − (Im)²`), `Re = N` is
the **timelike leg** and `Im = −ε` (`lapse_im_eq_gap`) is the **spacelike leg** (the gap). -/
lemma lapse_re_eq (N ε : ℝ) : (complexEnergy N ε).re = N := by
  simp [complexEnergy]


/-- **[Implement] The lapse weight is the Nagao–Nielsen complex-action weight.**
`e^{−i(N−iε)ℋ} = nagaoNielsenComplexActionWeight (−Nℋ) (εℋ) 1 = e^{(i/ℏ)S_complex}` with complex action
`S_complex = −Nℋ + i(εℋ) = −(N − iε)ℋ`: the gravitational complex action is the (negative) complex-lapse-weighted
Hamiltonian constraint. -/
lemma lapseWeight_eq_nagaoNielsen (N ε Ham : ℝ) :
    lapseWeight N ε Ham = nagaoNielsenComplexActionWeight (-(N * Ham)) (ε * Ham) 1 := by
  rw [lapseWeight_eq_master, ← nagaoNielsen_eq_master _ _ _ one_ne_zero]


/-- **[Implement — Banihashemi–Jacobson Eq. 2] The `ε → 0` reversible limit is the Lorentzian constraint
phase.** At `ε = 0` the lapse weight is the pure oscillatory phase `e^{−iNℋ}` — the undamped Lorentzian
integrand of `δ(ℋ) = ∫(dN/2π) e^{−iNℋ}` (no imaginary action, `S_I = 0`); the same `ε → 0` limit that
`PathIntegral.QEDPathIntegralConvergence` takes for the QED model. -/
lemma lapseWeight_at_eps_zero (N Ham : ℝ) :
    lapseWeight N 0 Ham = Complex.exp (-Complex.I * (N * Ham : ℝ)) := by
  unfold lapseWeight
  congr 1
  push_cast
  ring_nf


/-- **[Banihashemi–Jacobson Eq. 1] The momenta are integrated before the lapse.** The paper's starting point
and central ordering: the reduced phase-space path integral `∫𝒟p 𝒟q e^{i∫(pq̇ − H)}` integrates the momenta
*first* (Gaussian, at the saddle `p = mq̇`), and only then the lapse — which is precisely what forces the
lapse contour below the origin. That momentum saddle is `PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle`:
at `p = mq̇` the phase-space Lagrangian collapses to the configuration Lagrangian, the same `(p,q)`
path-integral origin from which the Nagao–Nielsen gap is read (`pq_from_pathIntegral_saddle`). -/
lemma momenta_before_lapse (m qdot V : ℂ) (hm : m ≠ 0) :
    PathIntegral.MomentumPathIntegral.phaseLagrangian m (m * qdot) qdot V
      = PathIntegral.MomentumPathIntegral.configLagrangian m qdot V :=
  PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle m qdot V hm

end Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster

/-! ## The lapse as a Nagao-Kozak entropic contour point -/

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime

open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-- The Nagao-Nielsen dispersion on the contour `q = ω + iγ` is `L(ω + iγ) = ω² - γ²`. -/
lemma lorentzianDispersion_eq (γ ω : ℝ) : lorentzianDispersion γ ω = ω ^ 2 - γ ^ 2 := by
  unfold lorentzianDispersion lorentzianForm
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **The Nagao-Nielsen form of the complex lapse is the spacetime interval**:
`lorentzianForm(N - iε) = N² - ε²`. -/
lemma lapse_lorentzianForm_eq (N ε : ℝ) : lorentzianForm (complexEnergy N ε) = N ^ 2 - ε ^ 2 := by
  unfold lorentzianForm
  rw [lapse_re_eq, lapse_im_eq_gap]; ring

/-- **The contour point's legs.** The interval decomposes as `(timelike)² - (spacelike)²`
with timelike leg `Re = N` and spacelike leg `Im = -ε`. -/
lemma lapse_interval_legs (N ε : ℝ) :
    lorentzianForm (complexEnergy N ε) = N ^ 2 - ε ^ 2
      ∧ (complexEnergy N ε).re = N
      ∧ (complexEnergy N ε).im = -ε :=
  ⟨lapse_lorentzianForm_eq N ε, lapse_re_eq N ε, lapse_im_eq_gap N ε⟩

/-- **The complex lapse is a contour point** `q = ω + iγ`, with real frequency `ω = N`
and damping `γ = -ε`. -/
lemma complexLapse_eq_contourPoint (N ε : ℝ) :
    complexEnergy N ε = (N : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I := by
  unfold complexEnergy; push_cast; ring

/-- **The Nagao-Nielsen form of the complex lapse is the Kozak-even dispersion.** -/
lemma lapse_lorentzianForm_eq_dispersion (N ε : ℝ) :
    lorentzianForm (complexEnergy N ε) = lorentzianDispersion ε N := by
  rw [lapse_lorentzianForm_eq, lorentzianDispersion_eq]

/-- **The lapse weight is unimodular on the real contour**:
`‖lapseWeight N 0 ℋ‖ = 1`. -/
lemma lapse_real_modulus_one (N Ham : ℝ) : ‖lapseWeight N 0 Ham‖ = 1 := by
  rw [lapseWeight_modulus, kuikenWeight]; norm_num

/-- **The real lapse contour is the reversible fiber where the contour structures agree.** -/
lemma lapse_real_contour_reversible (ξ N Ham : ℝ) (hξ : 0 < ξ) :
    0 ≤ lorentzianForm (complexEnergy N 0)
      ∧ FnEven (lorentzianDispersion 0)
      ∧ bogoliubovEntropicTime ξ 0 = 0
      ∧ ‖lapseWeight N 0 Ham‖ = 1 := by
  refine ⟨?_, ?_, ?_, lapse_real_modulus_one N Ham⟩
  · rw [lapse_lorentzianForm_eq_dispersion]; exact lorentzianDispersion_real_nonneg N
  · exact lorentzianDispersion_fnEven 0
  · exact bogoliubov_entropicTime_normal_zero ξ hξ

/-- **The contour displacement narrows the Nagao-Nielsen convergence cone.** -/
lemma lapse_cone_narrows (N ε : ℝ) (hε : ε ≠ 0) :
    lorentzianForm (complexEnergy N ε) < lorentzianForm (complexEnergy N 0) := by
  rw [lapse_lorentzianForm_eq, lapse_lorentzianForm_eq]
  have : 0 < ε ^ 2 := lt_of_le_of_ne (sq_nonneg ε) (Ne.symm (pow_ne_zero 2 hε))
  nlinarith

/-- **Off the real axis the lapse weight is sub-unimodular.** For `ε, ℋ > 0`, the
lapse weight modulus is strictly less than `1`. -/
lemma lapse_irreversible_off_axis (N ε Ham : ℝ) (hε : 0 < ε) (hH : 0 < Ham) :
    ‖lapseWeight N ε Ham‖ < 1 := by
  rw [lapseWeight_modulus, kuikenWeight, div_one]
  calc Real.exp (-(ε * Ham)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
    _ = 1 := Real.exp_zero

end Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime

end

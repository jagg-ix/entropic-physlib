/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Basic
public import Physlib.QuantumMechanics.NonHermitian.WickRotation
/-!

# Exact solutions of the Friedmann equations

Closed-form solutions of the Friedmann equations.  Formalized here: the
exponential-expansion (`a = e^{t/τ}`) scalar-field exact solution of Gumjudpai,
Gen. Relativ. Gravit. 41 (2009) 249 — the phantom field Eq. (21) verified
against its kinetic equation Eq. (20) (`exponential_scalar_field_solves`), the
de Sitter-era potential collapsing to a pure quadratic in the field, Eq. (36)
(`exponential_potential_quadratic`), the effective equation of state Eq. (43)
(`exponential_weff`) and the finite-time blowup of its coefficient Eq. (44)
(`weff_singularity` — an equation-of-state-coefficient singularity, `ρ_tot`
crossing zero, not a curvature singularity).  The standard textbook solutions
(de Sitter, radiation, Einstein-de Sitter, Milne, Einstein static) stay as
TODOs.  §B connects the cosmological NLS to the **Nagao–Nielsen non-Hermitian /
complex-action theory**: the Schrödinger energy `E = −κ²n²D/12` and potential
`P = (κ²n/4)aⁿεφ̇²`, the de Sitter identity `P = E` (the free/curvature-only
contour), the `complexEnergy` embedding on the reversible axis, and the
exponential mode `u = e^{−nt/2τ}` as the **Wick rotation** (`t ↦ −iτ`) of the
Nagao–Nielsen reversible phase / a pure-imaginary-energy evolution factor — de
Sitter expansion as Euclidean, non-normalizable non-Hermitian evolution.

-/

@[expose] public section

TODO "Prove that the de Sitter solution `a(t) = a₀ exp(±√(Λ/3) c t)` (with `ρ = 0`,
  `K = 0`, `Λ > 0`) solves the Friedmann equations, and that its deceleration
  parameter is `q = −1`."

TODO "Prove that the spatially flat radiation-dominated solution `a = (t/t₀)^(1/2)`
  solves the Friedmann equations, with `q₀ = 1` and `t₀ = 1 / (2 H₀)`."

TODO "Prove that the Einstein-de Sitter (spatially flat, dust) solution
  `a = (t/t₀)^(2/3)` solves the Friedmann equations, with `q₀ = 1/2` and
  `t₀ = 2 / (3 H₀)`."

TODO "Prove that the Milne solution `a = c t` (empty universe, `K < 0`) has
  vanishing scalar curvature, i.e. it is Minkowski space in expanding coordinates."

TODO "Define the Einstein static universe (`∂ₜ a = ∂ₜ ∂ₜ a = 0`, forcing `K > 0`
  and `ρ_m = 2 ρ_Λ`) and prove that it is an unstable equilibrium."

namespace Cosmology.FLRW.Solutions

/-! ## §A — the exponential-expansion scalar-field solution (Gumjudpai §4–§6) -/

/-- **[The phantom scalar solution verifies its kinetic equation]** (Gumjudpai
Eqs. (20)–(21), flat case): the field `φ(t) = 2τ√(D/3n)·e^{−nt/2τ} + φ₀` has
`φ̇ = −√(Dn/3)·e^{−nt/2τ}`, and `φ̇² = (nD/3)·e^{−nt/τ}` — so with a *phantom*
kinetic term (`ε = −1`), `εφ̇² = −(n/3)·ρ_γ` for the barotropic density
`ρ_γ = D·e^{−nt/τ} = D·a^{−n}`: the scalar field exactly cancels the fluid's
`w_eff` away from `−1`, sustaining exponential expansion.  (A canonical field
`ε = +1` would need `φ̇²  < 0`: the solution is real only when phantom.) -/
theorem exponential_scalar_field_solves (τ D n t φ₀ : ℝ) (hτ : τ ≠ 0)
    (hn : 0 < n) (hD : 0 ≤ D) :
    HasDerivAt
      (fun s => 2 * τ * Real.sqrt (D / (3 * n)) * Real.exp (-n * s / (2 * τ)) + φ₀)
      (-(Real.sqrt (D * n / 3) * Real.exp (-n * t / (2 * τ)))) t
    ∧ (-(Real.sqrt (D * n / 3) * Real.exp (-n * t / (2 * τ)))) ^ 2
        = n * D / 3 * Real.exp (-n * t / τ) := by
  have key : 2 * τ * Real.sqrt (D / (3 * n)) * (-n / (2 * τ))
      = -(Real.sqrt (D * n / 3)) := by
    have hsq : n * Real.sqrt (D / (3 * n)) = Real.sqrt (D * n / 3) := by
      have h1 : (n * Real.sqrt (D / (3 * n))) ^ 2 = D * n / 3 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
      calc n * Real.sqrt (D / (3 * n))
          = Real.sqrt ((n * Real.sqrt (D / (3 * n))) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ = Real.sqrt (D * n / 3) := by rw [h1]
    have h2τ : (2 * τ : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hτ
    calc 2 * τ * Real.sqrt (D / (3 * n)) * (-n / (2 * τ))
        = -(n * Real.sqrt (D / (3 * n))) * (2 * τ / (2 * τ)) := by ring
      _ = -(n * Real.sqrt (D / (3 * n))) := by rw [div_self h2τ, mul_one]
      _ = -(Real.sqrt (D * n / 3)) := by rw [hsq]
  constructor
  · have hlin : HasDerivAt (fun s : ℝ => -n * s / (2 * τ)) (-n / (2 * τ)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-n)).div_const (2 * τ)
    have hexp := hlin.exp
    have h := (hexp.const_mul (2 * τ * Real.sqrt (D / (3 * n)))).add_const φ₀
    have hval : 2 * τ * Real.sqrt (D / (3 * n))
        * (Real.exp (-n * t / (2 * τ)) * (-n / (2 * τ)))
        = -(Real.sqrt (D * n / 3) * Real.exp (-n * t / (2 * τ))) := by
      linear_combination Real.exp (-n * t / (2 * τ)) * key
    exact hval ▸ h
  · have hexp2 : Real.exp (-n * t / (2 * τ)) ^ 2 = Real.exp (-n * t / τ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [neg_sq, mul_pow, Real.sq_sqrt (by positivity), hexp2]
    ring

/-- **[The de Sitter-era potential is a pure quadratic]** (Gumjudpai Eqs.
(34)/(36), flat case): substituting the solution `φ − φ₀ = 2τ√(D/3n)·e^{−nt/2τ}`
into the exponential-era potential `V(t) = 3/(κ²τ²) + ((n−6)/6)·D·e^{−nt/τ}`
turns it into `V(φ) = 3/(κ²τ²) + ((n−6)/6)·(3n/4τ²)·(φ−φ₀)²` — an oscillator-type
quadratic whose sign flips at `n = 6` (the stiff-fluid boundary). -/
theorem exponential_potential_quadratic (κ τ D n t : ℝ) (hτ : τ ≠ 0)
    (hn : 0 < n) (hD : 0 ≤ D) :
    3 / (κ ^ 2 * τ ^ 2)
        + (n - 6) / 6 * (3 * n / (4 * τ ^ 2))
          * (2 * τ * Real.sqrt (D / (3 * n)) * Real.exp (-n * t / (2 * τ))) ^ 2
      = 3 / (κ ^ 2 * τ ^ 2) + (n - 6) / 6 * D * Real.exp (-n * t / τ) := by
  congr 1
  have hexp2 : Real.exp (-n * t / (2 * τ)) ^ 2 = Real.exp (-n * t / τ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hexp2]
  field_simp
  ring

/-- **[The effective equation of state of exponential expansion]** (Gumjudpai
Eq. (43)): for `a = e^{t/τ}` the total density is `ρ_tot = (3/κ²)(1/τ² + k·e^{−2t/τ})`
(the first Friedmann equation) and `ρ_tot + p_tot = (2k/κ²)e^{−2t/τ}` (the `Ḣ = 0`
relation), so away from the `ρ_tot = 0` crossing,

  `w_eff = [−1 − (kτ²/3)e^{−2t/τ}] / [1 + kτ²e^{−2t/τ}]` —

exactly `−1` for `k = 0`, but *curvature-shifted* otherwise. -/
theorem exponential_weff (κ τ k t : ℝ) (hκ : κ ≠ 0) (hτ : τ ≠ 0)
    (hden : 1 + k * τ ^ 2 * Real.exp (-2 * t / τ) ≠ 0) :
    (2 * k / κ ^ 2 * Real.exp (-2 * t / τ)
        - 3 / κ ^ 2 * (1 / τ ^ 2 + k * Real.exp (-2 * t / τ)))
      / (3 / κ ^ 2 * (1 / τ ^ 2 + k * Real.exp (-2 * t / τ)))
      = (-1 - k * τ ^ 2 / 3 * Real.exp (-2 * t / τ))
        / (1 + k * τ ^ 2 * Real.exp (-2 * t / τ)) := by
  rw [div_eq_div_iff]
  · field_simp
    ring
  · intro h
    apply hden
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (div_ne_zero (by norm_num) (pow_ne_zero 2 hκ))
    · have hsplit : 1 + k * τ ^ 2 * Real.exp (-2 * t / τ)
          = τ ^ 2 * (1 / τ ^ 2 + k * Real.exp (-2 * t / τ)) := by
        linear_combination (-1 : ℝ) * mul_inv_cancel₀ (pow_ne_zero 2 hτ)
      rw [hsplit, h1, mul_zero]
  · exact hden

/-- **[The `w_eff` blowup time]** (Gumjudpai Eq. (44)): the equation-of-state
coefficient of exponential expansion diverges — `ρ_tot` crosses zero — exactly at
`t = (τ/2)·ln(−kτ²)`, possible only for negative curvature (`kτ² < 0`).  This is
a coefficient singularity, not a curvature singularity. -/
theorem weff_singularity (k τ t : ℝ) (hτ : τ ≠ 0) (hk : k * τ ^ 2 < 0) :
    1 + k * τ ^ 2 * Real.exp (-2 * t / τ) = 0
      ↔ t = τ / 2 * Real.log (-(k * τ ^ 2)) := by
  have hpos : 0 < -(k * τ ^ 2) := by linarith
  constructor
  · intro h
    have hmul : -(k * τ ^ 2) * Real.exp (-2 * t / τ) = 1 := by linarith
    have hexp : Real.exp (-2 * t / τ) = (-(k * τ ^ 2))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by linarith [hmul])
    have hlog := congrArg Real.log hexp
    rw [Real.log_exp, Real.log_inv] at hlog
    rw [div_eq_iff hτ] at hlog
    linarith
  · intro h
    rw [h]
    have harg : -2 * (τ / 2 * Real.log (-(k * τ ^ 2))) / τ
        = -Real.log (-(k * τ ^ 2)) := by
      field_simp
    rw [harg, Real.exp_neg, Real.exp_log hpos, inv_neg, mul_neg,
      mul_inv_cancel₀ hk.ne]
    ring


/-! ## §B — the Nagao–Nielsen non-Hermitian / complex-action link -/

open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-- **The NLS Schrödinger energy** `E = −κ²n²D/12` (Gumjudpai Eq. (12)); with
`κ² = 8πG` this is the `E`-coefficient of `FriedmannEquation.nls_equation_from_friedmann`. -/
noncomputable def nlsEnergy (κ n D : ℝ) : ℝ := -(κ ^ 2 * n ^ 2 * D / 12)

/-- **The NLS Schrödinger potential** `P = (κ²n/4)·aⁿ·(εφ̇²)` (Gumjudpai Eq. (13)),
packaged from `aⁿ` and the signed kinetic term `εφ̇²`. -/
noncomputable def nlsPotential (κ n aPow kinetic : ℝ) : ℝ :=
  κ ^ 2 * n / 4 * aPow * kinetic

/-- **[The NLS energy is the Friedmann coefficient]** with `κ² = 8πG` the named
`nlsEnergy` is exactly the `E`-coefficient inside
`FriedmannEquation.nls_equation_from_friedmann` — no duplication, one energy. -/
theorem nlsEnergy_eq_friedmann_coefficient (n D G : ℝ) (hG : 0 ≤ G) :
    nlsEnergy (Real.sqrt (8 * Real.pi * G)) n D
      = -(8 * Real.pi * G) * n ^ 2 * D / 12 := by
  unfold nlsEnergy
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- **[The NLS energy is negative]** `E = −κ²n²D/12 < 0` for a real barotropic
constant `D > 0` — the cosmological Schrödinger problem is a *bound-state* energy,
the expansion signature (Gumjudpai's `E ≤ 0`, §3). -/
theorem nlsEnergy_neg (κ n D : ℝ) (hκ : κ ≠ 0) (hn : n ≠ 0) (hD : 0 < D) :
    nlsEnergy κ n D < 0 := by
  unfold nlsEnergy
  have h1 : 0 < κ ^ 2 := by positivity
  have h2 : 0 < n ^ 2 := by positivity
  nlinarith [mul_pos (mul_pos h1 h2) hD]

/-- **[de Sitter: the potential equals the energy] `P = E`.** On the
exponential-expansion phantom solution `εφ̇² = −(n/3)ρ_γ = −(n/3)D·a^{−n}`
(Gumjudpai Eq. (20)), the NLS potential collapses onto the NLS energy: the
Schrödinger operator's `E − P` vanishes, so the de Sitter mode sits on the *free*
(curvature-only) contour `u″ = −(nk/2)u^{(4−n)/n}` of the NLS equation. -/
theorem exponential_potential_eq_energy (κ n D aVal : ℝ) (ha : 0 < aVal) :
    nlsPotential κ n (aVal ^ n) (-(n / 3) * D * aVal ^ (-n)) = nlsEnergy κ n D := by
  unfold nlsPotential nlsEnergy
  have hprod : aVal ^ n * aVal ^ (-n) = 1 := by
    rw [← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero]
  linear_combination (-(κ ^ 2 * n ^ 2 * D / 12)) * hprod

/-- **[de Sitter is the free NLS contour] `E − P = 0`.** Corollary of
`exponential_potential_eq_energy`: on the exponential phantom mode the reversible
potential exactly cancels the energy — the imaginary (irreversible) generator of
the Nagao–Nielsen picture has nothing left to act on. -/
theorem deSitter_nls_free (κ n D aVal : ℝ) (ha : 0 < aVal) :
    nlsEnergy κ n D - nlsPotential κ n (aVal ^ n) (-(n / 3) * D * aVal ^ (-n)) = 0 := by
  rw [exponential_potential_eq_energy κ n D aVal ha]; ring

/-- **[The NLS energy lies on the reversible axis]** the Nagao–Nielsen complex
energy `E_C = E_R − iE_I` at the cosmological Schrödinger energy has *zero
imaginary part*: `complexEnergy (nlsEnergy κ n D) 0 = ↑(nlsEnergy κ n D)`.  The
cosmological `E` is a real (reversible, `H_I = 0`) eigenvalue of the Nagao–Nielsen
Hamiltonian. -/
theorem nlsEnergy_on_reversible_axis (κ n D : ℝ) :
    complexEnergy (nlsEnergy κ n D) 0 = ((nlsEnergy κ n D : ℝ) : ℂ) :=
  complexEnergy_at_E_I_zero _

/-- **[The exponential mode is the Wick rotation of the reversible phase]**
`u = e^{−nt/2τ}` (Gumjudpai Eq. (26)) is exactly the Nagao–Nielsen reversible
phase `exp(−iE_R t/ℏ)` continued to imaginary time `t ↦ −it` with reversible
eigenvalue `E_R = ℏn/2τ`: the de Sitter wave function is Euclidean (imaginary-time)
quantum evolution — the complex-time *contour* of the complex-action theory. -/
theorem exponential_wavefunction_is_wick_rotation
    (n τ hbar t : ℝ) (hτ : τ ≠ 0) (hbarz : hbar ≠ 0) :
    reversiblePhaseC (hbar * n / (2 * τ)) hbar (-Complex.I * (t : ℂ))
      = ((Real.exp (-(n * t / (2 * τ))) : ℝ) : ℂ) := by
  rw [reversiblePhase_wickRotation,
    show hbar * n / (2 * τ) * t / hbar = n * t / (2 * τ) from by field_simp]

/-- **[The exponential mode is a pure-imaginary-energy non-Hermitian evolution]**
`u = e^{−nt/2τ}` is the Nagao–Nielsen evolution factor with reversible part
`E_R = 0` and imaginary eigenvalue `E_I = ℏn/2τ`: a real, monotonically decaying
weight with no unit-modulus phase.  This is *why* the NLS wave function is
non-normalizable (Gumjudpai §3) — a genuine non-Hermitian
(probability-non-conserving) mode. -/
theorem exponential_wavefunction_is_nonHermitian_mode
    (n τ hbar t : ℝ) (hτ : τ ≠ 0) (hbarz : hbar ≠ 0) :
    evolutionFactor 0 (hbar * n / (2 * τ)) hbar t
      = ((Real.exp (-(n * t / (2 * τ))) : ℝ) : ℂ) := by
  rw [evolutionFactor_decomp]
  have hrev : reversiblePhase 0 hbar t = 1 := by
    unfold reversiblePhase; simp
  rw [hrev, one_mul,
    show hbar * n / (2 * τ) * t / hbar = n * t / (2 * τ) from by field_simp]

/-- **[The exponential mode is real: on the physical contour]** the Nagao–Nielsen
evolution factor of the de Sitter mode has *vanishing imaginary part* — the
solution is real, matching Gumjudpai's phantom-reality condition (Eq. (21): the
solution is real only for `ε = −1`; otherwise imaginary): the reality of the
scalar-field solution is the selection of the physical (real-action) contour. -/
theorem exponential_mode_real_on_contour
    (n τ hbar t : ℝ) (hτ : τ ≠ 0) (hbarz : hbar ≠ 0) :
    (evolutionFactor 0 (hbar * n / (2 * τ)) hbar t).im = 0 := by
  rw [exponential_wavefunction_is_nonHermitian_mode n τ hbar t hτ hbarz,
    Complex.ofReal_im]

end Cosmology.FLRW.Solutions

end

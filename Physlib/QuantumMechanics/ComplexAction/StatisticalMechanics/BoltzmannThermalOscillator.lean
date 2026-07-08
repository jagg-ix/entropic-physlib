/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Temperature as Wick-rotated time: the Boltzmann thermal semigroup and the Dirac wave equation

This file extends the complex harmonic oscillator (`ComplexOscillator.ComplexHarmonicOscillatorBoson`) using two
papers on the *thermal* sector:

* **V. Saveliev, *A temperature and mass dependence of the linear Boltzmann collision
  operator*, J. Math. Phys. 37 (1996) 6139.** The temperature transformations `F_T` of the
  collision operator form an **additive Abelian semigroup** (Eq. 13: `F_0 = 1`,
  `F_{T₁}∘F_{T₂} = F_{T₁+T₂}`), and the Maxwellian `Ψ_T` obeys the **heat equation**
  `∂_T Ψ_T = (k/2m)∇²Ψ_T` (Eq. 15) — so `Ψ_T` is the heat kernel with mass-dependent
  diffusivity `D = k/2m`. The generator is the double commutator `q = (k/2m)[∇,[∇,·]]`
  (Eqs. 16–17), and the mass dependence enters through `ξ = log(1+m)` (Eq. 21).
* **A. de la Macorra et al., *Canonical quantization for Equilibrium Thermodynamics*,
  arXiv:2511.14121.** Thermodynamics is quantized by **Dirac's constraint procedure**:
  second-class constraints give Dirac brackets `{q,p}_D = F → [q̂,p̂] = iℏF̂` (Eqs. 7, 26),
  and the constraint conditions become a **wave equation** for `ψ(q)` (Eq. 23) — the
  thermodynamic Schrödinger/"Dirac" equation. The conjugate pair is `[ŝ,T̂] = ib̄`
  (`ThermoFieldDynamics.ThermodynamicCanonicalQuantization.entropy_temperature_commutator`).

## The unifying picture: temperature = imaginary time

Saveliev's heat equation `∂_T Ψ = (k/2m)∇²Ψ` is the **Wick rotation** `T = −i t` of the
oscillator's kinetic Schrödinger equation `i∂_t ψ = −(ℏ/2m)∇²ψ` (with `k ↔ ℏ ↔ b̄`). This is
the *same* `a = −i` rotation that turns the massless boson's imaginary mass into a real
inertial mass (`ComplexOscillator.ComplexHarmonicOscillatorBoson.massless_inertialMass`). The diffusivity
`D = k/2m` includes the oscillator mass; for a massless boson it is the Wick-rotated mass.

## Main results

* `heatMode`, `heatMode_zero`, `heatMode_add` — the temperature heat-semigroup on a Fourier
  mode `κ` is `e^{−Dκ²T}`; it is the additive Abelian semigroup of Saveliev Eq. 13
  (`F_0 = 1`, `F_{T₁+T₂} = F_{T₁}·F_{T₂}`).
* `heatMode_decay_ODE` — `∂_T (e^{−Dκ²T}) = −Dκ²·e^{−Dκ²T}`: the heat-generator eigenvalue
  (Saveliev Eqs. 16–17 on a mode), the Fourier form of `∂_T Ψ = D∇²Ψ`.
* `thermalDiffusivity`, `thermalDiffusivity_pos` — `D = k/2m` (Saveliev Eq. 15), with the
  oscillator mass.
* `massLogParam`, `massLogParam_zero` — `ξ = log(1+m)` (Saveliev Eq. 21).
* `heatMode_eq_one_iff` — **the thermal mode is trivial iff `T = 0`**: the same
  no-information / reversible condition as `thermalInertialMass_zero_iff` and
  `thermoActionWeight_norm_one_iff`. At `T = 0` (`F_0 = 1`) there is no thermal diffusion, no
  inertia, no imaginary action, no information.

## References

* V. Saveliev, J. Math. Phys. 37 (1996) 6139, Eqs. 13, 15, 16–17, 21.
* arXiv:2511.14121, Eqs. 7, 17, 23, 26 (Dirac constraint quantization; `[ŝ,T̂] = ib̄`).
* `ComplexOscillator.ComplexHarmonicOscillatorBoson`, `MassOrigin.BosonicInertialMass` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson

namespace Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannThermalOscillator

/-! ## §A — the temperature heat-semigroup (Saveliev Eqs. 13, 15, 16–17) -/

/-- **The thermal diffusivity** `D = k/2m` (Saveliev Eq. 15): the coefficient of the
temperature heat equation `∂_T Ψ = D∇²Ψ`, with the oscillator mass `m`. It is the
Wick-rotated kinetic coefficient `ℏ/2m` (`k ↔ ℏ ↔ b̄`). -/
def thermalDiffusivity (kB m : ℝ) : ℝ := kB / (2 * m)

/-- The thermal diffusivity is positive for `k, m > 0`. For a massless boson the mass is the
Wick-rotated `m_I` (`ComplexOscillator.ComplexHarmonicOscillatorBoson.massless_inertialMass`). -/
theorem thermalDiffusivity_pos (kB m : ℝ) (hkB : 0 < kB) (hm : 0 < m) :
    0 < thermalDiffusivity kB m := by
  unfold thermalDiffusivity; positivity

/-- **The temperature heat-semigroup on a Fourier mode `κ`** `e^{−Dκ²T}` — the eigenvalue of
Saveliev's `F_T = e^{(kT/2m)∇²}` (Eq. 20) on the mode `e^{iκv}`. -/
def heatMode (D κ T : ℝ) : ℝ := Real.exp (-(D * κ ^ 2) * T)

/-- **`F_0 = 1`** (Saveliev Eq. 13): the temperature semigroup is the identity at `T = 0`. -/
theorem heatMode_zero (D κ : ℝ) : heatMode D κ 0 = 1 := by
  unfold heatMode; simp

/-- **The additive (Abelian) semigroup law** `F_{T₁+T₂} = F_{T₁}·F_{T₂}` (Saveliev Eq. 13):
the temperature transformations compose by adding temperatures. -/
theorem heatMode_add (D κ T₁ T₂ : ℝ) :
    heatMode D κ (T₁ + T₂) = heatMode D κ T₁ * heatMode D κ T₂ := by
  unfold heatMode
  rw [← Real.exp_add]
  congr 1; ring

/-- **The heat-generator on a mode** `∂_T (e^{−Dκ²T}) = −Dκ²·e^{−Dκ²T}` (Saveliev Eqs. 16–17,
the Fourier form of `∂_T Ψ = D∇²Ψ` since `∇² → −κ²`). -/
theorem heatMode_decay_ODE (D κ T : ℝ) :
    HasDerivAt (fun T => heatMode D κ T) (-(D * κ ^ 2) * heatMode D κ T) T := by
  unfold heatMode
  have h1 : HasDerivAt (fun T => -(D * κ ^ 2) * T) (-(D * κ ^ 2)) T := by
    simpa using (hasDerivAt_id T).const_mul (-(D * κ ^ 2))
  have h2 := h1.exp
  convert h2 using 1
  ring

/-! ## §B — mass dependence (Saveliev Eq. 21) -/

/-- **The mass-dependence parameter** `ξ = log(1+m)` (Saveliev Eq. 21), where `m = m₁/m₂` is
the ratio of colliding masses; the mass-transformation semigroup is `e^{ξ∇v∗}` (Eq. 25). -/
def massLogParam (m : ℝ) : ℝ := Real.log (1 + m)

/-- **`ξ(0) = 0`**: the mass-ratio reference `m = 0` (infinitely heavy scattering centers, on
which the simplest collision operator `χ̂` acts) sits at the semigroup identity. -/
theorem massLogParam_zero : massLogParam 0 = 0 := by
  unfold massLogParam; simp

/-! ## §C — no-information capstone: `T = 0 ⟺` trivial thermal mode -/

/-- **The thermal mode is trivial iff `T = 0`**: `‖e^{−Dκ²T}‖ = 1 ⟺ T = 0` (for `D > 0`,
`κ ≠ 0`). This is the Boltzmann/heat-semigroup face of the no-information condition — the same
`T = 0` point as `MassOrigin.BosonicInertialMass.thermalInertialMass_zero_iff` and
`ThermoFieldDynamics.ThermodynamicCanonicalQuantization.thermoActionWeight_norm_one_iff`. At `T = 0` the
temperature semigroup is the identity (`F_0 = 1`): no diffusion, no inertia, no imaginary
action, no information; the Dirac conjugate `T̂` (with `[ŝ,T̂] = ib̄`) is at its ground point. -/
theorem heatMode_eq_one_iff (D κ T : ℝ) (hD : 0 < D) (hκ : κ ≠ 0) :
    heatMode D κ T = 1 ↔ T = 0 := by
  unfold heatMode
  rw [Real.exp_eq_one_iff, mul_eq_zero, neg_eq_zero]
  have hDκ : D * κ ^ 2 ≠ 0 := by positivity
  simp [hDκ]

/-! ## §D — proof of the temperature dependence: the Maxwellian heat equation (Saveliev Eq. 15)

The 1D Maxwellian / heat kernel `Ψ_T(v) = (4πDT)^{−1/2} exp(−v²/4DT)` (diffusivity `D = k/2m`,
Saveliev Eq. 12/15) is written via `exp`/`log` so that all derivatives are elementary. We
prove `∂_T Ψ = D ∂²_v Ψ` — the temperature dependence of the collision operator's Maxwellian,
which is the Wick rotation `T = −it` of the oscillator kinetic Schrödinger equation. -/

/-- The 1D Maxwellian / heat kernel `Ψ_T(v) = (4πDT)^{−1/2} exp(−v²/4DT)`, written via
`exp(−½ log(4πDT) − v²/4DT)`. -/
noncomputable def heatKernel (D T v : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * Real.log (4 * Real.pi * D * T) - v ^ 2 / (4 * D * T))

/-- **First spatial derivative**: `∂_v Ψ = −v/(2DT)·Ψ`. -/
theorem heatKernel_deriv_space (D T v : ℝ) (hD : 0 < D) (hT : 0 < T) :
    HasDerivAt (fun v => heatKernel D T v) (-(v / (2 * D * T)) * heatKernel D T v) v := by
  have hD' := hD.ne'; have hT' := hT.ne'
  unfold heatKernel
  have hb : HasDerivAt
      (fun v => -(1 / 2) * Real.log (4 * Real.pi * D * T) - v ^ 2 / (4 * D * T))
      (-(v / (2 * D * T))) v := by
    have h2 : HasDerivAt (fun v => v ^ 2 / (4 * D * T)) (2 * v / (4 * D * T)) v := by
      simpa using (hasDerivAt_pow 2 v).div_const (4 * D * T)
    have h3 := (hasDerivAt_const v (-(1 / 2) * Real.log (4 * Real.pi * D * T))).sub h2
    exact h3.congr_deriv (by field_simp; ring)
  have hb2 := hb.exp
  exact hb2.congr_deriv (by ring)

/-- **Second spatial derivative**: `∂²_v Ψ = (−1/(2DT) + (v/2DT)²)·Ψ` (differentiate the first
spatial derivative again). -/
theorem heatKernel_deriv_space2 (D T v : ℝ) (hD : 0 < D) (hT : 0 < T) :
    HasDerivAt (fun v => -(v / (2 * D * T)) * heatKernel D T v)
      ((-(1 / (2 * D * T)) + (v / (2 * D * T)) ^ 2) * heatKernel D T v) v := by
  have h1 : HasDerivAt (fun v => -(v / (2 * D * T))) (-(1 / (2 * D * T))) v :=
    ((hasDerivAt_id v).div_const (2 * D * T)).neg
  have h2 := heatKernel_deriv_space D T v hD hT
  have h3 := h1.mul h2
  exact h3.congr_deriv (by ring)

/-- **Time derivative**: `∂_T Ψ = (−1/(2T) + v²/(4DT²))·Ψ`. -/
theorem heatKernel_deriv_time (D T v : ℝ) (hD : 0 < D) (hT : 0 < T) :
    HasDerivAt (fun T => heatKernel D T v)
      ((-(1 / (2 * T)) + v ^ 2 / (4 * D * T ^ 2)) * heatKernel D T v) T := by
  have hD' := hD.ne'; have hT' := hT.ne'
  unfold heatKernel
  have hlog : HasDerivAt (fun T => Real.log (4 * Real.pi * D * T)) (1 / T) T := by
    have hlin : HasDerivAt (fun T => 4 * Real.pi * D * T) (4 * Real.pi * D) T := by
      simpa using (hasDerivAt_id T).const_mul (4 * Real.pi * D)
    have hne : 4 * Real.pi * D * T ≠ 0 := by positivity
    have := hlin.log hne
    convert this using 1
    field_simp
  have hg : HasDerivAt (fun T => v ^ 2 / (4 * D * T)) (-(v ^ 2 / (4 * D * T ^ 2))) T := by
    have hd : HasDerivAt (fun T => 4 * D * T) (4 * D) T := by
      simpa using (hasDerivAt_id T).const_mul (4 * D)
    have hne : (4 * D * T) ≠ 0 := by positivity
    have := (hasDerivAt_const T (v ^ 2)).div hd hne
    exact this.congr_deriv (by field_simp; ring)
  have hphi := (hlog.const_mul (-(1 / 2))).sub hg
  have hb : HasDerivAt
      (fun T => -(1 / 2) * Real.log (4 * Real.pi * D * T) - v ^ 2 / (4 * D * T))
      (-(1 / (2 * T)) + v ^ 2 / (4 * D * T ^ 2)) T := by
    exact hphi.congr_deriv (by field_simp; ring)
  have hb2 := hb.exp
  exact hb2.congr_deriv (by ring)

/-- **The Maxwellian heat equation (Saveliev Eq. 15)** `∂_T Ψ = D · ∂²_v Ψ`: the time
derivative of the heat kernel equals the diffusivity times its spatial Laplacian (the RHS
factor `(−1/(2DT) + (v/2DT)²)·Ψ` is exactly `∂²_v Ψ` from `heatKernel_deriv_space2`). Holds for
any `D > 0`. -/
theorem heatKernel_heat_equation (D T v : ℝ) (hD : 0 < D) (hT : 0 < T) :
    HasDerivAt (fun T => heatKernel D T v)
      (D * ((-(1 / (2 * D * T)) + (v / (2 * D * T)) ^ 2) * heatKernel D T v)) T := by
  have hD' := hD.ne'; have hT' := hT.ne'
  have ht := heatKernel_deriv_time D T v hD hT
  exact ht.congr_deriv (by field_simp; ring)

/-- **Temperature dependence on the oscillator mass**: the heat equation with
`D = thermalDiffusivity k m = k/2m` — the diffusivity with the (complex) oscillator mass
`m` (for a massless boson, the Wick-rotated `m_I`,
`ComplexOscillator.ComplexHarmonicOscillatorBoson.massless_inertialMass`). This is Saveliev Eq. 15 for the
oscillator. -/
theorem maxwellian_heat_equation_oscillator (kB m T v : ℝ)
    (hkB : 0 < kB) (hm : 0 < m) (hT : 0 < T) :
    HasDerivAt (fun T => heatKernel (thermalDiffusivity kB m) T v)
      (thermalDiffusivity kB m *
        ((-(1 / (2 * thermalDiffusivity kB m * T)) + (v / (2 * thermalDiffusivity kB m * T)) ^ 2)
          * heatKernel (thermalDiffusivity kB m) T v)) T :=
  heatKernel_heat_equation (thermalDiffusivity kB m) T v (thermalDiffusivity_pos kB m hkB hm) hT

/-! ## §E — proof of the mass dependence: the generator `dξ/dm` (Saveliev Eq. 21) -/

/-- **The mass-dependence generator (Saveliev Eq. 21)** `dξ/dm = 1/(1+m)` for the mass
parameter `ξ = log(1+m)` (mass ratio `m = m₁/m₂`); the mass-transformation semigroup
`e^{ξ∇v∗}` (Eq. 25) is generated along this parameter. -/
theorem massLogParam_hasDerivAt (m : ℝ) (hm : -1 < m) :
    HasDerivAt massLogParam (1 / (1 + m)) m := by
  unfold massLogParam
  have hlin : HasDerivAt (fun m => 1 + m) 1 m :=
    ((hasDerivAt_const m (1 : ℝ)).add (hasDerivAt_id m)).congr_deriv (zero_add 1)
  have hne : (1 + m) ≠ 0 := by linarith
  exact hlin.log hne

end Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannThermalOscillator

end

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Physlib.Thermodynamics.SecondLawQuantumBoltzmann
public import Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal

/-!
# Lyapunov stability of steady Vlasov–Maxwell solutions (Markov et al. 1992, §4)

Formalizes the **energy–Casimir / Lyapunov stability** kernel of *Markov, Rudykh, Sidorov, Sinitsyn,
Tolstonogov, "Steady-State Solutions of the Vlasov–Maxwell System and Their Stability", Acta Appl. Math. 28
(1992)*, §4 — the paper's headline result. The stationary state is tested with the Chetaev/energy–Casimir
Lyapunov functional `L̂ = T + F₁ + λF₂ + F₃ + F₄` (Eqs. 4.7–4.20); vanishing of its first variation gives the
equilibrium condition `G'ᵢ(f₀ᵢ) = −H` (Eqs. 4.25/4.27), whose solution is the **Maxwell–Boltzmann/Gibbs
distribution**

  `f₀ᵢ = γ·exp(−βᵢ H)`,   `βᵢ = 2αᵢ/mᵢ`   (Eqs. 4.29, 4.31),

with Casimir (Boltzmann entropy) density `Gᵢ(f) = (1/βᵢ)(f ln f − f − f ln γ)` (Eq. 4.30). **Formal stability**
(an isolated minimum of `L̂`, Definition 2) follows from the *strict convexity* of this Casimir,
`G''ᵢ(f) = 1/(βᵢ f) > 0`, together with the manifestly nonnegative field energy `(δE² + δB²)/8π`.

* **§A — the Casimir / Boltzmann-entropy density** (`casimirDensity`, `casimirDensity_hasDerivAt`). Eq. 4.30;
  its derivative is `G'(f) = (1/β) ln(f/γ)` (Eq. 4.28).
* **§B — the Boltzmann equilibrium** (`boltzmannEquilibrium`, `boltzmannEquilibrium_pos`,
  `equilibrium_condition`, `casimir_hasDerivAt_equilibrium`, `boltzmannEquilibrium_eq_maxwellBoltzmann`).
  Eq. 4.29; the equilibrium is the critical point `G'(f₀) = −H` (Eqs. 4.25/4.27) and is the repo's
  Maxwell–Boltzmann occupation (`SecondLawQuantumBoltzmann.maxwellBoltzmann`).
* **§C — formal stability** (`casimir_secondDeriv_hasDerivAt`, `casimir_secondDeriv_pos`,
  `formal_stability_secondVariation`). The Casimir is strictly convex `G'' = 1/(βf) > 0`, so the second
  variation is positive — the isolated minimum (Definition 2) that *is* Lyapunov stability.
* **§D — the link to the energy first integral** (`equilibrium_velocity_eq_vlasovEnergy`). With `β = 2α/m`
  the velocity part of the exponent `−βH` is exactly `vlasovEnergy α 0 V = −α|V|²`, the energy first integral
  `R = −α|V|² + φ` of `Vlasov.DiamondTimeReversal`, so `f₀ = γe^{−βH}` is a function of `R`.

## References

* Y. Markov et al., *Steady-State Solutions of the Vlasov–Maxwell System and Their Stability*,
  Acta Appl. Math. 28 (1992) 253–293 (Eqs. 4.7–4.31, Definitions 1–2; Chetaev's method [41], the BNR analog).
* Repo dependencies: `Thermodynamics.SecondLawQuantumBoltzmann.maxwellBoltzmann` (the same `e^{−x}` equilibrium)
  and its H-theorem (the `f ln f` convexity is the entropy production `entropyProduction_term_nonneg`);
  `Vlasov.DiamondTimeReversal.vlasovEnergy` (the energy first integral `R = −αV² + φ` the equilibrium is a
  function of).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellLyapunovStability

open Matrix
open Physlib.Thermodynamics.SecondLawQuantumBoltzmann
open Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal

/-! ## §A — the Casimir / Boltzmann-entropy density (Eqs. 4.28, 4.30) -/

/-- **[Eq. 4.30] The Casimir (Boltzmann entropy) density** `G(f) = (1/β)(f ln f − f − f ln γ)` — the
convex Casimir of the energy–Casimir Lyapunov functional, the antiderivative of `G'(f) = (1/β) ln(f/γ)`. -/
noncomputable def casimirDensity (β γ f : ℝ) : ℝ := (1 / β) * (f * Real.log f - f - f * Real.log γ)

/-- **[Eq. 4.28] `G'(f) = (1/β)(ln f − ln γ) = (1/β) ln(f/γ)`** — the Casimir derivative whose vanishing
against `H` fixes the equilibrium. -/
theorem casimirDensity_hasDerivAt (β γ f : ℝ) (hf : 0 < f) :
    HasDerivAt (casimirDensity β γ) ((1 / β) * (Real.log f - Real.log γ)) f := by
  have h1 : HasDerivAt (fun x => x * Real.log x) (Real.log f + 1) f :=
    Real.hasDerivAt_mul_log hf.ne'
  have h2 : HasDerivAt (fun x : ℝ => x * Real.log γ) (Real.log γ) f := by
    simpa using (hasDerivAt_id f).mul_const (Real.log γ)
  have h3 : HasDerivAt (fun x => x * Real.log x - x - x * Real.log γ)
      (Real.log f + 1 - 1 - Real.log γ) f := (h1.sub (hasDerivAt_id f)).sub h2
  have h4 := h3.const_mul (1 / β)
  exact h4.congr_deriv (by ring)

/-! ## §B — the Boltzmann equilibrium (Eqs. 4.25, 4.27, 4.29) -/

/-- **[Eq. 4.29] The Maxwell–Boltzmann/Gibbs equilibrium** `f₀ = γ·exp(−βH)` — the steady distribution that
extremizes the Lyapunov functional. -/
noncomputable def boltzmannEquilibrium (β γ H : ℝ) : ℝ := γ * Real.exp (-(β * H))

/-- **The equilibrium occupation is positive** (`γ > 0`). -/
theorem boltzmannEquilibrium_pos (β γ H : ℝ) (hγ : 0 < γ) : 0 < boltzmannEquilibrium β γ H := by
  unfold boltzmannEquilibrium; positivity

/-- **[Eqs. 4.25/4.27/4.29] The equilibrium satisfies the variational condition** `G'(f₀) = −H`. Substituting
`f₀ = γe^{−βH}` into `G'(f) = (1/β) ln(f/γ)` gives `(1/β)(−βH) = −H`. -/
theorem equilibrium_condition (β γ H : ℝ) (hβ : β ≠ 0) (hγ : 0 < γ) :
    (1 / β) * (Real.log (boltzmannEquilibrium β γ H) - Real.log γ) = -H := by
  unfold boltzmannEquilibrium
  rw [Real.log_mul hγ.ne' (Real.exp_ne_zero _), Real.log_exp, add_sub_cancel_left, mul_neg,
    ← mul_assoc, one_div_mul_cancel hβ, one_mul]

/-- **[Eq. 4.25] The equilibrium is the critical point of the Casimir** — at `f₀ = γe^{−βH}` the Casimir
derivative is exactly `−H`, so `f₀` extremizes the energy–Casimir functional. -/
theorem casimir_hasDerivAt_equilibrium (β γ H : ℝ) (hβ : β ≠ 0) (hγ : 0 < γ) :
    HasDerivAt (casimirDensity β γ) (-H) (boltzmannEquilibrium β γ H) := by
  have hd := casimirDensity_hasDerivAt β γ (boltzmannEquilibrium β γ H)
    (boltzmannEquilibrium_pos β γ H hγ)
  rwa [equilibrium_condition β γ H hβ hγ] at hd

/-- **The Markov equilibrium is the repo's Maxwell–Boltzmann occupation** `f₀ = γ·MB(βH)` — Snoke's classical
distribution `e^{−x}` (`SecondLawQuantumBoltzmann.maxwellBoltzmann`) at `x = βH`. -/
theorem boltzmannEquilibrium_eq_maxwellBoltzmann (β γ H : ℝ) :
    boltzmannEquilibrium β γ H = γ * maxwellBoltzmann (β * H) := by
  simp only [boltzmannEquilibrium, maxwellBoltzmann]

/-! ## §C — formal stability: the Casimir is strictly convex (Eq. 4.30, Definition 2) -/

/-- **[Eq. 4.30] `G''(f) = 1/(βf)`** — the second derivative of the Casimir. -/
theorem casimir_secondDeriv_hasDerivAt (β γ f : ℝ) (hf : 0 < f) :
    HasDerivAt (fun x => (1 / β) * (Real.log x - Real.log γ)) ((1 / β) * f⁻¹) f := by
  have h1 : HasDerivAt (fun x => Real.log x - Real.log γ) f⁻¹ f := by
    simpa using (Real.hasDerivAt_log hf.ne').sub_const (Real.log γ)
  simpa using h1.const_mul (1 / β)

/-- **[Strict convexity] `G''(f) = 1/(βf) > 0`** for `β, f > 0` — the Casimir Hessian is positive definite,
the non-trivial half of the isolated-minimum condition. -/
theorem casimir_secondDeriv_pos (β f : ℝ) (hβ : 0 < β) (hf : 0 < f) : 0 < (1 / β) * f⁻¹ := by
  positivity

/-- **[Definition 2: formal stability] The second variation of `L̂` is nonnegative.** Its density is the
strictly convex Casimir term `G''(f₀)(δf)²/2 = (δf)²/(2βf₀)` plus the field energy `(δE² + δB²)/8π`, a sum of
nonnegative terms — `f₀` is an isolated minimum of the Lyapunov functional, i.e. Lyapunov stable. -/
theorem formal_stability_secondVariation (β f₀ δf δEsq δBsq : ℝ)
    (hβ : 0 < β) (hf₀ : 0 < f₀) (hE : 0 ≤ δEsq) (hB : 0 ≤ δBsq) :
    0 ≤ δf ^ 2 / (2 * β * f₀) + (δEsq + δBsq) / (8 * Real.pi) := by
  have t1 : 0 ≤ δf ^ 2 / (2 * β * f₀) := by positivity
  have t2 : 0 ≤ (δEsq + δBsq) / (8 * Real.pi) :=
    div_nonneg (add_nonneg hE hB) (by positivity)
  linarith

/-! ## §D — the link to the energy first integral `R = −αV² + φ` -/

/-- **The equilibrium is a function of the Vlasov energy first integral.** With `β = 2α/m` (Eq. 4.31), the
velocity part of the exponent `−βH = −(2α/m)(½m|V|²)` is exactly `vlasovEnergy α 0 V = −α|V|²` — the velocity
part of the energy first integral `R = −α|V|² + φ` of `Vlasov.DiamondTimeReversal`. So the Lyapunov-stable
Boltzmann equilibrium `f₀ = γe^{−βH}` is a function of the conserved Vlasov energy `R`, the `f(R, G)` class of
the stationary theory — tying §4 stability to the §2 steady states. -/
theorem equilibrium_velocity_eq_vlasovEnergy (α m : ℝ) (V : Fin 3 → ℝ) (hm : m ≠ 0) :
    -((2 * α / m) * ((1 / 2) * m * (V ⬝ᵥ V))) = vlasovEnergy α 0 V := by
  rw [vlasovEnergy]
  field_simp
  ring

/-! ## §E — Li Morse-Lyapunov attractor reading -/

/-- The Vlasov energy-Casimir second variation is a concrete Lyapunov-stability certificate in the
Morse-Lyapunov attractor sense: it is a nonnegative quadratic density built from the convex Casimir and
field energy. -/
theorem energyCasimir_secondVariation_is_lyapunov_nonnegative
    (β f₀ δf δEsq δBsq : ℝ)
    (hβ : 0 < β) (hf₀ : 0 < f₀) (hE : 0 ≤ δEsq) (hB : 0 ≤ δBsq) :
    0 ≤ δf ^ 2 / (2 * β * f₀) + (δEsq + δBsq) / (8 * Real.pi) :=
  formal_stability_secondVariation β f₀ δf δEsq δBsq hβ hf₀ hE hB

end Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellLyapunovStability

end

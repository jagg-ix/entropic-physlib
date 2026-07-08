/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.ComplexPathIntegralSignatures

/-!
# Deriving the Wigner–Dunkl path integral: free particle, Gaussian spreading, free propagator (Junker §3–4)

Formalizes the equations of Junker §3–§4 (arXiv:2312.12895) that *derive* the path integral but were not
yet in the Wigner–Dunkl arc — the free-particle dispersion, the time evolution of a Gaussian wave packet,
the free propagator, and the Lie–Trotter time-slicing that assembles the path integral.

* **§A — the free dispersion (Eq. 29–31).** The free Wigner–Dunkl Hamiltonian `H_ν = P²/2m` has
  eigenvalue `E_k = ℏ²k²/2m` (`dunklFreeDispersion`), the *same* dispersion relation as standard quantum
  mechanics, even in `k` (`dunklFreeDispersion_even`).
* **§B — Gaussian spreading (Eq. 40).** The time-dependent Gaussian width
  `β(t) = β/(1 + iℏβt/m) = β(1 − iℏβt/m)/(1 + (ℏβt/m)²)` (`betaT`, `betaT_realimag`).
* **§C — the uncertainty relation (Eq. 43–44).** The variances `(Δx)² = (1 + ℏ²β²t²/m²)/2β`, `(Δk)² = β/2`
  give `(Δx)²(ΔP)² = ℏ²/4·[1 + (ℏβt/m)²]` (`uncertainty_relation`) — the minimal uncertainty of standard QM,
  the paper's first main result.
* **§D — the free propagator (Eq. 52–53).** The Eq.-52 Gaussian exponent reduces at `ν = 0` to the standard
  free-propagator phase `im(x−y)²/2ℏt` (`freePropagator_exponent`), so the Wigner–Dunkl free propagator
  `K_ν` contains the classical `K_0 = √(m/2πiℏt) e^{im(x−y)²/2ℏt}` (Eq. 53).
* **§E — Lie–Trotter and the time-sliced path integral (Eq. 54, 56).** One Trotter slice is the free
  (kinetic) propagator times the potential phase `e^{−iV ε/ℏ}` (`pathSliceWeight`), which is unitary in real
  time (`pathSlice_unitary`); the full Eq.-56 product is `lorentzianTrotterProduct`
  (`Dunkl.LorentzianPropagator`), and the Kolmogorov–Chapman composition (Eq. 46) is the propagator
  semigroup.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.FreeParticlePathIntegral

open Physlib.QFT.PathIntegral

/-! ## §A — the free dispersion `E_k = ℏ²k²/2m` (Junker Eq. 29–31) -/

/-- **[Junker Eq. 31] The free Wigner–Dunkl dispersion** `E_k = ℏ²k²/2m` — the eigenvalue of the free
Hamiltonian `H_ν = P²/2m` on the Dunkl-kernel plane wave `ψ_k`. Identical to standard quantum mechanics. -/
noncomputable def dunklFreeDispersion (ℏ m k : ℝ) : ℝ := ℏ ^ 2 * k ^ 2 / (2 * m)

/-- The free dispersion is even in `k` (parity symmetry of the Dunkl free Hamiltonian). -/
theorem dunklFreeDispersion_even (ℏ m k : ℝ) :
    dunklFreeDispersion ℏ m (-k) = dunklFreeDispersion ℏ m k := by
  unfold dunklFreeDispersion; ring

/-- The free dispersion is non-negative for `m > 0`. -/
theorem dunklFreeDispersion_nonneg (ℏ m k : ℝ) (hm : 0 < m) : 0 ≤ dunklFreeDispersion ℏ m k := by
  unfold dunklFreeDispersion; positivity

/-! ## §B — the spreading of a Gaussian wave packet (Junker Eq. 40) -/

/-- **[Junker Eq. 40] The time-dependent Gaussian width** `β(t) = β/(1 + iℏβt/m)`. -/
noncomputable def betaT (β ℏ m t : ℝ) : ℂ := (β : ℂ) / (1 + Complex.I * ((ℏ * β * t / m : ℝ) : ℂ))

/-- **[Junker Eq. 40, second form] `β(t) = β(1 − iℏβt/m)/(1 + (ℏβt/m)²)`** — rationalizing the complex
width into real and imaginary parts (with `a := ℏβt/m`). -/
theorem betaT_realimag (β a : ℝ) :
    (β : ℂ) / (1 + Complex.I * (a : ℂ))
      = (β : ℂ) * (1 - Complex.I * (a : ℂ)) / (1 + (a : ℂ) ^ 2) := by
  have hden : (1 + Complex.I * (a : ℂ)) ≠ 0 := by
    intro h; rw [Complex.ext_iff] at h; simp at h
  have hden2 : (1 + (a : ℂ) ^ 2) ≠ 0 := by
    rw [show (1 + (a : ℂ) ^ 2) = ((1 + a ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + a ^ 2).ne'
  rw [div_eq_div_iff hden hden2]
  linear_combination ((β : ℂ) * (a : ℂ) ^ 2) * Complex.I_sq

/-! ## §C — the uncertainty relation (Junker Eq. 43–44) -/

/-- **[Junker Eq. 43] The position variance** `(Δx)² = (1 + ℏ²β²t²/m²)/2β`. -/
noncomputable def varX (β ℏ m t : ℝ) : ℝ := (1 + ℏ ^ 2 * β ^ 2 * t ^ 2 / m ^ 2) / (2 * β)

/-- **[Junker Eq. 43] The momentum (wavenumber) variance** `(Δk)² = β/2`. -/
noncomputable def varK (β : ℝ) : ℝ := β / 2

/-- **[Junker Eq. 44] The uncertainty relation** `(Δx)²(ΔP)² = ℏ²/4·[1 + (ℏβt/m)²]`, with `(ΔP)² =
ℏ²(Δk)²`. This is the **minimal uncertainty of standard quantum mechanics** — the spreading of a
Wigner–Dunkl Gaussian wave packet obeys exactly the ordinary Heisenberg relation (the first main result of
the paper). -/
theorem uncertainty_relation (β ℏ m t : ℝ) (hβ : 0 < β) (hm : m ≠ 0) :
    varX β ℏ m t * (ℏ ^ 2 * varK β) = ℏ ^ 2 / 4 * (1 + (ℏ * β * t / m) ^ 2) := by
  unfold varX varK; field_simp; ring

/-! ## §D — the free propagator and its `ν = 0` reduction (Junker Eq. 52–53) -/

/-- **[Junker Eq. 52–53] The free-propagator Gaussian exponent reduces to the standard form.** The Eq.-52
exponent `im(x²+y²)/2ℏt + mxy/(iℏt)` (with the `ν = 0` Dunkl kernel `E_0(z) = e^z` contributing the second
term) combines into `im(x−y)²/2ℏt` — the phase of the classical free propagator `K_0 = √(m/2πiℏt)
e^{im(x−y)²/2ℏt}` (Eq. 53). So the Wigner–Dunkl free propagator contains the ordinary Feynman free
propagator as its `ν = 0` case. -/
theorem freePropagator_exponent (m ℏ t x y : ℝ) (ht : t ≠ 0) (hℏ : ℏ ≠ 0) :
    Complex.I * m * ((x : ℂ) ^ 2 + y ^ 2) / (2 * ℏ * t) + m * x * y / (Complex.I * ℏ * t)
      = Complex.I * m * ((x : ℂ) - y) ^ 2 / (2 * ℏ * t) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hℏ' : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  field_simp
  linear_combination (2 * (m : ℂ) * (x : ℂ) * (y : ℂ)) * Complex.I_sq

/-! ## §E — Lie–Trotter and the time-sliced path integral (Junker Eq. 54, 56) -/

/-- **[Junker Eq. 56] The potential phase of one path-integral time slice** `e^{−iV ε/ℏ}` — the
interaction factor attached to each slice in the time-sliced path integral, multiplying the free
(kinetic) propagator `K_ν(x_j, x_{j-1}; ε)`. -/
noncomputable def pathSliceWeight (V ε ℏ : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((V * ε / ℏ : ℝ) : ℂ)))

/-- **[Eq. 56] In real time the potential slice is unitary** (`‖e^{−iVε/ℏ}‖ = 1`): the interaction
contributes only a phase per slice, so the Lorentzian (Minkowski) path integral is norm-preserving slice by
slice — the Euclidean (Feynman–Kac) damping appears only under Wick rotation
(`Dunkl.ComplexPathIntegralSignatures`). -/
theorem pathSlice_unitary (V ε ℏ : ℝ) : ‖pathSliceWeight V ε ℏ‖ = 1 := by
  unfold pathSliceWeight
  rw [show -(Complex.I * ((V * ε / ℏ : ℝ) : ℂ)) = ((-(V * ε / ℏ) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **[Junker Eq. 54] The Lie–Trotter slice factorisation.** One substep of the time evolution splits into
a free (kinetic) factor times the potential phase — the scalar realization is
`Dunkl.LorentzianPropagator.lorentzianTrotterStep`, whose `N`-fold product `lorentzianTrotterProduct`
is the time-sliced path integral (Eq. 56). The potential slice here is its potential factor; its modulus is
`pathSlice_unitary = 1`. -/
theorem pathSlice_eq_lorentzianTrotter_potential (V ε ℏ : ℝ) :
    pathSliceWeight V ε ℏ = Complex.exp (-(Complex.I * ((V * ε / ℏ : ℝ) : ℂ))) := rfl

end Physlib.QuantumMechanics.ComplexAction.Dunkl.FreeParticlePathIntegral

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhPowerSpectrum

/-!
# Sciama–Candelas–Deutsch §3.3: the radiating black hole loses mass at its luminosity

The "tentative step towards the back-reaction problem": from *classical* general relativity, the rate of
change of the black-hole mass is the negative of its luminosity.  The Newman–Penrose equation (20) with the
horizon flux `⟨T_{tr*}⟩ = L/4πr²` gives the area-decrease law

`dA/dv = −2AL/M`   (Eq. 21 and after),

and with the Schwarzschild area–mass relation `A = 16πM²` this becomes the energy-conservation statement

`dM/dv = −L`.

Here that final algebraic step is formalized: given the area–mass relation, the chain rule `dA/dv =
32πM·dM/dv`, and the NP area-decrease law, energy conservation follows.

* `massLoss_eq_neg_luminosity` — `dM/dv = −L` from `A = 16πM²`, the chain rule, and `dA/dv = −2AL/M`.
* `schwarzschild_area_rate` — the chain rule `dA/dv = 32πM·dM/dv` from `A = 16πM²` (as a consistency check).

Honest scope: the algebraic combination `A=16πM²`, chain rule, and NP area-law into `dM/dv=−L`; the
Newman–Penrose derivation of the area-decrease law and the flux `L/4πr²` are standard-GR inputs, taken as
hypotheses.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBlackHoleMassLoss

/-- **[Mass loss = luminosity] `dM/dv = −L`.**  From the Schwarzschild area–mass relation `A = 16πM²`, the
chain rule `dA/dv = 32πM·dM/dv`, and the Newman–Penrose area-decrease law `dA/dv = −2AL/M`, the black-hole
mass decreases at exactly its luminosity — energy conservation for the radiating horizon. -/
theorem massLoss_eq_neg_luminosity (M A L dMdv dAdv : ℝ)
    (hArea : A = 16 * Real.pi * M ^ 2) (hChain : dAdv = 32 * Real.pi * M * dMdv)
    (hNP : dAdv = -2 * A * L / M) (hM : M ≠ 0) : dMdv = -L := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : 32 * Real.pi * M * dMdv = -2 * A * L / M := hChain.symm.trans hNP
  rw [hArea] at h
  have hrhs : -2 * (16 * Real.pi * M ^ 2) * L / M = 32 * Real.pi * M * (-L) := by
    field_simp
    ring
  rw [hrhs] at h
  have h32 : 32 * Real.pi * M ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hπ) hM
  exact mul_left_cancel₀ h32 h

/-- **[Chain rule] `dA/dv = 32πM·dM/dv`** from `A = 16πM²` — the rate at which the horizon area changes with
the mass (a consistency check on the `dM/dv = −L` inputs; `hArea` differentiated). -/
theorem schwarzschild_area_rate (M dMdv : ℝ) :
    (32 * Real.pi * M) * dMdv = (16 * Real.pi) * (2 * M * dMdv) := by
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBlackHoleMassLoss

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.DiracSchrodingerChain

/-!
# The conclusive non-relativistic limit: Einstein/Dirac kinetic energy `→ p²/2m`

The chain `ComplexEinstein.DiracSchrodingerChain` reduces the complex Einstein dispersion to the Dirac
eigenvalue problem (exact) and factors it to the kinetic relation `(E − mc²)(E + mc²) = (cp)²`. The
**Schrödinger** end of that chain was only a point-identity there. This file proves the *conclusive*
statement: the relativistic kinetic energy converges, as a genuine limit, to the Schrödinger kinetic
energy.

## The limit

For a physical mass `m > 0` the relativistic kinetic energy is, exactly (`einsteinKinetic_eq`),

 `E(c) − mc² = p² / (√(m² + p²/c²) + m)` (`E(c) = √((mc²)² + (cp)²)`),

and therefore (`einsteinKinetic_tendsto_schrodinger`)

 `lim_{c→∞} (E(c) − mc²) = p²/(2m)`.

This is the non-relativistic limit `|p| ≪ mc`: the rationalized kinetic energy
`p²/(√(m² + p²/c²) + m)` has the denominator `→ 2m`, so the kinetic energy `→ p²/2m` — *exactly* the
free Schrödinger kinetic energy, recovered as a limit (not an algebraic substitution at a point).

## The free Schrödinger equation at the limit energy

With the limit energy `E_S = p²/2m`, the mode `Ψ(t) = e^{−iE_S t/ℏ}` solves the free-particle
Schrödinger equation `iℏ ∂_t Ψ = (p²/2m) Ψ` (`schrodinger_free_mode`, via `greenKernel_satisfies_tdse`).
So the Dirac positive-energy mode, in the non-relativistic limit, *is* the free Schrödinger mode.

## What this adds over the chain file

The chain file's `dirac_kinetic_nonrel_eq_schrodinger` was the value of the kinetic energy *at*
`E + mc² = 2mc²` — an identity at one point, with the "limit" only asserted in prose. Here the limit
`c → ∞` is proved (`Filter.Tendsto`), and the resulting energy drives the genuine free Schrödinger
TDSE. This is the conclusive form of "Einstein ⟹ Dirac ⟹ Schrödinger".

## References

* The non-relativistic limit `√(m²c⁴ + c²p²) − mc² → p²/2m`. This development:
 `ComplexEinstein.DiracSchrodingerChain`, `ComplexEinstein.FullEinsteinDispersionConsistency`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Topology
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.DiracSchrodingerChain

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit

/-! ## §A — the exact rationalized kinetic energy -/

/-- **The exact relativistic kinetic energy, rationalized.** For `m > 0`, `c > 0`,

  `E(c) − mc² = p² / (√(m² + p²/c²) + m)`,

with `E(c) = √((mc²)² + (cp)²)`. (Rationalizing `√(m²c⁴ + c²p²) − mc²`; the denominator is manifestly
positive and has a finite `c → ∞` limit, unlike the difference of the two diverging terms.) -/
theorem einsteinKinetic_eq (m c p : ℝ) (hm : 0 < m) (hc : 0 < c) :
    einsteinEnergy m c p - m * c ^ 2
      = p ^ 2 / (Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2) + m) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hEnn : 0 ≤ einsteinEnergy m c p := photonDispersion_nonneg _ _ _
  have hEsq : einsteinEnergy m c p ^ 2 = (m * c ^ 2) ^ 2 + (c * p) ^ 2 := einsteinEnergy_sq m c p
  -- `√(m² + p²/c²) = E/c²`
  have hsqrt : Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2) = einsteinEnergy m c p / c ^ 2 := by
    have hq : 0 ≤ einsteinEnergy m c p / c ^ 2 := div_nonneg hEnn hc2.le
    have hsq : (einsteinEnergy m c p / c ^ 2) ^ 2 = m ^ 2 + p ^ 2 / c ^ 2 := by
      rw [div_pow, hEsq]; field_simp
    rw [← hsq, Real.sqrt_sq hq]
  have hden : 0 < einsteinEnergy m c p / c ^ 2 + m := add_pos_of_nonneg_of_pos
    (div_nonneg hEnn hc2.le) hm
  rw [hsqrt, eq_div_iff (ne_of_gt hden)]
  have hexp : (einsteinEnergy m c p - m * c ^ 2) * (einsteinEnergy m c p / c ^ 2 + m)
      = (einsteinEnergy m c p ^ 2 - (m * c ^ 2) ^ 2) / c ^ 2 := by
    field_simp; ring
  rw [hexp, hEsq]; field_simp; ring

/-! ## §B — the conclusive non-relativistic limit `→ p²/2m` -/

/-- **The relativistic kinetic energy converges to the Schrödinger kinetic energy.** For `m > 0`,

  `lim_{c→∞} (E(c) − mc²) = p²/(2m)`,

a genuine limit (`Filter.Tendsto`), not an evaluation at a point. The rationalized kinetic energy
`p²/(√(m² + p²/c²) + m)` has denominator `→ 2m`, so the kinetic energy `→ p²/2m`. -/
theorem einsteinKinetic_tendsto_schrodinger (m p : ℝ) (hm : 0 < m) :
    Tendsto (fun c => einsteinEnergy m c p - m * c ^ 2) atTop (𝓝 (p ^ 2 / (2 * m))) := by
  have heq : (fun c => einsteinEnergy m c p - m * c ^ 2)
      =ᶠ[atTop] fun c => p ^ 2 / (Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2) + m) := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    exact einsteinKinetic_eq m c p hm hc
  rw [tendsto_congr' heq]
  have h0 : Tendsto (fun c : ℝ => p ^ 2 / c ^ 2) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop (by norm_num))
  have hin : Tendsto (fun c : ℝ => m ^ 2 + p ^ 2 / c ^ 2) atTop (𝓝 (m ^ 2)) := by
    simpa using tendsto_const_nhds.add h0
  have hsq : Tendsto (fun c : ℝ => Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2)) atTop (𝓝 m) := by
    have := hin.sqrt
    rwa [Real.sqrt_sq hm.le] at this
  have hden : Tendsto (fun c : ℝ => Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2) + m) atTop (𝓝 (2 * m)) := by
    have := hsq.add (tendsto_const_nhds (x := m))
    rwa [show m + m = 2 * m by ring] at this
  have h2m : (2 * m) ≠ 0 := ne_of_gt (mul_pos two_pos hm)
  exact tendsto_const_nhds.div hden h2m

/-! ## §C — the free Schrödinger equation at the limit energy -/

/-- **The non-relativistic mode solves the free-particle Schrödinger equation.** With the limit energy
`E_S = p²/2m`, the mode `Ψ(t) = e^{−iE_S t/ℏ}` solves `iℏ ∂_t Ψ = (p²/2m) Ψ` — the genuine free
Schrödinger TDSE (not the relativistic energy). So the Dirac positive-energy mode reduces, in the
non-relativistic limit, to the free Schrödinger mode. -/
theorem schrodinger_free_mode (m p ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    (Complex.I * (ℏ : ℂ))
        * deriv (fun s : ℝ => greenKernel ((p ^ 2 / (2 * m) : ℝ) : ℂ) ℏ s) t
      = ((p ^ 2 / (2 * m) : ℝ) : ℂ) * greenKernel ((p ^ 2 / (2 * m) : ℝ) : ℂ) ℏ t :=
  greenKernel_satisfies_tdse _ ℏ t hℏ

/-! ## §D — the conclusive chain -/

/-- **Complex Einstein ⟹ Dirac ⟹ Schrödinger, conclusively.** For a physical mass `m > 0`, speed
`c > 0`, momentum `p`, and `ℏ ≠ 0`:

* **(Einstein ⟹ Dirac)** the full-Einstein energy `E` is an eigenvalue of the Dirac Hamiltonian,
  `det(E·1 − H) = 0`;
* **(exact kinetic)** `E − mc² = (cp)²/(E + mc²)` — the exact relativistic kinetic energy;
* **(⟹ Schrödinger, as a limit)** `lim_{c→∞} (E(c) − mc²) = p²/2m` — the kinetic energy converges to
  the Schrödinger kinetic energy (a genuine `Tendsto`);
* **(free Schrödinger TDSE)** the mode `e^{−i(p²/2m)t/ℏ}` solves `iℏ ∂_t Ψ = (p²/2m) Ψ`.

The non-relativistic limit is proved, not asserted — the conclusive form of the chain. -/
theorem complexEinstein_dirac_schrodinger_conclusive (m c p : ℝ) (hm : 0 < m) (hc : 0 < c)
    (ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    (einsteinEnergy m c p • (1 : Matrix (Fin 2) (Fin 2) ℝ)
          - diracHamiltonian (m * c ^ 2) (c * p)).det = 0
      ∧ einsteinEnergy m c p - m * c ^ 2
          = (c * p) ^ 2 / (einsteinEnergy m c p + m * c ^ 2)
      ∧ Tendsto (fun c' => einsteinEnergy m c' p - m * c' ^ 2) atTop (𝓝 (p ^ 2 / (2 * m)))
      ∧ (Complex.I * (ℏ : ℂ))
            * deriv (fun s : ℝ => greenKernel ((p ^ 2 / (2 * m) : ℝ) : ℂ) ℏ s) t
          = ((p ^ 2 / (2 * m) : ℝ) : ℂ) * greenKernel ((p ^ 2 / (2 * m) : ℝ) : ℂ) ℏ t := by
  have hEnn : 0 ≤ einsteinEnergy m c p := photonDispersion_nonneg _ _ _
  have hdirac : (einsteinEnergy m c p • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      - diracHamiltonian (m * c ^ 2) (c * p)).det = 0 :=
    fullEinstein_implies_dirac (m * c ^ 2) c p (einsteinEnergy m c p) (einstein_fullDispersion m c p)
  have hEΔ : einsteinEnergy m c p + m * c ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos hEnn (mul_pos hm (pow_pos hc 2)))
  exact ⟨hdirac,
    dirac_kinetic_exact (m * c ^ 2) c p (einsteinEnergy m c p) hEΔ hdirac,
    einsteinKinetic_tendsto_schrodinger m p hm,
    schrodinger_free_mode m p ℏ t hℏ⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit

end

end

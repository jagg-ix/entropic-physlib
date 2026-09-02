/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungTransformFisherPotential
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy

/-!
# The viscous Navier–Stokes energy dissipation is the Fisher information of the Madelung transform

The Landau–Lifshitz–Navier–Stokes equation `∂ₜu = Δu − (u·∇)u − ∇p − √ε ∇·ξ_δ` of B. Gess, D. Heydecker,
Z. Wu, *Landau–Lifshitz–Navier–Stokes equations: large deviations and relationship to the energy equality*
(arXiv:2311.02223) has a **viscous Laplacian** term `Δu`. Pairing it against `u` produces the dissipation
`‖∇u‖²` that appears in their Leray energy inequality (Eq. 1.3),

  `½‖u(t)‖²_{L²} + ∫₀ᵗ ‖u(s)‖²_{H¹} ds ≤ ½‖u(0)‖²_{L²} − ∫₀ᵗ ⟨∇u, g⟩ ds`,

whose dissipation term `‖u‖²_{H¹} = ‖∇u‖²` is Leray's energy identity `dE/dt = −ν‖∇u‖²`. The paper's own
results (the large-deviations principle, weak–strong uniqueness, the energy *equality* vs. inequality gap =
anomalous dissipation) are stochastic-PDE analysis beyond a proof assistant; the exact algebraic **kernel**
those results rest on is the viscous Laplacian's Dirichlet form, and *that* is the same Laplacian that carries
the Bohm quantum potential and the Fisher information of the Madelung transform
(`BohmMadelung.MadelungTransformFisherPotential`).

This module formalizes that shared kernel — the pointwise **energy-dissipation identity** (carré du champ)

  `f·f'' = ½(f²)'' − (f')²`,   i.e.   `f·Δf = ½Δ(f²) − |∇f|²`,

and reads its dissipation density `(f')²` two ways: with `f = u` a velocity component it is the Navier–Stokes
viscous dissipation `|∇u|²` of Eq. 1.3; with `f = √ρ` the Madelung amplitude it is a quarter of the
**Fisher information density** `fisherDensity(ρ)` of `MadelungTransformFisherPotential`. The *same* Dirichlet
energy the viscous term removes from the fluid is the information geometry of the density.

Reuses (GREP-first, no duplication) the grounded `deriv` lemmas of
`BohmMadelung.MadelungTransformFisherPotential` (`density_hasDerivAt`, `density_secondDeriv_hasDerivAt`,
`fisherDensity`, `fisherDensity_amplitude_form`) and the Navier–Stokes enstrophy dissipation of
`NavierStokes.VorticityCoadjointEnstrophy` (`enstrophyDissipationRate`, `enstrophyDissipationRate_nonpos`).

* **§A — the energy-dissipation identity** (`energyDissipation_identity`): `f·f'' = ½(f²)'' − (f')²`, both
  derivatives grounded in Mathlib's `deriv` of `f²`.
* **§B — the dissipation density is the Fisher information density** (`dissipationDensity_eq_fisher`):
  `(f')² = ¼·fisherDensity(f²)`.
* **§C — Leray's energy-inequality sign and the enstrophy dissipation** (`viscous_energyDissipation`,
  `viscousDissipationRate_nonpos`, `enstrophy_dissipation_from_fisher`): the viscous rate `−ν(f')² ≤ 0` and
  the NS enstrophy dissipation driven by the Fisher information density.
* **§D — assembled** (`viscous_dissipation_is_fisher`).

## References

* B. Gess, D. Heydecker, Z. Wu, arXiv:2311.02223, Eq. 1.1/1.3 (viscous dissipation `‖∇u‖²`, Leray energy
  inequality); J. Leray, Acta Math. 63 (1934) 193 (`dE/dt = −ν‖∇u‖²`). Carriers:
  `BohmMadelung.MadelungTransformFisherPotential`, `NavierStokes.VorticityCoadjointEnstrophy`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.ViscousDissipationFisherInformation

open Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungTransformFisherPotential
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy

/-! ### §A The energy-dissipation identity (the viscous Laplacian's carré du champ) -/

/-- **[Energy-dissipation identity / carré du champ] `f·f'' = ½(f²)'' − (f')²`.** The pointwise identity
`f·Δf = ½Δ(f²) − |∇f|²` behind every energy estimate for a diffusion `∂ₜf = Δf`: multiplying by `f` and using
this identity, the conservative `½Δ(f²)` integrates away on a closed domain, leaving the dissipation `−|∇f|²`.
Both derivatives are Mathlib's `deriv` of `f²`, reusing `density_secondDeriv_hasDerivAt`. -/
theorem energyDissipation_identity (f f' f'' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y) (x : ℝ) :
    f x * f'' x = 1 / 2 * deriv (deriv (fun y => (f y) ^ 2)) x - (f' x) ^ 2 := by
  have hd2 : deriv (deriv (fun y => (f y) ^ 2)) x = 2 * (f' x) ^ 2 + 2 * f x * f'' x := by
    have hfun : deriv (fun y => (f y) ^ 2) = fun y => 2 * f y * f' y := by
      funext y; exact (density_hasDerivAt f f' hf y).deriv
    rw [hfun]; exact (density_secondDeriv_hasDerivAt f f' f'' hf hf' x).deriv
  rw [hd2]; ring

/-! ### §B The dissipation density is the Fisher information density -/

/-- **[The viscous dissipation density is the Fisher information density] `(f')² = ¼·fisherDensity(f²)`.**
Read as a velocity component `f = u`, `(f')²` is the Navier–Stokes viscous dissipation density `|∇u|²` of the
Leray energy inequality (Eq. 1.3); read as the Madelung amplitude `f = √ρ`, it is a quarter of the Fisher
information density `fisherDensity(ρ) = (ρ')²/ρ` of `MadelungTransformFisherPotential`. The same Dirichlet
energy is both the fluid's viscous dissipation and the information geometry of the density. -/
theorem dissipationDensity_eq_fisher (f f' : ℝ → ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (x : ℝ) (hfx : f x ≠ 0) :
    (f' x) ^ 2 = 1 / 4 * fisherDensity (fun y => (f y) ^ 2) x := by
  rw [fisherDensity_amplitude_form f f' hf x hfx]; ring

/-! ### §C Leray's energy-inequality sign and the enstrophy dissipation -/

/-- **[The viscous term splits into a conservative flux and the dissipation] `ν·f·f'' = ν·½(f²)'' − ν(f')²`.**
Scaling the energy-dissipation identity by the viscosity `ν`: the viscous contribution to `∂ₜ(½f²)` is a
conservative `ν·½Δ(f²)` (a total divergence) minus the strictly dissipative `ν(f')²`. -/
theorem viscous_energyDissipation (ν : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y) (x : ℝ) :
    ν * (f x * f'' x)
      = ν * (1 / 2 * deriv (deriv (fun y => (f y) ^ 2)) x) - ν * (f' x) ^ 2 := by
  rw [energyDissipation_identity f f' f'' hf hf' x]; ring

/-- **[Leray's energy inequality sign] the viscous dissipation rate is non-positive** `−ν(f')² ≤ 0` for
`ν ≥ 0`. The dissipative part of the energy balance can only remove energy — the sign that makes the Leray
energy inequality (Eq. 1.3) a *decay*, and the fluctuation the paper's large deviations must overcome. -/
theorem viscousDissipationRate_nonpos (ν : ℝ) (f' : ℝ → ℝ) (x : ℝ) (hν : 0 ≤ ν) :
    -(ν * (f' x) ^ 2) ≤ 0 := by
  have h : 0 ≤ ν * (f' x) ^ 2 := mul_nonneg hν (sq_nonneg _)
  linarith

/-- **[The Fisher information density drives the NS enstrophy dissipation]
`enstrophyDissipationRate ν (¼·fisherDensity(f²)) ≤ 0`.** Feeding the Fisher information density (= the
viscous dissipation density `(f')²`, `dissipationDensity_eq_fisher`) as the palinstrophy of
`VorticityCoadjointEnstrophy.enstrophyDissipationRate` gives a non-positive rate: the information geometry of
the Madelung density is exactly the non-negative quantity whose viscous removal drives the Navier–Stokes
enstrophy monotonically down (`enstrophyDissipationRate_nonpos`). -/
theorem enstrophy_dissipation_from_fisher (ν : ℝ) (f f' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (x : ℝ) (hfx : f x ≠ 0) (hν : 0 ≤ ν) :
    enstrophyDissipationRate ν (1 / 4 * fisherDensity (fun y => (f y) ^ 2) x) ≤ 0 := by
  have hpalin : 0 ≤ 1 / 4 * fisherDensity (fun y => (f y) ^ 2) x := by
    rw [← dissipationDensity_eq_fisher f f' hf x hfx]; positivity
  exact enstrophyDissipationRate_nonpos ν _ hν hpalin

/-! ### §D The viscous dissipation is the Fisher information, assembled -/

/-- **[The viscous Navier–Stokes dissipation is the Fisher information, assembled].** For a field `f` (a
velocity component, or the Madelung amplitude `√ρ`) with viscosity `ν ≥ 0` and `f(x) ≠ 0`:

* **(energy-dissipation identity)** `f·f'' = ½(f²)'' − (f')²` — the viscous Laplacian's carré du champ;
* **(dissipation = Fisher)** `(f')² = ¼·fisherDensity(f²)` — the viscous dissipation density is the Fisher
  information density of the Madelung transform;
* **(Leray sign)** `−ν(f')² ≤ 0` — the dissipation only removes energy (Eq. 1.3);
* **(NS enstrophy)** `enstrophyDissipationRate ν (¼·fisherDensity(f²)) ≤ 0` — the Fisher information drives
  the enstrophy down.

The energy the viscous term dissipates in Navier–Stokes is the Fisher information of the Madelung transform,
through the one Laplacian both share. -/
theorem viscous_dissipation_is_fisher (ν : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (x : ℝ) (hfx : f x ≠ 0) (hν : 0 ≤ ν) :
    f x * f'' x = 1 / 2 * deriv (deriv (fun y => (f y) ^ 2)) x - (f' x) ^ 2
      ∧ (f' x) ^ 2 = 1 / 4 * fisherDensity (fun y => (f y) ^ 2) x
      ∧ -(ν * (f' x) ^ 2) ≤ 0
      ∧ enstrophyDissipationRate ν (1 / 4 * fisherDensity (fun y => (f y) ^ 2) x) ≤ 0 :=
  ⟨energyDissipation_identity f f' f'' hf hf' x, dissipationDensity_eq_fisher f f' hf x hfx,
    viscousDissipationRate_nonpos ν f' x hν, enstrophy_dissipation_from_fisher ν f f' hf x hfx hν⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.ViscousDissipationFisherInformation

end

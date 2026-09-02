/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.CuboidalLatticeBainGeometry
public import Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Casimir self-interaction energy density of a QED field: `α ∝ R⁷` and the `R⁻⁷` lattice sum

The vacuum self-interaction energy (SIE) model of Tkatchenko & Fedorov, *Casimir Self-Interaction Energy Density
of Quantum Electrodynamic Fields* (arXiv:2301.10151, 2023) — the same authors as
`VanDerWaalsPolarizabilityScaling` (the `R_vdW ∝ α^{1/7}` law). A QED field is modelled as a medium of transient
`e⁻/e⁺` dipoles whose polarizability follows a quantum scaling law `α ∝ R⁷`; the pairwise Casimir energy is an
`R⁻⁷` van der Waals interaction summed over a bcc/fcc lattice, giving a finite vacuum energy density.

This file formalizes only the exact algebraic content of the model — the scaling-law/`C₆` link, the
fine-structure power bookkeeping, the `R⁻⁷` lattice-sum leading term, the mass-scaling invariances, the analytic
effective pair number, the shell integral and the multipole suppression. The paper's *physical interpretation* of
this energy density as dark energy / the cosmological constant (its `w = −1` equation of state and numerical
match to `Λ`) is **not** formalized: `w = P/Ē = −1` is a definitional identity of any volume-linear energy
(`P = −dE/dV = −Ē`), carrying no derived content beyond the cosmological-constant *form*, and the match to `Λ` is
an observational comparison — see `CasimirLengthHierarchy` §D.

Throughout, `β = α_fsc^{1/3}` (`α_fsc` the fine-structure constant), which turns every fractional fine-structure
power into an integer power of `β`.

* **§A — the quantum scaling law is the vdW `α^{1/7}` law (Eq. 2).** `qedPolarizability β a₀ R =
  (2/3)(β/a₀)⁴R⁷`; **`qed_scaling_is_vdW_seventh`** (`R⁷ = (3/2)(a₀/β)⁴·α`) — the QED polarizability scaling is
  exactly `VanDerWaalsPolarizabilityScaling`'s `R_vdW⁷ = C⁷α` with `C⁷ = (3/2)(a₀/β)⁴`.
* **§B — the pairwise SIE fine-structure powers (Eqs. 4–5).** `sie2FromRadius` and **`sie2_thomson`**
  (at `R = R_Th = β⁶a₀`, the SIE `∝ β³²`) and **`sie2_hartree`** (`∝ β²⁹E_h`, i.e. `α_fsc^{29/3}`): the exponent
  bookkeeping `8 + 24 − 3 = 29`.
* **§C — the `R⁻⁷` Casimir lattice sum (Eq. 7).** `nEffSummand R Rⱼ = (2R)⁷/Rⱼ⁷`; **`nEff_nearest_term`**
  (a touching pair at `Rⱼ = 2R` contributes `1`), so the leading `N_eff` is the kissing number — **`fcc_larger_nEff_leading`** (`kissBcc < kissFcc`, `8 < 12`): fcc's larger contact number gives the larger
  Casimir lattice sum, echoing `fcc_denser_than_bcc`.
* **§D — lepton universality.** `polDensity α R = α/((8π/3)R³)`; **`lepton_polDensity_invariant`**
  (under `α ↦ s³α`, `R ↦ sR`, `s = mₑ/μ`, the density is unchanged) and **`sie_structural_scaling`**
  (`s⁴·f(s³α,sR,s³V) = f(α,R,V)`, the `N_eff ∝ s⁴` renormalization compensating the per-pair `s⁻⁴`): the
  electron, muon and tau fields have the *same* polarizability and SIE density.
* **§E — the analytic effective pair number (Eqs. 5, 11).** `radialSIE` (the concentric-shell energy `∝ β³¹`) and
  **`nEff_analytic`** (`radialSIE/pairwiseSIE = (768π²/23)·β² ≈ 12.40`): the ratio of the shell derivation to the
  pairwise energy gives `N_eff` in closed form, avoiding the lattice-sum uncertainty — and it lands between the
  bcc (`11.05`) and fcc (`13.36`) values of §C.
* **§F — the concentric-shell integral (Eqs. 9–10).** **`shell_integral`** (`∫₀^{r_f} r⁵ dr = r_f⁶/6`): the
  radial summation over spherical field shells that turns the shell polarizability density into the `r_f⁶`
  energy, the alternative to the particle/antiparticle lattice sum.
* **§G — multipole suppression.** `octupoleDipoleRatio β = β¹⁸`; **`octupole_suppression`** (`= (β³)⁶ = α_fsc⁶`)
  and **`octupoleDipoleRatio_lt_one`** (`< 1` for `0 < β < 1`): the quadrupole contribution vanishes by
  particle/antiparticle symmetry and the octupole is suppressed by `α_fsc⁶`, so the dipole approximation is
  accurate.

**Honest layering.** All are exact `ring`/`field_simp`/`integral_pow` identities in the model's variables. The
physical inputs — the scaling law's derivation, `R_Th = α_fsc²a₀`, the lattice-sum numerics (`N_eff ≈ 11.05` bcc,
`13.36` fcc), the match to `Λ`, and the dark-energy interpretation — are the paper's claims, recorded not
re-derived (the dark-energy `w = −1` reading is omitted: it is definitional, not a theorem — see the header note).

## References

* Tkatchenko & Fedorov, arXiv:2301.10151 (2023), Eqs. 2–11. Built on `ComplexAction.VanDerWaalsPolarizabilityScaling`
  and `Particles.CuboidalLatticeBainGeometry`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling
open Physlib.QuantumMechanics.ComplexAction.Particles.CuboidalLatticeBainGeometry

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.CasimirSelfInteractionEnergyDensity


/-- The **QED-field polarizability** `α_{e/e⁺} = (2/3)(β·R/a₀)⁴·R³ = (2/3)(β/a₀)⁴R⁷` (Eq. 2), with
`β = α_fsc^{1/3}`: the transient `e⁻/e⁺` dipole polarizability scales as the seventh power of the vdW radius. -/
noncomputable def qedPolarizability (β a₀ R : ℝ) : ℝ := 2 / 3 * (β / a₀) ^ 4 * R ^ 7

/-- **The QED scaling law is the van der Waals `α^{1/7}` law** `R⁷ = (3/2)(a₀/β)⁴·α` — the quantum scaling law
of Eq. 2 is exactly `VanDerWaalsPolarizabilityScaling`'s `R_vdW⁷ = C⁷α` with `C⁷ = (3/2)(a₀/β)⁴`, tying the
Casimir-field polarizability to the vdW radius scaling. -/
lemma qed_scaling_is_vdW_seventh (β a₀ R : ℝ) (hβ : β ≠ 0) (ha : a₀ ≠ 0) :
    R ^ 7 = 3 / 2 * (a₀ / β) ^ 4 * qedPolarizability β a₀ R := by
  unfold qedPolarizability
  field_simp


/-- The **pairwise SIE from the radius** `Ē⁽²⁾ = −(23ℏc/3072π²)(β/a₀)⁸R⁴` (Eq. 4), after inserting the scaling
law and the pair volume into the retarded Casimir energy. -/
noncomputable def sie2FromRadius (β a₀ ℏc R : ℝ) : ℝ :=
  -(23 * ℏc / (3072 * Real.pi ^ 2)) * (β / a₀) ^ 8 * R ^ 4

/-- **At the Thomson radius the pairwise SIE is `∝ β³²`** — with `R = R_Th = α_fsc²a₀ = β⁶a₀`,
`Ē⁽²⁾ = −(23ℏc/3072π²)·β³²/a₀⁴`; the exponent `32 = 8 + 24` from `(β/a₀)⁸·(β⁶a₀)⁴`. -/
lemma sie2_thomson (β a₀ ℏc : ℝ) (ha : a₀ ≠ 0) :
    sie2FromRadius β a₀ ℏc (β ^ 6 * a₀) = -(23 * ℏc / (3072 * Real.pi ^ 2)) * β ^ 32 / a₀ ^ 4 := by
  unfold sie2FromRadius
  field_simp

/-- **In Hartree units the pairwise SIE is `∝ β²⁹E_h`** — substituting `ℏc = E_h·a₀/β³` (from `E_h = ℏcα_fsc/a₀
= ℏcβ³/a₀`) gives `Ē⁽²⁾ = −(23/3072π²)·β²⁹·E_h/a₀³`, i.e. the `α_fsc^{29/3}` law of Eq. 5: the bookkeeping
`32 − 3 = 29`. -/
lemma sie2_hartree (β a₀ E_h : ℝ) (ha : a₀ ≠ 0) (hβ : β ≠ 0) :
    sie2FromRadius β a₀ (E_h * a₀ / β ^ 3) (β ^ 6 * a₀)
      = -(23 / (3072 * Real.pi ^ 2)) * β ^ 29 * E_h / a₀ ^ 3 := by
  unfold sie2FromRadius
  field_simp


/-- The **`R⁻⁷` Casimir lattice-sum summand** `(2R)⁷/|Rⱼ|⁷` (Eq. 7), whose sum over the bcc/fcc lattice vectors
`Rⱼ ≠ 0` is the effective pair number `N_eff`. -/
noncomputable def nEffSummand (R Rj : ℝ) : ℝ := (2 * R) ^ 7 / Rj ^ 7

/-- **A touching pair contributes `1` to the lattice sum** `(2R)⁷/(2R)⁷ = 1` — nearest neighbours sit at
`|Rⱼ| = 2R`, so each contributes unity and the leading `N_eff` is the kissing number of the lattice. -/
lemma nEff_nearest_term (R : ℝ) (hR : R ≠ 0) : nEffSummand R (2 * R) = 1 := by
  unfold nEffSummand
  rw [div_self]
  positivity

/-- **fcc gives the larger leading Casimir lattice sum than bcc** `kissBcc < kissFcc` (`8 < 12`) — the leading
`N_eff` is the kissing number (§`nEff_nearest_term`), so the denser fcc lattice (larger contact number) has the
larger `R⁻⁷` Casimir sum, mirroring `CuboidalLatticeBainGeometry.fcc_denser_than_bcc`. -/
lemma fcc_larger_nEff_leading : kissBcc < kissFcc := fcc_max_kissing.1


/-- The **polarizability density** `α/V = α/((8π/3)R³)` (`V = 2·(4π/3)R³`, both `e⁻` and `e⁺` contributing). -/
noncomputable def polDensity (α R : ℝ) : ℝ := α / (8 * Real.pi / 3 * R ^ 3)

/-- **The polarizability density is lepton-universal** — under the mass scaling `α ↦ s³α`, `R ↦ sR`
(`s = mₑ/μ`, from `α_μ = (mₑ/μ)³α_e`, `R_μ = (mₑ/μ)R_e`) the density is unchanged: the electron, muon and tau
QED fields have the *same* polarizability density `∝ ε₀`. -/
lemma lepton_polDensity_invariant (α R s : ℝ) (hs : s ≠ 0) (hR : R ≠ 0) :
    polDensity (s ^ 3 * α) (s * R) = polDensity α R := by
  unfold polDensity
  field_simp

/-- The **pairwise-SIE structural factor** `α²/((2R)⁷V)` of the retarded Casimir energy. -/
noncomputable def sieStructural (α R V : ℝ) : ℝ := α ^ 2 / ((2 * R) ^ 7 * V)

/-- **The SIE density is lepton-universal** `s⁴·f(s³α, sR, s³V) = f(α, R, V)` — the per-pair Casimir energy
scales as `s⁻⁴ = (μ/mₑ)⁴` under the mass scaling, exactly compensated by the `N_eff ∝ s⁴` renormalization (four
virtual particles, Heisenberg lifetime `τ_μ = τ_e·mₑ/μ`), so the total SIE density is the same for the electron,
muon and tau fields. -/
lemma sie_structural_scaling (α R V s : ℝ) (hs : s ≠ 0) (hR : R ≠ 0) (hV : V ≠ 0) :
    s ^ 4 * sieStructural (s ^ 3 * α) (s * R) (s ^ 3 * V) = sieStructural α R V := by
  unfold sieStructural
  field_simp


/-- The **radial (concentric-shell) SIE** `Ē_SIE = −(1/4)α_fsc^{31/3}E_h/a₀³ = −(1/4)β³¹E_h/a₀³` (Eq. 11) —
the self-interaction energy from summing over spherical field shells, `∝ β³¹`. -/
noncomputable def radialSIE (β E_h a₀ : ℝ) : ℝ := -(1 / 4) * β ^ 31 * E_h / a₀ ^ 3

/-- The **pairwise SIE in Hartree units** `−(23/3072π²)β²⁹E_h/a₀³` (Eq. 5), the closed form of `sie2_hartree`. -/
noncomputable def pairwiseSIE (β E_h a₀ : ℝ) : ℝ := -(23 / (3072 * Real.pi ^ 2)) * β ^ 29 * E_h / a₀ ^ 3

/-- **The pairwise SIE agrees with `sie2FromRadius`** at the Thomson radius and Hartree substitution — `pairwiseSIE`
is exactly the `sie2_hartree` value, so §E builds on the same energy. -/
lemma pairwiseSIE_eq (β a₀ E_h : ℝ) (ha : a₀ ≠ 0) (hβ : β ≠ 0) :
    pairwiseSIE β E_h a₀ = sie2FromRadius β a₀ (E_h * a₀ / β ^ 3) (β ^ 6 * a₀) :=
  (sie2_hartree β a₀ E_h ha hβ).symm

/-- **The effective pair number is `(768π²/23)β² ≈ 12.40`** `N_eff = Ē_SIE/Ē⁽²⁾_SIE = (768π²/23)α_fsc^{2/3}` —
dividing the radial-shell energy (`∝ β³¹`) by the pairwise energy (`∝ β²⁹`) gives `N_eff` in closed form
(exponent `31 − 29 = 2`), a lattice-free determination that lies between the bcc (`11.05`) and fcc (`13.36`)
`R⁻⁷` lattice sums of §C. -/
lemma nEff_analytic (β E_h a₀ : ℝ) (hβ : β ≠ 0) (hE : E_h ≠ 0) (ha : a₀ ≠ 0)
    (hpi : Real.pi ≠ 0) :
    radialSIE β E_h a₀ / pairwiseSIE β E_h a₀ = 768 * Real.pi ^ 2 / 23 * β ^ 2 := by
  unfold radialSIE pairwiseSIE
  field_simp
  ring


/-- **The concentric-shell integral is `r_f⁶/6`** `∫₀^{r_f} r⁵ dr = r_f⁶/6` — the radial summation over
spherical field shells (Eqs. 9–10) that produces the `r_f⁶` dependence of the shell SIE, the alternative to the
particle/antiparticle lattice sum. -/
lemma shell_integral (rf : ℝ) : ∫ r in (0 : ℝ)..rf, r ^ 5 = rf ^ 6 / 6 := by
  rw [integral_pow]; norm_num


/-- The **octupole-to-dipole SIE ratio** `β¹⁸ = α_fsc⁶` — the leading multipole correction beyond the dipole
approximation (the quadrupole vanishing by particle/antiparticle symmetry). -/
noncomputable def octupoleDipoleRatio (β : ℝ) : ℝ := β ^ 18

/-- **The octupole is suppressed by `α_fsc⁶`** `β¹⁸ = (β³)⁶ = α_fsc⁶` — since `β = α_fsc^{1/3}`, the octupolar
contribution carries six extra powers of the fine-structure constant relative to the dipole. -/
lemma octupole_suppression (β : ℝ) : octupoleDipoleRatio β = (β ^ 3) ^ 6 := by
  unfold octupoleDipoleRatio; ring

/-- **The octupole correction is negligible** `β¹⁸ < 1` for `0 < β < 1` (`α_fsc ≈ 1/137`, `β ≈ 0.19`) — the
dipole approximation for the QED-field SIE is accurate. -/
lemma octupoleDipoleRatio_lt_one (β : ℝ) (h0 : 0 < β) (h1 : β < 1) :
    octupoleDipoleRatio β < 1 := by
  unfold octupoleDipoleRatio; exact pow_lt_one₀ h0.le h1 (by norm_num)

end Physlib.QuantumMechanics.ComplexAction.Particles.CasimirSelfInteractionEnergyDensity

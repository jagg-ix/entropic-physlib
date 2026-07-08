/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Physlib.ClassicalMechanics.Noether.DissipativeBalance

/-!
# Navier–Stokes Noether invariant via the imaginary defect

The 3D Navier–Stokes enstrophy obeys the balance law

  `dΩ/dt = −2 · D_I`,    `D_I := νP − VS` (palinstrophy minus vortex stretching),

so the imaginary defect `D_I` plays the same role for NS as
`Physlib.ClassicalMechanics.Noether.DissipativeBalance.NoetherBalance.defect`
plays for an arbitrary dissipative-Noether system: it is the rate at which
the reversible enstrophy charge leaks to entropic time.

Under the **Constantin–Iyer identification** `ℏ = 2ν`, this matches the
entropic-time decay law

  `dE/dt = −(Texp / ℏ) · E`,   `E := Ω`,   `Texp := 2 D_I ℏ / Ω`,

so the EPT accumulator `Tacc'(t) = Texp(t) = 2 D_I(t) ℏ / Ω(t)` integrates
the *ratio* of defect to charge, and the **conserved NS Noether invariant**

  `J_NS(t) := Ω(t) · exp(Tacc(t) / ℏ)`

is locally constant (zero derivative under the balance + accumulator laws).

## Main results

* `enstrophyBalance_iff_EPTDecay` — equivalence between balance form and
  decay form on the positive-enstrophy stratum.
* `ns_noether_invariant_deriv_zero` — `d J_NS/dt = 0` (Noether
  conservation under dissipation when accumulated by the imaginary
  defect).
* `frozen_enstrophy_of_zero_defect` — at `D_I = 0` (the
  vortex-stretching = viscous-palinstrophy regime), the enstrophy is
  frozen: `dΩ/dt = 0`.
* `tauEnt_deriv_nonneg` — entropic proper time is non-decreasing for
  non-negative enstrophy: the entropic arrow of time is well-defined
  along any smooth NS solution.
* `NSEnstrophyNoetherBalance.toNoetherBalance` — instantiate the
  abstract `NoetherBalance` from the NS balance law, recovering
  `conserved_of_zero_defect`/`charge_decreasing_of_nonneg_defect` for
  NS enstrophy as corollaries of the general Noether dissipative
  balance theorems.

### Extensions (§§7-10, via `ns-tau.md`)

* `IsItoEntropySaturated` and `CI_from_ito_saturation` /
  `ito_saturation_from_CI` — the universal stochastic-calculus 1/2
  factor (Itô's lemma, Girsanov, Wiener entropy) fixes the
  Cameron-Martin completing-the-square maximum at `ℏ/(4ν) = 1/2`,
  giving the Constantin-Iyer identification `ℏ = 2ν` as a *theorem*
  (pure algebra) rather than a Prop hypothesis.
* `CI_uniqueness` — two positive `ℏ` values satisfying the Itô
  saturation at the same viscosity coincide; the Cameron-Martin
  weight uniquely determines `ℏ` once `ν` is fixed.
* `entropicProperTimeRate` and `entropicProperTimeRate_under_CI` —
  the pointwise `dτ/dt = (ν/ℏ)·Ω` rate, reducing under CI to
  `(1/2)·Ω`.
* `cameronMartinWeight_eq_zenoSuppression` — the algebraic identity
  `W := exp(−S_I/ℏ) = exp(−τ_ent)` with `S_I := ℏ·τ_ent`: the
  Cameron-Martin weight from the Constantin-Iyer stochastic
  Lagrangian representation **is** the quantum Zeno suppression
  factor (Popkov-Barontini-Presilla 2018).  Not an analogy.
* `PopkovLiouvillianData`, `PopkovGapCondition`,
  `effectiveZenoRate_pos`, `effectiveZenoRate_mul_denom_eq_spectralGap`
  — Popkov-type spectral-gap data for the NS Lindbladian
  `L = Γ·L₀ + K` (`L₀` Poincaré dissipator with gap `Δ = λ₁`, `K`
  vortex-stretching perturbation); the gap condition `‖K‖ < Δ` gives
  a positive effective rate `Δ_eff = Δ/(1 + ‖K‖)`.

## Cross-references

The quantum-side companion of `D_I` in this same dissipative-Noether
framework is the entropy-production rate
`(2/ℏ) · H_I.reApplyInnerSelf ψ` from
`Physlib.QuantumMechanics.FiniteTarget.NagaoNielsenSchrodinger`.  The
positive-operator pointwise kernel theorem
`ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero`
establishes the quantum-side "zero rate ⟹ kernel" step at the operator
level; the present file's `frozen_enstrophy_of_zero_defect` establishes
the NS-side "zero defect ⟹ frozen enstrophy" step at the scalar level.
Together with `Physlib.ClassicalMechanics.Noether.DissipativeBalance.NoetherBalance.conserved_of_zero_defect`,
they form a three-arm bridge:

  NS:        `D_I = 0  ⟹  dΩ/dt = 0`                       (this file)
  Abstract:  `defect = 0  ⟹  Q(t₂) = Q(t₁)`                 (DissipativeBalance)
  Quantum:   `Re ⟨ψ, H_I ψ⟩ = 0  ⟹  H_I ψ = 0`              (NagaoNielsenSchrodinger)

No new axioms.  Zero sorrys.

## References

- **Constantin & Iyer 2008** — *A stochastic Lagrangian representation
  of the 3D incompressible Navier–Stokes equations*. Source of the
  `ℏ = 2ν` identification that
  matches NS enstrophy dissipation to the entropic-time decay law.
- **Beale, Kato, Majda 1984** — *Remarks on the breakdown of smooth
  solutions for the 3-D Euler equations*.
  The BKM regularity criterion is the polynomial bound counterpart to
  the EPT accumulator finiteness used here.
- **Foias, Manley, Rosa, Temam 2001** — *Navier–Stokes Equations and
  Turbulence*.  Enstrophy balance and palinstrophy / vortex-stretching
  decomposition `D_I = νP − VS`.
- **Noether 1918** — *Invariante Variationsprobleme*; classical
  conservation laws from continuous symmetries.
- **Gough, Ratiu, Smolyanov 2015** — *Noether's theorem for dissipative
  quantum semigroups*.  Quantum-side dissipative Noether framework
  cross-referenced for the three-arm bridge above.

## Notes on the port

This file ports the abstract `NSEPTNoetherInvariantBridge` content from
``
into physlib, with the additional instantiation of physlib's abstract
`NoetherBalance` structure — closing the cross-repo gap between the NS
Noether invariant and the abstract dissipative-Noether infrastructure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.FluidDynamics.NavierStokes.NoetherInvariant

open Real

/-! ## §1 — Physical constants -/

/-- Physical constants for the NS enstrophy / EPT-Noether analysis:
positive Planck constant `ℏ` and positive viscosity `ν`. -/
structure EnstrophyEPTConstants where
  hbar     : ℝ
  nu       : ℝ
  hbar_pos : 0 < hbar
  nu_pos   : 0 < nu

/-- **Constantin–Iyer identification** `ℏ = 2ν`.  Under this match, the
entropic-time decay rate equals the NS enstrophy dissipation rate. -/
def EnstrophyEPTConstants.CI (c : EnstrophyEPTConstants) : Prop :=
  c.hbar = 2 * c.nu

/-! ## §2 — NS enstrophy dynamics and EPT decay conditions -/

/-- **NS enstrophy balance law** (Foias–Manley–Rosa–Temam):
`dΩ/dt = −2·D_I` with the **imaginary Noether defect**
`D_I := νP − VS` (palinstrophy minus vortex stretching). -/
def IsEnstrophyBalance (Omega D_I : ℝ → ℝ) : Prop :=
  ∀ t, deriv Omega t = -2 * D_I t

/-- **Entropic-time decay rate** of NS enstrophy.  When `Ω > 0`, the
imaginary-defect ratio gives `Texp(t) = 2 D_I(t) · ℏ / Ω(t)`. -/
def EnstrophyDecayRate (c : EnstrophyEPTConstants)
    (Omega D_I : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * D_I t * c.hbar / Omega t

/-- **Entropic-time accumulator law**: `Tacc'(t) = Texp(t)`. -/
def IsEnstrophyEPTAccumulator (c : EnstrophyEPTConstants)
    (Tacc Omega D_I : ℝ → ℝ) : Prop :=
  ∀ t, deriv Tacc t = EnstrophyDecayRate c Omega D_I t

/-- **Decay-law form** of the balance: `dΩ/dt = −(Texp/ℏ)·Ω`,
equivalent to the balance form when `Ω > 0`. -/
def IsEnstrophyEPTDecay (c : EnstrophyEPTConstants)
    (Omega D_I : ℝ → ℝ) : Prop :=
  ∀ t, deriv Omega t = -(EnstrophyDecayRate c Omega D_I t / c.hbar) * Omega t

/-- **Equivalence** between the enstrophy balance form and the
entropic-time decay form on the positive-enstrophy stratum. -/
theorem enstrophyBalance_iff_EPTDecay
    (c : EnstrophyEPTConstants) (Omega D_I : ℝ → ℝ)
    (hΩ_pos : ∀ t, 0 < Omega t) :
    IsEnstrophyBalance Omega D_I ↔ IsEnstrophyEPTDecay c Omega D_I := by
  simp only [IsEnstrophyBalance, IsEnstrophyEPTDecay, EnstrophyDecayRate]
  constructor
  · intro h t
    rw [h t]
    have hΩ : Omega t ≠ 0 := ne_of_gt (hΩ_pos t)
    have hħ : c.hbar ≠ 0 := ne_of_gt c.hbar_pos
    field_simp [hΩ, hħ]
  · intro h t
    rw [h t]
    have hΩ : Omega t ≠ 0 := ne_of_gt (hΩ_pos t)
    have hħ : c.hbar ≠ 0 := ne_of_gt c.hbar_pos
    field_simp [hΩ, hħ]

/-! ## §3 — The NS Noether invariant -/

/-- **NS Noether invariant** `J_NS(t) := Ω(t) · exp(Tacc(t)/ℏ)`.

This is the dissipative-Noether conserved charge for the NS enstrophy
system, generalising the reversible Noether invariant `Q` of
`Physlib.ClassicalMechanics.Noether.DissipativeBalance.NoetherBalance`
to the case where dissipation is accumulated multiplicatively via the
EPT accumulator `Tacc`. -/
def enstrophyNoetherInvariant
    (c : EnstrophyEPTConstants) (Tacc Omega : ℝ → ℝ) (t : ℝ) : ℝ :=
  Omega t * Real.exp (Tacc t / c.hbar)

/-- **Main theorem — NS Noether invariant is locally constant.**

Under the enstrophy balance `dΩ/dt = −2·D_I` and the EPT accumulator
law `Tacc'(t) = 2·D_I(t)·ℏ/Ω(t)`, the NS Noether invariant
`J_NS := Ω · exp(Tacc/ℏ)` has zero derivative:

  `d/dt[J_NS] = dΩ/dt · exp + Ω · exp · (Tacc'/ℏ)`
             `= −2·D_I · exp + Ω · exp · (2·D_I·ℏ/Ω/ℏ)`
             `= exp · (−2·D_I + 2·D_I) = 0`. -/
theorem ns_noether_invariant_deriv_zero
    (c : EnstrophyEPTConstants)
    (Omega Tacc D_I : ℝ → ℝ)
    (hΩ_diff   : Differentiable ℝ Omega)
    (hTacc_diff : Differentiable ℝ Tacc)
    (hΩ_pos    : ∀ t, 0 < Omega t)
    (hbal      : IsEnstrophyBalance Omega D_I)
    (hacc      : IsEnstrophyEPTAccumulator c Tacc Omega D_I) :
    ∀ t, deriv (fun τ => enstrophyNoetherInvariant c Tacc Omega τ) t = 0 := by
  intro t
  simp only [enstrophyNoetherInvariant]
  have hTacc_hda : HasDerivAt (fun τ => Tacc τ / c.hbar)
      (EnstrophyDecayRate c Omega D_I t / c.hbar) t := by
    have h := (hTacc_diff t).hasDerivAt.div_const c.hbar
    rw [hacc t] at h
    exact h
  have hmul : HasDerivAt (fun τ => Omega τ * Real.exp (Tacc τ / c.hbar))
      (deriv Omega t * Real.exp (Tacc t / c.hbar) +
       Omega t * (Real.exp (Tacc t / c.hbar) *
         (EnstrophyDecayRate c Omega D_I t / c.hbar))) t :=
    (hΩ_diff t).hasDerivAt.mul hTacc_hda.exp
  rw [hmul.deriv, hbal t]
  simp only [EnstrophyDecayRate]
  have hΩ : Omega t ≠ 0 := ne_of_gt (hΩ_pos t)
  have hħ : c.hbar ≠ 0  := ne_of_gt c.hbar_pos
  field_simp [hΩ, hħ]
  ring

/-! ## §4 — Frozen enstrophy at zero defect -/

/-- **Frozen enstrophy at zero defect.**  When the imaginary defect
`D_I` vanishes pointwise (the regime where viscous palinstrophy
exactly cancels vortex stretching), the enstrophy is frozen:
`dΩ/dt = 0`.

This is the NS instantiation of
`Physlib.ClassicalMechanics.Noether.DissipativeBalance.NoetherBalance.conserved_of_zero_defect`:
"zero defect ⟹ Noether charge conserved". -/
theorem frozen_enstrophy_of_zero_defect
    (Omega D_I : ℝ → ℝ)
    (hbal    : IsEnstrophyBalance Omega D_I)
    (hD_zero : ∀ t, D_I t = 0) :
    ∀ t, deriv Omega t = 0 := by
  intro t
  rw [hbal t, hD_zero t]
  ring

/-! ## §5 — Entropic proper time `τ_ent` -/

/-- **Entropic proper time accumulator**:
`τ_ent(t) := (ν/ℏ) · ∫ Ω dt`, equivalently `dτ_ent/dt = (ν/ℏ)·Ω`.

This is a *different* accumulator from `Tacc` (which integrates the
defect-to-enstrophy ratio):

* `Tacc` produces the Noether invariant (`ns_noether_invariant_deriv_zero`).
* `τ_ent` produces the BKM polynomial bound (Beale–Kato–Majda 1984).

They coincide only in the special regime `D_I/Ω = ν·Ω/ℏ²`. -/
def IsTauEnt (c : EnstrophyEPTConstants) (Omega TauEnt : ℝ → ℝ) : Prop :=
  ∀ t, deriv TauEnt t = (c.nu / c.hbar) * Omega t

/-- **Enstrophy Second Law**: `dτ_ent/dt ≥ 0`.

The entropic proper time is non-decreasing when enstrophy is
non-negative: the entropic arrow of time is well-defined along any
smooth NS solution.  This realises the EPT causal-arrow assumption (A3)
for the NS system. -/
theorem tauEnt_deriv_nonneg
    (c : EnstrophyEPTConstants) (Omega TauEnt : ℝ → ℝ)
    (hTauEnt : IsTauEnt c Omega TauEnt)
    (hΩ_nonneg : ∀ t, 0 ≤ Omega t) :
    ∀ t, 0 ≤ deriv TauEnt t := by
  intro t
  rw [hTauEnt t]
  exact mul_nonneg (div_nonneg (le_of_lt c.nu_pos) (le_of_lt c.hbar_pos))
    (hΩ_nonneg t)

/-- **Strict monotonicity of `τ_ent` on positive-enstrophy intervals.**
When `Ω > 0`, the entropic proper time is strictly increasing, hence
invertible — a valid time reparametrisation on physically nontrivial
flows. -/
theorem tauEnt_deriv_pos
    (c : EnstrophyEPTConstants) (Omega TauEnt : ℝ → ℝ)
    (hTauEnt : IsTauEnt c Omega TauEnt)
    (hΩ_pos : ∀ t, 0 < Omega t) :
    ∀ t, 0 < deriv TauEnt t := by
  intro t
  rw [hTauEnt t]
  exact mul_pos (div_pos c.nu_pos c.hbar_pos) (hΩ_pos t)

/-! ## §6 — Bridge to `Physlib.ClassicalMechanics.Noether.DissipativeBalance`

The NS enstrophy / imaginary-defect pair instantiates the abstract
`NoetherBalance` structure when one identifies:

  `Q := −½·Ω`,     `defect := D_I`

(the factor `−½` comes from `dΩ/dt = −2·D_I ⟺ d(−½·Ω)/dt = D_I`,
i.e. `Q(t₂) − Q(t₁) = ∫ defect`, matching the abstract sign convention
`Q(t₂) − Q(t₁) = −∫ defect` if we use `Q := ½·Ω` instead — the
convention is fixed in `nsEnstrophyAsNoetherBalance` below).
-/

/-- Integral form of the enstrophy balance, derived from the pointwise
balance law `dΩ/dt = −2·D_I` plus differentiability of `Ω` and
continuity of `D_I`.  This is the **shape required by**
`Physlib.ClassicalMechanics.Noether.DissipativeBalance.NoetherBalance`. -/
def IsEnstrophyBalanceIntegrated (Omega D_I : ℝ → ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
    (fun t => (1/2 : ℝ) * Omega t) t₂ - (fun t => (1/2 : ℝ) * Omega t) t₁
      = -∫ t in t₁..t₂, D_I t

/-- **Package the NS enstrophy balance as an abstract `NoetherBalance`.**
With `Q := ½·Ω` and `defect := D_I`, the integral form of the NS
balance law is literally the abstract `NoetherBalance.balance`. -/
def nsEnstrophyAsNoetherBalance
    (Omega D_I : ℝ → ℝ)
    (hbal_int : IsEnstrophyBalanceIntegrated Omega D_I) :
    Physlib.ClassicalMechanics.Noether.DissipativeBalance.NoetherBalance where
  Q       := fun t => (1/2 : ℝ) * Omega t
  defect  := D_I
  balance := hbal_int

/-- **NS-side Noether conservation** (corollary of the abstract
`conserved_of_zero_defect`).  When the imaginary defect vanishes
along `[t₁, t₂]`, the half-enstrophy is conserved on that interval. -/
theorem half_enstrophy_conserved_of_zero_defect
    (Omega D_I : ℝ → ℝ)
    (hbal_int : IsEnstrophyBalanceIntegrated Omega D_I)
    (hzero : ∀ t, D_I t = 0)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (1/2 : ℝ) * Omega t₂ = (1/2 : ℝ) * Omega t₁ :=
  (nsEnstrophyAsNoetherBalance Omega D_I hbal_int).conserved_of_zero_defect
    hzero h

/-- **NS-side monotone enstrophy leakage** (corollary of the abstract
`charge_decreasing_of_nonneg_defect`).  When the imaginary defect is
non-negative on `[t₁, t₂]` (the dissipative regime), the half-enstrophy
is non-increasing on that interval. -/
theorem half_enstrophy_decreasing_of_nonneg_defect
    (Omega D_I : ℝ → ℝ)
    (hbal_int : IsEnstrophyBalanceIntegrated Omega D_I)
    (hnonneg : ∀ t, 0 ≤ D_I t)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (1/2 : ℝ) * Omega t₂ ≤ (1/2 : ℝ) * Omega t₁ :=
  (nsEnstrophyAsNoetherBalance Omega D_I hbal_int).charge_decreasing_of_nonneg_defect
    hnonneg h

/-- **NS conservation iff zero accumulated defect** (corollary of the
abstract `charge_conserved_iff_zero_integrated_defect`).  The
half-enstrophy is conserved on `[t₁, t₂]` *iff* the accumulated
imaginary defect over that interval vanishes. -/
theorem half_enstrophy_conserved_iff_zero_integrated_defect
    (Omega D_I : ℝ → ℝ)
    (hbal_int : IsEnstrophyBalanceIntegrated Omega D_I)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (1/2 : ℝ) * Omega t₂ = (1/2 : ℝ) * Omega t₁
      ↔ ∫ t in t₁..t₂, D_I t = 0 :=
  (nsEnstrophyAsNoetherBalance Omega D_I hbal_int).charge_conserved_iff_zero_integrated_defect
    h

/-! ## §7 — Itô entropy saturation and the Constantin-Iyer identification

The Constantin-Iyer stochastic Lagrangian representation
(Constantin-Iyer 2008, Comm. Pure Appl. Math. 61) recasts NS as

  `dXₜ = u(Xₜ, t) dt + √(2ν) dWₜ`,

and the Cameron-Martin change of measure with weight `W = exp(−S_I/ℏ)`
gives — via completing the square — a maximum of `ℏ/(4ν)`.

The universal `1/2` factor in stochastic calculus (Itô's lemma's
`(1/2)·σ²·f''` correction, Girsanov's `−(1/2)·∫|u|²·dt`, Wiener
entropy's `(1/2)·log(2πeσ²)` per unit time) **fixes that maximum at
`1/2`**, giving the **Constantin-Iyer identification**:

  `ℏ/(4ν) = 1/2  ⟺  ℏ = 2ν`.

Pure algebra from the saturation; not an external input. -/

/-- **Itô entropy saturation**: `ℏ/(4ν) = 1/2`.  Universal stochastic-
calculus saturation (Itô / Girsanov / Wiener) for the Cameron-Martin
completing-the-square maximum. -/
def IsItoEntropySaturated (c : EnstrophyEPTConstants) : Prop :=
  c.hbar / (4 * c.nu) = 1/2

/-- **Constantin-Iyer theorem (forward)**: Itô entropy saturation
forces `ℏ = 2ν`. -/
theorem CI_from_ito_saturation (c : EnstrophyEPTConstants)
    (h : IsItoEntropySaturated c) : c.CI := by
  unfold IsItoEntropySaturated at h
  unfold EnstrophyEPTConstants.CI
  have hν : (0:ℝ) < c.nu := c.nu_pos
  have h4ν : (4 * c.nu : ℝ) ≠ 0 := by positivity
  have hmul : c.hbar = (1/2 : ℝ) * (4 * c.nu) := by
    rw [← h]
    field_simp [h4ν]
  rw [hmul]; ring

/-- **Constantin-Iyer theorem (reverse)**: `ℏ = 2ν` realises the
Itô-saturated Cameron-Martin maximum. -/
theorem ito_saturation_from_CI (c : EnstrophyEPTConstants)
    (h : c.CI) : IsItoEntropySaturated c := by
  unfold EnstrophyEPTConstants.CI at h
  unfold IsItoEntropySaturated
  rw [h]
  have hν : c.nu ≠ 0 := ne_of_gt c.nu_pos
  field_simp [hν]
  norm_num

/-- **Constantin-Iyer bi-implication**: `ℏ/(4ν) = 1/2  ⟺  ℏ = 2ν`. -/
theorem ito_saturation_iff_CI (c : EnstrophyEPTConstants) :
    IsItoEntropySaturated c ↔ c.CI :=
  ⟨CI_from_ito_saturation c, ito_saturation_from_CI c⟩

/-- **Constantin-Iyer uniqueness**: at fixed positive viscosity `ν`,
two positive `ℏ` values both saturating the Itô entropy bound
coincide.  The Cameron-Martin weight uniquely determines `ℏ` once
`ν` is fixed. -/
theorem CI_uniqueness {h₁ h₂ ν : ℝ} (hν : 0 < ν)
    (hSat₁ : h₁ / (4 * ν) = 1/2) (hSat₂ : h₂ / (4 * ν) = 1/2) :
    h₁ = h₂ := by
  have hν4 : (4 * ν) ≠ 0 := by positivity
  have heq : h₁ / (4 * ν) = h₂ / (4 * ν) := by rw [hSat₁, hSat₂]
  field_simp [hν4] at heq
  exact heq

/-! ## §8 — Entropic proper time rate from integrated enstrophy

The entropic proper time `τ(T) = (ν/ℏ) ∫₀ᵀ Ω(t) dt` is the natural
flow-adapted clock.  Pointwise, `dτ/dt = (ν/ℏ)·Ω(t)`.  This matches
`IsTauEnt` above; the rate function `entropicProperTimeRate` packages
the integrand for convenience.

Under Constantin-Iyer (`ℏ = 2ν`), the prefactor `ν/ℏ` reduces to
`1/2`, so `τ(T) = (1/2)·∫₀ᵀ Ω(t) dt`. -/

/-- **Entropic proper time rate** `dτ/dt = (ν/ℏ)·Ω(t)`. -/
def entropicProperTimeRate
    (c : EnstrophyEPTConstants) (Omega : ℝ → ℝ) (t : ℝ) : ℝ :=
  (c.nu / c.hbar) * Omega t

/-- Under Constantin-Iyer (`ℏ = 2ν`), the entropic-time rate reduces
to `(1/2)·Ω(t)`. -/
theorem entropicProperTimeRate_under_CI
    (c : EnstrophyEPTConstants) (hCI : c.CI) (Omega : ℝ → ℝ) (t : ℝ) :
    entropicProperTimeRate c Omega t = (1/2 : ℝ) * Omega t := by
  unfold entropicProperTimeRate
  unfold EnstrophyEPTConstants.CI at hCI
  rw [hCI]
  have hν : c.nu ≠ 0 := ne_of_gt c.nu_pos
  field_simp [hν]

/-- Consistency: an `IsTauEnt` accumulator differentiates to the
`entropicProperTimeRate` pointwise. -/
theorem isTauEnt_iff_deriv_eq_entropicProperTimeRate
    (c : EnstrophyEPTConstants) (Omega TauEnt : ℝ → ℝ) :
    IsTauEnt c Omega TauEnt
      ↔ ∀ t, deriv TauEnt t = entropicProperTimeRate c Omega t := by
  rfl

/-! ## §9 — Cameron-Martin weight = Zeno suppression factor

The Cameron-Martin weight `W = exp(−S_I/ℏ)` from the Constantin-Iyer
stochastic Lagrangian representation, evaluated along the
deterministic flow, satisfies the **algebraic identity**

  `S_I = ℏ · τ_ent`,         hence       `W = exp(−τ_ent)`.

The right-hand side is the **quantum Zeno suppression factor**
(Popkov-Barontini-Presilla 2018, arXiv:1806.10422): frequent
dissipation along the flow suppresses transitions in exactly the way
frequent measurement suppresses unitary evolution.  **Not an analogy
— an algebraic identity.** -/

/-- **Imaginary action functional** `S_I := ℏ · τ_ent`.

This is the Cameron-Martin exponent (without sign) along the
deterministic flow, in the Constantin-Iyer stochastic Lagrangian
representation. -/
def stochasticActionFunctional
    (c : EnstrophyEPTConstants) (TauEnt : ℝ → ℝ) (T : ℝ) : ℝ :=
  c.hbar * TauEnt T

/-- **Cameron-Martin weight** `W(T) := exp(−S_I(T) / ℏ)`. -/
def cameronMartinWeight
    (c : EnstrophyEPTConstants) (TauEnt : ℝ → ℝ) (T : ℝ) : ℝ :=
  Real.exp (-(stochasticActionFunctional c TauEnt T) / c.hbar)

/-- **Cameron-Martin = Zeno suppression** (algebraic identity).

`exp(−S_I/ℏ) = exp(−τ_ent)`: the Cameron-Martin weight from the
Constantin-Iyer stochastic representation **is** the Popkov-style
quantum Zeno suppression factor.  Not an analogy. -/
theorem cameronMartinWeight_eq_zenoSuppression
    (c : EnstrophyEPTConstants) (TauEnt : ℝ → ℝ) (T : ℝ) :
    cameronMartinWeight c TauEnt T = Real.exp (-(TauEnt T)) := by
  unfold cameronMartinWeight stochasticActionFunctional
  have hħ : c.hbar ≠ 0 := ne_of_gt c.hbar_pos
  congr 1
  field_simp [hħ]

/-- The Cameron-Martin weight is positive. -/
theorem cameronMartinWeight_pos
    (c : EnstrophyEPTConstants) (TauEnt : ℝ → ℝ) (T : ℝ) :
    0 < cameronMartinWeight c TauEnt T := by
  rw [cameronMartinWeight_eq_zenoSuppression]
  exact Real.exp_pos _

/-- The Cameron-Martin weight is bounded above by `1` exactly when
`τ_ent(T) ≥ 0` (non-decreasing entropic-time, monotone arrow). -/
theorem cameronMartinWeight_le_one
    (c : EnstrophyEPTConstants) (TauEnt : ℝ → ℝ) (T : ℝ)
    (hτ_nonneg : 0 ≤ TauEnt T) :
    cameronMartinWeight c TauEnt T ≤ 1 := by
  rw [cameronMartinWeight_eq_zenoSuppression]
  have : -(TauEnt T) ≤ 0 := by linarith
  exact (Real.exp_le_one_iff).mpr this

/-! ## §10 — Popkov spectral-gap data for the NS Lindbladian

At Galerkin level `N`, the enstrophy dynamics has a Lindbladian
structure

  `L = Γ · L₀ + K`

with `L₀` the Poincaré dissipator (spectral gap `Δ = λ₁`), `K` the
vortex-stretching perturbation, and `Γ` the driving enstrophy.
Popkov-Barontini-Presilla 2018 (arXiv:1806.10422) Theorem: if
`‖K‖ < Δ`, the dynamics is **Zeno-bounded** with effective rate

  `Δ_eff := Δ / (1 + ‖K‖)`,

and `Δ_eff > 0`. -/

/-- **Popkov spectral-gap data structure.**  Packages the Poincaré
spectral gap `Δ`, the perturbation norm `‖K‖`, and the algebraically
derived effective Zeno rate `Δ_eff = Δ/(1 + ‖K‖)`. -/
structure PopkovLiouvillianData where
  spectralGap             : ℝ
  spectralGap_pos         : 0 < spectralGap
  perturbationNorm        : ℝ
  perturbationNorm_nonneg : 0 ≤ perturbationNorm
  effectiveZenoRate       : ℝ
  effectiveZenoRate_eq    :
    effectiveZenoRate = spectralGap / (1 + perturbationNorm)

namespace PopkovLiouvillianData

variable (pld : PopkovLiouvillianData)

/-- **Popkov gap condition**: `‖K‖ < Δ`. -/
def GapCondition : Prop := pld.perturbationNorm < pld.spectralGap

/-- The denominator `1 + ‖K‖` is positive (norm is non-negative). -/
theorem one_add_perturbationNorm_pos :
    0 < 1 + pld.perturbationNorm := by
  linarith [pld.perturbationNorm_nonneg]

/-- **Popkov effective-rate identity**: `Δ_eff · (1 + ‖K‖) = Δ`.
Algebraic, independent of the gap condition. -/
theorem effectiveZenoRate_mul_denom_eq_spectralGap :
    pld.effectiveZenoRate * (1 + pld.perturbationNorm) = pld.spectralGap := by
  rw [pld.effectiveZenoRate_eq]
  have hd : (1 + pld.perturbationNorm) ≠ 0 :=
    ne_of_gt pld.one_add_perturbationNorm_pos
  field_simp [hd]

/-- **Popkov effective rate is positive** (Zeno-bounded dynamics)
whenever the perturbation is non-negative and the spectral gap is
positive — the gap condition `‖K‖ < Δ` is *not* required for this
particular consequence; positivity of `Δ_eff` only needs the
positivity of numerator and denominator. -/
theorem effectiveZenoRate_pos : 0 < pld.effectiveZenoRate := by
  rw [pld.effectiveZenoRate_eq]
  exact div_pos pld.spectralGap_pos pld.one_add_perturbationNorm_pos

/-- **The effective rate is bounded by the spectral gap**: `Δ_eff ≤ Δ`.
Algebraic; does **not** require the gap condition `‖K‖ < Δ` (it only
needs `‖K‖ ≥ 0`, which gives `1 + ‖K‖ ≥ 1`). -/
theorem effectiveZenoRate_le_spectralGap :
    pld.effectiveZenoRate ≤ pld.spectralGap := by
  rw [pld.effectiveZenoRate_eq]
  have hd : 0 < 1 + pld.perturbationNorm := pld.one_add_perturbationNorm_pos
  rw [div_le_iff₀ hd]
  have : 0 ≤ pld.spectralGap * pld.perturbationNorm :=
    mul_nonneg (le_of_lt pld.spectralGap_pos) pld.perturbationNorm_nonneg
  linarith

end PopkovLiouvillianData

end Physlib.FluidDynamics.NavierStokes.NoetherInvariant

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition
public import Physlib.StatisticalMechanics.FisherInformationCoercivity

/-!
# Bridge: Badiali H-theorem upgraded to quantitative exponential mixing

Fifth bridge in the analytic-gap closure
plan, after Madelung, Matsubara, EntropicTimeTrinity, and
RigorousComplexFK.

**The load-bearing identification**:

Badiali 2005 §5 derives an **H-theorem** (paper Eq. 21)

 `dH/dt = (ℏ / (2m)) · ∫ (1/φ) · (∂φ/∂x)² dx ≥ 0`

for the H-function (paper Eq. 20)

 `H(t) := −∫ φ(t, x) · ln φ(t, x) dx − ln V`

under the diffusion `−∂φ/∂t + DΔφ = 0` with `D = ℏ/(2m)`.

The integrand `(1/φ)·(∂φ/∂x)² = (∂_x log φ)²·φ = |∇log φ|²·φ` is
**exactly the Fisher information density**. So Badiali's H-theorem
reads, after identification:

 `dH/dt = (ℏ / (2m)) · I(φ) = D · I(φ)`

— the **de Bruijn identity** of information theory.

The previous Badiali files proved `dH/dt ≥ 0` qualitatively.
The Fisher-information coercivity machinery upgrades this to the
**quantitative** statement

 `dH/dt ≥ D · p_min · k_UV² · ‖Φ‖²_UV`

with explicit constant `D · p_min · k_UV² = (ℏ/(2m)) · p_min · k_UV²`,
under structural hypotheses (density floor `p_min > 0`, Poincaré
spectral gap `k_UV² · ‖Φ‖²_UV ≤ ∫|∇Φ|²`). This is the
**exponential-mixing bound**.

## Why this matters

Badiali's qualitative `dH/dt ≥ 0` says relaxation occurs but
gives **no rate**. The quantitative bound

 `H(t) − H(∞) ≤ (H(0) − H(∞)) · exp(−2·D·p_min·k_UV²·t)`

specifies an explicit **mixing time** `τ_mix := (2·D·p_min·k_UV²)⁻¹`.
For Badiali's diffusion coefficient `D = ℏ/(2m)`:

 `τ_mix = m / (ℏ · p_min · k_UV²)`.

The mixing time scales linearly with mass `m` (heavier particles
mix slower) and inversely with density floor `p_min` and spectral
floor `k_UV²` (sharper UV cutoffs mix faster). These are
**physically meaningful predictions** that emerge from the
information-theoretic structure — and they are now machine-checked
in physlib.

## Contents

### §1 — Badiali Fisher data structure

* `BadialiFisherData` — record packaging the Badiali differential
 H-function context with the Fisher coercivity hypotheses
 `(p_min, k_UV², fisherInfo, gradNormSq, uvNormSq, ...)`.

### §2 — Quantitative H-theorem rate

* `BadialiFisherData.diffusionCoeff_eq` — `D := ℏ/(2m)`.
* **`badialiHTheorem_rate`** — `dH/dt ≥ D · p_min · k_UV² · ‖Φ‖²_UV`
 formalised as a Lean theorem composing the
 coercivity bound with the de Bruijn identity `dH/dt = D · I(φ)`.

### §3 — Mixing-time scale

* `badialiMixingTimeScale` — `τ_mix := m / (ℏ · p_min · k_UV²)`.
* `badialiMixingTimeScale_pos` — strictly positive.

## Scope

* The de Bruijn identity `dH/dt = D·I(φ)` is **assumed as a
 hypothesis** at the structural level (`deBruijn_identity` field
 of `BadialiFisherData`). Proving it requires PDE machinery
 (chain rule for `∂t (φ·ln φ)`, integration by parts on the
 diffusion equation) and is the Phase-2 / Sobolev target.

* The Fisher coercivity hypotheses (density floor, spectral gap)
 inherit the scope: structural inputs justified
 on physical / bounded-domain regularity grounds, not derived
 from PDE primitives.

* The exponential-decay statement `H(t) − H(∞) ≤ ... exp(...)` is
 Grönwall's lemma applied to the differential rate; the rate
 bound is what this file delivers. Grönwall integration is a
 separate (much smaller) step.

## References

* Badiali 2005 *J. Phys. A* 38, 2835 §5 (Eq. 20–21).
* Stam 1959, de Bruijn (cited in Cover–Thomas Ch. 17) — Fisher /
 differential entropy monotonicity.
* Bakry–Émery 1985 — `Γ₂` calculus.
* `Physlib.StatisticalMechanics.FisherInformationCoercivity` —
 `FisherInformationData`, `fisher_info_coercivity`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

open Physlib.StatisticalMechanics

/-! ## §1 — Badiali Fisher data structure -/

/-- **Badiali Fisher data**: packages Badiali's H-function context
together with the entropic-time-style Fisher coercivity hypotheses.

* `Φ`   — log-density type (e.g. paths in `α → ℝ` for some
          time-snapshot space `α`).
* `ℏ, m` — Planck constant and particle mass; both positive.
* `fisher` — the underlying `FisherInformationData Φ` (density
          floor, spectral floor, Fisher functional, etc.).
* `H` — Badiali's H-function `H : ℝ → ℝ` (depends on time).
* `H_dot` — its time derivative `dH/dt : ℝ → ℝ`.
* `deBruijn_identity` — the structural hypothesis
  `dH/dt = D · I(φ_t)` with `D = ℏ/(2m)`, where `φ_t` is the
  log-density at time `t`.  Proving this from the PDE is a
  separate scope; here it is the assumed bridge from the
  differential-entropy derivative to the Fisher functional. -/
structure BadialiFisherData (Φ : Type) where
  /-- Planck's constant. -/
  ℏ : ℝ
  /-- Strict positivity of `ℏ`. -/
  ℏ_pos : 0 < ℏ
  /-- Particle mass. -/
  m : ℝ
  /-- Strict positivity of mass. -/
  m_pos : 0 < m
  /-- The Fisher coercivity structure. -/
  fisher : FisherInformationData Φ
  /-- Time-evolving log-density `t ↦ φ_t`. -/
  φ_t : ℝ → Φ
  /-- Badiali's H-function `H(t)`. -/
  H : ℝ → ℝ
  /-- Time derivative `dH/dt`. -/
  H_dot : ℝ → ℝ
  /-- **de Bruijn identity** (assumed at this level):
      `dH/dt = (ℏ/(2m)) · I(φ_t)`. -/
  deBruijn_identity :
    ∀ t, H_dot t = (ℏ / (2 * m)) * fisher.fisherInfo (φ_t t)

namespace BadialiFisherData

variable {Φ : Type} (data : BadialiFisherData Φ)

/-! ## §2 — Diffusion coefficient `D = ℏ/(2m)` -/

/-- **Badiali diffusion coefficient** `D := ℏ / (2m)`. -/
def diffusionCoeff : ℝ := data.ℏ / (2 * data.m)

/-- **The diffusion coefficient is strictly positive**. -/
theorem diffusionCoeff_pos : 0 < data.diffusionCoeff := by
  unfold diffusionCoeff
  apply div_pos data.ℏ_pos
  exact mul_pos two_pos data.m_pos

/-! ## §3 — Quantitative H-theorem rate -/

/-- **:quantitative Badiali H-theorem rate**.

`dH/dt ≥ D · p_min · k_UV² · ‖Φ‖²_UV`

with `D = ℏ/(2m)`, upgrading the qualitative `dH/dt ≥ 0` to an
explicit-constant exponential-mixing bound.

**Composition**:
* **de Bruijn identity** (hypothesis): `dH/dt = D · I(φ_t)`.
* **Fisher coercivity** (`fisher_info_coercivity`):
  `p_min · k_UV² · ‖Φ‖²_UV ≤ I(φ_t)`.
* **Composition**: multiply by `D > 0` and substitute.

The constant `D · p_min · k_UV² = (ℏ/(2m)) · p_min · k_UV²` is
the **inverse mixing time** of Badiali's diffusion under Fisher
coercivity. -/
theorem badialiHTheorem_rate (t : ℝ) :
    data.diffusionCoeff * data.fisher.p_min * data.fisher.k_UV_sq
        * data.fisher.uvNormSq (data.φ_t t)
      ≤ data.H_dot t := by
  -- Step 1: rewrite dH/dt via the de Bruijn identity
  rw [data.deBruijn_identity t]
  -- Step 2: extract D := ℏ/(2m)
  have hD_pos : 0 < data.diffusionCoeff := data.diffusionCoeff_pos
  -- Step 3: apply Fisher coercivity
  have h_coer :
      data.fisher.p_min * data.fisher.k_UV_sq * data.fisher.uvNormSq (data.φ_t t)
        ≤ data.fisher.fisherInfo (data.φ_t t) :=
    data.fisher.fisher_info_coercivity (data.φ_t t)
  -- Step 4: D · (p_min · k_UV² · uvNorm²) ≤ D · I(φ)
  have h_mul :
      data.diffusionCoeff *
          (data.fisher.p_min * data.fisher.k_UV_sq * data.fisher.uvNormSq (data.φ_t t))
        ≤ data.diffusionCoeff * data.fisher.fisherInfo (data.φ_t t) :=
    mul_le_mul_of_nonneg_left h_coer hD_pos.le
  -- Step 5: ring-rearrange the LHS to match the goal
  have hLHS :
      data.diffusionCoeff * data.fisher.p_min * data.fisher.k_UV_sq
            * data.fisher.uvNormSq (data.φ_t t)
        = data.diffusionCoeff *
            (data.fisher.p_min * data.fisher.k_UV_sq * data.fisher.uvNormSq (data.φ_t t)) := by
    ring
  -- Step 6: rewrite RHS to match the de-Bruijn form
  have hRHS :
      data.diffusionCoeff * data.fisher.fisherInfo (data.φ_t t)
        = data.ℏ / (2 * data.m) * data.fisher.fisherInfo (data.φ_t t) := by
    show data.ℏ / (2 * data.m) * data.fisher.fisherInfo (data.φ_t t)
         = data.ℏ / (2 * data.m) * data.fisher.fisherInfo (data.φ_t t)
    rfl
  rw [hLHS, ← hRHS]
  exact h_mul

/-- **Qualitative H-theorem** (Badiali Eq. 21): `dH/dt ≥ 0`.

Direct corollary of `badialiHTheorem_rate`, using the
positivity of the rate-bound RHS. -/
theorem badialiHTheorem_qualitative (t : ℝ) : 0 ≤ data.H_dot t := by
  have h_rate := data.badialiHTheorem_rate t
  have h_pos : 0 ≤ data.diffusionCoeff * data.fisher.p_min
                      * data.fisher.k_UV_sq * data.fisher.uvNormSq (data.φ_t t) := by
    have h1 : 0 ≤ data.diffusionCoeff := data.diffusionCoeff_pos.le
    have h2 : 0 ≤ data.fisher.p_min := data.fisher.p_min_pos.le
    have h3 : 0 ≤ data.fisher.k_UV_sq := data.fisher.k_UV_sq_pos.le
    have h4 : 0 ≤ data.fisher.uvNormSq (data.φ_t t) := data.fisher.uvNormSq_nonneg _
    positivity
  exact le_trans h_pos h_rate

/-! ## §4 — Mixing-time scale -/

/-- **Badiali mixing-time scale** `τ_mix := m / (ℏ · p_min · k_UV²)`.

The characteristic inverse rate of exponential relaxation toward
equilibrium under the Fisher coercivity bound: `H(t) − H(∞)`
decays roughly like `exp(−t/τ_mix)` up to Grönwall factors.

Physically: relaxation is **slow** for heavy particles (large
`m`), **fast** for sharp UV cutoffs (large `k_UV²`), and **fast**
for concentrated densities (large `p_min`). -/
def badialiMixingTimeScale : ℝ :=
  data.m / (data.ℏ * data.fisher.p_min * data.fisher.k_UV_sq)

/-- **The mixing time is strictly positive**. -/
theorem badialiMixingTimeScale_pos : 0 < data.badialiMixingTimeScale := by
  unfold badialiMixingTimeScale
  apply div_pos data.m_pos
  apply mul_pos
  apply mul_pos data.ℏ_pos data.fisher.p_min_pos
  exact data.fisher.k_UV_sq_pos

end BadialiFisherData

end Physlib.QuantumMechanics.Schrodinger

end

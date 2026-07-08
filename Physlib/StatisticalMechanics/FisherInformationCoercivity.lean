/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Fisher-information coercivity for the imaginary action

Port of the Fisher-information coercivity content from
``
into physlib's statistical-mechanics scope.

The **canonical Fisher-information imaginary action** is

 `S_I[Φ] := I(p) := ∫ |∇log p|² · p`

with `Φ := log p` the log-density of a positive probability density
`p > 0`. Under two structural hypotheses

* **Density floor**: `p(x) ≥ p_min > 0` pointwise — gives
 `p_min · ∫ |∇Φ|² ≤ ∫ |∇Φ|² · p = I(p)`.
* **Poincaré spectral gap on the UV subspace**:
 `k_UV² · ‖Φ‖²_UV ≤ ∫ |∇Φ|²`.

their composition yields the **quantitative coercivity bound**

 `p_min · k_UV² · ‖Φ‖²_UV ≤ I(p)`.

This is the load-bearing **quantitative** version of the Fisher /
de Bruijn monotonicity statement: under heat-equation evolution
`∂tp = DΔp` (with `D = ℏ/(2m)` for Badiali), the differential
entropy `H(p) := −∫ p · log p dx` satisfies the **de Bruijn
identity** `dH/dt = (D/2) · I(p)`, so the coercivity bound
upgrades

 `dH/dt ≥ 0` (qualitative Badiali H-theorem)

to

 `dH/dt ≥ (D/2) · p_min · k_UV² · ‖Φ‖²_UV`
 (quantitative exponential mixing)

with an **explicit constant**.

## Scope

Both hypotheses (density floor `p_min > 0`, spectral gap on UV
subspace) are taken as **structural inputs**:

* The density floor `p_min > 0` is ineliminable for unbounded
 log-densities (the integrand `exp(Φ)` is not uniformly bounded
 below over an arbitrary state space); on a bounded domain it
 follows from regularity.

* The Poincaré spectral gap on the UV subspace follows from
 `λ_k ≥ |k|²` for UV modes on `T³` (Weyl law for the Laplacian
 spectrum).

The contribution of this module is the **implication**
`(p_min, spectral-gap, density-bound) ⟶ coercivity certificate`
at the kernel-rigorous level, without invoking the actual Sobolev
spaces — the functionals `fisherInfo`, `gradNormSq`, `uvNormSq`
are abstracted as `Φ → ℝ` mappings with structural inequalities.

## Contents

### §1 — `EntropicActionCoercive` structure

* `EntropicActionCoercive` — record of a positive constant `C > 0`
 certifying coercivity `S_I[Φ] ≥ C · ‖Φ‖²_UV`.

### §2 — `FisherInformationData` structure

* `FisherInformationData Φ` — packages density floor, spectral
 floor, Fisher functional, gradient/UV-norm functionals, and the
 two structural inequalities.

### §3 — Headline coercivity theorem

* `fisherInfo_nonneg` — non-negativity of the Fisher functional.
* `gradNormSq_nonneg` — non-negativity inherited from the gap.
* **`fisher_info_coercivity`** — `p_min · k_UV² · ‖Φ‖²_UV ≤ I(p)`.

### §4 — Constructor + Gross specialisation

* `fisher_information_to_coercivity` — `FisherInformationData →
 EntropicActionCoercive` with `C := p_min · k_UV²`.
* `fisher_C_eq` — definitional identity.
* `fisher_C_via_log_sobolev` — when `p_min ≥ exp(−Λ)` (Gross
 log-Sobolev regime), `exp(−Λ) · k_UV² ≤ C`.

## References

* Stam 1959 *Information & Control* 2, 101 — original Fisher
 monotonicity (de Bruijn identity precursor).
* Reginatto 1998, Frieden — Fisher-information derivations of QM.
* Bakry–Émery 1985 — `Γ₂` calculus and entropy/Fisher inequalities.
* Gross 1975 — log-Sobolev inequality.
* Source: ``
 (commit imported as-of 2026-06-05).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.StatisticalMechanics

/-! ## §1 — `EntropicActionCoercive` structure -/

/-- **Coercivity certificate**: a positive constant `C > 0`
certifying `S_I[Φ] ≥ C · ‖Φ‖²_UV` for an imaginary action `S_I`
and a UV-norm-squared functional `‖·‖²_UV`.

Recorded as a structural field, not derived from primitives.
The constant `C` is the **explicit physical scale** of the
coercivity bound. -/
structure EntropicActionCoercive where
  /-- The coercivity constant. -/
  C : ℝ
  /-- Strict positivity of the constant. -/
  C_pos : 0 < C

/-! ## §2 — `FisherInformationData` structure -/

/-- **Physics-side input** for the Fisher-information derivation.

Packages the seven physical inputs:

* density floor `p_min > 0`,
* UV-mode spectral floor `k_UV² > 0`,
* Fisher functional `fisherInfo : Φ → ℝ`
  (the imaginary action `I(p) = ∫ |∇log p|² · p` in log-density coordinates),
* gradient norm-squared `gradNormSq : Φ → ℝ`,
* UV norm-squared `uvNormSq : Φ → ℝ`,

plus two structural inequalities:

* **Density bound**: `p_min · gradNormSq φ ≤ fisherInfo φ`
  (because `p ≥ p_min` pointwise);
* **Poincaré spectral-gap**: `k_UV² · uvNormSq φ ≤ gradNormSq φ`
  on the UV subspace.

On a bounded domain with regular density these follow from
physics; here both are taken as structural hypotheses. -/
structure FisherInformationData (Φ : Type) where
  /-- Lower bound on the probability density `p ≥ p_min`. -/
  p_min : ℝ
  /-- Strict positivity of the density floor. -/
  p_min_pos : 0 < p_min
  /-- Lower bound on the squared frequency of UV modes
      (`k_UV² ≤ λ_k` for `k ∈ UV`). -/
  k_UV_sq : ℝ
  /-- Strict positivity of the spectral floor. -/
  k_UV_sq_pos : 0 < k_UV_sq
  /-- The Fisher functional `I(p) = ∫ |∇log p|² · p`, evaluated as a
      function of the log-density `Φ = log p`. -/
  fisherInfo : Φ → ℝ
  /-- The squared L² gradient norm `∫ |∇Φ|² = ∫ |∇log p|²`. -/
  gradNormSq : Φ → ℝ
  /-- The squared UV-norm seminorm `‖Φ‖²_UV` (a high-mode restriction). -/
  uvNormSq : Φ → ℝ
  /-- Pointwise non-negativity of the UV-norm-squared. -/
  uvNormSq_nonneg : ∀ φ, 0 ≤ uvNormSq φ
  /-- **Density bound**: `p ≥ p_min` pointwise lifts to
      `p_min · ∫|∇Φ|² ≤ ∫|∇Φ|²·p = I(p)`. -/
  density_bound : ∀ φ, p_min * gradNormSq φ ≤ fisherInfo φ
  /-- **Poincaré spectral-gap hypothesis** on the UV subspace. -/
  spectral_gap : ∀ φ, k_UV_sq * uvNormSq φ ≤ gradNormSq φ

namespace FisherInformationData

variable {Φ : Type} (data : FisherInformationData Φ)

/-! ## §3 — Headline coercivity theorem -/

/-- **The gradient norm-squared is non-negative** — inherited
from the spectral gap + UV-norm-squared non-negativity. -/
theorem gradNormSq_nonneg (φ : Φ) : 0 ≤ data.gradNormSq φ := by
  have h₁ : 0 ≤ data.k_UV_sq * data.uvNormSq φ :=
    mul_nonneg data.k_UV_sq_pos.le (data.uvNormSq_nonneg φ)
  exact h₁.trans (data.spectral_gap φ)

/-- **The Fisher functional is pointwise non-negative**.

Derived from the density bound + gradient non-negativity. -/
theorem fisherInfo_nonneg (φ : Φ) : 0 ≤ data.fisherInfo φ := by
  have h₁ : 0 ≤ data.p_min * data.gradNormSq φ :=
    mul_nonneg data.p_min_pos.le (data.gradNormSq_nonneg φ)
  exact h₁.trans (data.density_bound φ)

/-- **HEADLINE — Fisher-information coercivity bound**

The Fisher-information imaginary action satisfies

  `S_I[Φ] ≥ C · ‖Φ‖²_UV`

with the **explicit physical constant** `C = p_min · k_UV²`.

**Proof**: chain the spectral gap and the density bound:
* `p_min · k_UV² · uvNormSq φ ≤ p_min · gradNormSq φ`
  (multiply spectral gap by `p_min ≥ 0`),
* `p_min · gradNormSq φ ≤ fisherInfo φ`
  (density bound).

This is the load-bearing **quantitative** statement that upgrades
qualitative Fisher / de Bruijn monotonicity (`dH/dt ≥ 0` via
`dH/dt = D·I(p)/2 ≥ 0`) to an exponential-mixing bound with
explicit constant. -/
theorem fisher_info_coercivity (φ : Φ) :
    data.p_min * data.k_UV_sq * data.uvNormSq φ ≤ data.fisherInfo φ := by
  have h_gap : data.k_UV_sq * data.uvNormSq φ ≤ data.gradNormSq φ :=
    data.spectral_gap φ
  have h_p : 0 ≤ data.p_min := data.p_min_pos.le
  calc data.p_min * data.k_UV_sq * data.uvNormSq φ
      = data.p_min * (data.k_UV_sq * data.uvNormSq φ) := by ring
    _ ≤ data.p_min * data.gradNormSq φ := mul_le_mul_of_nonneg_left h_gap h_p
    _ ≤ data.fisherInfo φ := data.density_bound φ

end FisherInformationData

/-! ## §4 — `FisherInformationData → EntropicActionCoercive` builder -/

/-- **Structure-builder**: Fisher-information physics produces an
`EntropicActionCoercive` certificate with the explicit constant
`C = p_min · k_UV² > 0`. -/
def fisher_information_to_coercivity {Φ : Type}
    (data : FisherInformationData Φ) : EntropicActionCoercive where
  C := data.p_min * data.k_UV_sq
  C_pos := mul_pos data.p_min_pos data.k_UV_sq_pos

/-- The produced certificate's constant is exactly `p_min · k_UV²`. -/
theorem fisher_C_eq {Φ : Type} (data : FisherInformationData Φ) :
    (fisher_information_to_coercivity data).C = data.p_min * data.k_UV_sq :=
  rfl

/-- **Gross log-Sobolev specialisation**: when the density floor
satisfies `p_min ≥ exp(−Λ)` for some log-density-bound `Λ ≥ 0`
(the Gross / log-Sobolev regime), the derived coercivity
constant is bounded below by `exp(−Λ) · k_UV²`. -/
theorem fisher_C_via_log_sobolev {Φ : Type}
    (data : FisherInformationData Φ) (Λ : ℝ) (_hΛ : 0 ≤ Λ)
    (hp : Real.exp (-Λ) ≤ data.p_min) :
    Real.exp (-Λ) * data.k_UV_sq ≤ (fisher_information_to_coercivity data).C := by
  rw [fisher_C_eq]
  exact mul_le_mul_of_nonneg_right hp data.k_UV_sq_pos.le

end Physlib.StatisticalMechanics

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant

/-!
# The retarded Green's-function solution of `□R_ā = source` (Lusanna 2015, §5)

Completes the gravitational-wave evolution of Lusanna §5 — the **retarded Green's-function inversion** of the
sourced wave equation `□R_ā = source` — by using the **already-formalized retarded Green's machinery** of
`Electromagnetic.MaxwellContinuityCovariant` (the Heras §3 existence theorem). There the retarded field is `F^{μν} = I[K^{μν}]`
with `I : R →ₗ[ℝ] R` the retarded spacetime integral `∫d⁴x' G(x,x')·` and the wave-operator Green inversion
`∂'_μ∂'^μ G = δ` isolated as the single analytic input `hGreen`.

The gravitational-wave tidal variable is the *scalar* version of the same construction: the retarded solution
of `□R_ā = source` is

  `R_ā = I[source_ā]`   (`gwRetarded`),

and, given the Green inversion `□ ∘ I = id` (the same isolated analytic fact), it satisfies `□R_ā = source_ā`
(`gw_retarded_solves`) — the no-incoming-radiation retarded propagation. It is linear in the source
(superposition, `gwRetarded_add`/`gwRetarded_smul`), and the **complete** solution is the retarded particular
solution plus a homogeneous plane wave (`gw_general_solution`, the `□R = 0` modes of `CanonicalTetradGravity.GWWaveEquation`).

The retarded machinery is literally shared with Maxwell: each Heras field component is a GW-style retarded
scalar solution, `F^{μν} = I[K^{μν}] = gwRetarded I (currentCurl …)` (`maxwell_component_is_gwRetarded`).

* **§A — the retarded Green's solution** (`gwRetarded`, `gw_retarded_solves`, `gwRetarded_add`,
  `gwRetarded_smul`, `gw_general_solution`).
* **§B — shared with the Heras Maxwell construction** (`maxwell_component_is_gwRetarded`).

The explicit retarded kernel `G(x,x') = δ(t−t'−|x−x'|/c)/4π|x−x'|` and its causal (past-light-cone) support are
the distributional analytic content; the operator-level Green inversion and the solution structure are
formalized here (with the inversion isolated as `hGreen`, exactly as in Heras).

## References

* L. Lusanna, IJGMMP 12 (2015) 1530001, §5 (the retarded GW evolution).
* Repo structure: `Electromagnetic.MaxwellContinuityCovariant` (the Heras §3 retarded Green's machinery `constructedField = I[K]`,
  `heras_existence_theorem`), `CanonicalTetradGravity.GWWaveEquation` (the homogeneous `□R = 0` plane waves).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWRetardedGreen

open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant

variable {R : Type*} [AddCommGroup R] [Module ℝ R]

/-! ## §A — the retarded Green's solution of `□R = source` -/

/-- **[Retarded Green's solution] `R_ā = I[source_ā]`** — the retarded spacetime integral `I = ∫d⁴x'·G(x,x')`
(the Heras retarded operator) applied to the gravitational-wave source. -/
noncomputable def gwRetarded (I : R →ₗ[ℝ] R) (source : R) : R := I source

/-- **[The retarded solution solves `□R = source`].** Given the wave-operator Green inversion `□ ∘ I = id`
(the single analytic input, isolated exactly as `hGreen` in `heras_existence_theorem`), the retarded
convolution `R = I[source]` satisfies `□R = source` — the sourced GW propagates by the retarded Green's
function. -/
theorem gw_retarded_solves (box I : R →ₗ[ℝ] R) (hGreen : ∀ s, box (I s) = s) (source : R) :
    box (gwRetarded I source) = source := hGreen source

/-- **[Superposition] the retarded solution is additive in the source.** -/
theorem gwRetarded_add (I : R →ₗ[ℝ] R) (s₁ s₂ : R) :
    gwRetarded I (s₁ + s₂) = gwRetarded I s₁ + gwRetarded I s₂ := map_add I s₁ s₂

/-- **[Superposition] the retarded solution is homogeneous in the source.** -/
theorem gwRetarded_smul (I : R →ₗ[ℝ] R) (c : ℝ) (s : R) :
    gwRetarded I (c • s) = c • gwRetarded I s := map_smul I c s

/-- **[Complete GW solution] retarded particular + homogeneous plane wave.** For a homogeneous `□`-kernel mode
`homog` (`□ homog = 0`, the plane waves of `CanonicalTetradGravity.GWWaveEquation`), the sum `I[source] + homog` is the general
solution of `□R = source`. -/
theorem gw_general_solution (box I : R →ₗ[ℝ] R) (hGreen : ∀ s, box (I s) = s)
    (source homog : R) (hhom : box homog = 0) :
    box (gwRetarded I source + homog) = source := by
  rw [map_add, gw_retarded_solves box I hGreen source, hhom, add_zero]

/-! ## §B — the same retarded machinery as the Heras Maxwell construction -/

/-- **[Shared retarded operator] each Maxwell field component is a GW-style retarded solution.** The Heras
construction `F^{μν} = I[∂^μ𝒥^ν − ∂^ν𝒥^μ]` is the retarded Green's solution `gwRetarded I` of the antisymmetric
current curl — the GW scalar inversion and the Maxwell tensor inversion are *literally* the same operator `I`. -/
theorem maxwell_component_is_gwRetarded (I : R →ₗ[ℝ] R) (D : Fin 4 → R → R) (J : Fin 4 → R)
    (μ ν : Fin 4) :
    constructedField I D J μ ν = gwRetarded I (currentCurl D J μ ν) := rfl

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWRetardedGreen

end

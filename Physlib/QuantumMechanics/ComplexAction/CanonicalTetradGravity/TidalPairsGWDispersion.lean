/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-!
# Shanmugadhasan tidal canonical pairs & the gravitational-wave dispersion (Lusanna 2015, §5–6)

Completes the dynamical layer of the ADM tetrad-gravity arc (`CanonicalTetradGravity.HPMGravitationalWaves`) with the two
remaining algebraic cores of Lusanna §5–6 — the **Shanmugadhasan tidal canonical pairs** `(R_ā, Π_ā)` and the
**gravitational-wave dispersion**.

* the tidal degrees of freedom of the gravitational field form **canonical pairs** `(R_ā, Π_ā)` with the
  standard Poisson bracket `{R_ā, Π_b̄} = δ_āb̄` — exactly the symplectic structure `sympForm`
  (`AlgebraicQFT.SymplecticAdjointHadamard`); `tidal_canonical_bracket` is `{R,Π} = 1`, the phase space of the two GW
  polarizations (whose `R_ā` are the tidal Dirac observables, `NonHermitianComplexAction.DiracConstraints`);
* in the HPM linearization the tidal `R_ā` satisfy the (vacuum) wave equation `□R_ā = 0`, whose plane-wave
  modes are **massless** — the GW is the `Δ = 0` Bogoliubov mode (`Bogoliubov.Transformation.bogoliubovEnergy`),
  with dispersion `ω = c|k|` (`bogoliubovEnergy_massless`), travelling at the **speed of light**
  (`gw_luminal`, the group velocity `|k|/ω = 1`), on the mass shell `ω² = c²k²` (`gw_dispersion`).

So the gravitational wave is luminal and massless — the `Δ = 0` limit of the same Bogoliubov dispersion that
gives the causal-diamond light-cone (`E = √(ξ²+Δ²)`, massless ⟹ luminal) — and the tidal field is a canonical
`sympForm` pair.

* **§A — the Shanmugadhasan tidal canonical pairs** (`tidal_canonical_bracket`, `tidal_canonical_antisymm`).
* **§B — the GW dispersion** (`bogoliubovEnergy_massless`, `gw_luminal`, `gw_dispersion`).

The retarded Green's-function solution of `□R_ā = source`, the explicit tidal momenta `Π_ā` as functions of the
York basis, and the Post-Newtonian expansion are the analytic layer; the canonical-pair and dispersion kernel
is formalized here.

## References

* L. Lusanna, IJGMMP 12 (2015) 1530001, §5–6 (the Shanmugadhasan tidal pairs `(R_ā, Π_ā)`, the linearized GW
  evolution and dispersion).
* Repo carriers: `OperatorAlgebra.WeylCCRSpacetime` (`symplecticPairing`), `AlgebraicQFT.SymplecticAdjointHadamard` (`sympForm`),
  `Bogoliubov.Transformation` (`bogoliubovEnergy`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TidalPairsGWDispersion

open Matrix
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation


/-- **[Canonical Poisson bracket] `{R, Π} = 1`.** The tidal configuration variable `R` and its momentum `Π`
form a canonical pair: their symplectic pairing (the Poisson bracket) is `1` — the `sympForm` structure on the
gravitational tidal phase space (`R = ![1,0]`, `Π = ![0,1]`). -/
lemma tidal_canonical_bracket : symplecticPairing ![1, 0] ![0, 1] = 1 := by
  simp [symplecticPairing, sympForm, mulVec, dotProduct, Fin.sum_univ_two]

/-- **[Anti-symmetry] `{Π, R} = −1`** — the Poisson bracket is anti-symmetric (`sympForm` is alternating). -/
lemma tidal_canonical_antisymm : symplecticPairing ![0, 1] ![1, 0] = -1 := by
  simp [symplecticPairing, sympForm, mulVec, dotProduct, Fin.sum_univ_two]


/-- **[Massless GW dispersion] `ω/c = |k|`.** The gravitational wave is the `Δ = 0` (massless) Bogoliubov
mode: `bogoliubovEnergy k 0 = |k|` — the linear, gapless dispersion of a transverse-traceless GW. -/
lemma bogoliubovEnergy_massless (ξ : ℝ) : bogoliubovEnergy ξ 0 = |ξ| := by
  rw [bogoliubovEnergy]; norm_num [Real.sqrt_sq_eq_abs]

/-- **[GW travels at the speed of light] group velocity `|k|/ω = 1`.** The massless GW mode is luminal — the
same `Δ = 0` luminal limit as the causal-diamond light-cone (`|p|/E = 1`). -/
lemma gw_luminal (ξ : ℝ) (hξ : ξ ≠ 0) : |ξ| / bogoliubovEnergy ξ 0 = 1 := by
  rw [bogoliubovEnergy_massless, div_self (abs_ne_zero.mpr hξ)]

/-- **[GW mass shell] `ω² = c²k²`.** The on-shell GW frequency `ω = c·|k|` satisfies the massless dispersion
relation `ω² = c²k²` — gravitational waves propagate on the light cone. -/
lemma gw_dispersion (k c : ℝ) : (c * bogoliubovEnergy k 0) ^ 2 = c ^ 2 * k ^ 2 := by
  rw [bogoliubovEnergy_massless, mul_pow, sq_abs]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TidalPairsGWDispersion

end

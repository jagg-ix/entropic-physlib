/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.QuasifreeHorizonNoether

/-!
# The Nagao–Nielsen momentum-density action and the complex Noether charge: reversible/dissipative sectors

Links the **Levi-Civita momentum-density vector and Nagao–Nielsen `p·q` action**
(`LeviCivita.MomentumDensityNagaoNielsen`) to the **complex Noether charge**
(`GravitationalFieldEquations.GravitationalFluidComplexNoether`, `CanonicalTetradGravity.QuasifreeHorizonNoether`). Both are complex-action/entropic-time complex
objects with the **same reversible-real / dissipative-imaginary split**:

* the **Nagao–Nielsen momentum-density action** `p·q_ℂ` of the complex momentum density `q_ℂ = (T + iS) *ᵥ u`
  (with a *real* momentum covector `p`) is the **local** complex current: its **real part** is the
  reversible matter momentum work `p ⬝ᵥ (T *ᵥ u)` (`nnCanonicalPairing_real_re`), its **imaginary part**
  the entropic momentum work `p ⬝ᵥ (S *ᵥ u)` (`nnCanonicalPairing_real_im`);
* the **gravitational–fluid complex Noether charge** `Q` is the **global** complex charge: its **real
  part** is the reversible Wald charge `Re Q = −κA/(8πG)` (`gravFluidNoetherCharge_re`) on the Lusanna ADM
  tetrad geometry, its **imaginary part** the dissipative NS enstrophy rate `Im Q = ½·dΩ/dt`
  (`gravFluidNoetherCharge_im`), non-positive exactly under NS regularity `VS ≤ νP`
  (`gravFluidNoetherCharge_im_nonpos_iff`).

The two splits are the same complex-action/entropic-time structure read at two scales: the local momentum-density current
`p·q_ℂ` whose real/imaginary parts are the matter and entropic momentum work, and the global Noether
charge `Q` whose real/imaginary parts are the gravitational Wald charge and the fluid dissipation — both
anchored on the Lorentz-gauge-invariant Lusanna ADM tetrad geometry `g[ΛE] = g[E]`
(`tetradMetric_lorentz_gauge`). The reversible (geometric/matter) sector is real; the dissipative
(entropic/fluid) sector is imaginary.

* **§A — the NN momentum-density action's real/imaginary current split** (`nnCanonicalPairing_real_apply`,
  `nnCanonicalPairing_real_re`, `nnCanonicalPairing_real_im`).
* **§B — the assembly: local NN current and global Noether charge share the sector split**
  (`momentumDensity_complexNoether_sectors`).

## References

* T. Levi-Civita (arXiv:physics/9906004); K. Nagao, H. B. Nielsen (complex action); R. M. Wald
  (Noether-charge entropy); L. Lusanna (ADM tetrad gravity). Carriers:
  `LeviCivita.MomentumDensityNagaoNielsen` (`complexMomentumDensity`, `nnCanonicalPairing`),
  `GravitationalFieldEquations.GravitationalFluidComplexNoether` (`gravFluidNoetherCharge_re`, `gravFluidNoetherCharge_im`,
  `gravFluidNoetherCharge_im_nonpos_iff`), `CanonicalTetradGravity.TetradADMGravity` (`tetradMetric_lorentz_gauge`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MomentumDensityComplexNoether

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen
open Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Matrix

variable {ι : Type*} [Fintype ι]


/-- **[The NN momentum-density action with a real momentum splits] `p·q_ℂ = p·(T *ᵥ u) + i p·(S *ᵥ u)`.**
For a *real* momentum covector `p`, the Nagao–Nielsen canonical pairing of `p` with the complex momentum
density `q_ℂ = (T + iS) *ᵥ u` has its reversible matter momentum work in the real part and the entropic
momentum work in the imaginary part. -/
lemma nnCanonicalPairing_real_apply (p : ι → ℝ) (T S : Matrix ι ι ℝ) (u : ι → ℝ) :
    nnCanonicalPairing (fun ν => (p ν : ℂ)) (complexMomentumDensity T S u)
      = ((p ⬝ᵥ (T *ᵥ u) : ℝ) : ℂ) + Complex.I * ((p ⬝ᵥ (S *ᵥ u) : ℝ) : ℂ) := by
  rw [nnCanonicalPairing]
  simp only [dotProduct, complexMomentumDensity_apply]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ν _ => by ring

/-- **[Real part = reversible matter momentum work] `Re(p·q_ℂ) = p ⬝ᵥ (T *ᵥ u)`.** -/
lemma nnCanonicalPairing_real_re (p : ι → ℝ) (T S : Matrix ι ι ℝ) (u : ι → ℝ) :
    (nnCanonicalPairing (fun ν => (p ν : ℂ)) (complexMomentumDensity T S u)).re
      = p ⬝ᵥ (T *ᵥ u) := by
  rw [nnCanonicalPairing_real_apply]; simp

/-- **[Imaginary part = entropic momentum work] `Im(p·q_ℂ) = p ⬝ᵥ (S *ᵥ u)`.** -/
lemma nnCanonicalPairing_real_im (p : ι → ℝ) (T S : Matrix ι ι ℝ) (u : ι → ℝ) :
    (nnCanonicalPairing (fun ν => (p ν : ℂ)) (complexMomentumDensity T S u)).im
      = p ⬝ᵥ (S *ᵥ u) := by
  rw [nnCanonicalPairing_real_apply]; simp


/-- **[The NN momentum-density action and the complex Noether charge share the complex-action/entropic-time sector split].**
For a four-velocity `u`, a real momentum covector `p`, a Lorentz frame `Λ ∈ SO(1,3)` with cotetrad `E`,
and gravitational/fluid data `(κ, A, G, ν, P, VS)`:

* **local NN current** — the Nagao–Nielsen action `p·q_ℂ` of the complex momentum density splits into the
  reversible matter momentum work `Re(p·q_ℂ) = p ⬝ᵥ (T *ᵥ u)` and the entropic momentum work
  `Im(p·q_ℂ) = p ⬝ᵥ (S *ᵥ u)`;
* **global Noether charge** — the complex Noether charge `Q` splits into the reversible Wald charge
  `Re Q = −κA/(8πG)` and the dissipative NS enstrophy rate `Im Q = ½·dΩ/dt`, non-positive iff `VS ≤ νP`;
* **geometry** — both rest on the Lorentz-gauge-invariant Lusanna ADM tetrad metric `g[ΛE] = g[E]`.

The local momentum-density current and the global Noether charge are one complex-action/entropic-time structure: real =
reversible (matter / gravitational), imaginary = dissipative (entropic / fluid). -/
lemma momentumDensity_complexNoether_sectors {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (p : Fin 1 ⊕ Fin d → ℝ) (T S : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (u : Fin 1 ⊕ Fin d → ℝ) (κ A G ν P VS : ℝ) :
    (nnCanonicalPairing (fun ν => (p ν : ℂ)) (complexMomentumDensity T S u)).re = p ⬝ᵥ (T *ᵥ u)
      ∧ (nnCanonicalPairing (fun ν => (p ν : ℂ)) (complexMomentumDensity T S u)).im = p ⬝ᵥ (S *ᵥ u)
      ∧ (gravFluidNoetherCharge κ A G ν P VS).re = noetherCharge κ A G
      ∧ (gravFluidNoetherCharge κ A G ν P VS).im = enstrophyRate VS ν P / 2
      ∧ ((gravFluidNoetherCharge κ A G ν P VS).im ≤ 0 ↔ VS ≤ ν * P)
      ∧ tetradMetric (Λ * E) = tetradMetric E :=
  ⟨nnCanonicalPairing_real_re p T S u, nnCanonicalPairing_real_im p T S u,
    gravFluidNoetherCharge_re κ A G ν P VS, gravFluidNoetherCharge_im κ A G ν P VS,
    gravFluidNoetherCharge_im_nonpos_iff κ A G ν P VS, tetradMetric_lorentz_gauge hΛ⟩

end Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MomentumDensityComplexNoether

end

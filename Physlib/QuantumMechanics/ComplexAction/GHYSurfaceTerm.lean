/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction

/-!
# The Gibbons–Hawking–York surface term for spacelike/timelike segments (§II.B)

Section II.B of Lehner, Myers, Poisson & Sorkin (arXiv:1609.00207): the variation of the bulk
Einstein–Hilbert action over a spacelike or timelike boundary segment `Σ` produces the
**Gibbons–Hawking–York** term, the trace `K` of the extrinsic curvature integrated over `Σ`.

The boundary integrand splits (Eq. 2.29) into `−2δK`, a total divergence `−εD_aδA^a` (which becomes the
joint terms at `ℬ₁, ℬ₂`), and `K_abδh^{ab}` (which vanishes under the general-relativity boundary
condition `δh^{ab} = 0`). What remains is the variation of the GHY term `S_Σ = −2ε∫_Σ K dΣ` (Eq. 2.31),
with `ε = n·n = ±1` the signature of the unit normal.

* **§A — the signature** `ε = ±1` (Eq. 2.6). `signatureSq` (`ε² = 1`), the spacelike (`ε = −1`) and
  timelike (`ε = +1`) cases.
* **§B — the boundary integrand** (Eq. 2.29). Combining the two `δK` expressions (Eqs. 2.20, 2.26) and
  `δv^μn_μ = (h^{αβ}n_μ − n^αh^β_μ)δΓ^μ_{αβ}` (Eq. 2.28) gives
  `δv^μn_μ = −2δK − εD_aδA^a + K_abδh^{ab}` (`boundaryIntegrand_eq`) — a genuine linear identity.
* **§C — the GHY term** (Eq. 2.31). `ghySurfaceTerm ε (∫K) = −2ε∫K`; a spacelike segment (`ε = −1`)
  contributes `+2∫K` (`ghy_spacelike`), a timelike segment (`ε = +1`) contributes `−2∫K`
  (`ghy_timelike`) — the signs of Eq. 1.3.
* **§D — the two surface families of `S_∂𝒱`** (Eq. 1.3). The GHY `K`-term and the null `κ`-term
  (`NullBoundaryGravitationalAction.nullSegmentAction`) are the spacelike/timelike and null surface
  contributions that together make up `S_∂𝒱` (`boundary_surface_families`).

**Honest layering.** Proven: the signature identity, the boundary-integrand linear identity from the
component equations, the GHY signs, and the composition of the two surface families. Interpretive: the
scalars `δK`, `K_abδh^{ab}`, `εD_aδA^a`, `(δμ/μ)K`, and the `δΓ` contractions are the tensorial data of
§II.B (the extrinsic curvature `K_ab := e_a^α e_b^β∇_αn_β`, the projector `h^{αβ}`, the non-total
variation `δA^a`), taken here as scalars; the integrals are represented by their integrated values.

## References

* L. Lehner, R. C. Myers, E. Poisson, R. D. Sorkin, "Gravitational action with null boundaries",
  arXiv:1609.00207 [`Lehner:2016vdi`], §II.B, Eqs. (2.6)–(2.31). GHY: J. W. York, Phys. Rev. Lett. 28,
  1082 (1972); G. W. Gibbons, S. W. Hawking, Phys. Rev. D 15, 2752 (1977). Reuses
  `NullBoundaryGravitationalAction` (`nullSegmentAction`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm

open Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction


/-- **The signature squares to one** `ε² = 1` (Eq. 2.6): the unit normal has `ε := n·n = ±1`
(`−1` spacelike, `+1` timelike). -/
lemma signatureSq (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : ε ^ 2 = 1 := by
  rcases hε with h | h <;> rw [h] <;> ring


/-- **The boundary integrand** `δv^μn_μ = −2δK − εD_aδA^a + K_abδh^{ab}` (Eq. 2.29): a genuine linear
consequence of the two expressions for `δK` (Eqs. 2.20 `δK = K_abδh^{ab} + (δμ/μ)K − h^{αβ}n_μδΓ`;
2.26 `δK = −εD_aδA^a − (δμ/μ)K + n^αh^β_μδΓ`) and the completeness form of the integrand (Eq. 2.28
`δv^μn_μ = h^{αβ}n_μδΓ − n^αh^β_μδΓ`). The `(δμ/μ)K` normal-normal pieces cancel. -/
lemma boundaryIntegrand_eq (δvn δK dK_h dmuK dGamma_hh dGamma_nh εDdA : ℝ)
    (h20 : δK = dK_h + dmuK - dGamma_hh)
    (h26 : δK = -εDdA - dmuK + dGamma_nh)
    (h28 : δvn = dGamma_hh - dGamma_nh) :
    δvn = -2 * δK - εDdA + dK_h := by linarith


/-- **The Gibbons–Hawking–York surface term** `S_Σ = −2ε∫_Σ K dΣ` (Eq. 2.31): with the
general-relativity boundary condition `δh^{ab} = 0`, the boundary integrand `−2δK` integrates to the
variation of this term, the trace of the extrinsic curvature over the segment. -/
def ghySurfaceTerm (ε Kintegral : ℝ) : ℝ := -2 * ε * Kintegral

/-- **A spacelike segment contributes `+2∫K`** (Eq. 1.3, `ε = −1`). -/
lemma ghy_spacelike (Kintegral : ℝ) : ghySurfaceTerm (-1) Kintegral = 2 * Kintegral := by
  unfold ghySurfaceTerm; ring

/-- **A timelike segment contributes `−2∫K`** (Eq. 1.3, `ε = +1`). -/
lemma ghy_timelike (Kintegral : ℝ) : ghySurfaceTerm 1 Kintegral = -2 * Kintegral := by
  unfold ghySurfaceTerm; ring


/-- **The two surface families compose in `S_∂𝒱`** (Eq. 1.3): the GHY `K`-term (spacelike/timelike
segments, this section) and the null `κ`-term with its joints
(`NullBoundaryGravitationalAction.nullSegmentAction`, §II.C) are the two surface contributions to the
boundary action of a region with a broken boundary. -/
lemma boundary_surface_families (ε Kintegral kappaIntegral aTop aBot : ℝ) :
    ghySurfaceTerm ε Kintegral + nullSegmentAction kappaIntegral aTop aBot
      = -2 * ε * Kintegral + (-2 * kappaIntegral + 2 * aTop - 2 * aBot) := by
  unfold ghySurfaceTerm nullSegmentAction; ring

end Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm

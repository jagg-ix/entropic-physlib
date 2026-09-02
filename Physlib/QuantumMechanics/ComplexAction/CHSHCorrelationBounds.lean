/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.VectorBanachStoneDistortion
public import Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds

/-!
# CHSH: the continuous-observable classical bound and the Banach–Stone links

The shared CHSH core — the deterministic `±1` classical bound and its tightness, the
Tsirelson bound `S² ≤ 8` / `|S| ≤ 2√2` in correlation form, and the strict gap
`2 < 2√2` — lives in **`Bell.DeterministicBounds`** (`chsh_lhv_bound`,
`classicalCHSH_tight`, `tsirelson_sq_bound`, `tsirelson_correlation_bound`,
`classical_lt_tsirelson`, `tsirelsonWitness`); this module holds what that core does
not:

* `classical_chsh_abs_le_two` — the classical bound `|S| ≤ 2` for **continuous
  observables** in `[−1,1]` (deterministic non-contextual value assignments need not be
  dichotomic): the regrouping `a(b+b') + a'(b−b')` with a four-way sign analysis, not a
  finite case check.
* `chshVector_scalar_eq` — the vector CHSH functional of
  `AdSCFT.VectorBanachStoneDistortion.chshVector`, evaluated on the one-dimensional
  Hilbert space `ℝ`, **is** the correlation polynomial — the vector Tsirelson bound
  (unit vectors) and the correlation Tsirelson bound (`[−1,1]` observables) bound the
  same object along different slices.
* `quantum_classical_gap_eq_critical_distortion` — the gap ratio is the critical
  Banach–Stone distortion: `tsirelsonWitness/2 = √2 = M²` at `M⁴ = 2` — quantum
  mechanics exceeds local realism by exactly the distortion at which vector-valued
  Banach–Stone isomorphisms stop detecting topology.

**Honest layering.**  Sign analysis and algebra on the shared core's objects.  The
quantum realization of the Tsirelson value (Bell states, `S² = 8` at the optimal
angles), no-cloning, and no-signalling are `BellStateNoSignalling` /
`BellBlochHistoryLinks`, not re-derived here.

## References

* J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt, Phys. Rev. Lett. **23** (1969)
  880; B. S. Tsirelson, Lett. Math. Phys. **4** (1980) 93.  Shared core:
  `Bell.DeterministicBounds` (also from reference-tree `NoFTLBellBridge` /
  `BellCHSHBohmCoreAbstractions`).  Continuous-observable source: translator-tree
  `DSFCHSHBound.lean` (own authorship), re-authored.  Carrier links:
  `AdSCFT.VectorBanachStoneDistortion` (`chshVector`, critical distortion).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.VectorBanachStoneDistortion
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CHSHCorrelationBounds

/-! ## §A — the classical bound for continuous observables -/

private lemma chsh_le_two_aux (a a' b b' : ℝ)
    (ha : |a| ≤ 1) (ha' : |a'| ≤ 1) (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) :
    a * b + a * b' + a' * b - a' * b' ≤ 2 := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨ha'1, ha'2⟩ := abs_le.mp ha'
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hb'1, hb'2⟩ := abs_le.mp hb'
  have hgroup : a * b + a * b' + a' * b - a' * b'
      = a * (b + b') + a' * (b - b') := by ring
  rw [hgroup]
  rcases le_total 0 (b + b') with hp | hp <;> rcases le_total 0 (b - b') with hq | hq
  · have t1 : a * (b + b') ≤ b + b' := by nlinarith
    have t2 : a' * (b - b') ≤ b - b' := by nlinarith
    linarith
  · have t1 : a * (b + b') ≤ b + b' := by nlinarith
    have t2 : a' * (b - b') ≤ -(b - b') := by nlinarith
    linarith
  · have t1 : a * (b + b') ≤ -(b + b') := by nlinarith
    have t2 : a' * (b - b') ≤ b - b' := by nlinarith
    linarith
  · have t1 : a * (b + b') ≤ -(b + b') := by nlinarith
    have t2 : a' * (b - b') ≤ -(b - b') := by nlinarith
    linarith

/-- **The classical CHSH bound for continuous observables** in `[−1,1]` — deterministic
non-contextual outcomes need not be dichotomic: `|ab + ab' + a'b − a'b'| ≤ 2`.  The
dichotomic case is `Bell.DeterministicBounds.chsh_lhv_bound`. -/
theorem classical_chsh_abs_le_two (a a' b b' : ℝ)
    (ha : |a| ≤ 1) (ha' : |a'| ≤ 1) (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) :
    |a * b + a * b' + a' * b - a' * b'| ≤ 2 := by
  rw [abs_le]
  constructor
  · have h := chsh_le_two_aux (-a) (-a') b b' (by rwa [abs_neg]) (by rwa [abs_neg]) hb hb'
    nlinarith
  · exact chsh_le_two_aux a a' b b' ha ha' hb hb'

/-! ## §B — links across the arc -/

/-- **The vector CHSH functional on the one-dimensional Hilbert space is the correlation
polynomial**: `chshVector` of `AdSCFT.VectorBanachStoneDistortion`, evaluated on `H = ℝ`,
reduces to `ab + a'b + ab' − a'b'` — the vector Tsirelson bound (unit vectors) and the
correlation Tsirelson bound (`Bell.DeterministicBounds.tsirelson_correlation_bound`)
bound the same functional along different slices. -/
theorem chshVector_scalar_eq (a a' b b' : ℝ) :
    chshVector (H := ℝ) a a' b b' = a * b + a' * b + a * b' - a' * b' := by
  unfold chshVector
  simp
  ring

/-- **The quantum–classical gap is the critical Banach–Stone distortion**:
`tsirelsonWitness/2 = √2 = M²` at `M⁴ = 2` — quantum correlations exceed local realism
by exactly the distortion at which vector-valued Banach–Stone isomorphisms stop
determining the topology. -/
theorem quantum_classical_gap_eq_critical_distortion (M : ℝ) (hM : 0 < M)
    (hM4 : M^4 = 2) :
    tsirelsonWitness / 2 = M^2 := by
  unfold tsirelsonWitness
  rw [critical_distortion_eq_scalingFactor_two M hM hM4,
    Physlib.Mathematics.DimensionalScaling.scalingFactor, Nat.cast_ofNat]
  ring

end Physlib.QuantumMechanics.ComplexAction.CHSHCorrelationBounds

end

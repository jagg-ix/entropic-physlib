/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant

/-!
# The Ricci curvature decomposition (Weyl / traceless Ricci / Ricci scalar) on the tetrad metric

Links `LeviCivita.TetradInvariant` (the gauge-invariant *metric* scalars — proper separation
`xᵀ g x`, area defect `‖ξ×η‖²` on the tetrad metric `g = coordCongruence E η = EᵀηE`) to the gauge-invariant
*curvature* pieces — the irreducible decomposition of the Riemann tensor into

  **Weyl tensor** `C` ⊕ **traceless Ricci** `S_ab = R_ab − (R/n) g_ab` ⊕ **Ricci scalar** `R`.

physlib's general relativity is matrix-valued (the 2-index Ricci tensor `Ric`, the scalar curvature, the
metric `g`, the Einstein tensor `G = Ric − ½R g` of `ComplexEinstein.EinsteinFieldEquationsPhysLean`); there is no
4-index Riemann tensor, so the **Weyl tensor cannot be built as a tensor here**. What *is* exact and
matrix-representable is the **trace part** of the decomposition — the traceless Ricci and the Ricci scalar —
and the Weyl sector's *defining property*: it is the completely trace-free part of the curvature, so it is
exactly what survives in **vacuum** (`Ric = 0`), where the Ricci scalar and traceless Ricci both vanish.

* **§A — the trace decomposition.** `Ric = S + (R/n) g` (`ricci_trace_decomposition`); `S` is trace-free,
  `gᵃᵇ S_ab = 0` (`tracelessRicci_metricTraceFree`); the Einstein tensor in terms of the pieces
  (`einsteinTensor_eq_tracelessRicci_add`).
* **§B — the Weyl sector.** Vacuum curvature is pure Weyl: `Ric = 0` kills the Ricci scalar, the traceless
  Ricci and the Einstein tensor (`vacuum_pure_weyl`), so all curvature lives in the (here unresolved) Weyl
  tensor.
* **§C — on the tetrad metric.** With the tetrad metric `g = coordCongruence E η`, the traceless Ricci is
  trace-free with dimension `n = card ι` read off from `gᵃᵇ g_ab = tr 1 = card ι`
  (`tracelessRicci_tetrad_traceFree`); and the **flat** tetrad geometry (`Ric = 0`) has a trivial curvature
  decomposition — Weyl, traceless Ricci and Ricci scalar all vanish (`flat_tetrad_curvature_vanishes`) — the
  flat endpoint in which the bridge's gauge-invariant proper separation lives.

## References

* L. P. Eisenhart, *Riemannian Geometry* (the Ricci decomposition); H. Weyl (the conformal tensor). structure:
  `Physlib` (`ComplexEinstein.EinsteinFieldEquationsPhysLean`, `LeviCivita.TetradInvariant`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §A — the trace decomposition -/

/-- **The Ricci scalar** as the metric contraction of the Ricci tensor `R = gᵃᵇ R_ab = tr(g⁻¹ · Ric)`. -/
def ricciScalarContraction (gInv Ric : Matrix ι ι ℝ) : ℝ := (gInv * Ric).trace

/-- **The traceless (trace-free) Ricci tensor** `S_ab = R_ab − (R/n) g_ab`. -/
noncomputable def tracelessRicci (Ric g : Matrix ι ι ℝ) (scalarR n : ℝ) : Matrix ι ι ℝ :=
  Ric - (scalarR / n) • g

omit [Fintype ι] [DecidableEq ι] in
/-- **[Ricci trace decomposition] `Ric = S + (R/n) g`** — the Ricci tensor splits into its trace-free part
and its pure-trace (Ricci-scalar) part. -/
theorem ricci_trace_decomposition (Ric g : Matrix ι ι ℝ) (scalarR n : ℝ) :
    Ric = tracelessRicci Ric g scalarR n + (scalarR / n) • g := by
  rw [tracelessRicci, sub_add_cancel]

omit [DecidableEq ι] in
/-- **[The traceless Ricci is trace-free] `gᵃᵇ S_ab = 0`.** With `gᵃᵇ R_ab = R` and `gᵃᵇ g_ab = n` (`n ≠ 0`),
the metric trace of the traceless Ricci vanishes. -/
theorem tracelessRicci_metricTraceFree (gInv Ric g : Matrix ι ι ℝ) (scalarR n : ℝ)
    (hR : (gInv * Ric).trace = scalarR) (hg : (gInv * g).trace = n) (hn : n ≠ 0) :
    (gInv * tracelessRicci Ric g scalarR n).trace = 0 := by
  rw [tracelessRicci, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, hR, hg, div_mul_cancel₀ scalarR hn, sub_self]

omit [Fintype ι] [DecidableEq ι] in
/-- **[The Einstein tensor through the decomposition] `G = S + (R/n − R/2) g`.** -/
theorem einsteinTensor_eq_tracelessRicci_add (Ric g : Matrix ι ι ℝ) (scalarR n : ℝ) :
    einsteinTensor Ric scalarR g = tracelessRicci Ric g scalarR n + (scalarR / n - scalarR / 2) • g := by
  rw [einsteinTensor, tracelessRicci, sub_smul]
  abel

/-! ## §B — the Weyl sector -/

/-- **[Vacuum curvature is pure Weyl] `Ric = 0 ⇒` Ricci scalar `= 0`, traceless Ricci `= 0`, Einstein
tensor `= 0`.** In vacuum the Ricci scalar and the traceless Ricci both vanish, so all curvature resides in
the Weyl tensor — the completely trace-free part of the Riemann tensor (not resolved by this matrix/Ricci
framework). -/
theorem vacuum_pure_weyl (gInv g : Matrix ι ι ℝ) (n : ℝ) :
    ricciScalarContraction gInv 0 = 0 ∧ tracelessRicci 0 g 0 n = 0
      ∧ einsteinTensor 0 0 g = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ricciScalarContraction]
  · simp [tracelessRicci]
  · simp [einsteinTensor]

/-! ## §C — on the tetrad metric -/

variable [Nonempty ι]

/-- **[Traceless Ricci is trace-free on the tetrad metric, dimension `n = card ι`].** For the Lusanna /
Levi-Civita tetrad metric `g = coordCongruence E η` with inverse `gInv` (`gInv · g = 1`), the metric trace of
the traceless Ricci vanishes, the dimension `n = card ι` being read off from `gᵃᵇ g_ab = tr 1 = card ι`. -/
theorem tracelessRicci_tetrad_traceFree (E η gInv Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (hgInv : gInv * coordCongruence E η = 1) (hR : (gInv * Ric).trace = scalarR) :
    (gInv * tracelessRicci Ric (coordCongruence E η) scalarR (Fintype.card ι)).trace = 0 := by
  refine tracelessRicci_metricTraceFree gInv Ric (coordCongruence E η) scalarR (Fintype.card ι) hR
    ?_ ?_
  · rw [hgInv, Matrix.trace_one]
  · exact_mod_cast Fintype.card_ne_zero

omit [Nonempty ι] in
/-- **[Flat tetrad geometry ⇒ trivial curvature decomposition].** When the tetrad geometry is flat
(`Ric = 0`, hence `R = 0`), the Ricci scalar, traceless Ricci and Einstein tensor all vanish on
`g = coordCongruence E η`; the Weyl tensor vanishes too (flat ⇒ conformally flat), so the entire Weyl /
traceless-Ricci / Ricci-scalar decomposition is trivial — the flat endpoint in which the bridge's
gauge-invariant proper separation lives. -/
theorem flat_tetrad_curvature_vanishes (E η gInv : Matrix ι ι ℝ) (n : ℝ) :
    ricciScalarContraction gInv 0 = 0 ∧ tracelessRicci 0 (coordCongruence E η) 0 n = 0
      ∧ einsteinTensor 0 0 (coordCongruence E η) = 0 :=
  vacuum_pure_weyl gInv (coordCongruence E η) n

end Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad

end

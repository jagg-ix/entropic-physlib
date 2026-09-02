/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
public import Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge
public import Physlib.QuantumMechanics.ComplexAction.LovelockPalatiniCharacterization
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

/-!
# The affine (Palatini/Eddington) field equation and its first integral

In the metric-affine (Palatini) and purely-affine (Eddington–Schrödinger) formulations of gravity the
connection is an independent field. Varying the affine action gives a *connection* field equation whose
algebraic contraction fixes the connection, and a *first integral* of the form `M_{ab} = λ g_{ab}` for an
affine "matter tensor" `M_{ab}`; that first integral reproduces the cosmological Einstein equation, with
the cosmological constant emerging from the integration constant `λ`. This module formalizes that chain
and its pure-Lovelock generalization, building on the repository's Palatini/Lovelock/Einstein carriers
(`Curvature.DiffeomorphismMetricVariation`, `EinsteinPalatiniProjectiveGauge`,
`LovelockPalatiniCharacterization`, `ComplexEinstein.EinsteinFieldEquationsPhysLean`).

* **The connection field equation (§A).** `connectionResidual` is the trace-adjusted combination
  `2 Γ_{bpc} − δ_{bc} Γ^d_{pd} − δ_{bp} Γ^d_{cd}` appearing in the varied affine action.
  `connectionResidual_contract` contracts it (`b = c`) to force the density-derivative trace
  `∑_d Γ^d_{pd} = 0` for `dim ≥ 2`, and `connectionResidual_iff_density_parallel` promotes this to the
  full vanishing `Γ = 0` — the metric-compatible / density-parallel condition solving the connection EOM.
* **The first integral `M = λ g` gives Einstein-Λ (§B).** With the matter-affine tensor
  `matterAffineTensor = Ric − κ·(trace-reversed matter)`, the first integral `matterAffineTensor = λ g`
  yields `Ric = κ T + (…) g` (`firstIntegral_ricci_eq`), a fixed scalar curvature
  (`firstIntegral_scalarCurvature`), and finally the cosmological Einstein equation
  `einsteinFieldEquationCosmological` with `Λ = eddingtonLambda λ = (D/2 − 1) λ`
  (`firstIntegral_derives_einsteinLambda`).
* **A nonsingular first integral forces `Λ ≠ 0` (§C).** If `M = λ g` with `M` invertible (`IsUnit M.det`),
  then `λ ≠ 0` (`nonsingular_firstIntegral_lambda_ne_zero`) and hence the emergent cosmological constant is
  nonzero (`nonsingular_firstIntegral_eddingtonLambda_ne_zero`, for `dim > 2`): the affine formulation
  cannot produce a nonsingular geometry with vanishing `Λ`.
* **Torsion is killed by its vacuum equation (§D).** For an antisymmetric contorsion `K` whose vacuum
  field equation ties it to its trace, `torsionVacuumEom_forces_contorsion_zero` gives `K = 0` and a
  vanishing torsion trace — the metric-affine connection is torsion-free on shell.
* **Pure-Lovelock extension (§E).** The `m`-th pure-Lovelock affine first integral
  `lovelockAffineTensor m = λ g` reproduces the pure-Lovelock field equation
  `RicM − (L/2) g + Λ_{(m)} g = κ T` with `Λ_{(m)} = lovelockEddingtonLambda m λ`
  (`lovelockFirstIntegral_derives_fieldEquation`), the `m = 1` case being §B.

## Honest scope

This is the algebra of the affine first integral and its Lovelock generalization over a finite index type
`ι` (`dim = Fintype.card ι`), with the metric contraction `gInv * g = 1` supplied as a hypothesis. The
connection, curvature and matter tensors are taken as matrices/arrays; the underlying variational
derivation (that the varied affine action produces exactly these equations) is the standard
Palatini/Eddington content encoded here, not re-derived from a functional. The specific source note that
motivated the prototype did not record a citation; the result is the classical Eddington–Schrödinger
affine first integral, of a piece with the Palatini/Einstein–Hilbert equivalence of
`EinsteinPalatiniProjectiveGauge` (Dadhich–Pons).

## References

* A. S. Eddington, *The Mathematical Theory of Relativity*, CUP (1923), §§61–62 (the affine field
  equation and its first integral `R_{μν} = λ g_{μν}`); E. Schrödinger, *Space-Time Structure*, CUP
  (1950), Ch. XII.
* N. Dadhich, J. M. Pons, *On the equivalence of the Einstein–Hilbert and Einstein–Palatini
  formulations*, Gen. Rel. Grav. **44** (2012) 2337 — the Palatini connection equation, carried by
  `EinsteinPalatiniProjectiveGauge`.
* `ComplexEinstein.EinsteinFieldEquationsPhysLean` (`einsteinFieldEquationCosmological`, `einsteinTensor`);
  `LovelockPalatiniCharacterization`; `Curvature.DiffeomorphismMetricVariation`.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## A. The connection field equation and its density-parallel solution -/

/-- **The connection-equation residual** `2 Γ_{bpc} − δ_{bc} Γ^d_{pd} − δ_{bp} Γ^d_{cd}` — the
trace-adjusted combination of connection coefficients that the varied affine action sets to zero. -/
def connectionResidual (D : ι → Matrix ι ι ℝ) (b p c : ι) : ℝ :=
  2 * D b p c -
    (if b = c then ∑ d, D d p d else 0) -
    (if b = p then ∑ d, D d c d else 0)

/-- **Contracting the connection equation kills the density trace** (Eq. 8 → Eq. 9): if the residual
vanishes for all indices then `∑_d Γ^d_{pd} = 0`, for `dim ≥ 2` — the diagonal contraction `b = c`
isolates `(1 − dim)` times the trace. -/
theorem connectionResidual_contract
    (D : ι → Matrix ι ι ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (h : ∀ b p c, connectionResidual D b p c = 0)
    (p : ι) :
    ∑ d, D d p d = 0 := by
  have hs : ∑ b, connectionResidual D b p b = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    exact h b p b
  simp only [connectionResidual, if_pos, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hite :
      (∑ x, if x = p then ∑ d, D d x d else 0) =
        ∑ d, D d p d := by
    simp
  have htwo :
      (∑ x, 2 * D x p x) = 2 * ∑ x, D x p x := by
    rw [Finset.mul_sum]
  rw [hite, htwo] at hs
  have hne : (1 - (Fintype.card ι : ℝ)) ≠ 0 := by
    have : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
    linarith
  apply (mul_eq_zero.mp ?_).resolve_left hne
  convert hs using 1 <;> ring

/-- **The connection equation forces `Γ = 0`** (the density-parallel / metric-compatible solution):
the residual vanishes identically iff all connection coefficients vanish, for `dim ≥ 2`. -/
theorem connectionResidual_iff_density_parallel
    (D : ι → Matrix ι ι ℝ)
    (hcard : 2 ≤ Fintype.card ι) :
    (∀ b p c, connectionResidual D b p c = 0) ↔
      ∀ b p c, D b p c = 0 := by
  constructor
  · intro h b p c
    have hp := connectionResidual_contract D hcard h p
    have hc := connectionResidual_contract D hcard h c
    have hres := h b p c
    simp [connectionResidual, hp, hc] at hres
    linarith
  · intro h b p c
    simp [connectionResidual, h]

/-! ## B. The first integral `M = λ g` reproduces the cosmological Einstein equation -/

/-- The metric trace `g^{ab} T_{ab} = tr(g^{-1} T)`. -/
noncomputable def metricTrace
    (gInv T : Matrix ι ι ℝ) : ℝ :=
  (gInv * T).trace

/-- The trace-reversed matter tensor `T_{ab} − (g^{cd}T_{cd}/(D−2)) g_{ab}`. -/
noncomputable def traceReversedMatter
    (gInv g T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  T - (metricTrace gInv T / ((Fintype.card ι : ℝ) - 2)) • g

/-- **The matter-affine tensor** `M_{ab} = Ric_{ab} − κ·(trace-reversed matter)_{ab}` — the object whose
first integral `M = λ g` is the affine field equation. -/
noncomputable def matterAffineTensor
    (Ric gInv g T : Matrix ι ι ℝ) (κ : ℝ) : Matrix ι ι ℝ :=
  Ric - κ • traceReversedMatter gInv g T

/-- **The emergent cosmological constant** `Λ = (D/2 − 1) λ` from the first-integral constant `λ`. -/
noncomputable def eddingtonLambda (lam : ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) / 2 - 1) * lam

/-- **The first integral fixes the Ricci tensor**: `M = λ g` gives
`Ric = κ T + (λ − κ g^{cd}T_{cd}/(D−2)) g`. -/
theorem firstIntegral_ricci_eq
    (Ric gInv g T : Matrix ι ι ℝ) (κ lam : ℝ)
    (hfirst : matterAffineTensor Ric gInv g T κ = lam • g) :
    Ric = κ • T +
      (lam - κ * metricTrace gInv T /
        ((Fintype.card ι : ℝ) - 2)) • g := by
  unfold matterAffineTensor traceReversedMatter at hfirst
  ext i j
  have hij := congrFun (congrFun hfirst i) j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul] at hij ⊢
  linear_combination hij

/-- **The first integral fixes the scalar curvature**: `g^{ab}R_{ab} = D λ − 2κ g^{cd}T_{cd}/(D−2)`,
for `dim ≠ 2` and `g^{-1} g = 1`. -/
theorem firstIntegral_scalarCurvature
    (Ric gInv g T : Matrix ι ι ℝ) (κ lam : ℝ)
    (hdim : (Fintype.card ι : ℝ) ≠ 2)
    (hgInv : gInv * g = 1)
    (hfirst : matterAffineTensor Ric gInv g T κ = lam • g) :
    metricTrace gInv Ric =
      (Fintype.card ι : ℝ) * lam -
        2 * κ * metricTrace gInv T /
          ((Fintype.card ι : ℝ) - 2) := by
  rw [firstIntegral_ricci_eq Ric gInv g T κ lam hfirst]
  have hden : (Fintype.card ι : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr hdim
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, (Fintype.card ι : ℝ) - 2 = D := ⟨_, rfl⟩
  rw [hDdef] at hden ⊢
  simp only [metricTrace, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, hgInv, Matrix.trace_one, smul_eq_mul]
  field_simp [hden]
  subst hDdef
  ring

/-- **The affine first integral IS the cosmological Einstein equation**: `M = λ g` (for `dim ≠ 2`,
`g^{-1}g = 1`) implies `einsteinFieldEquationCosmological` with `Λ = eddingtonLambda λ`. The cosmological
constant of the metric formulation is the integration constant of the affine one. -/
theorem firstIntegral_derives_einsteinLambda
    (Ric gInv g T : Matrix ι ι ℝ) (κ lam : ℝ)
    (hdim : (Fintype.card ι : ℝ) ≠ 2)
    (hgInv : gInv * g = 1)
    (hfirst : matterAffineTensor Ric gInv g T κ = lam • g) :
    einsteinFieldEquationCosmological Ric (metricTrace gInv Ric)
      g T (eddingtonLambda (ι := ι) lam) κ := by
  have hRic := firstIntegral_ricci_eq Ric gInv g T κ lam hfirst
  have hR := firstIntegral_scalarCurvature Ric gInv g T κ lam hdim hgInv hfirst
  unfold einsteinFieldEquationCosmological einsteinTensor eddingtonLambda
  rw [hR, hRic]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  have hden : (Fintype.card ι : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr hdim
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, (Fintype.card ι : ℝ) - 2 = D := ⟨_, rfl⟩
  rw [hDdef] at hden ⊢
  field_simp [hden]
  subst hDdef
  ring

/-! ## C. A nonsingular first integral forces a nonzero cosmological constant -/

/-- **Nonsingular `M = λ g` ⟹ `λ ≠ 0`**: if the affine matter tensor is invertible, the first-integral
constant cannot vanish (else `M = 0` is singular). -/
theorem nonsingular_firstIntegral_lambda_ne_zero
    [Nonempty ι]
    (M g : Matrix ι ι ℝ) (lam : ℝ)
    (hunit : IsUnit M.det)
    (hfirst : M = lam • g) :
    lam ≠ 0 := by
  intro hlam
  rw [hlam, zero_smul] at hfirst
  rw [hfirst, Matrix.det_zero] at hunit
  exact not_isUnit_zero hunit

/-- **Nonsingular `M = λ g` ⟹ `Λ ≠ 0`** (for `dim > 2`): a nonsingular affine geometry carries a nonzero
emergent cosmological constant. -/
theorem nonsingular_firstIntegral_eddingtonLambda_ne_zero
    [Nonempty ι]
    (M g : Matrix ι ι ℝ) (lam : ℝ)
    (hcard : 2 < Fintype.card ι)
    (hunit : IsUnit M.det)
    (hfirst : M = lam • g) :
    eddingtonLambda (ι := ι) lam ≠ 0 := by
  have hlam := nonsingular_firstIntegral_lambda_ne_zero M g lam hunit hfirst
  unfold eddingtonLambda
  apply mul_ne_zero
  · have hc : (2 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
    linarith
  · exact hlam

/-! ## D. The torsion vacuum equation forces vanishing contorsion -/

/-- **Torsion is killed on shell**: an antisymmetric contorsion `K_{acd}` whose vacuum field equation
ties it to its trace `K_{acd} + δ_{ca} S_d = 0` is forced to vanish, `K = 0`, together with its trace —
the metric-affine connection is torsion-free in vacuum. -/
theorem torsionVacuumEom_forces_contorsion_zero
    [Nonempty ι]
    (K : ι → ι → ι → ℝ) (TorsionTrace : ι → ℝ)
    (hanti : ∀ a c d, K a c d = -K c a d)
    (heom : ∀ a c d,
      K a c d + (if c = a then TorsionTrace d else 0) = 0) :
    K = 0 ∧ TorsionTrace = 0 := by
  have htrace : ∀ d, TorsionTrace d = 0 := by
    intro d
    let a : ι := Classical.choice ‹Nonempty ι›
    have hdiag := hanti a a d
    have hK : K a a d = 0 := by linarith
    simpa [hK] using heom a a d
  constructor
  · funext a c d
    simpa [htrace] using heom a c d
  · funext d
    exact htrace d

/-! ## E. The pure-Lovelock affine first integral -/

/-- The pure-Lovelock trace-reversed matter tensor with denominator `D − 2m`. -/
noncomputable def lovelockTraceReversedMatter
    (m : ℕ) (gInv g T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  T - (metricTrace gInv T /
    ((Fintype.card ι : ℝ) - 2 * (m : ℝ))) • g

/-- The `m`-th pure-Lovelock matter-affine tensor `RicM − κ·(Lovelock trace-reversed matter)`. -/
noncomputable def lovelockAffineTensor
    (m : ℕ) (RicM gInv g T : Matrix ι ι ℝ) (κ : ℝ) :
    Matrix ι ι ℝ :=
  RicM - κ • lovelockTraceReversedMatter m gInv g T

/-- The `m`-th pure-Lovelock emergent cosmological constant `Λ_{(m)} = ((D − 2m)/2m) λ`. -/
noncomputable def lovelockEddingtonLambda (m : ℕ) (lam : ℝ) : ℝ :=
  (((Fintype.card ι : ℝ) - 2 * (m : ℝ)) / (2 * (m : ℝ))) * lam

/-- **The pure-Lovelock affine first integral gives the pure-Lovelock field equation**: for `m ≠ 0`,
`dim ≠ 2m`, `g^{-1}g = 1`, and `g^{ab}(RicM)_{ab} = m L`, the first integral
`lovelockAffineTensor m = λ g` yields `RicM − (L/2) g + Λ_{(m)} g = κ T` with
`Λ_{(m)} = lovelockEddingtonLambda m λ`. The `m = 1` case is `firstIntegral_derives_einsteinLambda`. -/
theorem lovelockFirstIntegral_derives_fieldEquation
    (m : ℕ) (hm : m ≠ 0)
    (RicM gInv g T : Matrix ι ι ℝ) (L κ lam : ℝ)
    (hdim : (Fintype.card ι : ℝ) ≠ 2 * (m : ℝ))
    (hgInv : gInv * g = 1)
    (htraceRic : metricTrace gInv RicM = (m : ℝ) * L)
    (hfirst : lovelockAffineTensor m RicM gInv g T κ = lam • g) :
    RicM - (L / 2) • g +
        lovelockEddingtonLambda (ι := ι) m lam • g =
      κ • T := by
  have hRic :
      RicM = κ • T +
        (lam - κ * metricTrace gInv T /
          ((Fintype.card ι : ℝ) - 2 * (m : ℝ))) • g := by
    unfold lovelockAffineTensor lovelockTraceReversedMatter at hfirst
    ext i j
    have hij := congrFun (congrFun hfirst i) j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul] at hij ⊢
    linear_combination hij
  have hden :
      (Fintype.card ι : ℝ) - 2 * (m : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hdim
  have hscalar :
      (m : ℝ) * L =
        (Fintype.card ι : ℝ) * lam -
          2 * (m : ℝ) * κ * metricTrace gInv T /
            ((Fintype.card ι : ℝ) - 2 * (m : ℝ)) := by
    rw [← htraceRic, hRic]
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ, (Fintype.card ι : ℝ) - 2 * (m : ℝ) = D := ⟨_, rfl⟩
    rw [hDdef] at hden ⊢
    simp only [metricTrace, Matrix.mul_add, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, hgInv, Matrix.trace_one, smul_eq_mul]
    field_simp [hden]
    subst hDdef
    ring
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h2m : (2 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hmR
  have hL : L = ((Fintype.card ι : ℝ) * lam -
      2 * (m : ℝ) * κ * metricTrace gInv T / ((Fintype.card ι : ℝ) - 2 * (m : ℝ))) / (m : ℝ) := by
    rw [eq_div_iff hmR]; linarith [hscalar]
  rw [hRic, hL]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  unfold lovelockEddingtonLambda
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, (Fintype.card ι : ℝ) - 2 * (m : ℝ) = D := ⟨_, rfl⟩
  rw [hDdef] at hden ⊢
  field_simp [hden, hmR, h2m]
  linear_combination (-(D * lam * g i j)) * hDdef

end Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral

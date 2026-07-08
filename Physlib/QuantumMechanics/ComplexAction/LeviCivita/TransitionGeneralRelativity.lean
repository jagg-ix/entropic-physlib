/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates

/-!
# Transition to general relativity: from the Euclidean `ds²` to an a priori arbitrary metric

Formalizes Levi-Civita's **§5 "Transition to general relativity"** (arXiv:physics/9906004). Having
referred the energy tensor to arbitrary co-ordinates (`LeviCivita.ArbitraryCoordinates`, the congruence
`JᵀMJ`) while still assuming a Euclidean (flat) `ds²`, the transition to general relativity takes `ds²`
to be **a priori arbitrary** (a genuinely curved metric `g`), subject to two conditions:

* **(a) the signature conditions (Eq. 5)** `g₀₀ > 0` and `gᵢᵢ < 0` (`physicalSignature`), so that `x₀` can
  be interpreted as time and `x₁, x₂, x₃` as space co-ordinates;
* **(b) the local mechanical interpretation is preserved** at infinitesimal scale, so the energy tensor
  is **uniquely defined through the physical ratios** (Eq. of §3, §5)

  `T_ki/√(gᵢᵢg_kk)` (stress, `stressRatio`),  `T_0i/√(−g₀₀gᵢᵢ)` (force/energy-flow, `forceRatio`),
  `T₀₀/g₀₀` (energy density, `energyDensityRatio`).

Under condition (a) these ratios are **well-defined** — the radicands and denominators are positive
(`physicalSignature_ratios_wellDefined`): `gᵢᵢg_kk > 0` and `−g₀₀gᵢᵢ > 0` because the space-space metric
entries are negative, and `g₀₀ > 0`. This is exactly what the signature conditions buy.

The **flat (Euclidean) metric is the trivial case** of the transition: the Minkowski metric `η`
(`minkowskiMatrix`, `η₀₀ = 1`, `ηᵢᵢ = −1`) satisfies the signature conditions
(`minkowski_physicalSignature`), and on it the physical ratios reduce **exactly to the bare
special-relativistic energy-tensor components** `T_ik` of §2–§3 (`stressRatio_minkowski`,
`forceRatio_minkowski`, `energyDensityRatio_minkowski`): `√(ηᵢᵢη_kk) = √((−1)(−1)) = 1`,
`√(−η₀₀ηᵢᵢ) = 1`, `η₀₀ = 1`. So the locally-measured stress, force, and energy density — which in special
relativity *are* the bare tensor components — become the metric ratios in general relativity, agreeing at
infinitesimal scale. The curved `ds²` is the arbitrary-coordinate metric `g = coordCongruence E η`
(`LeviCivita.ArbitraryCoordinates`) of the previous section, now taken as fundamental form.

* **§A — the signature conditions and well-definedness of the ratios** (`physicalSignature`, `stressRatio`,
  `forceRatio`, `energyDensityRatio`, `physicalSignature_ratios_wellDefined`,
  `minkowski_physicalSignature`).
* **§B — the flat case: the ratios reduce to the bare special-relativistic components**
  (`stressRatio_minkowski`, `forceRatio_minkowski`, `energyDensityRatio_minkowski`).
* **§C — the transition assembled** (`leviCivita_transition_to_general_relativity`).

## References

* T. Levi-Civita (arXiv:physics/9906004, §5, Eq. 5): transition to general relativity, the a priori
  arbitrary `ds²` and the energy tensor via the metric ratios. structures:
  `LeviCivita.ArbitraryCoordinates` (`coordCongruence`), `Physlib.Relativity.MinkowskiMatrix`
  (`minkowskiMatrix`, `inl_0_inl_0`, `inr_i_inr_i`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.TransitionGeneralRelativity

variable {d : ℕ}

/-! ## §A — the signature conditions (Eq. 5) and the physical energy-tensor ratios -/

/-- **[The signature conditions, Eq. 5] `g₀₀ > 0 ∧ gᵢᵢ < 0`.** The condition for the transition to general
relativity: `x₀` is time-like (`g₀₀ > 0`) and the `xᵢ` are space-like (`gᵢᵢ < 0`), so that the metric `g`
admits the local mechanical interpretation of a physical space-time. -/
def physicalSignature (g : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) : Prop :=
  0 < g (Sum.inl 0) (Sum.inl 0) ∧ ∀ i : Fin d, g (Sum.inr i) (Sum.inr i) < 0

/-- **The stress ratio** `T_ki/√(gᵢᵢg_kk)` — the orthogonal stress component along the line `xᵢ` of the
stress on a surface element normal to `x_k` (Levi-Civita §3, §5). -/
def stressRatio (T g : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (i k : Fin d) : ℝ :=
  T (Sum.inr i) (Sum.inr k) / Real.sqrt (g (Sum.inr i) (Sum.inr i) * g (Sum.inr k) (Sum.inr k))

/-- **The force / energy-flow ratio** `T_0i/√(−g₀₀gᵢᵢ)` — the component of the force `f` (energy flow)
along the line `xᵢ` (Levi-Civita §3, §5). -/
def forceRatio (T g : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (i : Fin d) : ℝ :=
  T (Sum.inl 0) (Sum.inr i) /
    Real.sqrt (-(g (Sum.inl 0) (Sum.inl 0)) * g (Sum.inr i) (Sum.inr i))

/-- **The energy-density ratio** `T₀₀/g₀₀` — the density of the energy distribution in the space
`(x₁, x₂, x₃)` (Levi-Civita §3, §5). -/
def energyDensityRatio (T g : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) : ℝ :=
  T (Sum.inl 0) (Sum.inl 0) / g (Sum.inl 0) (Sum.inl 0)

/-- **[The signature conditions make the ratios well-defined].** Under Eq. 5 the radicands and denominator
of the physical ratios are positive: `gᵢᵢg_kk > 0` (negative × negative), `−g₀₀gᵢᵢ > 0` (`−g₀₀ < 0` times
`gᵢᵢ < 0`), and `g₀₀ > 0`. So on any a priori arbitrary metric satisfying the signature conditions, the
locally-measured stress, force, and energy density are genuine real quantities. -/
theorem physicalSignature_ratios_wellDefined (g : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (hg : physicalSignature g) (i k : Fin d) :
    0 < g (Sum.inr i) (Sum.inr i) * g (Sum.inr k) (Sum.inr k)
      ∧ 0 < -(g (Sum.inl 0) (Sum.inl 0)) * g (Sum.inr i) (Sum.inr i)
      ∧ 0 < g (Sum.inl 0) (Sum.inl 0) :=
  ⟨mul_pos_of_neg_of_neg (hg.2 i) (hg.2 k),
    mul_pos_of_neg_of_neg (by linarith [hg.1]) (hg.2 i), hg.1⟩

/-- **[The flat metric satisfies the signature conditions] `η₀₀ = 1 > 0`, `ηᵢᵢ = −1 < 0`.** The Minkowski
metric of special relativity is the trivial case of the transition. -/
theorem minkowski_physicalSignature :
    physicalSignature (minkowskiMatrix : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :=
  ⟨by rw [minkowskiMatrix.inl_0_inl_0]; norm_num,
    fun i => by rw [minkowskiMatrix.inr_i_inr_i]; norm_num⟩

/-! ## §B — the flat case: the ratios reduce to the bare special-relativistic components -/

/-- **[Flat stress ratio is the bare component] `T_ki/√(ηᵢᵢη_kk) = T_ki`.** On the Minkowski metric,
`√((−1)(−1)) = 1`, so the stress ratio is the bare special-relativistic stress component `T_ik` of §2. -/
theorem stressRatio_minkowski (T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (i k : Fin d) :
    stressRatio T minkowskiMatrix i k = T (Sum.inr i) (Sum.inr k) := by
  rw [stressRatio, minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.inr_i_inr_i,
    show ((-1 : ℝ) * (-1)) = 1 by norm_num, Real.sqrt_one, div_one]

/-- **[Flat force ratio is the bare component] `T_0i/√(−η₀₀ηᵢᵢ) = T_0i`.** On the Minkowski metric,
`√(−1·−1) = 1`, so the force ratio is the bare special-relativistic force/energy-flow component `T_0i`. -/
theorem forceRatio_minkowski (T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (i : Fin d) :
    forceRatio T minkowskiMatrix i = T (Sum.inl 0) (Sum.inr i) := by
  rw [forceRatio, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    show (-(1 : ℝ) * (-1)) = 1 by norm_num, Real.sqrt_one, div_one]

/-- **[Flat energy-density ratio is the bare component] `T₀₀/η₀₀ = T₀₀`.** On the Minkowski metric
`η₀₀ = 1`, so the energy-density ratio is the bare special-relativistic energy density `T₀₀`. -/
theorem energyDensityRatio_minkowski (T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    energyDensityRatio T minkowskiMatrix = T (Sum.inl 0) (Sum.inl 0) := by
  rw [energyDensityRatio, minkowskiMatrix.inl_0_inl_0, div_one]

/-! ## §C — the transition assembled -/

/-- **[Transition to general relativity, assembled].** For any energy tensor `T`:

* the flat (Euclidean) metric `η` satisfies the signature conditions Eq. 5 (`x₀` time, `xᵢ` space) — the
  trivial case of the transition;
* on `η` the physical ratios — the stress `T_ki/√(ηᵢᵢη_kk)`, the force `T_0i/√(−η₀₀ηᵢᵢ)`, and the energy
  density `T₀₀/η₀₀` — reduce **exactly to the bare special-relativistic energy-tensor components** `T_ik`.

So the transition to general relativity replaces the Euclidean `ds²` with an a priori arbitrary metric `g`
(the curved fundamental form `g = coordCongruence E η` of the arbitrary-coordinates section) subject to the
signature conditions; the locally-measured stress, force, and energy density — bare tensor components in
special relativity — become the metric ratios, agreeing with special relativity at infinitesimal scale. -/
theorem leviCivita_transition_to_general_relativity
    (T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (i k : Fin d) :
    physicalSignature (minkowskiMatrix : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
      ∧ stressRatio T minkowskiMatrix i k = T (Sum.inr i) (Sum.inr k)
      ∧ forceRatio T minkowskiMatrix i = T (Sum.inl 0) (Sum.inr i)
      ∧ energyDensityRatio T minkowskiMatrix = T (Sum.inl 0) (Sum.inl 0) :=
  ⟨minkowski_physicalSignature, stressRatio_minkowski T i k, forceRatio_minkowski T i,
    energyDensityRatio_minkowski T⟩

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.TransitionGeneralRelativity

end

end

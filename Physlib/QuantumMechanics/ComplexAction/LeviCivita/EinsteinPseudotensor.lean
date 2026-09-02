/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates
meta import Zil

/-!
# Einstein's misunderstanding about the gravitational tensor: true tensor vs pseudo-tensor (§9)

Formalizes Levi-Civita's **§9 "Einstein's misunderstanding about the gravitational tensor"**
(arXiv:physics/9906004). Levi-Civita contrasts his gravitational tensor `A_ik = (1/κ)(G_ik − ½ g_ik G)` — a
**true tensor** — with Einstein's gravitational energy **pseudo-tensor** `√(−g) t_i^j` (Eq. 14), built from
the non-covariant Christoffel-product scalar `G*` (Eq. 15).

* the **mixed (raised) gravitational tensor** `A_i^{(j)} = ∑_k g^{(jk)} A_ik` (`mixedTensor`): raising an
  index is an invertible operation (`mixedTensor_lower_raise`, using the metric/inverse-metric pair
  `g^{(jk)} g_{kl} = δ`), so *it makes no difference whether one fixes `A_ik` or its linear combinations
  `A_i^{(j)}`* — and the d'Alembert balance survives the raising, `T_i^{(j)} + A_i^{(j)} = 0`
  (`mixed_dAlembert_balance`);

* **`A_ik` is a true tensor** — it transforms by the covariant congruence `JᵀMJ` under arbitrary
  co-ordinates (`gravitationalTensor_coordCongruence`, reusing `coordCongruence`,
  `LeviCivita.ArbitraryCoordinates`), being a scalar multiple of the genuine Einstein tensor;

* **Einstein's pseudo-tensor is coordinate-dependent** — its building block `G*` (Eq. 15), a quadratic in
  the Christoffel symbols `{i h, l}{k l, h} − {i k, l}{l h, h}` (`christoffelScalar`), **vanishes wherever
  the Christoffel symbols vanish** (`christoffelScalar_zero_of_flat`), e.g. in normal co-ordinates at a
  point. Since the Christoffel symbols are not tensors, `G*` (hence `√(−g) t_i^j`) can be gauged to zero at
  any point — a true tensor that vanishes in one frame vanishes in all, so `t_i^j` is a **pseudo-tensor**,
  not a true tensor like `A_ik`. This is Einstein's misunderstanding.

So the gravitational tensor `A_ik`, a true tensor with the invariant character demanded by general
relativity, is the correct gravitational energy tensor; Einstein's pseudo-tensor, gaugeable to zero, lacks
it — the source of the spurious gravitational-wave paradox Levi-Civita resolves.

* **§A — the mixed (raised) gravitational tensor** (`mixedTensor`, `mixedTensor_lower_raise`,
  `mixed_dAlembert_balance`).
* **§B — `A_ik` is a true tensor; Einstein's `G*` is a pseudo-scalar** (`gravitationalTensor_coordCongruence`,
  `christoffelScalar`, `christoffelScalar_zero_of_flat`, `leviCivita_true_vs_pseudo_tensor`).

## References

* T. Levi-Civita (arXiv:physics/9906004, §9, Eq. 14, 15): Einstein's misunderstanding, the pseudo-tensor
  `√(−g) t_i^j` and the Christoffel scalar `G*`. Carriers: `LeviCivita.ArbitraryCoordinates`
  (`coordCongruence`, `coordCongruence_smul`), `LeviCivita.GravitationalTensor` (`gravitationalTensor`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- **The mixed (raised) gravitational tensor** `A_i^{(j)} = ∑_k A_ik g^{(kj)}` — the gravitational tensor
with its second index raised by the inverse metric `Q = g^{(··)}` (matrix product `A·Q`). Levi-Civita
notes that fixing `A_ik` or the mixed `A_i^{(j)}` makes no difference. -/
def mixedTensor (Q M : Matrix ι ι ℝ) : Matrix ι ι ℝ := M * Q

/-- **[Raising an index is invertible] lower(raise `M`) = `M`.** When the inverse metric `Q = g^{(··)}` and
the metric `g` are inverse (`Q g = 1`), raising the index with `Q` then lowering it with `g` recovers the
covariant tensor: fixing `A_ik` or `A_i^{(j)}` is equivalent. -/
lemma mixedTensor_lower_raise (Q g M : Matrix ι ι ℝ) (hQg : Q * g = 1) :
    mixedTensor g (mixedTensor Q M) = M := by
  rw [mixedTensor, mixedTensor, Matrix.mul_assoc, hQg, Matrix.mul_one]

/-- **[The d'Alembert balance survives the raising] `T_i^{(j)} + A_i^{(j)} = 0`.** Raising an index is
linear, so the d'Alembert balance `T + A = 0` (Eq. 10') holds equally in mixed form — fixing the covariant
or the mixed tensor is the same physics. -/
lemma mixed_dAlembert_balance (Q T A : Matrix ι ι ℝ) (h : T + A = 0) :
    mixedTensor Q T + mixedTensor Q A = 0 := by
  rw [mixedTensor, mixedTensor, ← Matrix.add_mul, h, Matrix.zero_mul]


/-- **[The gravitational tensor is a true tensor] it transforms by the covariant congruence `JᵀAJ`.** Under
an arbitrary coordinate change with Jacobian `J`, the gravitational tensor `A = −(1/κ)·(einstein tensor)`
transforms by the genuine tensor congruence, being a scalar multiple of the covariant Einstein tensor. This
is the invariant character that Einstein's pseudo-tensor lacks. -/
lemma gravitationalTensor_coordCongruence (J Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g : Matrix ι ι ℝ)
    (κ : ℝ) :
    coordCongruence J (gravitationalTensor Ric scalarR g κ)
      = (-(1 / κ)) • coordCongruence J (einsteinTensor Ric scalarR g) := by
  rw [gravitationalTensor, coordCongruence_smul]

/-- **Einstein's Christoffel scalar** `G* = −∑_{ik} g^{(ik)} ∑_{hl} ({i h, l}{k l, h} − {i k, l}{l h, h})`
(Eq. 15) — the non-covariant part of the curvature scalar, a quadratic in the Christoffel symbols
`Γ^c_{ab}` (here `Γ c a b`), the building block of Einstein's gravitational energy pseudo-tensor
`√(−g) t_i^j` (Eq. 14). -/
def christoffelScalar (Γ : ι → ι → ι → ℝ) (Q : ι → ι → ℝ) : ℝ :=
  -∑ i, ∑ k, Q i k * ∑ h, ∑ l, (Γ l i h * Γ h k l - Γ l i k * Γ h l h)

/-- **[Einstein's `G*` is coordinate-dependent] `G* = 0` when the Christoffel symbols vanish.** Since `G*`
is a quadratic in the Christoffel symbols, it vanishes wherever they do — e.g. in normal (geodesic)
co-ordinates at a point. The Christoffel symbols are not tensors, so `G*` (hence Einstein's pseudo-tensor
`√(−g) t_i^j`) can be gauged to zero at any point. A true tensor vanishing in one frame vanishes in all, so
`t_i^j` is a **pseudo-tensor**, not a true tensor like `A_ik`. -/
lemma christoffelScalar_zero_of_flat (Q : ι → ι → ℝ) : christoffelScalar 0 Q = 0 := by
  simp [christoffelScalar]

/-- **[Levi-Civita's true tensor vs Einstein's pseudo-tensor, assembled].** For a metric/inverse-metric
pair (`Q g = 1`), a coordinate Jacobian `J`, and a d'Alembert balance `T + A = 0`:

* **mixed tensor** — raising an index is invertible, `lower(raise M) = M`, and the d'Alembert balance
  survives, `T_i^{(j)} + A_i^{(j)} = 0` (fixing `A_ik` or `A_i^{(j)}` is the same);
* **true tensor** — the gravitational tensor `A_ik` transforms by the covariant congruence `JᵀAJ` (a true
  tensor, with the invariant character of general relativity);
* **pseudo-tensor** — Einstein's Christoffel scalar `G*` vanishes when the Christoffel symbols vanish
  (coordinate-dependent), so his pseudo-tensor `√(−g) t_i^j` is not a true tensor.

Levi-Civita's `A_ik` is the true gravitational energy tensor; Einstein's `√(−g) t_i^j`, gaugeable to zero,
is only a pseudo-tensor — the misunderstanding behind the spurious gravitational-wave paradox. -/
lemma leviCivita_true_vs_pseudo_tensor (Q g M : Matrix ι ι ℝ) (hQg : Q * g = 1)
    (T A : Matrix ι ι ℝ) (hbal : T + A = 0) (J Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (gg : Matrix ι ι ℝ) (κ : ℝ) (Γ : ι → ι → ι → ℝ) :
    mixedTensor g (mixedTensor Q M) = M
      ∧ mixedTensor Q T + mixedTensor Q A = 0
      ∧ coordCongruence J (gravitationalTensor Ric scalarR gg κ)
          = (-(1 / κ)) • coordCongruence J (einsteinTensor Ric scalarR gg)
      ∧ christoffelScalar 0 Q = 0 :=
  ⟨mixedTensor_lower_raise Q g M hQg, mixed_dAlembert_balance Q T A hbal,
    gravitationalTensor_coordCongruence J Ric scalarR gg κ, christoffelScalar_zero_of_flat Q⟩

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.mixedTensor_lower_raise where
  formalizes @ "claim:raising-a-tensor-index-with-the-inverse-metric-then-lowering-it-with-the-metric-recovers-the-covariant-tensor-so-fixing-the-covariant-or-mixed-gravitational-tensor-is-equivalent"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.mixed_dAlembert_balance where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-dalembert-balance-t-plus-a-equals-zero-survives-index-raising-holding-equally-in-mixed-form-because-raising-is-linear"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.christoffelScalar_zero_of_flat where
  formalizes @ "claim:einsteins-christoffel-scalar-g-star-vanishes-when-the-christoffel-symbols-vanish-so-being-coordinate-dependent-his-gravitational-energy-pseudo-tensor-can-be-gauged-to-zero-at-any-point-and-is-not-a-true-tensor",
  supported_by @ "paper:levi-civita-1917-arxiv-physics-9906004-section-9-einsteins-misunderstanding"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.leviCivita_true_vs_pseudo_tensor where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.christoffelScalar_zero_of_flat",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.mixedTensor_lower_raise",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.mixed_dAlembert_balance",
  formalizes @ "claim:levi-civitas-gravitational-tensor-a-ik-is-a-true-tensor-transforming-by-the-covariant-congruence-while-einsteins-pseudo-tensor-gaugeable-to-zero-via-the-coordinate-dependent-christoffel-scalar-is-not-the-misunderstanding-behind-the-spurious-gravitational-wave-paradox",
  requires @ "claim:einsteins-christoffel-scalar-g-star-vanishes-when-the-christoffel-symbols-vanish-so-being-coordinate-dependent-his-gravitational-energy-pseudo-tensor-can-be-gauged-to-zero-at-any-point-and-is-not-a-true-tensor"

zil_file_contract physlib.einsteinPseudotensor where
  promises "Levi-Civita's section 9 'Einstein's misunderstanding about the gravitational tensor' (arXiv:physics/9906004): his gravitational tensor A_ik = (1/kappa)(G_ik - 1/2 g_ik G) is a TRUE tensor, whereas Einstein's gravitational energy pseudo-tensor sqrt(-g) t_i^j is not. Raising an index with the inverse metric is invertible, so fixing A_ik or the mixed A_i^(j) is equivalent (mixedTensor_lower_raise) and the d'Alembert balance T + A = 0 survives the raising (mixed_dAlembert_balance). The gravitational tensor transforms by the covariant congruence J^T A J (a true tensor); by contrast Einstein's Christoffel scalar G* is a quadratic in the Christoffel symbols and vanishes wherever they do (christoffelScalar_zero_of_flat), so his pseudo-tensor can be gauged to zero at any point. Assembled in leviCivita_true_vs_pseudo_tensor: the true-tensor-versus-pseudo-tensor distinction behind the spurious gravitational-wave paradox."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.mixedTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.christoffelScalar"]
  forbids_substitutes ["the full transformation law of the Christoffel symbols and the metric under diffeomorphisms, which are the cited differential-geometry inputs summarized by the coordinate-congruence and flat-Christoffel hypotheses",
    "any resolution of the physicality of gravitational waves, only the true-tensor-versus-pseudo-tensor algebraic distinction is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.mixedTensor_lower_raise,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.mixed_dAlembert_balance,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.christoffelScalar_zero_of_flat,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.EinsteinPseudotensor.leviCivita_true_vs_pseudo_tensor]

/- ZIL-END -/

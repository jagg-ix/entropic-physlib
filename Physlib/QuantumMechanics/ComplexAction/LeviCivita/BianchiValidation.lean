/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

/-!
# Formal validation derived from the Bianchi identities (both identities)

Formalizes Levi-Civita's **§7 "Formal validation derived from the Bianchi identities"**
(arXiv:physics/9906004). Both Bianchi identities of the Riemann symbols `g_{ij,hk}` (`riem`) enter the
validation of the gravitational field equations `G_ik − ½ g_ik G = −κ T_ik` (Eq. 10):

* the **first (algebraic) Bianchi identity** `R_{ijkl} + R_{iklj} + R_{iljk} = 0` (cyclic, the "well known
  properties of the Riemann symbols" Levi-Civita invokes) — together with the antisymmetry of the second
  index pair `R_{ijkl} = −R_{ijlk}` and the symmetry of the inverse metric `g^{(jl)}` — forces the two
  metric contractions of the Riemann tensor to coincide up to sign,
  `∑_{jl} g^{(jl)} R_{ijkl} + ∑_{jl} g^{(jl)} R_{iljk} = 0` (`firstBianchi_ricci_relation`): the algebraic
  identity is what makes the Ricci tensor (hence the symmetric Einstein tensor) well-defined;

* the **second (contracted differential) Bianchi identity** is, after the double contraction `½ g^{(kl)}
  g^{(jh)}` of §7, exactly Levi-Civita's **Eq. 12** `∑_{kl} g^{(kl)} G_{ikl} − ½ G_i = 0`
  (`contractedSecondBianchi`), the vanishing divergence of the Einstein tensor `G_ik − ½ g_ik G`
  (`einsteinDivergence_eq_zero_iff`).

This is the **formal validation** of the field equations: the right-hand side `−κ T_ik` of Eq. 10 has
vanishing divergence (an isolated system is conserved), so if no further condition is imposed on `ds²`, the
divergence of the left-hand side must *identically* vanish — which is exactly Eq. 12. Conversely, given Eq.
12 and the field equation, the matter stress-energy is conserved `∇^μ T_{μν} = 0`
(`bianchi_validates_fieldEquation`): the second Bianchi identity guarantees the consistency of `G = −κT`
with `∇T = 0`.

* **§A — the first (algebraic) Bianchi identity and the Ricci contraction** (`FirstBianchi`,
  `firstBianchi_ricci_relation`).
* **§B — the contracted second Bianchi (Eq. 12) and the validation** (`contractedSecondBianchi`,
  `einsteinDivergence`, `einsteinDivergence_eq_zero_iff`, `bianchi_validates_fieldEquation`).
* **§C — the formal validation assembled** (`leviCivita_formal_validation`).

## References

* T. Levi-Civita (arXiv:physics/9906004, §7, Eq. 12): formal validation from the Bianchi identities, the
  vanishing divergence of `G_ik − ½ g_ik G`. structures: `LeviCivita.GravitationalTensor` (`gravitationalTensor`,
  the d'Alembert balance), `ComplexEinstein.EinsteinFieldEquationsPhysLean` (`bianchi_implies_conservation`); cf.
  `BCJDoubleCopy.SecondBianchiConservation` (the gauge-side first Bianchi / kinematic Jacobi).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## §A — the first (algebraic) Bianchi identity and the Ricci contraction -/

/-- **The first (algebraic) Bianchi identity** `R_{ijkl} + R_{iklj} + R_{iljk} = 0` — the cyclic identity
of the Riemann symbols (cyclic in the last three indices). -/
def FirstBianchi (R : ι → ι → ι → ι → ℝ) : Prop :=
  ∀ a b c d, R a b c d + R a c d b + R a d b c = 0

/-- **[The first Bianchi identity relates the two Ricci contractions] `∑ g^{(jl)}R_{ijkl} + ∑
g^{(jl)}R_{iljk} = 0`.** With the inverse metric `Q = g^{(jl)}` symmetric and the Riemann symbols
antisymmetric in their second index pair (`R_{ijkl} = −R_{ijlk}`), summing the first Bianchi identity
against `Q` makes the middle term vanish (symmetric × antisymmetric) and ties the two surviving metric
contractions of the Riemann tensor together. The algebraic Bianchi identity is what makes the Ricci tensor
— hence the symmetric Einstein tensor `G_ik − ½ g_ik G` of Eq. 10 — well-defined. -/
theorem firstBianchi_ricci_relation {R : ι → ι → ι → ι → ℝ} {Q : ι → ι → ℝ}
    (hQ : ∀ a b, Q a b = Q b a) (hAnti : ∀ a b c d, R a b c d = -R a b d c)
    (hFB : FirstBianchi R) (i k : ι) :
    (∑ j, ∑ l, Q j l * R i j k l) + (∑ j, ∑ l, Q j l * R i l j k) = 0 := by
  -- the middle contraction `∑ Q j l R_{iklj}` vanishes (symmetric metric × antisymmetric pair)
  have hmid : (∑ j, ∑ l, Q j l * R i k l j) = 0 := by
    have hswap : (∑ j, ∑ l, Q j l * R i k l j) = ∑ j, ∑ l, Q j l * R i k j l := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by rw [hQ y x]))
    have hzero : (∑ j, ∑ l, Q j l * R i k l j) + (∑ j, ∑ l, Q j l * R i k j l) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero; intro j _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero; intro l _
      rw [hAnti i k l j]; ring
    rw [← hswap] at hzero
    linarith [hzero]
  -- the full contraction of the first Bianchi identity splits into the three Ricci contractions
  have hsum : (∑ j, ∑ l, Q j l * R i j k l) + (∑ j, ∑ l, Q j l * R i k l j)
      + (∑ j, ∑ l, Q j l * R i l j k) = 0 := by
    have h0 : (∑ j, ∑ l, (Q j l * R i j k l + Q j l * R i k l j + Q j l * R i l j k)) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      apply Finset.sum_eq_zero; intro l _
      linear_combination Q j l * hFB i j k l
    simpa only [Finset.sum_add_distrib] using h0
  rw [hmid, add_zero] at hsum
  exact hsum

/-! ## §B — the contracted second Bianchi (Eq. 12) and the validation -/

/-- **The Einstein-tensor divergence vector** `∑_{kl} g^{(kl)} G_{ikl} − ½ G_i` — the divergence of
`G_ik − ½ g_ik G`, the left-hand side of Levi-Civita's Eq. 12, built from the divergence of the Ricci
tensor `divRicci_i = ∑_{kl} g^{(kl)} ∇_l G_ik` and the gradient of the scalar curvature `gradScalar_i = ∇_i G`. -/
noncomputable def einsteinDivergence (divRicci gradScalar : ι → ℝ) : ι → ℝ :=
  divRicci - (1 / 2 : ℝ) • gradScalar

/-- **The contracted second Bianchi identity (Eq. 12)** `∑_{kl} g^{(kl)} G_{ikl} = ½ G_i` — the twice-traced
differential Bianchi identity of §7, equivalently the vanishing divergence of the Einstein tensor. -/
def contractedSecondBianchi (divRicci gradScalar : ι → ℝ) : Prop :=
  divRicci = (1 / 2 : ℝ) • gradScalar

/-- **[The contracted second Bianchi identity is the vanishing Einstein divergence] Eq. 12 ⟺ `∇(G−½gG) = 0`.**
Levi-Civita's Eq. 12 `∑ g^{(kl)}G_{ikl} − ½ G_i = 0` is exactly the statement that the divergence of the
Einstein tensor `G_ik − ½ g_ik G` vanishes. -/
theorem einsteinDivergence_eq_zero_iff (divRicci gradScalar : ι → ℝ) :
    einsteinDivergence divRicci gradScalar = 0 ↔ contractedSecondBianchi divRicci gradScalar := by
  rw [einsteinDivergence, contractedSecondBianchi, sub_eq_zero]

/-- **[Formal validation of the field equations] the second Bianchi identity gives `∇^μ T_{μν} = 0`.** Given
the Einstein field equation `G_ik − ½ g_ik G = −κ T_ik` (Eq. 10, in divergence form `∇(G−½gG) = −κ ∇T`,
`κ ≠ 0`) and the contracted second Bianchi identity (Eq. 12, the divergence of the left-hand side vanishes),
the matter stress-energy is conserved `∇^μ T_{μν} = 0`. This is the formal validation of §7: the divergence
of the right-hand side of Eq. 10 vanishes, hence so must that of the left-hand side — which is Eq. 12. -/
theorem bianchi_validates_fieldEquation (divRicci gradScalar divT : ι → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) : divT = 0 := by
  rw [← einsteinDivergence_eq_zero_iff] at hBianchi
  rw [hBianchi] at hField
  rcases smul_eq_zero.mp hField.symm with h | h
  · exact absurd (neg_eq_zero.mp h) hκ
  · exact h

/-! ## §C — the formal validation assembled -/

/-- **[Formal validation derived from the Bianchi identities, assembled].** For Riemann symbols `R` with a
symmetric inverse metric `Q`, antisymmetric second index pair, and the **first (algebraic) Bianchi
identity**, together with the **contracted second (differential) Bianchi identity** (Eq. 12) and the
Einstein field equation `G − ½gG = −κT` (`κ ≠ 0`):

* **first Bianchi** — the two Ricci contractions of `R` are tied together,
  `∑ g^{(jl)}R_{ijkl} + ∑ g^{(jl)}R_{iljk} = 0` (the algebraic identity makes the Einstein tensor
  well-defined);
* **second Bianchi (Eq. 12)** — the divergence of the Einstein tensor `G − ½gG` vanishes;
* **validation** — the matter stress-energy is conserved, `∇^μ T_{μν} = 0`.

The two Bianchi identities formally validate the gravitational field equations: the algebraic one makes the
Einstein tensor a well-defined symmetric tensor, the differential one makes it divergence-free, consistent
with the conserved matter source. -/
theorem leviCivita_formal_validation {R : ι → ι → ι → ι → ℝ} {Q : ι → ι → ℝ}
    (hQ : ∀ a b, Q a b = Q b a) (hAnti : ∀ a b c d, R a b c d = -R a b d c) (hFB : FirstBianchi R)
    (divRicci gradScalar divT : ι → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) (i k : ι) :
    ((∑ j, ∑ l, Q j l * R i j k l) + (∑ j, ∑ l, Q j l * R i l j k) = 0)
      ∧ einsteinDivergence divRicci gradScalar = 0
      ∧ divT = 0 :=
  ⟨firstBianchi_ricci_relation hQ hAnti hFB i k,
    (einsteinDivergence_eq_zero_iff divRicci gradScalar).mpr hBianchi,
    bianchi_validates_fieldEquation divRicci gradScalar divT κ hκ hField hBianchi⟩

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

end

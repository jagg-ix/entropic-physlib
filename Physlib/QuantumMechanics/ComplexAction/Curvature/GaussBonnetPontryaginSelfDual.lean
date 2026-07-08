/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination
public import Physlib.QuantumMechanics.ComplexAction.PenroseTwistorSpace
public import Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge

/-!
# Gauss–Bonnet and Pontryagin: the four-dimensional topological terms, and the self-dual link to twistors

The final remark of D. Lovelock, *The Einstein Tensor and Its Generalizations* (J. Math. Phys. **12**
(1971) 498, p. 501): in four dimensions the most general scalar Lagrangian `L(g, ∂g, ∂²g)` has the
Euler–Lagrange expression

 `g^{½}(α + β δ^{ij}_{ab}R_{ij}^{ab} + γ δ^{ijkl}_{abcd}R_{ij}^{ab}R_{kl}^{cd}) + μ R_{ijkl}*R^{ijkl}`,

i.e. **four** terms: the cosmological `α`, the Einstein–Hilbert `β` (giving `G^{ij}`), the **Gauss–Bonnet**
`γ` (the parity-even Euler density), and the **Pontryagin** `μ` (`R*R`, the parity-odd density built with
the dual). The first two are dynamical (`aG + bg`, `LovelockDimensionalTermination.lovelock_dim4_…`);
the last two are **topological** — total derivatives in four dimensions.

Both topological terms are quadratic in the curvature two-form, and split cleanly under the **Hodge dual**
into self-dual (`C⁺`) and anti-self-dual (`C⁻`) parts: with `s = |C⁺|²`, `a = |C⁻|²`,

 Gauss–Bonnet (Euler) `= s + a`, Pontryagin `= s − a`.

The self-dual sector is one `SL(2,ℂ)` chirality — the *same* `SL(2,ℂ)` that acts on Penrose twistor
space (`PenroseTwistorSpace`). Its principal null direction is a point of the Riemann sphere `CP¹`,
transformed by the boundary Möbius action, exactly like a twistor's direction.

* **§A — the four `4`D terms.** `FourDGravitationalTerm` (cosmological/Einstein/Gauss–Bonnet/Pontryagin);
 `fourD_term_count` (`= 4`), `fourD_dynamical_count` (`= 2`, the field-equation terms `aG + bg`).
* **§B — the self-dual decomposition.** `gaussBonnetDensity s a = s + a`, `pontryaginDensity s a = s − a`;
 `gaussBonnet_add_pontryagin`/`_sub_pontryagin` (`= 2s` / `2a`); `selfDual_gaussBonnet_eq_pontryagin`
 (a self-dual gravitational instanton `a = 0` has Euler `=` Pontryagin); `pontryagin_parity_odd`,
 `gaussBonnet_parity_even`.
* **§C — the link to twistor space.** `selfDualPrincipalDirection χ = weylRatio χ = ` the
 `PenroseTwistorSpace.twistorDirection` of a twistor with `π = χ` (`selfDual_eq_twistorDirection`); under
 `SL(2,ℂ)` it moves by the same boundary Möbius map (`selfDual_direction_sl2c`).
* **§D — the Euler–signature inequality.** `|Pontryagin| ≤ Euler` (`abs_pontryagin_le_gaussBonnet`, the
 bound `χ ≥ |τ|`), saturated exactly by (anti-)self-dual instantons (`abs_pontryagin_eq_gaussBonnet_iff`,
 `selfDual_saturates_bound`).
* **§E — the light-cone / repo links.** `gaussBonnet_sq_sub_pontryagin_sq` (`Euler² − Pontryagin² =
 4|C⁺|²|C⁻|²`, the same `(2,2)` structure as `PenroseTwistorSpace.twistorNorm`);
 `gaussBonnet_sq_eq_pontryagin_sq_iff` (saturation = the "null" case, `PenroseTwistorSpace.IsNullTwistor`
 analogue); `selfDual_instanton_twistorDirection` (a self-dual instanton is twistor data). The Euler
 density is the contraction of the double-dual `Curvature.MoulinDoubleDualCotton.doubleDualRiemann`.
* **§F — parity link to the Deser topological mass.** `pontryagin_parity_sign_eq_topologicalMass` (the
 Pontryagin transforms under parity by `TopologicallyMassiveGauge.massSignParity = −1`, exactly like the
 Chern–Simons topological mass — both parity-odd); `gaussBonnet_parity_ne_topologicalMass` (Gauss–Bonnet
 is parity-even, the opposite behaviour).

Proven: the enumeration and dynamical count of the four terms; the exact self-dual
algebra of Euler/Pontryagin and its parity; and that the self-dual principal direction is a twistor
direction transforming by the twistor `SL(2,ℂ)` Möbius action. Interpretive: identifying `s`, `a` with
`|C⁺|²`, `|C⁻|²` of the Weyl two-form, and `χ` with the principal spinor of the self-dual Weyl tensor, is
the standard spinor/twistor dictionary (the Weyl tensor itself is not formalized).

## References

* D. Lovelock, J. Math. Phys. **12** (1971) 498 (p. 501, the four-term `4`D Lagrangian). Links
 `LovelockDimensionalTermination` and `PenroseTwistorSpace` (`twistorDirection`, `sl2c_weylRatio`).

No additional assumptions.
-/

set_option autoImplicit false

open scoped MatrixGroups
open OnePoint
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.GaussBonnetPontryaginSelfDual

/-! ## §A — the four four-dimensional gravitational Lagrangian terms (Lovelock p. 501) -/

/-- **The four `4`D gravitational Lagrangian terms** (Lovelock's final remark): the cosmological `α`, the
Einstein–Hilbert `β`, the Gauss–Bonnet `γ`, and the Pontryagin `μ`. -/
inductive FourDGravitationalTerm
  /-- The cosmological constant term `α` (the metric). -/
  | cosmological
  /-- The Einstein–Hilbert term `β` (the scalar curvature `R`, giving the Einstein tensor). -/
  | einstein
  /-- The Gauss–Bonnet term `γ` (the parity-even Euler density, topological in `4`D). -/
  | gaussBonnet
  /-- The Pontryagin term `μ` (`R*R`, the parity-odd density, topological in `4`D). -/
  | pontryagin
  deriving DecidableEq, Fintype

/-- **Whether a `4`D term contributes to the field equations**: the cosmological and Einstein terms are
dynamical; the Gauss–Bonnet and Pontryagin terms are topological (total derivatives). -/
def isDynamical : FourDGravitationalTerm → Bool
  | .cosmological => true
  | .einstein => true
  | .gaussBonnet => false
  | .pontryagin => false

/-- **There are exactly four `4`D gravitational Lagrangian terms.** -/
theorem fourD_term_count : Fintype.card FourDGravitationalTerm = 4 := by decide

/-- **Exactly two of them are dynamical** — the cosmological and Einstein terms, giving the field
equations `aG^{ij} + bg^{ij}`; the other two are topological. -/
theorem fourD_dynamical_count :
    (Finset.univ.filter (fun t => isDynamical t)).card = 2 := by decide

/-! ## §B — the self-dual decomposition of the topological densities -/

/-- **The Gauss–Bonnet (Euler) density** `= |C⁺|² + |C⁻|²`: the sum of the self-dual and anti-self-dual
squared norms of the Weyl two-form. -/
def gaussBonnetDensity (s a : ℝ) : ℝ := s + a

/-- **The Pontryagin density** `R*R = |C⁺|² − |C⁻|²`: the *difference* of the self-dual and anti-self-dual
squared norms. -/
def pontryaginDensity (s a : ℝ) : ℝ := s - a

/-- **Euler `+` Pontryagin `= 2|C⁺|²`.** -/
theorem gaussBonnet_add_pontryagin (s a : ℝ) :
    gaussBonnetDensity s a + pontryaginDensity s a = 2 * s := by
  unfold gaussBonnetDensity pontryaginDensity; ring

/-- **Euler `−` Pontryagin `= 2|C⁻|²`.** -/
theorem gaussBonnet_sub_pontryagin (s a : ℝ) :
    gaussBonnetDensity s a - pontryaginDensity s a = 2 * a := by
  unfold gaussBonnetDensity pontryaginDensity; ring

/-- **A self-dual gravitational instanton has Euler `=` Pontryagin** (`a = |C⁻|² = 0`): its Euler number
and signature coincide (up to normalization) — the instanton `χ = |τ|` relation. -/
theorem selfDual_gaussBonnet_eq_pontryagin (s a : ℝ) (h : a = 0) :
    gaussBonnetDensity s a = pontryaginDensity s a := by
  unfold gaussBonnetDensity pontryaginDensity; rw [h]; ring

/-- **Pontryagin is parity-odd**: swapping the self-dual and anti-self-dual parts (a parity/orientation
reversal) flips its sign. -/
theorem pontryagin_parity_odd (s a : ℝ) :
    pontryaginDensity a s = -pontryaginDensity s a := by
  unfold pontryaginDensity; ring

/-- **Gauss–Bonnet (Euler) is parity-even**: it is unchanged by swapping the self-dual and anti-self-dual
parts. -/
theorem gaussBonnet_parity_even (s a : ℝ) :
    gaussBonnetDensity a s = gaussBonnetDensity s a := by
  unfold gaussBonnetDensity; ring

/-! ## §C — the self-dual sector links to Penrose twistor space -/

/-- **The principal null direction of a self-dual Weyl spinor**, as a point of the Riemann sphere `CP¹`:
the self-dual sector's `SL(2,ℂ)` chirality is the twistor group, so this is a `weylRatio` point. -/
noncomputable def selfDualPrincipalDirection (χ : Fin 2 → ℂ) : OnePoint ℂ := weylRatio χ

/-- **The self-dual principal direction is a twistor direction**: it equals the
`PenroseTwistorSpace.twistorDirection` of a twistor whose `π`-spinor is `χ` — the self-dual Weyl sector
lives on the same Riemann sphere as the twistor. -/
theorem selfDual_eq_twistorDirection (ω χ : Fin 2 → ℂ) :
    selfDualPrincipalDirection χ
      = Physlib.QuantumMechanics.ComplexAction.PenroseTwistorSpace.twistorDirection (ω, χ) :=
  rfl

/-- **The self-dual direction transforms by the twistor `SL(2,ℂ)` Möbius action**
`M • (χ₀/χ₁) = (M₀₀χ₀+M₀₁χ₁)/(M₁₀χ₀+M₁₁χ₁)`: the Lorentz `SL(2,ℂ)` of the self-dual Weyl sector acts on
its principal direction exactly as it acts on a twistor's direction (`sl2c_weylRatio`). -/
theorem selfDual_direction_sl2c (M : SL(2, ℂ)) (χ : Fin 2 → ℂ) (hb : χ 1 ≠ 0)
    (hden : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * χ 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * χ 1 ≠ 0) :
    M.toGL • selfDualPrincipalDirection χ
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * χ 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * χ 1)
          / ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * χ 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * χ 1)
          : ℂ) : OnePoint ℂ) := by
  unfold selfDualPrincipalDirection weylRatio
  rw [if_neg hb]
  exact sl2c_weylRatio M (χ 0) (χ 1) hb hden

/-! ## §D — the Euler–signature inequality and its self-dual saturation -/

/-- **The Euler–signature inequality** `|Pontryagin| ≤ Euler` (the topological bound `χ ≥ |τ|`, up to
normalization): since `|C⁺|², |C⁻|² ≥ 0`, the parity-odd Pontryagin density `s − a` is bounded in
absolute value by the parity-even Euler density `s + a`. -/
theorem abs_pontryagin_le_gaussBonnet (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) :
    |pontryaginDensity s a| ≤ gaussBonnetDensity s a := by
  unfold pontryaginDensity gaussBonnetDensity
  rw [abs_le]
  constructor <;> linarith

/-- **The bound is saturated exactly by (anti-)self-dual fields** `|Pontryagin| = Euler ↔ |C⁻|² = 0 ∨
|C⁺|² = 0`: equality in the Euler–signature inequality holds iff the curvature is self-dual (`a = 0`) or
anti-self-dual (`s = 0`) — a gravitational instanton saturates `χ = |τ|`. -/
theorem abs_pontryagin_eq_gaussBonnet_iff (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) :
    |pontryaginDensity s a| = gaussBonnetDensity s a ↔ s = 0 ∨ a = 0 := by
  unfold pontryaginDensity gaussBonnetDensity
  rw [abs_eq (by linarith : (0 : ℝ) ≤ s + a)]
  constructor
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

/-- **A self-dual gravitational instanton saturates the bound** `a = 0 → |Pontryagin| = Euler`: the
Euler and Pontryagin densities of a self-dual field agree in magnitude — the equality case of
`χ ≥ |τ|`. -/
theorem selfDual_saturates_bound (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (h : a = 0) :
    |pontryaginDensity s a| = gaussBonnetDensity s a :=
  (abs_pontryagin_eq_gaussBonnet_iff s a hs ha).mpr (Or.inr h)

/-! ## §E — the `(Euler, Pontryagin)` light-cone: link to the twistor `(2,2)` structure -/

/-- **The Euler–Pontryagin Lorentzian invariant** `Euler² − Pontryagin² = 4|C⁺|²|C⁻|²`: the pair
`(Euler, Pontryagin) = (s+a, s−a)` behaves like a `1+1` light-cone vector whose Minkowski square is
`4sa`. This is the same self-dual `(2,2)` signature — one norm `s+a`, one signature-difference `s−a` —
that underlies the twistor Hermitian form `PenroseTwistorSpace.twistorNorm`; the Euler density
(`= *R*_{ijkl}R^{ijkl}`, built from the double-dual `Curvature.MoulinDoubleDualCotton.doubleDualRiemann`)
is the norm, the Pontryagin the signature. -/
theorem gaussBonnet_sq_sub_pontryagin_sq (s a : ℝ) :
    gaussBonnetDensity s a ^ 2 - pontryaginDensity s a ^ 2 = 4 * s * a := by
  unfold gaussBonnetDensity pontryaginDensity; ring

/-- **Saturating `χ ≥ |τ|` is the "null" case** `Euler² = Pontryagin² ↔ |C⁺|² = 0 ∨ |C⁻|² = 0`: the
Euler–signature bound is saturated exactly when the light-cone invariant `4|C⁺|²|C⁻|²` vanishes — i.e.
the curvature is (anti-)self-dual — the gravitational analogue of a null twistor
(`PenroseTwistorSpace.IsNullTwistor`, `twistorNorm = 0`). -/
theorem gaussBonnet_sq_eq_pontryagin_sq_iff (s a : ℝ) :
    gaussBonnetDensity s a ^ 2 = pontryaginDensity s a ^ 2 ↔ s = 0 ∨ a = 0 := by
  rw [← sub_eq_zero, gaussBonnet_sq_sub_pontryagin_sq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact Or.inl h2
    · exact Or.inr h1
  · rintro (h | h) <;> simp [h]

/-- **A self-dual gravitational instanton has a definite twistor direction**: at saturation (`a = 0`) the
curvature has a single `SL(2,ℂ)` chirality, whose principal null direction is exactly the
`PenroseTwistorSpace.twistorDirection` of a twistor with `π = χ` — self-dual curvature is twistor data. -/
theorem selfDual_instanton_twistorDirection (ω χ : Fin 2 → ℂ) :
    selfDualPrincipalDirection χ
      = Physlib.QuantumMechanics.ComplexAction.PenroseTwistorSpace.twistorDirection (ω, χ) :=
  selfDual_eq_twistorDirection ω χ

/-! ## §F — parity link to the Deser topological mass -/

/-- **The gravitational Pontryagin shares the parity-odd sign of the Deser topological mass**: under a
parity/orientation reversal (swapping the self-dual and anti-self-dual parts) the Pontryagin density
transforms by the factor `TopologicallyMassiveGauge.massSignParity = −1` — exactly like the
Chern–Simons topological mass term. Both are parity-violating topological terms of Levi-Civita/dual
origin (the Pontryagin density is the exterior derivative of the gravitational Chern–Simons form). -/
theorem pontryagin_parity_sign_eq_topologicalMass (s a : ℝ) :
    pontryaginDensity a s
      = (TopologicallyMassiveGauge.massSignParity : ℝ) * pontryaginDensity s a := by
  simp only [TopologicallyMassiveGauge.massSignParity, Int.cast_neg, Int.cast_one]
  unfold pontryaginDensity; ring

/-- **The Gauss–Bonnet (Euler) density does NOT include the topological-mass parity sign** — it is
parity-even, so (for a nonzero density) it is not multiplied by `massSignParity = −1` under the parity
swap. The two `4`D topological terms have opposite parity: `γ` (Gauss–Bonnet) even, `μ` (Pontryagin) odd. -/
theorem gaussBonnet_parity_ne_topologicalMass (s a : ℝ) (h : gaussBonnetDensity s a ≠ 0) :
    gaussBonnetDensity a s
      ≠ (TopologicallyMassiveGauge.massSignParity : ℝ) * gaussBonnetDensity s a := by
  rw [gaussBonnet_parity_even]
  simp only [TopologicallyMassiveGauge.massSignParity, Int.cast_neg, Int.cast_one]
  intro heq
  exact h (by linarith)

end Physlib.QuantumMechanics.ComplexAction.Curvature.GaussBonnetPontryaginSelfDual

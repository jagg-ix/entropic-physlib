/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy
public import Mathlib.Tactic.FieldSimp

/-!
# The Wald / Jacobson–Myers Lovelock black-hole entropy functional

For a diffeomorphism-invariant Lagrangian the black-hole entropy is Wald's Noether charge
`S = −2π ∮_Σ (∂L/∂R_{abcd}) ε_{ab} ε_{cd}`. For Lovelock gravity — a sum of dimensionally-continued
Euler-density Lagrangians `L = Σ_m c_m L_m` — this is the **Jacobson–Myers** functional
  `S = 4π Σ_m m c_m ∮_Σ L_{m−1}`,
where `L_{m−1}` is the order-`(m−1)` Euler density built from the **intrinsic** Riemann curvature of the
`(D−2)`-dimensional horizon cross-section `Σ` (J. D. Bekenstein / R. M. Wald, Phys. Rev. D 48 (1993)
R3427; T. Jacobson, R. C. Myers, Phys. Rev. Lett. 70 (1993) 3684).

This formalizes the algebraic kernel of the functional — its per-order weight and the dimension counting
of the surface density — following the same generalized-Kronecker termination
(`Curvature.LovelockDimensionalTermination`) that governs the bulk terms, and anchors the Einstein case to
the Ryu–Takayanagi / Bekenstein–Hawking area law `A/(4G)` (`AdSCFT.RyuTakayanagiFormulaAlgebra`).

* **§A — the entropy weight `4π m c_m`.** `jacobsonMyersWeight`, `jacobsonMyersWeight_zero` (the
  cosmological term carries no entropy), `jacobsonMyers_einstein_eq_bekensteinHawking` (order `1` with
  `c₁ = 1/(16πG)` reproduces the RT area law).
* **§B — the surface density is one Lovelock order lower.** `entropy_surface_iff_bulk_lagrangian` (an
  order-`m` term contributes to the entropy iff it is a nonvanishing bulk Lagrangian term),
  `gaussBonnet_4d_entropy_but_no_dynamics` (Gauss–Bonnet contributes to 4D black-hole entropy through the
  Euler characteristic of the horizon while leaving the field equations untouched).
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.WaldJacobsonMyersLovelockEntropy

open scoped Real
open Physlib.QuantumMechanics.ComplexAction.Curvature
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra


/-- **The Jacobson–Myers entropy weight** of the order-`m` Lovelock term: in
`S = 4π Σ_m m c_m ∮_Σ L_{m−1}` the order-`m` dimensionally-continued Euler-density Lagrangian with
coupling `c` contributes to the horizon entropy with weight `4π m c` and a surface density one Lovelock
order lower. -/
noncomputable def jacobsonMyersWeight (m : ℕ) (c : ℝ) : ℝ := 4 * π * m * c

/-- **The cosmological term carries no horizon entropy**: the order-`0` term (a bare cosmological
constant, `L₀ = 1`) has Wald weight `4π·0·c = 0`, so it does not contribute to the black-hole entropy. -/
lemma jacobsonMyersWeight_zero (c : ℝ) : jacobsonMyersWeight 0 c = 0 := by
  unfold jacobsonMyersWeight; simp

/-- **Einstein gravity gives the Bekenstein–Hawking / Ryu–Takayanagi area law**: the order-`1` term with
Einstein coupling `c₁ = 1/(16πG)` has Wald weight `1/(4G)`, so its entropy `jacobsonMyersWeight 1 c₁ · A`
equals `RyuTakayanagi.rtAreaEntropy A G = A/(4G)` — the Jacobson–Myers functional reduces to the RT area
law at lowest order. -/
lemma jacobsonMyers_einstein_eq_bekensteinHawking (area G : ℝ) (hG : G ≠ 0) :
    jacobsonMyersWeight 1 (1 / (16 * π * G)) * area = rtAreaEntropy area G := by
  unfold jacobsonMyersWeight rtAreaEntropy
  have hpi : π ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  ring


/-- **The horizon entropy surface density is one Lovelock order lower**: the order-`(p+1)` bulk Lovelock
term contributes to the black-hole entropy through the order-`p` intrinsic Euler density `L_p` of the
`(D−2)`-dimensional horizon cross-section (bulk dimension `D = k+2`). That surface density is nonvanishing
iff `2p ≤ k`, which is exactly the condition for the order-`(p+1)` bulk Lagrangian term to be a
nonvanishing term of the bulk Lagrangian in dimension `D`: an order-`m` Lovelock term contributes to the
horizon entropy exactly when it is a genuine term of the bulk Lagrangian. -/
lemma entropy_surface_iff_bulk_lagrangian (p k : ℕ) :
    0 < LovelockDimensionalTermination.genKroneckerTrace k (2 * p)
      ↔ 0 < LovelockDimensionalTermination.genKroneckerTrace (k + 2) (2 * (p + 1)) := by
  rw [LovelockDimensionalTermination.genKroneckerTrace_pos_iff,
    LovelockDimensionalTermination.genKroneckerTrace_pos_iff]
  omega

/-- **Gauss–Bonnet contributes to 4D black-hole entropy without affecting the field equations**: in bulk
dimension `D = 4` the Gauss–Bonnet term (`m = 2`) is EOM-trivial — its order-2 tensor term vanishes
(`genKroneckerTrace 4 5 = 0`, the topological/critical case `D = 2m`) — yet it is a nonvanishing bulk
Lagrangian term (`0 < genKroneckerTrace 4 4`) and so contributes to the horizon entropy through the
order-1 intrinsic Euler density `L₁` of the 2-dimensional cross-section (`0 < genKroneckerTrace 2 2`), the
intrinsic Ricci scalar whose integral is the Euler characteristic of the horizon. -/
lemma gaussBonnet_4d_entropy_but_no_dynamics :
    LovelockDimensionalTermination.genKroneckerTrace 4 5 = 0
      ∧ 0 < LovelockDimensionalTermination.genKroneckerTrace 4 4
      ∧ 0 < LovelockDimensionalTermination.genKroneckerTrace 2 2 := by
  decide


/-! ### §D — the tower's entropy, and the one order that carries none

The Jacobson–Myers functional sums the Lovelock orders, `S = 4π Σ_m m c_m ∮ L_{m−1}`.  Two
facts about that sum are proved here, and together they say something sharp about which parts
of gravity carry information.

The dimensional reading supplies the motive.  Under the holographic typing `[G] = ` area per
bit, the Einstein-order entropy `A/4G` is a *nat count* — `RyuTakayanagi.rtAreaEntropy` measures
`[I]`, as does the Brown–Henneaux central charge, so both sides of Ryu–Takayanagi are counts of
the same kind.  Since the surface densities `∮L_{m−1}` are pure geometry and carry no
information charge, every coupling that contributes to the entropy must carry that charge
itself: the property `[G] = ` area-per-bit is not special to Einstein gravity but runs up the
whole tower.

Exactly one order escapes, and it escapes identically, not approximately.

The Einstein order of the tower is moreover *derived*, not posited: it equals the on-shell
Euclidean action of the bulk gravitational path integral
(`lovelockHorizonEntropy_einstein_eq_euclideanSaddleAction`), and the surface densities are the
intrinsic Euler densities of the horizon cross-section, whose order-by-order existence is
settled by `entropy_surface_iff_bulk_lagrangian`. -/

/-- **The Jacobson–Myers horizon entropy of a Lovelock tower** truncated at order `n`: each
order contributes its Wald weight times the intrinsic Euler density one order lower. -/
noncomputable def lovelockHorizonEntropy (n : ℕ) (coupling density : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, jacobsonMyersWeight m (coupling m) * density m

/-- **An order carries entropy exactly when it is neither the cosmological term nor
uncoupled.**  The Wald weight `4π m c` vanishes precisely at `m = 0` or `c = 0`, so among the
orders that are actually present in the Lagrangian, the cosmological term is the unique one
with no horizon entropy. -/
lemma jacobsonMyersWeight_ne_zero_iff (m : ℕ) (c : ℝ) :
    jacobsonMyersWeight m c ≠ 0 ↔ m ≠ 0 ∧ c ≠ 0 := by
  unfold jacobsonMyersWeight
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> rintro rfl <;> simp at h
  · rintro ⟨hm, hc⟩
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨by norm_num, hpi⟩, hmR⟩, hc⟩

/-- **The horizon entropy of a Lovelock tower does not depend on its cosmological coupling.**
Changing `c₀` — the coefficient of the order-`0` term, a bare cosmological constant — to any
other value whatsoever leaves the entropy unchanged, because that order enters the sum with
Wald weight `4π·0·c₀ = 0`.

This is the Wald-entropy statement of what the dimensional typing found independently: the
cosmological term is the informationally empty term of gravity.  Every other Lovelock order
carries a coupling that converts geometry into a bit count; `Λ` carries none, contributes
none, and can be varied freely without moving a single bit across the horizon. -/
theorem lovelockHorizonEntropy_indep_cosmologicalCoupling
    (n : ℕ) (coupling density : ℕ → ℝ) (c₀ : ℝ) :
    lovelockHorizonEntropy n (Function.update coupling 0 c₀) density
      = lovelockHorizonEntropy n coupling density := by
  unfold lovelockHorizonEntropy
  refine Finset.sum_congr rfl ?_
  intro m _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [jacobsonMyersWeight]
  · rw [Function.update_of_ne (by omega)]

/-- **The two-term tower is exactly the Ryu–Takayanagi area law.**  Keeping the cosmological
and Einstein orders, with the Einstein coupling `c₁ = 1/(16πG)` and the order-`1` surface
density the horizon area, the Jacobson–Myers entropy is `A/(4G)` — the cosmological term drops
out by the theorem above, and what survives is the area law whose two sides
`RyuTakayanagiFormulaAlgebra` measures as nat counts. -/
theorem lovelockHorizonEntropy_einstein_eq_rtAreaEntropy
    (area G c₀ : ℝ) (hG : G ≠ 0) :
    lovelockHorizonEntropy 2 (fun m => if m = 1 then 1 / (16 * π * G) else c₀)
        (fun m => if m = 1 then area else 0)
      = rtAreaEntropy area G := by
  unfold lovelockHorizonEntropy
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [jacobsonMyersWeight]
  rw [← jacobsonMyers_einstein_eq_bekensteinHawking area G hG]
  unfold jacobsonMyersWeight
  norm_num

/-- **The Einstein order of the tower is the Euclidean path-integral saddle.**  In natural
units (`G = ℓ_P = 1`) the two-term Jacobson–Myers entropy evaluated on the Schwarzschild
horizon area equals `Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildEuclideanSaddleAction` — the on-shell
Euclidean action of the *bulk path integral*, assembled there from the Euclidean Schwarzschild
metric, its vanishing bulk Einstein–Hilbert term, the Gibbons–Hawking–York boundary integral
with its reference subtraction, and the removal of the cutoff.

So the Jacobson–Myers functional is not an independent postulate at this order: its Einstein
term is *derived* from the gravitational path integral, and the partition function
`exp(−I_E/ℏ)` whose exponent it computes is the same nat count that `rtAreaEntropy` and the
Brown–Henneaux central charge measure.  The action of the bulk path integral, divided by `ℏ`,
is the information the horizon carries. -/
theorem lovelockHorizonEntropy_einstein_eq_euclideanSaddleAction (M c₀ : ℝ) (hM : 0 < M) :
    lovelockHorizonEntropy 2 (fun m => if m = 1 then 1 / (16 * π * 1) else c₀)
        (fun m => if m = 1 then
          Physlib.Relativity.SemiClassical.schwarzschildArea M 1 1 else 0)
      = Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildEuclideanSaddleAction M := by
  rw [lovelockHorizonEntropy_einstein_eq_rtAreaEntropy _ 1 c₀ one_ne_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildEuclideanSaddleAction_eq_bekensteinTauEnt M hM]
  unfold rtAreaEntropy Physlib.Thermodynamics.bekensteinTauEnt
  norm_num

/-- **The Einstein–Hilbert action's entire information content is on the boundary.**  The
Jacobson–Myers Einstein-order entropy is the cutoff limit of the *complete* Euclidean
gravitational action `I_EH(R) + I_GHY(R)` — and on the Schwarzschild vacuum the bulk
Einstein–Hilbert integral vanishes identically, because the metric-derived scalar curvature is
zero at every exterior point (Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildRegulatedEuclideanBulkAction_eq_zero).

So every bit the horizon carries comes from the Gibbons–Hawking–York *boundary* term; the bulk
Lagrangian of general relativity contributes exactly none.  For this solution holography is not
an assumption about where information lives but a theorem about where the action does. -/
theorem lovelockHorizonEntropy_einstein_isLimit_einsteinHilbertGHYAction
    (M c₀ : ℝ) (hM : 0 < M) :
    Filter.Tendsto
        (Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildRegulatedEinsteinHilbertGHYAction
          (Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildEuclideanPeriod M) M)
        Filter.atTop
        (nhds (lovelockHorizonEntropy 2 (fun m => if m = 1 then 1 / (16 * π * 1) else c₀)
          (fun m => if m = 1 then
            Physlib.Relativity.SemiClassical.schwarzschildArea M 1 1 else 0))) := by
  rw [lovelockHorizonEntropy_einstein_eq_euclideanSaddleAction M c₀ hM]
  exact Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildRegulatedEinsteinHilbertGHYAction_tendsto_saddleAction M hM

/-- **The bulk contributes nothing.**  Stated on its own: at every cutoff radius the bulk
Einstein–Hilbert part of the action that produces the entropy above is zero. -/
theorem einsteinHilbert_bulk_contributes_no_entropy (β M R : ℝ) (hM : 0 < M) :
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildRegulatedEuclideanBulkAction β M R = 0 :=
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildRegulatedEuclideanBulkAction_eq_zero β M R hM

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.WaldJacobsonMyersLovelockEntropy

end

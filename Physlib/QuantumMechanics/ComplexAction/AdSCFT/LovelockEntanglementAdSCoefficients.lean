/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.WaldJacobsonMyersLovelockEntropy

/-!
# Second-order Lovelock gravity from entanglement: the AdS on-shell coefficients

C. Fan, G. La Nave, P. W. Phillips, *Second-order Lovelock Gravity from Entanglement in Conformal Field
Theories* derive Lovelock gravity from the Ryu–Takayanagi area law and the first law of entanglement on
ball-shaped regions, and show that the Wald / Jacobson–Myers entropy of Lovelock gravity coincides with
the RT area law up to second order. Their Section II fixes the order-`m` Lovelock Lagrangian as the
generalized Kronecker delta contracted with `m` Riemann tensors (Eq. 12,
`L_{(m)} = 2^{−m} δ^{a₁b₁…}_{c₁d₁…} R^{c₁d₁}{}_{a₁b₁} ⋯`) — exactly the generalized-Kronecker trace of
`Curvature.LovelockDimensionalTermination` — and evaluates its tensor and entropy on the maximally
symmetric AdS background (Eq. 18, `R_{abcd} = −α^{−2}(g_{ac}g_{bd} − g_{ad}g_{bc})`).

This formalizes the two closed-form coefficients that background produces:

* **§A — Eq. 19, the on-shell Lovelock tensor.** `adsOnShellLovelockCoeff D m = (D−1)!/(D−2m−1)! =
  genKroneckerTrace (D−1) (2m)`; it survives iff `2m + 1 ≤ D` (`adsOnShellLovelockCoeff_pos_iff`), i.e.
  iff `m ≤ M = ⌊(D−1)/2⌋` (`adsOnShellLovelockCoeff_pos_iff_le_M`, Eq. 13), and vanishes above `M`
  (`adsOnShellLovelockCoeff_eq_zero_iff`) — the truncation of the cosmological-constant sum Eq. 20.
* **§B — Eq. 49, the Wald entropy as an area law.** `waldEntropyAreaCoeff D m = (D−2)!/(D−2m)! =
  genKroneckerTrace (D−2) (2(m−1))` is the order-`(m−1)` intrinsic Euler density on the `(D−2)`-surface
  (`WaldJacobsonMyersLovelockEntropy.entropy_surface_iff_bulk_lagrangian`); it is `1` for Einstein
  (`waldEntropyAreaCoeff_einstein`, the pure area `S = C₀ A`), and contributes iff `2m ≤ D`
  (`waldEntropyAreaCoeff_pos_iff`) — the bulk-Lagrangian survival condition.
* **§C — Eq. 45/46, the Jacobson–Myers functional.** the paper's per-order weight `m c_m` is
  `WaldJacobsonMyersLovelockEntropy.jacobsonMyersWeight` up to the `4π` normalization
  (`jacobsonMyersWeight_eq_paper_weight`).
* **§D — Eq. 26, the first-order equation of motion.** `firstOrderEinsteinCoeff D m =
  m · genKroneckerTrace (D−3) (2(m−1))`; the first-order Lovelock tensor is a multiple of the linearized
  Einstein tensor (`firstOrderEinsteinCoeff_einstein`, `_pos_iff`), so vacuum first-order Lovelock is
  first-order Einstein (Eq. 27).
* **§E — Appendix A, the symplectic current.** `symplecticFlowCoeff D m = m · genKroneckerTrace (D−2)
  (2(m−1)) = m · waldEntropyAreaCoeff` (`symplecticFlowCoeff_eq_mul_area`); the Lovelock symplectic
  potential is proportional to Einstein's on AdS (`symplecticFlowCoeff_einstein`).
* **§F — the intersection of branches.** `einstein_normalization`: entropy, symplectic current, and
  first-order EOM all reduce to Einstein at `m = 1`, so vacuum AdS lies at the intersection of all Lovelock
  branches — the concrete basis for the anticipation that RT on all subregions encodes the full non-linear
  Einstein equations (an expectation about generic metrics, stated in the docstring, not a theorem).
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.LovelockEntanglementAdSCoefficients

open Physlib.QuantumMechanics.ComplexAction.Curvature
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.WaldJacobsonMyersLovelockEntropy


/-- **The Eq. 19 on-shell coefficient** `(D−1)!/(D−2m−1)! = genKroneckerTrace (D−1) (2m)`: evaluating the
order-`m` Lovelock tensor `E^{a(m)}_b` on the maximally-symmetric AdS Riemann tensor (Eq. 18) gives
`E^{a(m)}_b = −(−α^{−2})^m · adsOnShellLovelockCoeff D m · δ^a_b`. -/
def adsOnShellLovelockCoeff (D m : ℕ) : ℕ :=
  LovelockDimensionalTermination.genKroneckerTrace (D - 1) (2 * m)

/-- **The on-shell term survives iff `2m + 1 ≤ D`** — the same dimensional-termination bound as the bulk
tensor term (`LovelockDimensionalTermination.lovelockTensorTerm_pos_iff`), read on the AdS background:
`0 < (D−1)!/(D−2m−1)!` iff `2m + 1 ≤ D`. -/
lemma adsOnShellLovelockCoeff_pos_iff (D m : ℕ) (hD : 1 ≤ D) :
    0 < adsOnShellLovelockCoeff D m ↔ 2 * m + 1 ≤ D := by
  unfold adsOnShellLovelockCoeff
  rw [LovelockDimensionalTermination.genKroneckerTrace_pos_iff]
  omega

/-- **The on-shell term vanishes iff `D < 2m + 1`** — Eq. 19 drops the order-`m` term out of the equations
of motion (and hence out of the cosmological-constant sum Eq. 20) once `2m + 1 > D`, i.e. above
`M = ⌊(D−1)/2⌋`. -/
lemma adsOnShellLovelockCoeff_eq_zero_iff (D m : ℕ) (hD : 1 ≤ D) :
    adsOnShellLovelockCoeff D m = 0 ↔ D < 2 * m + 1 := by
  unfold adsOnShellLovelockCoeff
  rw [LovelockDimensionalTermination.genKroneckerTrace_eq_zero_iff]
  omega

/-- **The Lovelock order is capped at `M = ⌊(D−1)/2⌋`** (Eq. 13): the on-shell tensor is nonzero iff
`m ≤ ⌊(D−1)/2⌋`. -/
lemma adsOnShellLovelockCoeff_pos_iff_le_M (D m : ℕ) (hD : 1 ≤ D) :
    0 < adsOnShellLovelockCoeff D m ↔ m ≤ (D - 1) / 2 := by
  rw [adsOnShellLovelockCoeff_pos_iff D m hD]
  omega


/-- **The Eq. 49 Wald-entropy area coefficient** `(D−2)!/(D−2m)! = genKroneckerTrace (D−2) (2(m−1))`:
the order-`m` term of the Lovelock Wald / Jacobson–Myers entropy functional, evaluated on the projected
AdS metric of the minimal surface (Eq. 48), contributes `(m c_m (D−2)!/(D−2m)!)(−α^{−2})^{m−1}` times the
area `A`, so `S_LW = C₀ A` (Eq. 49) is a constant multiple of the area. -/
def waldEntropyAreaCoeff (D m : ℕ) : ℕ :=
  LovelockDimensionalTermination.genKroneckerTrace (D - 2) (2 * (m - 1))

/-- **The area-law term is exactly the `(D−2)`-surface Euler density** of
`WaldJacobsonMyersLovelockEntropy`: the order-`m` Wald-entropy coefficient is the order-`(m−1)` intrinsic
Euler density on the `(D−2)`-dimensional horizon cross-section — the surface density that
`entropy_surface_iff_bulk_lagrangian` counts. -/
lemma waldEntropyAreaCoeff_eq_surface (D m : ℕ) :
    waldEntropyAreaCoeff D m
      = LovelockDimensionalTermination.genKroneckerTrace (D - 2) (2 * (m - 1)) := rfl

/-- **The Einstein term is the pure area law**: for `m = 1` the coefficient is `(D−2)!/(D−2)! = 1`, so the
Einstein contribution to the Wald entropy is exactly the area — the Bekenstein–Hawking / Ryu–Takayanagi
`A/(4G)` of `jacobsonMyers_einstein_eq_bekensteinHawking`. -/
lemma waldEntropyAreaCoeff_einstein (D : ℕ) : waldEntropyAreaCoeff D 1 = 1 := by
  unfold waldEntropyAreaCoeff
  simp [LovelockDimensionalTermination.genKroneckerTrace]

/-- **The area-law term contributes iff `2m ≤ D`** — the bulk-Lagrangian survival condition of
`WaldJacobsonMyersLovelockEntropy.entropy_surface_iff_bulk_lagrangian`: an order-`m` Lovelock term adds to
the pure-AdS Wald entropy exactly when it is a nonvanishing term of the bulk Lagrangian. -/
lemma waldEntropyAreaCoeff_pos_iff (D m : ℕ) (hD : 2 ≤ D) (hm : 1 ≤ m) :
    0 < waldEntropyAreaCoeff D m ↔ 2 * m ≤ D := by
  unfold waldEntropyAreaCoeff
  rw [LovelockDimensionalTermination.genKroneckerTrace_pos_iff]
  omega


/-- **The paper's Jacobson–Myers per-order weight is `jacobsonMyersWeight`**: the entropy functional
`S = ∫ √γ Σ_m m c_m L̃_{(m−1)}` (Eq. 45/46) weights the order-`m` surface density by `m c_m`, which is
`WaldJacobsonMyersLovelockEntropy.jacobsonMyersWeight m c` up to the `4π` normalization. -/
lemma jacobsonMyersWeight_eq_paper_weight (m : ℕ) (c : ℝ) :
    jacobsonMyersWeight m c = 4 * Real.pi * ((m : ℝ) * c) := by
  unfold jacobsonMyersWeight
  ring


/-- **The Eq. 26 first-order coefficient** `m (D−3)!/(D−2m−1)! = m · genKroneckerTrace (D−3) (2(m−1))`:
the first-order perturbation of the order-`m` Lovelock tensor about AdS is
`δ₁E^{a(m)}_b = firstOrderEinsteinCoeff D m · (−α^{−2})^{m−1} (R^{a(1)}_b − ½ δ^a_b R^{(1)})` — a multiple
of the *linearized Einstein tensor*, so the vacuum first-order Lovelock equation (Eq. 27) is the
linearized Einstein equation for every order `m`. -/
def firstOrderEinsteinCoeff (D m : ℕ) : ℕ :=
  m * LovelockDimensionalTermination.genKroneckerTrace (D - 3) (2 * (m - 1))

/-- **First-order Lovelock coincides with Einstein**: for `m = 1` the coefficient is `1`, so the order-1
term *is* the linearized Einstein tensor and every higher order is a scalar multiple of it. -/
lemma firstOrderEinsteinCoeff_einstein (D : ℕ) : firstOrderEinsteinCoeff D 1 = 1 := by
  unfold firstOrderEinsteinCoeff
  simp [LovelockDimensionalTermination.genKroneckerTrace]

/-- **The first-order term survives iff `2m + 1 ≤ D`** — the same order cap as the on-shell tensor (§A):
below `M = ⌊(D−1)/2⌋` every Lovelock order contributes a nonzero multiple of the linearized Einstein
tensor. -/
lemma firstOrderEinsteinCoeff_pos_iff (D m : ℕ) (hD : 3 ≤ D) (hm : 1 ≤ m) :
    0 < firstOrderEinsteinCoeff D m ↔ 2 * m + 1 ≤ D := by
  unfold firstOrderEinsteinCoeff
  rw [Nat.pos_iff_ne_zero, mul_ne_zero_iff, ← Nat.pos_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    LovelockDimensionalTermination.genKroneckerTrace_pos_iff]
  omega


/-- **The Appendix-A symplectic coefficient** `m (D−2)!/(D−2m)! = m · genKroneckerTrace (D−2) (2(m−1))`:
on the AdS background the order-`m` symplectic potential is
`P^{abcd}_{(m)} = symplecticFlowCoeff D m · (−α^{−2})^{m−1} P^{abcd}_{(1)}` (Eq. A4), so the symplectic
current of Lovelock gravity is proportional to that of Einstein. -/
def symplecticFlowCoeff (D m : ℕ) : ℕ :=
  m * LovelockDimensionalTermination.genKroneckerTrace (D - 2) (2 * (m - 1))

/-- The symplectic coefficient is `m` times the Wald-entropy area coefficient of §B: the symplectic
potential and the entropy share the same `(D−2)`-surface Euler density. -/
lemma symplecticFlowCoeff_eq_mul_area (D m : ℕ) :
    symplecticFlowCoeff D m = m * waldEntropyAreaCoeff D m := rfl

/-- **The symplectic flow reduces to Einstein**: for `m = 1` the coefficient is `1`. -/
lemma symplecticFlowCoeff_einstein (D : ℕ) : symplecticFlowCoeff D 1 = 1 := by
  unfold symplecticFlowCoeff
  simp [LovelockDimensionalTermination.genKroneckerTrace]


/-- **Every Einstein-proportionality coefficient normalizes to `1` at `m = 1`**: on the AdS background the
Wald entropy (Eq. 49), the symplectic current (Appendix A), and the first-order equation of motion
(Eq. 26) all reduce to their Einstein values, so first-order Einstein and Lovelock coincide and vacuum AdS
lies at the intersection of all Lovelock branches (Conclusion). This is the concrete basis for the paper's
anticipation that Ryu–Takayanagi on all subregions encodes the full non-linear Einstein equations on
asymptotically AdS spacetimes — an expectation about generic (non-AdS) metrics that is not itself a
theorem here. -/
lemma einstein_normalization (D : ℕ) :
    waldEntropyAreaCoeff D 1 = 1
      ∧ symplecticFlowCoeff D 1 = 1
      ∧ firstOrderEinsteinCoeff D 1 = 1 :=
  ⟨waldEntropyAreaCoeff_einstein D, symplecticFlowCoeff_einstein D, firstOrderEinsteinCoeff_einstein D⟩

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.LovelockEntanglementAdSCoefficients

end

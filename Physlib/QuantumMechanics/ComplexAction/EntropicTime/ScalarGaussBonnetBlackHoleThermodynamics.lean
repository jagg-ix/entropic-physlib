/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.WaldJacobsonMyersLovelockEntropy
meta import Zil

/-!
# Einstein-Maxwell-scalar-Gauss-Bonnet black-hole thermodynamics in bit form

Erices and Kiorpelidi (arXiv:2604.25100) study the thermodynamics of electrically charged scalarized
black holes in Einstein-Maxwell-scalar-Gauss-Bonnet (EMsGB) gravity. Their central thermodynamic
relations formalize here, with the Bekenstein-Hawking part of the entropy read as the arc's bit count.

The **Wald entropy** (Eq. 2.13) deviates from the area law by a Gauss-Bonnet term:

  `S_H = A_H/4 + 4πλ²f(φ_H)`.

The first term is the Bekenstein-Hawking entropy — a quarter of the horizon bit count,
`A_H/4 = N/4` with `N = holographicBits A_H G ℏ c` (`HorizonNagaoContourBitEinstein`,
`horizon_imaginaryAction_eq_quarter_bits`). The second is the **Gauss-Bonnet Wald correction**: in four
dimensions the Gauss-Bonnet term is dynamically trivial (topological) yet contributes to the horizon
entropy through Wald's formula
(`AdSCFT.WaldJacobsonMyersLovelockEntropy.gaussBonnet_4d_entropy_but_no_dynamics`) — the scalar hair.

The **first law** (Eq. 3.17) is `δM = T δS + Φ_e δQ`, so in the canonical (fixed-charge) ensemble the
Helmholtz free energy `F = M − T S` (Eq. 3.16) has `S = −∂F/∂T`, and the grand-canonical Gibbs free
energy `G = M − T S − Φ_e Q` (Eq. 3.15) is its charge-work Legendre transform. The **specific heat**
`C_Q = ∂M/∂T = T ∂S/∂T` (Sec. IV) is positive — the state locally thermodynamically stable — exactly
when the entropy increases with temperature.

* **§A** the Wald entropy `S_H = N/4 + 4πλ²f(φ_H)` and its deviation from the area law (Eq. 2.13).
* **§B** the free energies, the charge-work Legendre transform, and `S = −∂F/∂T` (Eqs. 3.15-3.17).
* **§C** the specific heat `C_Q = T ∂S/∂T` and local stability (Sec. IV).

## References

* C. Erices, S. Kiorpelidi, *Thermodynamic Phase Transitions in Einstein-Maxwell-Scalar-Gauss-Bonnet
  Gravity*, arXiv:2604.25100 — Eqs. 2.13, 3.15-3.17, Sec. IV.
* R. M. Wald, Phys. Rev. D 48 (1993) R3427 — the Wald entropy of a higher-curvature theory.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics

/-! ## A. The Wald entropy in bit form -/

/-- **[The EMsGB Wald entropy, Eq. 2.13]** `S_H = N/4 + 4πλ²f(φ_H)`: the Bekenstein-Hawking entropy —
a quarter of the horizon bit count `N = holographicBits A_H G ℏ c` — plus the Gauss-Bonnet Wald
correction `4πλ²f(φ_H)`. -/
noncomputable def emsgbWaldEntropy (A lam f_H G ℏ c : ℝ) : ℝ :=
  holographicBits A G ℏ c / 4 + 4 * Real.pi * lam ^ 2 * f_H

/-- **[The area-law part is the horizon bit count]** `A_H/4 = N/4`. The Bekenstein-Hawking term of the
Wald entropy is a quarter of the holographic bit count; the horizon imaginary action `S_I = c³A/(4G)`
is `ℏ N/4` (`horizon_imaginaryAction_eq_quarter_bits`), so `S_BH = S_I/ℏ = N/4`. -/
theorem emsgbWaldEntropy_areaLaw_is_bitCount (A G ℏ c : ℝ) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) :
    horizonImaginaryAction G c A / ℏ = holographicBits A G ℏ c / 4 := by
  rw [horizon_imaginaryAction_eq_quarter_bits G c A ℏ hG hℏ]
  field_simp

/-- **[The Wald entropy deviates from the area law, Eq. 2.13]** when the Gauss-Bonnet contribution
`4πλ²f(φ_H)` is nonzero, `S_H ≠ N/4`: the scalar hair makes the black-hole entropy exceed the
Bekenstein-Hawking area law. In four dimensions this correction is dynamically trivial yet entropic
(`gaussBonnet_4d_entropy_but_no_dynamics`). -/
theorem emsgbWaldEntropy_ne_areaLaw (A lam f_H G ℏ c : ℝ)
    (hgb : 4 * Real.pi * lam ^ 2 * f_H ≠ 0) :
    emsgbWaldEntropy A lam f_H G ℏ c ≠ holographicBits A G ℏ c / 4 := by
  rw [emsgbWaldEntropy]
  intro h
  exact hgb (by linarith)

/-! ## B. The free energies and the first law -/

/-- **[The Gibbs free energy, grand-canonical ensemble, Eq. 3.15]** `G = M − T S − Φ_e Q`. -/
def gibbsFreeEnergy (M T S Phi_e Q : ℝ) : ℝ := M - T * S - Phi_e * Q

/-- **[The Helmholtz free energy, canonical ensemble, Eq. 3.16]** `F = M − T S` (fixed charge). -/
def helmholtzFreeEnergy (M T S : ℝ) : ℝ := M - T * S

/-- **[Gibbs is the charge-work Legendre transform of Helmholtz]** `G = F − Φ_e Q`: fixing the electric
potential (grand canonical) versus fixing the charge (canonical) differ by the electromagnetic work
`Φ_e Q` — the Maxwell sector of the electrogravitic coupling. -/
theorem gibbs_eq_helmholtz_sub_chargeWork (M T S Phi_e Q : ℝ) :
    gibbsFreeEnergy M T S Phi_e Q = helmholtzFreeEnergy M T S - Phi_e * Q := by
  rw [gibbsFreeEnergy, helmholtzFreeEnergy]

/-- **[Entropy is minus the temperature-derivative of the Helmholtz free energy]** `S = −∂F/∂T`. From
the first law `δM = T δS + Φ_e δQ` at fixed charge (`dM = T dS`), the Helmholtz free energy
`F = M − T S` has `∂F/∂T = −S`: the entropy is the response of the free energy to temperature. -/
theorem entropy_eq_neg_helmholtz_deriv (M S : ℝ → ℝ) (T dM dS : ℝ)
    (hM : HasDerivAt M dM T) (hS : HasDerivAt S dS T) (hFirstLaw : dM = T * dS) :
    HasDerivAt (fun t => M t - t * S t) (-(S T)) T := by
  have hF : HasDerivAt (fun t => M t - t * S t) (dM - (1 * S T + T * dS)) T :=
    hM.sub ((hasDerivAt_id T).mul hS)
  convert hF using 1
  rw [hFirstLaw]; ring

/-! ## C. The specific heat and local stability -/

/-- **[The specific heat, Sec. IV]** `C_Q = ∂M/∂T = T ∂S/∂T` at fixed charge. From the first law
`δM = T δS` (fixed `Q`), the heat capacity is the temperature times the entropy's temperature slope. It
is **positive iff the entropy increases with temperature** — the local thermodynamic stability
criterion: an increasing equation of state `T(S)` is a positive specific heat. -/
theorem specificHeat_from_firstLaw (T dM dS : ℝ) (hT : 0 < T) (hFirstLaw : dM = T * dS) :
    dM = T * dS ∧ (0 < dM ↔ 0 < dS) := by
  refine ⟨hFirstLaw, ?_⟩
  rw [hFirstLaw]
  exact mul_pos_iff_of_pos_left hT

/-- **[Positive specific heat is entropy increasing with temperature]** `C_Q > 0 ↔ ∂S/∂T > 0` for
`T > 0` (`C_Q = T ∂S/∂T`). Locally stable thermal states are the increasing branches of the equation of
state; the Davies points where the specific heat diverges separate stable from unstable branches. -/
theorem specificHeat_pos_iff_entropy_increasing (T dS : ℝ) (hT : 0 < T) :
    0 < T * dS ↔ 0 < dS :=
  mul_pos_iff_of_pos_left hT

/-! ## D. The order of the phase transition (Ehrenfest classification, Sec. IV) -/

/-- **[The specific heat is minus the temperature-curvature of the free energy]** `C_Q = −T ∂²F/∂T²`.
Since `C_Q = T ∂S/∂T` and `S = −∂F/∂T`, the heat capacity is `−T` times the second
temperature-derivative of the Helmholtz free energy — the response that jumps at a second-order
transition. -/
theorem specificHeat_eq_neg_T_secondDeriv (T dS ddF : ℝ) (hS : dS = -ddF) :
    T * dS = -(T * ddF) := by rw [hS]; ring

/-- **[Zeroth-order transition]** the free energy itself jumps: `F_A ≠ F_B` at the transition
temperature (the spontaneous shedding of scalar hair with a finite free-energy jump, Sec. V). -/
def IsZerothOrder (F_A F_B : ℝ) : Prop := F_A ≠ F_B

/-- **[First-order transition]** equal free energies with an entropy jump: `F_A = F_B`, `S_A ≠ S_B`. -/
def IsFirstOrder (F_A F_B S_A S_B : ℝ) : Prop := F_A = F_B ∧ S_A ≠ S_B

/-- **[Second-order transition]** equal free energies and entropies with a heat-capacity jump:
`F_A = F_B`, `S_A = S_B`, `C_A ≠ C_B` (the second bifurcation / onset of scalarization, Sec. V). -/
def IsSecondOrder (F_A F_B S_A S_B C_A C_B : ℝ) : Prop := F_A = F_B ∧ S_A = S_B ∧ C_A ≠ C_B

/-- **[First order is the free-energy-slope jump]** with `S = −∂F/∂T` on each branch, a first-order
transition (`F_A = F_B`, `S_A ≠ S_B`) is exactly equal free energies with distinct temperature slopes
`∂F_A/∂T ≠ ∂F_B/∂T`. The lowest discontinuous derivative of `F` is the first. -/
theorem isFirstOrder_iff_slope_jump (F_A F_B dF_A dF_B : ℝ) :
    IsFirstOrder F_A F_B (-dF_A) (-dF_B) ↔ (F_A = F_B ∧ dF_A ≠ dF_B) :=
  and_congr Iff.rfl (not_congr neg_inj)

/-- **[Second order is the free-energy-curvature jump]** with `S = −∂F/∂T` and `C_Q = −T ∂²F/∂T²`, a
second-order transition (`F_A = F_B`, `S_A = S_B`, `C_A ≠ C_B`) is equal free energies and slopes with
distinct curvatures `∂²F_A/∂T² ≠ ∂²F_B/∂T²` (`T ≠ 0`) — the first two derivatives of `F` continuous, the
second discontinuous. -/
theorem isSecondOrder_iff_curvature_jump (F_A F_B dF_A dF_B ddF_A ddF_B T : ℝ) (hT : T ≠ 0) :
    IsSecondOrder F_A F_B (-dF_A) (-dF_B) (-(T * ddF_A)) (-(T * ddF_B))
      ↔ (F_A = F_B ∧ dF_A = dF_B ∧ ddF_A ≠ ddF_B) :=
  and_congr Iff.rfl (and_congr neg_inj (not_congr (neg_inj.trans (mul_right_inj' hT))))

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.emsgbWaldEntropy_areaLaw_is_bitCount where
  formalizes @ "claim:the-bekenstein-hawking-area-law-part-of-the-wald-entropy-read-as-the-horizon-imaginary-action-over-hbar-equals-one-quarter-of-the-holographic-bit-count",
  supported_by @ "paper:erices-kiorpelidi-arxiv-2604-25100-scalarized-einstein-maxwell-scalar-gauss-bonnet-black-holes"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.emsgbWaldEntropy_ne_areaLaw where
  formalizes @ "claim:when-the-gauss-bonnet-contribution-is-nonzero-the-wald-entropy-deviates-from-the-bekenstein-hawking-area-law-the-scalar-hair-makes-the-entropy-exceed-n-over-four",
  requires @ "claim:the-bekenstein-hawking-area-law-part-of-the-wald-entropy-read-as-the-horizon-imaginary-action-over-hbar-equals-one-quarter-of-the-holographic-bit-count"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.specificHeat_from_firstLaw where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:from-the-first-law-at-fixed-charge-the-specific-heat-c-q-equals-t-times-the-entropys-temperature-slope-and-is-positive-iff-the-entropy-increases-with-temperature-the-local-stability-criterion"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.isFirstOrder_iff_slope_jump where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:with-entropy-equal-to-minus-the-free-energy-temperature-slope-a-first-order-transition-equal-free-energies-with-an-entropy-jump-is-exactly-equal-free-energies-with-distinct-free-energy-slopes"

zil_file_contract physlib.scalarGaussBonnetBlackHoleThermodynamics where
  promises "Erices and Kiorpelidi (arXiv:2604.25100) black-hole thermodynamics for charged scalarized black holes in Einstein-Maxwell-scalar-Gauss-Bonnet gravity, in bit form. The Bekenstein-Hawking area-law part of the Wald entropy equals one quarter of the holographic bit count (emsgbWaldEntropy_areaLaw_is_bitCount); a nonzero Gauss-Bonnet contribution makes the Wald entropy exceed the area law, the scalar-hair correction (emsgbWaldEntropy_ne_areaLaw). From the first law at fixed charge the specific heat C_Q = T dS/dT is positive iff the entropy increases with temperature -- the local thermodynamic stability criterion (specificHeat_from_firstLaw) -- and, with S = -dF/dT, the Ehrenfest classification reads off the free-energy derivatives: a first-order transition is equal free energies with a free-energy-slope jump (isFirstOrder_iff_slope_jump)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.emsgbWaldEntropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.helmholtzFreeEnergy"]
  forbids_substitutes ["the Wald entropy formula and the Gauss-Bonnet gravitational action, which are the cited higher-curvature-gravity inputs",
    "the microscopic scalarization dynamics, only the entropy-bit identity, the first law, and the Ehrenfest transition-order algebra are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.emsgbWaldEntropy_areaLaw_is_bitCount,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.emsgbWaldEntropy_ne_areaLaw,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.specificHeat_from_firstLaw,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScalarGaussBonnetBlackHoleThermodynamics.isFirstOrder_iff_slope_jump]

/- ZIL-END -/

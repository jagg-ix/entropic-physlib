/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LambShiftOriginDensity

/-!
# Alavi: Dirac hydrogen and the Lamb shift in dynamical non-commutative space

This file formalizes the exact algebraic surface of S. A. Alavi and N. Rezaei,
*Dirac equation, hydrogen atom spectrum and the Lamb shift in dynamical non-commutative spaces*, Pramana
88:77 (2017). The analytic content of the paper is a first-order perturbative calculation of Dirac-hydrogen
matrix elements. Here we isolate the parts that are cleanly formalizable without importing the full
Dirac-Coulomb spectral analysis:

* **§A — DNCS commutators** (`DNCSPlane`, `SatisfiesDNCSRelations`). This is the paper's Eq. (2), expressed
  for a generic operator carrier. Theorems `bracket_XY_tau_zero`, `bracket_XPx_tau_zero`,
  `bracket_XPy_tau_zero`, and `bracket_YPy_tau_zero` prove the `tau = 0` reduction to ordinary theta-space
  commutation relations, i.e. Eq. (3).
* **§B — Hamiltonian split** (`alaviHamiltonian`). This records the paper's first-order split
  `H = Hs + H_tau + H_theta`, Eq. (13), independent of the representation chosen for the operators.
* **§C — reported energy-shift coefficients** (`groundShiftCoeff`, `twoSShiftCoeff`, `twoPShiftCoeff`).
  The numerical coefficients from Eq. (17) and Eq. (20) are kept as exact rationals:
  `260.401 = 260401/1000`, `4.87865 = 487865/100000`, `7.31797 = 731797/100000`.
* **§D — Lamb-shift contrast** (`theta_twoS_no_correction`, `alavi_tau_lamb_extra`). This captures the
  paper's key qualitative distinction: theta-space gives no `2S_{1/2}` correction in this treatment, while
  dynamical non-commutativity shifts both `2S_{1/2}` and `2P_{1/2}`. The extra tau contribution to the
  `2P - 2S` splitting is exactly `(7.31797 - 4.87865) tau = (60983/25000) tau`.
* **§E — Repo integration** (`alaviLambLevelEnergy`, `alavi_lamb_2S_minus_2P`). This composes the Alavi
  perturbation with the existing `Electromagnetic.CovariantMaxwellLambShift` Dirac/Lamb carrier and the
  `LambShiftOriginDensity` selection rule.

The file deliberately does not claim to rederive the perturbative integrals of Eq. (14) from the explicit
Dirac spinors Eq. (15)--(16). It formalizes the paper's operator algebra, first-order decomposition, and the
coefficient arithmetic downstream of those integrals.

## References

* S. A. Alavi, N. Rezaei, Pramana 88:77 (2017), DOI 10.1007/s12043-017-1381-4.
* Repo carriers: `Electromagnetic.CovariantMaxwellLambShift` and `LambShiftOriginDensity` for the ordinary Lamb-shift
  baseline.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlaviDynamicalNoncommutativeHydrogen


/-- A generic ring commutator `[a,b] = ab - ba`. -/
def commutator {A : Type*} [Sub A] [Mul A] (a b : A) : A := a * b - b * a

/-- The carrier data for the Alavi-Fring-Gouba-Scholtz dynamical non-commutative plane.

The fields `xOp`, `yOp`, `pxOp`, `pyOp` stand for the paper's `X`, `Y`, `P_x`, `P_y`; `theta`, `tau`, and
`hbar` are the parameters `theta`, `tau`, and `hbar`; `bracket` is the chosen commutator operation. -/
structure DNCSPlane (A : Type*) [AddCommMonoid A] [One A] [Mul A] [Module ℂ A] where
  xOp : A
  yOp : A
  pxOp : A
  pyOp : A
  theta : ℂ
  tau : ℂ
  hbar : ℂ
  bracket : A → A → A

/-- **The DNCS commutator relations** of Alavi-Rezaei Eq. (2):
`[X,Y] = i theta (1 + tau Y^2)`, `[X,P_x] = i hbar (1 + tau Y^2)`,
`[X,P_y] = 2 i tau Y(theta P_y + hbar X)`, `[Y,P_y] = i hbar (1 + tau Y^2)`,
with `[P_y,P_x] = 0` and `[Y,P_x] = 0`. -/
def SatisfiesDNCSRelations {A : Type*} [AddCommMonoid A] [One A] [Mul A] [Module ℂ A]
    (D : DNCSPlane A) : Prop :=
  D.bracket D.xOp D.yOp = (Complex.I * D.theta) • ((1 : A) + D.tau • (D.yOp * D.yOp))
    ∧ D.bracket D.xOp D.pxOp = (Complex.I * D.hbar) • ((1 : A) + D.tau • (D.yOp * D.yOp))
    ∧ D.bracket D.xOp D.pyOp =
        (2 * Complex.I * D.tau) • (D.yOp * (D.theta • D.pyOp + D.hbar • D.xOp))
    ∧ D.bracket D.yOp D.pyOp = (Complex.I * D.hbar) • ((1 : A) + D.tau • (D.yOp * D.yOp))
    ∧ D.bracket D.pyOp D.pxOp = 0
    ∧ D.bracket D.yOp D.pxOp = 0

namespace DNCSPlane

variable {A : Type*} [AddCommMonoid A] [One A] [Mul A] [Module ℂ A] (D : DNCSPlane A)

/-- **`tau = 0` reduces `[X,Y]` to theta-space**: `[X,Y] = i theta`. -/
lemma bracket_XY_tau_zero (hD : SatisfiesDNCSRelations D) (hτ : D.tau = 0) :
    D.bracket D.xOp D.yOp = (Complex.I * D.theta) • (1 : A) := by
  rw [hD.1, hτ]
  simp

/-- **`tau = 0` reduces `[X,P_x]` to the canonical theta-space relation**: `[X,P_x] = i hbar`. -/
lemma bracket_XPx_tau_zero (hD : SatisfiesDNCSRelations D) (hτ : D.tau = 0) :
    D.bracket D.xOp D.pxOp = (Complex.I * D.hbar) • (1 : A) := by
  rw [hD.2.1, hτ]
  simp

/-- **`tau = 0` kills the dynamical mixed bracket**: `[X,P_y] = 0`. -/
lemma bracket_XPy_tau_zero (hD : SatisfiesDNCSRelations D) (hτ : D.tau = 0) :
    D.bracket D.xOp D.pyOp = 0 := by
  rw [hD.2.2.1, hτ]
  simp

/-- **`tau = 0` reduces `[Y,P_y]` to the canonical theta-space relation**: `[Y,P_y] = i hbar`. -/
lemma bracket_YPy_tau_zero (hD : SatisfiesDNCSRelations D) (hτ : D.tau = 0) :
    D.bracket D.yOp D.pyOp = (Complex.I * D.hbar) • (1 : A) := by
  rw [hD.2.2.2.1, hτ]
  simp

end DNCSPlane


variable {A : Type*} [Add A]

/-- **Alavi-Rezaei first-order Hamiltonian split** `H = Hs + H_tau + H_theta` (Eq. 13). -/
def alaviHamiltonian (Hs Hτ Hθ : A) : A := Hs + Hτ + Hθ

/-- The Hamiltonian is definitionally the standard part plus tau- and theta-perturbations. -/
lemma alaviHamiltonian_decompose (Hs Hτ Hθ : A) :
    alaviHamiltonian Hs Hτ Hθ = Hs + Hτ + Hθ := rfl


/-- Hydrogen levels whose tau corrections are reported in Alavi-Rezaei Eq. (17) and Eq. (20). -/
inductive AlaviLevel where
  | ground
  | twoS
  | twoP
deriving DecidableEq

open AlaviLevel

/-- **Eq. (17)**: `Delta E_ground = (260.401 eV/m^2) tau`. -/
noncomputable def groundShiftCoeff : ℝ := 260401 / 1000

/-- **Eq. (20)**: `Delta E_{2S_{1/2}} = (4.87865 eV/m^2) tau`. -/
noncomputable def twoSShiftCoeff : ℝ := 487865 / 100000

/-- **Eq. (20)**: `Delta E_{2P_{1/2}} = (7.31797 eV/m^2) tau`. -/
noncomputable def twoPShiftCoeff : ℝ := 731797 / 100000

/-- The reported tau-shift coefficient for each level. -/
noncomputable def tauShiftCoeff : AlaviLevel → ℝ
  | ground => groundShiftCoeff
  | twoS => twoSShiftCoeff
  | twoP => twoPShiftCoeff

/-- The first-order tau energy shift `Delta E = C_level tau`. -/
noncomputable def tauEnergyShift (τ : ℝ) (level : AlaviLevel) : ℝ := tauShiftCoeff level * τ

lemma ground_tauEnergyShift (τ : ℝ) :
    tauEnergyShift τ ground = (260401 / 1000 : ℝ) * τ := rfl

lemma twoS_tauEnergyShift (τ : ℝ) :
    tauEnergyShift τ twoS = (487865 / 100000 : ℝ) * τ := rfl

lemma twoP_tauEnergyShift (τ : ℝ) :
    tauEnergyShift τ twoP = (731797 / 100000 : ℝ) * τ := rfl

/-- **The tau contribution to the `2P - 2S` splitting** is exactly
`(7.31797 - 4.87865) tau = (60983/25000) tau`. -/
lemma twoP_minus_twoS_tauShift (τ : ℝ) :
    tauEnergyShift τ twoP - tauEnergyShift τ twoS = (60983 / 25000 : ℝ) * τ := by
  unfold tauEnergyShift tauShiftCoeff twoPShiftCoeff twoSShiftCoeff
  ring

lemma twoS_tauShift_pos {τ : ℝ} (hτ : 0 < τ) : 0 < tauEnergyShift τ twoS := by
  unfold tauEnergyShift tauShiftCoeff twoSShiftCoeff
  positivity

lemma twoP_tauShift_pos {τ : ℝ} (hτ : 0 < τ) : 0 < tauEnergyShift τ twoP := by
  unfold tauEnergyShift tauShiftCoeff twoPShiftCoeff
  positivity

/-- For positive `tau`, the reported `2P_{1/2}` tau shift is larger than the `2S_{1/2}` tau shift. -/
lemma twoP_tauShift_gt_twoS {τ : ℝ} (hτ : 0 < τ) :
    tauEnergyShift τ twoS < tauEnergyShift τ twoP := by
  have hdiff : 0 < tauEnergyShift τ twoP - tauEnergyShift τ twoS := by
    rw [twoP_minus_twoS_tauShift]
    positivity
  linarith


/-- The qualitative theta-space correction model used for the contrast in the paper:
the `2S_{1/2}` level receives no theta correction, while `2P_{1/2}` may receive one. -/
noncomputable def thetaEnergyShift (θCoeff θ : ℝ) : AlaviLevel → ℝ
  | ground => 0
  | twoS => 0
  | twoP => θCoeff * θ

/-- **Theta-space gives no correction to `2S_{1/2}`** in the cited non-dynamical treatment. -/
lemma theta_twoS_no_correction (θCoeff θ : ℝ) :
    thetaEnergyShift θCoeff θ twoS = 0 := rfl

/-- The theta correction channel retained for `2P_{1/2}`. -/
lemma theta_twoP_correction (θCoeff θ : ℝ) :
    thetaEnergyShift θCoeff θ twoP = θCoeff * θ := rfl

/-- Combined reported first-order shift: tau correction plus the qualitative theta correction model. -/
noncomputable def alaviObservedShift (τ θCoeff θ : ℝ) (level : AlaviLevel) : ℝ :=
  tauEnergyShift τ level + thetaEnergyShift θCoeff θ level

/-- **The pure tau contribution to the Alavi Lamb-splitting correction**:
`Delta E_2P - Delta E_2S = (60983/25000) tau`. -/
lemma alavi_tau_lamb_extra (τ : ℝ) :
    alaviObservedShift τ 0 0 twoP - alaviObservedShift τ 0 0 twoS
      = (60983 / 25000 : ℝ) * τ := by
  simp [alaviObservedShift, thetaEnergyShift, twoP_minus_twoS_tauShift]

/-- **Ground-state accuracy bound**. If the reported ground-state shift is bounded by an experimental
accuracy `δ`, then `tau ≤ δ / 260.401`. This is the algebraic content of Eq. (18), before the unit conversion
used in the paper to report `sqrt(tau) ≤ 10^{-17} eV`. -/
lemma tau_bound_from_ground_shift {τ d : ℝ} (hshift : tauEnergyShift τ ground ≤ d) :
    τ ≤ d / groundShiftCoeff := by
  unfold tauEnergyShift tauShiftCoeff groundShiftCoeff at hshift
  unfold groundShiftCoeff
  nlinarith [hshift]

lemma groundShiftCoeff_pos : 0 < groundShiftCoeff := by
  unfold groundShiftCoeff
  positivity

lemma twoSShiftCoeff_pos : 0 < twoSShiftCoeff := by
  unfold twoSShiftCoeff
  positivity

lemma twoPShiftCoeff_pos : 0 < twoPShiftCoeff := by
  unfold twoPShiftCoeff
  positivity

/-- The exact ordering of the two reported excited-state tau coefficients. -/
lemma coefficient_order :
    twoSShiftCoeff < twoPShiftCoeff ∧ 0 < twoSShiftCoeff := by
  constructor
  · unfold twoSShiftCoeff twoPShiftCoeff
    norm_num
  · exact twoSShiftCoeff_pos


open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift
open Physlib.QuantumMechanics.ComplexAction.LambShiftOriginDensity

/-- The existing repo Dirac energy carrier, indexed by the Alavi levels formalized here. -/
noncomputable def repoDiracLevelEnergy (Zα : ℝ) : AlaviLevel → ℝ
  | ground => diracStateEnergy Zα 1 0 (1 / 2)
  | twoS => diracStateEnergy Zα 2 0 (1 / 2)
  | twoP => diracStateEnergy Zα 2 1 (1 / 2)

/-- The existing repo observed-energy carrier, indexed by the Alavi levels formalized here. -/
noncomputable def repoLambLevelEnergy (Zα α L : ℝ) : AlaviLevel → ℝ
  | ground => observedEnergy Zα α L 1 0 (1 / 2)
  | twoS => observedEnergy Zα α L 2 0 (1 / 2)
  | twoP => observedEnergy Zα α L 2 1 (1 / 2)

/-- Dirac carrier plus the Alavi tau/theta first-order correction. -/
noncomputable def alaviDiracLevelEnergy (Zα τ θCoeff θ : ℝ) (level : AlaviLevel) : ℝ :=
  repoDiracLevelEnergy Zα level + alaviObservedShift τ θCoeff θ level

/-- Repo Lamb-shift carrier plus the Alavi tau/theta first-order correction. -/
noncomputable def alaviLambLevelEnergy (Zα α L τ θCoeff θ : ℝ) (level : AlaviLevel) : ℝ :=
  repoLambLevelEnergy Zα α L level + alaviObservedShift τ θCoeff θ level

/-- The repo Dirac carrier preserves the usual `2S_{1/2}`/`2P_{1/2}` degeneracy. -/
lemma repoDirac_2S_2P_degenerate (Zα : ℝ) :
    repoDiracLevelEnergy Zα twoS = repoDiracLevelEnergy Zα twoP :=
  dirac_2S_2P_degenerate Zα

/-- The repo Lamb carrier gives the ordinary `2S_{1/2} - 2P_{1/2}` Bethe splitting. -/
lemma repoLamb_2S_minus_2P (Zα α L : ℝ) :
    repoLambLevelEnergy Zα α L twoS - repoLambLevelEnergy Zα α L twoP = betheLambShift α L 2 :=
  lamb_lifts_degeneracy Zα α L

/-- With only the Alavi tau correction, the Dirac `2P_{1/2} - 2S_{1/2}` degeneracy is lifted by the exact
reported coefficient difference. -/
lemma alavi_lifts_dirac_degeneracy_p_minus_s (Zα τ : ℝ) :
    alaviDiracLevelEnergy Zα τ 0 0 twoP - alaviDiracLevelEnergy Zα τ 0 0 twoS =
      (60983 / 25000 : ℝ) * τ := by
  unfold alaviDiracLevelEnergy repoDiracLevelEnergy
  rw [← dirac_2S_2P_degenerate Zα]
  unfold alaviObservedShift tauEnergyShift tauShiftCoeff thetaEnergyShift twoPShiftCoeff twoSShiftCoeff
  ring

/-- The ordinary repo Lamb splitting and the Alavi correction compose additively: the tau channel lowers the
`2S - 2P` gap by `(60983/25000) tau`, and the retained theta channel lowers it by `thetaCoeff * theta`. -/
lemma alavi_lamb_2S_minus_2P (Zα α L τ θCoeff θ : ℝ) :
    alaviLambLevelEnergy Zα α L τ θCoeff θ twoS -
        alaviLambLevelEnergy Zα α L τ θCoeff θ twoP =
      betheLambShift α L 2 - (60983 / 25000 : ℝ) * τ - θCoeff * θ := by
  unfold alaviLambLevelEnergy repoLambLevelEnergy
  simp only
  calc
    observedEnergy Zα α L 2 0 (1 / 2) + alaviObservedShift τ θCoeff θ twoS -
        (observedEnergy Zα α L 2 1 (1 / 2) + alaviObservedShift τ θCoeff θ twoP)
        = (observedEnergy Zα α L 2 0 (1 / 2) - observedEnergy Zα α L 2 1 (1 / 2)) +
          (alaviObservedShift τ θCoeff θ twoS - alaviObservedShift τ θCoeff θ twoP) := by
            ring
    _ = betheLambShift α L 2 +
          (alaviObservedShift τ θCoeff θ twoS - alaviObservedShift τ θCoeff θ twoP) := by
            rw [lamb_lifts_degeneracy Zα α L]
    _ = betheLambShift α L 2 - (60983 / 25000 : ℝ) * τ - θCoeff * θ := by
      unfold alaviObservedShift tauEnergyShift tauShiftCoeff thetaEnergyShift twoPShiftCoeff twoSShiftCoeff
      ring

/-- If the Alavi correction is smaller than the ordinary Bethe splitting, the corrected model keeps the
observed `2S_{1/2}` level above `2P_{1/2}`. -/
lemma alavi_corrected_2S_above_2P (Zα α L τ θCoeff θ : ℝ)
    (hsmall : (60983 / 25000 : ℝ) * τ + θCoeff * θ < betheLambShift α L 2) :
    alaviLambLevelEnergy Zα α L τ θCoeff θ twoP <
      alaviLambLevelEnergy Zα α L τ θCoeff θ twoS := by
  have hsplit := alavi_lamb_2S_minus_2P Zα α L τ θCoeff θ
  linarith

/-- The tau correction gives a `2P_{1/2}` shift even though the repo origin-density rule still identifies
the `P`-state density at the nucleus as zero. -/
lemma dncs_tau_escapes_origin_density_selection (Z a₀ τ : ℝ) (hτ : 0 < τ) :
    densityAtOrigin 2 1 Z a₀ = 0 ∧ 0 < tauEnergyShift τ twoP :=
  ⟨densityAtOrigin_eq_zero_of_l_pos 2 1 Z a₀ (by norm_num), twoP_tauShift_pos hτ⟩

end Physlib.QuantumMechanics.ComplexAction.AlaviDynamicalNoncommutativeHydrogen

end

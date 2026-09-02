/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralMeasureValid
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# Both the Nagao–Nielsen `(p,q)` and the non-Hermitian gap come from the path integral

Recognizes — and links into the QED/Cameron–Martin construction — that the two ingredients of the
complex-action framework were *both derived from a path integral*:

* the **Nagao–Nielsen `(p,q)` phase space** (`PathIntegral.MomentumPathIntegral`): the phase-space path integral
  `∫Dp Dq e^{i(pq̇−H)/ℏ}`, completed-square and integrated over the momentum `p` (saddle `p = mq̇`,
  Eqs. 3.10/3.15/3.17), yields the configuration path integral — `(p,q)` is the *form* of the path
  integral, not an extra assumption;
* the **non-Hermitian gap `E_I`** (`WickRotation`): the complex energy `E_C = E_R − iE_I` generates the
  eigen-evolution `u(t) = e^{−iE_C t/ℏ}` — the propagator weight — whose **modulus is `e^{−E_I t/ℏ}`**
  (`norm_evolutionFactor`). So the gap `E_I` is read off the path-integral propagator's modulus.

These are exactly the real and imaginary actions of the measure-valid QED model: `S_R = E_R` (the
Nagao–Nielsen `(p,q)` reversible phase) and `S_I = E_I` (the non-Hermitian gap), and the QED Cameron–Martin
weight is precisely the gap damping.

* **§A — the non-Hermitian gap from the path integral.** `gap_eq_complexEnergy_im`
  (`E_I = −Im E_C`), `gap_from_pathIntegral` (`‖u(t)‖ = e^{−E_I t/ℏ}`, the gap *is* the propagator modulus).
* **§B — the Nagao–Nielsen `(p,q)` from the path integral.** `pq_from_pathIntegral_saddle` (the
  phase-space Lagrangian reduces to the configuration one at the saddle `p = mq̇`).
* **§C — the link to the QED Cameron–Martin construction.** `qed_actionIm_is_gap` (the QED model's
  imaginary action *is* the non-Hermitian gap `E_I`), `qed_weight_is_gap_damping` (the QED Cameron–Martin
  weight modulus *is* the non-Hermitian gap propagator modulus `‖u(1)‖`).

## References

* K. Nagao, H. B. Nielsen, *Momentum relation and classical limit in the future-not-included complex
  action theory*, Prog. Theor. Phys., arXiv:1304.4017, §3, §5 — the Nagao–Nielsen `(p,q)` momentum
  relation `p = mq̇` derived from the phase-space (Feynman) path integral (§B here).
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. 126 (2011) 1021 —
  the complex Hamiltonian `H_C = H_R − iH_I` and the non-Hermitian gap `E_I` (§A here).
* Repo carriers used: `PathIntegral.MomentumPathIntegral` (`phaseLagrangian_at_saddle`, `momentum_relation`, the
  `(p,q)` path integral), `NonHermitian.WickRotation` (`complexEnergy`, `evolutionFactor`,
  `norm_evolutionFactor` — the complex energy `E_C` and its eigen-propagator `e^{−iE_C t/ℏ}`),
  `PathIntegral.QEDPathIntegralMeasureValid` (the measure-valid QED Cameron–Martin construction).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.GapPathIntegralOrigin

open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QuantumMechanics.ComplexAction
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy


/-- **The non-Hermitian gap is the imaginary part of the complex energy** `E_I = −Im(E_C)`, where
`E_C = E_R − iE_I` (`WickRotation.complexEnergy`) is the eigenvalue of the non-Hermitian Hamiltonian. -/
lemma gap_eq_complexEnergy_im (E_R E_I : ℝ) : (complexEnergy E_R E_I).im = -E_I := by
  simp [complexEnergy]

/-- **[Origin] The non-Hermitian gap `E_I` IS the modulus of the path-integral propagator.** The
eigen-evolution `u(t) = e^{−iE_C t/ℏ}` (the path-integral weight on an `H_C`-eigenstate,
`WickRotation.evolutionFactor`) has modulus `‖u(t)‖ = e^{−E_I t/ℏ}` (`norm_evolutionFactor`): the gap is
not postulated — it is *read off* the path integral as the decay rate of the propagator. -/
lemma gap_from_pathIntegral (E_R E_I ℏ t : ℝ) :
    ‖evolutionFactor E_R E_I ℏ t‖ = Real.exp (-(E_I * t / ℏ)) :=
  norm_evolutionFactor E_R E_I ℏ t


/-- **[Origin] The Nagao–Nielsen `(p,q)` phase space is the path-integral phase-space form.** The
phase-space Lagrangian `L(p, q̇) = pq̇ − H` of the path integral `∫Dp e^{i(pq̇−H)/ℏ}` reduces, at the
momentum saddle `p = mq̇` (`PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle`, Eqs. 3.15/3.17), to the
configuration Lagrangian `½mq̇² − V` — `(p,q)` emerges from integrating the path integral over the
momentum, it is not an extra postulate. -/
lemma pq_from_pathIntegral_saddle (m qdot V : ℂ) (hm : m ≠ 0) :
    PathIntegral.MomentumPathIntegral.phaseLagrangian m (m * qdot) qdot V
      = PathIntegral.MomentumPathIntegral.configLagrangian m qdot V :=
  PathIntegral.MomentumPathIntegral.phaseLagrangian_at_saddle m qdot V hm

/-- **The Nagao–Nielsen canonical momentum** `p = ∂L/∂q̇ = mq̇` (`PathIntegral.MomentumPathIntegral.momentum_relation`,
Eq. 3.10) — the saddle of the momentum path integral. -/
lemma pq_momentum_relation (m qdot V : ℂ) :
    HasDerivAt (fun q' => PathIntegral.MomentumPathIntegral.configLagrangian m q' V) (m * qdot) qdot :=
  PathIntegral.MomentumPathIntegral.momentum_relation m qdot V


/-- **[Link] The QED model's imaginary action IS the non-Hermitian gap `E_I`.** Setting the fermion
damping to the gap, `(qedExchangeModel ℏ E_I 0).actionIm = E_I` — the `S_I` that makes the QED path integral
measure-valid is exactly the non-Hermitian gap derived from the path integral (§A). -/
lemma qed_actionIm_is_gap (ℏ E_I : ℝ) (hℏ : 0 < ℏ) (hI : 0 ≤ E_I) (x : ℝ) :
    (PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ E_I 0 hℏ hI le_rfl).actionIm x = E_I := by
  simp [PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel]

/-- **[Link] The QED Cameron–Martin weight modulus IS the non-Hermitian gap propagator modulus.**
`‖(qedExchangeModel ℏ E_I 0).weight x‖ = ‖e^{−iE_C/ℏ}‖ = e^{−E_I/ℏ}` (`gap_from_pathIntegral` at `t = 1`):
the measure-valid QED Cameron–Martin weight and the non-Hermitian eigen-propagator's modulus are the same
scalar — the gap derived from the path integral *is* the QED entropic damping. -/
lemma qed_weight_is_gap_damping (ℏ E_R E_I : ℝ) (hℏ : 0 < ℏ) (hI : 0 ≤ E_I) (x : ℝ) :
    ‖(PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ E_I 0 hℏ hI le_rfl).weight x‖
      = ‖evolutionFactor E_R E_I ℏ 1‖ := by
  rw [PathIntegral.QEDPathIntegralMeasureValid.qed_cameronMartin_eq_weight_modulus, norm_evolutionFactor]
  congr 1; ring

/-! ## D. The non-Hermitian gap as a finite variational deficit -/

variable {State : Type*} [Fintype State]

/-- The variational non-Hermitian gap is the finite trial free energy above its Gibbs minimum.
It has energy units; unlike `β` times this expression, it can consistently occupy the imaginary
part `E_I` of the complex energy. -/
noncomputable def variationalDissipativeGap
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ) : ℝ :=
  finiteTrialFreeEnergy p G.energy G.beta - gibbsFreeEnergy G.partition G.beta

/-- The dissipative energy gap is exactly relative entropy divided by inverse temperature. -/
theorem variationalDissipativeGap_eq_relativeEntropy_div
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    variationalDissipativeGap G p = finiteRelativeEntropy p G.gibbsWeight / G.beta :=
  G.freeEnergy_gap_eq_relativeEntropy_div p hp hnorm

/-- The finite variational dissipative gap is nonnegative. -/
theorem variationalDissipativeGap_nonneg
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    0 ≤ variationalDissipativeGap G p :=
  G.freeEnergy_gap_nonneg p hp hnorm

/-- **[Non-Hermitian variational weld]** Putting the variational free-energy deficit into the
imaginary energy makes the propagator modulus decay with exponent
`-(D(p ‖ p_Gibbs)/β)t/ℏ`. -/
theorem variationalGap_from_pathIntegral
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) (E_R ℏ t : ℝ) :
    ‖evolutionFactor E_R (variationalDissipativeGap G p) ℏ t‖ =
      Real.exp (-((finiteRelativeEntropy p G.gibbsWeight / G.beta) * t / ℏ)) := by
  rw [gap_from_pathIntegral,
    variationalDissipativeGap_eq_relativeEntropy_div G p hp hnorm]

/-- For positive Planck scale and forward time, the variational non-Hermitian propagator is a
contraction in norm. -/
theorem variationalGap_evolution_norm_le_one
    (G : FiniteGibbsVariationalSystem State) (p : State → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1)
    (E_R ℏ t : ℝ) (hℏ : 0 < ℏ) (ht : 0 ≤ t) :
    ‖evolutionFactor E_R (variationalDissipativeGap G p) ℏ t‖ ≤ 1 := by
  rw [gap_from_pathIntegral]
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (div_nonneg
    (mul_nonneg (variationalDissipativeGap_nonneg G p hp hnorm) ht) hℏ.le)

/- ZIL-BEGIN -/

zil attach variationalDissipativeGap_eq_relativeEntropy_div where
  supported_by @ "lean:FiniteGibbsVariationalSystem.freeEnergy_gap_eq_relativeEntropy_div",
  formalizes @ "claim:finite-nonhermitian-dissipative-energy-gap-is-gibbs-free-energy-deficit-and-relative-entropy-over-beta",
  epistemic_status @ "risky",
  caveat @ "claim:definition-selects-the-variational-gap-identification-and-does-not-derive-it-for-every-effective-nonhermitian-hamiltonian"

zil attach variationalGap_from_pathIntegral where
  supported_by @ "lean:variationalDissipativeGap_eq_relativeEntropy_div",
  formalizes @ "claim:variational-free-energy-deficit-controls-nonhermitian-propagator-modulus",
  epistemic_status @ "risky",
  requires @ "claim:finite-nonhermitian-dissipative-energy-gap-is-gibbs-free-energy-deficit-and-relative-entropy-over-beta",
  caveat @ "claim:finite-diagonal-gap-carrier-not-a-general-lindblad-unravelling-equivalence"

zil attach variationalGap_evolution_norm_le_one where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.GapPathIntegralOrigin.gap_from_pathIntegral",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.GapPathIntegralOrigin.variationalDissipativeGap_nonneg",
  formalizes @ "claim:positive-variational-dissipative-gap-produces-forward-time-propagator-contraction",
  epistemic_status @ "risky",
  caveat @ "claim:norm-contraction-does-not-prove-complete-positivity-trace-preservation-or-pt-symmetry"

zil_file_contract physlib.nonHermitianVariationalGap where
  promises "The finite Gibbs variational deficit is a nonnegative energy-valued non-Hermitian gap, exactly relative entropy divided by beta; inserted into the existing complex-energy propagator it yields the corresponding entropy-controlled damping and a forward-time norm contraction."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.NonHermitian.WickRotation.norm_evolutionFactor",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy.FiniteGibbsVariationalSystem.freeEnergy_gap_eq_relativeEntropy_div"
  ]
  forbids_substitutes [
    "claiming every non-Hermitian imaginary energy is a Gibbs free-energy deficit",
    "claiming a finite scalar decay identity is a full Lindblad unravelling",
    "identifying a rate with a free-energy deficit without an explicit time scale"
  ]
  witnessed_by [variationalDissipativeGap_eq_relativeEntropy_div,
    variationalGap_from_pathIntegral, variationalGap_evolution_norm_le_one]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.GapPathIntegralOrigin

end

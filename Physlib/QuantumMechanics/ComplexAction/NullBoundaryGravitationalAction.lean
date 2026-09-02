/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.Wick.Consistency
public import Physlib.Relativity.SemiClassical.HawkingTemperature

/-!
# Gravitational action with null boundaries (Lehner–Myers–Poisson–Sorkin)

Lehner, Myers, Poisson & Sorkin, *Gravitational action with null boundaries* (arXiv:1609.00207),
formalizing the algebraic backbone of the null-boundary term, its parametrization ambiguity, the joint
`a`-terms, the stationary/Killing-horizon case, and the *complexity = action* rate `dI/dt = 2M`.

The gravitational action of a region `𝒱` with a broken boundary is
`S = 16π G_N I = ∫_𝒱 (R − 2Λ) dV + S_{∂𝒱}` (Eq. 1.2), where a **null** segment `Σ` contributes the
boundary term `S_Σ = −2∫_Σ κ √γ d²θ dλ + (joint a-terms)` (Eqs. 2.66–2.67). Here `κ` is the
inaffinity of the null generators (`k^β∇_β k^α = κ k^α`), and the joint contribution is
`a = ln|n·k|` (null joined to spacelike/timelike) or `a = ln(−½ k·k̄)` (null–null).

* **§A — reparametrization of the null generators** (Eq. 2.69). With `e^{−β} := ∂λ/∂λ̃`:
  `k̃ = e^β k`, `Θ̃ = e^β Θ`, `κ̃ = e^β(κ + ∂_λβ)`, `ā = a + β`. The inaffinity transforms
  **inhomogeneously** like a connection (`reparamInaffinity`): affine parametrization `κ̃ = 0` exists
  exactly for `∂_λβ = −κ` (`reparamInaffinity_eq_zero_iff`), and once affine, staying affine forces
  `∂_λβ = 0` — the residual constant rescaling of the affine parameter (`reparamInaffinity_affine_residual`).
* **§B — the null boundary action** (Eqs. 2.66–2.67). `nullSegmentAction`; affine parametrization
  (`κ = 0`) leaves **only** the joint terms (`nullSegmentAction_affine`).
* **§C — reparametrization change of the action** (Eq. 2.70). `S̃ = S + 2∫_Σ Θβ √γ dλ`; a
  **stationary** null surface (`Θ = 0`) is reparametrization invariant (`reparamAction_stationary`).
* **§D — the stationary / Killing-horizon joint** (Eqs. 2.23, 2.68). `a = −ln(2κ)`; the two joints
  cancel and `S_Σ* = −2κ* 𝒜 (λ₂* − λ₁*)` (`stationaryNullAction_eq`). The exponentiated joint is the
  surface gravity `exp(−a) = 2κ` (`stationaryJointA_exp`), tying it to the **Hawking temperature**
  `T_H = ℏκ/(2πck_B)` of the same `κ` (`stationaryJointA_hawkingTemperature`).
* **§E — redefinition of Φ** (Eq. 2.73). `ā = a + ln(dΦ̃/dΦ)`, i.e. `exp(ā) = exp(a)·(dΦ̃/dΦ)`
  (`redefPhiJointA_exp`).
* **§F — the joint term as a log inner product** (Eqs. 1.3, §II.H). `a = ln|n·k|` exponentiates to the
  normal inner product `exp(a) = |n·k|` (`nullNonnullJointA_exp`).
* **§G — complexity = action** (Eqs. 1.1, 3.29). `dS/dt = 32π G_N M ⟺ dI/dt = 2M` for `I = S/(16πG_N)`
  (`dSdt_iff_dIdt`); the complexity `C = I/(πℏ)` then grows at `dC/dt = 2M/(πℏ)`
  (`complexity_rate_of_dIdt`).
* **§H — pure-phase amplitude.** The on-shell WdW-patch action is real, so its `complexActionWeight`
  amplitude is a pure phase (unitary, `‖·‖ = 1`) — the entropic-weight hub link
  (`wdw_action_amplitude_pure_phase`).

**Honest layering.** Proven: the reparametrization group law and its affine fixed-point/residual
freedom, the affine reduction of the boundary action, the stationary-case joint cancellation and its
surface-gravity/Hawking-temperature identity, the Φ-redefinition and log-inner-product exponentials,
and the `dI/dt = 2M` normalization with the pure-phase amplitude. Interpretive: the tensorial geometry
(the congruence `k^α`, the transverse metric `γ_AB`, the area element `√γ d²θ`, the extrinsic-curvature
origin of `κ`) is the physical content behind the scalar integrands `κ`, `a`, `Θ`, taken here as the
data; the integrals are represented by their integrated values.

## References

* L. Lehner, R. C. Myers, E. Poisson, R. D. Sorkin, "Gravitational action with null boundaries",
  arXiv:1609.00207 [`Lehner:2016vdi`], Eqs. (1.1)–(1.2), (2.66)–(2.74), (3.29). Reuses
  `Physlib.QFT.Wick.Consistency` (`complexActionWeight`, `norm_complexActionWeight_zero_imag`) and
  `Physlib.Relativity.SemiClassical` (`hawkingTemperature`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction

open Physlib.QFT.Wick.Consistency
open Physlib.Relativity.SemiClassical


/-- **The reparametrized tangent** `k̃ = e^β k` (Eq. 2.69), where `e^{−β} := ∂λ/∂λ̃`. -/
noncomputable def reparamTangent (β k : ℝ) : ℝ := Real.exp β * k

/-- **The reparametrized expansion** `Θ̃ = e^β Θ` (Eq. 2.69). -/
noncomputable def reparamExpansion (β Θ : ℝ) : ℝ := Real.exp β * Θ

/-- **The reparametrized inaffinity** `κ̃ = e^β(κ + ∂_λβ)` (Eq. 2.69). Unlike `k`, `Θ`, `B`, the
inaffinity transforms **inhomogeneously**: the `∂_λβ` term makes `κ` behave like a connection under
reparametrizations of the null generators. -/
noncomputable def reparamInaffinity (β dβ κ : ℝ) : ℝ := Real.exp β * (κ + dβ)

/-- **The reparametrized joint value** `ā = a + β` (Eq. 2.69, first relation). -/
def reparamJointA (β a : ℝ) : ℝ := a + β

/-- **Affine parametrization exists** (Eq. 2.69): the inaffinity vanishes iff `∂_λβ = −κ`. Because
`e^β ≠ 0`, `κ̃ = e^β(κ + ∂_λβ) = 0` forces `κ + ∂_λβ = 0`. This is the paper's central observation:
the null generators can always be affinely parametrized, taming the ambiguous `κ`-term. -/
lemma reparamInaffinity_eq_zero_iff (β dβ κ : ℝ) :
    reparamInaffinity β dβ κ = 0 ↔ dβ = -κ := by
  unfold reparamInaffinity
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (Real.exp_ne_zero β)
    · linarith
  · intro h; right; linarith

/-- **The affine choice** `∂_λβ = −κ` yields `κ̃ = 0`. -/
lemma reparamInaffinity_affine (β κ : ℝ) : reparamInaffinity β (-κ) κ = 0 :=
  (reparamInaffinity_eq_zero_iff β (-κ) κ).mpr rfl

/-- **The residual freedom is a constant rescaling** (Eq. 2.69, abstract): once the parameter is affine
(`κ = 0`), a further reparametrization stays affine (`κ̃ = 0`) iff `∂_λβ = 0`, i.e. `β` is constant
along each generator — a rescaling of the affine parameter by a constant factor. -/
lemma reparamInaffinity_affine_residual (β dβ : ℝ) :
    reparamInaffinity β dβ 0 = 0 ↔ dβ = 0 := by
  rw [reparamInaffinity_eq_zero_iff]; simp


/-- **The null-segment boundary action** `S_Σ = −2∫_Σ κ √γ d²θ dλ + 2∮_{ℬ₂} a √γ d²θ − 2∮_{ℬ₁} a √γ d²θ`
(Eq. 2.67, the joined form), represented by the integrated inaffinity term and the two joint values. -/
def nullSegmentAction (kappaIntegral aTop aBot : ℝ) : ℝ :=
  -2 * kappaIntegral + 2 * aTop - 2 * aBot

/-- **Affine parametrization eliminates the bulk null term** (Eq. 2.66 with `κ = 0`): with the
generators affinely parametrized, the null segment contributes **only** through its joints. -/
lemma nullSegmentAction_affine (aTop aBot : ℝ) :
    nullSegmentAction 0 aTop aBot = 2 * aTop - 2 * aBot := by
  unfold nullSegmentAction; ring


/-- **The reparametrized boundary action** `S̃_Σ = S_Σ + 2∫_Σ Θβ √γ d²θ dλ` (Eq. 2.70). -/
def reparamAction (S ΘβIntegral : ℝ) : ℝ := S + 2 * ΘβIntegral

/-- **A stationary null boundary is reparametrization invariant** (Eq. 2.70, exception): when the
expansion vanishes (`Θ = 0`, so `∫Θβ = 0`) the boundary action is unchanged under a reparametrization
of the null generators — the property that makes the Killing-horizon term unambiguous. -/
lemma reparamAction_stationary (S ΘβIntegral : ℝ) (h : ΘβIntegral = 0) :
    reparamAction S ΘβIntegral = S := by
  unfold reparamAction; rw [h]; ring


/-- **The stationary null-joint value** `a = −ln(2κ)` (Eq. 2.23), with `κ` the surface gravity of the
Killing horizon (`k^α = ξ^α`, `Φ = ξ_α ξ^α`). -/
noncomputable def stationaryJointA (κ : ℝ) : ℝ := -Real.log (2 * κ)

/-- **The stationary null action** `S_Σ* = −2κ* 𝒜 (λ₂* − λ₁*)` (Eq. 2.68), `𝒜` the cross-sectional
area. -/
noncomputable def stationaryNullAction (κ area lamTop lamBot : ℝ) : ℝ :=
  -2 * κ * area * (lamTop - lamBot)

/-- **The joint terms cancel on a stationary null surface** (Eq. 2.67 → 2.68): with constant surface
gravity `κ` (so `∫κ √γ dλ = κ 𝒜 (λ₂ − λ₁)`), equal cross-sections (`𝒜₁ = 𝒜₂ = 𝒜`), and equal joint
values (`a₁ = a₂`), `S_Σ(joined)` reduces to `−2κ 𝒜 (λ₂ − λ₁)`. -/
lemma stationaryNullAction_eq (κ area lamTop lamBot aVal : ℝ) :
    nullSegmentAction (κ * area * (lamTop - lamBot)) (aVal * area) (aVal * area)
      = stationaryNullAction κ area lamTop lamBot := by
  unfold nullSegmentAction stationaryNullAction; ring

/-- **The exponentiated stationary joint is the surface gravity** `exp(−a) = 2κ` (Eq. 2.23): the
`a`-term is a logarithm of `2κ`, so it exponentiates to twice the surface gravity. -/
lemma stationaryJointA_exp (κ : ℝ) (hκ : 0 < κ) :
    Real.exp (- stationaryJointA κ) = 2 * κ := by
  unfold stationaryJointA
  rw [neg_neg, Real.exp_log (by positivity)]

/-- **The stationary joint is the Hawking temperature datum** (Eq. 2.23 ∧ `hawkingTemperature`): the
`a = −ln(2κ)` joint of a Killing horizon carries the same surface gravity `κ` as the Hawking
temperature `T_H = ℏκ/(2πck_B)`, so `T_H = ℏ exp(−a)/(4πck_B)`. -/
lemma stationaryJointA_hawkingTemperature (ℏ κ c kB : ℝ) (hκ : 0 < κ) :
    hawkingTemperature ℏ κ c kB
      = ℏ * Real.exp (- stationaryJointA κ) / (4 * Real.pi * c * kB) := by
  rw [stationaryJointA_exp κ hκ]
  unfold hawkingTemperature
  ring


/-- **The Φ-redefined joint value** `ā = a + ln(dΦ̃/dΦ)` (Eq. 2.73): redefining the scalar `Φ` that
describes the null hypersurface shifts the `a₀` piece of the joint value by `ln(dΦ̃/dΦ)`. -/
noncomputable def redefPhiJointA (a lnDeriv : ℝ) : ℝ := a + lnDeriv

/-- **The Φ-redefinition rescales the exponentiated joint** (Eq. 2.73): with `lnDeriv = ln(dΦ̃/dΦ)` and
`dΦ̃/dΦ = d > 0`, `exp(ā) = exp(a)·d`. The ill-definedness of `S_Σ(joined)` under `Φ → Φ̃(Φ)` is this
multiplicative rescaling of the joint weight. -/
lemma redefPhiJointA_exp (a d : ℝ) (hd : 0 < d) :
    Real.exp (redefPhiJointA a (Real.log d)) = Real.exp a * d := by
  unfold redefPhiJointA
  rw [Real.exp_add, Real.exp_log hd]


/-- **The null–nonnull joint value** `a = ln|n·k|` (Eq. 1.3, §II.G), where `n^α` is the unit normal to
the spacelike/timelike segment and `k^α` the null normal. -/
noncomputable def nullNonnullJointA (nDotk : ℝ) : ℝ := Real.log |nDotk|

/-- **The null–null joint value** `a = ln(−½ k·k̄)` (Eq. 1.3, §II.G), with `k^α`, `k̄^α` the two null
normals. -/
noncomputable def nullNullJointA (kDotkbar : ℝ) : ℝ := Real.log (-(1 / 2) * kDotkbar)

/-- **The exponentiated null–nonnull joint is the normal inner product** `exp(a) = |n·k|` (§II.G): the
joint contributes `a = ln|n·k|` to the action, so its exponential weight is exactly the inner product
of the two boundary normals. -/
lemma nullNonnullJointA_exp (nDotk : ℝ) (h : nDotk ≠ 0) :
    Real.exp (nullNonnullJointA nDotk) = |nDotk| := by
  unfold nullNonnullJointA
  rw [Real.exp_log (abs_pos.mpr h)]


/-- **The gravitational action normalization** `S = 16π G_N I` (Eq. 1.2). -/
noncomputable def gravAction (GN I : ℝ) : ℝ := 16 * Real.pi * GN * I

/-- **The complexity = action functional** `C = I/(πℏ)` (Brown et al; §I). -/
noncomputable def complexity (I hbar : ℝ) : ℝ := I / (Real.pi * hbar)

/-- **`dS/dt = 32π G_N M ⟺ dI/dt = 2M`** (Eqs. 3.29 ↔ 1.1): for the Wheeler–deWitt patch of a
Schwarzschild-AdS black hole with `I := S/(16πG_N)`, the late-time rate `dS/dt = 32πG_N M` is
equivalent to `dI/dt = 2M`, since `dS/dt = 16πG_N dI/dt` and `16πG_N ≠ 0`. -/
lemma dSdt_iff_dIdt (GN M dIdt dSdt : ℝ) (hGN : GN ≠ 0)
    (hrel : dSdt = 16 * Real.pi * GN * dIdt) :
    dSdt = 32 * Real.pi * GN * M ↔ dIdt = 2 * M := by
  rw [hrel, show (32 : ℝ) * Real.pi * GN * M = 16 * Real.pi * GN * (2 * M) by ring]
  have hne : (16 : ℝ) * Real.pi * GN ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hGN
  exact ⟨fun h => mul_left_cancel₀ hne h, fun h => by rw [h]⟩

/-- **The complexity grows at `dC/dt = 2M/(πℏ)`** (Eqs. 1.1, C = I/(πℏ)): given the complexity = action
rate `dI/dt = 2M`, the complexity `C = I/(πℏ)` grows linearly at late times with slope `2M/(πℏ)`. -/
lemma complexity_rate_of_dIdt (M hbar dIdt : ℝ) (h : dIdt = 2 * M) :
    dIdt / (Real.pi * hbar) = 2 * M / (Real.pi * hbar) := by rw [h]


/-- **The on-shell WdW action gives a pure-phase amplitude** (`complexActionWeight` hub): the
gravitational action `I` of a Wheeler–deWitt patch is **real** on shell (the null-boundary ambiguities
are real), so its amplitude weight `exp(iI/ℏ) = complexActionWeight I 0 ℏ` has modulus one — a unitary
pure phase, the `S_I = 0` case of the entropic damping `‖w‖ = exp(−S_I/ℏ)`. -/
lemma wdw_action_amplitude_pure_phase (I hbar : ℝ) :
    ‖complexActionWeight I 0 hbar‖ = 1 :=
  norm_complexActionWeight_zero_imag I hbar

end Physlib.QuantumMechanics.ComplexAction.NullBoundaryGravitationalAction

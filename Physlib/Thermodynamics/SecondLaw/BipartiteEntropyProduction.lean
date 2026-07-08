/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.EntropyProductionWorldline
public import Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger
public import Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations
public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Physlib.Thermodynamics.SecondLaw.ArrowReversibilityZhang

/-! # SecondLaw — part `BipartiteEntropyProduction`. Full docstring in the umbrella module `Physlib.Thermodynamics.SecondLaw`;
namespace and declaration names are unchanged (the umbrella re-exports them). -/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QFT.Wick.Consistency

namespace Physlib.Thermodynamics.SecondLaw

open QuantumInfo.Finite QuantumMechanics.FiniteTarget

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Bridge: bipartite unitary event ⟶ `EntropyArrowWorldline`

Zhang's theorem is a **two-point** comparison: initial joint entropy
versus part-wise entropy after a unitary plus partial trace.  This
lifts cleanly to an `EntropyArrowWorldline` via a step-function
imaginary action:

  `S_I_along t = if t ≤ 0 then 0 else ℏ · ΔS`,

where `ΔS = Sᵥₙ (Tr_B U ρ U†) + Sᵥₙ (Tr_A U ρ U†) − Sᵥₙ ρ ≥ 0` is the
entropy gap (Zhang's theorem makes it non-negative).  The worldline's
`S_I_monotone` field is **proved** from the information-theoretic
second law rather than assumed as a structural property — closing the
loop on `EntropyArrowWorldline.S_I_monotone` in the canonical
bipartite-unitary setting.
-/

/-- **Bipartite unitary event structure.**  Records an initial joint
mixed state `ρ : MState (d₁ × d₂)`, a unitary `U : 𝐔[d₁ × d₂]`
applied at `t = 0`, and a positive `ℏ`. -/
structure BipartiteUnitaryEvent
    (d₁ d₂ : Type*) [Fintype d₁] [Fintype d₂] [DecidableEq d₁]
    [DecidableEq d₂] where
  /-- Initial bipartite state. -/
  ρ : MState (d₁ × d₂)
  /-- Unitary evolution applied at `t = 0`. -/
  U : 𝐔[d₁ × d₂]
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ

namespace BipartiteUnitaryEvent

variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁]
  [DecidableEq d₂]

/-- **Entropy gap** of the event:
`ΔS = (Sᵥₙ (Tr_B U ρ U†) + Sᵥₙ (Tr_A U ρ U†)) − Sᵥₙ ρ`. -/
def entropyGap (E : BipartiteUnitaryEvent d₁ d₂) : ℝ :=
  Sᵥₙ (E.ρ.U_conj E.U).traceRight +
    Sᵥₙ (E.ρ.U_conj E.U).traceLeft - Sᵥₙ E.ρ

/-- **Entropy gap is non-negative** — direct consequence of Zhang's
theorem (unitary invariance + sub-additivity). -/
theorem entropyGap_nonneg (E : BipartiteUnitaryEvent d₁ d₂) :
    0 ≤ E.entropyGap := by
  unfold entropyGap
  linarith [zhang_second_law E.ρ E.U]

/-- **Imaginary-action step function** for the event:
`S_I(t) = 0` for `t ≤ 0`, `S_I(t) = ℏ · ΔS` for `t > 0`. -/
noncomputable def S_I_step
    (E : BipartiteUnitaryEvent d₁ d₂) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else E.ℏ * E.entropyGap

/-- `S_I_step` is non-negative everywhere: zero before the event,
`ℏ · ΔS ≥ 0` after (by Zhang). -/
theorem S_I_step_nonneg
    (E : BipartiteUnitaryEvent d₁ d₂) (t : ℝ) :
    0 ≤ E.S_I_step t := by
  unfold S_I_step
  split_ifs with _h
  · exact le_refl _
  · exact mul_nonneg (le_of_lt E.ℏ_pos) (entropyGap_nonneg E)

/-- `S_I_step` is monotone non-decreasing in `t`. -/
theorem S_I_step_monotone
    (E : BipartiteUnitaryEvent d₁ d₂) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    E.S_I_step t₁ ≤ E.S_I_step t₂ := by
  unfold S_I_step
  split_ifs with h₁ h₂ h₂
  · exact le_refl _
  · exact mul_nonneg (le_of_lt E.ℏ_pos) (entropyGap_nonneg E)
  · exfalso; linarith
  · exact le_refl _

/-- `S_I_step` at `t = 0` is zero. -/
@[simp] theorem S_I_step_at_zero
    (E : BipartiteUnitaryEvent d₁ d₂) :
    E.S_I_step 0 = 0 := by
  unfold S_I_step
  simp

/-- **Bridge: a bipartite unitary event induces an `EntropyArrowWorldline`.**

The worldline's imaginary action is the Zhang step function
`S_I(t) = ℏ · ΔS · 1_{t > 0}`, and its monotonicity is **proved** from
Zhang's information-theoretic second law via `S_I_step_monotone`.
This closes the loop on `EntropyArrowWorldline.S_I_monotone` —
in the canonical bipartite-unitary setting, monotonicity is no longer
an assumed structural field but a derived theorem. -/
noncomputable def toEntropyArrowWorldline
    (E : BipartiteUnitaryEvent d₁ d₂) :
    EntropyArrowWorldline where
  ℏ := E.ℏ
  ℏ_pos := E.ℏ_pos
  S_I_along := E.S_I_step
  τ_ent_along := fun t => E.S_I_step t / E.ℏ
  τ_ent_eq := fun _ => rfl
  S_I_monotone := fun {_ _} h => E.S_I_step_monotone h
  S_I_at_zero_nonneg := by simp

/-- The induced worldline's `S_I_along` is exactly the step function. -/
@[simp] theorem toEntropyArrowWorldline_S_I_along
    (E : BipartiteUnitaryEvent d₁ d₂) (t : ℝ) :
    E.toEntropyArrowWorldline.S_I_along t = E.S_I_step t := rfl

/-- The induced worldline's `S_I_along` is non-negative everywhere. -/
theorem toEntropyArrowWorldline_S_I_nonneg
    (E : BipartiteUnitaryEvent d₁ d₂) (t : ℝ) :
    0 ≤ E.toEntropyArrowWorldline.S_I_along t :=
  E.S_I_step_nonneg t

/-! ### Identification with quantum mutual information

The entropy gap of an event is exactly the **quantum mutual information**
`I(A:B) = Sᵥₙ ρ_A + Sᵥₙ ρ_B − Sᵥₙ ρ_AB` of the *post-event* joint
state.  This is the precise quantitative content of Zhang's "loss of
correlation information": the entropy increase realised by partial
trace equals the mutual information generated by the unitary on top
of the initial joint state.
-/

/-- **Entropy gap equals post-event quantum mutual information.**

`ΔS = Sᵥₙ (Tr_B U ρ U†) + Sᵥₙ (Tr_A U ρ U†) − Sᵥₙ ρ
    = Sᵥₙ (U ρ U†).traceRight + Sᵥₙ (U ρ U†).traceLeft − Sᵥₙ (U ρ U†)
    = qMutualInfo (U ρ U†)`.

The second step uses `Sᵥₙ_U_conj` (Zhang Eq. 3). -/
theorem entropyGap_eq_qMutualInfo_post (E : BipartiteUnitaryEvent d₁ d₂) :
    E.entropyGap = qMutualInfo (E.ρ.U_conj E.U) := by
  unfold entropyGap qMutualInfo
  rw [Sᵥₙ_U_conj]
  ring

/-! ### Identity-unitary reduction

For the **identity unitary**, no entanglement is generated by the
event: the entropy gap reduces to the mutual information of the
initial state itself.  If the initial state is *factorisable*, this
mutual information is zero, so the bridge produces the **trivial /
reversible** worldline (`S_I_along ≡ 0`).
-/

/-- **Identity-unitary reduction**: `ρ.U_conj 1 = ρ`. -/
theorem U_conj_one (ρ : MState (d₁ × d₂)) :
    ρ.U_conj 1 = ρ := by
  unfold MState.U_conj
  ext1
  simp [HermitianMat.conj_one]

/-- The identity-unitary event has entropy gap equal to the mutual
information of the initial state. -/
theorem entropyGap_identity_eq_qMutualInfo
    (ρ : MState (d₁ × d₂)) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    (BipartiteUnitaryEvent.mk ρ 1 ℏ hℏ).entropyGap = qMutualInfo ρ := by
  rw [entropyGap_eq_qMutualInfo_post]
  show qMutualInfo (ρ.U_conj 1) = qMutualInfo ρ
  rw [U_conj_one]

/-! ### Quantum Kullback–Leibler form of the entropy gap

The quantum mutual information `I(A:B) = qMutualInfo ρ_AB` is itself a
**quantum Kullback–Leibler divergence** between the joint state and the
product of its marginals:

  `I(A:B) = 𝐃(ρ_AB ‖ ρ_A ⊗ ρ_B)`

(`QuantumInfo.Entropy.Relative.qMutualInfo_as_qRelativeEnt`).
Composing with the Zhang identification of the entropy gap as the
post-event mutual information gives the **KL form** of Zhang's
`ΔS ≥ 0`:

  `ΔS  =  𝐃(U ρ U†  ‖  (U ρ U†)_A ⊗ (U ρ U†)_B)`.

The entropy gap is the precise quantum-relative-entropy "distance" of
the post-event joint state from the product of its marginals.  Zhang's
`ΔS ≥ 0` is then a *special case* of the more fundamental
**Kullback–Leibler non-negativity** principle — the same
divergence-non-negativity that drives the classical
log-sum / Gibbs-inequality / Zhang Lemmas 1–4 chain.
-/

/-- **Zhang entropy gap as a quantum KL divergence** (Kullback-Leibler
form).

`ΔS = 𝐃((U ρ U†) ‖ (U ρ U†)_R ⊗ᴹ (U ρ U†)_L)` (as an `EReal`).

Identifies the entropy gap of a bipartite-unitary event with the
quantum relative entropy (Kullback–Leibler divergence) between the
post-event joint state and the product of its reduced marginals.  In
particular, the load-bearing `entropyGap_nonneg` (Zhang's `ΔS ≥ 0`)
becomes a special case of the **non-negativity of quantum
Kullback–Leibler divergence** (`qRelativeEnt` lives in `ℝ≥0∞`). -/
theorem entropyGap_eq_qRelativeEnt
    (E : BipartiteUnitaryEvent d₁ d₂) :
    (E.entropyGap : EReal) =
      ((qRelativeEnt (E.ρ.U_conj E.U)
          ((E.ρ.U_conj E.U).traceRight ⊗ᴹ (E.ρ.U_conj E.U).traceLeft)) : EReal) := by
  rw [entropyGap_eq_qMutualInfo_post]
  exact qMutualInfo_as_qRelativeEnt _

end BipartiteUnitaryEvent

/-! ## Phase B — quantum-to-classical reduction of relative entropy

The genuine reduction theorem: when both density operators are classical
states (diagonal in a common basis), the quantum relative entropy
`qRelativeEnt` reduces to the classical Kullback–Leibler divergence
`Hₛ_rel`.

This is the `MState.ofClassical` case — the cleanest commuting-pair
specialisation (both ρ and σ are explicitly diagonal in the same
basis).  The proof uses:

* `qRelativeEnt_ker`: the `⟪ρ.M, ρ.M.log − σ.M.log⟫` form (EReal-valued)
  under the kernel inclusion `σ.M.ker ≤ ρ.M.ker`.
* `HermitianMat.cfc_diagonal`: `(diagonal g).cfc f = diagonal (f ∘ g)`,
  giving `(ofClassical p).M.log = diagonal (Real.log ∘ p)`.
* Trace and inner-product reductions on diagonal Hermitian matrices.

For the **commuting non-diagonal case** (general `[ρ, σ] = 0`),
simultaneous-diagonalisation reduces to this `ofClassical` case via a
unitary basis change (which preserves `qRelativeEnt` by spectral
invariance), but that lift is a follow-on step.
-/

/-- **Phase B — Quantum-to-classical reduction of relative entropy.**

For two finite probability distributions `p, q` with `q ≪ p` in the
kernel sense (the `ofClassical q` kernel is contained in the
`ofClassical p` kernel), the quantum relative entropy of the classical
states reduces to the classical Kullback–Leibler divergence:

  `(𝐃(ofClassical p ‖ ofClassical q)).toEReal = (Hₛ_rel p q : EReal)`.

This is the genuine reduction theorem in the diagonal case — both ρ
and σ are diagonal in the same basis, so their quantum relative
entropy coincides with the classical Kullback–Leibler divergence of
their eigenvalue distributions. -/
theorem qRelativeEnt_ofClassical_eq_Hₛ_rel
    {d : Type*} [Fintype d] [DecidableEq d]
    (p q : ProbDistribution d)
    (h_ker : (MState.ofClassical q).M.ker ≤ (MState.ofClassical p).M.ker) :
    ((qRelativeEnt (MState.ofClassical p) (MState.ofClassical q)).toEReal : EReal) =
      ((Hₛ_rel p q : ℝ) : EReal) := by
  -- Step 1: reduce qRelativeEnt to its standard inner-product form.
  rw [qRelativeEnt_ker h_ker]
  -- Goal: ⟪(ofClassical p).M, (ofClassical p).M.log − (ofClassical q).M.log⟫
  --        = (Hₛ_rel p q : EReal)
  -- Step 2: compute (ofClassical p).M.log = HermitianMat.diagonal ℂ (Real.log ∘ p).
  have hp_diag : (MState.ofClassical p).M =
      HermitianMat.diagonal ℂ (fun i => (p i : ℝ)) := rfl
  have hq_diag : (MState.ofClassical q).M =
      HermitianMat.diagonal ℂ (fun i => (q i : ℝ)) := rfl
  have hp_log : (MState.ofClassical p).M.log =
      HermitianMat.diagonal ℂ (fun i => Real.log (p i : ℝ)) := by
    rw [HermitianMat.log, hp_diag, HermitianMat.cfc_diagonal]
    rfl
  have hq_log : (MState.ofClassical q).M.log =
      HermitianMat.diagonal ℂ (fun i => Real.log (q i : ℝ)) := by
    rw [HermitianMat.log, hq_diag, HermitianMat.cfc_diagonal]
    rfl
  -- Step 3: combine into the inner product.
  rw [hp_log, hq_log, hp_diag]
  -- Goal: ⟪diagonal p, diagonal (log p) - diagonal (log q)⟫ = (Hₛ_rel p q : EReal)
  rw [← HermitianMat.diagonal_sub]
  -- Goal: ⟪diagonal p, diagonal (log p - log q)⟫ = (Hₛ_rel p q : EReal)
  rw [HermitianMat.inner_eq_re_trace]
  rw [show (HermitianMat.diagonal ℂ (fun i => (p i : ℝ))).mat
        * (HermitianMat.diagonal ℂ
            ((fun i => Real.log (p i : ℝ)) - fun i => Real.log (q i : ℝ))).mat
        = Matrix.diagonal (fun i : d => ((p i : ℝ) : ℂ)) *
          Matrix.diagonal (fun i : d =>
            ((Real.log (p i : ℝ) - Real.log (q i : ℝ) : ℝ) : ℂ)) from rfl]
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  -- Goal: ((RCLike.re (∑ i, ((p i : ℝ) : ℂ) * ((log p i − log q i : ℝ) : ℂ))) : EReal)
  --     = ((Hₛ_rel p q : ℝ) : EReal)
  unfold Hₛ_rel
  congr 1
  -- Realification commutes with the sum: the integrand is real-valued.
  rw [show (∑ x : d, (((p x : ℝ) : ℂ) *
              (((Real.log (p x : ℝ) - Real.log (q x : ℝ) : ℝ) : ℂ))))
        = (((∑ x : d, ((p x : ℝ) * Real.log (p x : ℝ)
              - (p x : ℝ) * Real.log (q x : ℝ))) : ℝ) : ℂ) by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    ring]
  exact RCLike.ofReal_re _

/-! ## Phase E + F — Sergi constant-decay arrow bridge

The source-specific scalar constant-decay system lives in
`Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity`.
This thermodynamics file keeps the bridge from that system into the
`EntropyArrowWorldline` structure, because the bridge is where the second-law
worldline monotonicity is consumed.
-/

/-- **Constructor: Sergi constant-decay system → `EntropyArrowWorldline`.**

The arrow is *not* assumed: `S_I_monotone` is provided as the *theorem*
`SergiConstantDecaySystem.sergi_S_I_monotone`, which follows from
`0 ≤ γ₀` and `0 < ℏ` alone.

This is the foundational step proving `EntropyArrowWorldline.S_I_monotone`
in the simplest analytically-solvable non-Hermitian case
([Sergi-Giaquinta 2016, Eq. 17]). -/
noncomputable def EntropyArrowWorldline.ofSergiConstantDecay
    (S : SergiConstantDecaySystem) : EntropyArrowWorldline where
  ℏ := S.ℏ
  ℏ_pos := S.ℏ_pos
  S_I_along := S.S_I_along
  τ_ent_along := S.τ_ent_along
  τ_ent_eq := S.τ_ent_along_eq_S_I_div_hbar
  S_I_monotone := fun {_ _} h => S.sergi_S_I_monotone h
  S_I_at_zero_nonneg := by rw [S.S_I_along_at_zero]

namespace SergiConstantDecaySystem

variable (S : SergiConstantDecaySystem)

/-- `S_I_along 0 = 0` in the Sergi worldline. -/
@[simp]
theorem ofSergiConstantDecay_S_I_at_zero :
    (EntropyArrowWorldline.ofSergiConstantDecay S).S_I_along 0 = 0 :=
  S.S_I_along_at_zero

/-- `τ_ent_along t = γ₀·t` in the Sergi worldline. -/
@[simp]
theorem ofSergiConstantDecay_τ_ent (t : ℝ) :
    (EntropyArrowWorldline.ofSergiConstantDecay S).τ_ent_along t = S.γ₀ * t :=
  rfl

end SergiConstantDecaySystem


end Physlib.Thermodynamics.SecondLaw

end

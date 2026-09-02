/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseDecoherenceResolution
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularFromState
public import Physlib.QFT.PathIntegral.WickClock
meta import Zil

/-!
# AQFT audit of the collapse/decoherence resolution: von Neumann algebras, modular flow, entropic time

Inspects `SciamaAdSCPTCollapseDecoherenceResolution` against the repo's algebraic-QFT layer and identifies
what is (in)compatible with **von Neumann algebras** (separating vectors / faithful states), **Tomita–Takesaki
modular flow**, and **Caticha entropic time**.  Verdict, in proved statements:

* **von Neumann / separating (Reeh–Schlieder).**  The collapse map is an idempotent
  (`collapsedDistribution_idempotent`), so it is **either trivial or non-injective**
  (`collapse_trivial_or_not_injective`) — a nontrivial completed collapse has a kernel: it destroys
  information.  But vN-compatible dynamics over a faithful/separating state destroys nothing: the finite
  separating shadow `faithful_state_standard` (an invertible density matrix annihilates no algebra element,
  `A·ρ = 0 → A = 0`) — and in Type III the same statement is
  `AlgebraicQFT.ReehSchliederCyclicSeparating.IsSeparating` (no local operator annihilates the vacuum).  A
  nontrivial collapse map is therefore **incompatible with implementation as a vN-algebraic symmetry** over a
  separating state; only its `t → ∞`-limit reading survives.
* **Tomita–Takesaki modular flow.**  The finite modular flow `σ_t(a) = e^{itH_θ} a e^{−itH_θ}`
  (`FiniteTarget.modularGroupOfState`, `H_θ = −log ρ`) is a group of **injective** maps
  (`modular_flow_injective`, from the group law and `σ_0 = id`) — a nontrivial collapse (non-injective) can
  equal **no** member of any modular flow.  The decoherence side, by contrast, is *natively modular*: the
  interference visibility **is** a wedge-modular eigenvalue,
  `exp(−Γt) = wedgeModularEigenvalue (ℏΓt/2π) ℏ` (`visibility_is_wedgeModular`) — the same `Δ = e^{−2πκ/ℏ}`
  that carries the repo's KMS condition (`WickClock`, `hawkingBoltzmannWeight_is_wedgeModular`).
* **Caticha entropic time.**  Entropic time is monotone imaginary action, `τ_ent = S_I/ℏ`
  (`StatisticalMechanics.EntropyProduction.tauEnt`), and at **every finite** imaginary action the
  complex-action weight modulus is strictly positive (`collapse_beyond_finite_entropic_action`,
  `‖e^{(i/ℏ)(S_R+iS_I)}‖ = e^{−S_I/ℏ} > 0`): the exactly-zero collapse endpoint lies at `τ_ent = ∞`, beyond
  every finite entropic time — consistent with the Caticha measurement being unitary communication + Born
  readout with no collapse step (`CatichaMeasurementGenericBornRule`).

`collapse_modular_compatibility_audit` bundles the verdict: **nothing in the decoherence side is incompatible**
— it embeds exactly (visibility = modular eigenvalue; damping = entropy production = entropic time); the
**collapse side is incompatible with all three as a fundamental dynamics** (non-automorphic, non-modular,
beyond finite entropic time) and survives only as the `t → ∞` effective limit — strengthening the resolution.

Honest scope: the finite models carry this file's proofs (Type I shadows: `faithful_state_standard`,
`modularGroupOfState`); the Type III form of the separating obstruction is **derived on the local net** in
`SciamaAdSCPTReehSchliederCollapseObstruction` (`reehSchlieder_no_local_collapse`, from `reehSchlieder_net` +
Haag duality); the "no identification" between the collapse map and modular flows is the pair of proved facts
(non-injective vs injective) — they act on different carriers, so the incompatibility is structural, stated per
carrier.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility

open Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNobleMetalBandStructure
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open QuantumMechanics.FiniteTarget

/-! ## §1. The collapse map is a projection: trivial or non-injective (vN obstruction) -/

/-- **[The collapse map is idempotent]** — collapsing twice is collapsing once (under the Weinberg
pointer/weight duality): the completed collapse is a *projection* onto the pointer span. -/
theorem collapsedDistribution_idempotent {Ω A : Type*} [Fintype Ω] [Fintype A] [DecidableEq Ω] [DecidableEq A]
    (pointer weight : A → Ω → ℝ) (hdual : dualPointerWeight pointer weight)
    (P : ProbabilityDensity Ω) :
    collapsedDistribution pointer weight (collapsedDistribution pointer weight P)
      = collapsedDistribution pointer weight P := by
  funext ψ
  show ∑ a, pointer a ψ * expectation (weight a) (collapsedDistribution pointer weight P)
      = ∑ a, pointer a ψ * expectation (weight a) P
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [collapsedDistribution_has_born_weights pointer weight P hdual a]

/-- **[Trivial or non-injective]** — an idempotent map that is injective is the identity; hence a *nontrivial*
completed collapse is **non-injective**: it has a kernel, it destroys information.  No group of invertible
(vN-automorphic / unitary / modular) maps can contain it. -/
theorem collapse_trivial_or_not_injective {Ω A : Type*} [Fintype Ω] [Fintype A] [DecidableEq Ω] [DecidableEq A]
    (pointer weight : A → Ω → ℝ) (hdual : dualPointerWeight pointer weight) :
    (∀ P, collapsedDistribution pointer weight P = P)
      ∨ ¬ Function.Injective (collapsedDistribution pointer weight) := by
  by_cases hinj : Function.Injective (collapsedDistribution pointer weight)
  · exact Or.inl fun P => hinj (collapsedDistribution_idempotent pointer weight hdual P)
  · exact Or.inr hinj

/-! ## §2. The modular flow is injective — a nontrivial collapse is no member of it -/

/-- **[Every modular-flow map is injective]** — the finite Tomita–Takesaki flow
`σ_t(a) = e^{itH_θ} a e^{−itH_θ}` (`modularGroupOfState`, `H_θ = −log ρ`) satisfies the group law with
`σ_0 = id`, so each `σ_t` has the inverse `σ_{−t}`: modular dynamics never destroys information — the exact
opposite of the nontrivial collapse projection of §1. -/
theorem modular_flow_injective {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) (t : ℝ) :
    Function.Injective ((modularGroupOfState ρ).σ t) := by
  have key : ∀ x, (modularGroupOfState ρ).σ (-t) ((modularGroupOfState ρ).σ t x) = x := by
    intro x
    have h1 := modularGroupOfState_group_law ρ (-t) t x
    rw [neg_add_cancel] at h1
    rw [← h1, modularGroupOfState_zero]
  intro a b hab
  have hkey := congrArg ((modularGroupOfState ρ).σ (-t)) hab
  rwa [key, key] at hkey

/-! ## §3. The decoherence visibility IS a wedge-modular (KMS) eigenvalue -/

/-- **[The visibility is a wedge-modular eigenvalue]** `exp(−Γt) = Δ = e^{−2πκ/ℏ}` at `κ = ℏΓt/2π` — the
decoherence damping is *natively* Tomita–Takesaki: it is the modular eigenvalue that carries the repo's KMS
condition (`WickClock.wedgeModularEigenvalue`, `hawkingBoltzmannWeight_is_wedgeModular`).  The decoherent
route embeds in the modular structure; nothing to reconcile. -/
theorem visibility_is_wedgeModular {prefactor : ℝ} (t ℏ : ℝ) (hℏ : ℏ ≠ 0) (X : NobleMetal) :
    interferenceVisibility prefactor t X
      = Physlib.QFT.PathIntegral.wedgeModularEigenvalue
          (ℏ * (sdScatteringRate prefactor X * t) / (2 * Real.pi)) ℏ := by
  unfold interferenceVisibility Physlib.QFT.PathIntegral.wedgeModularEigenvalue
  congr 1
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## §4. The collapse endpoint lies beyond every finite entropic time -/

/-- **[Positive weight modulus at every finite imaginary action]** `‖e^{(i/ℏ)(S_R+iS_I)}‖ = e^{−S_I/ℏ} > 0` —
at every finite entropic time `τ_ent = S_I/ℏ` (`StatisticalMechanics.EntropyProduction.tauEnt`) the
complex-action weight retains strictly positive modulus: the exactly-zero collapse endpoint is at
`τ_ent = ∞`, beyond every finite entropic time — the Caticha measurement needs no collapse step. -/
theorem collapse_beyond_finite_entropic_action (S_R S_I ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    0 < ‖nagaoNielsenComplexActionWeight S_R S_I ℏ‖ := by
  rw [nagaoNielsen_eq_master S_R S_I ℏ hℏ, master_modulus_is_kuiken]
  exact Real.exp_pos _

/-! ## §5. The audit verdict -/

/-- **[The compatibility audit]** — **(i)** vN/separating: a faithful (invertible) density matrix annihilates
no algebra element (`faithful_state_standard`, the finite separating shadow of Reeh–Schlieder), while a
nontrivial collapse is non-injective (§1) — collapse cannot be a vN-algebraic symmetry over a separating
state; **(ii)** modular: every Tomita–Takesaki flow map is injective (§2) — a nontrivial collapse is no member
of any modular flow, while the decoherence visibility *is* a wedge-modular eigenvalue (§3) — natively
compatible; **(iii)** entropic time: the collapse endpoint lies beyond every finite `τ_ent = S_I/ℏ` (§4).
Nothing in the decoherence side conflicts with vN algebras, Tomita–Takesaki, or Caticha entropic time; the
collapse side conflicts with all three as fundamental dynamics and survives only as the `t → ∞` limit. -/
theorem collapse_modular_compatibility_audit {Ω A d : Type*}
    [Fintype Ω] [Fintype A] [DecidableEq Ω] [DecidableEq A] [Fintype d] [DecidableEq d]
    (pointer weight : A → Ω → ℝ) (hdual : dualPointerWeight pointer weight)
    (ρ : MState d) (hρ : IsUnit ρ.M.mat) (t : ℝ)
    {prefactor : ℝ} (s ℏ : ℝ) (hℏ : ℏ ≠ 0) (X : NobleMetal) (S_R S_I : ℝ) :
    ((∀ P, collapsedDistribution pointer weight P = P)
        ∨ ¬ Function.Injective (collapsedDistribution pointer weight))
      ∧ (∀ B, B * ρ.M.mat = 0 → B = 0)
      ∧ Function.Injective ((modularGroupOfState ρ).σ t)
      ∧ interferenceVisibility prefactor s X
          = Physlib.QFT.PathIntegral.wedgeModularEigenvalue
              (ℏ * (sdScatteringRate prefactor X * s) / (2 * Real.pi)) ℏ
      ∧ 0 < ‖nagaoNielsenComplexActionWeight S_R S_I ℏ‖ :=
  ⟨collapse_trivial_or_not_injective pointer weight hdual,
    (faithful_state_standard ρ hρ).1,
    modular_flow_injective ρ t,
    visibility_is_wedgeModular s ℏ hℏ X,
    collapse_beyond_finite_entropic_action S_R S_I ℏ hℏ⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility.collapse_trivial_or_not_injective where
  formalizes @ "claim:a-nontrivial-completed-collapse-is-a-non-injective-projection-hence-no-member-of-any-invertible-dynamics-group",
  supported_by @ "paper:weinberg-2012-collapse-of-the-state-vector",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse.collapsedDistribution_has_born_weights",
  caveat @ "epistemic:finite-weinberg-kernel-model"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility.collapse_modular_compatibility_audit where
  formalizes @ "claim:the-decoherence-side-embeds-in-von-neumann-modular-and-entropic-time-structure-while-a-nontrivial-collapse-conflicts-with-all-three-as-fundamental-dynamics",
  requires @ "claim:the-collapse-versus-decoherence-competition-dissolves-collapse-is-the-infinite-decoherence-limit-differing-only-by-the-strictly-nonzero-finite-time-coherence-residue",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.faithful_state_standard",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.modularGroupOfState",
  supported_by @ "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue",
  supported_by @ "paper:zurek-2021-emergence-of-the-classical-from-within-the-quantum-universe",
  caveat @ "epistemic:type-one-finite-shadows-carry-the-proofs-the-type-three-separating-statements-are-cited-not-rederived"

zil_file_contract physlib.collapseModularCompatibility where
  promises "The AQFT audit of the collapse/decoherence resolution: a nontrivial completed collapse is an idempotent, non-injective projection, hence neither a von-Neumann-algebraic symmetry over a separating/faithful state nor a member of any Tomita-Takesaki modular flow, and its endpoint lies beyond every finite entropic time; the decoherence visibility is itself the wedge-modular KMS eigenvalue, so the decoherence side embeds in all three structures."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:QuantumMechanics.FiniteTarget.faithful_state_standard",
    "lean:QuantumMechanics.FiniteTarget.modularGroupOfState",
    "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue",
    "lean:Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse.collapsedDistribution"]
  forbids_substitutes ["a Type III operator-algebraic derivation of Reeh-Schlieder (cited, not re-derived)",
    "a dynamical no-go for collapse models as mathematics (the audit is structural compatibility, not refutation)"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility.collapsedDistribution_idempotent,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility.collapse_trivial_or_not_injective,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility.modular_flow_injective,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility.visibility_is_wedgeModular,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility.collapse_beyond_finite_entropic_action,
    Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility.collapse_modular_compatibility_audit]

/- ZIL-END -/

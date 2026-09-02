/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# Koopman quantization of a reversible discrete dynamics

The general quantization of a bijection `σ` of an arbitrary state set: the
Koopman lift acts on square-summable amplitudes `ℓ²` by substitution
(Koopman's Hilbert-space formulation of deterministic dynamics), and the
Page-Wootters timeless constraint of
`Physlib.QuantumMechanics.RelationalTime` characterizes its stationary sector
orbit by orbit:

* **The Koopman lift.** Substitution by the inverse step (`koopman`) is
  well defined on `ℓ²` for every bijection, norm-preserving
  (`koopman_norm_eq` - reversibility quantizes to unitarity), and transports
  basis states exactly as the classical dynamics (`koopman_single` - the
  classical dynamics is the shadow of its quantum lift on the computational
  basis).
* **The timeless constraint.** The Page-Wootters Hamiltonian constraint with
  total operator `U - 1` (`koopmanTimelessConstraint`) is the discrete
  Wheeler-DeWitt operator of the quantized dynamics: physical states are the
  stationary states `U ψ = ψ` (`isPhysical_iff_fixed`), the discrete
  time-independent Schrodinger condition.
* **The orbit dichotomy.** A stationary amplitude is constant along every
  orbit (`stationary_forward`); any amplitude supported on the fixed points
  is stationary (`stationary_of_support_fixed`); and on a point with
  infinite forward orbit a square-summable stationary amplitude must vanish
  (`stationary_vanishes_on_infinite_orbit`) - a constant on infinitely many
  sites is not square-summable unless zero. Normalizable time-independent
  Schrodinger solutions live only where the classical dynamics recurs.

Instances live with their models: the integer automaton of
`Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality` quantizes its
homogeneous shear here and obtains the exact zero-momentum characterization
of its timeless sector.

**Honest boundary.** Stationarity means eigenvalue one of the step unitary -
no spectral theory beyond that eigenvalue, no continuous-time generator, and
no measure-theoretic Koopmanism; the state set is arbitrary but the amplitude
space is the discrete `ℓ²`.
-/

set_option autoImplicit false

open scoped ENNReal

@[expose] public section

namespace Physlib.QuantumMechanics.KoopmanQuantization

open Physlib.QuantumMechanics.RelationalTime

variable {ι : Type*}

/-- The exponent of the amplitude space is positive. -/
lemma two_toReal_pos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by
  norm_num

/-- The exponent of the amplitude space as a natural power. -/
lemma two_toReal_eq : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by
  norm_num

/-- **The Koopman lift** of a bijection of the state set: substitution by the
inverse step on square-summable amplitudes - the quantization of a reversible
deterministic dynamics as a linear substitution operator on `ℓ²`. -/
noncomputable def koopman (σ : ι ≃ ι) (ψ : lp (fun _ : ι => ℂ) 2) :
    lp (fun _ : ι => ℂ) 2 :=
  ⟨fun x => ψ (σ.symm x), by
    refine memℓp_gen ?_
    exact (((lp.memℓp ψ).summable two_toReal_pos).comp_injective
      σ.symm.injective).congr fun x => rfl⟩

@[simp] lemma koopman_apply (σ : ι ≃ ι) (ψ : lp (fun _ : ι => ℂ) 2)
    (x : ι) : (koopman σ ψ : ι → ℂ) x = ψ (σ.symm x) := rfl

/-- **The Koopman lift is an isometry**: the quantum step preserves the
amplitude norm - reversibility quantizes to unitarity. -/
@[zil_level physical_theorem]
theorem koopman_norm_eq (σ : ι ≃ ι) (ψ : lp (fun _ : ι => ℂ) 2) :
    ‖koopman σ ψ‖ = ‖ψ‖ := by
  rw [lp.norm_eq_tsum_rpow two_toReal_pos, lp.norm_eq_tsum_rpow two_toReal_pos]
  congr 1
  calc ∑' x : ι, ‖(koopman σ ψ : ι → ℂ) x‖ ^ (2 : ℝ≥0∞).toReal
      = ∑' x : ι, ‖ψ (σ.symm x)‖ ^ (2 : ℝ≥0∞).toReal := rfl
    _ = ∑' x : ι, ‖ψ x‖ ^ (2 : ℝ≥0∞).toReal :=
        Equiv.tsum_eq σ.symm fun i => ‖ψ i‖ ^ (2 : ℝ≥0∞).toReal

/-- **The classical shadow**: the Koopman lift transports basis states exactly
as the classical dynamics transports states - the quantized dynamics
restricted to the computational basis is the dynamics itself. -/
@[zil_level physical_theorem]
theorem koopman_single [DecidableEq ι] (σ : ι ≃ ι) (x : ι) (c : ℂ) :
    koopman σ (lp.single 2 x c) = lp.single 2 (σ x) c := by
  apply lp.ext
  funext y
  simp only [koopman_apply, lp.coeFn_single, Pi.single_apply, Equiv.symm_apply_eq]

/-- The Koopman lift as a linear map. -/
noncomputable def koopmanLinear (σ : ι ≃ ι) :
    lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun := koopman σ
  map_add' ψ φ := by
    apply lp.ext
    funext x
    simp only [koopman_apply, lp.coeFn_add, Pi.add_apply]
  map_smul' c ψ := by
    apply lp.ext
    funext x
    simp only [koopman_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]

/-- The Koopman lift as a continuous linear map (bounded by its isometry). -/
noncomputable def koopmanCLM (σ : ι ≃ ι) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  (koopmanLinear σ).mkContinuous 1 fun ψ => by
    rw [show koopmanLinear σ ψ = koopman σ ψ from rfl, koopman_norm_eq, one_mul]

@[simp] lemma koopmanCLM_apply (σ : ι ≃ ι) (ψ : lp (fun _ : ι => ℂ) 2) :
    koopmanCLM σ ψ = koopman σ ψ := rfl

/-- **The Koopman lift as a surjective linear isometry** of `ℓ²`: the unitary
quantization of any reversible classical relabeling `σ`, with inverse the Koopman
lift of `σ.symm` and norm preservation `koopman_norm_eq`. -/
noncomputable def koopmanStateStep (σ : ι ≃ ι) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun := koopman σ
  invFun := koopman σ.symm
  left_inv ψ := by
    apply lp.ext
    funext x
    simp [koopman_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv ψ := by
    apply lp.ext
    funext x
    simp [koopman_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  map_add' := (koopmanLinear σ).map_add
  map_smul' := (koopmanLinear σ).map_smul
  norm_map' := koopman_norm_eq σ

@[simp] theorem koopmanStateStep_apply (σ : ι ≃ ι)
    (ψ : lp (fun _ : ι => ℂ) 2) (x : ι) :
    koopmanStateStep σ ψ x = ψ (σ.symm x) :=
  rfl

/-- **The timeless constraint of a quantized dynamics**: the Page-Wootters
Hamiltonian constraint whose total operator is `U - 1` for the Koopman step
unitary `U` - the discrete Wheeler-DeWitt operator; its kernel is the
stationary (time-independent Schrodinger) sector. -/
noncomputable def koopmanTimelessConstraint (σ : ι ≃ ι) :
    HamiltonianConstraint (lp (fun _ : ι => ℂ) 2) where
  H_total := koopmanCLM σ - ContinuousLinearMap.id ℂ _

/-- **Physical iff stationary**: the timeless constraint selects exactly the
fixed states of the quantum step - the discrete time-independent Schrodinger
condition `U ψ = ψ`. -/
@[zil_level bridge_theorem]
theorem isPhysical_iff_fixed (σ : ι ≃ ι) (ψ : lp (fun _ : ι => ℂ) 2) :
    (koopmanTimelessConstraint σ).IsPhysical ψ ↔ koopman σ ψ = ψ := by
  unfold HamiltonianConstraint.IsPhysical koopmanTimelessConstraint
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    koopmanCLM_apply]
  exact sub_eq_zero

/-- A stationary amplitude pulls back along the inverse step pointwise. -/
lemma stationary_pointwise {σ : ι ≃ ι} {ψ : lp (fun _ : ι => ℂ) 2}
    (h : koopman σ ψ = ψ) (y : ι) : ψ (σ.symm y) = ψ y := by
  have happ : (koopman σ ψ : ι → ℂ) y = ψ y := by rw [h]
  rw [koopman_apply] at happ
  exact happ

/-- **Stationary amplitudes are constant along orbits**: `ψ (σ y) = ψ y` for
every state `y`. -/
@[zil_level physical_theorem]
theorem stationary_forward {σ : ι ≃ ι} {ψ : lp (fun _ : ι => ℂ) 2}
    (h : koopman σ ψ = ψ) (y : ι) : ψ (σ y) = ψ y := by
  have h1 := stationary_pointwise h (σ y)
  rw [Equiv.symm_apply_apply] at h1
  exact h1.symm

/-- **Fixed-point-supported amplitudes are stationary**: a state whose
amplitude vanishes on every moved point solves the time-independent
Schrodinger condition of the quantum step. -/
@[zil_level physical_theorem]
theorem stationary_of_support_fixed {σ : ι ≃ ι} {ψ : lp (fun _ : ι => ℂ) 2}
    (h : ∀ y : ι, σ y ≠ y → ψ y = 0) :
    koopman σ ψ = ψ := by
  apply lp.ext
  funext y
  rw [koopman_apply]
  rcases eq_or_ne (σ.symm y) y with hy | hy
  · rw [hy]
  · have hmoved : σ (σ.symm y) ≠ σ.symm y := by
      rw [Equiv.apply_symm_apply]
      exact fun hcontra => hy hcontra.symm
    have hymoved : σ y ≠ y := by
      intro hcontra
      refine hy ?_
      rw [← hcontra, Equiv.symm_apply_apply]
      exact hcontra.symm
    rw [h (σ.symm y) hmoved, h y hymoved]

/-- A stationary amplitude is constant along the forward orbit. -/
lemma stationary_orbit_const {σ : ι ≃ ι} {ψ : lp (fun _ : ι => ℂ) 2}
    (h : koopman σ ψ = ψ) (x : ι) (n : ℕ) : ψ ((⇑σ)^[n] x) = ψ x := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', stationary_forward h, ih]

/-- **No normalizable stationary amplitude on an infinite orbit**: if the
forward orbit of `x` never repeats, a square-summable stationary amplitude
vanishes at `x` - it is constant along infinitely many distinct sites, and a
nonzero constant is not square-summable. Normalizable time-independent
Schrodinger solutions of a quantized dynamics live only where the classical
dynamics recurs. -/
@[zil_level physical_theorem]
theorem stationary_vanishes_on_infinite_orbit {σ : ι ≃ ι}
    {ψ : lp (fun _ : ι => ℂ) 2} (h : koopman σ ψ = ψ) {x : ι}
    (horb : Function.Injective fun n : ℕ => (⇑σ)^[n] x) :
    ψ x = 0 := by
  have hsummable := (lp.memℓp ψ).summable two_toReal_pos
  have hcomp := hsummable.comp_injective horb
  have hconstsum : Summable fun _ : ℕ => ‖ψ x‖ ^ (2 : ℝ≥0∞).toReal := by
    refine hcomp.congr fun n => ?_
    show ‖ψ ((⇑σ)^[n] x)‖ ^ (2 : ℝ≥0∞).toReal = _
    rw [stationary_orbit_const h]
  have hzero : ‖ψ x‖ ^ (2 : ℝ≥0∞).toReal = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstsum.tendsto_atTop_zero
  rw [two_toReal_eq, Real.rpow_natCast] at hzero
  have hnorm : ‖ψ x‖ = 0 :=
    (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hzero
  exact norm_eq_zero.mp hnorm

/-- **Unimodular configurations are not square-summable**: a function of
constant norm one on an infinite state set lies outside the amplitude space -
the exact form of the infinite-energy exclusion of unimodular (edge-type)
configurations from `ℓ²`. -/
@[zil_level physical_theorem]
theorem unimodular_not_memℓp [Infinite ι] (f : ι → ℂ)
    (h : ∀ x, ‖f x‖ = 1) : ¬ Memℓp f 2 := by
  intro hmem
  have hsum := hmem.summable two_toReal_pos
  have hemb := Infinite.natEmbedding ι
  have hcomp := hsum.comp_injective hemb.injective
  have hconst : Summable fun _ : ℕ => (1 : ℝ) := by
    refine hcomp.congr fun n => ?_
    show ‖f (hemb n)‖ ^ (2 : ℝ≥0∞).toReal = 1
    rw [h (hemb n), Real.one_rpow]
  have hzero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst.tendsto_atTop_zero
  norm_num at hzero

end Physlib.QuantumMechanics.KoopmanQuantization

end

open Physlib.QuantumMechanics.KoopmanQuantization in
#physlib_axiom_clean_all [
  koopman_norm_eq,
  koopman_single,
  isPhysical_iff_fixed,
  stationary_forward,
  stationary_of_support_fixed,
  stationary_orbit_const,
  stationary_vanishes_on_infinite_orbit,
  unimodular_not_memℓp ]

open Physlib.QuantumMechanics.KoopmanQuantization in
#physlib_non_vacuous_all [
  koopman_norm_eq,
  koopman_single,
  isPhysical_iff_fixed,
  stationary_forward,
  stationary_of_support_fixed,
  stationary_orbit_const,
  stationary_vanishes_on_infinite_orbit,
  unimodular_not_memℓp ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.KoopmanQuantization.koopman_norm_eq where
  formalizes @ "claim:the-koopman-lift-of-a-reversible-dynamics-is-an-isometry-of-the-amplitude-space",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:koopman-1931-hamiltonian-systems-and-transformations-in-hilbert-space"

zil attach Physlib.QuantumMechanics.KoopmanQuantization.koopman_single where
  formalizes @ "claim:the-quantized-dynamics-acts-on-basis-states-exactly-as-the-classical-dynamics",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:koopman-1931-hamiltonian-systems-and-transformations-in-hilbert-space"

zil attach Physlib.QuantumMechanics.KoopmanQuantization.isPhysical_iff_fixed where
  formalizes @ "claim:the-page-wootters-constraint-of-a-quantized-dynamics-selects-the-stationary-states",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint",
  supported_by @ "paper:page-wootters-1983-evolution-without-evolution-dynamics-described-by-stationary-observables"

zil attach Physlib.QuantumMechanics.KoopmanQuantization.stationary_of_support_fixed where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:fixed-point-supported-amplitudes-solve-the-time-independent-schrodinger-condition",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.KoopmanQuantization.stationary_vanishes_on_infinite_orbit where
  formalizes @ "claim:no-normalizable-stationary-amplitude-lives-on-an-infinite-orbit",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:stationarity-is-eigenvalue-one-of-the-step-unitary-no-further-spectral-theory-is-formalized"

zil attach Physlib.QuantumMechanics.KoopmanQuantization.unimodular_not_memℓp where
  formalizes @ "claim:unimodular-configurations-on-an-infinite-state-set-are-not-square-summable",
  epistemic_status @ "consistency-identity"

zil_file_contract physlib.koopmanQuantization where
  promises "The general Koopman quantization of a bijection of an arbitrary state set: the substitution lift is well defined and norm-preserving on square-summable amplitudes, shadows the classical dynamics on basis states, carries the Page-Wootters timeless constraint with total operator U minus one whose physical states are the stationary states, and its stationary sector is characterized orbit by orbit - constant along orbits, solvable on fixed-point support, and vanishing on every infinite orbit."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint",
    "lean:lp.single", "lean:Memℓp", "lean:Equiv.tsum_eq"]
  forbids_substitutes ["spectral theory of the Koopman operator beyond the eigenvalue-one sector",
    "a continuous-time Koopman generator or measure-theoretic Koopmanism",
    "amplitude spaces other than the discrete square-summable space"]
  witnessed_by [
    Physlib.QuantumMechanics.KoopmanQuantization.koopman_norm_eq,
    Physlib.QuantumMechanics.KoopmanQuantization.koopman_single,
    Physlib.QuantumMechanics.KoopmanQuantization.isPhysical_iff_fixed,
    Physlib.QuantumMechanics.KoopmanQuantization.stationary_forward,
    Physlib.QuantumMechanics.KoopmanQuantization.stationary_of_support_fixed,
    Physlib.QuantumMechanics.KoopmanQuantization.stationary_vanishes_on_infinite_orbit,
    Physlib.QuantumMechanics.KoopmanQuantization.unimodular_not_memℓp ]

/- ZIL-END -/

#zil_formalization_lint physlib.koopmanQuantization


/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock
public import Physlib.QuantumMechanics.KoopmanQuantization
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.ZMod.Basic

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.BornCompositionCorrelation -/

/- Consolidated from Physlib.QuantumMechanics.BornCompositionCorrelation -/

/-!
# Born-distribution composition and Koopman correlation generation

Two interacting subsystems live on the product state index `ι × κ`.  A coupling
permutation that does not factor over the two factors generates statistical
correlation between the subsystems.

The bridge is the Born distribution `bornDist ψ i = ‖ψ i‖²`.  The Koopman
quantization of a classical relabeling transports the Born distribution by the
classical pushforward (`bornDist_koopmanStateStep`).  A product (non-interacting)
relabeling keeps a product Born distribution a product, so its total correlation
stays zero; a coupling relabeling — here the shear `(i, j) ↦ (i, i + j)`, the
finite analogue of a controlled shift — turns a product Born distribution into a
genuinely correlated one, so `totalCorrelation` becomes strictly positive.

The correlation is measured by the already-formalized
`TotalCorrelationEntropicClock.totalCorrelation`; nothing about entropy or
mutual information is re-proved here.  This is a statement about the reversible
Koopman dynamics on `ℓ²(ι × κ)` and its Born distribution, not a full tensor
product of arbitrary Hilbert spaces: the composite here is a coordinate product
index, and the coupling is a permutation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality

namespace Physlib.QuantumMechanics.BornCompositionCorrelation

open Physlib.QuantumMechanics.KoopmanQuantization

/-! ## The Born distribution and its Koopman pushforward -/

/-- The **Born distribution** of a state: the squared modulus of each amplitude. -/
def bornDist {ι : Type*} (ψ : lp (fun _ : ι => ℂ) 2) (i : ι) : ℝ :=
  ‖(ψ : ι → ℂ) i‖ ^ 2

theorem bornDist_nonneg {ι : Type*} (ψ : lp (fun _ : ι => ℂ) 2) (i : ι) : 0 ≤ bornDist ψ i := by
  unfold bornDist; positivity

/-- **The Koopman state step transports the Born distribution by the classical
pushforward**: the reversible unitary induced by a relabeling `σ` moves the Born
weight at `i` to what sat at `σ.symm i`. -/
@[zil_level structural]
theorem bornDist_koopmanStateStep {ι : Type*} (σ : ι ≃ ι) (ψ : lp (fun _ : ι => ℂ) 2) (i : ι) :
    bornDist (koopmanStateStep σ ψ) i = bornDist ψ (σ.symm i) := by
  unfold bornDist
  rw [show ((koopmanStateStep σ ψ : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i = (ψ : ι → ℂ) (σ.symm i) from
    koopmanStateStep_apply σ ψ i]

/-! ## The Born boundary is a probability distribution when normalized

`bornDist` is the quantum-to-classical boundary map: it sends a Hilbert-space
state to a real weight on the index.  For a finite carrier its weights sum to the
squared norm, so a normalized state maps to a genuine finite probability
distribution — the typed interface the correlation theorems consume. -/

/-- **The Born boundary normalization law**: on a finite carrier the Born weights
sum to the squared norm. -/
@[zil_level physical_theorem]
theorem bornDist_sum_eq_normSq {ι : Type*} [Fintype ι] (ψ : lp (fun _ : ι => ℂ) 2) :
    ∑ i, bornDist ψ i = ‖ψ‖ ^ 2 := by
  unfold bornDist
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) ψ, lp.inner_eq_tsum, tsum_fintype, map_sum]
  exact Finset.sum_congr rfl fun i _ => (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- A normalized state's Born boundary is a probability distribution: its weights
are nonnegative and sum to one. -/
theorem bornDist_sum_one_of_norm_one {ι : Type*} [Fintype ι] (ψ : lp (fun _ : ι => ℂ) 2)
    (h : ‖ψ‖ = 1) : ∑ i, bornDist ψ i = 1 := by
  rw [bornDist_sum_eq_normSq, h, one_pow]

/-! ## Generic distribution relabeling

The Koopman state step acts on the Born boundary as a classical relabeling
(pushforward).  Relabeling preserves total weight and nonnegativity, and a
*product* relabeling `σ × τ` keeps a product distribution a product — so a
non-interacting step cannot generate correlation.  The coupling shear is a
relabeling that is not of product form, which is exactly why it can. -/

/-- **Relabeling a distribution** by a bijection of its index — the classical
pushforward, the boundary image of a Koopman state step. -/
def relabelDist {ι : Type*} (σ : ι ≃ ι) (p : ι → ℝ) : ι → ℝ :=
  fun i => p (σ.symm i)

@[simp] theorem relabelDist_apply {ι : Type*} (σ : ι ≃ ι) (p : ι → ℝ) (i : ι) :
    relabelDist σ p i = p (σ.symm i) :=
  rfl

theorem relabelDist_refl {ι : Type*} (p : ι → ℝ) :
    relabelDist (Equiv.refl ι) p = p :=
  rfl

theorem relabelDist_nonneg {ι : Type*} (σ : ι ≃ ι) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (i : ι) : 0 ≤ relabelDist σ p i :=
  hp _

/-- Relabeling preserves the total weight. -/
theorem relabelDist_sum {ι : Type*} [Fintype ι] (σ : ι ≃ ι) (p : ι → ℝ) :
    ∑ i, relabelDist σ p i = ∑ i, p i :=
  Equiv.sum_comp σ.symm p

/-- **The Born boundary of a Koopman step is the relabeled Born boundary** — the
state-space step realizes the classical pushforward on the boundary. -/
theorem bornDist_koopman_eq_relabel {ι : Type*} (σ : ι ≃ ι) (ψ : lp (fun _ : ι => ℂ) 2) :
    bornDist (koopmanStateStep σ ψ) = relabelDist σ (bornDist ψ) :=
  funext fun i => bornDist_koopmanStateStep σ ψ i

/-- **A product relabeling keeps a product distribution a product**: an
`σ × τ` relabeling of `f ⊗ g` is `(f ∘ σ⁻¹) ⊗ (g ∘ τ⁻¹)`, still a product, so it
cannot generate correlation between the factors. -/
@[zil_level structural]
theorem relabelDist_prodCongr_product {ι κ : Type*} (σ : ι ≃ ι) (τ : κ ≃ κ)
    (f : ι → ℝ) (g : κ → ℝ) :
    relabelDist (Equiv.prodCongr σ τ) (fun z => f z.1 * g z.2)
      = fun z => f (σ.symm z.1) * g (τ.symm z.2) :=
  rfl

/-- **A normalized product distribution has zero total correlation** — the generic
independence statement the concrete demo instantiates. -/
@[zil_level physical_theorem]
theorem totalCorrelation_product_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → ℝ) (G : κ → ℝ) (hF : ∑ i, F i = 1) (hG : ∑ j, G j = 1) :
    totalCorrelation (fun z : ι × κ => F z.1 * G z.2) = 0 := by
  apply totalCorrelation_eq_zero_of_independent
  intro z
  have hmF : marginalFst (fun z : ι × κ => F z.1 * G z.2) z.1 = F z.1 := by
    unfold marginalFst
    simp only []
    rw [← Finset.mul_sum, hG, mul_one]
  have hmS : marginalSnd (fun z : ι × κ => F z.1 * G z.2) z.2 = G z.2 := by
    unfold marginalSnd
    simp only []
    rw [← Finset.sum_mul, hF, one_mul]
  rw [hmF, hmS]

/-- **Product-local dynamics preserve independence**: relabeling a normalized
product distribution by a product bijection keeps it a product with zero total
correlation.  A non-interacting step cannot generate correlation, in general — the
shear generates correlation only because it is not of product form. -/
@[zil_level physical_theorem]
theorem product_local_preserves_zero_correlation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι ≃ ι) (τ : κ ≃ κ) (F : ι → ℝ) (G : κ → ℝ)
    (hF : ∑ i, F i = 1) (hG : ∑ j, G j = 1) :
    totalCorrelation (relabelDist (Equiv.prodCongr σ τ) (fun z => F z.1 * G z.2)) = 0 := by
  rw [relabelDist_prodCongr_product]
  exact totalCorrelation_product_zero (fun i => F (σ.symm i)) (fun j => G (τ.symm j))
    (Equiv.sum_comp σ.symm F |>.trans hF) (Equiv.sum_comp τ.symm G |>.trans hG)

/-! ## A state realizing a prescribed distribution -/

/-- A finite ℓ² state from an arbitrary amplitude function. -/
def l2OfFun {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) : lp (fun _ : ι => ℂ) 2 :=
  ∑ i : ι, f i • lp.single 2 i 1

theorem l2OfFun_coe {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) (j : ι) :
    ((l2OfFun f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j = f j := by
  unfold l2OfFun
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_single,
    smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j f, if_pos (Finset.mem_univ j)]

/-- A state whose Born distribution is a prescribed nonnegative distribution: the
amplitudes are the pointwise square roots. -/
def stateOfDist {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) : lp (fun _ : ι => ℂ) 2 :=
  ∑ i : ι, (Real.sqrt (p i) : ℂ) • lp.single 2 i 1

theorem stateOfDist_coe {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (j : ι) :
    ((stateOfDist p : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j = (Real.sqrt (p j) : ℂ) := by
  unfold stateOfDist
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_single,
    smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j (fun i => (Real.sqrt (p i) : ℂ))]
  rw [if_pos (Finset.mem_univ j)]

/-- **The prescribed nonnegative distribution is exactly the state's Born
distribution.** -/
theorem stateOfDist_bornDist {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (j : ι) : bornDist (stateOfDist p) j = p j := by
  unfold bornDist
  rw [stateOfDist_coe, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp j)]

/-- Expansion of a real sum over the two elements of `ZMod 2`. -/
theorem sum_zmod_two (f : ZMod 2 → ℝ) : ∑ i : ZMod 2, f i = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_pair (by decide)]

/-! ## The coupling relabeling and its Born pushforward -/

/-- The **coupling shear** `(i, j) ↦ (i, i + j)` on the product index — the finite
analogue of a controlled shift, a relabeling that does not factor over the two
factors. -/
def coupleShear (N : ℕ) : ZMod N × ZMod N ≃ ZMod N × ZMod N where
  toFun z := (z.1, z.1 + z.2)
  invFun z := (z.1, z.2 - z.1)
  left_inv z := by
    obtain ⟨i, j⟩ := z
    simp only [add_sub_cancel_left]
  right_inv z := by
    obtain ⟨i, j⟩ := z
    simp only [add_sub_cancel]

@[simp] theorem coupleShear_symm_apply (N : ℕ) (z : ZMod N × ZMod N) :
    (coupleShear N).symm z = (z.1, z.2 - z.1) :=
  rfl

/-- **The coupling Koopman step moves the Born weight along the shear.** -/
theorem bornDist_coupleShear {N : ℕ} (ψ : lp (fun _ : ZMod N × ZMod N => ℂ) 2)
    (z : ZMod N × ZMod N) :
    bornDist (koopmanStateStep (coupleShear N) ψ) z
      = bornDist ψ (z.1, z.2 - z.1) := by
  rw [bornDist_koopmanStateStep, coupleShear_symm_apply]

/-! ## A concrete product state and the correlation the coupling generates -/

/-- A biased single-factor weight `3/4, 1/4`. -/
def demoG (i : ZMod 2) : ℝ := if i = 0 then 3 / 4 else 1 / 4

/-- A uniform single-factor weight `1/2, 1/2`. -/
def demoF (_ : ZMod 2) : ℝ := 1 / 2

/-- The product (non-interacting) joint distribution `demoF ⊗ demoG`. -/
def demoJoint (z : ZMod 2 × ZMod 2) : ℝ := demoF z.1 * demoG z.2

/-- The sheared (interacting) joint distribution — the Born pushforward of
`demoJoint` under the coupling. -/
def shearDemo (z : ZMod 2 × ZMod 2) : ℝ := demoJoint (z.1, z.2 - z.1)

/-- The demo is an instance of the generic relabeling layer: the sheared
distribution is the coupling relabeling of the product distribution.  The
coupling shear is not a product relabeling, which is why — unlike
`relabelDist_prodCongr_product` — it generates correlation. -/
theorem shearDemo_eq_relabel : shearDemo = relabelDist (coupleShear 2) demoJoint :=
  rfl

@[simp] theorem demoF_val (i : ZMod 2) : demoF i = 1 / 2 := rfl

@[simp] theorem demoG_zero : demoG 0 = 3 / 4 := by rw [demoG, if_pos rfl]

@[simp] theorem demoG_one : demoG 1 = 1 / 4 := by rw [demoG, if_neg (by decide)]

theorem demoG_pos (i : ZMod 2) : 0 < demoG i := by
  unfold demoG; split_ifs <;> norm_num

theorem demoJoint_pos (z : ZMod 2 × ZMod 2) : 0 < demoJoint z :=
  mul_pos (by rw [demoF_val]; norm_num) (demoG_pos z.2)

theorem sum_demoG : ∑ j : ZMod 2, demoG j = 1 := by
  rw [sum_zmod_two, demoG_zero, demoG_one]; norm_num

theorem sum_demoF : ∑ i : ZMod 2, demoF i = 1 := by
  rw [sum_zmod_two, demoF_val, demoF_val]; norm_num

theorem marginalFst_demoJoint (i : ZMod 2) : marginalFst demoJoint i = demoF i := by
  unfold marginalFst
  rw [sum_zmod_two (fun j => demoJoint (i, j))]
  show demoF i * demoG 0 + demoF i * demoG 1 = demoF i
  rw [demoF_val, demoG_zero, demoG_one]; norm_num

theorem marginalSnd_demoJoint (j : ZMod 2) : marginalSnd demoJoint j = demoG j := by
  unfold marginalSnd
  rw [sum_zmod_two (fun i => demoJoint (i, j))]
  show demoF 0 * demoG j + demoF 1 * demoG j = demoG j
  rw [demoF_val, demoF_val]; ring

/-- **The product state carries no total correlation.** -/
theorem demoJoint_independent (z : ZMod 2 × ZMod 2) :
    demoJoint z = marginalFst demoJoint z.1 * marginalSnd demoJoint z.2 := by
  rw [marginalFst_demoJoint, marginalSnd_demoJoint]
  rfl

theorem totalCorrelation_demoJoint : totalCorrelation demoJoint = 0 :=
  totalCorrelation_eq_zero_of_independent demoJoint demoJoint_independent

/-! ## The sheared distribution is genuinely correlated -/

theorem shearDemo_pos (z : ZMod 2 × ZMod 2) : 0 < shearDemo z :=
  demoJoint_pos _

theorem shearDemo_00 : shearDemo (0, 0) = 3 / 8 := by
  show demoF 0 * demoG ((0 : ZMod 2) - 0) = 3 / 8
  rw [sub_zero, demoF_val, demoG_zero]; norm_num

theorem shearDemo_01 : shearDemo (0, 1) = 1 / 8 := by
  show demoF 0 * demoG ((1 : ZMod 2) - 0) = 1 / 8
  rw [sub_zero, demoF_val, demoG_one]; norm_num

theorem shearDemo_10 : shearDemo (1, 0) = 1 / 8 := by
  show demoF 1 * demoG ((0 : ZMod 2) - 1) = 1 / 8
  rw [show ((0 : ZMod 2) - 1) = 1 from by decide, demoF_val, demoG_one]; norm_num

theorem shearDemo_11 : shearDemo (1, 1) = 3 / 8 := by
  show demoF 1 * demoG ((1 : ZMod 2) - 1) = 3 / 8
  rw [sub_self, demoF_val, demoG_zero]; norm_num

theorem shearDemo_sum_one : ∑ z : ZMod 2 × ZMod 2, shearDemo z = 1 := by
  rw [Fintype.sum_prod_type, sum_zmod_two]
  rw [sum_zmod_two (fun j => shearDemo (0, j)), sum_zmod_two (fun j => shearDemo (1, j))]
  rw [shearDemo_00, shearDemo_01, shearDemo_10, shearDemo_11]; norm_num

theorem marginalFst_shearDemo_zero : marginalFst shearDemo 0 = 1 / 2 := by
  unfold marginalFst
  rw [sum_zmod_two (fun j => shearDemo (0, j)), shearDemo_00, shearDemo_01]; norm_num

theorem marginalSnd_shearDemo_one : marginalSnd shearDemo 1 = 1 / 2 := by
  unfold marginalSnd
  rw [sum_zmod_two (fun i => shearDemo (i, 1)), shearDemo_01, shearDemo_11]; norm_num

/-- **The sheared state is not independent**: at `(0, 1)` the joint weight `1/8`
differs from the product of its marginals `1/4`. -/
theorem shearDemo_not_independent :
    ¬ (∀ z, shearDemo z = marginalFst shearDemo z.1 * marginalSnd shearDemo z.2) := by
  intro h
  have hz := h (0, 1)
  rw [shearDemo_01, marginalFst_shearDemo_zero, marginalSnd_shearDemo_one] at hz
  norm_num at hz

/-- **The coupling generates strictly positive total correlation.** -/
theorem totalCorrelation_shearDemo_pos : 0 < totalCorrelation shearDemo := by
  rcases lt_or_eq_of_le
    (totalCorrelation_nonneg shearDemo (fun z => shearDemo_pos z) shearDemo_sum_one) with h | h
  · exact h
  · exfalso
    exact shearDemo_not_independent
      ((totalCorrelation_eq_zero_iff_independent shearDemo (fun z => shearDemo_pos z)
        shearDemo_sum_one).mp h.symm)

/-! ## Native correlation generation -/

theorem stateOfDemo_bornDist : bornDist (stateOfDist demoJoint) = demoJoint :=
  funext (stateOfDist_bornDist demoJoint (fun i => (demoJoint_pos i).le))

theorem coupled_bornDist :
    bornDist (koopmanStateStep (coupleShear 2) (stateOfDist demoJoint)) = shearDemo := by
  funext z
  rw [bornDist_coupleShear, stateOfDemo_bornDist]
  rfl

/-- **A non-interacting product state has zero total correlation.** -/
@[zil_level physical_theorem]
theorem product_state_no_correlation :
    totalCorrelation (bornDist (stateOfDist demoJoint)) = 0 := by
  rw [stateOfDemo_bornDist, totalCorrelation_demoJoint]

/-- **The interaction generates correlation between the subsystems**: applying the
coupling Koopman step to the product state produces a Born distribution with
strictly positive total correlation, from an initial state that had none. -/
@[zil_level bridge_theorem]
theorem coupling_generates_correlation :
    0 < totalCorrelation
      (bornDist (koopmanStateStep (coupleShear 2) (stateOfDist demoJoint))) := by
  rw [coupled_bornDist]
  exact totalCorrelation_shearDemo_pos

zil attach bornDist_koopmanStateStep where
  formalizes @ "claim:the-koopman-state-step-transports-the-born-distribution-by-the-classical-pushforward",
  supported_by @ "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopmanStateStep",
  epistemic_status @ "consistency-identity"

zil attach stateOfDist_bornDist where
  formalizes @ "claim:the-square-root-amplitude-state-realizes-a-prescribed-nonnegative-born-distribution",
  supported_by @ "mathlib:Real.sq_sqrt"

zil attach product_local_preserves_zero_correlation where
  formalizes @ "claim:generic-product-local-dynamics-preserve-independence-and-zero-classical-total-correlation",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.totalCorrelation_product_zero"

zil attach product_state_no_correlation where
  formalizes @ "claim:a-non-interacting-product-state-carries-zero-total-correlation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_zero_of_independent"

zil attach coupling_generates_correlation where
  formalizes @ "claim:a-coupling-koopman-step-generates-strictly-positive-total-correlation-from-a-product-state",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation_eq_zero_iff_independent",
  caveat @ "claim:the-composite-is-a-coordinate-product-index-with-a-permutation-coupling-not-a-general-hilbert-tensor-product-of-arbitrary-models",
  epistemic_status @ "consistency-identity"

zil attach bornDist_sum_eq_normSq where
  formalizes @ "claim:the-finite-born-boundary-weights-sum-to-the-squared-norm",
  supported_by @ "mathlib:inner_self_eq_norm_sq"

zil attach relabelDist_prodCongr_product where
  formalizes @ "claim:a-product-relabeling-keeps-a-product-distribution-a-product-so-cannot-generate-correlation",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.relabelDist",
  epistemic_status @ "consistency-identity"

zil_file_contract physlib.bornCompositionCorrelation where
  promises "This module supplies a composite face on the product state index: the Born distribution of a state is squared amplitude, and the Koopman quantization of a classical relabeling transports it by the classical pushforward. A product relabeling keeps a product Born distribution independent with zero total correlation, while the coupling shear relabeling - the finite controlled shift - turns the concrete product state into one whose Born distribution has strictly positive total correlation, generating subsystem correlation from an interaction that a non-interacting step cannot produce. The Born boundary is typed: its finite weights sum to the squared norm, so a normalized state maps to a genuine probability distribution, and the Koopman step acts on it as a generic distribution relabeling whose product form provably cannot generate correlation. The correlation is the repository's existing totalCorrelation, not re-proved here."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopmanStateStep",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.marginalFst"
  ]
  forbids_substitutes [
    "claiming a general Hilbert tensor product of two arbitrary Hilbert spaces",
    "calling the coordinate product index an operator-space tensor product",
    "identifying the permutation coupling with an arbitrary entangling gate",
    "reading positive total correlation as a specific measured entanglement value"
  ]
  witnessed_by [
    bornDist_koopmanStateStep,
    bornDist_sum_eq_normSq,
    relabelDist_prodCongr_product,
    totalCorrelation_product_zero,
    product_local_preserves_zero_correlation,
    product_state_no_correlation,
    coupling_generates_correlation
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.bornCompositionCorrelation

end Physlib.QuantumMechanics.BornCompositionCorrelation

/- Consolidated from Physlib.QuantumMechanics.BornCompositionProductState -/

/-!
# The product-state constructor on the entropic composite carrier

`BornCompositionCorrelation` composes systems on the coordinate-product ℓ² carrier
`lp (fun _ : ι × κ => ℂ) 2` and proves that a product *distribution* has zero total correlation while
the shear coupling generates it.  What it lacked was a genuine product-*state* constructor `ψ ⊗ φ` on
that carrier (it only carried the classical product *distribution* `demoF ⊗ demoG`).  This module
adds it, matching the `Ket`-layer `⊗ᵠ` on the framework's own ℓ² type.

* `l2Prod` — the product state `(ψ ⊗ φ)(i,j) = ψ(i)·φ(j)` on `lp (fun _ : ι × κ => ℂ) 2`.
* `bornDist_l2Prod` — its Born distribution factorizes: `bornDist (ψ ⊗ φ) (i,j) = bornDist ψ i · bornDist φ j`.
* `totalCorrelation_l2Prod_zero` — a product state of two normalized states has **zero total
  correlation** — the framework's own carrier realizes the uncorrelated composite.

Honest scope: this is the product (separable) sector of composition on the framework's ℓ² carrier;
it is not the general Hilbert tensor product of arbitrary Hilbert spaces, and the coupling that
generates correlation remains a coordinate-index permutation (Koopman), not an arbitrary entangling
gate — the general/infinite tensor product stays in the separate QuantumInfo `MState`/`Ket` layer.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.BornCompositionProductState

open Physlib.QuantumMechanics.BornCompositionCorrelation
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock

/-- **The product state** `(ψ ⊗ φ)(i,j) = ψ(i)·φ(j)` on the coordinate-product ℓ² carrier — a genuine
product-state constructor on the framework's own Hilbert carrier. -/
def l2Prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ψ : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2) : lp (fun _ : ι × κ => ℂ) 2 :=
  l2OfFun (fun z : ι × κ => (ψ : ι → ℂ) z.1 * (φ : κ → ℂ) z.2)

/-- **The Born distribution of a product state factorizes**:
`bornDist (ψ ⊗ φ) (i,j) = bornDist ψ i · bornDist φ j`. -/
@[zil_level bridge_theorem]
theorem bornDist_l2Prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ψ : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2) (z : ι × κ) :
    bornDist (l2Prod ψ φ) z = bornDist ψ z.1 * bornDist φ z.2 := by
  simp only [bornDist, l2Prod, l2OfFun_coe, norm_mul, mul_pow]

/-- **A product state of two normalized states has zero total correlation** — the framework's own
composite carrier realizes an uncorrelated (separable) composite, matching
`totalCorrelation_product_zero` for the product distribution. -/
@[zil_level physical_theorem]
theorem totalCorrelation_l2Prod_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ψ : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    totalCorrelation (bornDist (l2Prod ψ φ)) = 0 := by
  have hb : bornDist (l2Prod ψ φ) = fun z : ι × κ => bornDist ψ z.1 * bornDist φ z.2 :=
    funext (bornDist_l2Prod ψ φ)
  rw [hb]
  exact totalCorrelation_product_zero (bornDist ψ) (bornDist φ)
    (bornDist_sum_one_of_norm_one ψ hψ) (bornDist_sum_one_of_norm_one φ hφ)

end Physlib.QuantumMechanics.BornCompositionProductState

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.BornCompositionProductState

zil attach bornDist_l2Prod where
  supported_by @ "lean:ProbDistribution.normalized",
  formalizes @ "claim:the-born-distribution-of-a-product-state-psi-tensor-phi-on-the-coordinate-product-l2-carrier-factorizes-as-the-product-of-the-factor-born-distributions"

zil attach totalCorrelation_l2Prod_zero where
  formalizes @ "claim:a-product-state-of-two-normalized-states-on-the-frameworks-own-composite-l2-carrier-has-zero-total-correlation-realizing-an-uncorrelated-separable-composite",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.totalCorrelation_product_zero"

zil_file_contract physlib.bornCompositionProductState where
  promises "The product-state constructor on the entropic composite carrier, filling the missing product-state piece of composition on the framework's own coordinate-product l2 carrier. The product state psi tensor phi at index i j equals psi at i times phi at j, a genuine product-state constructor on the framework's Hilbert carrier, matching the Ket-layer product on the framework's own l2 type. Its Born distribution factorizes as the product of the factor Born distributions, and a product state of two normalized states has zero total correlation, so the framework's own composite carrier realizes an uncorrelated separable composite matching the product-distribution zero-correlation theorem. Honest scope: this is the product separable sector of composition on the framework's l2 carrier, not the general Hilbert tensor product of arbitrary Hilbert spaces; the coupling that generates correlation remains a coordinate-index Koopman permutation, not an arbitrary entangling gate, and the general infinite tensor product stays in the separate QuantumInfo MState and Ket layer."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.bornDist",
    "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.l2OfFun",
    "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.totalCorrelation_product_zero"
  ]
  forbids_substitutes [
    "reading the product-state constructor on the coordinate-product l2 carrier as the general Hilbert tensor product of arbitrary Hilbert spaces or the coordinate-permutation coupling as an arbitrary entangling gate"
  ]
  witnessed_by [
    bornDist_l2Prod,
    totalCorrelation_l2Prod_zero
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.bornCompositionProductState

/- Consolidated from Physlib.QuantumMechanics.BornCompositionInfinite -/

/-!
# Quantum composition on the framework carrier, without finiteness

Statement 7 of the relational framework — composite systems live on tensor products — was
carried for *finite* factors only: `BornCompositionProductState.l2Prod` and the isometry
`EuclideanTensorCompositionIso.euclideanTensorEquiv` both require `Fintype`.  This module
removes the restriction.  For **arbitrary** index types the coordinate product

  `(ψ ⊗ φ)(i, k) = ψ(i) · φ(k)`

is a well-defined member of `ℓ²(ι × κ)` (§A), is bilinear (§B), multiplies inner products
and norms (§C), sends basis vectors to basis vectors, and has **dense span** (§D) — which is
the universal characterization of the Hilbert-space tensor product: `ℓ²(ι × κ)` *is*
`ℓ²(ι) ⊗ ℓ²(κ)`, with the algebraic tensor product sitting inside it as the span of the
products and the completion adding nothing but limits.  The framework's composite carrier
was never a stand-in for the tensor product; it is the tensor product.

The Born layer follows for free (§E): the Born distribution of an infinite product state
factorizes exactly as in the finite case, because `bornDist` was never finite to begin with.

**Honest layering.**  This is the tensor structure realized *on* `ℓ²(ι × κ)`; the abstract
tensor-product functor (associators, braidings, an `≃ₗᵢ` against a completed `⊗`) is not
constructed, since Mathlib's completed Hilbert tensor product is not available to weld to.
The density theorem is exactly the statement such a functor would need.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.BornCompositionInfinite

open Physlib.QuantumMechanics.BornCompositionCorrelation
open scoped ENNReal

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

variable {ι κ : Type*}

/-! ### §A — the product lands in ℓ² -/

/-- Two square-summable norm families have square-summable product over the product index. -/
theorem summable_norm_sq_mul (ψ : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2) :
    Summable fun z : ι × κ => ‖(ψ : ι → ℂ) z.1‖ ^ (2 : ℝ) * ‖(φ : κ → ℂ) z.2‖ ^ (2 : ℝ) := by
  have hψ : Summable fun i => ‖(ψ : ι → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).mp (lp.memℓp ψ)
  have hφ : Summable fun k => ‖(φ : κ → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).mp (lp.memℓp φ)
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h2] at hψ hφ
  exact hψ.mul_of_nonneg hφ (fun i => Real.rpow_nonneg (norm_nonneg _) _)
    fun k => Real.rpow_nonneg (norm_nonneg _) _

/-- **The coordinate product is square-summable**: `(i,k) ↦ ψ(i)φ(k)` belongs to `ℓ²(ι×κ)`
for any `ψ ∈ ℓ²(ι)`, `φ ∈ ℓ²(κ)` — no finiteness. -/
theorem memℓp_prod_mul (ψ : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2) :
    Memℓp (fun z : ι × κ => (ψ : ι → ℂ) z.1 * (φ : κ → ℂ) z.2) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h2]
  have hrw : (fun z : ι × κ => ‖(ψ : ι → ℂ) z.1 * (φ : κ → ℂ) z.2‖ ^ (2 : ℝ))
      = fun z : ι × κ => ‖(ψ : ι → ℂ) z.1‖ ^ (2 : ℝ) * ‖(φ : κ → ℂ) z.2‖ ^ (2 : ℝ) := by
    funext z
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [hrw]
  exact summable_norm_sq_mul ψ φ

/-- **The product state on the framework carrier, for arbitrary index types** —
`(ψ ⊗ φ)(i,k) = ψ(i)φ(k)` as an element of `ℓ²(ι × κ)`.  The infinite-dimensional
generalization of `BornCompositionProductState.l2Prod`. -/
noncomputable def l2ProdInfinite (ψ : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2) :
    lp (fun _ : ι × κ => ℂ) 2 :=
  ⟨fun z => (ψ : ι → ℂ) z.1 * (φ : κ → ℂ) z.2, memℓp_prod_mul ψ φ⟩

@[simp] theorem l2ProdInfinite_apply (ψ : lp (fun _ : ι => ℂ) 2)
    (φ : lp (fun _ : κ => ℂ) 2) (z : ι × κ) :
    (l2ProdInfinite ψ φ : ι × κ → ℂ) z = (ψ : ι → ℂ) z.1 * (φ : κ → ℂ) z.2 := rfl

/-! ### §B — bilinearity -/

theorem l2ProdInfinite_add_left (ψ ψ' : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2) :
    l2ProdInfinite (ψ + ψ') φ = l2ProdInfinite ψ φ + l2ProdInfinite ψ' φ := by
  apply lp.ext
  funext z
  simp only [l2ProdInfinite_apply, lp.coeFn_add, Pi.add_apply]
  ring

theorem l2ProdInfinite_add_right (ψ : lp (fun _ : ι => ℂ) 2) (φ φ' : lp (fun _ : κ => ℂ) 2) :
    l2ProdInfinite ψ (φ + φ') = l2ProdInfinite ψ φ + l2ProdInfinite ψ φ' := by
  apply lp.ext
  funext z
  simp only [l2ProdInfinite_apply, lp.coeFn_add, Pi.add_apply]
  ring

theorem l2ProdInfinite_smul_left (c : ℂ) (ψ : lp (fun _ : ι => ℂ) 2)
    (φ : lp (fun _ : κ => ℂ) 2) :
    l2ProdInfinite (c • ψ) φ = c • l2ProdInfinite ψ φ := by
  apply lp.ext
  funext z
  simp only [l2ProdInfinite_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem l2ProdInfinite_smul_right (c : ℂ) (ψ : lp (fun _ : ι => ℂ) 2)
    (φ : lp (fun _ : κ => ℂ) 2) :
    l2ProdInfinite ψ (c • φ) = c • l2ProdInfinite ψ φ := by
  apply lp.ext
  funext z
  simp only [l2ProdInfinite_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### §C — inner products and norms multiply -/

/-- Cauchy–Schwarz summability of the coordinate products. -/
theorem summable_norm_mul (ψ ψ' : lp (fun _ : ι => ℂ) 2) :
    Summable fun i => ‖(ψ : ι → ℂ) i‖ * ‖(ψ' : ι → ℂ) i‖ := by
  have hψ : Summable fun i => ‖(ψ : ι → ℂ) i‖ ^ 2 := by
    have hm := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp ψ)
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ≥0∞).toReal := by norm_num
    rw [← hcast] at hm
    simpa [Real.rpow_natCast] using hm
  have hψ' : Summable fun i => ‖(ψ' : ι → ℂ) i‖ ^ 2 := by
    have hm := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp ψ')
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ≥0∞).toReal := by norm_num
    rw [← hcast] at hm
    simpa [Real.rpow_natCast] using hm
  refine Summable.of_nonneg_of_le
    (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun i => ?_) ((hψ.add hψ').div_const 2)
  have hsq := sq_nonneg (‖(ψ : ι → ℂ) i‖ - ‖(ψ' : ι → ℂ) i‖)
  nlinarith [hsq, norm_nonneg ((ψ : ι → ℂ) i), norm_nonneg ((ψ' : ι → ℂ) i)]

/-- The coordinate inner products are norm-summable — Cauchy–Schwarz on the diagonal.
Stated in the `y·conj x` orientation that `RCLike.inner_apply` produces. -/
theorem summable_norm_inner_mul (ψ ψ' : lp (fun _ : ι => ℂ) 2) :
    Summable fun i => ‖(ψ' : ι → ℂ) i * (starRingEnd ℂ) ((ψ : ι → ℂ) i)‖ :=
  Summable.of_nonneg_of_le (fun i => norm_nonneg _)
    (fun i => le_of_eq (by rw [norm_mul, RCLike.norm_conj, mul_comm]))
    (summable_norm_mul ψ ψ')

/-- **Inner products multiply**: `⟪ψ⊗φ, ψ'⊗φ'⟫ = ⟪ψ,ψ'⟫·⟪φ,φ'⟫` — the defining identity of
the Hilbert tensor product, on the framework carrier, for arbitrary index types. -/
theorem inner_l2ProdInfinite (ψ ψ' : lp (fun _ : ι => ℂ) 2) (φ φ' : lp (fun _ : κ => ℂ) 2) :
    ⟪l2ProdInfinite ψ φ, l2ProdInfinite ψ' φ'⟫ = ⟪ψ, ψ'⟫ * ⟪φ, φ'⟫ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [RCLike.inner_apply, l2ProdInfinite_apply]
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_inner_mul ψ ψ')
    (summable_norm_inner_mul φ φ')]
  apply tsum_congr
  intro z
  simp only [map_mul]
  ring

/-- **Norms multiply**: `‖ψ⊗φ‖ = ‖ψ‖·‖φ‖` — the product embedding is an isometry on pure
tensors. -/
theorem norm_l2ProdInfinite (ψ : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2) :
    ‖l2ProdInfinite ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  have h := inner_l2ProdInfinite ψ ψ φ φ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h1 : ‖l2ProdInfinite ψ φ‖ ^ 2 = ‖ψ‖ ^ 2 * ‖φ‖ ^ 2 := by exact_mod_cast h
  have h4 : ‖l2ProdInfinite ψ φ‖ = Real.sqrt (‖ψ‖ ^ 2 * ‖φ‖ ^ 2) := by
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  rw [h4, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

/-! ### §D — basis vectors map to basis vectors, and the span is dense -/

/-- The product of two basis vectors is the corresponding product-index basis vector. -/
theorem l2ProdInfinite_single [DecidableEq ι] [DecidableEq κ] (i : ι) (k : κ) (a b : ℂ) :
    l2ProdInfinite (lp.single 2 i a) (lp.single 2 k b) = lp.single 2 (i, k) (a * b) := by
  apply lp.ext
  funext z
  obtain ⟨x, y⟩ := z
  simp only [l2ProdInfinite_apply, lp.single_apply, Prod.mk.injEq]
  by_cases hx : x = i <;> by_cases hy : y = k <;>
    simp [hx, hy, Prod.ext_iff]

/-- **The span of the product states is dense** — the universal-property half of "`ℓ²(ι×κ)`
is the Hilbert tensor product": every state of the composite system is a limit of finite
superpositions of products.  With `inner_l2ProdInfinite` (the algebraic tensor product embeds
isometrically) this characterizes the composite carrier as `ℓ²(ι) ⊗ ℓ²(κ)` completed —
nothing in the composite Hilbert space outruns entangled superpositions of products. -/
theorem dense_span_l2ProdInfinite [DecidableEq ι] [DecidableEq κ] :
    Dense (↑(Submodule.span ℂ
      (Set.range fun p : lp (fun _ : ι => ℂ) 2 × lp (fun _ : κ => ℂ) 2 =>
        l2ProdInfinite p.1 p.2)) : Set (lp (fun _ : ι × κ => ℂ) 2)) := by
  intro f
  have hsum : HasSum (fun z : ι × κ => lp.single 2 z ((f : ι × κ → ℂ) z)) f :=
    lp.hasSum_single (by norm_num) f
  refine mem_closure_of_tendsto hsum ?_
  filter_upwards with s
  refine Submodule.sum_mem _ fun z _ => ?_
  obtain ⟨i, k⟩ := z
  have hz : lp.single 2 (i, k) ((f : ι × κ → ℂ) (i, k))
      = l2ProdInfinite (lp.single 2 i ((f : ι × κ → ℂ) (i, k))) (lp.single 2 k 1) := by
    rw [l2ProdInfinite_single, mul_one]
  rw [hz]
  exact Submodule.subset_span ⟨(_, _), rfl⟩

/-! ### §E — the Born layer, now without finiteness -/

/-- **The Born distribution of an infinite product state factorizes**:
`P_{ψ⊗φ}(i,k) = P_ψ(i)·P_φ(k)` for arbitrary index types — statement 7's measurement face,
freed of the `Fintype` hypothesis that `BornCompositionProductState.bornDist_l2Prod`
carried. -/
theorem bornDist_l2ProdInfinite (ψ : lp (fun _ : ι => ℂ) 2) (φ : lp (fun _ : κ => ℂ) 2)
    (z : ι × κ) :
    bornDist (l2ProdInfinite ψ φ) z = bornDist ψ z.1 * bornDist φ z.2 := by
  simp [bornDist, l2ProdInfinite_apply, norm_mul, mul_pow]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.BornCompositionInfinite.inner_l2ProdInfinite where
  formalizes @ "claim:the-coordinate-product-of-two-square-summable-states-multiplies-inner-products-for-arbitrary-index-types-the-defining-identity-of-the-hilbert-tensor-product",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.bornDist"

zil attach Physlib.QuantumMechanics.BornCompositionInfinite.dense_span_l2ProdInfinite where
  supported_by @ "lean:bornDist_l2Prod",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionInfinite.l2ProdInfinite_single",
  formalizes @ "claim:the-span-of-product-states-is-dense-in-the-composite-carrier-so-l2-of-the-product-index-is-the-completed-hilbert-tensor-product-of-the-factors",
  derives @ "claim:relational-07-quantum-composition-holds-for-infinite-dimensional-factors-on-the-frameworks-own-carrier",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-tensor-structure-is-realized-on-the-composite-carrier-directly-an-abstract-tensor-functor-with-associators-is-not-constructed-because-mathlib-has-no-completed-hilbert-tensor-product-to-weld-to"

zil attach Physlib.QuantumMechanics.BornCompositionInfinite.bornDist_l2ProdInfinite where
  formalizes @ "claim:the-born-distribution-of-an-infinite-product-state-factorizes-exactly-as-in-the-finite-case",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionProductState.bornDist_l2Prod"

/- ZIL-END -/

end Physlib.QuantumMechanics.BornCompositionInfinite

end


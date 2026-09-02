/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.ContinuumCAR
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ElectronZitterbewegung
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion
meta import Zil

/-!
# The positron: the electron's CPT / charge-conjugate mirror

The positron `e⁺` is built as the charge conjugate `C(e⁻)` of the electron of `ComptonClock.ElectronZitterbewegung`,
so the two are one CPT pair: **same** mass, spin, and magnetic anomaly (CPT-invariant), **opposite** charge,
**mirror** knot.

* **§A — charge & charge conjugation.** The positron is the integer-winding `n = +3` state, charge `Q = +1`
  (`positron_charge`), the negation of the electron's `n = −3` (`positron_is_charge_conjugate`,
  `windingCharge 3 = −windingCharge (−3)` from `windingCharge_neg`); on the `(Q,B,L)` lattice
  `e⁺ = (1, 0, −1)` (`positron_quantumNumbers_eq`, the antilepton).
* **§B — topology (mirror trefoil).** The positron is the *mirror* trefoil — the electron's Chern-Simons-
  Witten Jones invariant under `A → A⁻¹` (`positron_trefoil_mirror`), and the trefoil is chiral so the
  positron is genuinely distinct from the electron (`positron_ne_electron`).
* **§C — the CPT-shared facets.** Spin-½ (`positron_is_fermion`, `ribbonTwist ½ = −1` — antiparticles have
  the same statistics), the same magnetic anomaly `a = K²−1` (`positron_anomaly_eq_schmidt_defect`), and
  annihilation with the electron (`positron_annihilates_electron`, `(Q,B,L)` cancel; and the knot
  unknotting `chargeState q · chargeState(−q) = 1`).
* **§D — the whole positron** (`positron_complete`): the main result mirroring `electron_complete`.
* **§E — the CPT/mirror double and weak link.** Counter-rotation has the same fermionic holonomy and
  therefore does not imply antimatter. Charge conjugation plus the mirror trefoil constructs the actual
  partner sector, while a rational Nambu rotation supplies arbitrarily weak nonzero continuum
  CAR-preserving mixings without fixing a physical coupling.

**Honest layering.** Proven: the positron's charge is `+1` (winding `+3`), it is the charge conjugate of
the electron (opposite charge, `(Q,B,L)` reversed), the mirror trefoil distinct from the electron, a spin-½
fermion with the same anomaly, and it annihilates the electron to the vacuum. The antiparticle/CPT
identification is the standard reading; the algebra (`windingCharge 3 = −windingCharge(−3)`,
`electronJones 2 ≠ positronJones 2`, `e⁻ + e⁺ = 0`) is exact. The positron's Zitterbewegung and double cover
are the *same* operators as the electron's (one Dirac field), so they are inherited from the hub rather than
restated.

## References

* Charge conjugation, the positron as `C(e⁻)`, particle–antiparticle annihilation. `Physlib`
  (`ComptonClock.ElectronZitterbewegung`, `AntiparticleConjugation`, `Winding.QuarkChargeWinding`,
  `ChernSimons.TrefoilFermionChernSimonsInvariant`).


-/

set_option autoImplicit false

open scoped RealInnerProductSpace

open Matrix Complex
open Quaternion
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.ContinuumCAR
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion
open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration
open Physlib.QuantumMechanics.ComplexAction.Fermion.AnnihilationTwoPhotons
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel


/-- **[Positron charge `+1`]** the positron is the integer-winding `n = +3` state, `Q = +1` — the mirror of
the electron's `n = −3` (`Winding.QuarkChargeWinding`). -/
lemma positron_charge : windingCharge 3 = 1 := by
  unfold windingCharge; norm_num

/-- **[The positron is the electron's charge conjugate]** `Q(e⁺) = −Q(e⁻)`: `windingCharge 3 = −windingCharge
(−3)` — opposite charges, the winding negated (`windingCharge_neg`). -/
lemma positron_is_charge_conjugate : windingCharge 3 = - windingCharge (-3) := by
  rw [positron_charge, Winding.QuarkChargeWinding.electron_charge]; norm_num

/-- **[Positron quantum numbers]** `e⁺ = (1, 0, −1)` — charge `+1`, antilepton `L = −1`
(`AntiparticleConjugation`). -/
lemma positron_quantumNumbers_eq : positron = ⟨1, 0, -1⟩ := positron_quantumNumbers


/-- **[Positron = mirror trefoil]** `⟨e⁺⟩ = A⁻⁷ + A⁻³ + A − A⁹` — the electron trefoil's Chern-Simons-Witten
Jones invariant under the charge-conjugation substitution `A → A⁻¹`
(`ChernSimons.TrefoilFermionChernSimonsInvariant.positronJones_eq`). -/
lemma positron_trefoil_mirror (A : ℂ) :
    positronJones A = (A ^ 7)⁻¹ + (A ^ 3)⁻¹ + A - A ^ 9 := positronJones_eq A

/-- **[Positron ≠ electron]** the trefoil is chiral, so the Jones invariant separates the positron from the
electron (`electronJones 2 ≠ positronJones 2`) — the topological particle/antiparticle distinction. -/
lemma positron_ne_electron : electronJones 2 ≠ positronJones 2 := trefoil_chiral_distinguishes


/-- **[The positron is a spin-½ fermion]** `ribbonTwist ½ = −1` — antiparticles carry the same spin and
statistics (CPT). -/
lemma positron_is_fermion : ribbonTwist (1 / 2) = -1 := ribbonTwist_fermion

/-- **[Same magnetic anomaly]** `a = K²−1` at the operating-point rapidity — CPT fixes the positron's `g−2` equal to
the electron's. -/
lemma positron_anomaly_eq_schmidt_defect (K : ℝ) (hK : 1 < K) :
    anomaly (rapidity K) = K ^ 2 - 1 := anomaly_rapidity K hK

/-- **[Electron–positron annihilation]** `e⁻ + e⁺ = vacuum`: all additive quantum numbers cancel
(`AntiparticleConjugation`). -/
lemma positron_annihilates_electron :
    Particles.BaryonLeptonNumberConservation.electron + positron = ⟨0, 0, 0⟩ :=
  electron_positron_annihilate

/-- **[The positron's Dirac dynamics is `CPT`-invariant]** `A·D(−p)·A⁻¹ = D(p)` with `A = (−i)γ⁵` — the
positron is the `CPT` image of the electron, living in the *same* `CPT`-invariant Dirac dynamics
(`PTSymmetricQFT.CPTDiracDynamics`); the dynamical `CPT` theorem is particle/antiparticle-symmetric. -/
lemma positron_dirac_cpt_invariant (p : Fin 4 → ℝ) (m : ℝ) :
    ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m :=
  cpt_diracOp_invariant p m


/-- **[The positron in one theorem]** the electron's CPT/charge-conjugate mirror: (i) charge `+1` as winding
`n = +3`; (ii) the charge conjugate of the electron (`Q(e⁺) = −Q(e⁻)`); (iii) `(Q,B,L) = (1,0,−1)`;
(iv) the mirror trefoil, distinct from the electron; (v) spin-½ (same statistics, CPT); (vi) the same `g−2`
anomaly `K²−1` (CPT); (vii) annihilation with the electron to the vacuum; (viii) the **dynamical CPT
theorem** `A·D(−p)·A⁻¹=D(p)` — the positron is the `CPT` image of the electron. Distinguishing facets
(charge, mirror knot) are reversed; CPT-shared facets (spin, anomaly, CPT-invariant dynamics) match the
electron. -/
lemma positron_complete (m : ℝ) (p : Fin 4 → ℝ) (q : ℤ) (K : ℝ) (hK : 1 < K) :
    windingCharge 3 = 1
      ∧ windingCharge 3 = - windingCharge (-3)
      ∧ positron = ⟨1, 0, -1⟩
      ∧ electronJones 2 ≠ positronJones 2
      ∧ ribbonTwist (1 / 2) = -1
      ∧ anomaly (rapidity K) = K ^ 2 - 1
      ∧ chargeState q * chargeState (-q) = 1
      ∧ ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m :=
  ⟨positron_charge, positron_is_charge_conjugate, positron_quantumNumbers,
    trefoil_chiral_distinguishes, ribbonTwist_fermion, anomaly_rapidity K hK,
    fermion_antifermion_unknots q, cpt_diracOp_invariant p m⟩

/-! ## E. CPT/mirror doubling and a continuum CAR-preserving link -/

set_option backward.isDefEq.respectTransparency false in
/-- The two orientations of the canonical CPT double. These are representation sectors; assigning both
sectors nonzero physical support is an additional dynamical or state-selection condition. -/
inductive CPTOrientation where
  | particle
  | antiparticle
  deriving DecidableEq, Fintype

namespace CPTOrientation

/-- Exchange the particle and antiparticle orientations. -/
def partner : CPTOrientation → CPTOrientation
  | .particle => .antiparticle
  | .antiparticle => .particle

@[simp] lemma partner_particle : partner .particle = .antiparticle := rfl

@[simp] lemma partner_antiparticle : partner .antiparticle = .particle := rfl

/-- CPT-sector exchange is an involution. -/
lemma partner_involutive : Function.Involutive partner := by
  intro s
  cases s <;> rfl

/-- The two orientations of the canonical double are distinct. -/
lemma partner_ne (s : CPTOrientation) : partner s ≠ s := by
  cases s <;> simp

end CPTOrientation

/-- Spinorial holonomy of an integer number of full turns. It records parity of the winding magnitude,
so reversing the orientation of the same winding does not turn a spinor into an antiparticle. -/
def spinorWindingHolonomy (w : ℤ) : ℂ := (-1 : ℂ) ^ w.natAbs

@[simp] lemma spinorWindingHolonomy_one : spinorWindingHolonomy 1 = -1 := by
  norm_num [spinorWindingHolonomy]

@[simp] lemma spinorWindingHolonomy_neg_one : spinorWindingHolonomy (-1) = -1 := by
  norm_num [spinorWindingHolonomy]

/-- Reversing a full-turn orientation preserves its spinorial holonomy. -/
lemma spinorWindingHolonomy_neg (w : ℤ) :
    spinorWindingHolonomy (-w) = spinorWindingHolonomy w := by
  simp [spinorWindingHolonomy]

/-- In the three-nodule region the reference and both counter-rotating nodules have the same spinorial
holonomy. Thus counter-rotation alone cannot supply the particle/antiparticle distinction. -/
@[zil_level physical_theorem]
lemma counterrotation_spinor_holonomy_eq (R : ThreeNodulePhaseRegion) :
    spinorWindingHolonomy (R.turn 0) = spinorWindingHolonomy (R.turn 1)
      ∧ spinorWindingHolonomy (R.turn 0) = spinorWindingHolonomy (R.turn 2) := by
  rw [R.reference_turn, R.left_counter_turn, R.right_counter_turn]
  simp

/-- A CPT/mirror double on a trefoil presentation. The partner reverses all additive quantum numbers
and evaluates the mirror knot invariant by `A ↦ A⁻¹`. -/
structure CPTTrefoilBranchLink where
  /-- Additive quantum numbers carried by each orientation. -/
  quantumNumbers : CPTOrientation → QuantumNumbers
  /-- Trefoil/Jones invariant carried by each orientation. -/
  jones : CPTOrientation → ℂ → ℂ
  /-- Sector exchange acts by charge conjugation. -/
  quantumNumbers_partner : ∀ s, quantumNumbers s.partner = conjugate (quantumNumbers s)
  /-- Sector exchange acts by the mirror substitution. -/
  jones_partner : ∀ s A, jones s.partner A = jones s A⁻¹

/-- Canonical CPT/mirror double constructed from any charge vector and any knot invariant. This proves
mathematical constructibility of the partner sector; it does not assert that a physical state gives the
partner nonzero Born weight or a nonzero interaction strength. -/
noncomputable def canonicalCPTTrefoilBranchLink (q : QuantumNumbers) (J : ℂ → ℂ) :
    CPTTrefoilBranchLink where
  quantumNumbers
    | .particle => q
    | .antiparticle => conjugate q
  jones
    | .particle => J
    | .antiparticle => fun A => J A⁻¹
  quantumNumbers_partner := by
    intro s
    cases s with
    | particle => rfl
    | antiparticle => exact (conjugate_involutive q).symm
  jones_partner := by
    intro s A
    cases s <;> simp

/-- Every additive charge vector and trefoil invariant admits a canonical CPT/mirror double. -/
@[zil_level domain_model]
lemma canonical_cpt_trefoil_link_exists (q : QuantumNumbers) (J : ℂ → ℂ) :
    ∃ L : CPTTrefoilBranchLink,
      L.quantumNumbers .particle = q ∧ L.jones .particle = J := by
  exact ⟨canonicalCPTTrefoilBranchLink q J, rfl, rfl⟩

/-- The electron/positron specialization of the canonical CPT/mirror double. -/
noncomputable def electronCPTTrefoilBranchLink : CPTTrefoilBranchLink :=
  canonicalCPTTrefoilBranchLink electron electronJones

/-- The canonical electron partner has positron quantum numbers and the mirror-trefoil invariant, which
the existing chirality theorem distinguishes from the electron invariant. -/
@[zil_level bridge_theorem]
lemma electron_cpt_mirror_trefoil_partner (A : ℂ) :
    electronCPTTrefoilBranchLink.quantumNumbers .antiparticle = positron
      ∧ electronCPTTrefoilBranchLink.jones .antiparticle A = positronJones A
      ∧ electronJones 2 ≠ electronCPTTrefoilBranchLink.jones .antiparticle 2 := by
  exact ⟨rfl, rfl, positron_ne_electron⟩

/-- Diagonal amplitude in a rational one-parameter rotation of the particle/antiparticle Nambu double. -/
noncomputable def weakLinkU (epsilon : ℝ) : ℝ := (1 - epsilon ^ 2) / (1 + epsilon ^ 2)

/-- Off-diagonal amplitude in the rational Nambu rotation. It vanishes at `epsilon = 0` and is nonzero
for every nonzero `epsilon`. -/
noncomputable def weakLinkV (epsilon : ℝ) : ℝ := 2 * epsilon / (1 + epsilon ^ 2)

/-- The rational branch-link amplitudes lie on the unit circle, so they define a canonical
CAR-preserving Nambu rotation. -/
lemma weakLink_normalized (epsilon : ℝ) :
    weakLinkU epsilon ^ 2 + weakLinkV epsilon ^ 2 = 1 := by
  have hden : 1 + epsilon ^ 2 ≠ 0 := by positivity
  unfold weakLinkU weakLinkV
  field_simp
  ring

@[simp] lemma weakLinkU_zero : weakLinkU 0 = 1 := by
  norm_num [weakLinkU]

@[simp] lemma weakLinkV_zero : weakLinkV 0 = 0 := by
  norm_num [weakLinkV]

/-- A nonzero mixing coordinate gives a nonzero off-diagonal branch amplitude. -/
lemma weakLinkV_ne_zero {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    weakLinkV epsilon ≠ 0 := by
  unfold weakLinkV
  exact div_ne_zero (mul_ne_zero (by norm_num) hepsilon) (by positivity)

/-- The off-diagonal branch amplitude is controlled by twice the absolute mixing coordinate. -/
lemma abs_weakLinkV_le (epsilon : ℝ) :
    |weakLinkV epsilon| ≤ 2 * |epsilon| := by
  unfold weakLinkV
  rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos (by positivity : 0 < 1 + epsilon ^ 2)]
  exact div_le_self (mul_nonneg (by norm_num) (abs_nonneg epsilon))
    (by nlinarith [sq_nonneg epsilon])

/-- There are nonzero normalized branch-mixing amplitudes below every positive tolerance. This is a
mathematical existence result for admissible weak links, not a derivation of nature's coupling value. -/
@[zil_level physical_theorem]
lemma exists_arbitrarily_weak_nonzero_branch_mix {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, epsilon ≠ 0 ∧ |weakLinkV epsilon| < delta
      ∧ weakLinkU epsilon ^ 2 + weakLinkV epsilon ^ 2 = 1 := by
  refine ⟨delta / 4, by positivity, ?_, weakLink_normalized (delta / 4)⟩
  calc
    |weakLinkV (delta / 4)| ≤ 2 * |delta / 4| := abs_weakLinkV_le (delta / 4)
    _ = delta / 2 := by rw [abs_of_pos (by positivity : 0 < delta / 4)]; ring
    _ < delta := by linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The weak branch rotation preserves the inner product on the continuum Nambu carrier `H ⊕ H`.
By the existing continuum criterion, its smeared fermionic CAR are therefore preserved. -/
@[zil_level bridge_theorem]
lemma weakBranchLink_preserves_inner (epsilon : ℝ) (f g f' g' : H) :
    ⟪weakLinkU epsilon • f + weakLinkV epsilon • g,
        weakLinkU epsilon • f' + weakLinkV epsilon • g'⟫
      + ⟪(-(weakLinkV epsilon • f)) + weakLinkU epsilon • g,
          (-(weakLinkV epsilon • f')) + weakLinkU epsilon • g'⟫
      = ⟪f, f'⟫ + ⟪g, g'⟫ :=
  nambu_bogoliubov_preserves_inner _ _ (weakLink_normalized epsilon) f g f' g'

/-- The dynamical capstone: a Dirac solution is sent to the reversed-momentum CPT solution while its
canonical trefoil presentation is sent to the positron charge sector and mirror invariant. -/
@[zil_level bridge_theorem]
lemma cpt_mirror_trefoil_maps_dirac_solution (p : Fin 4 → ℝ) (m : ℝ)
    (psi : Fin 4 → ℂ) (A : ℂ) (h : diracOp p m *ᵥ psi = 0) :
    diracOp (-p) m *ᵥ ((-((-Complex.I) • γ5)) *ᵥ psi) = 0
      ∧ electronCPTTrefoilBranchLink.quantumNumbers .antiparticle = positron
      ∧ electronCPTTrefoilBranchLink.jones .antiparticle A = positronJones A := by
  exact ⟨cpt_maps_dirac_solution p m psi h, rfl, rfl⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.counterrotation_spinor_holonomy_eq where
  formalizes @ "claim:positive-and-negative-full-turns-have-the-same-fermionic-holonomy",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:counter-rotation-alone-does-not-imply-charge-conjugation-or-an-antiparticle"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.canonical_cpt_trefoil_link_exists where
  formalizes @ "claim:every-charge-vector-and-knot-invariant-admits-a-canonical-cpt-mirror-double",
  epistemic_status @ "mathematical-construction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation.conjugate_involutive",
  caveat @ "claim:constructibility-of-the-doubled-representation-does-not-prove-nonzero-born-support-for-both-sectors"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.electron_cpt_mirror_trefoil_partner where
  formalizes @ "claim:the-electron-cpt-partner-has-positron-charges-and-the-mirror-trefoil-invariant",
  epistemic_status @ "model-representation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant.trefoil_chiral_distinguishes",
  caveat @ "claim:the-electron-trefoil-identification-is-the-soliton-model-presentation"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.exists_arbitrarily_weak_nonzero_branch_mix where
  formalizes @ "claim:normalized-nonzero-nambu-mixings-exist-below-every-positive-amplitude-tolerance",
  epistemic_status @ "mathematical-construction",
  caveat @ "claim:this-does-not-determine-or-measure-a-physical-interbranch-coupling"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.weakBranchLink_preserves_inner where
  formalizes @ "claim:the-rational-weak-branch-mixing-preserves-the-continuum-nambu-inner-product-and-car-criterion",
  epistemic_status @ "exact-mathematical-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.ContinuumCAR.nambu_bogoliubov_preserves_inner",
  caveat @ "claim:this-is-the-continuum-one-particle-car-criterion-not-a-fock-implementability-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.cpt_mirror_trefoil_maps_dirac_solution where
  formalizes @ "claim:cpt-maps-a-dirac-solution-to-reversed-momentum-while-the-trefoil-presentation-maps-to-the-positron-mirror",
  epistemic_status @ "bridge-theorem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics.cpt_maps_dirac_solution",
  caveat @ "claim:the-theorem-composes-cpt-dynamics-with-the-trefoil-model-and-does-not-derive-a-new-standard-model-interaction"

zil_file_contract physlib.cptTrefoilBranchLink where
  promises "A canonical involutive CPT/mirror fermion double, an exact obstruction to reading counter-rotation alone as antimatter, and arbitrarily weak nonzero continuum Nambu mixings that preserve the CAR criterion."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation.conjugate",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant.positronJones",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.ContinuumCAR.nambu_bogoliubov_preserves_inner",
    "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics.cpt_maps_dirac_solution"]
  forbids_substitutes ["claiming-that-counter-rotation-alone-proves-an-antiparticle",
    "claiming-that-the-two-spin-four-spheres-are-everett-branches",
    "claiming-that-mathematical-existence-fixes-a-physical-coupling-or-born-weight",
    "placing-an-antiunitary-charge-conjugation-map-directly-as-a-linear-hamiltonian-block"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.counterrotation_spinor_holonomy_eq,
    Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.canonical_cpt_trefoil_link_exists,
    Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.electron_cpt_mirror_trefoil_partner,
    Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.exists_arbitrarily_weak_nonzero_branch_mix,
    Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.weakBranchLink_preserves_inner,
    Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel.cpt_mirror_trefoil_maps_dirac_solution]

/- ZIL-END -/

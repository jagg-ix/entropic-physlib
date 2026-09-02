/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.L2KetAdapter
meta import Zil

/-!
# State presentations and proved bridges

The architecture centers on proved coherence maps, not a privileged carrier.  A
`StatePresentation` is a carrier equipped with a Born distribution on a shared
index; a `StatePresentationBridge` is a map that preserves that distribution, so
every functional of it — probabilities, entropy, total correlation — is
preserved.  A `StatePresentationEquiv` is a bridge with a two-sided inverse.

The finite `ℓ²` carrier and the QuantumInfo `Ket` carrier are made two
presentations of the same states, related by a proved equivalence (both round
trips) that preserves the Born distribution; the classical total correlation is
therefore identical across the two presentations.  This is the reusable form of
the state-composition migration: a legitimate carrier is admitted through a
proved bridge, not an analogy.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock

namespace Physlib.QuantumMechanics.L2StatePresentation

open Physlib.QuantumMechanics.L2KetAdapter
open Physlib.QuantumMechanics.KoopmanQuantization
open Physlib.QuantumMechanics.BornCompositionCorrelation

/-- A **presentation** of a system: a carrier equipped with a Born distribution
on a shared index. -/
structure StatePresentation (ι : Type*) where
  Carrier : Type*
  born : Carrier → ι → ℝ

/-- A **proved bridge** between two presentations: a map that preserves the Born
distribution.  Every functional of the distribution is then preserved. -/
structure StatePresentationBridge {ι : Type*} (P Q : StatePresentation ι) where
  map : P.Carrier → Q.Carrier
  born_preserved : ∀ s i, Q.born (map s) i = P.born s i

/-- A **presentation equivalence**: a bridge with a two-sided inverse, so the two
carriers present the same states. -/
structure StatePresentationEquiv {ι : Type*} (P Q : StatePresentation ι)
    extends StatePresentationBridge P Q where
  inv : Q.Carrier → P.Carrier
  left_inv : ∀ s, inv (map s) = s
  right_inv : ∀ t, map (inv t) = t

namespace StatePresentationBridge

variable {ι : Type*} {P Q : StatePresentation ι}

/-- The bridge preserves the whole Born distribution. -/
theorem born_eq (B : StatePresentationBridge P Q) (s : P.Carrier) :
    Q.born (B.map s) = P.born s :=
  funext (B.born_preserved s)

/-- **The bridge preserves classical total correlation** — the same information
content on both presentations. -/
@[zil_level bridge_theorem]
theorem totalCorrelation_eq {κ : Type*} [Fintype ι] [Fintype κ]
    {P Q : StatePresentation (ι × κ)} (B : StatePresentationBridge P Q)
    (s : P.Carrier) :
    totalCorrelation (Q.born (B.map s)) = totalCorrelation (P.born s) := by
  rw [B.born_eq]

end StatePresentationBridge

/-! ## The ℓ² and Ket presentations and their proved equivalence -/

/-- The finite `ℓ²` carrier as a presentation, on normalized states. -/
def normalizedL2Presentation (ι : Type*) [Fintype ι] : StatePresentation ι where
  Carrier := {ψ : lp (fun _ : ι => ℂ) 2 // ‖ψ‖ = 1}
  born := fun s => bornDist s.1

/-- The QuantumInfo `Ket` carrier as a presentation. -/
def ketPresentation (ι : Type*) [Fintype ι] : StatePresentation ι where
  Carrier := Ket ι
  born := fun k i => ‖(k : ι → ℂ) i‖ ^ 2

/-- **The adapter is a proved presentation equivalence**: the normalized `ℓ²`
states and the Kets present the same states, and the Born distribution — hence
all its functionals — agrees. -/
@[zil_level bridge_theorem]
def l2KetEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    StatePresentationEquiv (normalizedL2Presentation ι) (ketPresentation ι) where
  map := fun s => ketOfL2State s.1 s.2
  born_preserved := fun s i => (congrFun (bornDist_eq_ketBorn s.1 s.2) i).symm
  inv := fun k => ⟨l2OfKet k, l2OfKet_norm_one k⟩
  left_inv := fun s => Subtype.ext (l2OfKet_ketOfL2State s.1 s.2)
  right_inv := fun k => ketOfL2State_l2OfKet k

/-! ## Naturality: the dynamics intertwines across presentations

The evolution intertwining of steps 5–6 is the reusable naturality law of a
bridge: each presentation carries a dynamics, and a natural bridge preserves the
Born distribution *and* intertwines the two dynamics. -/

/-- A presentation equipped with a dynamics on its carrier. -/
structure DynamicalPresentation (ι : Type*) extends StatePresentation ι where
  evolve : Carrier → Carrier

/-- A **natural bridge**: a Born-preserving bridge that also intertwines the two
dynamics — the evolution is one map across the presentations. -/
structure NaturalBridge {ι : Type*} (P Q : DynamicalPresentation ι) extends
    StatePresentationBridge P.toStatePresentation Q.toStatePresentation where
  evolution_intertwines : ∀ s, map (P.evolve s) = Q.evolve (map s)

/-- The `ℓ²` presentation with the Koopman dynamics, on normalized states. -/
def dynamicalL2Presentation (m : Type*) [Fintype m] (σ : m ≃ m) :
    DynamicalPresentation m where
  toStatePresentation := normalizedL2Presentation m
  evolve := fun s => ⟨koopmanStateStep σ s.1, by
    rw [(koopmanStateStep σ).norm_map]; exact s.2⟩

/-- The `Ket` presentation with the relabeling dynamics. -/
def dynamicalKetPresentation (m : Type*) [Fintype m] (σ : m ≃ m) :
    DynamicalPresentation m where
  toStatePresentation := ketPresentation m
  evolve := ketRelabel σ

/-- **The adapter is a natural bridge**: it preserves the Born distribution and
intertwines the Koopman step with the Ket relabeling — the steps 5–6 naturality
law in reusable form. -/
@[zil_level bridge_theorem]
def l2KetNaturalBridge (m : Type*) [Fintype m] [DecidableEq m] (σ : m ≃ m) :
    NaturalBridge (dynamicalL2Presentation m σ) (dynamicalKetPresentation m σ) where
  toStatePresentationBridge := (l2KetEquiv m).toStatePresentationBridge
  evolution_intertwines := fun s => ketOfL2State_koopman σ s.1 s.2

/-! ## Behavioral minimal realizations

Reachability and observability give an honest replacement for a universal
model-equivalence hub.  For unary deterministic dynamics, the complete Born
behavior stream determines a reachable minimal presentation uniquely up to its
carrier equivalence. -/

/-- A dynamical state presentation with a distinguished initial state. -/
structure PointedDynamicalPresentation (ι : Type*) extends DynamicalPresentation ι where
  initial : Carrier

namespace PointedDynamicalPresentation

variable {ι : Type*}

/-- Iterate the presentation dynamics `n` times from `s`. -/
def evolveN (P : PointedDynamicalPresentation ι) : ℕ → P.Carrier → P.Carrier
  | 0, s => s
  | n + 1, s => P.evolve (P.evolveN n s)

@[simp] lemma evolveN_zero (P : PointedDynamicalPresentation ι) (s : P.Carrier) :
    P.evolveN 0 s = s := rfl

@[simp] lemma evolveN_succ (P : PointedDynamicalPresentation ι) (n : ℕ) (s : P.Carrier) :
    P.evolveN (n + 1) s = P.evolve (P.evolveN n s) := rfl

lemma evolveN_add (P : PointedDynamicalPresentation ι) (n k : ℕ) (s : P.Carrier) :
    P.evolveN (n + k) s = P.evolveN k (P.evolveN n s) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, evolveN_succ, evolveN_succ, ih]

/-- The orbit of the distinguished initial state. -/
def orbit (P : PointedDynamicalPresentation ι) (n : ℕ) : P.Carrier :=
  P.evolveN n P.initial

@[simp] lemma orbit_zero (P : PointedDynamicalPresentation ι) : P.orbit 0 = P.initial := rfl

@[simp] lemma orbit_succ (P : PointedDynamicalPresentation ι) (n : ℕ) :
    P.orbit (n + 1) = P.evolve (P.orbit n) := rfl

lemma orbit_add (P : PointedDynamicalPresentation ι) (n k : ℕ) :
    P.orbit (n + k) = P.evolveN k (P.orbit n) :=
  P.evolveN_add n k P.initial

/-- The complete observable Born behavior stream from a state. -/
def behavior (P : PointedDynamicalPresentation ι) (s : P.Carrier) : ℕ → ι → ℝ :=
  fun n => P.born (P.evolveN n s)

/-- Every carrier state is reached from the distinguished initial state. -/
def IsReachable (P : PointedDynamicalPresentation ι) : Prop :=
  Function.Surjective P.orbit

/-- The complete Born behavior stream separates carrier states. -/
def IsObservable (P : PointedDynamicalPresentation ι) : Prop :=
  Function.Injective P.behavior

/-- Reachability and observability, the minimal-realization conditions used here. -/
def IsMinimal (P : PointedDynamicalPresentation ι) : Prop :=
  P.IsReachable ∧ P.IsObservable

/-- Two pointed presentations expose the same behavior from their initial states. -/
def SameBehavior (P Q : PointedDynamicalPresentation ι) : Prop :=
  P.behavior P.initial = Q.behavior Q.initial

end PointedDynamicalPresentation

/-- A pointed natural equivalence preserves Born weights, dynamics, and the
distinguished initial state, with a two-sided inverse on carriers. -/
structure PointedNaturalEquiv {ι : Type*}
    (P Q : PointedDynamicalPresentation ι) extends
    StatePresentationEquiv P.toStatePresentation Q.toStatePresentation where
  initial_preserved : map P.initial = Q.initial
  evolution_intertwines : ∀ s, map (P.evolve s) = Q.evolve (map s)

namespace PointedNaturalEquiv

variable {ι : Type*} {P Q : PointedDynamicalPresentation ι}

/-- The carrier equivalence underlying a pointed natural equivalence. -/
def toEquiv (E : PointedNaturalEquiv P Q) : P.Carrier ≃ Q.Carrier where
  toFun := E.map
  invFun := E.inv
  left_inv := E.left_inv
  right_inv := E.right_inv

/-- A pointed natural equivalence transports the complete initial orbit. -/
lemma map_orbit (E : PointedNaturalEquiv P Q) (n : ℕ) :
    E.map (P.orbit n) = Q.orbit n := by
  induction n with
  | zero => exact E.initial_preserved
  | succ n ih =>
      rw [PointedDynamicalPresentation.orbit_succ,
        PointedDynamicalPresentation.orbit_succ, E.evolution_intertwines, ih]

/-- Between reachable pointed presentations, a pointed natural equivalence is
unique as a carrier equivalence. -/
@[zil_level structural]
theorem toEquiv_unique (hP : P.IsReachable) (E F : PointedNaturalEquiv P Q) :
    E.toEquiv = F.toEquiv := by
  apply Equiv.ext
  intro s
  obtain ⟨n, rfl⟩ := hP s
  exact (E.map_orbit n).trans (F.map_orbit n).symm

end PointedNaturalEquiv

namespace PointedDynamicalPresentation

variable {ι : Type*} (P Q : PointedDynamicalPresentation ι)

/-- Equal initial behavior transports to equal behavior from corresponding
points of the two initial orbits. -/
lemma sameBehavior_orbit (hsame : P.SameBehavior Q) (n : ℕ) :
    P.behavior (P.orbit n) = Q.behavior (Q.orbit n) := by
  funext k i
  change P.born (P.evolveN k (P.orbit n)) i =
    Q.born (Q.evolveN k (Q.orbit n)) i
  rw [← P.orbit_add n k, ← Q.orbit_add n k]
  exact congrFun (congrFun hsame (n + k)) i

/-- Equality of two orbit states in `P` transfers to `Q` when `Q` is observable. -/
lemma orbit_eq_transfer (hsame : P.SameBehavior Q) (hQobs : Q.IsObservable)
    {m n : ℕ} (h : P.orbit m = P.orbit n) : Q.orbit m = Q.orbit n := by
  apply hQobs
  rw [← P.sameBehavior_orbit Q hsame m, ← P.sameBehavior_orbit Q hsame n, h]

/-- Equality of two orbit states in `Q` transfers to `P` when `P` is observable. -/
lemma orbit_eq_transfer_rev (hsame : P.SameBehavior Q) (hPobs : P.IsObservable)
    {m n : ℕ} (h : Q.orbit m = Q.orbit n) : P.orbit m = P.orbit n := by
  apply hPobs
  rw [P.sameBehavior_orbit Q hsame m, P.sameBehavior_orbit Q hsame n, h]

/-- A chosen initial-orbit index witnessing reachability of `s`. -/
noncomputable def chosenIndex (hP : P.IsReachable) (s : P.Carrier) : ℕ :=
  Classical.choose (hP s)

lemma orbit_chosenIndex (hP : P.IsReachable) (s : P.Carrier) :
    P.orbit (P.chosenIndex hP s) = s :=
  Classical.choose_spec (hP s)

/-- Map a reachable state to the corresponding point of `Q`'s initial orbit. -/
noncomputable def minimalMap (hP : P.IsReachable) (s : P.Carrier) : Q.Carrier :=
  Q.orbit (P.chosenIndex hP s)

/-- Construct the canonical pointed natural equivalence between two reachable,
observable presentations with identical initial behavior. -/
noncomputable def minimalEquiv (hP : P.IsReachable) (hQ : Q.IsReachable)
    (hPobs : P.IsObservable) (hQobs : Q.IsObservable) (hsame : P.SameBehavior Q) :
    PointedNaturalEquiv P Q where
  map := P.minimalMap Q hP
  born_preserved := by
    intro s i
    let n := P.chosenIndex hP s
    have hn : P.orbit n = s := P.orbit_chosenIndex hP s
    change Q.born (Q.orbit n) i = P.born s i
    rw [← hn]
    exact (congrFun (congrFun hsame n) i).symm
  inv := Q.minimalMap P hQ
  left_inv := by
    intro s
    let n := P.chosenIndex hP s
    let m := Q.chosenIndex hQ (P.minimalMap Q hP s)
    have hn : P.orbit n = s := P.orbit_chosenIndex hP s
    have hm : Q.orbit m = P.minimalMap Q hP s := Q.orbit_chosenIndex hQ _
    have hmnQ : Q.orbit m = Q.orbit n := hm
    change P.orbit m = s
    rw [← hn]
    exact P.orbit_eq_transfer_rev Q hsame hPobs hmnQ
  right_inv := by
    intro t
    let n := Q.chosenIndex hQ t
    let m := P.chosenIndex hP (Q.minimalMap P hQ t)
    have hn : Q.orbit n = t := Q.orbit_chosenIndex hQ t
    have hm : P.orbit m = Q.minimalMap P hQ t := P.orbit_chosenIndex hP _
    have hmnP : P.orbit m = P.orbit n := hm
    change Q.orbit m = t
    rw [← hn]
    exact P.orbit_eq_transfer Q hsame hQobs hmnP
  initial_preserved := by
    let n := P.chosenIndex hP P.initial
    have hn : P.orbit n = P.orbit 0 := P.orbit_chosenIndex hP P.initial
    change Q.orbit n = Q.initial
    rw [← Q.orbit_zero]
    exact P.orbit_eq_transfer Q hsame hQobs hn
  evolution_intertwines := by
    intro s
    let n := P.chosenIndex hP s
    let m := P.chosenIndex hP (P.evolve s)
    have hn : P.orbit n = s := P.orbit_chosenIndex hP s
    have hm : P.orbit m = P.evolve s := P.orbit_chosenIndex hP _
    have hmn : P.orbit m = P.orbit (n + 1) := by
      rw [hm, P.orbit_succ, hn]
    change Q.orbit m = Q.evolve (Q.orbit n)
    rw [← Q.orbit_succ]
    exact P.orbit_eq_transfer Q hsame hQobs hmn

/-- **Behavioral minimal-realization uniqueness.** Reachable and observable
pointed deterministic presentations with the same complete Born behavior admit
a pointed dynamics/Born-preserving equivalence, unique as a carrier
equivalence. -/
@[zil_level bridge_theorem]
theorem exists_unique_minimal_equiv
    (hP : P.IsMinimal) (hQ : Q.IsMinimal) (hsame : P.SameBehavior Q) :
    ∃ E : PointedNaturalEquiv P Q,
      ∀ F : PointedNaturalEquiv P Q, E.toEquiv = F.toEquiv := by
  let E := P.minimalEquiv Q hP.1 hQ.1 hP.2 hQ.2 hsame
  exact ⟨E, fun F => PointedNaturalEquiv.toEquiv_unique hP.1 E F⟩

end PointedDynamicalPresentation

zil attach l2KetEquiv where
  formalizes @ "claim:the-normalized-l2-and-ket-carriers-are-a-proved-presentation-equivalence-preserving-the-born-distribution",
  represents @ "lean:Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State",
  preserves_probability @ "lean:Physlib.QuantumMechanics.L2KetAdapter.bornDist_eq_ketBorn",
  supported_by @ "lean:Physlib.QuantumMechanics.L2KetAdapter.bornDist_eq_ketBorn",
  epistemic_status @ "consistency-identity"

zil attach StatePresentationBridge.totalCorrelation_eq where
  formalizes @ "claim:a-born-preserving-presentation-bridge-preserves-classical-total-correlation",
  preserves_probability @ "lean:Physlib.QuantumMechanics.L2StatePresentation.StatePresentationBridge.born_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.L2StatePresentation.StatePresentationBridge.born_eq"

zil attach l2KetNaturalBridge where
  formalizes @ "claim:the-adapter-is-a-natural-bridge-preserving-born-and-intertwining-the-dynamics-the-reusable-naturality-law",
  intertwines @ "lean:Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State_koopman",
  supported_by @ "lean:Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State_koopman",
  epistemic_status @ "consistency-identity"

zil attach PointedDynamicalPresentation.exists_unique_minimal_equiv where
  formalizes @ "claim:two-reachable-observable-pointed-deterministic-presentations-with-the-same-complete-born-behavior-are-uniquely-equivalent",
  unique_up_to @ "lean:Physlib.QuantumMechanics.L2StatePresentation.PointedNaturalEquiv.toEquiv",
  supported_by @ "lean:Physlib.QuantumMechanics.L2StatePresentation.PointedDynamicalPresentation.sameBehavior_orbit",
  caveat @ "claim:uniqueness-is-of-the-carrier-equivalence-for-unary-deterministic-presentations-and-requires-both-reachability-and-observability"

zil_file_contract physlib.l2StatePresentation where
  promises "State presentations and proved bridges: a presentation is a carrier with a Born distribution on a shared index, a bridge preserves that distribution so every functional of it is preserved, and an equivalence adds a two-sided inverse. The finite l2 and Ket carriers are a proved presentation equivalence with agreeing Born distributions and hence identical classical total correlation. For pointed unary deterministic presentations, reachability and observability plus equality of the complete initial Born behavior construct a dynamics/Born-preserving carrier equivalence that is unique as a carrier equivalence."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.bornDist",
    "lean:Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State",
    "lean:Physlib.QuantumMechanics.L2KetAdapter.l2OfKet"
  ]
  forbids_substitutes [
    "admitting a carrier by analogy rather than a Born-preserving bridge",
    "claiming an equivalence without both round trips",
    "claiming behavioral uniqueness without reachability and observability",
    "identifying preserved classical correlation with preserved entanglement"
  ]
  witnessed_by [
    StatePresentationBridge.totalCorrelation_eq,
    l2KetEquiv,
    l2KetNaturalBridge,
    PointedDynamicalPresentation.exists_unique_minimal_equiv
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.l2StatePresentation

end Physlib.QuantumMechanics.L2StatePresentation

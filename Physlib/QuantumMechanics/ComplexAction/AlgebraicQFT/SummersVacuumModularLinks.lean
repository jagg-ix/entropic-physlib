/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.BoostGenerator
public import Physlib.QFT.PathIntegral.WickClock
meta import Zil

/-!
# Linking the Summers vacuum to the modular cluster, the Lorentz algebra, and Tomita–Takesaki

Wires `AlgebraicQFT.SummersRelativisticVacuum` (the Bisognano–Wichmann modular flow `Δ_W^{it} = U(λ_W(2πt))` and
Reeh–Schlieder) into the rest of the arc:

* **the Tomita–Takesaki cluster** (`ThermoFieldDynamics.KazamaTomitaTakesakiModular`): the abstract modular generator
  `δ_K = ad_K = collisionStar K` and its fixed-point algebra;
* **the standard Lorentz infrastructure** (`Lorentz.StandardLorentzBoost`): the velocity-form Lorentz
  factor `LorentzGroup.γ`;
* **the `𝔰𝔬(1,3)` boost generator** (`Lorentz.BoostGenerator`): the modular Hamiltonian as the
  PhysLean Lorentz boost generator.

The thread: by Bisognano–Wichmann the wedge modular Hamiltonian `K = log Δ_W` is (a multiple of) the
**boost generator**. The arc's `bogoliubovGenerator` is exactly that generator (its `(t, xᵢ)` block is
PhysLean's `𝔰𝔬(1,3)` `boostGenerator`, `Lorentz.BoostGenerator`), so the **vacuum modular flow's
Hamiltonian is the Lorentz boost generator** (`wedgeModularHamiltonian`); its Tomita–Takesaki
**modular flow fixes exactly the commutant** `{K}'` — the algebra of the **causal complement** of the
wedge (`summers_modularFlow_fixes_commutant`, via `modularFixed_eq_commutant`); and the modular flow's
energy is the **standard Lorentz `γ`-factor** (`modularBoost_energy_eq_lorentzGamma`).

* **§A — modular energy is the standard Lorentz `γ`-factor** (`modularBoost_energy_eq_lorentzGamma`).
* **§B — the modular Hamiltonian is the Lorentz boost generator** (`wedgeModularHamiltonian`,
  `wedgeModularHamiltonian_eq_boostGenerator_block`).
* **§C — Tomita–Takesaki: the modular flow fixes the commutant** (`summers_modularFlow_fixes_commutant`,
  `wedgeModularHamiltonian_mem_fixed`).
* **§D — the synthesis** (`summers_vacuum_modular_links`).

## References

* S. J. Summers, arXiv:0802.1854; J. Bisognano, E. Wichmann, J. Math. Phys. 16 (1975) 985. Repo
  carriers: `AlgebraicQFT.SummersRelativisticVacuum`, `ThermoFieldDynamics.KazamaTomitaTakesakiModular` (`modularFixed`,
  `modularFixed_eq_commutant`, `modularHamiltonian_mem_fixed`), `Lorentz.BoostGenerator`
  (`bogoliubovGenerator_eq_boostGenerator_block`), `Lorentz.StandardLorentzBoost`
  (`bogoliubovEnergy_eq_lorentzGamma`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks

open Real
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
open Physlib.QuantumMechanics.ComplexAction.Lorentz.StandardLorentzBoost
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.Relativity.Special


/-- **[Modular energy = standard Lorentz `γ`] `(Δ_W^{it})₀₀ = γ(tanh 2πt)`.** The time–time component
of the Bisognano–Wichmann vacuum modular flow is PhysLean's velocity-form Lorentz factor
`LorentzGroup.γ` at the modular velocity `tanh(2πt)` (`Lorentz.StandardLorentzBoost`), confirming the
modular flow as the standard relativistic boost. -/
lemma modularBoost_energy_eq_lorentzGamma (t : ℝ) :
    (modularBoost t) 0 0 = LorentzGroup.γ (Real.tanh (2 * Real.pi * t)) := by
  rw [modularBoost_energy, bogoliubovEnergy_eq_lorentzGamma]


/-- **The Bisognano–Wichmann wedge modular Hamiltonian** `K = log Δ_W` — the generator of the vacuum
modular flow, which (by Bisognano–Wichmann) is the **boost generator** `bogoliubovGenerator = [[0,1],
[1,0]]` (complexified to act on the operator algebra). -/
noncomputable def wedgeModularHamiltonian : Matrix (Fin 2) (Fin 2) ℂ :=
  bogoliubovGenerator.map Complex.ofReal

/-- **[The modular Hamiltonian is the `𝔰𝔬(1,3)` boost generator block]** the real boost generator
`bogoliubovGenerator` carried by the wedge modular Hamiltonian is the `(t, xᵢ)` off-diagonal of
PhysLean's Lorentz boost generator `lorentzAlgebra.boostGenerator i` (`Lorentz.BoostGenerator`).
So the vacuum modular Hamiltonian is the standard Lorentz boost generator. -/
lemma wedgeModularHamiltonian_eq_boostGenerator_block (i : Fin 3) :
    lorentzAlgebra.boostGenerator i (Sum.inl 0) (Sum.inr i) = bogoliubovGenerator 0 1 :=
  (Lorentz.BoostGenerator.bogoliubovGenerator_eq_boostGenerator_block i).2.1


/-- **[Tomita–Takesaki / Bisognano–Wichmann] the modular flow fixes exactly the commutant** `Fix(σ) =
{K}'`. The fixed-point algebra of the vacuum modular flow (generated by the wedge modular Hamiltonian
`K`) is the **commutant** `{K}'` — by Bisognano–Wichmann the algebra of the **causal complement** of
the wedge (`modularFixed_eq_commutant`). -/
lemma summers_modularFlow_fixes_commutant :
    modularFixed wedgeModularHamiltonian = commutant {wedgeModularHamiltonian} :=
  modularFixed_eq_commutant wedgeModularHamiltonian

/-- **[The modular Hamiltonian is modular-invariant] `K ∈ Fix(σ)`** — the boost generator commutes with
itself (`[K,K] = 0`), so the wedge modular Hamiltonian is fixed by its own modular flow. -/
lemma wedgeModularHamiltonian_mem_fixed :
    wedgeModularHamiltonian ∈ modularFixed wedgeModularHamiltonian :=
  modularHamiltonian_mem_fixed wedgeModularHamiltonian


/-- **[Summers vacuum, linked into the modular / Lorentz / Tomita–Takesaki cluster].** The
Bisognano–Wichmann vacuum modular flow has energy the standard Lorentz `γ`-factor
(`modularBoost_energy_eq_lorentzGamma`); its modular Hamiltonian is PhysLean's `𝔰𝔬(1,3)` Lorentz boost
generator (`wedgeModularHamiltonian_eq_boostGenerator_block`); and its Tomita–Takesaki modular flow
fixes exactly the commutant — the causal-complement algebra (`summers_modularFlow_fixes_commutant`),
with the modular Hamiltonian itself fixed (`wedgeModularHamiltonian_mem_fixed`). The remarkable vacuum's
modular structure is the arc's Bogoliubov boost = the standard Lorentz boost, with its Tomita–Takesaki
fixed-point algebra the causal complement. -/
lemma summers_vacuum_modular_links (t : ℝ) (i : Fin 3) :
    (modularBoost t) 0 0 = LorentzGroup.γ (Real.tanh (2 * Real.pi * t))
      ∧ lorentzAlgebra.boostGenerator i (Sum.inl 0) (Sum.inr i) = bogoliubovGenerator 0 1
      ∧ modularFixed wedgeModularHamiltonian = commutant {wedgeModularHamiltonian}
      ∧ wedgeModularHamiltonian ∈ modularFixed wedgeModularHamiltonian :=
  ⟨modularBoost_energy_eq_lorentzGamma t, wedgeModularHamiltonian_eq_boostGenerator_block i,
    summers_modularFlow_fixes_commutant, wedgeModularHamiltonian_mem_fixed⟩

/-! ## §E Haag duality and the von Neumann property of the wedge algebra

The final pillar of a Tomita–Takesaki / AQFT wedge structure: **Haag duality** — "the algebra of a region is
the commutant of the algebra of its causal complement", `𝔐(W) = 𝔐(W′)′` (Ogata–Pérez-García–Ruiz-de-Alarcón,
arXiv:2509.23734; Haag–Kastler). Naming the wedge algebra `𝔐(W) := {K}″` (the von Neumann algebra generated
by the modular Hamiltonian `K`) and the causal-complement algebra `𝔐(W′) := {K}′`, Haag duality is exactly the
repo's existing `commutant_triple` (`{K}‴ = {K}′`), and the causal-complement algebra is exactly the
modular-fixed algebra `Fix(σ)` (`modularFixed_eq_commutant`, `summers_modularFlow_fixes_commutant`). The wedge
algebra is a genuine von Neumann algebra — bicommutant-closed (`commutant_isBicommutantClosed`). -/

variable {A : Type*} [Ring A]

/-- **The wedge algebra** `𝔐(W) := {K}″` — the von Neumann algebra generated by the modular Hamiltonian `K`. -/
def wedgeAlgebra (K : A) : Set A := commutant (commutant {K})

/-- **The causal-complement algebra** `𝔐(W′) := {K}′` — the commutant, where the modular flow acts trivially. -/
def causalComplementAlgebra (K : A) : Set A := commutant {K}

/-- **[The causal-complement algebra is the modular-fixed algebra] `𝔐(W′) = Fix(σ)`.** The algebra of the
causal complement is exactly where the modular flow of `K` acts trivially (`modularFixed_eq_commutant`). -/
lemma causalComplement_eq_modularFixed (K : A) :
    causalComplementAlgebra K = modularFixed K :=
  (modularFixed_eq_commutant K).symm

/-- **[Haag duality] `𝔐(W)′ = 𝔐(W′)`.** The commutant of the wedge algebra is the causal-complement algebra —
"the algebra of a region equals the commutant of the algebra of its causal complement" (Haag–Kastler; Ogata et
al. 2509.23734). At this algebraic level it is exactly `commutant_triple`: `{K}‴ = {K}′`. -/
@[zil_claim physlib.wedgeKms.haagDuality,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.singleGeneratorWedgeAlgebra,
  zil_export]
theorem wedge_haag_duality (K : A) :
    commutant (wedgeAlgebra K) = causalComplementAlgebra K :=
  commutant_triple {K}

/-- **[The wedge algebra is a von Neumann algebra] `𝔐(W)″ = 𝔐(W)`.** It is bicommutant-closed, being a
commutant (`commutant_isBicommutantClosed`). -/
lemma wedgeAlgebra_isBicommutantClosed (K : A) :
    IsBicommutantClosed (wedgeAlgebra K) :=
  commutant_isBicommutantClosed (commutant {K})

/-- **[The modular Hamiltonian lives in its wedge algebra] `K ∈ 𝔐(W)`.** -/
lemma modularHamiltonian_mem_wedgeAlgebra (K : A) : K ∈ wedgeAlgebra K :=
  bicommutant_subset {K} rfl

/-- **[The Tomita–Takesaki wedge, complete] Haag duality + von Neumann closure + causal complement = modular
fixed.** For the Bisognano–Wichmann wedge modular Hamiltonian: the commutant of the wedge algebra is the
causal-complement algebra (**Haag duality**, `𝔐(W)′ = 𝔐(W′)`); the wedge algebra is a **von Neumann algebra**
(`𝔐(W)″ = 𝔐(W)`); the causal-complement algebra is exactly the **modular-fixed** algebra `Fix(σ)`; and the
modular Hamiltonian lives in its wedge algebra. -/
@[zil_claim physlib.wedgeKms.wedgeTomitaTakesakiHaagDuality,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bisognanoWichmannWedge,
  zil_export]
theorem wedge_tomita_takesaki_haag_duality :
    commutant (wedgeAlgebra wedgeModularHamiltonian)
        = causalComplementAlgebra wedgeModularHamiltonian
      ∧ IsBicommutantClosed (wedgeAlgebra wedgeModularHamiltonian)
      ∧ causalComplementAlgebra wedgeModularHamiltonian = modularFixed wedgeModularHamiltonian
      ∧ wedgeModularHamiltonian ∈ wedgeAlgebra wedgeModularHamiltonian :=
  ⟨wedge_haag_duality _, wedgeAlgebra_isBicommutantClosed _,
   causalComplement_eq_modularFixed _, modularHamiltonian_mem_wedgeAlgebra _⟩

zil_theorem_intent wedge_haag_duality where
  at_level bridge_theorem
  must_mention [commutant, wedgeAlgebra, causalComplementAlgebra]

zil_theorem_intent wedge_tomita_takesaki_haag_duality where
  at_level bridge_theorem
  must_mention [commutant, wedgeAlgebra, modularFixed, wedgeModularHamiltonian]

zil attach wedge_haag_duality where
  formalizes @ "claim:haag-duality-commutant-of-region-is-causal-complement",
  requires @ "assumption:single-generator-wedge-algebra",
  supported_by @ "paper:ogata-perezgarcia-ruizdealarcon-2025",
  supported_by @ "paper:haag-kastler-1964"

zil attach wedge_tomita_takesaki_haag_duality where
  formalizes @ "claim:bisognano-wichmann-wedge-satisfies-haag-duality-and-von-neumann",
  requires @ "assumption:bisognano-wichmann-wedge",
  requires @ "claim:haag-duality-commutant-of-region-is-causal-complement",
  supported_by @ "paper:ogata-perezgarcia-ruizdealarcon-2025",
  supported_by @ "paper:bisognano-wichmann-1975",
  caveat @ "claim:single-generator-matrix-shadow-not-type-iii-wedge-algebra"

zil_file_contract physlib.wedgeHaagDuality where
  promises "The Bisognano-Wichmann wedge modular structure satisfies Haag duality: naming the wedge algebra the bicommutant of the modular Hamiltonian and the causal-complement algebra its commutant, the commutant of the wedge algebra equals the causal-complement algebra (via commutant_triple), that causal-complement algebra is exactly the modular-fixed algebra, and the wedge algebra is a von Neumann algebra (bicommutant-closed)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.wedgeAlgebra",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.causalComplementAlgebra",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant",
    "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular.modularFixed",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.wedgeModularHamiltonian"]
  forbids_substitutes ["a type III wedge-local von Neumann algebra claim from the finite matrix shadow",
    "a proof of Haag duality for a concrete quantum field net",
    "an identification of the single-generator algebra with the full local observable algebra"]
  witnessed_by [wedge_haag_duality, wedge_tomita_takesaki_haag_duality]

#zil_formalization_lint physlib.wedgeHaagDuality

/-! ## §F The modular automorphism (conjugation action) and the Reeh–Schlieder standard form

Two more Tomita–Takesaki pillars:

* **the modular automorphism `σ_t(A) = Δ_W^{it} A Δ_W^{−it}`** — conjugation by the modular boost is a
  one-parameter group of *ring* automorphisms (`modularAut_mul`, `modularAut_group`) that **fixes the modular
  Hamiltonian** (`modularAut_fixes_generator`, `σ_t K = K`) and **preserves its commutant** setwise
  (`modularAut_preserves_generator_commutant`, `σ_t 𝔐(W)′ = 𝔐(W)′`) — the finite counterpart of the existing
  infinitesimal statement `summers_modularFlow_fixes_commutant` (`ker(ad_K) = {K}′`);
* **Reeh–Schlieder wired to the standard subspace** (`reehSchlieder_standardSubspace_correspondence`) — the
  separating vacuum's algebraic Reeh–Schlieder property (`reehSchlieder_event_occurs`) and the one-particle
  standard form (`WickClock.standardSubspace_directSum`, unique `K ⊕ iK`) are the two faces of the same
  cyclic-and-separating structure that makes the Tomita operator well-defined. -/

/-- **The modular automorphism `σ_t(A) = Δ_W^{it} A Δ_W^{−it}`** — conjugation of an observable by the
Bisognano–Wichmann modular boost. -/
noncomputable def modularAut (t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  modularBoost t * A * modularBoost (-t)

/-- **[σ_0 = id]** the modular automorphism at time zero is the identity. -/
lemma modularAut_zero (A : Matrix (Fin 2) (Fin 2) ℝ) : modularAut 0 A = A := by
  rw [modularAut, neg_zero, modularBoost_zero, one_mul, mul_one]

/-- **[σ_t is unital] `σ_t(1) = 1`.** -/
lemma modularAut_one (t : ℝ) : modularAut t 1 = 1 := by
  rw [modularAut, mul_one, modularBoost_group, add_neg_cancel, modularBoost_zero]

/-- **[σ_t is multiplicative — a ring automorphism] `σ_t(A B) = σ_t(A) σ_t(B)`.** Conjugation is a ring
homomorphism: the modular flow acts by *automorphisms* of the observable algebra. -/
@[zil_claim physlib.wedgeKms.modularAutomorphismMultiplicative,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bisognanoWichmannWedge, zil_export]
theorem modularAut_mul (t : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    modularAut t (A * B) = modularAut t A * modularAut t B := by
  have hinv : modularBoost (-t) * modularBoost t = 1 := by
    rw [modularBoost_group, neg_add_cancel, modularBoost_zero]
  calc modularAut t (A * B)
      = modularBoost t * A * (modularBoost (-t) * modularBoost t) * B * modularBoost (-t) := by
        rw [hinv]; simp only [modularAut]; noncomm_ring
    _ = modularAut t A * modularAut t B := by simp only [modularAut]; noncomm_ring

/-- **[σ is a one-parameter group of automorphisms] `σ_s ∘ σ_t = σ_{s+t}`.** -/
@[zil_claim physlib.wedgeKms.modularAutomorphismGroup,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bisognanoWichmannWedge, zil_export]
theorem modularAut_group (s t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    modularAut s (modularAut t A) = modularAut (s + t) A := by
  simp only [modularAut]
  rw [show modularBoost s * (modularBoost t * A * modularBoost (-t)) * modularBoost (-s)
      = modularBoost s * modularBoost t * A * (modularBoost (-t) * modularBoost (-s)) from by
    noncomm_ring, modularBoost_group, modularBoost_group, show -t + -s = -(s + t) from by ring]

/-- **[σ_t fixes everything commuting with the flow element] `A ∈ {Δ_W^{it}}′ ⟹ σ_t(A) = A`.** -/
theorem modularAut_fixes_flow_commutant (t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A ∈ commutant {modularBoost t}) : modularAut t A = A := by
  have hcomm : modularBoost t * A = A * modularBoost t :=
    Set.mem_centralizer_iff.mp hA (modularBoost t) rfl
  rw [modularAut, hcomm, mul_assoc, modularBoost_group, add_neg_cancel, modularBoost_zero, mul_one]

/-- **[The modular boost commutes with its generator] `Δ_W^{it} K = K Δ_W^{it}`.** The boost is the
exponential of the generator, so they commute — a direct `Fin 2` computation. -/
lemma modularBoost_commutes_bogoliubovGenerator (t : ℝ) :
    modularBoost t * bogoliubovGenerator = bogoliubovGenerator * modularBoost t := by
  simp only [modularBoost, ThermoFieldDynamics.TFDImaginaryPart.thermoBogoliubov, bogoliubovGenerator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- **[The modular flow fixes the modular Hamiltonian] `σ_t(K) = K`** — the finite counterpart of
`wedgeModularHamiltonian_mem_fixed` (`K ∈ ker ad_K`). -/
@[zil_claim physlib.wedgeKms.modularAutomorphismFixesGenerator,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bisognanoWichmannWedge, zil_export]
theorem modularAut_fixes_generator (t : ℝ) :
    modularAut t bogoliubovGenerator = bogoliubovGenerator :=
  modularAut_fixes_flow_commutant t bogoliubovGenerator
    (Set.mem_centralizer_iff.mpr fun g hg => by
      rw [Set.mem_singleton_iff] at hg; subst hg
      exact modularBoost_commutes_bogoliubovGenerator t)

/-- **[The modular flow preserves the commutant of the generator] `σ_t(𝔐(W)′) = 𝔐(W)′`.** Since `σ_t` is a
ring automorphism fixing `K`, it maps `{K}′` into itself: if `A` commutes with `K` then so does `σ_t(A)`. The
finite counterpart of `summers_modularFlow_fixes_commutant` — the modular flow leaves the causal-complement
algebra invariant. -/
@[zil_claim physlib.wedgeKms.modularAutomorphismPreservesCommutant,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bisognanoWichmannWedge, zil_export]
theorem modularAut_preserves_generator_commutant (t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A ∈ commutant {bogoliubovGenerator}) :
    modularAut t A ∈ commutant {bogoliubovGenerator} := by
  simp only [commutant, Set.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg; subst hg
  have hAcomm : bogoliubovGenerator * A = A * bogoliubovGenerator :=
    Set.mem_centralizer_iff.mp hA bogoliubovGenerator rfl
  calc bogoliubovGenerator * modularAut t A
      = modularAut t bogoliubovGenerator * modularAut t A := by rw [modularAut_fixes_generator]
    _ = modularAut t (bogoliubovGenerator * A) := (modularAut_mul t _ _).symm
    _ = modularAut t (A * bogoliubovGenerator) := by rw [hAcomm]
    _ = modularAut t A * modularAut t bogoliubovGenerator := modularAut_mul t _ _
    _ = modularAut t A * bogoliubovGenerator := by rw [modularAut_fixes_generator]

/-! ### The modular automorphism group `σ : ℝ → Aut(𝔐)` as a genuine object -/

/-- **[σ_t is additive] `σ_t(A + B) = σ_t(A) + σ_t(B)`** — conjugation distributes over addition. -/
lemma modularAut_add (t : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    modularAut t (A + B) = modularAut t A + modularAut t B := by
  simp only [modularAut, mul_add, add_mul]

/-- **[σ_t annihilates 0] `σ_t(0) = 0`.** -/
lemma modularAut_zero_map (t : ℝ) : modularAut t 0 = 0 := by
  simp [modularAut]

/-- **The modular automorphism `σ_t` as a ring automorphism** `Δ_W^{it} · Δ_W^{−it}` — a genuine element of
`RingAut 𝔐`, with inverse `σ_{−t}`. -/
noncomputable def modularAutEquiv (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ ≃+* Matrix (Fin 2) (Fin 2) ℝ where
  toFun := modularAut t
  invFun := modularAut (-t)
  left_inv A := by rw [modularAut_group, neg_add_cancel, modularAut_zero]
  right_inv A := by rw [modularAut_group, add_neg_cancel, modularAut_zero]
  map_mul' := modularAut_mul t
  map_add' := modularAut_add t

/-- **[σ_0 = id as a ring automorphism].** -/
lemma modularAutEquiv_zero : modularAutEquiv 0 = 1 :=
  RingEquiv.ext fun A => modularAut_zero A

/-- **[The modular automorphisms compose] `σ_{s+t} = σ_s ∘ σ_t` in `RingAut 𝔐`.** -/
lemma modularAutEquiv_group (s t : ℝ) :
    modularAutEquiv (s + t) = modularAutEquiv s * modularAutEquiv t :=
  RingEquiv.ext fun A => (modularAut_group s t A).symm

/-- **The modular automorphism group `σ : ℝ → RingAut 𝔐`** as a genuine group homomorphism from `(ℝ, +)` into
the automorphisms of the observable algebra — the Tomita–Takesaki modular automorphism group. -/
noncomputable def modularAutGroupHom :
    Multiplicative ℝ →* (Matrix (Fin 2) (Fin 2) ℝ ≃+* Matrix (Fin 2) (Fin 2) ℝ) where
  toFun t := modularAutEquiv (Multiplicative.toAdd t)
  map_one' := modularAutEquiv_zero
  map_mul' s t := modularAutEquiv_group (Multiplicative.toAdd s) (Multiplicative.toAdd t)

/-- **[The modular automorphism group, assembled]** `σ_t` is a one-parameter group of ring automorphisms of
the observable algebra: `σ_0 = id`, `σ_{s+t} = σ_s ∘ σ_t`, and each `σ_t` acts by conjugation
`A ↦ Δ_W^{it} A Δ_W^{−it}`. -/
@[zil_claim physlib.wedgeKms.modularAutomorphismGroupObject,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bisognanoWichmannWedge, zil_export]
theorem modularAut_oneParameterGroup :
    modularAutEquiv 0 = 1
      ∧ (∀ s t : ℝ, modularAutEquiv (s + t) = modularAutEquiv s * modularAutEquiv t)
      ∧ (∀ (t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ), modularAutEquiv t A = modularAut t A) :=
  ⟨modularAutEquiv_zero, modularAutEquiv_group, fun _ _ => rfl⟩

/-! ### §G The infinitesimal generator of the modular automorphism group is `2π·ad_K`

The operator-level derivative: `σ_t(A) = B(t)·A·B(−t)` with `B(t) = cosh(2πt)·1 + sinh(2πt)·K`
(`thermoBogoliubov_eq_gen`), so

  `σ_t(A) = cosh²(2πt)·A + cosh(2πt)sinh(2πt)·[K,A] − sinh²(2πt)·K A K`,

and differentiating at `t = 0` (entrywise — for `Fin 2` matrices, entrywise is the derivative in every norm)
gives `dσ_t(A)/dt|₀ = 2π·[K,A] = 2π·collisionStar K A = 2π·modularGenerator K A` — the Tomita–Takesaki
modular automorphism group is generated by `2π` times the adjoint action of the modular Hamiltonian, tying the
finite conjugation flow `modularAut` to the arc's abstract modular generator
(`KazamaTomitaTakesakiModular.modularGenerator = collisionStar`). -/

/-- **[The conjugation flow expanded in the generator]**
`σ_t(A) = cosh²(2πt)·A + cosh(2πt)sinh(2πt)·[K,A] − sinh²(2πt)·K A K` — the modular automorphism through the
`e^{θK}` decomposition of the boost. -/
lemma modularAut_expand (t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    modularAut t A
      = (Real.cosh (2 * Real.pi * t) * Real.cosh (2 * Real.pi * t)) • A
        + (Real.cosh (2 * Real.pi * t) * Real.sinh (2 * Real.pi * t)) •
            collisionStar bogoliubovGenerator A
        - (Real.sinh (2 * Real.pi * t) * Real.sinh (2 * Real.pi * t)) •
            (bogoliubovGenerator * A * bogoliubovGenerator) := by
  have hB : modularBoost t
      = Real.cosh (2 * Real.pi * t) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + Real.sinh (2 * Real.pi * t) • bogoliubovGenerator := by
    rw [modularBoost, thermoBogoliubov_eq_gen]
  have hBneg : modularBoost (-t)
      = Real.cosh (2 * Real.pi * t) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        - Real.sinh (2 * Real.pi * t) • bogoliubovGenerator := by
    rw [modularBoost, thermoBogoliubov_eq_gen,
      show 2 * Real.pi * -t = -(2 * Real.pi * t) from by ring,
      Real.cosh_neg, Real.sinh_neg, neg_smul, ← sub_eq_add_neg]
  rw [modularAut, hB, hBneg, collisionStar]
  simp only [add_mul, mul_add, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, smul_sub]
  module

/-- **[The infinitesimal generator of the modular automorphism group is `2π·ad_K`]**
`dσ_t(A)/dt|₀ = 2π·[K, A]` entrywise — the derivative of the conjugation flow at time zero is `2π` times the
commutator with the modular Hamiltonian: `2π · collisionStar K A`. The operator-level generator statement. -/
@[zil_claim physlib.wedgeKms.modularAutInfinitesimalAdK,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bisognanoWichmannWedge, zil_export]
theorem modularAut_hasDerivAt_adK (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => modularAut t A i j)
      (2 * Real.pi * collisionStar bogoliubovGenerator A i j) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * t) (2 * Real.pi) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * Real.pi)
  have hc : HasDerivAt (fun t : ℝ => Real.cosh (2 * Real.pi * t)) 0 0 := by
    simpa [Real.sinh_zero] using hlin.cosh
  have hs : HasDerivAt (fun t : ℝ => Real.sinh (2 * Real.pi * t)) (2 * Real.pi) 0 := by
    simpa [Real.cosh_zero] using hlin.sinh
  have hfun : (fun t => modularAut t A i j)
      = fun t => (Real.cosh (2 * Real.pi * t) * Real.cosh (2 * Real.pi * t)) * A i j
          + (Real.cosh (2 * Real.pi * t) * Real.sinh (2 * Real.pi * t))
              * collisionStar bogoliubovGenerator A i j
          - (Real.sinh (2 * Real.pi * t) * Real.sinh (2 * Real.pi * t))
              * (bogoliubovGenerator * A * bogoliubovGenerator) i j := by
    funext t
    rw [modularAut_expand]
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfun]
  have H := (((hc.mul hc).mul_const (A i j)).add
      ((hc.mul hs).mul_const (collisionStar bogoliubovGenerator A i j))).sub
    ((hs.mul hs).mul_const ((bogoliubovGenerator * A * bogoliubovGenerator) i j))
  convert H using 1 <;>
    first
      | rfl
      | (funext t; simp)
      | norm_num [Real.cosh_zero, Real.sinh_zero]

/-- **[The generator is the arc's abstract modular generator] `dσ_t/dt|₀ = 2π·modularGenerator K`** — the
finite conjugation flow `modularAut` is generated by the same object as the abstract Tomita–Takesaki cluster:
`KazamaTomitaTakesakiModular.modularGenerator K = collisionStar K = ad_K`. -/
@[zil_claim physlib.wedgeKms.modularAutGeneratorIsKazama,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.bisognanoWichmannWedge, zil_export]
theorem modularAut_generator_is_modularGenerator (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => modularAut t A i j)
      (2 * Real.pi * modularGenerator bogoliubovGenerator A i j) 0 :=
  modularAut_hasDerivAt_adK A i j

/-- **[Reeh–Schlieder wired to the standard subspace]** for a separating vacuum `ω` (Reeh–Schlieder) and the
one-particle standard subspace `K` of the wedge, both faces of the cyclic-and-separating standard form hold:
every nonzero local observable has nonzero vacuum expectation (`reehSchlieder_event_occurs`), and every vector
decomposes uniquely as `ξ + iη` with `ξ, η ∈ K` (`standardSubspace_directSum`). These are the algebra-level and
one-particle-level shadows of the same structure that makes the Tomita operator `S` well-defined. -/
@[zil_claim physlib.wedgeKms.reehSchliederStandardSubspace,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.separatingVacuum, zil_export]
theorem reehSchlieder_standardSubspace_correspondence
    {B : Type*} [Ring B] [StarRing B] (ω : B → ℂ) (hsep : IsSeparating ω)
    (κ ℏ : ℝ) (p : ℂ × ℂ) (a : B) (ha : a ≠ 0) :
    gnsForm ω a a ≠ 0
      ∧ (∃ ξ ∈ Physlib.QFT.PathIntegral.standardSubspacePair κ ℏ,
          ∃ η ∈ Physlib.QFT.PathIntegral.standardSubspacePair κ ℏ, p = ξ + Complex.I • η) :=
  ⟨reehSchlieder_event_occurs ω hsep a ha,
   (Physlib.QFT.PathIntegral.standardSubspace_directSum κ ℏ p).1⟩

/-! ## §H Buchholz–Florig–Summers: passivity selects the AdS KMS branch

The paper's thermodynamic argument has two logically distinct deep inputs:

1. Pusz–Woronowicz: a passive, mixing stationary state is a ground state or a KMS state.
2. AdS/Nelson analyticity: for the wedge boost the allowed positive inverse temperature lies
   in the first modular period and obeys the group constraint `sin (β/2) = 0`.

Those operator-algebraic theorems are not re-proved by the finite matrix model.  The carrier below
therefore records them as named fields, while the AdS sign-reversal exclusion and the resulting
selection `β = 2π` are proved here.
-/

/-- **Operational passivity for a specified class of cyclic unitaries.** No allowed cyclic
unitary lowers the energy of the vacuum. -/
def IsPassiveFor {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (energy : H → ℝ) (vacuum : H) (cyclicUnitaries : Set (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∀ U ∈ cyclicUnitaries, energy vacuum ≤ energy (U vacuum)

/-- **Mixing through supplied Cesàro correlations.** The analytic carrier supplies the
time-averaged correlation; mixing says that it converges to the product state. -/
def IsMixingFor {A : Type*}
    (cesaroCorrelation : ℝ → A → A → ℂ) (expectation : A → ℂ) : Prop :=
  ∀ a b, Filter.Tendsto (fun T => cesaroCorrelation T a b)
    Filter.atTop (nhds (expectation a * expectation b))

/-- **Ground-state positivity of a boost quadratic form.** -/
def IsGroundQuadratic {H : Type*} (boostEnergy : H → ℝ) : Prop :=
  ∀ ψ, 0 ≤ boostEnergy ψ

/-- **The AdS group-analytic KMS constraint.** The rotated boost generator can be
skew-adjoint only when `sin (β/2) = 0`; this is the scalar condition extracted in
Buchholz–Florig–Summers before the refined `β = 2π` conclusion. -/
def AdSKMSAnalyticConstraint (β : ℝ) : Prop :=
  Real.sin (β / 2) = 0

/-- **The AdS rotation excludes the ground-state branch.** If a unitary rotation conjugates
the boost energy to its negative and the generator is nontrivial, its quadratic form cannot
be nonnegative on every vector.  This is the formal core of
`e^{iπM₁₂} M₀₁ e^{-iπM₁₂} = -M₀₁`. -/
theorem ads_boost_not_ground_of_rotation_sign_reversal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (boostEnergy : H → ℝ) (rotation : H ≃ₗᵢ[ℂ] H)
    (hsign : ∀ ψ, boostEnergy (rotation ψ) = -boostEnergy ψ)
    (hnontrivial : ∃ ψ, boostEnergy ψ ≠ 0) :
    ¬ IsGroundQuadratic boostEnergy := by
  intro hground
  obtain ⟨ψ, hψ⟩ := hnontrivial
  have hpos : 0 ≤ boostEnergy ψ := hground ψ
  have hrot : 0 ≤ boostEnergy (rotation ψ) := hground (rotation ψ)
  rw [hsign] at hrot
  exact hψ (le_antisymm (neg_nonneg.mp hrot) hpos)

/-- **First-period AdS analyticity fixes the Unruh inverse temperature.**
If `0 < β ≤ 2π` and the AdS group constraint `sin(β/2)=0` holds, then `β=2π`.
The first-period bound is the load-bearing refinement cited by the paper. -/
theorem adsKms_beta_eq_two_pi
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 2 * Real.pi)
    (hanalytic : AdSKMSAnalyticConstraint β) :
    β = 2 * Real.pi := by
  have hhalfpos : 0 < β / 2 := by linarith
  have hhalfle : β / 2 ≤ Real.pi := by linarith
  have hhalf : β / 2 = Real.pi := by
    rcases eq_or_lt_of_le hhalfle with heq | hhalflt
    · exact heq
    ·
      have hsinpos : 0 < Real.sin (β / 2) :=
        Real.sin_pos_of_pos_of_lt_pi hhalfpos hhalflt
      exact False.elim (hsinpos.ne' hanalytic)
  linarith

/-- **Abstract Buchholz AdS vacuum carrier.**

`puszWoronowicz` and `adsAnalytic` are deliberately visible fields: the former packages the
operator-algebraic passivity/mixing theorem, while the latter packages the Nelson analytic-vector
and refined first-period argument.  The sign-reversing AdS rotation is concrete enough to exclude
the ground branch inside this carrier. -/
structure BuchholzAdSVacuumData
    (H A : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  vacuum : H
  boostEnergy : H → ℝ
  cyclicUnitaries : Set (H ≃ₗᵢ[ℂ] H)
  passive : IsPassiveFor boostEnergy vacuum cyclicUnitaries
  expectation : A → ℂ
  cesaroCorrelation : ℝ → A → A → ℂ
  mixing : IsMixingFor cesaroCorrelation expectation
  adsRotation : H ≃ₗᵢ[ℂ] H
  rotation_reverses_boost : ∀ ψ, boostEnergy (adsRotation ψ) = -boostEnergy ψ
  boost_nontrivial : ∃ ψ, boostEnergy ψ ≠ 0
  isKMSAt : ℝ → Prop
  /-- Pusz–Woronowicz ground/KMS dichotomy for the passive mixing state. -/
  puszWoronowicz :
    IsPassiveFor boostEnergy vacuum cyclicUnitaries →
      IsMixingFor cesaroCorrelation expectation →
        IsGroundQuadratic boostEnergy ∨ ∃ β, 0 ≤ β ∧ isKMSAt β
  /-- AdS group analyticity plus the refined first-period restriction. -/
  adsAnalytic :
    ∀ {β}, isKMSAt β →
      0 < β ∧ β ≤ 2 * Real.pi ∧ AdSKMSAnalyticConstraint β

/-- **[Second law + AdS covariance ⇒ Unruh KMS temperature]**
A Buchholz AdS vacuum is KMS at exactly `β = 2π`: the AdS rotation removes the
ground-state arm of Pusz–Woronowicz, and the group-analytic constraint fixes the
remaining positive KMS parameter to the Bisognano–Wichmann value. -/
theorem buchholz_passive_mixing_vacuum_is_unruhKMS
    {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : BuchholzAdSVacuumData H A) :
    D.isKMSAt (2 * Real.pi) := by
  have hnotground : ¬ IsGroundQuadratic D.boostEnergy :=
    ads_boost_not_ground_of_rotation_sign_reversal D.boostEnergy D.adsRotation
      D.rotation_reverses_boost D.boost_nontrivial
  rcases D.puszWoronowicz D.passive D.mixing with hground | ⟨β, _hβnonneg, hKMS⟩
  · exact False.elim (hnotground hground)
  · obtain ⟨hβpos, hβle, hanalytic⟩ := D.adsAnalytic hKMS
    have hβ : β = 2 * Real.pi :=
      adsKms_beta_eq_two_pi hβpos hβle hanalytic
    simpa [hβ] using hKMS

/-! ## §I Buchholz AdS TCP reflection from a dense Tomita core

The paper first proves `J² = 1` on vectors `AΩ` in the wedge Tomita core and then uses
cyclicity to extend the identity to the whole Hilbert space.  Here `J` is carried by a genuine
conjugate-linear isometric equivalence, so continuity plus density performs exactly that extension.
-/

/-- **The modular conjugation is involutive on the whole Hilbert space when it is involutive
on a dense Tomita core.** This is the analytic closure step in the Buchholz proof of `J² = 1`;
the dense core is supplied by the cyclic wedge vacuum. -/
theorem antiunitary_involution_of_dense_tomita_core
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (J : H ≃ₗᵢ⋆[ℂ] H) {D : Set H} (hD : Dense D)
    (hcore : ∀ x ∈ D, J (J x) = x) :
    ∀ x, J (J x) = x := by
  have hEq : (fun x : H => J (J x)) = id := by
    apply hD.denseRange_val.equalizer
    · exact (SemilinearIsometryClass.continuous J).comp
        (SemilinearIsometryClass.continuous J)
    · exact continuous_id
    · funext x
      exact hcore x x.property
  intro x
  exact congrFun hEq x

/-- **The antiunitary AdS TCP implementation.** `U` is the connected AdS representation,
`reflection` is `g ↦ θgθ`, and the antiunitary modular conjugation satisfies
`J U(g) = U(θgθ) J` and `J² = 1`.  These data extend the connected representation by the
disconnected reflection. -/
structure BuchholzAdSTCPData
    (G H : Type*) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  U : G → (H ≃ₗᵢ[ℂ] H)
  U_one : ∀ x, U 1 x = x
  U_mul : ∀ g h x, U (g * h) x = U g (U h x)
  reflection : G → G
  reflection_one : reflection 1 = 1
  reflection_mul : ∀ g h, reflection (g * h) = reflection g * reflection h
  reflection_involutive : ∀ g, reflection (reflection g) = g
  J : H ≃ₗᵢ⋆[ℂ] H
  J_intertwines : ∀ g x, J (U g x) = U (reflection g) (J x)
  J_involutive : ∀ x, J (J x) = x

namespace BuchholzAdSTCPData

/-- **Construct the global TCP implementation from its dense Tomita core.**
All representation/intertwining laws are retained, while global `J²=1` is derived rather than
stored independently. -/
def ofDenseTomitaCore
    {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : G → (H ≃ₗᵢ[ℂ] H))
    (hUone : ∀ x, U 1 x = x)
    (hUmul : ∀ g h x, U (g * h) x = U g (U h x))
    (reflection : G → G)
    (hreflectionOne : reflection 1 = 1)
    (hreflectionMul : ∀ g h, reflection (g * h) = reflection g * reflection h)
    (hreflectionInv : ∀ g, reflection (reflection g) = g)
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hintertwines : ∀ g x, J (U g x) = U (reflection g) (J x))
    {D : Set H} (hD : Dense D) (hcore : ∀ x ∈ D, J (J x) = x) :
    BuchholzAdSTCPData G H where
  U := U
  U_one := hUone
  U_mul := hUmul
  reflection := reflection
  reflection_one := hreflectionOne
  reflection_mul := hreflectionMul
  reflection_involutive := hreflectionInv
  J := J
  J_intertwines := hintertwines
  J_involutive := antiunitary_involution_of_dense_tomita_core J hD hcore

/-- **[AdS TCP conjugation] `J U(g) J = U(θgθ)`.**
The Buchholz intertwiner and the globally proved involution turn the connected AdS
representation into its reflected, antiunitarily implemented representation. -/
theorem conjugates_representation
    {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : BuchholzAdSTCPData G H) (g : G) (x : H) :
    T.J (T.U g (T.J x)) = T.U (T.reflection g) x := by
  calc
    T.J (T.U g (T.J x)) = T.U (T.reflection g) (T.J (T.J x)) :=
      T.J_intertwines g (T.J x)
    _ = T.U (T.reflection g) x := by rw [T.J_involutive]

end BuchholzAdSTCPData

zil_theorem_intent modularAut_mul where
  at_level bridge_theorem
  must_mention [modularAut]

zil_theorem_intent modularAut_group where
  at_level bridge_theorem
  must_mention [modularAut]

zil_theorem_intent modularAut_fixes_generator where
  at_level bridge_theorem
  must_mention [modularAut, bogoliubovGenerator]

zil_theorem_intent modularAut_preserves_generator_commutant where
  at_level bridge_theorem
  must_mention [modularAut, commutant, bogoliubovGenerator]

zil_theorem_intent reehSchlieder_standardSubspace_correspondence where
  at_level bridge_theorem
  must_mention [gnsForm, Physlib.QFT.PathIntegral.standardSubspacePair]

zil_theorem_intent modularAut_oneParameterGroup where
  at_level bridge_theorem
  must_mention [modularAutEquiv, modularAut]

zil_theorem_intent modularAut_hasDerivAt_adK where
  at_level bridge_theorem
  must_mention [modularAut,
    Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular.collisionStar,
    bogoliubovGenerator]

zil_theorem_intent modularAut_generator_is_modularGenerator where
  at_level bridge_theorem
  must_mention [modularAut,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular.modularGenerator]

zil attach modularAut_hasDerivAt_adK where
  formalizes @ "claim:modular-flow-infinitesimal-generator-is-two-pi-ad-k",
  requires @ "assumption:bisognano-wichmann-wedge",
  supported_by @ "definition:thermo-bogoliubov-exponential-decomposition",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:entrywise-derivative-equals-matrix-derivative-for-finite-size"

zil attach modularAut_generator_is_modularGenerator where
  formalizes @ "claim:modular-aut-generator-is-kazama-modular-generator",
  requires @ "claim:modular-flow-infinitesimal-generator-is-two-pi-ad-k",
  supported_by @ "definition:kazama-modular-generator-collision-star"

zil attach modularAut_oneParameterGroup where
  formalizes @ "claim:modular-automorphism-group-object",
  requires @ "claim:modular-flow-is-ring-automorphism",
  requires @ "claim:modular-automorphism-one-parameter-group",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:single-generator-matrix-shadow-not-type-iii-wedge-algebra"

zil attach modularAut_mul where
  formalizes @ "claim:modular-flow-is-ring-automorphism",
  requires @ "assumption:bisognano-wichmann-wedge",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699"

zil attach modularAut_group where
  formalizes @ "claim:modular-automorphism-one-parameter-group",
  requires @ "assumption:bisognano-wichmann-wedge",
  supported_by @ "definition:modular-boost-group"

zil attach modularAut_fixes_generator where
  formalizes @ "claim:modular-flow-fixes-modular-hamiltonian",
  requires @ "assumption:bisognano-wichmann-wedge",
  supported_by @ "definition:modular-boost-commutes-generator"

zil attach modularAut_preserves_generator_commutant where
  formalizes @ "claim:modular-flow-preserves-causal-complement-algebra",
  requires @ "claim:modular-flow-is-ring-automorphism",
  requires @ "claim:modular-flow-fixes-modular-hamiltonian",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:single-generator-matrix-shadow-not-type-iii-wedge-algebra"

zil attach reehSchlieder_standardSubspace_correspondence where
  formalizes @ "claim:reeh-schlieder-wired-to-standard-subspace",
  requires @ "assumption:separating-vacuum",
  supported_by @ "paper:reeh-schlieder-1961",
  supported_by @ "definition:standard-subspace-direct-sum",
  caveat @ "claim:cross-level-correspondence-not-single-object-reduction"

zil attach ads_boost_not_ground_of_rotation_sign_reversal where
  formalizes @ "claim:ads-pi-rotation-conjugates-the-wedge-boost-generator-to-its-negative-and-excludes-the-ground-state-branch",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:nontriviality-of-the-boost-generator-is-an-explicit-premise"

zil attach adsKms_beta_eq_two_pi where
  formalizes @ "claim:ads-first-period-analytic-kms-constraint-fixes-beta-to-two-pi",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:the-first-period-bound-and-sine-constraint-are-the-refined-nelson-analytic-input-not-derived-by-the-finite-matrix-shadow"

zil attach buchholz_passive_mixing_vacuum_is_unruhKMS where
  formalizes @ "claim:buchholz-passive-mixing-ads-vacuum-selects-the-unruh-kms-state-at-beta-two-pi",
  requires @ "theorem:pusz-woronowicz-passive-mixing-ground-or-kms-dichotomy",
  requires @ "claim:ads-first-period-analytic-kms-constraint-fixes-beta-to-two-pi",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:the-pusz-woronowicz-and-nelson-analytic-theorems-are-explicit-carrier-fields-not-reproved-here"

zil attach antiunitary_involution_of_dense_tomita_core where
  formalizes @ "claim:buchholz-modular-conjugation-j-squared-is-the-identity-globally-by-continuity-from-the-dense-wedge-tomita-core",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  supported_by @ "theorem:reeh-schlieder-cyclic-wedge-vacuum-supplies-dense-tomita-core",
  caveat @ "claim:the-core-identity-j-squared-a-omega-equals-a-omega-is-an-explicit-tomita-boundary-input"

zil attach BuchholzAdSTCPData.conjugates_representation where
  formalizes @ "claim:buchholz-ads-tcp-reflection-is-antiunitarily-implemented-as-j-u-g-j-equals-u-theta-g-theta",
  requires @ "claim:buchholz-modular-conjugation-j-squared-is-the-identity-globally-by-continuity-from-the-dense-wedge-tomita-core",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:the-intertwining-j-u-g-equals-u-theta-g-theta-j-is-explicit-representation-data-the-continuum-lie-group-analytic-continuation-is-not-reproved"

zil_file_contract physlib.modularAutomorphismReehSchlieder where
  promises "The Bisognano-Wichmann modular flow acts by ring automorphisms (conjugation by the modular boost): a one-parameter group fixing the modular Hamiltonian and preserving its commutant (the causal-complement algebra) setwise; and the separating-vacuum Reeh-Schlieder property is wired to the one-particle standard subspace's unique cyclic-separating direct-sum decomposition."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.modularBoost",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.IsSeparating",
    "lean:Physlib.QFT.PathIntegral.standardSubspacePair",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant"]
  forbids_substitutes ["a type III wedge-local automorphism claim from the finite matrix shadow",
    "an identification of the abstract separating vacuum with the concrete standard subspace",
    "a claim that conjugation by a matrix is the full Tomita-Takesaki modular automorphism group"]
  witnessed_by [modularAut_mul, modularAut_group, modularAut_fixes_generator,
    modularAut_preserves_generator_commutant, reehSchlieder_standardSubspace_correspondence,
    modularAut_oneParameterGroup, modularAut_hasDerivAt_adK,
    modularAut_generator_is_modularGenerator]

#zil_formalization_lint physlib.modularAutomorphismReehSchlieder

zil_file_contract physlib.buchholzAdSPassivityKMS where
  promises "The Buchholz-Florig-Summers AdS thermodynamic chain is represented without collapsing its analytic obligations into definitions. A sign-reversing AdS rotation proves that a nontrivial wedge-boost generator is not a ground-state generator. Given the explicit Pusz-Woronowicz ground-or-KMS result for a passive mixing vacuum and the explicit refined AdS/Nelson analytic constraint, the remaining KMS branch is proved to have inverse temperature beta = 2 pi."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.BuchholzAdSVacuumData",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.IsPassiveFor",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.IsMixingFor"]
  forbids_substitutes ["a proof of the full Pusz-Woronowicz theorem from the finite matrix model",
    "a proof of Nelson analytic-vector continuation for the continuum AdS representation",
    "defining beta to be two pi and presenting the resulting rewrite as a thermodynamic derivation"]
  witnessed_by [ads_boost_not_ground_of_rotation_sign_reversal,
    adsKms_beta_eq_two_pi, buchholz_passive_mixing_vacuum_is_unruhKMS]

zil_file_contract physlib.buchholzAdSTCP where
  promises "The Buchholz AdS TCP implementation is carried by a genuine conjugate-linear isometric equivalence J. Its involutivity is promoted from the dense Tomita core to the whole Hilbert space by continuity, and the modular intertwining relation then proves J U(g) J = U(theta g theta), the reflected antiunitary extension of the connected AdS representation."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.BuchholzAdSTCPData",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector.reehSchlieder_standard"]
  forbids_substitutes ["a construction of the continuum SO(2,n-1) representation from local fields",
    "a reproof of the Nelson analytic-vector continuation used to obtain the intertwining relation",
    "calling a merely complex-linear involution antiunitary"]
  witnessed_by [antiunitary_involution_of_dense_tomita_core,
    BuchholzAdSTCPData.conjugates_representation]

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib
public import Physlib.Meta.ZilAssert
public import Physlib.Meta.ZilTokenDiscipline

/-!
# Gate: the WEP chain is exactly one bare postulate deep, and the ledger's top is primitive

`analysis/empirical-discrimination-plan.md` §15 reported, from query output, that the entropic-force
weak-equivalence result rests on exactly one underived postulate, and that the assumption ledger's
top premises have no hidden derivations under any vocabulary.  This gate converts that report into
build-enforced facts over the full graph: if anyone later adds a derivation of a premise asserted
primitive here (good news — update the gate and claim the discharge), or breaks an edge of the WEP
chain (bad news — the depth claim fails), **the build fails** instead of the prose silently rotting.

The chain being certified, end to end:

  `eotvos_null` —[requires]→ WEP-claim —[formalized-by]→ `inertial_reading_eq_gravitational_reading`
  —[requires]→ `assumption:displacement-entropy-ansatz` — **primitive**.

The former postulate at the bottom is now discharged (§3): the ansatz is derived from the
anchored clock's entropic action, and what remains beneath the MICROSCOPE observable is the
Compton-anchor calibration — a unit choice — and exact identities.
-/

-- §1 The WEP chain edges exist exactly as stated.
#zil_assert_edge Physlib.Thermodynamics.eotvos_null
  "requires"
  "claim:in-the-entropic-force-derivation-the-inertial-and-gravitational-readings-of-the-force-consume-the-same-displacement-entropy-mass-so-the-weak-equivalence-principle-is-a-theorem-of-the-derivation-rather-than-an-empirical-input"

#zil_assert_edge Physlib.Thermodynamics.inertial_reading_eq_gravitational_reading
  "formalizes"
  "claim:in-the-entropic-force-derivation-the-inertial-and-gravitational-readings-of-the-force-consume-the-same-displacement-entropy-mass-so-the-weak-equivalence-principle-is-a-theorem-of-the-derivation-rather-than-an-empirical-input"

#zil_assert_edge Physlib.Thermodynamics.inertial_reading_eq_gravitational_reading
  "requires"
  "assumption:displacement-entropy-ansatz"

-- §2 The intermediate claim is established (so the chain has no dangling link)…
#zil_assert_established
  "claim:in-the-entropic-force-derivation-the-inertial-and-gravitational-readings-of-the-force-consume-the-same-displacement-entropy-mass-so-the-weak-equivalence-principle-is-a-theorem-of-the-derivation-rather-than-an-empirical-input"

-- §3 …and the premise at the bottom is DISCHARGED: the displacement-entropy ansatz is
-- derived — it is the `k_B` reading of the anchored clock's entropic action over the
-- displacement (`verlindeDisplacementEntropy_eq_entropicAction_reading`, with `S_I = mc·Δx`
-- from the rest-energy rate).  What remains beneath the WEP chain is the Compton-anchor
-- *calibration* (a unit choice, carried as the anchor file's caveat) and exact identities:
-- zero free postulates.  This is the gate's own advertised good-news path, claimed.
#zil_assert_established "assumption:displacement-entropy-ansatz"

-- §4 The ledger's other top premises, verified primitive by the §15 sweep, held so by the build:
-- if any of these gains a derivation, the build failure is the *discovery announcement*.
#zil_assert_primitive
  "assumption:doubled-boost-mode",
  "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  "model:the-irreversible-generator-is-the-dimensionless-log-k-rapidity-scaling-of-a-fixed-reference-operator"

-- §5 The postulate's dimensional identity, build-enforced: the displacement entropy
-- `2π k_B m c Δx / ħ` is an entropy per nat (framework `[k_B] = E·Θ⁻¹·I⁻¹`).  If the
-- definition's form ever changes dimension, the WEP chain's physical reading changes
-- with it — and the build says so.
#zil_assert_dimension Physlib.Thermodynamics.verlindeDisplacementEntropy "L^2 T^-2 M Θ^-1 I^-1"

-- §6 The holographic-`G` collision, build-enforced on the same chain's bit count
-- `N = A·c³/(G·ℏ)`.  Under SI `G` the count is a pure number — the information is
-- invisible to the 5-base projection.  Under the holographic typing the framework forces
-- (`GravitationalCouplingDimensions.holographicBits_forces_newton_perBit`: Newton's
-- constant is area-per-bit, `[G] = L³M⁻¹T⁻²·I⁻¹`), the same formula carries exactly one
-- nat.  Both readings are held by the build; together they are the `forgetInfo` collision
-- of `oneNat_threads_system`, stated at the meta level.
#zil_assert_dimension Physlib.Thermodynamics.holographicBits "1" with "A : L^2"
#zil_assert_dimension Physlib.Thermodynamics.holographicBits "I"
  with "A : L^2, G : L^3 T^-2 M^-1 I^-1"

-- …and the defect has the opposite sign where `G` enters the numerator: the Schwarzschild
-- radius `2GM/c²` is a length under SI `G` but a length *per nat* under holographic `G` —
-- the meta-level image of `bitFormSchwarzschild_defect`.  One typing, one nat, two signs.
#zil_assert_dimension Physlib.Relativity.SemiClassical.schwarzschildRadius "L"
#zil_assert_dimension Physlib.Relativity.SemiClassical.schwarzschildRadius "L I^-1"
  with "G : L^3 T^-2 M^-1 I^-1"

-- §7 The fault line, swept and held.  A full audit under the holographic typing (2609
-- definitions, every attached conclusion) healed no SI finding and broke exactly six
-- statements — every one a bit-form/holographic bridge, every discrepancy exactly one nat.
-- The two halves of that sweep, build-enforced:
--
-- (a) The WEP chain.  The Eötvös *observable* is typing-invariant — the nat charge cancels
-- between the two test bodies, so no free-fall ratio experiment can see the information
-- axis.  The WEP *identity* `m·a = G·M·m/R²` is clean under SI `G` and exactly one nat off
-- under holographic `G`: under the holographic typing, "inertial = gravitational" is the
-- one-nat conversion statement.
#zil_assert_relation_defect Physlib.Thermodynamics.eotvos_null "1"
#zil_assert_relation_defect Physlib.Thermodynamics.eotvos_null "1"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Physlib.Thermodynamics.inertial_reading_eq_gravitational_reading
  "1" with "a : L T^-2"
#zil_assert_relation_defect Physlib.Thermodynamics.inertial_reading_eq_gravitational_reading
  "I^-1" with "a : L T^-2, G : L^3 T^-2 M^-1 I^-1"

-- (b) The five bridge theorems the sweep discovered (the sixth, `weakFieldG00_schwarzschild`,
-- carries its nat inside a sum and is held by the audit rather than a relation assert).
-- Each extends `oneNat_threads_system` into an arc §C never covered: BCJ double copy,
-- TT-graviton coupling, the electrogravitic dictionary, entropic-`G` convergence, and the
-- Golse–Paul Poisson bridge.  In every one, each determinable relation is trivial or
-- exactly one nat — no other charge appears anywhere.
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling_bitForm
  "I^-1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge.lorentzForce_bcj_electrogravitic_bit_closure
  "I^-1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.HolographicElectrograviticResidual.holographicScreen_electrograviticResidual_dictionary
  "I^-1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges
  "I^-1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaul_monokineticCurrent_holographicPoisson_bridge
  "I^-1" with "G : L^3 T^-2 M^-1 I^-1"

-- …and the two members unmasked once literal `0` became dimension-polymorphic: the §F
-- rigidity statement (cell-`G` ⟺ Planck mass) and the holographic-Newton Einstein chain.
-- Eight bridges, one defect.
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain.comptonCellG_eq_iff_planck_mass
  "I^-1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_einstein_chain
  "I^-1" with "G : L^3 T^-2 M^-1 I^-1"

-- §8 The thermodynamic laws are information-neutral; their ingredients are not.
--
-- Zeroth law (Jacobson–Visser, `κ` constant on the horizon → uniform Hawking temperature):
-- homogeneous under both typings — no `G`, nothing to convert.
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw.zerothLaw_uniform_temperature
  "1" with "κ : L T^-2"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw.zerothLaw_uniform_temperature
  "1" with "κ : L T^-2, G : L^3 T^-2 M^-1 I^-1"

-- First law (`T_H · dS/dM = c²`, both carriers: the Smarr form and the entropic-time
-- `HasDerivAt` variation): homogeneous under BOTH typings.  `G` enters twice — through the
-- surface gravity (denominator: +1 nat) and through the Planck-area entropy (numerator:
-- −1 nat) — and the charges cancel *inside the law*.  Like the Eötvös ratio, the law is an
-- information-neutral observable built from information-charged ingredients; the nat lives
-- in `T` and `S` separately and is invisible in `T·dS`.
#zil_assert_relation_defect Physlib.Thermodynamics.HolographicEntropyBounds.schwarzschild_first_law
  "1"
#zil_assert_relation_defect Physlib.Thermodynamics.HolographicEntropyBounds.schwarzschild_first_law
  "1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Physlib.Relativity.SemiClassical.schwarzschild_first_law "1"
#zil_assert_relation_defect Physlib.Relativity.SemiClassical.schwarzschild_first_law
  "1" with "G : L^3 T^-2 M^-1 I^-1"

-- §9 The Compton/de Broglie clock sector is information-neutral end to end.
--
-- The clocks carry no `G` and no `k_B`: their dimensions are identical under SI and
-- holographic typing — no nat anywhere.  The nat enters the framework's gravity exclusively
-- at the `G`-construction (§6/§7: `G·m·M ≐ ħ·c` is the one-nat conversion); the clock that
-- anchors CAT/EPT ticks cleanly on both sides of it.  The unifier's clock battery emitted
-- `E ≐ m·c²` as the de Broglie ↔ Compton bridge constraint — the rest-energy identification
-- itself is the residue of the match (cross-validating `deBroglie_eq_gamma_compton`).
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency "T^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency "T^-1"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency "T^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency "T^-1"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength "L"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength "L"
  with "G : L^3 T^-2 M^-1 I^-1"

-- The proven clock identities are homogeneous and typing-invariant: the zitterbewegung
-- doubling at rest, and the de Broglie clock as the boosted Compton clock.
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton
  "1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton
  "1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglie_eq_gamma_compton
  "1" with "γ : 1"

-- §10 The two gaps the unifier reported, closed and held.
--
-- The Compton temperature `T_C = mc²/(2π k_B)` now exists as the `k_B` interface of the
-- Compton clock, and the temperature triangle gains its clock vertex:
-- `unruh_eq_comptonTemperature_iff` (`a = mc³/ℏ`, the Compton acceleration — twice it is
-- Caianiello's maximal acceleration).  The Gibbons–Hawking temperature now has its SI form,
-- and the de Sitter weld `unruh_eq_gibbonsHawkingSI_iff` (`a = c·H`) is recorded.  Both welds
-- are `G`-free, hence homogeneous and typing-invariant — clock-sector statements, as §9
-- requires.
#zil_assert_relation_defect Physlib.Thermodynamics.unruh_eq_comptonTemperature_iff
  "1" with "a : L T^-2"
#zil_assert_relation_defect Physlib.Thermodynamics.unruh_eq_comptonTemperature_iff
  "1" with "a : L T^-2, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Cosmology.FLRW.HorizonEntropyExpansion.unruh_eq_gibbonsHawkingSI_iff
  "1" with "a : L T^-2, H : T^-1"
#zil_assert_relation_defect Cosmology.FLRW.HorizonEntropyExpansion.unruh_eq_gibbonsHawkingSI_iff
  "1" with "a : L T^-2, H : T^-1, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension Physlib.Thermodynamics.comptonTemperature "Θ I"
#zil_assert_dimension Physlib.Thermodynamics.comptonTemperature "Θ I"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI "Θ I"
  with "H : T^-1"
#zil_assert_dimension Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI "Θ I"
  with "H : T^-1, G : L^3 T^-2 M^-1 I^-1"

-- §11 The temperature triangle closes consistently.
--
-- The unifier, re-run on the closed carriers, finds the one remaining pairing:
-- `comptonTemperature ≐ gibbonsHawkingTemperatureSI` with constraint `m·c² ≐ ℏ·H` — exactly
-- the composition of the two §10 welds through the shared Unruh carrier (eliminate `a` between
-- `a = c·H` and `a = mc³/ℏ`).  Proven as `comptonTemperature_eq_gibbonsHawkingSI_iff`; the
-- three pairwise constraints among the Unruh, Compton, and Gibbons–Hawking temperatures are a
-- consistent triangle.  `G`-free; held under both typings.
#zil_assert_relation_defect
  Cosmology.FLRW.HorizonEntropyExpansion.comptonTemperature_eq_gibbonsHawkingSI_iff
  "1" with "H : T^-1"
#zil_assert_relation_defect
  Cosmology.FLRW.HorizonEntropyExpansion.comptonTemperature_eq_gibbonsHawkingSI_iff
  "1" with "H : T^-1, G : L^3 T^-2 M^-1 I^-1"

-- §12 The temperature sector, held as one diagram.
--
-- `#zil_assert_diagram` (ZilUnifyDiagram) holds the sector as a single object: on
-- {Unruh, Compton, Gibbons–Hawking-SI, Hawking} every edge's bridge constraint is
-- dimensionally homogeneous under the given typing AND every edge has a connecting theorem.
-- The tool's first run reported the two Hawking edges as underived composites (both flanks
-- proven through the Unruh carrier); they are now proven *as* those compositions —
-- `hawking_eq_comptonTemperature_iff` (`κ = mc³/ℏ`) and `hawking_eq_gibbonsHawkingSI_iff`
-- (`κ = c·H`, the de Sitter surface gravity) — closing the diagram the tool opened.
-- Composition is exact by construction at the normal-form level; what the assert holds is
-- homogeneity plus proof coverage, fail-closed.  All four carriers are `G`-free, so the
-- diagram holds under both typings.
#zil_assert_diagram Physlib.Thermodynamics.unruhTemperature,
  Physlib.Thermodynamics.comptonTemperature,
  Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI,
  Physlib.Relativity.SemiClassical.hawkingTemperature
  with "a : L T^-2, H : T^-1, κ : L T^-2"
#zil_assert_diagram Physlib.Thermodynamics.unruhTemperature,
  Physlib.Thermodynamics.comptonTemperature,
  Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI,
  Physlib.Relativity.SemiClassical.hawkingTemperature
  with "a : L T^-2, H : T^-1, κ : L T^-2, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Physlib.Thermodynamics.hawking_eq_comptonTemperature_iff
  "1" with "κ : L T^-2"
#zil_assert_relation_defect Physlib.Thermodynamics.hawking_eq_comptonTemperature_iff
  "1" with "κ : L T^-2, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Cosmology.FLRW.HorizonEntropyExpansion.hawking_eq_gibbonsHawkingSI_iff
  "1" with "κ : L T^-2, H : T^-1"
#zil_assert_relation_defect Cosmology.FLRW.HorizonEntropyExpansion.hawking_eq_gibbonsHawkingSI_iff
  "1" with "κ : L T^-2, H : T^-1, G : L^3 T^-2 M^-1 I^-1"

-- §13 The gravity vertex: the diagram sees the fault line.
--
-- Adding `verlindeGravityTemperature` as a fifth object: under SI typing all ten edges are
-- homogeneous and connected — the two composites the tool reported are proven as their
-- compositions (`gravity_eq_comptonTemperature_iff`: `GM/R² = mc³/ℏ`;
-- `gravity_eq_gibbonsHawkingSI_iff`: `GM/R² = c·H`), and the Hawking edge was already covered
-- (`verlindeTemperature_at_horizon_is_hawking`).  Under the holographic typing the five-object
-- diagram is NOT asserted, and that is the finding: exactly the four edges into the gravity
-- vertex go inhomogeneous, each by exactly one nat — §7's fault line as diagram geometry.
-- The `G`-free four-object core (§12) is typing-invariant; the nat lives on every edge into
-- gravity.  Held per-edge below: defect `1` under SI, exactly `I^-1` under holographic `G`.
#zil_assert_diagram Physlib.Thermodynamics.unruhTemperature,
  Physlib.Thermodynamics.comptonTemperature,
  Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI,
  Physlib.Relativity.SemiClassical.hawkingTemperature,
  Physlib.Thermodynamics.verlindeGravityTemperature
  with "a : L T^-2, H : T^-1, κ : L T^-2"
#zil_assert_relation_defect Physlib.Thermodynamics.gravity_eq_comptonTemperature_iff "1"
#zil_assert_relation_defect Physlib.Thermodynamics.gravity_eq_comptonTemperature_iff
  "I^-1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Cosmology.FLRW.HorizonEntropyExpansion.gravity_eq_gibbonsHawkingSI_iff
  "1" with "H : T^-1"
#zil_assert_relation_defect Cosmology.FLRW.HorizonEntropyExpansion.gravity_eq_gibbonsHawkingSI_iff
  "I^-1" with "H : T^-1, G : L^3 T^-2 M^-1 I^-1"

-- §14 The mediator pattern, mechanized and held on its two historical instances.
--
-- `#zil_assert_mediator` (ZilUnifyMediator) re-runs the §10 discoveries as searches: the
-- dimensional defect of the pair is solved exactly over {ℏ, k_B, c, G}, the candidate
-- mediator's normal form is constructed, and the corpus sweep must find the definition that
-- closed the gap — `comptonTemperature` for the clock/temperature interface (prescription
-- `1/(2π)`), `gibbonsHawkingTemperatureSI` for the energy-convention interface (exact).
-- Both under both typings (the carriers are `G`-free, so the conversions are identical).
-- Delete or rename a mediator and this gate fails.
#zil_assert_mediator
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency
  Physlib.Thermodynamics.unruhTemperature
  finds Physlib.Thermodynamics.comptonTemperature with "a : L T^-2"
#zil_assert_mediator
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency
  Physlib.Thermodynamics.unruhTemperature
  finds Physlib.Thermodynamics.comptonTemperature
  with "a : L T^-2, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_mediator Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperature
  Physlib.Thermodynamics.unruhTemperature
  finds Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI
  with "H : T^-1, a : L T^-2"
#zil_assert_mediator Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperature
  Physlib.Thermodynamics.unruhTemperature
  finds Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperatureSI
  with "H : T^-1, a : L T^-2, G : L^3 T^-2 M^-1 I^-1"

-- §15 The first hunt's findings, closed and held.
--
-- The mediator search run as a discovery sweep (record in `ZilUnifyMediator`): the
-- rate-sector image of the Unruh temperature turned out to already exist in a *different
-- arc* — `CausalDiamond.QIFEquilibrium.qifEntropicRate`, an exact match — and is now welded
-- (`unruhTemperature_eq_qifEntropicRate_scaled`: `T_U = (ℏ/k_B)·λ`, with the Hawking face as
-- instantiation).  The temperature-sector image of `deBroglieFrequency` was genuinely
-- missing and is now `deBroglieTemperature = E/(2πk_B)`, welded to Unruh at `a = Ec/ℏ` and
-- to the Compton temperature exactly at the rest energy `E = mc²` — the §9 unifier residue
-- as a theorem.  All carriers `G`-free: held under both typings.
#zil_assert_mediator
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency
  Physlib.Thermodynamics.unruhTemperature
  finds Physlib.Thermodynamics.deBroglieTemperature with "a : L T^-2"
#zil_assert_mediator
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency
  Physlib.Thermodynamics.unruhTemperature
  finds Physlib.Thermodynamics.deBroglieTemperature
  with "a : L T^-2, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension Physlib.Thermodynamics.deBroglieTemperature "Θ I"
#zil_assert_dimension Physlib.Thermodynamics.deBroglieTemperature "Θ I"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Physlib.Thermodynamics.unruh_eq_deBroglieTemperature_iff
  "1" with "a : L T^-2"
#zil_assert_relation_defect Physlib.Thermodynamics.unruh_eq_deBroglieTemperature_iff
  "1" with "a : L T^-2, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Physlib.Thermodynamics.deBroglie_eq_comptonTemperature_iff "1"
#zil_assert_relation_defect Physlib.Thermodynamics.deBroglie_eq_comptonTemperature_iff
  "1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium.unruhTemperature_eq_qifEntropicRate_scaled
  "1" with "a : L T^-2"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QIFEquilibrium.unruhTemperature_eq_qifEntropicRate_scaled
  "1" with "a : L T^-2, G : L^3 T^-2 M^-1 I^-1"

-- §16 The converter: one map behind the SI temperature sector, and the mass shell.
--
-- The `2π`-quantization family the analogy layer reported is one definition:
-- `deBroglieTemperature = E/(2πk_B)` is the sector's converter, and `comptonTemperature`
-- and `gibbonsHawkingTemperatureSI` are now *defined* as its instances at `E = mc²` and
-- `E = ℏH` — the duplicated denominators and iff-proof blocks collapsed into the converter's
-- injectivity and homogeneity.  On it, the full Einstein relation: the boost law
-- (`deBroglieTemperature_gamma_compton`; the rest-point weld is the `γ = 1` slice) and the
-- mass shell transported to the temperature sector (`deBroglieTemperature_sq_massShell_iff`:
-- `E² = (pc)² + (mc²)²` iff `T_dB(E)² = T_C² + T_dB(pc)²`).  All `G`-free; held under both
-- typings.
#zil_assert_relation_defect Physlib.Thermodynamics.deBroglieTemperature_gamma_compton
  "1" with "γ : 1"
#zil_assert_relation_defect Physlib.Thermodynamics.deBroglieTemperature_gamma_compton
  "1" with "γ : 1, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Physlib.Thermodynamics.deBroglieTemperature_sq_massShell_iff
  "1" with "p : L T^-1 M"
#zil_assert_relation_defect Physlib.Thermodynamics.deBroglieTemperature_sq_massShell_iff
  "1" with "p : L T^-1 M, G : L^3 T^-2 M^-1 I^-1"

-- §17 Millikan's `h` and the fault line: the photoelectric route is information-neutral.
--
-- Millikan 1916 (`PhotoelectricPlanckDetermination`) under both typings.  Einstein's equation
-- carries no `G` and no `k_B`: the stopping energy is a pure energy under SI and holographic
-- typing alike, and every identity of the determination is defect-free — the photoelectric
-- route to `h` never touches the information axis.  The Planck radiation route, by contrast,
-- runs through nat-charged ingredients — the framework `k_B` carries `I⁻¹`, so the
-- radiation-density constant `a = 8π⁵k⁴/(15h³c³)` carries `I⁻⁴` (and Stefan's `σ = ac/4`
-- with it) — yet the inversion is still defect-1 under both typings: the charges cancel
-- inside the law (`k⁴` against `a`), the §8 mechanism.  The two historical routes to `h`
-- differ exactly on the information axis; `h` itself is measured on the clean side of the
-- one-nat fault line.
#zil_assert_dimension Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.stoppingEnergy
  "L^2 T^-2 M" with "h : L^2 T^-1 M, ν : T^-1, p : L^2 T^-2 M"
#zil_assert_dimension Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.stoppingEnergy
  "L^2 T^-2 M" with "h : L^2 T^-1 M, ν : T^-1, p : L^2 T^-2 M, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.stoppingPotential_charge
  "1" with "h : L^2 T^-1 M, ν : T^-1, p : L^2 T^-2 M, e : C"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.stoppingPotential_charge
  "1" with "h : L^2 T^-1 M, ν : T^-1, p : L^2 T^-2 M, e : C, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.contact_emf_equation
  "1" with "h : L^2 T^-1 M, ν : T^-1, ν₀ : T^-1, ν₀' : T^-1, e : C, V₀ : L^2 T^-2 M C^-1, V₀' : L^2 T^-2 M C^-1, K : L^2 T^-2 M C^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.contact_emf_equation
  "1" with "h : L^2 T^-1 M, ν : T^-1, ν₀ : T^-1, ν₀' : T^-1, e : C, V₀ : L^2 T^-2 M C^-1, V₀' : L^2 T^-2 M C^-1, K : L^2 T^-2 M C^-1, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.planck_radiation_density_iff
  "1" with "h : L^2 T^-1 M, k : L^2 T^-2 M Θ^-1 I^-1, a : L^-1 T^-2 M Θ^-4 I^-4, c : L T^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.planck_radiation_density_iff
  "1" with "h : L^2 T^-1 M, k : L^2 T^-2 M Θ^-1 I^-1, a : L^-1 T^-2 M Θ^-4 I^-4, c : L T^-1, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.radiation_density_stefan
  "1" with "a : L^-1 T^-2 M Θ^-4 I^-4, σ : T^-3 M Θ^-4 I^-4, c : L T^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.photoelectric_temperature_additivity
  "1" with "h : L^2 T^-1 M, ν : T^-1, p : L^2 T^-2 M, e : C, V : L^2 T^-2 M C^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.PhotoelectricPlanckDetermination.photoelectric_temperature_additivity
  "1" with "h : L^2 T^-1 M, ν : T^-1, p : L^2 T^-2 M, e : C, V : L^2 T^-2 M C^-1, G : L^3 T^-2 M^-1 I^-1"

-- §18 The one-mass family: the Compton clock welded across four arcs.
--
-- Script-applied welds from the `#zil_link` survey: the Compton temperature's mass binder
-- reaches the Schwarzschild radius (`comptonTemperature_eq_schwarzschildRadius_scaled`),
-- the KayWald Euclidean period (`comptonTemperature_eq_schwarzschildEuclideanPeriod_scaled`,
-- natural-units carrier — its `G = c = 1` convention is absorbed in the prescription), and
-- Padmanabhan's gravitational length
-- (`comptonTemperature_eq_gravitationalLength_scaled`).  The `G`-carrying welds have `G` on
-- both sides (scale and carrier), so the nat charge cancels *inside the weld* — defect 1
-- under both typings, the §8 mechanism, unlike §13's single-`G` edges.  A fourth candidate
-- (`jacobsonMyersWeight`) was a same-letter false positive — its `m` is a ℕ-valued Lovelock
-- order, not a mass — dropped, and the binder-type check is queued for the linking layer.
#zil_assert_relation_defect
  Physlib.Relativity.SemiClassical.comptonTemperature_eq_schwarzschildRadius_scaled "1"
#zil_assert_relation_defect
  Physlib.Relativity.SemiClassical.comptonTemperature_eq_schwarzschildRadius_scaled
  "1" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.comptonTemperature_eq_gravitationalLength_scaled
  "1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.comptonTemperature_eq_gravitationalLength_scaled
  "1" with "G : L^3 T^-2 M^-1 I^-1"

-- §19 Token string discipline: the graph's string layer is itself gated.  Prefix coinage
-- on the establishment relations (formalizes/derives/supported_by) fails the build — the
-- whitelist below is the vocabulary, and editing it is a deliberate act (the `axiom:`
-- incident, made structurally unrepeatable).  Every `lean:` cross-reference must resolve
-- in the environment up to a ratchet bound for pre-existing rot, lower-only.  The bound is
-- the enforcement context's own measurement: module semantics cannot see non-public
-- constants, so this gate reads a few more rotten than a classic-import scratch does.
-- Burned down 112 → 8 by `scripts/repair_lean_refs.py` plus manual triage, across five
-- distinct rot classes: declarations that moved namespace; tokens spelling FILE PATHS
-- (`QuantumInfo.Entropy.X`) where the real namespace is bare or class-scoped — these live
-- in sibling source roots the resolver initially never searched, so they read as deleted;
-- malformed tokens carrying prose slugs where a declaration name belongs; ASCII
-- transliteration of Unicode identifiers (`Igamma1gamma3` for `Iγ1γ3`); and tokens naming
-- a whole module rather than a result; ORPHAN MODULES never added to the root manifest, whose
-- constants no `import Physlib` environment ever loads (two found; both now in the manifest);
-- and a manifest module with no `public section`, all of whose theorems were module-private
-- (exposed).  The final reference cited a Fourier-inversion name where the proof uses
-- Plancherel; it now points at `MeasureTheory.Lp.norm_fourier_eq`, which the proof calls.
-- The assert below carries NO allowance: every lean: reference must resolve, forever.  Retagged into `claim:`
-- at gate birth: 18 paper-anchored prefixes (vytheeswaran-1998-*, golse-paul-*), 3
-- prefixless equation statements, 1 one-off `geometry:`.
#zil_assert_token_prefixes "claim", "law", "constant", "assumption", "definition",
  "theorem", "input", "model", "extension", "lean", "paper", "mathlib", "cite", "book",
  "source", "measurement", "value", "object", "experiment", "postulate"
#zil_assert_lean_refs

-- §20 The ceiling weld under the holographic Newton constant, and where the nat lives.
-- `covariantBound_ceiling_eq_sphericalBound` says the covariant bound's ceiling is the
-- spherical bound's right-hand side under `ℓ_P² = Gℏ/c³`.  Read with an SI `G` and a plain
-- length `ℓ_P`, it is homogeneous.  Read with the holographic `G` (area per bit,
-- `[G] = L³M⁻¹T⁻²I⁻¹`) and `ℓ_P` still a plain length, it breaks by exactly one nat — the
-- seventh member of the §7 bit-form family.  But the theorem's own hypothesis forbids that
-- reading: with holographic `G`, `Gℏ/c³` carries `I⁻¹`, so `ℓ_P` carries `I^{-1/2}` and the
-- weld is homogeneous again.  The fault line, traced to its source, sits at the Planck
-- *area*: `ℓ_P²` is area-per-nat, which is the holographic principle itself (`N = A/ℓ_P²`).
-- The Planck length is not a pure length under holographic typing — it is the square root
-- of an area per nat, and that half-nat is where the whole one-nat tower is anchored.
#zil_assert_relation_defect Physlib.Thermodynamics.covariantBound_ceiling_eq_sphericalBound
  "1" with "A : L^2, ℓP : L"
#zil_assert_relation_defect Physlib.Thermodynamics.covariantBound_ceiling_eq_sphericalBound
  "I^-1" with "A : L^2, ℓP : L, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect Physlib.Thermodynamics.covariantBound_ceiling_eq_sphericalBound
  "1" with "A : L^2, ℓP : L I^-1/2, G : L^3 T^-2 M^-1 I^-1"

-- §21 The nat-charge ladder, and where the half-nat comes from.  Substituting the
-- holographic `G` into the repository's three standard lengths sorts them by information
-- charge: the Compton wavelength `ℏ/mc` carries none (no `G` in it), the gravitational
-- length `Gm/c²` carries one inverse nat, and the Planck length sits at exactly half.
-- Padmanabhan's zero-point-length identity `ℓ_P² = λ_C · r_g`
-- (`compton_grav_product_eq_planckSq`) is therefore homogeneous under *both* typings while
-- explaining the half: `0 + 1 = 2 × ½`.  The Planck length is the geometric mean of a
-- nat-free quantum length and a one-nat gravitational length, and that is the whole origin
-- of the half-integer charge — every one-nat defect elsewhere is this half appearing twice.
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength "L"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.gravitationalLength "L I^-1"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLengthSq "L^2 I^-1"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.compton_grav_product_eq_planckSq
  "1" with "G : L^3 T^-2 M^-1 I^-1"

-- The mass side carries the opposite half: `m_P² = ℏc/G` reads `M² I`, so `m_P` is
-- `M I^{+1/2}` and the Planck product `ℓ_P·m_P = ℏ/c` is nat-free — `G` cancels between
-- numerator and denominator, and so does the information charge.
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.planckMassSq "M^2 I"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLengthSq_mul_planckMassSq
  "1" with "G : L^3 T^-2 M^-1 I^-1"

-- A black hole's surface gravity is not a plain acceleration under this typing: `c⁴/(4GM)`
-- carries one nat.  So the Unruh temperature of an accelerated observer and the Hawking
-- temperature at a *supplied* surface gravity agree at one nat, while the Hawking
-- temperature evaluated at the Schwarzschild surface gravity carries two — the extra one is
-- the horizon's own bit count, entering through `G`.  Equivalence holds exactly as long as
-- the horizon's bits are not resolved.
#zil_assert_dimension Physlib.Relativity.SemiClassical.schwarzschildSurfaceGravity "L T^-2 I"
  with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension Physlib.Relativity.SemiClassical.hawkingTemperature "Θ I" with "κ : L T^-2"
#zil_assert_dimension Physlib.Thermodynamics.unruhTemperature "Θ I" with "a : L T^-2"
#zil_assert_dimension Physlib.Relativity.SemiClassical.hawkingTemperature "Θ I^2"
  with "κ : L T^-2 I, G : L^3 T^-2 M^-1 I^-1"

-- §22 Jacobson's equation of state under the two typings.  `clausius_equation_of_state`
-- takes the Clausius relation on a local Rindler horizon with the Unruh temperature and
-- the area-entropy and returns `R_kk = 8πG T_kk`.  Typed so that the SI reading is
-- homogeneous (the theorem is written in `c = 1` units, so the standard `c⁴` is absent),
-- the holographic reading carries exactly one inverse nat.  The split is on the two sides:
-- the Ricci null contraction is pure geometry and information-free, while the matter term
-- reaches it only through `G`, which is area-per-bit.  **The Einstein equation of state is
-- the one-nat conversion between geometry and matter** — the same shape as §7's result that
-- the inertial-equals-gravitational reading is the one-nat conversion, and traceable by
-- §21 to the Planck area being area-per-nat.
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.clausius_equation_of_state
  "1" with "Rkk : L^-2, Tkk : M L^-5 T^2, κb : L T^-2, T_U : Θ I"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.clausius_equation_of_state
  "I^-1" with "Rkk : L^-2, Tkk : M L^-5 T^2, κb : L T^-2, T_U : Θ I, G : L^3 T^-2 M^-1 I^-1"

-- §23 The Einstein equation at tensor level: **where** the nat of §22 sits, and what it
-- says about Λ.  The equation is `G_ab + Λ g_ab = κ T_ab` with `κ = 8πG/c⁴`.  Of its three
-- terms, the Einstein tensor is pure curvature and the `Λ g_ab` term has no `G` in it, so
-- both are information-free; only the coupling carries the nat.  §22's one-nat defect is
-- therefore *localized*: it sits on `κ`, and nowhere else.
--
-- The consequence is sharp and is the physics content of this section.  `Λ` and `T_ab` are
-- **not interchangeable** under this typing.  Absorbing the cosmological constant into the
-- matter side means writing `ρ_Λ = Λc²/(8πG)`, and dividing by `G` injects one nat: the
-- vacuum energy density reads `[M L⁻³]` under SI and `[M L⁻³ I]` under the holographic `G`,
-- while an ordinary matter density carries none.  **Dark energy and ordinary matter differ
-- by exactly one nat.**  `Λ` is a geometric, information-free quantity; presenting it as a
-- matter density is precisely what charges it.
#zil_assert_dimension Cosmology.FLRW.MatterContent.vacuumEnergyDensity "L^-3 M"
  with "Λ : L^-2"
#zil_assert_dimension Cosmology.FLRW.MatterContent.vacuumEnergyDensity "L^-3 M I"
  with "Λ : L^-2, G : L^3 T^-2 M^-1 I^-1"

-- And the reading that keeps `Λ` itself neutral: in horizon-bit form `Λ = 12πc³/(ℏGN)` the
-- inverse nat of `G` is cancelled by the nat of the bit count `N`, so `Λ` is information-free
-- under both typings — but *only* when `N` is typed as a genuine count of bits.  Left
-- dimensionless, the same identity breaks by one nat.  The bit-count reading of the de Sitter
-- horizon is exactly what makes the cosmological constant information-neutral.
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits.cosmologicalConstant_bitForm
  "1" with "Λ : L^-2"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits.cosmologicalConstant_bitForm
  "1" with "Λ : L^-2, G : L^3 T^-2 M^-1 I^-1, N : I"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits.cosmologicalConstant_bitForm
  "I^-1" with "Λ : L^-2, G : L^3 T^-2 M^-1 I^-1"

-- Tooling limit, recorded rather than papered over: `#zil_dimension_of` cannot type
-- matrix- or tensor-valued binders (`einsteinTensor` returns every binder unknown), so the
-- tensor-level statement above is made through the equation's *scalar coefficient slots*
-- (`1`, `Λ`, `κ`) and not by typing `G_ab`, `g_ab` and `T_ab` themselves.  Extending the
-- dimensional layer to tensor-valued carriers is the open frontier here.

-- §24 The complex Einstein equation under the holographic `G`: the two sectors have
-- **opposite** information character.  Substituting `[G] = L³M⁻¹T⁻²I⁻¹` into
-- `G_ab + iΛ_ab = κ(T_ab + iS_ab)` and propagating through the repository's own definitions
-- (`entropicStressTensor` gives `[S] = [∇φ]²`; the imaginary curvature is built from `∇∇φ`,
-- so `[Λ] = [φ]/L²`) the imaginary field equation `Λ = κS` forces `[φ] = 1/[κ] = c⁴/8πG`.
-- The entropic potential is therefore a **force**, not a dimensionless phase — and `c⁴/G` is
-- the maximum force of general relativity.
--
-- Measured below: that scale reads `[L T⁻² M]` under SI and `[L T⁻² M I]` under the
-- holographic `G` — one nat, inherited from `G` sitting in its denominator — while the
-- coupling carries exactly the opposite.  Propagating: `[∇φ]` one nat, `[S] = [∇φ]²` two,
-- `[Λ] = [φ]/L²` one, and `[κS]` is `−1 + 2 = 1`.  **The imaginary sector is
-- information-balanced**, whereas the real sector `G_ab = κT_ab` carries the single inverse
-- nat of §22–§23.  The entropic sector has information on both sides and needs no conversion;
-- the real sector is where bits become curvature.
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.entropicPotentialScale
  "L T^-2 M"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.entropicPotentialScale
  "L T^-2 M I" with "G : L^3 T^-2 M^-1 I^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.einsteinCouplingScalar
  "L^-1 T^2 M^-1"
#zil_assert_dimension
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.einsteinCouplingScalar
  "L^-1 T^2 M^-1 I^-1" with "G : L^3 T^-2 M^-1 I^-1"

-- The two scales are reciprocal, so their nats cancel: the product is dimensionless and
-- information-free under both typings.  That cancellation is the mechanism of the balance.
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.entropicPotentialScale_mul_einsteinCouplingScalar
  "1"
#zil_assert_relation_defect
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.entropicPotentialScale_mul_einsteinCouplingScalar
  "1" with "G : L^3 T^-2 M^-1 I^-1"

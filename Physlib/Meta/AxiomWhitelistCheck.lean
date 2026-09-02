/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PathIntegral.DampedHeatLandauerDichotomy
public import Physlib.QFT.PathIntegral.WickClock
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularFromState
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks
public import Physlib.Meta.DyadicCalderonScaleLadderZil
public import Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold
public import Physlib.Thermodynamics.ComputationLandauer
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# Standard-axiom build gate for the dissipation / wedge-modular arc

Physlib's cleanliness bar is that every headline theorem depends only on the three standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. ZIL's embedded `no_new_axioms` check demands an *empty*
transitive axiom closure, which no Mathlib-based proof can satisfy, so it is never usable in practice — the
guarantee physlib actually wants has until now been checked by hand with `#print axioms`.

This optional development/CI module supplies the missing gate. `#physlib_axiom_clean <decl>` fails
elaboration if any axiom **outside** the standard three appears in the declaration's transitive closure,
turning the manual `#print axioms` habit into a build-time invariant, and then runs that gate over the
dissipation / Tomita–Takesaki wedge-modular arc.

It is built on Lean's own `Lean.collectAxioms` — the exact collector `#print axioms` uses, which precomputes
axiom dependencies at olean export and looks them up module-locally. (ZIL's hand-rolled `declarationAxioms`
walks `getUsedConstantsAsSet` directly and over-collects sealed imported declarations under the module
system, so it cannot back a whitelist; that is also why ZIL's all-or-nothing `no_new_axioms` is unusable and
only `no_sorry` is ever asserted.)

It adds no physical definitions, theorem aliases, axioms, or proof terms; production roots do not import it.
-/

@[expose] public section

open Lean Elab Command

namespace Physlib.Meta.AxiomWhitelistCheck

/-- The three standard Lean axioms a physlib "axiom-clean" proof is permitted to depend on. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The native-evaluation / compiler-trust axioms introduced by `native_decide`. These are a *distinct trust
class* from `standardAxioms`: they trust the compiler's `reduceBool`/`reduceNat`, not only the kernel. Physlib
records them separately so a proof depending on them is *compiler-trusting*, not *kernel-clean*. In current
Lean, `native_decide` also emits a *per-declaration* generated axiom whose name carries the `native_decide`
marker (`⟨decl⟩._native.native_decide.ax_…`); `isCompilerTrustAxiom` catches both the named core axioms and
that generated family. -/
meta def compilerTrustAxioms : List Name :=
  [``Lean.trustCompiler, ``Lean.ofReduceBool, ``Lean.ofReduceNat]

/-- Whether an axiom name belongs to the compiler-trust (`native_decide`) family — either one of the named
core axioms or a per-declaration generated `native_decide` axiom. -/
meta def isCompilerTrustAxiom (a : Name) : Bool :=
  compilerTrustAxioms.contains a
    || (a.toString.splitOn "native_decide").length > 1
    || (a.toString.splitOn "_native").length > 1

/-- **Three-tier axiom classification.** A declaration is `kernel-clean` if its transitive axiom closure lies
within `standardAxioms`; `compiler-trusting` if it additionally uses only compiler-trust (`native_decide`)
axioms; and `exotic` otherwise. -/
meta def classifyAxioms (axioms : Array Name) : String :=
  let exotic := axioms.filter fun a => !(standardAxioms.contains a) && !(isCompilerTrustAxiom a)
  if !exotic.isEmpty then s!"exotic: {exotic.toList}"
  else if axioms.any isCompilerTrustAxiom then "compiler-trusting (native_decide)"
  else "kernel-clean"

syntax (name := physlibAxiomReportCmd) "#physlib_axiom_report " ident : command

/-- Log the three-tier axiom classification of a declaration without failing the build — the queryable
honesty report behind the strict `#physlib_axiom_clean` gate. -/
@[command_elab physlibAxiomReportCmd]
meta def elabPhyslibAxiomReport : CommandElab := fun stx => do
  match stx with
  | `(#physlib_axiom_report $target:ident) =>
      let declaration ← resolveGlobalConstNoOverload target
      let axioms ← Lean.collectAxioms declaration
      logInfoAt stx m!"physlib axiom-report: '{declaration}' is {classifyAxioms axioms} ({axioms.size} axioms)"
  | _ => throwUnsupportedSyntax

syntax (name := physlibAxiomCleanCmd) "#physlib_axiom_clean " ident : command

/-- Fail elaboration unless the declaration's transitive axiom closure lies within `standardAxioms`;
otherwise report the offending axioms. This is the `no_exotic_axioms` gate that `#zil_validate_embedded`'s
all-or-nothing `no_new_axioms` cannot express. -/
@[command_elab physlibAxiomCleanCmd]
meta def elabPhyslibAxiomClean : CommandElab := fun stx => do
  match stx with
  | `(#physlib_axiom_clean $target:ident) =>
      let declaration ← resolveGlobalConstNoOverload target
      let axioms ← Lean.collectAxioms declaration
      let exotic := axioms.filter (fun a => !standardAxioms.contains a)
      unless exotic.isEmpty do
        throwErrorAt target
          "physlib axiom-clean failed for '{declaration}': non-standard axioms {exotic.toList}"
      logInfoAt stx
        m!"physlib axiom-clean: '{declaration}' uses only the standard axioms ({axioms.size} total)"
  | _ => throwUnsupportedSyntax

/-- Whether a declaration's *statement* is a definitional restatement — an equality or iff whose two sides
are already definitionally equal, hence provable by `rfl`, hence adding no content beyond its definitions.
Works from the type alone (robust under the module system, which seals proof terms). A `bridge_theorem` for
which this is `true` is a `def` in disguise — the physlib "no vacuous theorems" bar. -/
meta def isDefinitionalRestatement (declType : Expr) : MetaM Bool :=
  Meta.forallTelescope declType fun _ concl => do
    match concl.eq? with
    | some (_, lhs, rhs) => Meta.isDefEq lhs rhs
    | none =>
      match concl.iff? with
      | some (lhs, rhs) => Meta.isDefEq lhs rhs
      | none => return false

syntax (name := physlibNonVacuousCmd) "#physlib_non_vacuous " ident : command

/-- **Non-vacuity gate.** Fail elaboration if the declaration's statement is a *definitional restatement* —
an `=`/`↔` whose sides are already defeq (provable by `rfl`), which the physlib bar counts as a `def`, not a
formalization. Any genuine theorem — sides not defeq, or a non-`=`/`↔` shape — passes. -/
@[command_elab physlibNonVacuousCmd]
meta def elabPhyslibNonVacuous : CommandElab := fun stx => do
  match stx with
  | `(#physlib_non_vacuous $target:ident) =>
      let declaration ← resolveGlobalConstNoOverload target
      let some info := (← getEnv).find? declaration
        | throwErrorAt target "unknown declaration '{declaration}'"
      let isTrivial ← liftTermElabM (isDefinitionalRestatement info.type)
      if isTrivial then
        throwErrorAt target
          "physlib non-vacuous failed for '{declaration}': statement is a definitional restatement (sides defeq, provable by rfl)"
      logInfoAt stx m!"physlib non-vacuous: '{declaration}' is substantive (not a definitional restatement)"
  | _ => throwUnsupportedSyntax

syntax (name := physlibVacuityReportCmd) "#physlib_vacuity_report " ident : command

/-- Non-failing report of whether a declaration's statement is a definitional restatement — the queryable
form of the non-vacuity gate. -/
@[command_elab physlibVacuityReportCmd]
meta def elabPhyslibVacuityReport : CommandElab := fun stx => do
  match stx with
  | `(#physlib_vacuity_report $target:ident) =>
      let declaration ← resolveGlobalConstNoOverload target
      let some info := (← getEnv).find? declaration
        | throwErrorAt target "unknown declaration '{declaration}'"
      let isTrivial ← liftTermElabM (isDefinitionalRestatement info.type)
      let verdict : String := if isTrivial then "definitional restatement (sides defeq)" else "substantive"
      logInfoAt stx m!"physlib vacuity-report: '{declaration}' is {verdict}"
  | _ => throwUnsupportedSyntax

syntax (name := physlibAxiomCleanAllCmd) "#physlib_axiom_clean_all " "[" ident,* "]" : command

/-- **Batch axiom-clean gate.** Run `#physlib_axiom_clean` over a bracketed list of declarations, collecting
*every* taint rather than stopping at the first, then fail once with the full offenders list. Lets a spine
audit gate a whole family in one command instead of one line per declaration, and reports all failures at
once. -/
@[command_elab physlibAxiomCleanAllCmd]
meta def elabPhyslibAxiomCleanAll : CommandElab := fun stx => do
  match stx with
  | `(#physlib_axiom_clean_all [ $targets,* ]) => do
      let targetArr := targets.getElems
      let mut failures : Array (Name × List Name) := #[]
      for target in targetArr do
        let declaration ← resolveGlobalConstNoOverload target
        let axioms ← Lean.collectAxioms declaration
        let exotic := axioms.filter (fun a => !standardAxioms.contains a)
        unless exotic.isEmpty do
          failures := failures.push (declaration, exotic.toList)
      unless failures.isEmpty do
        throwErrorAt stx m!"physlib axiom-clean-all failed for {failures.size} of {targetArr.size} \
          declarations: {failures.toList}"
      logInfoAt stx
        m!"physlib axiom-clean-all: all {targetArr.size} declarations use only the standard axioms"
  | _ => throwUnsupportedSyntax

syntax (name := physlibNonVacuousAllCmd) "#physlib_non_vacuous_all " "[" ident,* "]" : command

/-- **Batch non-vacuity gate.** Run `#physlib_non_vacuous` over a bracketed list of declarations, collecting
every definitional restatement, then fail once with the full offenders list. The batch companion to
`#physlib_axiom_clean_all` — both honesty bars, machine-defended over a whole spine in one command. -/
@[command_elab physlibNonVacuousAllCmd]
meta def elabPhyslibNonVacuousAll : CommandElab := fun stx => do
  match stx with
  | `(#physlib_non_vacuous_all [ $targets,* ]) => do
      let targetArr := targets.getElems
      let mut failures : Array Name := #[]
      for target in targetArr do
        let declaration ← resolveGlobalConstNoOverload target
        let some info := (← getEnv).find? declaration
          | throwErrorAt target "unknown declaration '{declaration}'"
        let isTrivial ← liftTermElabM (isDefinitionalRestatement info.type)
        if isTrivial then
          failures := failures.push declaration
      unless failures.isEmpty do
        throwErrorAt stx m!"physlib non-vacuous-all failed — {failures.size} of {targetArr.size} \
          declarations are definitional restatements (sides defeq): {failures.toList}"
      logInfoAt stx
        m!"physlib non-vacuous-all: all {targetArr.size} declarations are substantive"
  | _ => throwUnsupportedSyntax

/-! ### Audit — the damped-heat / Landauer dichotomy

Gated with the batch commands `#physlib_axiom_clean_all` / `#physlib_non_vacuous_all`: one command over
the whole family, both honesty bars at once. -/

#physlib_axiom_clean_all [
  Physlib.QFT.PathIntegral.dampedHeat_isometry_iff,
  Physlib.QFT.PathIntegral.dampedHeat_strict_contraction,
  Physlib.QFT.PathIntegral.dampedHeat_bit_erasure_time,
  Physlib.QFT.PathIntegral.dampedCascade_isometric_iff_landauerCount_zero,
  Physlib.QFT.PathIntegral.dampedHeat_two_sided_isometry_iff,
  Physlib.QFT.PathIntegral.dampedHeatSemigroup_isometry_iff,
  Physlib.QFT.PathIntegral.dampedHeatGenerator_eq_zero_iff ]

#physlib_non_vacuous_all [
  Physlib.QFT.PathIntegral.dampedHeat_isometry_iff,
  Physlib.QFT.PathIntegral.dampedCascade_isometric_iff_landauerCount_zero,
  Physlib.QFT.PathIntegral.dampedHeat_two_sided_isometry_iff,
  Physlib.QFT.PathIntegral.dampedHeatSemigroup_isometry_iff,
  Physlib.QFT.PathIntegral.dampedHeatGenerator_eq_zero_iff ]

/-! ### Audit — the Bisognano–Wichmann wedge KMS / Tomita structure -/

#physlib_axiom_clean Physlib.QFT.PathIntegral.wedgeModular_sqrt_at_pi
#physlib_axiom_clean Physlib.QFT.PathIntegral.reversiblePhaseC_kms_shift
#physlib_axiom_clean Physlib.QFT.PathIntegral.reversiblePhaseC_conj
#physlib_axiom_clean Physlib.QFT.PathIntegral.wedge_conjugation_antiunitary
#physlib_axiom_clean Physlib.QFT.PathIntegral.tomitaSPair_involutive
#physlib_axiom_clean Physlib.QFT.PathIntegral.tomitaSStar_comp_tomitaS
#physlib_axiom_clean Physlib.QFT.PathIntegral.wedge_boost_wick_dichotomy

/-! ### Audit — Hawking/Unruh wires and finite standardness -/

#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon.hawkingBoltzmannWeight_is_wedgeModular
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon.unruhBoltzmannWeight_is_wedgeModular
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon.wedgeModular_natural_is_unruhBeta
#physlib_axiom_clean QuantumMechanics.FiniteTarget.faithful_state_standard

/-! ### Audit — the Landauer computability anchor -/

#physlib_axiom_clean Physlib.Thermodynamics.ComputationLandauer.computation_keeps_kl

/-! ### Audit — toward full Tomita–Takesaki: modular flow, standard subspace, Haag duality -/

#physlib_axiom_clean Physlib.QFT.PathIntegral.modularFlowPair_group
#physlib_axiom_clean Physlib.QFT.PathIntegral.modularFlowPair_unitary
#physlib_axiom_clean Physlib.QFT.PathIntegral.modularFlow_kms_shift
#physlib_axiom_clean Physlib.QFT.PathIntegral.standardSubspace_separating
#physlib_axiom_clean Physlib.QFT.PathIntegral.standardSubspace_cyclic
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.wedge_haag_duality
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.wedge_tomita_takesaki_haag_duality

/-! ### Audit — modular automorphism, Reeh–Schlieder standard form -/

#physlib_axiom_clean Physlib.QFT.PathIntegral.standardSubspace_directSum
#physlib_axiom_clean Physlib.QFT.PathIntegral.modularTwoPointFunction_kms
#physlib_axiom_clean Physlib.QFT.PathIntegral.modular_kms_two_point
#physlib_axiom_clean Physlib.QFT.PathIntegral.modularTwoPointFunction_generator
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut_mul
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut_group
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut_fixes_generator
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut_preserves_generator_commutant
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.reehSchlieder_standardSubspace_correspondence
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut_oneParameterGroup
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut_hasDerivAt_adK
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut_generator_is_modularGenerator
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.ads_boost_not_ground_of_rotation_sign_reversal
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.adsKms_beta_eq_two_pi
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.buchholz_passive_mixing_vacuum_is_unruhKMS
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.antiunitary_involution_of_dense_tomita_core
#physlib_axiom_clean
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.BuchholzAdSTCPData.conjugates_representation

/-! ### Audit — the dyadic Calderón / scale-ladder weld -/

#physlib_axiom_clean Physlib.Meta.DyadicCalderonScaleLadderZil.dyadicCalderon_blockspin_ladder
#physlib_axiom_clean Physlib.Meta.DyadicCalderonScaleLadderZil.dampedHeat_dyadic_step
#physlib_axiom_clean Physlib.Meta.DyadicCalderonScaleLadderZil.multiNormLogPoint_blockspin_ladder

/-! ### Audit — the Carleson threshold layer -/

#physlib_axiom_clean Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.schrodinger_ae_subsequence_recovery
#physlib_axiom_clean Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.hasSobolevRegularity_mono
#physlib_axiom_clean Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.carlesonExponent_lt_bourgainMultilinear
#physlib_axiom_clean Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.tendsto_carlesonExponent_atTop
#physlib_axiom_clean Physlib.Mathematics.LpAeConvergence.ae_eventually_enorm_lt_of_eLpNorm_le_geometric
#physlib_axiom_clean Physlib.Mathematics.LpAeConvergence.ae_summable_norm_of_eLpNorm_le_geometric
#physlib_axiom_clean Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.schrodinger_borelCantelli_maximal_step
#physlib_axiom_clean Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.carlesonExponent_mul_maximalLebesgueExponent
#physlib_axiom_clean Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.schrodinger_ae_continuum_limit
#physlib_axiom_clean Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.spacetime_energy_slab

end Physlib.Meta.AxiomWhitelistCheck

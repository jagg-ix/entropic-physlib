/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Real.Basic
public import Physlib.Meta.AxiomWhitelistCheck
public meta import Lean.Elab.Command

/-!
# Antecedent-satisfiability build gate

The non-vacuity gate `#physlib_non_vacuous` rejects one vacuity class: a statement whose
*conclusion* is a definitional restatement. Its telescope discards every hypothesis, so it is
blind to the complementary class - *antecedent-failure vacuity*, a conditional theorem whose
hypotheses are jointly unsatisfiable, making the implication true over an empty model class. A
nontrivial proof of such a statement passes every existing gate: the axiom closure is standard,
the conclusion is substantive, and the ZIL contract checks wiring, not models.

`#physlib_hypotheses_inhabited <thm> using <wit>` closes that gap. It telescopes the theorem's
binders, builds the *hypothesis closure* - the existential quantification over all data binders
occurring at or before the last hypothesis, conjoining every `Prop` binder in order - and fails
elaboration unless the named witness declaration proves exactly that closure. A conditional
theorem gated this way cannot have an empty antecedent: the witness exhibits one full
instantiation of its hypotheses.

The closure for `theorem foo (x : ℝ) (hx : 0 < x) (y : ℝ) (hxy : x < y) : P` is
`∃ x : ℝ, 0 < x ∧ ∃ y : ℝ, x < y`; data binders after the last hypothesis are irrelevant to
inhabitation and are skipped. On mismatch the gate prints the expected closure, so the witness
statement can be copied from the error. Satisfiability is undecidable in general - the gate does
not *find* witnesses, it *demands* them.

Like the axiom-whitelist gate, this is a development/CI module: production roots do not import
it.
-/

@[expose] public section

open Lean Elab Command

namespace Physlib.Meta.HypothesisInhabitationCheck

/-- A declaration's type with its universe parameters instantiated by fresh level metavariables,
so `isDefEq` can unify universes between a polymorphic theorem and a monomorphic witness. -/
meta def typeWithFreshLevels (info : ConstantInfo) : MetaM Expr := do
  let us ← info.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
  return info.type.instantiateLevelParams info.levelParams us

/-- The **hypothesis closure** of a theorem type: existentially quantify every data binder up to
the last `Prop` binder, conjoin the `Prop` binders in order (quantifying a proof binder only when
a later binder's type depends on it), and return `True` for an unconditional statement. The
conclusion itself is discarded - this is the satisfiability content of the antecedent alone. -/
meta def hypothesisClosure (declType : Expr) : MetaM Expr :=
  Meta.forallTelescope declType fun args _concl => do
    let mut acc? : Option Expr := none
    for x in args.reverse do
      let xType ← Meta.inferType x
      let isHyp ← Meta.isProp xType
      match acc? with
      | none =>
        if isHyp then
          acc? := some xType
      | some acc =>
        if isHyp && !acc.hasAnyFVar (· == x.fvarId!) then
          acc? := some (mkApp2 (.const ``And []) xType acc)
        else
          let u ← Meta.getLevel xType
          acc? := some (mkApp2 (.const ``Exists [u]) xType (← Meta.mkLambdaFVars #[x] acc))
    match acc? with
    | none => return .const ``True []
    | some acc => return acc

syntax (name := physlibHypothesesInhabitedCmd)
  "#physlib_hypotheses_inhabited " ident " using " ident : command

/-- **Antecedent-satisfiability gate.** Fail elaboration unless the witness declaration proves
the theorem's hypothesis closure, exhibiting one full instantiation of its hypotheses. The
complement of `#physlib_non_vacuous`: that gate rejects trivial conclusions, this one rejects
empty antecedents. -/
@[command_elab physlibHypothesesInhabitedCmd]
meta def elabPhyslibHypothesesInhabited : CommandElab := fun stx => do
  match stx with
  | `(#physlib_hypotheses_inhabited $target:ident using $witness:ident) =>
      let thm ← resolveGlobalConstNoOverload target
      let wit ← resolveGlobalConstNoOverload witness
      let env ← getEnv
      let some thmInfo := env.find? thm
        | throwErrorAt target "unknown declaration '{thm}'"
      let some witInfo := env.find? wit
        | throwErrorAt witness "unknown declaration '{wit}'"
      let (ok, closureFmt) ← liftTermElabM do
        let closure ← hypothesisClosure (← typeWithFreshLevels thmInfo)
        let ok ← Meta.isDefEq (← typeWithFreshLevels witInfo) closure
        pure (ok, ← Meta.ppExpr closure)
      unless ok do
        throwErrorAt witness
          "physlib hypotheses-inhabited failed for '{thm}': witness '{wit}' does not prove \
          the hypothesis closure; expected a proof of  {closureFmt}"
      logInfoAt stx
        m!"physlib hypotheses-inhabited: antecedent of '{thm}' is witnessed by '{wit}'"
  | _ => throwUnsupportedSyntax

/-- Gate sample: a conditional statement whose antecedent must be exhibited. -/
theorem conditionalSample (x : ℝ) (hx : 0 < x) : x ≠ 0 := ne_of_gt hx

/-- Gate sample witness: the hypothesis closure of `conditionalSample`. -/
theorem conditionalSample_hypotheses : ∃ x : ℝ, 0 < x := ⟨1, one_pos⟩

/-- Gate sample with two data binders and two hypotheses, exercising the mixed
existential-conjunctive closure. -/
theorem conditionalSample₂ (x y : ℝ) (_hx : 0 < x) (hxy : x < y) : x ≠ y := ne_of_lt hxy

/-- Gate sample witness: the hypothesis closure of `conditionalSample₂`. -/
theorem conditionalSample₂_hypotheses : ∃ x y : ℝ, 0 < x ∧ x < y := ⟨1, 2, one_pos, one_lt_two⟩

end Physlib.Meta.HypothesisInhabitationCheck

end

open Physlib.Meta.HypothesisInhabitationCheck in
#physlib_hypotheses_inhabited conditionalSample using conditionalSample_hypotheses

open Physlib.Meta.HypothesisInhabitationCheck in
#physlib_hypotheses_inhabited conditionalSample₂ using conditionalSample₂_hypotheses

open Physlib.Meta.HypothesisInhabitationCheck in
#physlib_axiom_clean_all [
  conditionalSample,
  conditionalSample_hypotheses,
  conditionalSample₂,
  conditionalSample₂_hypotheses ]

open Physlib.Meta.HypothesisInhabitationCheck in
#physlib_non_vacuous_all [
  conditionalSample,
  conditionalSample_hypotheses,
  conditionalSample₂,
  conditionalSample₂_hypotheses ]

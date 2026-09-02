/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Meta.ZilConceptLookup

meta import Zil.Datalog.Attach

/-!
# `#zil_query` — clause-based retrieval over the ZIL graph

`#zil_concept_lookup` closed the audit-only gap with bare keyword conjunction, and its first run
also exposed the residual failure mode: `"gamma lorentz-factor" → 0` even though the material
exists, because conjunction cannot express synonyms.  This module supplies the SQL-shaped clause
layer:

  `#zil_query subject ~ "cauchy|development einstein", relation = "formalizes" limit 20`
  `#zil_query relation = "experimental_bound", subject ~ "eotvos|free-fall|microscope"`
  `#zil_query decl ~ "Tetrad", subject !~ "klein-gordon"`

**Clauses** (comma-separated, combined with AND):

* `subject ~ "kw1 kw2"` — the attached token contains **all** space-separated keywords;
  each keyword may carry `|`-alternation (`cauchy|development` = either), which is the OR that
  conjunction lacked — synonym search is one query instead of several misses.
* `subject !~ "kw1 kw2"` — the token contains **none** of the keywords.
* `decl ~ "…"` / `decl !~ "…"` — same matching on the declaration name (namespace filtering).
* `relation = "formalizes"` — exact relation filter (`formalizes`, `supported_by`, `requires`,
  `caveat`, `epistemic_status`, `experimental_bound`, `derives`, …).
* `status = "conditional-model"` — sugar for the epistemic-status edge: matches declarations whose
  `epistemic_status` subject contains the keywords (alternation works, so
  `status = "ansatz|risky"` finds every honestly-conditional claim in one query).
* `limit n` — output cap (default 40).

All matching is case-insensitive substring; pure string work over `declarationAttachments`, so no
`maxHeartbeats` concerns.  Import alongside `Physlib` for whole-repository retrieval.

The design rule carried over from the retrieval-gap postmortem: **queries search the graph's
vocabulary, not yours** — alternation exists precisely so that a vocabulary guess can be widened in
place instead of silently returning zero and being read as absence.
-/

@[expose] public section

namespace Physlib.Meta.ZilQuery

open Lean Elab Command Zil.Datalog

/-- One keyword with `|`-alternation: matches if any alternative is a substring (inputs already
lowercased). -/
meta def kwMatches (tokLower : String) (kw : String) : Bool :=
  (kw.splitOn "|").any fun k => k ≠ "" && decide (1 < (tokLower.splitOn k).length)

/-- Every space-separated keyword matches (AND over keywords, OR inside each via `|`). -/
meta def allKwMatch (tok : String) (kws : String) : Bool :=
  let l := tok.toLower
  ((kws.splitOn " ").filter (fun k => k ≠ "")).all fun k => kwMatches l k.toLower

/-- Some space-separated keyword matches — used by the negative clause. -/
meta def anyKwMatch (tok : String) (kws : String) : Bool :=
  let l := tok.toLower
  ((kws.splitOn " ").filter (fun k => k ≠ "")).any fun k => kwMatches l k.toLower

/-- A parsed query clause. -/
meta inductive Clause
  | subjHas (kws : String)
  | subjNot (kws : String)
  | declHas (kws : String)
  | declNot (kws : String)
  | relEq (r : String)
  | statusHas (kws : String)

/-- Clause satisfaction against one graph edge. -/
meta def Clause.sat (declStr rel subj : String) : Clause → Bool
  | .subjHas kws => allKwMatch subj kws
  | .subjNot kws => !anyKwMatch subj kws
  | .declHas kws => allKwMatch declStr kws
  | .declNot kws => !anyKwMatch declStr kws
  | .relEq r => rel == r
  | .statusHas kws => rel == "epistemic_status" && allKwMatch subj kws

declare_syntax_cat zilClause

syntax "subject" " ~ " str : zilClause
syntax "subject" " !~ " str : zilClause
syntax "decl" " ~ " str : zilClause
syntax "decl" " !~ " str : zilClause
syntax "relation" " = " str : zilClause
syntax "status" " = " str : zilClause

syntax (name := zilQueryCmd) "#zil_query " zilClause,+ : command
syntax (name := zilQueryLimitCmd) "#zil_query " zilClause,+ " limit " num : command

/-- Parse one clause. -/
meta def elabClause (stx : TSyntax `zilClause) : CommandElabM Clause := do
  match stx with
  | `(zilClause| subject ~ $s:str) => return .subjHas s.getString
  | `(zilClause| subject !~ $s:str) => return .subjNot s.getString
  | `(zilClause| decl ~ $s:str) => return .declHas s.getString
  | `(zilClause| decl !~ $s:str) => return .declNot s.getString
  | `(zilClause| relation = $s:str) => return .relEq s.getString
  | `(zilClause| status = $s:str) => return .statusHas s.getString
  | _ => throwUnsupportedSyntax

/-- Run the query: scan every attachment, keep edges satisfying all clauses. -/
meta def runQuery (clauses : List Clause) (lim : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let mut hits : Nat := 0
  let mut shown : Nat := 0
  let mut out : String := ""
  for att in (declarationAttachments env).toList do
    match att.atom.subject with
    | .symbol subj =>
      let declStr := att.declaration.toString
      if clauses.all (Clause.sat declStr att.atom.relation subj) then
        hits := hits + 1
        if shown < lim then
          out := out ++ s!"  · {att.declaration}\n      [{att.atom.relation}] {subj}\n"
          shown := shown + 1
    | _ => pure ()
  logInfo m!"zil query: {hits} matching edges (showing {shown}, limit {lim})\n{out}"

elab_rules : command
  | `(#zil_query $cs:zilClause,*) => do
    let clauses ← cs.getElems.toList.mapM elabClause
    runQuery clauses 40
  | `(#zil_query $cs:zilClause,* limit $n:num) => do
    let clauses ← cs.getElems.toList.mapM elabClause
    runQuery clauses n.getNat

end Physlib.Meta.ZilQuery

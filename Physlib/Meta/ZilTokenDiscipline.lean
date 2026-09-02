/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.ZilConceptLookup

meta import Zil.Datalog.Attach

/-!
# `#zil_token_*` — string discipline for graph tokens

Graph subjects are raw strings, and raw strings fail silently: a typo mints a fresh island
token, an undeclared prefix smuggles in vocabulary (the `axiom:` incident), a `lean:`
reference rots when its declaration is renamed, and the same concept can live under two
spellings with nothing to notice (`assumption:displacement-entropy-ansatz` vs
`assumption:verlinde-displacement-entropy-ansatz` — found by hand, days late).  This module
makes the string layer inspectable and enforceable:

* `#zil_token_report` — prefix histogram over every attached symbol subject, tokens with no
  prefix at all, and same-body-different-prefix pairs (one concept, two vocabularies).
* `#zil_assert_token_prefixes "claim", "assumption", …` — **gate**: on the relations where
  a prefix is load-bearing (`formalizes`, `derives`, `supported_by`), every token's prefix
  is in the given whitelist.  Coining a new prefix fails the build until the whitelist is
  edited deliberately.
* `#zil_assert_lean_refs [allow n]` — **gate**: every `lean:<name>` token resolves to a
  constant in the current environment; `allow n` is a ratchet bound for pre-existing rot
  (first whole-graph run: 107 of 1597) — the build fails if rot exceeds the bound, and the
  bound is only ever lowered as references are repaired.
* `#zil_token_near_duplicates "prefix" [limit n]` — triage report: token pairs in one
  prefix class where one body contains the other (the spelling-drift shape of the
  ansatz-token hole).  Judgment stays with the reader; nothing is auto-merged.

Vocabulary note: `postulate:` and `input:` tokens appear only under the
`standard_physics_postulates` relation — they attribute inputs to *standard physics*
(citation labels, like `paper:`), never to this repository, which imposes no axioms.

Import alongside `Physlib` for whole-graph coverage; pure string scans over
`declarationAttachments`, no `whnf`, no `maxHeartbeats`.
-/

@[expose] public section

namespace Physlib.Meta.ZilTokenDiscipline

open Lean Elab Command Zil.Datalog

/-- The prefix of a token: the segment before the first `:`, if any. -/
meta def tokenPrefix (tok : String) : Option String :=
  match tok.splitOn ":" with
  | p :: _ :: _ => some p
  | _ => none

/-- The body of a token: everything after the first `:`. -/
meta def tokenBody (tok : String) : String :=
  match tok.splitOn ":" with
  | _ :: rest => String.intercalate ":" rest
  | [] => tok

/-- Relations whose subjects are prefixed tokens.  Contract relations (`promises`,
`forbids_substitutes`, …) carry prose sentences, not tokens — they are outside the
discipline; the report's relation histogram keeps that boundary visible. -/
meta def tokenRelations : List String :=
  ["formalizes", "derives", "requires", "caveat", "supported_by", "epistemic_status",
   "standard_physics_postulates", "experimental_bound", "prediction_class"]

/-- All symbol-subject edges in the environment, with declaration and relation. -/
meta def allEdges (env : Environment) : List (Name × String × String) :=
  (declarationAttachments env).toList.filterMap fun a =>
    match a.atom.subject with
    | .symbol s => some (a.declaration, a.atom.relation, s)
    | _ => none

/-- Tokens on token-bearing relations only, with their carrying declarations. -/
meta def allTokens (env : Environment) : List (Name × String) :=
  (allEdges env).filterMap fun (d, r, s) =>
    if tokenRelations.contains r then some (d, s) else none

/-- Relations where a prefix is load-bearing: `formalizes`/`derives` decide establishment,
`supported_by` decides provenance kind.  `caveat`/`requires` tolerate prose sentences and
`epistemic_status` values are prefixless by design — the prefix gate does not reach them. -/
meta def strictTokenRelations : List String := ["formalizes", "derives", "supported_by"]

meta def runTokenReport : CommandElabM Unit := do
  let env ← getEnv
  let edges := allEdges env
  let mut relHist : List (String × Nat) := []
  for (_, r, _) in edges do
    match relHist.find? (·.1 == r) with
    | some (_, n) => relHist := (r, n + 1) :: relHist.filter (·.1 != r)
    | none => relHist := (r, 1) :: relHist
  let toks := allTokens env
  let distinct := (toks.map (·.2)).eraseDups
  let mut hist : List (String × Nat) := []
  let mut prefixless : List String := []
  for t in distinct do
    match tokenPrefix t with
    | some p =>
      match hist.find? (·.1 == p) with
      | some (_, n) => hist := (p, n + 1) :: hist.filter (·.1 != p)
      | none => hist := (p, 1) :: hist
    | none => prefixless := t :: prefixless
  let sorted := hist.toArray.qsort (fun a b => a.2 > b.2)
  let relSorted := relHist.toArray.qsort (fun a b => a.2 > b.2)
  let mut out := s!"zil token report: {edges.length} symbol edges over {relSorted.size} \
    relations; {distinct.length} distinct tokens on token-bearing relations, \
    {sorted.size} prefixes\n  relations: "
  for (r, n) in relSorted do
    let mark := if tokenRelations.contains r then "" else "*"
    out := out ++ s!"{r}{mark}:{n} "
  out := out ++ "  (* = outside token discipline)\n"
  for (p, n) in sorted do
    out := out ++ s!"  {n}\t{p}:\n"
  unless prefixless.isEmpty do
    out := out ++ s!"  PREFIXLESS ({prefixless.length}): {prefixless.take 10}\n"
  let mut crossPrefix : List (String × String) := []
  for t in distinct do
    if let some p := tokenPrefix t then
      let b := tokenBody t
      if b.length ≥ 8 then
        for t' in distinct do
          if let some p' := tokenPrefix t' then
            if p < p' && tokenBody t' == b then
              crossPrefix := (t, t') :: crossPrefix
  unless crossPrefix.isEmpty do
    out := out ++ s!"  SAME BODY, TWO PREFIXES ({crossPrefix.length}):\n"
    for (a, b) in crossPrefix.take 10 do
      out := out ++ s!"    · {a}  ↔  {b}\n"
  logInfo out

meta def runAssertPrefixes (allowed : List String) : CommandElabM Unit := do
  let edges := (allEdges (← getEnv)).filter fun (_, r, _) => strictTokenRelations.contains r
  let mut bad : List (Name × String) := []
  for (d, _, t) in edges do
    match tokenPrefix t with
    | some p => unless allowed.contains p do bad := (d, t) :: bad
    | none => bad := (d, t) :: bad
  unless bad.isEmpty do
    let shown := (bad.map fun (d, t) => s!"  · {d}: {t}").take 20
    throwError "zil_assert_token_prefixes FAILED: {bad.length} token(s) on \
      formalizes/derives/supported_by outside the whitelist — a new prefix is a vocabulary \
      decision, edit the whitelist deliberately or retag:\n{String.intercalate "\n" shown}"
  logInfo m!"zil_assert_token_prefixes: {edges.length} strict-relation tokens within \
    {allowed.length} whitelisted prefixes"

meta def runAssertLeanRefs (allow : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let mut bad : List (Name × String) := []
  let mut total : Nat := 0
  for (d, t) in allTokens env do
    if (tokenPrefix t) == some "lean" then
      total := total + 1
      let ref := (tokenBody t).toName
      unless env.contains ref do bad := (d, t) :: bad
  if bad.length > allow then
    let shown := (bad.map fun (d, t) => s!"  · {d}: {t}").take 20
    throwError "zil_assert_lean_refs FAILED: {bad.length} of {total} lean: reference(s) \
      name no constant in the environment, exceeding the ratchet bound {allow} \
      (renamed or deleted — update the tokens, never raise the bound):\n\
      {String.intercalate "\n" shown}"
  if bad.isEmpty then
    logInfo m!"zil_assert_lean_refs: {total} lean: reference(s) all resolve"
  else
    logInfo m!"zil_assert_lean_refs: {bad.length} of {total} rotten ≤ ratchet {allow} — \
      lower the bound as references are repaired"

meta def runLeanRefsReport (lim : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let mut bad : List (Name × String) := []
  let mut total : Nat := 0
  for (d, t) in allTokens env do
    if (tokenPrefix t) == some "lean" then
      total := total + 1
      let ref := (tokenBody t).toName
      unless env.contains ref do bad := (d, t) :: bad
  let mut out := s!"zil lean refs report: {bad.length} of {total} unresolved\n"
  for (d, t) in bad.take lim do
    out := out ++ s!"  ROTTEN\t{d}\t{t}\n"
  logInfo out

meta def runNearDuplicates (pfx : String) (lim : Nat) : CommandElabM Unit := do
  let toks := ((allTokens (← getEnv)).map (·.2)).eraseDups.filter
    (fun t => tokenPrefix t == some pfx)
  let bodies := toks.map tokenBody
  let mut pairs : List (String × String) := []
  for a in bodies do
    if a.length ≥ 8 then
      for b in bodies do
        if a.length < b.length && (b.splitOn a).length > 1 then
          pairs := (a, b) :: pairs
  let mut out := s!"zil near-duplicates in `{pfx}:` ({toks.length} tokens): \
    {pairs.length} containment pair(s)\n"
  for (a, b) in pairs.take lim do
    out := out ++ s!"  · {pfx}:{a}\n    ⊂ {pfx}:{b}\n"
  logInfo out

syntax (name := zilTokenReportCmd) "#zil_token_report" : command
syntax (name := zilAssertPrefixesCmd) "#zil_assert_token_prefixes " str,+ : command
syntax (name := zilAssertLeanRefsCmd) "#zil_assert_lean_refs" : command
syntax (name := zilAssertLeanRefsAllowCmd) "#zil_assert_lean_refs " "allow " num : command
syntax (name := zilLeanRefsReportCmd) "#zil_lean_refs_report" " limit " num : command
syntax (name := zilNearDupCmd) "#zil_token_near_duplicates " str : command
syntax (name := zilNearDupLimitCmd) "#zil_token_near_duplicates " str " limit " num : command

elab_rules : command
  | `(#zil_token_report) => runTokenReport
  | `(#zil_assert_token_prefixes $ps:str,*) =>
    runAssertPrefixes (ps.getElems.toList.map (·.getString))
  | `(#zil_assert_lean_refs) => runAssertLeanRefs 0
  | `(#zil_assert_lean_refs allow $n:num) => runAssertLeanRefs n.getNat
  | `(#zil_lean_refs_report limit $n:num) => runLeanRefsReport n.getNat
  | `(#zil_token_near_duplicates $p:str) => runNearDuplicates p.getString 20
  | `(#zil_token_near_duplicates $p:str limit $n:num) => runNearDuplicates p.getString n.getNat

end Physlib.Meta.ZilTokenDiscipline

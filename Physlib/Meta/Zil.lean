/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic.Lemma
/- ZIL-BEGIN -/
public meta import Zil.Generated.DependencyAvailability
/- ZIL-END -/

/-!
# ZIL integration

This module checks that Physlib can consume an immutable native-ZIL program and use its certified
evaluator without consulting external services during elaboration.
-/

@[expose] public section

/- ZIL-BEGIN -/
open Zil
/- ZIL-END -/

namespace Physlib

/- ZIL-BEGIN -/
/-
@zil target=self
self#formalizes@claim:physlib.dependencyAvailability.
self#requires@assumption:dependencySnapshot.
self#requires_check@check:lean_compile.
@endzil
-/
/-- The frozen dependency-availability rule derives the expected service dependency. -/
@[zil_claim physlib.dependencyAvailability, zil_requires dependencySnapshot]
lemma zilDependencyAvailability :
    Holds Zil.Generated.DependencyAvailability.program {
      object := .symbol "app:svc1"
      relation := "dependency_available"
      subject := .symbol "service:db1"
    } := by
  zil_solve

#zil_validate_embedded zilDependencyAvailability where
  no_sorry, claim_linked, requirement_linked

/-- A stable ZIL claim name resolves back to the linked kernel theorem. -/
lemma zilDependencyAvailabilityViaClaim :
    Holds Zil.Generated.DependencyAvailability.program {
      object := .symbol "app:svc1"
      relation := "dependency_available"
      subject := .symbol "service:db1"
    } := by
  zil_apply physlib.dependencyAvailability

/- ZIL-END -/
end Physlib

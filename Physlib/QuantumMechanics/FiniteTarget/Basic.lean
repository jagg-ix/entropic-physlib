/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget

/-!
# Re-export shim

The `FiniteTarget` structure and its time evolution now live in
`Physlib.QuantumMechanics.FiniteTarget` (upstream's version, a strict superset of the
copy this module used to hold). Re-export so `FiniteTarget.Basic` importers keep working.
-/

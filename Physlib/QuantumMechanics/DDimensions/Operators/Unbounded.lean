/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded

/-!
# Unbounded operators (re-export)

The unbounded-operator development now lives at
`Physlib.QuantumMechanics.Operators.Unbounded` — upstream's generalisation of the copy
this module used to hold (96 shared declarations; upstream adds 15, and the three
declarations only this copy had — `LinearPMap.IsBounded`, `isBounded_def`, a
`DistribMulAction` instance — have no consumers in the fork tree). This module survives
as a re-export so the fork's `DDimensions.Operators.*` importers keep working.
-/

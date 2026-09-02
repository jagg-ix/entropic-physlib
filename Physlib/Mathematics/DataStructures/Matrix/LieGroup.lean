/-
Copyright (c) 2026 Physlib Contributors.
Released under Apache 2.0 license.
Authors: Physlib Contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix Lie Group Helpers

This module records small reusable interfaces for matrix Lie groups over `C`.

## Main definitions

* `MatrixLieGroup.glChartedSpace` is the standard charted-space structure on
  `GL(n, C)` inherited from the open embedding of units in the matrix normed
  algebra.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, Springer,
  Chapter 1.
-/

@[expose] public noncomputable section

open scoped Matrix MatrixGroups Matrix.Norms.Operator Manifold

namespace MatrixLieGroup

attribute [local instance] Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedRing

/-! ## A. General Linear Groups -/

/-- The standard charted-space structure on `GL(n, C)` inherited from the units
of the matrix normed algebra. -/
@[reducible]
def glChartedSpace (n : ℕ) : ChartedSpace (Matrix (Fin n) (Fin n) ℂ) (GL (Fin n) ℂ) :=
  Units.instChartedSpace

end MatrixLieGroup

end

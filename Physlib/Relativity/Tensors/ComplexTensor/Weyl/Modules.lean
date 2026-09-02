/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded
public import Physlib.Relativity.Fermions.Weyl.Duals
public import Physlib.Relativity.Fermions.Weyl.Metric
public import Physlib.Relativity.Fermions.Weyl.Two
public import Physlib.Relativity.Fermions.Weyl.Unit
public import Physlib.Relativity.Fermions.Weyl.Contraction

/-!
# Re-export shim

The Weyl-fermion development now lives under `Physlib.Relativity.Fermions.Weyl`
(upstream's relocation; 121 of this tree's declarations are the same names, and the
remainder had no consumers outside the tree). This module survives as a re-export so
the old `ComplexTensor.Weyl` module paths keep resolving.
-/

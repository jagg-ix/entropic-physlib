/-
Copyright (c) 2026 Jorge Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge Garcia
-/
module

public import Physlib.Gravity.Canonical.Basic

/-!
# Constraint algebra for canonical systems

This module records the closure conditions expected from scalar and momentum
constraints in canonical gravity.

The detailed distributional structure functions are not constructed here. They
are represented as explicit closure propositions.
-/

@[expose] public section

namespace Physlib.Gravity.Canonical

/--
Abstract Dirac / hypersurface-deformation algebra package.

The intended schematic meaning is:

* `{H_i, H_j}` closes on momentum constraints;
* `{H_perp, H_i}` closes on scalar constraints;
* `{H_perp, H_perp}` closes on momentum constraints, with structure functions.
-/
structure DiracAlgebraPackage (C : CanonicalSystem) where
  /-- Momentum-momentum brackets close on momentum constraints. -/
  momentum_momentum_closure : Prop
  /-- Scalar-momentum brackets close on scalar constraints. -/
  scalar_momentum_closure : Prop
  /-- Scalar-scalar brackets close on momentum constraints with structure functions. -/
  scalar_scalar_closure : Prop

/-- The canonical system satisfies the packaged Dirac-algebra closure laws. -/
def SatisfiesDiracAlgebra
    (C : CanonicalSystem)
    (A : DiracAlgebraPackage C) : Prop :=
  A.momentum_momentum_closure ∧
  A.scalar_momentum_closure ∧
  A.scalar_scalar_closure

theorem satisfiesDiracAlgebra_intro
    (C : CanonicalSystem)
    (A : DiracAlgebraPackage C)
    (hDD : A.momentum_momentum_closure)
    (hHD : A.scalar_momentum_closure)
    (hHH : A.scalar_scalar_closure) :
    SatisfiesDiracAlgebra C A :=
  ⟨hDD, hHD, hHH⟩

theorem momentum_momentum_closure_of_satisfiesDiracAlgebra
    (C : CanonicalSystem)
    (A : DiracAlgebraPackage C)
    (h : SatisfiesDiracAlgebra C A) :
    A.momentum_momentum_closure :=
  h.1

theorem scalar_momentum_closure_of_satisfiesDiracAlgebra
    (C : CanonicalSystem)
    (A : DiracAlgebraPackage C)
    (h : SatisfiesDiracAlgebra C A) :
    A.scalar_momentum_closure :=
  h.2.1

theorem scalar_scalar_closure_of_satisfiesDiracAlgebra
    (C : CanonicalSystem) (A : DiracAlgebraPackage C) (h : SatisfiesDiracAlgebra C A) :
    A.scalar_scalar_closure :=
  h.2.2

end Physlib.Gravity.Canonical

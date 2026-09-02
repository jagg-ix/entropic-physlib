/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.BoundaryLevelShift

/-!
# One-loop exact quantization of Chern-Simons theory

This module formalizes the algebraic spine of Owen Gwilliam and Brian Williams,
*A one-loop exact quantization of Chern-Simons theory*, arXiv:1910.05230v2
(6 May 2020), from the local PDF
`one-loop-exact-chern-simons-1910.05230v2.pdf`.

The paper's analytic work is the construction of a holomorphic gauge in which
mixed BF theory and its chiral deformations have finite one-loop exact
quantizations.  This file records the checked consequences that the rest of the
repo can use:

* the mixed BF action plus the chiral Chern-Simons deformation;
* the Euler-Lagrange equation in which the `∂α` term converts the mixed BF
  equation to the flat Chern-Simons equation;
* the theorem-level carriers for Theorem 4.1, Theorem 5.1, Corollary 5.2, and
  Theorem 6.1;
* the concrete algebraic fact that the one-loop correction turns mixed BF into
  Chern-Simons with no higher-loop residue;
* the paper's graph-shape restriction: tree graphs and one-loop wheels only;
* the boundary level shift by the adjoint trace term;
* the deformation-complex, holomorphic-gauge, heat-kernel, BV/QME, anomaly,
  boundary-condition, and CS/WZW factorization-algebra claims from the
  remaining sections of the paper;
* links to the existing finite local CSW action, contour-deformation layer,
  modular/Wilson invariant layer, Levi-Civita tetrad invariants, and the
  Gel'fand-Yaglom one-loop prefactor, plus the repo's Euclidean heat-kernel
  propagator.


-/

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WittenAnalyticContinuationChernSimons.TrefoilKauffmanRepoLinks

/-!
# Analytic continuation of Chern-Simons theory: Lefschetz cycles and the trefoil

This module formalizes the Lean-checkable core of E. Witten,
*Analytic Continuation Of Chern-Simons Theory* (arXiv:1001.2933v4), with special emphasis on the
trefoil-knot analysis of Section 5.2.

The full analytic continuation of the infinite-dimensional Chern-Simons path integral is not asserted here.
Instead, the file records the finite Picard-Lefschetz bookkeeping that Witten uses:

* a cycle is an integer coefficient function on Lefschetz thimbles;
* crossing a Stokes curve adds an integer multiple of a thimble;
* for the trefoil, the relevant nonabelian thimbles are indexed by
  `y = ±(1/6 + p)`, `p : Z`;
* along the positive real `gamma = n/k` axis, the first jumps are exactly
  `J_ab`, `J_ab + J_1/6`, `J_ab + J_1/6 - J_5/6`,
  `J_ab + J_1/6 - J_5/6 + J_7/6`, and
  `J_ab + J_1/6 - J_5/6 + J_7/6 - J_11/6`, matching Witten Eq. (5.31);
* the nonabelian semiclassical exponent is the explicit quadratic carrier
  `-3*pi*i*n*gamma^-1*(gamma-y)^2` from Witten Eq. (5.30).

The last section links this analytic-continuation layer back to the repository's existing trefoil and CSW
infrastructure: the trefoil braid word, Sawin's Kauffman bracket computation, and Wilson-loop braiding as the
Verlinde `S`-matrix.

## References

* E. Witten, *Analytic Continuation Of Chern-Simons Theory*, arXiv:1001.2933v4, especially
  Sections 2-3 and 5.2, Eqs. (5.28)-(5.33).
  Local source: `Analytic Continuation Of Chern-Simons Theory1001.2933v4.pdf`.
* Repo carriers:
  `ChernSimons.WittenComplexChernSimonsQuantization`, `ChernSimons.WittenJonesPolynomialChernSimons`,
  `ChernSimons.BraidRelationTrefoilTorus`, `QuantumGroupSkein.TrefoilBracketTemperleyLieb`,
  `ChernSimons.WilsonLoopBraidingRibbon`.


-/

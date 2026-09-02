/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas.Recurrence

/-!
# ABJM Wilson loops and the Fermi-gas Chern-Simons representation

This module formalizes the Lean-checkable algebraic surface of Boldis-Korchemsky-Testa,
*Wilson loops in ABJM theory reloaded*, arXiv:2512.02119v3.

The paper's full Tracy-Widom/Fredholm analysis is analytic input.  The checked layer here records:

* ABJM parameters `N, k`, opposite Chern-Simons levels `k, -k`, and the Fermi-gas Planck constant
  `hbar = 2πk`;
* the Fermi-gas kernel `ρ(x,y)`, its coordinate/momentum kernel factorization, the `N = 1` closed
  form, and the pole/convergence condition `k > 2n`;
* the normalized `1/6` Wilson loop `W_n / W_0` and the partition relation `Z = W_0 / N`;
* the `1/2` BPS Wilson loop as the signed linear combination of the two opposite-level `1/6` loops;
* fugacity `z = exp μ`, grand-canonical normalization `W_n(z,k) = raw_n(z,k) / Xi(z,k)`,
  coefficient extraction, and the `W₀ = z∂z log Ξ` relation as explicit carriers;
* abstract carriers for the Fredholm determinant/resolvent representation, Tracy-Widom `ψ` system,
  parity/shift identities, phase quantization, and potential recurrences;
* explicit coefficient functions `A₁,B₁,C₁,A₂,B₂,C₂`, the `k = 6` polynomial for `A₁`, and the
  weak-coupling and large-`µ` leading Wilson-loop formulas;
* the algebraic cancellation from the `1/6` decomposition (5.16) to the `1/2` result (5.19), the
  `A₂(A₁,F)` relation (5.23), and the large-`µ` constant term (6.13);
* bridges back to the existing Witten/Jones, rigorous complex Feynman-Kac, CSW theta, and Kálnay
  Bose-bilinear fermion-field infrastructure.

## References

* B. Boldis, G. P. Korchemsky, A. Testa, *Wilson loops in ABJM theory reloaded*,
  arXiv:2512.02119v3. Local source:
  `Wilson loops in ABJM theory reloaded-2512.02119v3.pdf`.
* Repo carriers: `ChernSimons.WittenJonesPolynomialChernSimons`, `ChernSimons.ThetaModular`,
  `QFT.PathIntegral.RigorousComplexFK`, `BoseFermiOperatorAlgebra.Basic`.


-/

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.Classical
public import Physlib.QFT.ScalarGreenFunctions.ComplexField
public import Physlib.QFT.ScalarGreenFunctions.Continuum
public import Physlib.QFT.ScalarGreenFunctions.ContinuumDysonSchwinger
public import Physlib.QFT.ScalarGreenFunctions.ContinuumVacuum
public import Physlib.QFT.ScalarGreenFunctions.DysonWick
public import Physlib.QFT.ScalarGreenFunctions.EntropicTime
public import Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchange
public import Physlib.QFT.ScalarGreenFunctions.PropagatorHierarchy
public import Physlib.QFT.ScalarGreenFunctions.SourceJet
public import Physlib.QFT.ScalarGreenFunctions.TraceLog
public import Physlib.QFT.ScalarGreenFunctions.VacuumCharacterization

/-!
# Scalar Green functions and perturbative solutions

Aggregate import for the formalization of R. J. Rivers, *Path Integral Methods
in Quantum Field Theory*, Chapter 1, "Scalar Green functions and their
perturbative solutions".

The imported modules cover:

* classical scalar potentials and finite functional derivatives;
* measure-theoretic scalar and charged Green functions;
* formal source jets and coefficient extraction;
* quartic Dyson--Schwinger equations and contact terms;
* exact Dyson--Wick interaction-operator truncations;
* finite and continuum propagator-form hierarchies;
* continuum pointwise multipliers, `L²` kernels, and Dirac contacts;
* distribution-valued continuum Dyson--Schwinger equations;
* unique formal perturbative recursion without a convergence assumption;
* free real and complex Gaussian generating functionals;
* external-field resolvents, determinant factors, and trace-log identities;
* finite- and continuum-mode Gaussian Schrödinger vacua;
* complex-action and entropic-time weighting, including the theorem that a
  global imaginary-action offset cancels from normalized Green functions.
* Glenn's two-process photon-exchange convolution: linear QME response versus
  the interrupted fourth-vacuum-order nonlinear response, now linked to the
  explicit weighted Wigner--Dunkl Chapman--Kolmogorov kernel and its four
  reflecting/absorbing Euclidean frequency channels.

Coincident continuum fields are represented distributionally. The modules
reuse Physlib's `Lp`, maximal-domain multiplication-operator, Schwartz,
distribution, path-integral, and Wick-contraction APIs rather than introducing
parallel foundations.
-/

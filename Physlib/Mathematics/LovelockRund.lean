/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.CanonicalStressEnergy
public import Physlib.Mathematics.LovelockRund.ComplexActionVariational
public import Physlib.Mathematics.LovelockRund.ContinuumVariational
public import Physlib.Mathematics.LovelockRund.CurvatureContractions
public import Physlib.Mathematics.LovelockRund.CurvatureForms
public import Physlib.Mathematics.LovelockRund.DifferentialForms
public import Physlib.Mathematics.LovelockRund.HamiltonJacobi
public import Physlib.Mathematics.LovelockRund.HigherOrderVariation
public import Physlib.Mathematics.LovelockRund.LieDerivative
public import Physlib.Mathematics.LovelockRund.MultiNoether
public import Physlib.Mathematics.LovelockRund.NormalCoordinates
public import Physlib.Mathematics.LovelockRund.PoincareStokes
public import Physlib.Mathematics.LovelockRund.PointwiseOperators
public import Physlib.Mathematics.LovelockRund.RiemannianVariational
public import Physlib.Mathematics.LovelockRund.SubmanifoldGeometry
public import Physlib.Mathematics.LovelockRund.TensorFields

/-!
# Lovelock--Rund tensors, forms, and variational principles

Aggregate import for the formalization of the most reusable structures from
David Lovelock and Hanno Rund, *Tensors, Differential Forms, and Variational
Principles*.

The formalized surface includes:

* arbitrary-index pointwise tensor fields, infinite contractions, Ricci and
  scalar-curvature contractions;
* vector and covector covariant derivatives with finite compatibility;
* differential forms on arbitrary normed, possibly infinite-dimensional,
  model spaces;
* `d² = 0`, exact-implies-closed, pullback naturality, and vector-field
  evaluation of the exterior derivative;
* scalar, vector, and Cartan Lie derivatives;
* the Poincaré lemma for closed 1-forms on convex sets;
* one-dimensional Stokes and the Bochner divergence theorem on boxes;
* generic vector-valued `L²` continuum fields;
* maximal-domain pointwise multiplication and Euler--Lagrange operators;
* continuum weak variations and the fundamental lemma;
* first-order and higher-order Euler--Lagrange residuals;
* single- and multi-parameter Noether current identities;
* complex Euler--Lagrange and Hamilton--Jacobi residuals with entropic-time
  rates;
* curvature 2-forms, Bianchi identities, and Einstein-tensor components;
* continuum metric energy and arbitrary-index geodesic equations;
* normal-coordinate consequences;
* Gauss--Codazzi hypersurface geometry;
* bridges to Physlib's existing Riemannian and contracted-Bianchi APIs.

No finite-dimensional restriction is imposed on the differential-form model
space, field-value space, tensor index type, geodesic coordinate index,
symmetry-parameter family, or hypersurface tangent-index type unless a theorem
explicitly specializes to an existing finite-dimensional manifold or box
integral carrier.
-/

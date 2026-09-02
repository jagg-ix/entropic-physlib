/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.Asymptotics
public import Physlib.QuantumMechanics.PeriodicSchrodinger.Basic
public import Physlib.QuantumMechanics.PeriodicSchrodinger.BindingFormula
public import Physlib.QuantumMechanics.PeriodicSchrodinger.BlochApproximation
public import Physlib.QuantumMechanics.PeriodicSchrodinger.Continuum
public import Physlib.QuantumMechanics.PeriodicSchrodinger.DirectionalPotential
public import Physlib.QuantumMechanics.PeriodicSchrodinger.EntropicSelection
public import Physlib.QuantumMechanics.PeriodicSchrodinger.Isoenergetic
public import Physlib.QuantumMechanics.PeriodicSchrodinger.ResonanceMatrix
public import Physlib.QuantumMechanics.PeriodicSchrodinger.Simplicity

/-!
# Multidimensional periodic Schrödinger perturbation theory

Aggregate import for the formalization of the algebraic, geometric, continuum,
and spectral-selection core of O. A. Veliev's *Perturbation Theory for the
Multidimensional Schrödinger Operator with a Periodic Potential*.

The imported modules provide:

* free Bloch energies and diffraction hyperplanes;
* resonance and nonresonance domains;
* arbitrary reciprocal-mode lattices;
* finite Fourier convolution and exact binding equations;
* denominator-controlled coefficient recovery;
* finite perturbation iteration with an exact remainder;
* finite Hermitian resonance matrices;
* known-part separation and simple-label uniqueness;
* directional potentials and directional-reference binding formulas;
* finite and summable infinite Bloch coefficient localization;
* periodic pointwise potentials and maximal-domain continuum `L²` operators;
* arbitrary-order recursive known parts and explicit approximation interfaces;
* isoenergetic crossing and spectral-tail consequences;
* complex-action and entropic-time penalties for spectral mismatch.

The full Sobolev/lattice-counting estimates proving Veliev's arbitrary-order
error rates and asymptotically full-measure simple sets remain explicit theorem
inputs. They are not replaced by axioms or unqualified big-O notation.
-/

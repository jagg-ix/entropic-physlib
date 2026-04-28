/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import Physlib.Mathematics.VariationalCalculus.HasVarAdjDeriv
/-!

# Distributional Electromagnetic Potential

## i. Overview

In electromagnetism, charge and current distributions are often idealised as objects that
are not smooth functions: point particles, infinitely thin wires, charged surfaces, and so on.
A point charge, for example, is conventionally written as `ρ(x) = q δ³(x - x₀)`, where `δ³`
is the Dirac delta. These idealisations are not functions in the usual sense, and cannot be
described within a formulation of electromagnetism that only allows smooth functions, because
they are incompatible with the assumption that a field has a well-defined value at every
point. The same issue arises for the fields they source: the electric field of a point charge
diverges at the location of the charge, and the magnetic field of an infinitely thin wire
diverges along the wire.

The resolution is to give up asking for the value of a field
at a single point and instead ask for its value averaged over a region of space, weighted by
a test function `φ`. Physically, one can think of `φ` as the response profile of a measuring
device: a real device cannot probe a single mathematical point, but only a small region with
some smooth sensitivity profile. The idealised pointwise value is then replaced by the
weighted average `∫ f(x) φ(x) dx`, and a "field" is identified with the rule `φ ↦ ∫ f φ dx`
that sends each test function to a number.

When the test functions are taken to be `Schwartz maps` (smooth functions which, together
with all their derivatives, decay faster than any polynomial at infinity), the resulting
mathematical object is called a tempered distribution. Fields and charge or current
distributions are then specified by their action on test functions rather than by their
pointwise values. Ordinary smooth functions `f` still fit into this framework via the rule
`φ ↦ ∫ f φ dx`, but the framework is strictly larger: it also accommodates point particles,
surface charges, and other singular sources.

For example, if the charge distribution is represented by the tempered distribution `ρ`, then
the charge registered by a device with weighting `φ` is `ρ φ`, or notionally `∫ ρ(x) φ(x) dx`.
For a point charge `q` at the origin this evaluates to `q · φ(0)`: the device "sees" the
charge weighted by the value of its response profile at the location of the charge, exactly as
physical intuition would suggest.

Derivatives still make sense in this framework, but they are defined by integration by parts.
If `f` is a tempered distribution, its derivative `∂f` is the distribution acting on test
functions by `(∂f) φ := - f (∂φ)`. For smooth `f` this reproduces the ordinary derivative
(the boundary terms vanish because Schwartz functions decay rapidly), but it also assigns a
meaningful derivative to objects such as the step function, whose distributional derivative
is the Dirac delta. This is what allows Maxwell's equations to retain their differential form
even when the sources are singular.

Because pointwise values are no longer available, some constructions from classical
electromagnetism cease to be well defined in the distributional setting. The Lagrangian
density `ℒ = - Aᵤ Jᵘ - ¼ Fᵤᵥ Fᵘᵛ` is one such example: it relies on pointwise products of
distributions (such as `A` with `J`, or `F` with itself), and in general the product of two
distributions is not defined. For a point charge, for instance, both `A` and `J` are singular
at the location of the charge, and their product has no distributional meaning.

Other constructions must be reformulated rather than abandoned. The flux of `E` out of a
surface `S`, classically `∫_S E · dA`, is no longer well defined, but one can still speak of
the flux weighted by a test function `φ`, notionally defined as `- ∫ E x · ∇ φ x dx`.
The intuition is that `φ` plays the role of a smoothed-out version of the region `V`
enclosed by `S`: imagine `φ` equal to `1` deep inside `V`, equal to `0` far outside, and
transitioning smoothly across `S` over a thin layer. Its gradient `∇ φ` is then nonzero only
in this transition layer, points inward (from `0` to `1`), and concentrates more sharply on
`S` the thinner the layer is made. By the divergence theorem,
`- ∫ E · ∇ φ dV = ∫ φ (∇ · E) dV`, which for a sharp `φ` is approximately the integral of
`∇ · E` over `V`, i.e. the flux of `E` out of `S`. As `φ` is taken to be a sharper and sharper
approximation of `V`, the weighted flux approaches the classical flux through `S`. The flux
through `S` itself is not directly accessible in the framework, since a perfectly sharp `φ`
(equal to `1` on `V` and `0` outside, with no smooth transition) is not a Schwartz map; but
it can be recovered as a limit of weighted fluxes over progressively sharper test functions.

In this setting, Gauss's law states precisely that the flux with weighting
`φ` equals the charge measured with the same weighting `φ`. Notionally this is
`- ∫ E x · ∇ φ x dx = ∫ ρ x φ x dx`.
In the distributional setting, this 'integral' form of Gauss's law
is exactly equivalent to the differential form `∇ · E = ρ`,
due to the way derivatives are defined by integration by parts.

-/

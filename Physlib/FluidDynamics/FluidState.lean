/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Basic
/-!

# Compatibility carriers for the pre-FluidFlow fluid API

This module preserves the legacy `FluidState` and `FluidInMomentumBalance`
carriers used by the entropic-physlib development branch while reusing the
field types and carrier hierarchy from the current upstream fluid API.

New code should prefer `FluidFlow` for density/velocity data and `CauchyFlow`
for momentum-balance data. The explicit conversion maps below make the legacy
API a migration layer rather than a second independent fluid model.
-/

@[expose] public section

namespace FluidDynamics

/-- Legacy name for a specific body-force field. New Cauchy-flow code uses a
`VectorField` directly as `CauchyFlow.specificBodyForce`. -/
abbrev BodyForce (d : ℕ) := VectorField d

/-- Legacy density/velocity carrier retained for migration compatibility.
New code should use `FluidFlow`. -/
structure FluidState (d : ℕ) where
  /-- The mass density field. -/
  rho : MassDensity d
  /-- The velocity field. -/
  velocity : VelocityField d

namespace FluidState

/-- View a legacy `FluidState` as the current upstream `FluidFlow` carrier. -/
def toFluidFlow {d : ℕ} (fluid : FluidState d) : FluidFlow d where
  rho := fluid.rho
  velocity := fluid.velocity

@[simp] lemma toFluidFlow_rho {d : ℕ} (fluid : FluidState d) :
    fluid.toFluidFlow.rho = fluid.rho := rfl

@[simp] lemma toFluidFlow_velocity {d : ℕ} (fluid : FluidState d) :
    fluid.toFluidFlow.velocity = fluid.velocity := rfl

end FluidState

namespace FluidFlow

/-- View a current upstream `FluidFlow` as the legacy `FluidState` carrier. -/
def toFluidState {d : ℕ} (fluid : FluidFlow d) : FluidState d where
  rho := fluid.rho
  velocity := fluid.velocity

@[simp] lemma toFluidState_rho {d : ℕ} (fluid : FluidFlow d) :
    fluid.toFluidState.rho = fluid.rho := rfl

@[simp] lemma toFluidState_velocity {d : ℕ} (fluid : FluidFlow d) :
    fluid.toFluidState.velocity = fluid.velocity := rfl

@[simp] lemma toFluidState_toFluidFlow {d : ℕ} (fluid : FluidFlow d) :
    fluid.toFluidState.toFluidFlow = fluid := by
  cases fluid
  rfl

end FluidFlow

@[simp] lemma FluidState.toFluidFlow_toFluidState {d : ℕ} (fluid : FluidState d) :
    fluid.toFluidFlow.toFluidState = fluid := by
  cases fluid
  rfl

/-- Legacy momentum-balance carrier retained for migration compatibility.
New code should use `CauchyFlow`, whose body-force projection is
`specificBodyForce`. -/
structure FluidInMomentumBalance (d : ℕ) extends FluidState d where
  /-- The stress tensor field. -/
  stress : StressTensor d
  /-- The body-force field per unit mass. -/
  bodyForce : BodyForce d

namespace FluidInMomentumBalance

/-- View legacy momentum-balance data as a current upstream `CauchyFlow`. -/
def toCauchyFlow {d : ℕ} (data : FluidInMomentumBalance d) : CauchyFlow d where
  toFluidFlow := data.toFluidState.toFluidFlow
  stress := data.stress
  specificBodyForce := data.bodyForce

@[simp] lemma toCauchyFlow_rho {d : ℕ} (data : FluidInMomentumBalance d) :
    data.toCauchyFlow.rho = data.rho := rfl

@[simp] lemma toCauchyFlow_velocity {d : ℕ} (data : FluidInMomentumBalance d) :
    data.toCauchyFlow.velocity = data.velocity := rfl

@[simp] lemma toCauchyFlow_stress {d : ℕ} (data : FluidInMomentumBalance d) :
    data.toCauchyFlow.stress = data.stress := rfl

@[simp] lemma toCauchyFlow_specificBodyForce {d : ℕ} (data : FluidInMomentumBalance d) :
    data.toCauchyFlow.specificBodyForce = data.bodyForce := rfl

end FluidInMomentumBalance

end FluidDynamics

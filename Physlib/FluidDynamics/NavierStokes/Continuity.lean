/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.FluidState
public import Physlib.FluidDynamics.FluidFlow.Continuity
/-!

# Legacy Navier-Stokes continuity compatibility API

The current upstream fluid API places mass conservation in
`FluidDynamics.FluidFlow`.  This module preserves the historical
`FluidDynamics.NavierStokes` names used by the entropic-physlib branch and
forwards them through `FluidState.toFluidFlow`.
-/

@[expose] public section

namespace FluidDynamics
namespace NavierStokes

/-- Legacy spelling of `FluidFlow.ClassicalContinuityEquation`. -/
def ClassicalContinuityEquation (d : ℕ) (fluid : FluidState d) : Prop :=
  FluidFlow.ClassicalContinuityEquation d fluid.toFluidFlow

/-- Legacy spelling of `FluidFlow.continuityResidual`. -/
noncomputable def continuityResidual (d : ℕ) (fluid : FluidState d) : Time → Space d → ℝ :=
  FluidFlow.continuityResidual d fluid.toFluidFlow

/-- Legacy spelling of `FluidFlow.SmoothContinuityEquation`. -/
def SmoothContinuityEquation (d : ℕ) (fluid : FluidState d) : Prop :=
  FluidFlow.SmoothContinuityEquation d fluid.toFluidFlow

/-- Compatibility bridge to the current upstream continuity theorem. -/
lemma SmoothContinuityEquation.toClassical (d : ℕ) (fluid : FluidState d) :
    SmoothContinuityEquation d fluid → ClassicalContinuityEquation d fluid := by
  exact FluidFlow.classicalContinuityEquation_of_smoothContinuityEquation d fluid.toFluidFlow

end NavierStokes
end FluidDynamics

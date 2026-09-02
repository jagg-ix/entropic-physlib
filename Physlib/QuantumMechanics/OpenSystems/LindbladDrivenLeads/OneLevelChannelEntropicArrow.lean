/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannel
public import Physlib.Thermodynamics.QuantumRelativeEntropyArrow
meta import Zil

/-!
# The one-level channel's monotone entropic clock, from the quantum H-theorem

`OneLevelChannelProduction` proved the production rate `σ` strictly positive away from equilibrium and
the occupation deviation `|N(t) - f|` strictly decreasing, but left the genuine monotone *decrease of a
relative entropy* along the trajectory as a follow-up. This file supplies it — not by a bespoke
`HasDerivAt` calculation on the Bernoulli `binaryKL`, but by connecting the channel to the repository's
already-derived discrete quantum H-theorem `QuantumRelativeEntropyArrow.dissipative_orbit_antitone`.

The one-level (generalized-amplitude-damping) channel `oneLevelChannel d` has the diagonal state
`diag(1 - f, f)`, `f = occupation`, as a fixed point (`oneLevelChannel_stationaryState_fixed`); this holds
for every parameter choice because the off-diagonal block is a pure contraction and the diagonal block
already satisfies detailed balance at `f`. Data-processing then makes the entropic proper time
`entropicProperTime (Φⁿ ρ₀) σ_f = D̃₁(Φⁿ ρ₀ ‖ σ_f)` of the running state against the stationary reference
**antitone in `n`** (`oneLevelChannel_entropicProperTime_orbit_antitone`) — the coordinate-free second law
for this channel — with equilibrium a zero-production fixed point
(`oneLevelChannel_stationary_discreteSpohnProduction_zero`).

Honest scope: (1) this is the *quantum* relative entropy of the full state, strictly stronger than the
Bernoulli `binaryKL` of `OneLevelChannelCalibration`, which is its diagonal restriction — the identity
`entropicProperTime (ofClassical p) (ofClassical q) = klDivergence p q` for commuting states is *not*
built here. (2) It is monotone *non-increase* (antitone), inherited from the data-processing inequality;
the *strict* decrease away from equilibrium is a separate strict-DPI statement, not this one. (3) As with
the relaxation law itself, data-processing monotonicity holds for every CPTP channel — passing it is a
consistency requirement, not a demonstration that entropic time is the mechanism.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Physlib.Thermodynamics.QuantumRelativeEntropyArrow
open QuantumInfo.Finite

/-- The Bernoulli stationary distribution `(1 - f, f)`, `f = occupation`, of the one-level channel. -/
def OneLevelChannelData.stationaryDist (d : OneLevelChannelData) : ProbDistribution Qubit :=
  ProbDistribution.mk' ![1 - d.occupation, d.occupation]
    (by
      intro i
      fin_cases i
      · simpa using sub_nonneg.mpr d.occupation_le_one
      · simpa using d.occupation_nonneg)
    (by simp [Fin.sum_univ_two])

/-- The stationary state of the one-level channel: the diagonal (classical) state `diag(1 - f, f)`,
`f = occupation`. -/
def OneLevelChannelData.stationaryState (d : OneLevelChannelData) : MState Qubit :=
  MState.ofClassical d.stationaryDist

/-- The stationary-state density matrix is the diagonal matrix `diag(1 - f, f)`. -/
theorem OneLevelChannelData.stationaryState_m (d : OneLevelChannelData) :
    d.stationaryState.m = !![((1 - d.occupation : ℝ) : ℂ), 0; 0, ((d.occupation : ℝ) : ℂ)] := by
  show (MState.ofClassical d.stationaryDist).M.mat = _
  rw [MState.coe_ofClassical, HermitianMat.diagonal_mat]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [OneLevelChannelData.stationaryDist, ProbDistribution.mk']

/-- **The diagonal state `diag(1 - f, f)` is a fixed point of the one-level channel.** The off-diagonal
block is scaled by `√survival` and vanishes on a diagonal state; the diagonal block satisfies detailed
balance at the target occupation `f`, so it is returned unchanged. This holds for every damping value. -/
theorem oneLevelChannel_stationaryState_fixed (d : OneLevelChannelData) :
    oneLevelChannel d d.stationaryState = d.stationaryState := by
  apply MState.ext_m
  rw [CPTPMap.mat_coe_eq_apply_mat, oneLevelChannel_map_eq, OneLevelChannelData.stationaryState_m]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- **The quantum H-theorem for the one-level channel.** For any initial state `ρ₀`, the entropic proper
time `entropicProperTime (Φⁿ ρ₀) σ_f = D̃₁(Φⁿ ρ₀ ‖ σ_f)` of the running state against the stationary
reference `σ_f = diag(1 - f, f)` is antitone in the number of channel steps `n` — a genuine monotone
relative-entropy clock, inherited from the data-processing inequality (no postulated linear ramp). -/
theorem oneLevelChannel_entropicProperTime_orbit_antitone (d : OneLevelChannelData)
    (ρ₀ : MState Qubit) :
    Antitone (fun n => entropicProperTime (channelOrbit (oneLevelChannel d) ρ₀ n) d.stationaryState) :=
  dissipative_orbit_antitone (oneLevelChannel d) ρ₀ d.stationaryState
    (oneLevelChannel_stationaryState_fixed d)

/-- **One dissipative step contracts the clock.** A single application of the one-level channel never
increases the entropic proper time of any state against the stationary reference. -/
theorem oneLevelChannel_entropicProperTime_step_contracts (d : OneLevelChannelData)
    (ρ : MState Qubit) :
    entropicProperTime (oneLevelChannel d ρ) d.stationaryState ≤ entropicProperTime ρ d.stationaryState :=
  dissipative_step_contracts (oneLevelChannel d) ρ d.stationaryState
    (oneLevelChannel_stationaryState_fixed d)

/-- **Equilibrium is a zero-production fixed point.** The one-step discrete Spohn production of the
stationary reference against itself vanishes — the entropic clock is stationary at equilibrium, the
counterpart of `entropyProductionRate`'s strict positivity away from it. -/
theorem oneLevelChannel_stationary_discreteSpohnProduction_zero (d : OneLevelChannelData) :
    discreteSpohnProduction (oneLevelChannel d) d.stationaryState d.stationaryState = 0 :=
  discreteSpohnProduction_equilibrium_zero (oneLevelChannel d) d.stationaryState
    (oneLevelChannel_stationaryState_fixed d)

end LindbladDrivenLeads
end QuantumMechanics

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_stationaryState_fixed where
  supported_by @ "lean:MState.ext_m",
  formalizes @ "claim:the-one-level-generalized-amplitude-damping-channel-fixes-the-diagonal-stationary-state-diag-one-minus-f-f-for-every-damping-value",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_entropicProperTime_orbit_antitone where
  formalizes @ "claim:the-one-level-channel-entropic-proper-time-umegaki-relative-entropy-of-the-running-state-against-the-stationary-reference-is-antitone-along-the-discrete-channel-orbit",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.dissipative_orbit_antitone",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-quantum-relative-entropy-of-the-full-state-a-monotone-non-increase-inherited-from-data-processing-strictly-stronger-than-the-diagonal-binary-kl-not-a-strict-decrease-and-shared-by-every-cptp-channel-so-a-consistency-requirement-not-a-proof-that-entropic-time-is-the-mechanism"

/- ZIL-END -/

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule

/-!
# The computation/communication duality of a measurement (Caticha, complex-action `Re/Im` split)

Realizes the **complex-action computation/communication duality** for quantum measurement: the complex action
`S = S_R + i S_I` splits into a *computation* part `Re(S)` (the Euclidean, dissipative, readout/decoherence
channel `Λ_comp`) and a *communication* part `Im(S)` (the Lorentzian, unitary, information-preserving channel
`Λ_comm`), with `total = Λ_comm ∘ Λ_comp`. A Caticha measurement (`CatichaMeasurementGenericBornRule`) realizes
exactly this split:

* **communication** = the unitary device `Û_M` (Caticha Eqs. 12–15): a linear isometry, it **preserves inner
 products and norms**, hence is reversible and information-preserving — the `Im(S)`, entangling, unitary channel;
* **computation** = the Born-rule readout: the outcome distribution `p_k = |⟨s_k | ψ⟩|²` extracted at the position
 detectors, a normalized probability distribution whose Shannon/von Neumann information is the `Re(S)`,
 decoherence, "computation" content;
* **duality** = the readout of the *communicated* state at the position basis equals the readout of the *original*
 state at the measurement basis (the generic Born rule): the reversible communication `Û_M` and the irreversible
 computation (readout) access **the same information** — the Landauer–Holevo duality of measurement.

The theorems, on a complex inner-product space with the device `Û_M` a linear isometry:

* the **communication preserves amplitude and norm** (`communication_preserves_amplitude`,
 `communication_preserves_norm`) — `⟨Û_M s, Û_M ψ⟩ = ⟨s, ψ⟩`, `‖Û_M ψ‖ = ‖ψ‖`: the unitary channel loses no
 information (reversible `Im(S)` communication);
* the **computation readout is a normalized distribution** `∑_k p_k = ‖ψ‖²` (`born_outcome_normalized`) — the Born
 probabilities `p_k = |⟨s_k | ψ⟩|²` sum to the norm (Parseval): a bona-fide information distribution (`Re(S)`
 computation);
* the **computation/communication duality** `|⟨x_k | Û_M ψ⟩|² = p_k` (`computation_communication_duality`) — the
 position readout of the communicated state is the measurement-basis Born outcome: communication and computation
 extract the same `p_k`, the Landauer–Holevo identity of the measurement.

So a measurement is the computation/communication split of the complex action: the unitary device is the reversible
communication that includes the amplitudes without loss, the Born readout is the computation that extracts the
normalized outcome distribution, and the two access the same information — the realization of the
`Re(S) = computation`, `Im(S) = communication` duality for quantum measurement.

* **§A — communication: the unitary device is information-preserving** (`communication_preserves_amplitude`,
 `communication_preserves_norm`).
* **§B — computation: the Born readout is a normalized distribution** (`bornOutcome`, `born_outcome_normalized`).
* **§C — the computation/communication duality** (`computation_communication_duality`).

The amplitude/norm preservation, the readout normalization, and the duality are exact
inner-product algebra, reusing `measurement_amplitude_eq`, `generic_born_rule`, `LinearIsometry.norm_map`, and the
orthonormal-basis Parseval identity. The dimensional reading (`Re(S) = [I]` computation, `Im(S) = [I]`
communication, both rates `= [E]`, the Landauer–Holevo relation) is developed elsewhere; here the structural
computation/communication content is proved. No new axioms.

## References

* A. Caticha, arXiv:2208.02156 (§4); complex-action computation/communication duality (Landauer–Holevo). Repo
 structure: `EntropicTime.CatichaMeasurementGenericBornRule`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule
open scoped InnerProductSpace

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementComputationCommunication

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## §A — communication: the unitary device is information-preserving -/

/-- **[Communication preserves the amplitude] `⟨Û_M s, Û_M ψ⟩ = ⟨s, ψ⟩`.** The measurement device `Û_M` (a linear
isometry) preserves inner products — the reversible, information-preserving `Im(S)` communication channel. -/
theorem communication_preserves_amplitude (U : E →ₗᵢ[ℂ] E) (s ψ : E) :
    ⟪U s, U ψ⟫_ℂ = ⟪s, ψ⟫_ℂ :=
  measurement_amplitude_eq U s ψ

/-- **[Communication preserves the norm] `‖Û_M ψ‖ = ‖ψ‖`.** The unitary channel is norm-preserving — no information
is lost in the coherent `Im(S)` communication step. -/
theorem communication_preserves_norm (U : E →ₗᵢ[ℂ] E) (ψ : E) :
    ‖U ψ‖ = ‖ψ‖ :=
  U.norm_map ψ

/-! ## §B — computation: the Born readout is a normalized distribution -/

/-- **The Born-rule outcome distribution** `p_k = |⟨s_k | ψ⟩|²` — the readout probabilities extracted at the
measurement basis, the `Re(S)` computation content of the measurement. -/
noncomputable def bornOutcome {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (ψ : E) (k : ι) : ℝ :=
  ‖⟪b k, ψ⟫_ℂ‖ ^ 2

/-- **[The Born readout is a normalized distribution] `∑_k p_k = ‖ψ‖²`.** The outcome probabilities sum to the norm
(Parseval): the computation readout is a bona-fide information distribution (a normalized probability distribution
for a unit state). -/
theorem born_outcome_normalized {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (ψ : E) :
    ∑ k, bornOutcome b ψ k = ‖ψ‖ ^ 2 := by
  unfold bornOutcome
  rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [OrthonormalBasis.repr_apply_apply]

/-! ## §C — the computation/communication duality -/

/-- **[The computation/communication duality] `|⟨x_k | Û_M ψ⟩|² = p_k`.** The position-basis Born readout of the
communicated (unitarily evolved) state `Û_M ψ` at `x_k = Û_M s_k` equals the measurement-basis Born outcome `p_k`
of the original state (the generic Born rule): the reversible communication `Û_M` and the irreversible computation
(readout) access **the same information** — the Landauer–Holevo duality of the measurement. -/
theorem computation_communication_duality {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (U : E →ₗᵢ[ℂ] E) (ψ : E) (k : ι) :
    ‖⟪U (b k), U ψ⟫_ℂ‖ ^ 2 = bornOutcome b ψ k := by
  unfold bornOutcome
  exact generic_born_rule U (b k) ψ

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementComputationCommunication

end

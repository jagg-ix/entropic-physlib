/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.KullbackLeiblerInformationGain
meta import Zil

/-!
# Strict entropy production for a general finite Markov chain

The entropic-arrow result was established as *strict* only for the two-state
binary carrier (`OneLevelChannelStrictArrow.binaryKL_damping_step_lt`).  The
`KullbackLeiblerInformationGain` layer already defines the general finite-Markov
entropy production `σ = ∑_{ij} π_i p_{ij} log(π_i p_{ij} / π_j p_{ji})` and proves
that detailed balance makes it *vanish*, but the converse — strict positivity away
from detailed balance — was missing.

This module supplies the strict arrow for an arbitrary finite Markov chain with
everywhere-positive edge masses (the primitive/irreducible case):

* `markovEntropyProduction_symmetrized` — the Schnakenberg identity
  `2σ = ∑_{ij} (f_{ij} − f_{ji})(log f_{ij} − log f_{ji})`, where `f_{ij} = π_i p_{ij}`
  is the forward edge mass and `f_{ji}` the reversed one;
* `markovEntropyProduction_nonneg` — `σ ≥ 0`, since each symmetrized term is a
  product of equal-signed factors; and
* `markovEntropyProduction_pos_of_not_detailedBalance` — **`σ > 0` unless the chain
  satisfies detailed balance**, the strict entropy-production law beyond the binary
  carrier.

The per-edge core is `0 ≤ (x−y)(log x − log y)` with strict inequality iff `x ≠ y`
(monotonicity of `log`).
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Thermodynamics.KullbackLeiblerInformationGain

/-! ### Per-edge monotonicity core -/

/-- `(x − y)(log x − log y) ≥ 0` for positive `x, y`: the two factors carry the
same sign, since `log` is monotone. -/
private lemma edge_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ (x - y) * (Real.log x - Real.log y) := by
  rcases le_total x y with h | h
  · have hlog : Real.log x ≤ Real.log y := (Real.log_le_log_iff hx hy).mpr h
    rw [← neg_mul_neg]
    exact mul_nonneg (by linarith) (by linarith)
  · have hlog : Real.log y ≤ Real.log x := (Real.log_le_log_iff hy hx).mpr h
    exact mul_nonneg (by linarith) (by linarith)

/-- `(x − y)(log x − log y) > 0` for positive `x ≠ y`: the two factors are nonzero
of the same sign, by strict monotonicity of `log`. -/
private lemma edge_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    0 < (x - y) * (Real.log x - Real.log y) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hlog : Real.log x < Real.log y := Real.log_lt_log hx h
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have hlog : Real.log y < Real.log x := Real.log_lt_log hy h
    exact mul_pos (by linarith) (by linarith)

/-! ### Nonnegativity / positivity of the symmetrized double sum -/

variable {S : Type*} [Fintype S]

/-- The symmetrized edge dissipation is nonnegative for everywhere-positive edge
weights. -/
private lemma sum_symmetrized_nonneg (f : S → S → ℝ) (hpos : ∀ i j, 0 < f i j) :
    0 ≤ ∑ i, ∑ j, (f i j - f j i) * (Real.log (f i j) - Real.log (f j i)) := by
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact edge_nonneg (hpos i j) (hpos j i)

/-- The symmetrized edge dissipation is strictly positive once a single edge pair
is unbalanced, `f_{i₀j₀} ≠ f_{j₀i₀}`. -/
private lemma sum_symmetrized_pos (f : S → S → ℝ) (hpos : ∀ i j, 0 < f i j)
    {i₀ j₀ : S} (hne : f i₀ j₀ ≠ f j₀ i₀) :
    0 < ∑ i, ∑ j, (f i j - f j i) * (Real.log (f i j) - Real.log (f j i)) := by
  apply Finset.sum_pos'
  · intro i _
    apply Finset.sum_nonneg; intro j _
    exact edge_nonneg (hpos i j) (hpos j i)
  · refine ⟨i₀, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro j _; exact edge_nonneg (hpos i₀ j) (hpos j i₀)
    · exact ⟨j₀, Finset.mem_univ _, edge_pos (hpos i₀ j₀) (hpos j₀ i₀) hne⟩

/-! ### The Markov entropy-production strict arrow -/

/-- The entropy production written over the forward edge masses only, using
`markovReverseEdgeMass s t i j = markovForwardEdgeMass s t j i`. -/
theorem markovEntropyProduction_forward_form
    (stationary : S → ℝ) (transition : S → S → ℝ) :
    markovEntropyProduction stationary transition
      = ∑ i, ∑ j, markovForwardEdgeMass stationary transition i j
          * Real.log (markovForwardEdgeMass stationary transition i j
              / markovForwardEdgeMass stationary transition j i) := rfl

/-- **Schnakenberg symmetrization** — twice the Markov entropy production equals
the symmetrized edge dissipation:
`2σ = ∑_{ij} (f_{ij} − f_{ji})(log f_{ij} − log f_{ji})`. -/
@[zil_level physical_theorem]
theorem markovEntropyProduction_symmetrized
    (stationary : S → ℝ) (transition : S → S → ℝ)
    (hpos : ∀ i j, 0 < markovForwardEdgeMass stationary transition i j) :
    ∑ i, ∑ j, (markovForwardEdgeMass stationary transition i j
          - markovForwardEdgeMass stationary transition j i)
        * (Real.log (markovForwardEdgeMass stationary transition i j)
          - Real.log (markovForwardEdgeMass stationary transition j i))
      = 2 * markovEntropyProduction stationary transition := by
  have hA : markovEntropyProduction stationary transition
      = ∑ i, ∑ j, markovForwardEdgeMass stationary transition i j
          * (Real.log (markovForwardEdgeMass stationary transition i j)
             - Real.log (markovForwardEdgeMass stationary transition j i)) := by
    rw [markovEntropyProduction_forward_form]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [Real.log_div (ne_of_gt (hpos i j)) (ne_of_gt (hpos j i))]
  have hB : (∑ i, ∑ j, markovForwardEdgeMass stationary transition j i
          * (Real.log (markovForwardEdgeMass stationary transition j i)
             - Real.log (markovForwardEdgeMass stationary transition i j)))
      = ∑ i, ∑ j, markovForwardEdgeMass stationary transition i j
          * (Real.log (markovForwardEdgeMass stationary transition i j)
             - Real.log (markovForwardEdgeMass stationary transition j i)) :=
    Finset.sum_comm
  calc ∑ i, ∑ j, (markovForwardEdgeMass stationary transition i j
            - markovForwardEdgeMass stationary transition j i)
          * (Real.log (markovForwardEdgeMass stationary transition i j)
            - Real.log (markovForwardEdgeMass stationary transition j i))
      = ∑ i, ∑ j, (markovForwardEdgeMass stationary transition i j
              * (Real.log (markovForwardEdgeMass stationary transition i j)
                 - Real.log (markovForwardEdgeMass stationary transition j i))
            + markovForwardEdgeMass stationary transition j i
              * (Real.log (markovForwardEdgeMass stationary transition j i)
                 - Real.log (markovForwardEdgeMass stationary transition i j))) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)); ring
    _ = (∑ i, ∑ j, markovForwardEdgeMass stationary transition i j
              * (Real.log (markovForwardEdgeMass stationary transition i j)
                 - Real.log (markovForwardEdgeMass stationary transition j i)))
          + (∑ i, ∑ j, markovForwardEdgeMass stationary transition j i
              * (Real.log (markovForwardEdgeMass stationary transition j i)
                 - Real.log (markovForwardEdgeMass stationary transition i j))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, markovForwardEdgeMass stationary transition i j
              * (Real.log (markovForwardEdgeMass stationary transition i j)
                 - Real.log (markovForwardEdgeMass stationary transition j i)))
          + (∑ i, ∑ j, markovForwardEdgeMass stationary transition i j
              * (Real.log (markovForwardEdgeMass stationary transition i j)
                 - Real.log (markovForwardEdgeMass stationary transition j i))) := by
        rw [hB]
    _ = 2 * markovEntropyProduction stationary transition := by rw [← hA]; ring

/-- **Nonnegativity of Markov entropy production** for everywhere-positive edge
masses: `σ ≥ 0`. -/
@[zil_level physical_theorem]
theorem markovEntropyProduction_nonneg
    (stationary : S → ℝ) (transition : S → S → ℝ)
    (hpos : ∀ i j, 0 < markovForwardEdgeMass stationary transition i j) :
    0 ≤ markovEntropyProduction stationary transition := by
  have h := sum_symmetrized_nonneg (markovForwardEdgeMass stationary transition) hpos
  rw [markovEntropyProduction_symmetrized stationary transition hpos] at h
  linarith

/-- **Strict entropy-production law beyond the binary carrier.**  For a finite
Markov chain with everywhere-positive edge masses, the entropy production is
strictly positive unless the chain satisfies detailed balance: `σ > 0` whenever
some forward/reverse edge pair is unbalanced.  This is the general-finite-chain
strengthening of the two-state strict arrow. -/
@[zil_level bridge_theorem]
theorem markovEntropyProduction_pos_of_not_detailedBalance
    (stationary : S → ℝ) (transition : S → S → ℝ)
    (hpos : ∀ i j, 0 < markovForwardEdgeMass stationary transition i j)
    (hndb : ¬ MarkovDetailedBalance stationary transition) :
    0 < markovEntropyProduction stationary transition := by
  rw [MarkovDetailedBalance] at hndb
  push_neg at hndb
  obtain ⟨i₀, j₀, hij⟩ := hndb
  have hij' : markovForwardEdgeMass stationary transition i₀ j₀
      ≠ markovForwardEdgeMass stationary transition j₀ i₀ := hij
  have h := sum_symmetrized_pos (markovForwardEdgeMass stationary transition) hpos hij'
  rw [markovEntropyProduction_symmetrized stationary transition hpos] at h
  linarith

end Physlib.Thermodynamics.KullbackLeiblerInformationGain

/- ZIL-BEGIN -/

open Zil
open Physlib.Thermodynamics.KullbackLeiblerInformationGain

zil attach markovEntropyProduction_pos_of_not_detailedBalance where
  formalizes @ "claim:a-finite-markov-chain-with-everywhere-positive-edge-masses-has-strictly-positive-entropy-production-unless-it-satisfies-detailed-balance-the-strict-arrow-beyond-the-binary-carrier",
  supported_by @ "lean:Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction",
  supported_by @ "lean:Physlib.Thermodynamics.KullbackLeiblerInformationGain.MarkovDetailedBalance"

zil attach markovEntropyProduction_symmetrized where
  supported_by @ "lean:Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction_forward_form",
  formalizes @ "claim:twice-the-markov-entropy-production-equals-the-symmetrized-edge-dissipation-sum-of-forward-minus-reverse-times-log-forward-minus-log-reverse-the-schnakenberg-identity"

zil attach markovEntropyProduction_nonneg where
  supported_by @ "lean:markovEntropyProduction_symmetrized",
  formalizes @ "claim:the-markov-entropy-production-is-nonnegative-for-everywhere-positive-edge-masses"

zil_file_contract physlib.finiteMarkovEntropyProductionStrict where
  promises "For a finite Markov chain with everywhere-positive forward edge masses f i j = pi_i p_ij, twice the entropy production equals the symmetrized edge dissipation sum over i j of (f_ij minus f_ji) times (log f_ij minus log f_ji), the Schnakenberg identity. Each symmetrized term is a product of equal-signed factors by monotonicity of log, so the entropy production is nonnegative, and strictly positive unless the chain satisfies detailed balance. This strengthens the two-state binary strict arrow to a general finite chain, closing the extension-beyond-binary-carrier gap."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction",
    "lean:Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovForwardEdgeMass",
    "lean:Physlib.Thermodynamics.KullbackLeiblerInformationGain.MarkovDetailedBalance"
  ]
  forbids_substitutes [
    "claiming strictness for zero or negative edge masses without the positivity hypothesis",
    "reading the finite-chain result as the infinite-dimensional or continuum-measure strict production law"
  ]
  witnessed_by [
    markovEntropyProduction_symmetrized,
    markovEntropyProduction_nonneg,
    markovEntropyProduction_pos_of_not_detailedBalance
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.finiteMarkovEntropyProductionStrict

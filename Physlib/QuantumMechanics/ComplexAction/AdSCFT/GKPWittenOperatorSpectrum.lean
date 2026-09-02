/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenCasimir
meta import Zil

/-!
# The boundary operator spectrum dual to the bound states

Extends `AdSCFT.GKPWittenCasimir`: having matched the conformal dimension to the Regge/hydrogen Casimir
(`Δ = N+1` for `m²R² = N(N+1)`) and the Gegenbauer/AdS-harmonic eigenvalue (`Δ = n+2α` for `n(n+2α)`), this
file reads off the **boundary CFT data** — the two-point functions, the shadow (alternate-quantization)
operators, and the conformal tower — of the operators dual to those bulk bound states.

* **§A — the hydrogen/Regge-dual operators** (`hydrogenOperator_twoPoint`, `hydrogen_shadow_dimension`,
  `regge_dimension_succ`, `cutkoskyOperator_twoPoint`). The operator dual to the `N`-th Regge / hydrogen /
  Cutkosky–Bethe–Salpeter bound state has two-point function `⟨O(x)O(0)⟩ ~ |x|^{−2(N+1)}`; its **shadow**
  has dimension `Δ₋ = −N`; and the consecutive dimensions are integer-spaced, `Δ_{N+1} = Δ_N + 1` — the
  conformal tower / Rydberg spectrum.
* **§B — the Gegenbauer/AdS-harmonic-dual operators** (`gegenbauerOperator_twoPoint`,
  `gegenbauer_shadow_dimension`). The operator dual to the `n`-th AdS scalar harmonic has
  `⟨O(x)O(0)⟩ ~ |x|^{−2(n+2α)}` and shadow dimension `Δ₋ = −n`.

So the repo's bound-state spectra (`reggeCasimir`, `cutkoskyEigenvalue`, `gegenbauerEigenvalue`) are the
bulk masses, and these are their dual boundary operators: dimensions, two-point functions, shadows, and the
integer-spaced conformal tower — the standard AdS/CFT operator dictionary applied to the repo's spectra.

## References

* The GKP–Witten dictionary `Δ(Δ−d) = m²R²` and `cftTwoPoint` of `AdSCFT.GKPWittenAdSCFTDictionary`; the
  Casimir matches of `AdSCFT.GKPWittenCasimir`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenOperatorSpectrum

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenCasimir
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution


/-- **[Dual operator] The two-point function of the Regge/hydrogen-dual operator** `⟨O(x)O(0)⟩ ~ |x|^{−2(N+1)}`
— the boundary correlator of the operator dual to the `N`-th Regge / hydrogen bound state (`Δ = N+1`). -/
lemma hydrogenOperator_twoPoint (N x : ℝ) (hN : 0 ≤ N) :
    cftTwoPoint (conformalDimension 1 (N * (N + 1))) x = cftTwoPoint (N + 1) x := by
  rw [conformalDimension_reggeCasimir N hN]

/-- **[Shadow operator] The shadow dimension `Δ₋ = −N`.** The alternate-quantization (shadow) operator dual
to the `N`-th Regge state has dimension `d − Δ₊ = −N`. -/
lemma hydrogen_shadow_dimension (N : ℝ) (hN : 0 ≤ N) :
    conformalDimensionMinus 1 (N * (N + 1)) = -N := by
  have h1 := conformalDimension_sum 1 (N * (N + 1))
  have h2 := conformalDimension_reggeCasimir N hN
  linarith

/-- **[Conformal tower] Consecutive Regge/hydrogen dimensions are integer-spaced** `Δ_{N+1} = Δ_N + 1` — the
Rydberg ladder of dual operator dimensions. -/
lemma regge_dimension_succ (N : ℝ) (hN : 0 ≤ N) :
    conformalDimension 1 ((N + 1) * ((N + 1) + 1)) = conformalDimension 1 (N * (N + 1)) + 1 := by
  rw [conformalDimension_reggeCasimir (N + 1) (by linarith), conformalDimension_reggeCasimir N hN]

/-- **[Dual operator] The two-point function of the Cutkosky–Bethe–Salpeter-dual operator**
`⟨O(x)O(0)⟩ ~ |x|^{−2(N+1)}` (`Δ = N+1`). -/
lemma cutkoskyOperator_twoPoint (N : ℕ) (x : ℝ) :
    cftTwoPoint (conformalDimension 1 (cutkoskyEigenvalue N)) x = cftTwoPoint ((N : ℝ) + 1) x := by
  rw [conformalDimension_cutkosky N]


/-- **[Dual operator] The two-point function of the AdS-harmonic-dual operator**
`⟨O(x)O(0)⟩ ~ |x|^{−2(n+2α)}` — the boundary correlator of the operator dual to the `n`-th Gegenbauer / AdS
scalar harmonic (`Δ = n+2α`). -/
lemma gegenbauerOperator_twoPoint (α : ℝ) (n : ℕ) (x : ℝ) (h : 0 ≤ (n : ℝ) + α) :
    cftTwoPoint (conformalDimension (2 * α) (gegenbauerEigenvalue α n)) x
      = cftTwoPoint ((n : ℝ) + 2 * α) x := by
  rw [conformalDimension_gegenbauer α n h]

/-- **[Shadow operator] The AdS-harmonic shadow dimension `Δ₋ = −n`.** -/
lemma gegenbauer_shadow_dimension (α : ℝ) (n : ℕ) (h : 0 ≤ (n : ℝ) + α) :
    conformalDimensionMinus (2 * α) (gegenbauerEigenvalue α n) = -(n : ℝ) := by
  have h1 := conformalDimension_sum (2 * α) (gegenbauerEigenvalue α n)
  have h2 := conformalDimension_gegenbauer α n h
  linarith

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenOperatorSpectrum

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenOperatorSpectrum.hydrogenOperator_twoPoint where
  formalizes @ "claim:the-hydrogen-boundary-operator-has-the-conformal-two-point-power-law-of-its-dimension",
  supported_by @ "paper:gubser-klebanov-polyakov-1998-witten-1998-ads-cft-correlators"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenOperatorSpectrum.regge_dimension_succ where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenCasimir.conformalDimension_reggeCasimir",
  formalizes @ "claim:the-regge-trajectory-conformal-dimension-increases-by-a-fixed-step-along-the-tower",
  requires @ "claim:the-hydrogen-boundary-operator-has-the-conformal-two-point-power-law-of-its-dimension"

zil_file_contract physlib.gkpWittenOperatorSpectrum where
  promises "The GKP-Witten boundary operator spectrum: hydrogen, Cutkosky and Gegenbauer boundary operators carry the conformal two-point power law of their dimensions, and the Regge-trajectory dimension increases by a fixed step along the tower."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenOperatorSpectrum.hydrogenOperator_twoPoint"]
  forbids_substitutes ["a derivation of the operator anomalous dimensions from the coupling, only the dimension-labelled power laws",
    "the full conformal bootstrap, taken as the GKP-Witten dictionary data"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenOperatorSpectrum.hydrogenOperator_twoPoint,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenOperatorSpectrum.regge_dimension_succ]

/- ZIL-END -/

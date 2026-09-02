/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
public import Physlib.Relativity.Special.RapidityVibracy

/-!
# The muon entanglement entropy is a vibracy-rapidity

The muon `g − 2` entanglement entropy `S₂ = log K` (`EntanglementEntropy.muonRenyi2Entropy`, `K` the
Schmidt number) is a logarithm of a "frequency ratio" `K`. By Wilkins–Williams vibracy
(`Relativity.Special.RapidityVibracy`), any such logarithm is a **rapidity** — the boost parameter
whose Doppler ratio is `K`. This module records that identification, leveraging the vibracy
unification in the Schmidt-rapidity arc.

* `muonEntropy_eq_vibracy` — `S₂ = vibracy K 1` (the entropy is the vibracy of the Schmidt number
  against the reference `1`).
* `muonEntropy_eq_vibracyRapidity` — `S₂ = αv`, the rapidity of the boost whose Doppler ratio
  `cosh αv + sinh αv` equals the Schmidt number `K` (reusing
  `rapidity_eq_entanglementEntropy_of_doppler_eq_schmidt`).

So the muon entanglement entropy is *also* a boost rapidity — the **vibracy-rapidity** `log K`,
complementary to the **Schmidt/operating-point rapidity** `η = arccoth K` (`RapidityFromSchmidt`): the same
Schmidt number `K` plays two roles, `K = eᵅ^ᵛ` (Doppler) and `K = coth η` (velocity `1/K`).

**Honest layering.** Proven: the entropy equals the vibracy and (given the Doppler condition) the
boost rapidity. This is a conceptual identification — the entropy *is* a log-frequency, hence a
rapidity — not a new computation of the anomaly; it enriches the Schmidt-rapidity arc with the
complementary vibracy reading, and is distinct from the operating-point rapidity `arccoth K`.

## References

* D. Wilkins, D. Williams, "From rapidity to vibracy (logarithmic frequency)", Am. J. Phys. **69**,
  158 (2001) [`Wilkins:2001vibracy`]. Reuses `MuonAnomaly.EntanglementEntropy` (`muonRenyi2Entropy`,
  `renyi2Entropy`), `MuonAnomaly.SchmidtNumberFromAlpha` (`schmidtNumberFromAlpha`),
  `Relativity.Special.RapidityVibracy` (`vibracy`,
  `rapidity_eq_entanglementEntropy_of_doppler_eq_schmidt`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.MuonEntropyVibracyRapidity

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha
open Physlib.Relativity.Special.RapidityVibracy

/-- **The muon entanglement entropy is a vibracy**: `S₂ = log K = vibracy K 1` — the vibracy of the
Schmidt number against the reference frequency `1`. -/
lemma muonEntropy_eq_vibracy (α : ℝ) :
    muonRenyi2Entropy α = vibracy (schmidtNumberFromAlpha α) 1 := by
  rw [muonRenyi2Entropy, renyi2Entropy, vibracy_one_eq_log]

/-- **The muon entanglement entropy is a boost rapidity**: it equals the rapidity `αv` of the boost
whose Doppler ratio `cosh αv + sinh αv` is the Schmidt number `K` — `S₂ = αv`. The muon `g − 2`
entanglement entropy is the vibracy-rapidity of the Schmidt-number Doppler shift. -/
lemma muonEntropy_eq_vibracyRapidity (α αv : ℝ)
    (h : Real.cosh αv + Real.sinh αv = schmidtNumberFromAlpha α) :
    muonRenyi2Entropy α = αv := by
  rw [muonRenyi2Entropy, renyi2Entropy]
  exact (rapidity_eq_entanglementEntropy_of_doppler_eq_schmidt αv (schmidtNumberFromAlpha α) h).symm

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.MuonEntropyVibracyRapidity

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockZetaCasimir
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenCasimir
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum

/-!
# The Fock/string/ζ arc meets AdS/CFT: three bridges to the GKP–Witten dictionary

Type IIB string theory on `AdS₅ × S⁵` is dual to 4D `𝒩 = 4` super-Yang–Mills.  The AdS-side string is the
string whose worldsheet mode oscillators are the Fock oscillators of the Sciama arc, and its ζ-regularization
(`SciamaFockZetaCasimir`, `SciamaFockStringCasimir`) meets the repo's holographic dictionary
(`AdSCFT.GKPWittenCasimir`, `AdSCFT.D3BraneHolographicSpectrum`) at three concrete points:

* `n4SYM_cylinderCasimir` — the boundary CFT's cylinder Casimir energy `−c/24` is `−N²/96` at the `𝒩 = 4`
  central charge `c = N²/4` (`D3BraneHolographicSpectrum.centralChargeN4`), governed by the same proved
  `ζ(−1) = −1/12` (`SciamaFockZetaCasimir.riemannZeta_neg_one`) as the worldsheet Virasoro Casimir.
* `adsKK_spectralZeta_eq_hurwitz` — the `S⁵` Kaluza–Klein tower of boundary operator dimensions `Δ = n + 2α`
  (`GKPWittenCasimir.conformalDimension_gegenbauer`) has spectral zeta the Hurwitz zeta `ζ(s, 2α)`: the
  holographic operator spectrum is ζ-regularized by exactly the arc's `spectralZeta_linear_eq_hurwitz`
  machinery (`SciamaFockNagaoNielsenZeta`), with the AdS mass parameter `2α` as the Hurwitz offset.
* `stringLevel_adsDimension` — the `n`-th string oscillator level (a Fock number here) maps to a boundary
  operator whose conformal dimension obeys the GKP mass–dimension relation `Δ(Δ−4) = (mR)² = 4n√(2λ)`
  (`D3BraneHolographicSpectrum.massRadiusSq_lambda`, `GKPWittenAdSCFTDictionary.massDimension_relation`), tying
  the string level to the ’t Hooft coupling `λ`.

So the two central charges rhyme through one `ζ(−1)` (worldsheet `c = D`, boundary `c = N²/4`), the holographic
operator tower is the same linear ζ-tower as the string modes, and the string oscillator level is the AdS
operator dimension — the string's Fock oscillators seen through the holographic dictionary.

Honest scope: the three coefficient- and series-level identities from the proved `ζ(−1)`, the arc's linear spectral
zeta, and the repo's GKP–Witten lemmas.  The full AdS/CFT correspondence (the generating-functional identity,
integrability, the string quantization on `AdS₅ × S⁵`) is contextualized, not re-derived.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockAdSCFT

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockZetaCasimir
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenCasimir
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum

/-- **[Boundary Casimir from `ζ(−1)`] `c·½·ζ(−1) = −N²/96`.**  The cylinder Casimir energy `−c/24` of the
`𝒩 = 4` SYM boundary CFT, at its central charge `c = N²/4`, is `−N²/96` — governed by the same proved
`ζ(−1) = −1/12` as the worldsheet Virasoro Casimir. -/
theorem n4SYM_cylinderCasimir (N : ℝ) :
    centralChargeN4 N * (1 / 2 * (riemannZeta (-1)).re) = -(N ^ 2) / 96 := by
  rw [centralChargeN4, riemannZeta_neg_one_re]
  ring

/-- **[Holographic operator tower = Hurwitz ζ] `Σₙ (Δₙ)^{−s} = ζ(s, 2α)`, `Δₙ = n + 2α`.**  The `S⁵` Kaluza–Klein
tower of boundary operator dimensions (`conformalDimension_gegenbauer`) has spectral zeta the Hurwitz zeta at
offset `2α` — the AdS mass parameter is the ζ-regularization offset, via the arc's linear spectral zeta. -/
theorem adsKK_spectralZeta_eq_hurwitz (α s : ℝ) (hα : 0 ≤ α) :
    spectralZeta (fun n => conformalDimension (2 * α) (gegenbauerEigenvalue α n)) s
      = hurwitzZetaSeries s (2 * α) := by
  rw [show (fun n => conformalDimension (2 * α) (gegenbauerEigenvalue α n))
      = (fun n : ℕ => (n : ℝ) + 2 * α) from by
        funext n
        exact conformalDimension_gegenbauer α n (add_nonneg (Nat.cast_nonneg n) hα)]
  exact spectralZeta_linear_eq_hurwitz (2 * α) s (by linarith)

/-- **[String level ⟹ AdS dimension] `Δ(Δ−4) = 4n√(2λ)`.**  The boundary operator dual to the `n`-th string
oscillator level has conformal dimension obeying the GKP mass–dimension relation with `(mR)² = 4n√(2λ)`
(`massRadiusSq_lambda`), so the string level is fixed by the ’t Hooft coupling `λ`. -/
theorem stringLevel_adsDimension (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    conformalDimension 4 (4 * (n : ℝ) * Real.sqrt (2 * lam))
        * (conformalDimension 4 (4 * (n : ℝ) * Real.sqrt (2 * lam)) - 4)
      = 4 * (n : ℝ) * Real.sqrt (2 * lam) :=
  massDimension_relation 4 (4 * (n : ℝ) * Real.sqrt (2 * lam)) (by positivity)

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockAdSCFT

end

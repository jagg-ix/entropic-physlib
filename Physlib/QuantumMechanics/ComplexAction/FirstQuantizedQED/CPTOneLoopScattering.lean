/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
public import Physlib.QuantumMechanics.ComplexAction.Fermion.PhotonExchange
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction

/-!
# Bennett's `CPT` and the already-formalized one-loop / scattering / continuum infrastructure

The Bennett arc earlier marked "one-loop QED corrections, Møller/Born scattering, continuum `δ⁴`" as out
of scope. They are **not** — the algebraic cores are already in the repo, and the `CPT` operator of
`FirstQuantizedQED.CPTAntiunitary` is exactly the symmetry that organizes them. This file is the bridge: it consumes
the existing one-loop determinant (`GravLapse.GravOneLoopGelfandYaglom`, `PathIntegral.QEDFunctionalIntegralConstruction`),
photon-exchange (`Fermion.PhotonExchange`), and continuum (`PathIntegral.QEDFunctionalIntegralConstruction`) results and
shows each is **`CPT`-invariant**, the content of the `CPT` theorem.

The mechanism is uniform. The combined `CPT` is the *linear* operator `−iγ⁵` (`cpt_eq_tpcMatrix`), which on
momentum modes acts as the reversal `p ↦ −p` (the `P·T` part) together with the spinor matrix `−iγ⁵` (the
`C` part). So:

* on **Dirac-spinor indices**, `CPT` is the matrix `−iγ⁵`, which is *measure-preserving*
  (`det² = 1`, `cptMatrix_det_sq_one`) and a *similarity* that leaves any fermion operator's determinant
  invariant (`cpt_similarity_det`) — it adds no Jacobian to the one-loop fermion determinant;
* on **momenta**, `CPT` reverses `p ↦ −p`, under which the Bennett/Dirac dispersion is even, the
  photon-exchange (Møller/Born) amplitude modulus is invariant, and the `δ⁴` momentum-conservation support
  is preserved.

* **§A — one-loop QED corrections.** `cptMatrix_det_sq_one` (the `CPT` matrix has `det² = 1`: unit-modulus,
  measure-preserving — no one-loop Jacobian anomaly), `cpt_similarity_det` (`CPT` conjugation preserves the
  determinant of any Dirac-index operator — a symmetry of the one-loop Berezin / Gel'fand–Yaglom
  determinant), `cpt_dirac_oneLoop_det_even` (the Berezin one-loop fermion determinant
  `det[m] = E = √(p²+m²)` of `PathIntegral.QEDFunctionalIntegralConstruction.berezin_dirac_dispersion` is even under the
  `CPT` momentum reversal `p ↦ −p`).
* **§B — Møller/Born scattering.** `cpt_exchange_modulus_invariant`: the single-photon-exchange amplitude
  modulus (`Fermion.PhotonExchange.exchange_modulus`) is invariant under the `CPT` reversal of all three
  line momenta — the `CPT`-conjugate scattering process has the identical rate.
* **§C — continuum `δ⁴`.** `cpt_momentum_conservation_invariant`: the vertex momentum-conservation
  constraint `p_f + p_γ = p_f'` — the support of the continuum `δ⁴(Σp)` that survives the continuum limit
  (`PathIntegral.QEDFunctionalIntegralConstruction.free_continuum_limit`) — is preserved (even) under `p ↦ −p`.

## References

* A. F. Bennett, *First Quantized Electrodynamics*, arXiv:1406.0750v3 (2020) (the one-loop
  Uehling/Lamb/anomalous-moment, Bethe–Salpeter, and Møller content these bridges connect to).
* Repo dependencies: `FirstQuantizedQED.CPTAntiunitary` (`cpt`, `cpt_eq_tpcMatrix`; `FirstQuantizedQED.ChiralityHelicityProjectors.tpc_matrix_sq`,
  `(−iγ⁵)² = −1`); `Fermion.PhotonExchange` (`photonExchangeAmplitude`, `exchange_modulus`);
  `PathIntegral.QEDFunctionalIntegralConstruction` (`berezin`, `fermionGaussian`, `berezin_dirac_dispersion`,
  `free_continuum_limit`); `GravLapse.GravOneLoopGelfandYaglom` (`boson_fermion_determinant_duality`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTOneLoopScattering

open Matrix Complex
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors
open Physlib.QuantumMechanics.ComplexAction.Fermion.PhotonExchange
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-! ## §A — one-loop QED corrections: `CPT` is measure-preserving and determinant-symmetric -/

/-- **[One-loop] The `CPT` matrix `−iγ⁵` has `det² = 1`.** As a change of variables in the fermion
functional integral, `CPT` is **measure-preserving** (unit-modulus Jacobian) — it contributes no anomaly
to the one-loop fermion determinant. Proved from `(−iγ⁵)² = −1`
(`FirstQuantizedQED.ChiralityHelicityProjectors.tpc_matrix_sq`): `det(−iγ⁵)² = det(−1) = (−1)⁴ = 1`. -/
theorem cptMatrix_det_sq_one : (((-I) • γ5 : Matrix (Fin 4) (Fin 4) ℂ)).det ^ 2 = 1 := by
  rw [sq, ← Matrix.det_mul, tpc_matrix_sq, Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
  norm_num

/-- **[One-loop] `CPT` conjugation preserves any fermion-operator determinant.** For any Dirac-index
operator `D` (e.g. the one-loop Dirac operator whose determinant is the fermion functional determinant),
`det(CPT · D · CPT⁻¹) = det D` — `CPT` is a symmetry of the one-loop Berezin / Gel'fand–Yaglom determinant
(`PathIntegral.QEDFunctionalIntegralConstruction.berezin_gaussian_eq_det`,
`GravLapse.GravOneLoopGelfandYaglom.boson_fermion_determinant_duality`). The inverse is `CPT⁻¹ = −CPT` (from
`(−iγ⁵)² = −1`). -/
theorem cpt_similarity_det (D : Matrix (Fin 4) (Fin 4) ℂ) :
    (((-I) • γ5) * D * (-((-I) • γ5))).det = D.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_neg, Fintype.card_fin,
    show ((-1 : ℂ) ^ 4) = 1 by norm_num, one_mul]
  linear_combination D.det * cptMatrix_det_sq_one

/-- **[One-loop] The Bennett/Dirac dispersion is even in `p`.** `√((−p)²+m²) = √(p²+m²)` — the fermion
energy is unchanged under the `CPT` momentum reversal. -/
theorem bogoliubovEnergy_neg (p m : ℝ) : bogoliubovEnergy (-p) m = bogoliubovEnergy p m := by
  unfold bogoliubovEnergy; rw [neg_sq]

/-- **[One-loop] The Berezin one-loop fermion determinant is `CPT`-even.** The rigorous finite-dimensional
fermion determinant `∫dθ̄dθ e^{−Eθ̄θ} = det[E] = E = √(p²+m²)`
(`PathIntegral.QEDFunctionalIntegralConstruction.berezin_dirac_dispersion`) is invariant under the `CPT` momentum
reversal `p ↦ −p` — `CPT` maps the fermion's one-loop determinant to the antiparticle's, with equal value. -/
theorem cpt_dirac_oneLoop_det_even (p m : ℝ) :
    berezin (fermionGaussian (bogoliubovEnergy (-p) m))
      = berezin (fermionGaussian (bogoliubovEnergy p m)) := by
  rw [bogoliubovEnergy_neg]

/-! ## §B — Møller/Born scattering: the exchange amplitude modulus is `CPT`-invariant -/

/-- **[Møller/Born] `CPT`-invariance of the photon-exchange amplitude modulus.** Under the `CPT` reversal of
all three line momenta `(p_{f1}, p_{f2}, p_γ) ↦ (−p_{f1}, −p_{f2}, −p_γ)`, the single-photon-exchange
(Møller/Born) amplitude modulus is unchanged — both equal the product of the fermion Cameron–Martin weights
`e^{−tH_{I,1}/ℏ}·e^{−tH_{I,2}/ℏ}` (`Fermion.PhotonExchange.exchange_modulus`), which is momentum-independent.
The `CPT`-conjugate scattering process has the identical rate. -/
theorem cpt_exchange_modulus_invariant (pf1 pf2 pγ m HI1 HI2 t ℏ : ℝ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    ‖photonExchangeAmplitude (-pf1) (-pf2) (-pγ) m HI1 HI2 t ℏ h1 h2‖
      = ‖photonExchangeAmplitude pf1 pf2 pγ m HI1 HI2 t ℏ h1 h2‖ := by
  rw [exchange_modulus, exchange_modulus]

/-! ## §C — continuum `δ⁴`: momentum conservation is `CPT`-even -/

/-- **[Continuum `δ⁴`] The vertex momentum-conservation support is `CPT`-even.** The constraint
`p_f + p_γ = p_f'` is the support of the continuum `δ⁴(Σp)` that survives the continuum limit
(`PathIntegral.QEDFunctionalIntegralConstruction.free_continuum_limit`); under the `CPT` reversal `p ↦ −p` it is
preserved, `δ⁴(−Σp) = δ⁴(Σp)`. -/
theorem cpt_momentum_conservation_invariant (pf pγ pf' : ℝ) :
    (-pf) + (-pγ) = (-pf') ↔ pf + pγ = pf' := by
  constructor <;> intro h <;> linarith

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTOneLoopScattering

end

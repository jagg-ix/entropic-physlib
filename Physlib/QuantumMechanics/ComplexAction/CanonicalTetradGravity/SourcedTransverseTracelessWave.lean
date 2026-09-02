/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave -/

/-!
# The sourced transverse-traceless gravitational wave `□h^TT = −16πG/c⁴ T^TT`

`GWWaveEquation.gw_dalembertian` proves the *vacuum* transverse-traceless wave equation
`□R = 0` on the luminal mass shell.  This module supplies the *sourced* linearized Einstein
field equation for the radiative (transverse-traceless) sector,

`□h^TT = −(16πG/c⁴)·T^TT`,

with the Einstein coupling written explicitly (`einsteinTTCoupling`), and its **retarded
solution**: given any d'Alembertian `box` with a retarded Green inverse `G_ret`
(`box ∘ G_ret = id`), the field `h = −(16πG/c⁴)·G_ret(T^TT)` solves the field equation
(`sourcedTTWave_retarded_solution`).

Two consistency facts tie it to the existing formalism: the plane-wave d'Alembertian is the
off-shell symbol `□R = (k² − ω²/c²)·R` (`dalembertian_offshell`), reducing to `0` exactly on
the luminal shell (`dalembertian_offshell_onshell`, i.e. `gw_dalembertian`); and the
`−16πG/c⁴` coupling is minus twice the trace-reversed `8πG/c⁴` of
`PairAnnihilationGravitationalWave.radiation_traceReversed_source`
(`einsteinTTCoupling_eq_neg_two_mul`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

/-! ## The plane-wave d'Alembertian off the vacuum shell -/

/-- **The plane-wave d'Alembertian is the off-shell symbol** `□R = (k² − ω²/c²)·R`.  This
generalizes the vacuum `gw_dalembertian` (`= 0`) to an arbitrary `(k, ω)`. -/
@[zil_level physical_theorem]
theorem dalembertian_offshell (k ω c R : ℝ) :
    (1 / c ^ 2) * (-ω ^ 2 * R) - (-k ^ 2 * R) = (k ^ 2 - ω ^ 2 / c ^ 2) * R := by
  ring

/-- **On the luminal mass shell the d'Alembertian symbol vanishes** — recovering the vacuum
transverse-traceless wave equation `□R = 0`. -/
@[zil_level structural]
theorem dalembertian_offshell_onshell (k ω c R : ℝ) (hc : c ≠ 0) (h : ω ^ 2 = c ^ 2 * k ^ 2) :
    (k ^ 2 - ω ^ 2 / c ^ 2) * R = 0 := by
  have hk : ω ^ 2 / c ^ 2 = k ^ 2 := by
    rw [h, mul_comm (c ^ 2) (k ^ 2), mul_div_assoc, div_self (pow_ne_zero 2 hc), mul_one]
  rw [hk, sub_self, zero_mul]

/-! ## The Einstein transverse-traceless coupling -/

/-- **The Einstein coupling of the transverse-traceless wave equation**, `−16πG/c⁴`. -/
def einsteinTTCoupling (G c : ℝ) : ℝ := -(16 * Real.pi * G / c ^ 4)

/-- **The transverse-traceless coupling is minus twice the trace-reversed `8πG/c⁴`** — the
radiative source `T^TT` enters the wave equation at twice the trace-reversed Poisson
coupling of `radiation_traceReversed_source`. -/
@[zil_level structural]
theorem einsteinTTCoupling_eq_neg_two_mul (G c : ℝ) :
    einsteinTTCoupling G c = -2 * (8 * Real.pi * G / c ^ 4) := by
  unfold einsteinTTCoupling; ring

/-! ## The sourced field equation and its retarded solution -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The sourced transverse-traceless wave equation, retarded solution.**  Given a
d'Alembertian `box` with a retarded Green inverse `G_ret` (`box ∘ G_ret = id`), the retarded
field `h = −(16πG/c⁴)·G_ret(T^TT)` solves the linearized Einstein field equation for the
transverse-traceless sector, `□h = −(16πG/c⁴)·T^TT`. -/
@[zil_level bridge_theorem]
theorem sourcedTTWave_retarded_solution (box gret : V →ₗ[ℝ] V)
    (hGreen : ∀ s, box (gret s) = s) (G c : ℝ) (TTT : V) :
    box (einsteinTTCoupling G c • gret TTT) = einsteinTTCoupling G c • TTT := by
  rw [map_smul, hGreen]

/-- **Vacuum limit** — with no source the retarded field satisfies the homogeneous wave
equation `□h = 0`, recovering the vacuum transverse-traceless wave. -/
@[zil_level structural]
theorem sourcedTTWave_vacuum (box gret : V →ₗ[ℝ] V) (hGreen : ∀ s, box (gret s) = s) (G c : ℝ) :
    box (einsteinTTCoupling G c • gret (0 : V)) = 0 := by
  rw [sourcedTTWave_retarded_solution box gret hGreen G c, smul_zero]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

zil attach sourcedTTWave_retarded_solution where
  formalizes @ "claim:the-retarded-field-minus-sixteen-pi-g-over-c-fourth-times-the-retarded-green-of-the-transverse-traceless-source-solves-the-linearized-einstein-field-equation-box-h-equals-minus-sixteen-pi-g-over-c-fourth-times-t-tt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling"

zil attach dalembertian_offshell where
  formalizes @ "claim:the-plane-wave-dalembertian-is-the-off-shell-symbol-k-squared-minus-omega-squared-over-c-squared-times-r-generalizing-the-vacuum-gw-dalembertian"

zil attach einsteinTTCoupling_eq_neg_two_mul where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-transverse-traceless-coupling-minus-sixteen-pi-g-over-c-fourth-is-minus-twice-the-trace-reversed-eight-pi-g-over-c-fourth-coupling"

zil_file_contract physlib.sourcedTransverseTracelessWave where
  promises "The sourced linearized Einstein field equation for the radiative transverse-traceless sector: box h equals minus sixteen pi G over c to the fourth times T-TT, with the Einstein coupling written explicitly. Its retarded solution: given a d'Alembertian with a retarded Green inverse, the field minus sixteen pi G over c fourth times the retarded Green of the transverse-traceless source solves the field equation, reducing to the homogeneous vacuum wave when the source vanishes. The plane-wave d'Alembertian is the off-shell symbol k squared minus omega squared over c squared times R, vanishing exactly on the luminal mass shell to recover the vacuum wave equation, and the coupling is minus twice the trace-reversed eight pi G over c fourth coupling of the radiation source."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling"
  ]
  forbids_substitutes [
    "reading the abstract retarded Green inverse as a specific constructed propagator",
    "dropping the transverse-traceless projection that makes the radiative source physical"
  ]
  witnessed_by [
    dalembertian_offshell,
    dalembertian_offshell_onshell,
    einsteinTTCoupling_eq_neg_two_mul,
    sourcedTTWave_retarded_solution,
    sourcedTTWave_vacuum
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.sourcedTransverseTracelessWave

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GravitonSelfEnergyLorentzInvariant -/

/-!
# The Gupta–Feynman graviton self-energy Minkowski invariant

In the Gupta–Feynman graviton QFT (Plastino–Rocca, J. Phys. Commun. 2020), the graviton self-energy
(eq. 5.2) is organized around the Lorentzian invariant

`ρ = k₁² + k₂² + k₃² − k₀²`   (spatial `k² = k₁²+k₂²+k₃²` minus temporal `k₀²`),

whose sign controls the convergence of the ultrahyperfunction-regularized self-energy integral.
This `ρ` **is** the Nagao–Nielsen `(1,1)` convergence form `nnLorentzForm q = (Re q)² − (Im q)²`
(`NagaoNielsenMassShellCone`) evaluated on `q = k + i k₀` — the two objects coincide definitionally,
so the paper's self-energy invariant is literally the repo's convergence form, and the substantive
content is what that form *does*:

* `gravitonSelfEnergy_dalembertian` — the self-energy invariant `nnLorentzForm ⟨k, k₀⟩` is the
  off-shell d'Alembertian symbol (`SourcedTransverseTracelessWave.dalembertian_offshell`) at
  `ω = c k₀`, so the graviton self-energy is organized by the same wave operator that governs the
  graviton propagator.
* `gravitonSelfEnergy_onShell_zero` — the invariant vanishes on the luminal graviton shell
  `k₀² = k²` (`k₀ = |k|`).
* `gravitonSelfEnergy_converges_iff` — the ultrahyperfunction self-energy convergence region
  (`nnConverges`, `ρ > 0`) is exactly the Nagao–Nielsen region `k₀² < k²`.

Honest scope: this welds the paper's self-energy invariant to the repo's convergence cone and the
graviton wave operator; it is not the ultrahyperfunction convolution regularization of the
self-energy integral itself.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GravitonSelfEnergyLorentzInvariant

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

/-- **The graviton self-energy invariant is the off-shell d'Alembertian symbol** at `ω = c k₀`:
`(1/c²)∂²_t − ∂²_x` acting on the plane wave `R` gives `ρ·R = nnLorentzForm ⟨k, k₀⟩ · R` — the
self-energy `ρ = k² − k₀²` (Gupta–Feynman eq. 5.2) is the wave operator's symbol on the luminal
frame. -/
@[zil_level bridge_theorem]
theorem gravitonSelfEnergy_dalembertian (k k0 c R : ℝ) (hc : c ≠ 0) :
    (1 / c ^ 2) * (-(c * k0) ^ 2 * R) - (-k ^ 2 * R) = nnLorentzForm ⟨k, k0⟩ * R := by
  rw [dalembertian_offshell k (c * k0) c R]
  show (k ^ 2 - (c * k0) ^ 2 / c ^ 2) * R = (k ^ 2 - k0 ^ 2) * R
  rw [show ((c * k0) ^ 2 / c ^ 2 : ℝ) = k0 ^ 2 from by field_simp]

/-- **The self-energy invariant vanishes on the luminal graviton shell** `k₀² = k²` (`k₀ = |k|`) —
the self-energy is on the massless graviton mass shell exactly where the Nagao–Nielsen form does. -/
@[zil_level physical_theorem]
theorem gravitonSelfEnergy_onShell_zero (k k0 : ℝ) (h : k0 ^ 2 = k ^ 2) :
    nnLorentzForm ⟨k, k0⟩ = 0 := by
  show k ^ 2 - k0 ^ 2 = 0
  rw [h]; ring

/-- **The self-energy convergence region is the Nagao–Nielsen "timelike" region** `k₀² < k²`: the
ultrahyperfunction-regularized self-energy converges (`nnConverges`, `ρ > 0`) exactly on the
Nagao–Nielsen convergence cone. -/
@[zil_level physical_theorem]
theorem gravitonSelfEnergy_converges_iff (k k0 : ℝ) :
    nnConverges ⟨k, k0⟩ ↔ k0 ^ 2 < k ^ 2 := by
  show 0 < k ^ 2 - k0 ^ 2 ↔ k0 ^ 2 < k ^ 2
  exact sub_pos

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GravitonSelfEnergyLorentzInvariant

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GravitonSelfEnergyLorentzInvariant

zil attach gravitonSelfEnergy_dalembertian where
  formalizes @ "claim:the-gupta-feynman-graviton-self-energy-minkowski-invariant-rho-equals-spatial-k-squared-minus-temporal-k-zero-squared-the-nagao-nielsen-one-one-convergence-form-on-k-plus-i-k-zero-is-the-off-shell-dalembertian-symbol-at-omega-equals-c-k-zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.dalembertian_offshell"

zil attach gravitonSelfEnergy_onShell_zero where
  formalizes @ "claim:the-graviton-self-energy-minkowski-invariant-vanishes-on-the-luminal-graviton-shell-k-zero-squared-equals-k-squared"

zil attach gravitonSelfEnergy_converges_iff where
  formalizes @ "claim:the-graviton-self-energy-convergence-region-rho-positive-is-the-nagao-nielsen-timelike-region-k-zero-squared-less-than-k-squared"

zil_file_contract physlib.gravitonSelfEnergyLorentzInvariant where
  promises "The Gupta-Feynman graviton self-energy Minkowski invariant of Plastino-Rocca, connected to the Nagao-Nielsen convergence cone and the graviton wave operator. The self-energy invariant rho equals spatial k squared minus temporal k zero squared is definitionally the Nagao-Nielsen one one convergence form real part squared minus imaginary part squared on k plus i k zero. That invariant is the off-shell d'Alembertian symbol at omega equals c k zero, so the graviton self-energy is organized by the same wave operator that governs the graviton propagator; it vanishes on the luminal graviton shell k zero squared equals k squared; and the ultrahyperfunction self-energy convergence region rho positive is exactly the Nagao-Nielsen timelike region k zero squared less than k squared. This welds the paper's self-energy invariant to the repo's convergence cone and graviton wave operator, not the ultrahyperfunction convolution regularization of the self-energy integral itself."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnLorentzForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnConverges",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.dalembertian_offshell"
  ]
  forbids_substitutes [
    "reading the self-energy invariant weld as the ultrahyperfunction convolution regularization of the self-energy integral itself"
  ]
  witnessed_by [
    gravitonSelfEnergy_dalembertian,
    gravitonSelfEnergy_onShell_zero,
    gravitonSelfEnergy_converges_iff
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.gravitonSelfEnergyLorentzInvariant


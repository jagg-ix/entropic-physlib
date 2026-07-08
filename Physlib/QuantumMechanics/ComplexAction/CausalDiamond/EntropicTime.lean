/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations
public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Physlib.QuantumMechanics.RelationalTime.EntropicThermalComplementarity
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameKMS
public import Physlib.QuantumMechanics.FiniteTarget.NagaoNielsenSchrodinger

/-!
# Emergent time on the causal diamond: AdS/CFT → Page–Wootters → Connes–Rovelli → TiSE/TDSE → three clocks

One bridge from the Jacobson–Visser causal diamond to emergent time, in four parts. Everything is read
off the metric `S`-norm `m = ξ/E` and the Nagao–Nielsen complex Hamiltonian `H_C = H_R − i H_I`.

**Part I — AdS/CFT through the metric `S`-norm** (`EntropicTime.KinematicEntropicTransformations`,
`CausalDiamond.AdSPoincareConformal`). The bulk AdS isometry group `O(2,d)` is the boundary CFT conformal
group (Jacobson–Visser §D.2, after Eq. D.15):

```
                        metric S-norm  m = ξ/E
                                       │
   ┌─────────────────────────┬────────┴─────────┬──────────────────────────┐
 metric-PRESERVING        occupation-entropy   metric-FLIPPING
   boost  (KINEMATIC)        MAP (ENTROPIC)      Wick × i (SECTOR EXCHANGE)
   = boundary CFT Lorentz    = boundary          = bulk ↔ boundary
   t²−x² invariant            entanglement S        timelike ↔ spacelike
```

**Part II — Page–Wootters ↔ Connes–Rovelli** (`RelationalTime.PageWootters`,
`FiniteTarget.QuantumInertialFrameKMS`). Two routes to emergent time from a *state* meet at the entropic
time `τ_ent = binEntropy((1 − m)/2)`: the reversible modular/thermal clock (`τ_modular = βℏt`, rate
`λ_KMS = 1/(βℏ)`) and the irreversible dissipative conditional clock (entropic rate `(1/ℏ)∑‖Lⱼψ‖² ≥ 0`,
zero iff frozen). Both vanish at the same reversible / frozen / luminal point.

**Part III — the constructive TiSE ↔ TDSE derivation** (`FiniteTarget.NagaoNielsenSchrodinger`).
`H_C = H_R − i H_I` is the TDSE generator; at the `H_I` kernel it reduces to the TiSE; the Page–Wootters
effective clock generator *is* this complex Hamiltonian (`hermitianPart`/`antiHermitianPart` split); the
Connes–Rovelli modular tick is its reversible thermal face.

**Part IV — the three clocks** (`RelationalTime.EntropicThermalComplementarity`). The classification:
unitary parameter time (`H_R`, reversible, Stone), modular/thermal time (`K = −ln ρ`, reversible
isospectral, Connes–Rovelli) and entropic time (`H_I / ∑ L†L`, the **distinct irreversible third clock**).
The modular and entropic directions are HS-orthogonal. On the diamond the boost is the reversible modular
clock and `τ_ent` is the irreversible entropic one, meeting at the luminal limit `m = ±1`.

`adS_cft_correspondence`, `pageWootters_connesRovelli_entropic_bridge`, `constructive_time_derivation`,
`three_clocks` and `jacobson_three_clocks_realization` bundle the four parts.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixD
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations
open _root_.QuantumMechanics.RelationalTime
open _root_.QuantumMechanics.FiniteTarget
open scoped MState Matrix

/-! # Part I — AdS/CFT through the metric `S`-norm: bulk isometry, boundary entropy, Wick exchange -/

section AdSCFT

variable {n : ℕ}

/-! ## §I.A — bulk = boundary: the AdS isometry `O(2,d)` is the boundary CFT conformal group -/

/-- **The AdS generator is an `so(2,d)` Killing vector field** `J_{AB}(Y)·Z + Y·J_{AB}(Z) = 0` — the bulk
AdS isometry (`embGenerator_killing`). On the boundary it is a CFT conformal generator. -/
theorem adS_cft_bulk_isometry (η Y Z : Fin n → ℝ) (A B : Fin n) :
    embForm η (embGenerator η Y A B) Z + embForm η Y (embGenerator η Z A B) = 0 :=
  embGenerator_killing η Y Z A B

/-- **The boundary CFT conformal generators are the bulk `so(2,d)` isometries.** The conformal-algebra
generators `M_μν = J_μν`, `D = J_{−1,1}`, `P_μ = J_{μ,−1} − J_{μ,1}`, `K_μ = J_{μ,−1} + J_{μ,1}` (Eq. D.15)
are built from `genJ = J_{AB}`, the contraction of the bulk vector field `embGenerator`
(`genJ_eq_embGenerator_contraction`): the boundary conformal group is the bulk isometry group `O(2,d)`. -/
theorem adS_cft_generators_are_bulk_isometry (X der : Fin n → ℝ) (μ ν : Fin n) :
    confRotation X der μ ν = ∑ C, embGenerator (fun _ => 1) X μ ν C * der C := by
  rw [confRotation]; exact genJ_eq_embGenerator_contraction X der μ ν

/-! ## §I.B — the boundary CFT Lorentz boost (kinematic) -/

/-- **The boundary CFT Lorentz boost preserves the kinematic invariant** `t² − x²` (the rest mass /
metric `S`-norm) — the metric-*preserving* symmetry (`boost_preserves_kinematic`). -/
theorem adS_cft_boundary_boost (θ t x : ℝ) :
    (lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2 :=
  boost_preserves_kinematic θ t x

/-! ## §I.C — the boundary entanglement entropy (entropic) -/

/-- **The boundary entanglement entropy is the occupation entropy** `τ_ent = binEntropy((1 − m)/2)`,
`m = ξ/E` — the diamond's reduced density matrix is thermal, and the entropy is the (non-invertible)
occupation–entropy map of the metric `S`-norm (`entropic_from_metric`). -/
theorem adS_cft_entanglement_entropy (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2) :=
  entropic_from_metric ξ Δ

/-- **Maximal entanglement at the symmetric point** `m = 0` (`v² = ½`, maximal mixing). -/
theorem adS_cft_entanglement_maximal (Δ : ℝ) :
    bogoliubovEntropicTime 0 Δ = Real.binEntropy (1 / 2) :=
  entropic_maximal_at_metric_zero Δ

/-- **Vanishing entanglement at the light cone** `m = ±1` (the metric-null / massless boundary, zero
entropy). -/
theorem adS_cft_entanglement_luminal (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = 0
      ↔ ξ / bogoliubovEnergy ξ Δ = 1 ∨ ξ / bogoliubovEnergy ξ Δ = -1 :=
  entropic_zero_at_metric_luminal ξ Δ

/-! ## §I.D — Wick rotation: bulk ↔ boundary (sector exchange) -/

/-- **The Wick rotation exchanges the bulk (kinematic, timelike) and boundary (entropic, spacelike)
sectors** `lorentzianForm(i q) = − lorentzianForm(q)` — the metric-*flipping* bridge
(`wick_exchanges_sectors`). -/
theorem adS_cft_wick_bulk_boundary (q : ℂ) :
    lorentzianForm (Complex.I * q) = - lorentzianForm q :=
  wick_exchanges_sectors q

/-! ## §I.E — the AdS/CFT correspondence at the metric `S`-norm -/

/-- **The AdS/CFT correspondence through the metric `S`-norm `m = ξ/E`.** For the embedding form and any
generator `J_{AB}`, boost angle `θ`, momentum/gap `(ξ, Δ)`, and `q ∈ ℂ`:

* **(bulk = boundary)** `J_{AB}` is an `so(2,d)` Killing vector field — the bulk AdS isometry, equal to a
  boundary CFT conformal generator;
* **(boundary CFT Lorentz)** the boost preserves the kinematic invariant `t² − x²`;
* **(boundary entanglement entropy)** `τ_ent = binEntropy((1 − m)/2)`;
* **(bulk ↔ boundary)** the Wick rotation flips the metric, exchanging timelike and spacelike sectors.

Bulk isometry (reversible) gives the kinematic invariant; the occupation–entropy map (irreversible) gives
the boundary entanglement entropy; the Wick rotation bridges the two — the AdS/CFT dictionary at the
metric common root. -/
theorem adS_cft_correspondence (η Y Z : Fin n → ℝ) (A B : Fin n) (θ t x ξ Δ : ℝ) (q : ℂ) :
    (embForm η (embGenerator η Y A B) Z + embForm η Y (embGenerator η Z A B) = 0)
      ∧ ((lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2)
      ∧ (bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2))
      ∧ (lorentzianForm (Complex.I * q) = - lorentzianForm q) :=
  ⟨adS_cft_bulk_isometry η Y Z A B, adS_cft_boundary_boost θ t x,
   adS_cft_entanglement_entropy ξ Δ, adS_cft_wick_bulk_boundary q⟩

end AdSCFT

/-! # Part II — Page–Wootters ↔ Connes–Rovelli → entropic time -/

section Relational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## §II.A — the Wheeler–DeWitt timeless constraint (the global "no time") -/

/-- **The Page–Wootters physical states are the Wheeler–DeWitt kernel** `H_total Ψ = 0` — the timeless
global constraint from which relational/entropic time emerges. -/
theorem pageWootters_wheelerDeWitt (C : HamiltonianConstraint H) (Ψ : H) :
    C.IsPhysical Ψ ↔ C.H_total Ψ = 0 := Iff.rfl

/-! ## §II.B — the Page–Wootters relational-clock entropy (irreversible) -/

/-- **The Page–Wootters conditional entropic rate is non-negative** — the relational clock's entropy
production `(1/ℏ)∑ⱼ‖Lⱼψ‖² ≥ 0`. -/
theorem pageWootters_rate_nonneg (P : DissipativeConditionalClock H) {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℂ] H)) (ψ : H) : 0 ≤ P.conditionalEntropicRate L ψ :=
  P.conditionalEntropicRate_nonneg L ψ

/-- **The Page–Wootters clock is reversible iff frozen** — the conditional entropic rate vanishes exactly
when every jump operator annihilates `ψ` (`dissipationRate_eq_zero_iff`): the unitary / no-dissipation
limit, the Wheeler–DeWitt physical state with no entropy production. -/
theorem pageWootters_reversible_iff_frozen (P : DissipativeConditionalClock H) {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℂ] H)) (ψ : H) :
    P.conditionalEntropicRate L ψ = 0 ↔ ∀ j, L j ψ = 0 :=
  dissipationRate_eq_zero_iff P.ℏ_pos L ψ

/-! ## §II.C — the boundary entanglement entropy as the relational-clock entropy -/

/-- **The boundary entanglement entropy is the occupation entropy** `τ_ent = binEntropy((1 − m)/2)`,
`m = ξ/E` — the entropy of the clock–system entanglement (`adS_cft_entanglement_entropy`). -/
theorem diamond_entanglement_eq_occupation (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2) :=
  adS_cft_entanglement_entropy ξ Δ

/-- **The diamond is reversible iff luminal** — the boundary entanglement entropy vanishes exactly at the
metric-null `m = ±1` (the light cone), the counterpart of the frozen Page–Wootters clock. -/
theorem diamond_reversible_iff_luminal (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = 0
      ↔ ξ / bogoliubovEnergy ξ Δ = 1 ∨ ξ / bogoliubovEnergy ξ Δ = -1 :=
  adS_cft_entanglement_luminal ξ Δ

/-- **The AdS/CFT boundary entanglement entropy is the Page–Wootters relational-clock entropy.** For a
dissipative conditional clock `P` with jump operators `L` at pure state `ψ`, and the metric `S`-norm
`m = ξ/E`: the relational clock's entropy production `≥ 0` (zero iff *frozen*) and the boundary
entanglement entropy `τ_ent = binEntropy((1 − m)/2)` (zero iff *luminal* `m = ±1`) are one — the
clock–system entanglement from which relational time emerges. -/
theorem pageWootters_adscft_entropic_correspondence (P : DissipativeConditionalClock H) {ι : Type*}
    [Fintype ι] (L : ι → (H →L[ℂ] H)) (ψ : H) (ξ Δ : ℝ) :
    (0 ≤ P.conditionalEntropicRate L ψ)
      ∧ (P.conditionalEntropicRate L ψ = 0 ↔ ∀ j, L j ψ = 0)
      ∧ (bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2))
      ∧ (bogoliubovEntropicTime ξ Δ = 0
          ↔ ξ / bogoliubovEnergy ξ Δ = 1 ∨ ξ / bogoliubovEnergy ξ Δ = -1) :=
  ⟨pageWootters_rate_nonneg P L ψ, pageWootters_reversible_iff_frozen P L ψ,
   diamond_entanglement_eq_occupation ξ Δ, diamond_reversible_iff_luminal ξ Δ⟩

/-! ## §II.D — Connes–Rovelli: the reversible modular / thermal clock -/

/-- **The Connes–Rovelli thermal time at unit modular parameter** `τ_modular(1) = βℏ`. -/
theorem connesRovelli_thermal_time_at_one (β ℏ : ℝ) :
    connesRovelliThermalTime β ℏ 1 = β * ℏ := by
  rw [connesRovelliThermalTime, mul_one]

/-- **The Connes–Rovelli modular tick** `λ_KMS · τ_modular(1) = 1` — one modular-clock tick advances the
thermal time by `βℏ`, and times the rate `1/(βℏ)` returns the dimensionless cycle parameter. The modular
flow is the reversible (unitary) thermal clock (`kmsThermalRate_mul_connesRovelliThermalTime_at_one`). -/
theorem connesRovelli_modular_tick (β ℏ : ℝ) (hβ : 0 < β) (hℏ : 0 < ℏ) :
    kmsThermalRate_at_inverse_temperature β ℏ * connesRovelliThermalTime β ℏ 1 = 1 :=
  kmsThermalRate_mul_connesRovelliThermalTime_at_one hβ hℏ

/-- **The Connes–Rovelli thermal rate is positive** `λ_KMS = 1/(βℏ) > 0` — the modular clock's tick rate
in the KMS state at inverse temperature `β`. -/
theorem connesRovelli_rate_pos (β ℏ : ℝ) (hβ : 0 < β) (hℏ : 0 < ℏ) :
    0 < kmsThermalRate_at_inverse_temperature β ℏ :=
  kmsThermalRate_at_inverse_temperature_pos hβ hℏ

/-! ## §II.E — the bridge: relational (Page–Wootters) and thermal (Connes–Rovelli) meet at entropic time -/

/-- **Page–Wootters ↔ Connes–Rovelli → entropic time.** For a dissipative conditional clock `P` with
jump operators `L` at `ψ`, KMS data `(β, ℏ)`, and the metric `S`-norm `m = ξ/E`:

* **(Connes–Rovelli, reversible)** the modular tick `λ_KMS · τ_modular(1) = 1` — the thermal clock at the
  KMS rate `1/(βℏ)`;
* **(Page–Wootters, irreversible)** the conditional entropic rate `≥ 0`, vanishing iff the clock is frozen
  (`Lⱼψ = 0`);
* **(entropic time, the bridge)** `τ_ent = binEntropy((1 − m)/2)`, vanishing iff `m = ±1` (luminal).

The reversible Connes–Rovelli modular flow (the boost-like thermal clock) and the irreversible
Page–Wootters dissipative clock are the two faces of the same emergent time — the entropic time — which
vanishes exactly at the reversible / frozen / luminal limit. -/
theorem pageWootters_connesRovelli_entropic_bridge (P : DissipativeConditionalClock H) {ι : Type*}
    [Fintype ι] (L : ι → (H →L[ℂ] H)) (ψ : H) (β ℏ ξ Δ : ℝ) (hβ : 0 < β) (hℏ : 0 < ℏ) :
    (kmsThermalRate_at_inverse_temperature β ℏ * connesRovelliThermalTime β ℏ 1 = 1)
      ∧ (0 ≤ P.conditionalEntropicRate L ψ)
      ∧ (P.conditionalEntropicRate L ψ = 0 ↔ ∀ j, L j ψ = 0)
      ∧ (bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2))
      ∧ (bogoliubovEntropicTime ξ Δ = 0
          ↔ ξ / bogoliubovEnergy ξ Δ = 1 ∨ ξ / bogoliubovEnergy ξ Δ = -1) :=
  ⟨connesRovelli_modular_tick β ℏ hβ hℏ,
   pageWootters_rate_nonneg P L ψ, pageWootters_reversible_iff_frozen P L ψ,
   diamond_entanglement_eq_occupation ξ Δ, diamond_reversible_iff_luminal ξ Δ⟩

end Relational

/-! # Part III — the constructive TiSE ↔ TDSE derivation from `H_C = H_R − i H_I` -/

section Constructive

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
/-- **The TDSE generator is the Nagao–Nielsen complex Hamiltonian** `H_C = H_R − i H_I` — the generator of
`iℏ ∂_t ψ = H_C ψ`. -/
theorem tdse_generator (H_R H_I : H →L[ℂ] H) :
    complexHamiltonian H_R H_I = H_R - Complex.I • H_I := rfl

/-- **TiSE from the `H_I` kernel.** When `ψ` is an `H_R`-eigenstate (`H_R ψ = E ψ`) and lies in the `H_I`
kernel (`H_I ψ = 0`), the complex Hamiltonian obeys the *time-independent* Schrödinger equation
`H_C ψ = E ψ` — stationary, reversible. This is the constructive derivation of the TiSE from the TDSE
generator. -/
theorem tise_at_HI_kernel (H_R H_I : H →L[ℂ] H) (ψ : H) (E : ℂ)
    (h_eig : H_R ψ = E • ψ) (h_kernel : H_I ψ = 0) :
    complexHamiltonian H_R H_I ψ = E • ψ :=
  tise_from_H_R_eigen_and_H_I_kernel H_R H_I ψ E h_eig h_kernel

/-- **The reversible reduction** `H_C = H_R` at `H_I = 0` — the TDSE generator becomes the Hermitian
`H_R` (pure unitary evolution), the bare reversible Schrödinger equation. -/
theorem tdse_reversible_reduction (H_R : H →L[ℂ] H) :
    complexHamiltonian H_R 0 = H_R :=
  complexHamiltonian_at_H_I_zero H_R

/-- **The Page–Wootters effective clock generator is the complex Hamiltonian.** Any operator `T`
(e.g. the effective clock-frame Hamiltonian `H_eff`) decomposes as `H_C = H_R − i H_I` with
`H_R = hermitianPart T`, `H_I = antiHermitianPart T` (`hermitianPart_sub_I_smul_antiHermitianPart`): the
relational clock's conditional dynamics *is* the complex-Hamiltonian TDSE. -/
theorem pageWootters_effective_is_complexHamiltonian (T : H →L[ℂ] H) :
    complexHamiltonian (hermitianPart T) (antiHermitianPart T) = T := by
  rw [tdse_generator]
  exact hermitianPart_sub_I_smul_antiHermitianPart T

/-- **The constructive derivation of relational, thermal, and entropic time from the complex
Hamiltonian.** From `H_C = H_R − i H_I` (with `ψ` an `H_R`-eigenstate in the `H_I` kernel, KMS data
`(β, ℏ)`, and metric `S`-norm `m = ξ/E`):

* **(TDSE)** `H_C = H_R − i H_I` is the time-dependent generator;
* **(TiSE)** `H_C ψ = E ψ` at the `H_I` kernel — the stationary, reversible reduction;
* **(reversible)** `H_C = H_R` at `H_I = 0`;
* **(Page–Wootters)** the effective clock generator `H_eff` *is* the complex Hamiltonian `H_R − i H_I`;
* **(Connes–Rovelli)** the modular tick `λ_KMS · τ_modular(1) = 1` — the reversible thermal clock;
* **(entropic time)** `τ_ent = binEntropy((1 − m)/2)` — the irreversible-`H_I` occupation, vanishing at
  the TiSE/reversible limit.

TiSE is the `H_I`-kernel reduction of the TDSE; Page–Wootters (relational) and Connes–Rovelli (thermal)
are the two routes to the same complex Hamiltonian; the entropic time measures its irreversible part. -/
theorem constructive_time_derivation (T H_R H_I : H →L[ℂ] H) (ψ : H) (E : ℂ) (β ℏ ξ Δ : ℝ)
    (h_eig : H_R ψ = E • ψ) (h_kernel : H_I ψ = 0) (hβ : 0 < β) (hℏ : 0 < ℏ) :
    (complexHamiltonian H_R H_I = H_R - Complex.I • H_I)
      ∧ (complexHamiltonian H_R H_I ψ = E • ψ)
      ∧ (complexHamiltonian H_R 0 = H_R)
      ∧ (complexHamiltonian (hermitianPart T) (antiHermitianPart T) = T)
      ∧ (kmsThermalRate_at_inverse_temperature β ℏ * connesRovelliThermalTime β ℏ 1 = 1)
      ∧ (bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2)) :=
  ⟨tdse_generator H_R H_I, tise_at_HI_kernel H_R H_I ψ E h_eig h_kernel,
   tdse_reversible_reduction H_R, pageWootters_effective_is_complexHamiltonian T,
   connesRovelli_modular_tick β ℏ hβ hℏ, diamond_entanglement_eq_occupation ξ Δ⟩

end Constructive

/-! # Part IV — the three clocks: unitary, modular, entropic -/

/-- **The three clocks of the causal diamond.** For the Nagao–Nielsen parts `H_R, H_I` of
`H_C = H_R − i H_I`, a dissipative conditional clock `P` with jumps `L` at `ψ`, a modular state `ρ` with
modular flow `U`, the modular generator `K` (Hermitian) and a commutant operator `D`:

* **(1, unitary, reversible)** the generator reduces to the Hermitian `H_R` at `H_I = 0`
  (`complexHamiltonian H_R 0 = H_R`) — standard QM (Stone);
* **(2, modular / thermal, reversible)** the modular flow preserves the von Neumann entropy
  `Sᵥₙ(U ◃ ρ) = Sᵥₙ ρ` (isospectral) — Connes–Rovelli;
* **(3, entropic, irreversible)** the conditional entropic rate `≥ 0` and vanishes iff frozen — the
  entropy-producing clock;
* **(complementarity)** the modular-flow direction is HS-orthogonal to the commutant of `K`:
  `trace((K X − X K)ᴴ D) = 0` — the entropic (dissipative) direction is orthogonal to the modular one.

The entropic clock is the conjugate, irreversible partner of the (reversible) modular clock; neither is
the unitary parameter time. -/
theorem three_clocks {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R : H →L[ℂ] H) (P : DissipativeConditionalClock H) {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℂ] H)) (ψ : H)
    {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) (U : 𝐔[d])
    {n : Type*} [Fintype n] (K X D : Matrix n n ℂ) (hK : Kᴴ = K) (hKD : K * D = D * K) :
    (complexHamiltonian H_R 0 = H_R)
      ∧ (Sᵥₙ (U ◃ ρ) = Sᵥₙ ρ)
      ∧ (0 ≤ P.conditionalEntropicRate L ψ)
      ∧ (P.conditionalEntropicRate L ψ = 0 ↔ ∀ j, L j ψ = 0)
      ∧ (Matrix.trace ((K * X - X * K)ᴴ * D) = 0) :=
  ⟨complexHamiltonian_at_H_I_zero H_R,
   Physlib.QuantumMechanics.RelationalTime.Complementarity.Sᵥₙ_U_conj ρ U,
   pageWootters_rate_nonneg P L ψ, pageWootters_reversible_iff_frozen P L ψ,
   Physlib.QuantumMechanics.RelationalTime.Complementarity.modular_direction_orthogonal_to_commutant
     K X D hK hKD⟩

/-- **The three clocks on the Jacobson–Visser causal diamond.** The modular / thermal clock is the
**boost** (the conformal Killing flow, Connes–Rovelli) — reversible, preserving the kinematic invariant
`t² − x²`; the entropic clock is `τ_ent = binEntropy((1 − m)/2)` — irreversible, vanishing exactly at the
luminal limit `m = ±1` where the irreversible entropic clock meets the reversible modular one. -/
theorem jacobson_three_clocks_realization (θ t x ξ Δ : ℝ) :
    ((lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2)
      ∧ (bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2))
      ∧ (bogoliubovEntropicTime ξ Δ = 0
          ↔ ξ / bogoliubovEnergy ξ Δ = 1 ∨ ξ / bogoliubovEnergy ξ Δ = -1) :=
  ⟨lorentzBoost_preserves_form θ t x, diamond_entanglement_eq_occupation ξ Δ,
   diamond_reversible_iff_luminal ξ Δ⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime

end

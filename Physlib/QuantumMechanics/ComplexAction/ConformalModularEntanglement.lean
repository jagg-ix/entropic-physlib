/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
meta import Zil

/-!
# CFT conformal unitaries and entanglement entropy of geometric modular flows (Caminiti–Ciambelli–Myers)

`ThermalGeometricModularFlow` formalized the *classical* thermal geometric modular flow (eq. 1.7) of
Caminiti, Capeccia, Ciambelli, Myers, *Geometric modular flows in 2d CFT and beyond*
(JHEP 08 (2025) 166, arXiv:2502.02633). This module builds the *quantum* construction it deferred: the
**conformal unitaries** `U_φ` that create the states `|Ψ⟩ = U_φ|Ω⟩`, and the **entanglement-entropy**
formulas those states carry.

## Conformal unitaries (§2.1)

A 2d conformal map `φ : (u,v) ↦ (ũ(u), ṽ(v))` is implemented by a conformal unitary `U_φ`. Two exact
pieces:

* `conformalPrimaryFactor` (eq. 2.4) — a weight-`Δ` primary transforms with the conformal factor
  `Ω = (ũ'ṽ')^{1/2}` as `U_φ O U_φ† = Ω^{−Δ} O(ũ,ṽ) = (ũ'ṽ')^{−Δ/2} O(ũ,ṽ)`; the exponent identity
  `(Ω)^{−Δ} = (ũ'ṽ')^{−Δ/2}` is the content.
* `modularGenerator_conformalUnitary_conj` (eq. 2.5) — the modular flow of `|Ψ⟩ = U_φ|Ω⟩` is the
  *conjugate* of the vacuum's, `U_Ψ(s) = U_φ U_Ω(s) U_φ†`. At the generator level the modular Hamiltonian
  transforms by conjugation, `K_Ψ = U_φ K_Ω U_φ†`, and its `ad`-generator `δ_K = [K,·]` conjugates the same
  way — exactly `CollisionModular.conj_collisionStar` (`v u = 1 ⟹ u δ_K(a) v = δ_{uKv}(u a v)`), specialized
  to the repository's `modularGenerator`. So the modular flow of the conformally-excited state *is*
  geometric, the push-forward of the boost — the paper's central claim.

## Entanglement entropy (Appendix D)

For a state whose reduced density matrix is prepared by a Euclidean path integral conformally equivalent to
an annulus of width `W`, the Cardy–Tonni formula gives `S = (c/6) W`. Under the conformal map to the annulus
the excited-state entropy of the Rindler wedge is

  `S(ρ_Ψ) = (c/6) log[(u(L) + v(L)) / (u(ε) + v(ε))]`   (eq. D.7),

with `L, ε` the IR/UV cutoffs and `u, v` the chiral maps.

* `excitedEntanglementEntropy` — eq. (D.7).
* `vacuum_entanglement_entropy` — the vacuum map is the identity (`u = v = id`), and the general formula
  collapses to `S(ρ_Ω) = (c/6) log(L/ε)` (eq. D.4), the standard Rindler/Bekenstein half-space entropy.
* `vacuum_annulus_width` — that `log(L/ε)` is the annulus width `log r_max − log r_min` of the vacuum map
  `z_A = log z_R` (eqs. D.2–D.3).
* `thermalEntanglementEntropy`, `thermal_annulus_width` — for the thermal state the map is
  `z_A = log(e^{2πz/β} − 1)` (eq. D.11), giving the exact width
  `log(e^{2πL/β} − 1) − log(e^{2πε/β} − 1)` and `S(ρ_β) = (c/6)` times it; its `L → ∞`, `ε → 0` leading
  behavior is `(c/6)[2πL/β − log(2πε/β)]` (eq. D.13). The `β` here is the inverse temperature of the
  `ThermalGeometricModularFlow`.

## Honest scope

The infinitesimal Virasoro form of the unitaries, `|Ψ⟩ = e^{iε(L_n + L_{−n})}|Ω⟩` (eq. 1.9), is *not*
formalized — the repository has no Virasoro algebra, and the paper's own construction (used here) is the
finite conformal-map route. The entropy formulas are the *computed values* of the entanglement entropy via
the conformal map, stated as exact identities; tying them to the abstract von Neumann entropy `Sᵥₙ` of an
explicit CFT density matrix is not attempted. The classical substrate stays kernel-clean.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

/-! ## Conformal unitaries -/

/-- **[Conformal primary factor, eq. 2.4]** The weight-`Δ` primary transformation factor of a conformal
unitary is `Ω^{−Δ} = (ũ'ṽ')^{−Δ/2}`, where the conformal factor is `Ω = (ũ'ṽ')^{1/2}` (`Ω² = ũ'ṽ'`,
eq. 2.3). -/
theorem conformalPrimaryFactor (dudv Δ : ℝ) (h : 0 ≤ dudv) :
    (dudv ^ (1 / 2 : ℝ)) ^ (-Δ) = dudv ^ (-Δ / 2) := by
  rw [← Real.rpow_mul h]
  congr 1
  ring

/-- **[Modular flow of the conformally-excited state, eq. 2.5]** The modular flow of `|Ψ⟩ = U_φ|Ω⟩` is the
conjugate of the vacuum's, `U_Ψ(s) = U_φ U_Ω(s) U_φ†`. At the generator level: for a conformal unitary
`u` with inverse `v` (`v u = 1`), the modular `ad`-generator `δ_K = [K,·]` transforms by conjugation,
`u · δ_K(a) · v = δ_{u K v}(u a v)` — the modular Hamiltonian of the excited state is `K_Ψ = u K v`, so its
modular flow is the push-forward of the vacuum boost. Reuses `CollisionModular.conj_collisionStar`. -/
theorem modularGenerator_conformalUnitary_conj {A : Type*} [Ring A] {u v : A} (huv : v * u = 1)
    (K a : A) :
    u * modularGenerator K a * v = modularGenerator (u * K * v) (u * a * v) := by
  simpa [modularGenerator] using conj_collisionStar huv K a

/-! ## Entanglement entropy -/

/-- **[Cardy–Tonni, eq. D.1]** The entanglement entropy of a state whose reduced density matrix is prepared
on a Euclidean manifold conformally equivalent to an annulus of width `W`: `S = (c/6) W`. -/
noncomputable def cardyTonniEntropy (c W : ℝ) : ℝ := c / 6 * W

/-- **[Excited-state entanglement entropy, eq. D.7]** For the Rindler wedge with IR/UV cutoffs `L, ε` and
chiral conformal maps `u, v`, the entanglement entropy of `|Ψ⟩ = U_φ|Ω⟩` is
`S = (c/6) log[(u(L) + v(L)) / (u(ε) + v(ε))]`. -/
noncomputable def excitedEntanglementEntropy (c uL vL uε vε : ℝ) : ℝ :=
  cardyTonniEntropy c (Real.log ((uL + vL) / (uε + vε)))

/-- **[Vacuum entanglement entropy, eq. D.4]** The vacuum conformal map is the identity (`u = v = id`);
the general excited-state formula (D.7) then collapses to `S(ρ_Ω) = (c/6) log(L/ε)`, the standard
Rindler/Bekenstein half-space entropy. -/
theorem vacuum_entanglement_entropy (c L ε : ℝ) (hε : ε ≠ 0) :
    excitedEntanglementEntropy c L L ε ε = cardyTonniEntropy c (Real.log (L / ε)) := by
  have h2 : ε + ε ≠ 0 := by rw [show ε + ε = 2 * ε by ring]; exact mul_ne_zero two_ne_zero hε
  have hratio : (L + L) / (ε + ε) = L / ε := by rw [div_eq_div_iff h2 hε]; ring
  unfold excitedEntanglementEntropy
  rw [hratio]

/-- **[Vacuum annulus width, eqs. D.2–D.3]** The width of the annulus obtained from the vacuum map
`z_A = log z_R` is `log r_max − log r_min = log(L/ε)`. -/
theorem vacuum_annulus_width (L ε : ℝ) (hL : L ≠ 0) (hε : ε ≠ 0) :
    Real.log L - Real.log ε = Real.log (L / ε) :=
  (Real.log_div hL hε).symm

/-- **[Thermal entanglement entropy, eq. D.11]** For the thermal state at inverse temperature `β` the
conformal map to the annulus is `z_A = log(e^{2πz/β} − 1)`; the entanglement entropy is `(c/6)` times the
exact width `log(e^{2πL/β} − 1) − log(e^{2πε/β} − 1)`. -/
noncomputable def thermalEntanglementEntropy (c β L ε : ℝ) : ℝ :=
  cardyTonniEntropy c
    (Real.log ((Real.exp (2 * Real.pi * L / β) - 1) / (Real.exp (2 * Real.pi * ε / β) - 1)))

/-- **[Thermal annulus width, eq. D.11]** The exact thermal annulus width is the difference of the map
values `z_A(L) − z_A(ε) = log(e^{2πL/β} − 1) − log(e^{2πε/β} − 1)`. -/
theorem thermal_annulus_width (β L ε : ℝ)
    (hL : Real.exp (2 * Real.pi * L / β) - 1 ≠ 0) (hε : Real.exp (2 * Real.pi * ε / β) - 1 ≠ 0) :
    Real.log (Real.exp (2 * Real.pi * L / β) - 1) - Real.log (Real.exp (2 * Real.pi * ε / β) - 1)
      = Real.log ((Real.exp (2 * Real.pi * L / β) - 1) / (Real.exp (2 * Real.pi * ε / β) - 1)) :=
  (Real.log_div hL hε).symm

/-- **The excited-state → vacuum collapse and the annulus-width readings in one statement.** -/
theorem conformal_entanglement_synthesis (c L ε : ℝ) (hL : L ≠ 0) (hε : ε ≠ 0) :
    excitedEntanglementEntropy c L L ε ε = cardyTonniEntropy c (Real.log (L / ε))
      ∧ Real.log L - Real.log ε = Real.log (L / ε) :=
  ⟨vacuum_entanglement_entropy c L ε hε, vacuum_annulus_width L ε hL hε⟩

end Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.modularGenerator_conformalUnitary_conj where
  formalizes @ "claim:the-modular-flow-of-the-conformally-excited-state-u-phi-omega-is-the-unitary-conjugate-of-the-vacuum-modular-flow-so-the-modular-generator-transforms-by-conjugation-and-the-flow-is-the-pushforward-of-the-boost",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular.conj_collisionStar"

zil attach Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.vacuum_entanglement_entropy where
  formalizes @ "claim:the-vacuum-conformal-map-is-the-identity-so-the-general-excited-state-cardy-tonni-entanglement-entropy-collapses-to-c-over-six-log-l-over-epsilon-the-rindler-half-space-entropy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.excitedEntanglementEntropy"

zil_file_contract physlib.conformalModularEntanglement where
  promises "The quantum construction of geometric modular flows deferred by ThermalGeometricModularFlow: the conformal unitaries U_phi that create the states Psi = U_phi Omega, and the entanglement entropy those states carry. Eq (2.4): a weight-Delta primary transforms with the conformal factor Omega = (u-prime v-prime)^{1/2} as Omega^{-Delta} = (u-prime v-prime)^{-Delta/2}. Eq (2.5): the modular flow of Psi = U_phi Omega is the conjugate of the vacuum's, U_Psi(s) = U_phi U_Omega(s) U_phi-dagger, so the modular ad-generator delta_K = [K,.] transforms by conjugation u delta_K(a) v = delta_{uKv}(u a v), reusing CollisionModular.conj_collisionStar; the excited-state modular flow is the pushforward of the boost. Appendix D: the Cardy-Tonni entanglement entropy S = (c/6) W of a state prepared on a Euclidean manifold conformally equivalent to an annulus of width W; the excited-state Rindler-wedge entropy is (c/6) log[(u(L)+v(L))/(u(epsilon)+v(epsilon))] (D.7), which for the identity vacuum map collapses to (c/6) log(L/epsilon) (D.4), the standard Rindler/Bekenstein half-space entropy, equal to (c/6) times the vacuum annulus width log(L/epsilon) of the map z_A = log z_R. For the thermal state at inverse temperature beta the map z_A = log(e^{2 pi z/beta} - 1) gives the exact width log(e^{2 pi L/beta}-1) - log(e^{2 pi epsilon/beta}-1) and entropy (c/6) times it, with beta the inverse temperature of the thermal geometric modular flow. Honest scope: the infinitesimal Virasoro form Psi = exp(i epsilon (L_n + L_{-n})) Omega (eq 1.9) is not formalized (no Virasoro algebra in the repository); the finite conformal-map route used here is the paper's own construction. The entropy formulas are the computed values of the entanglement entropy via the conformal map, not tied to an explicit von Neumann entropy of a CFT density matrix."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular.conj_collisionStar",
    "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular.modularGenerator"]
  forbids_substitutes [
    "the infinitesimal Virasoro construction Psi = exp(i epsilon (L_n + L_{-n})) Omega: no Virasoro algebra exists in the repository and only the finite conformal-map route is formalized",
    "identifying the computed 2d CFT entropy formula c/6 log(...) with the abstract von Neumann entropy of an explicit CFT density matrix, which is not constructed"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.conformalPrimaryFactor,
    Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.modularGenerator_conformalUnitary_conj,
    Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.vacuum_entanglement_entropy,
    Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.vacuum_annulus_width,
    Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.thermal_annulus_width,
    Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement.conformal_entanglement_synthesis]

#zil_horn_grounding physlib.conformalModularEntanglement

/- ZIL-END -/

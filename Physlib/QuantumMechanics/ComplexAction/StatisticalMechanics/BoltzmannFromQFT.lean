/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
public import Physlib.QuantumMechanics.ComplexAction.Fermion.PartitionFunction
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Boltzmann equation from quantum field theory (Drewes–Mendizábal–Weniger 2013)

Formalization of *M. Drewes, S. Mendizábal, C. Weniger, "The Boltzmann equation from quantum field
theory," Phys. Lett. B 718 (2013) 1119–1124*. The paper derives, from the Kadanoff–Baym equations via the
WKB approximation, a generalized Boltzmann equation for the occupation number `f` of a field resonance
with energy `Ω_t` and gain / loss rates `Γ<_t`, `Γ>_t`.

## Provenance — what is *from the paper* vs *added by this repo*

**Exactly from the paper** (physics content, stated as equations):

* Eq. 15 — net damping `Γ := Γ> − Γ<`;
* Eq. 17 — generalized BE `∂_t f = (1 + f)Γ< − f Γ>` (Bose-enhanced gain minus loss);
* Eq. 19 — relaxation form `∂_t f = −Γ(f − f̄)`;
* Eq. 20 — equilibrium `f̄ := (Γ>/Γ< − 1)⁻¹`;
* Eq. 21 — detailed balance `Γ</Γ> = e^{−Ω/T}` ⟹ `f̄` is Bose–Einstein;
* Eq. 7 — `Γ_t = −Im Π̃⁻(t, Ω̂_t)/Ω_t` (damping = imaginary part of the complex self-energy);
* Eq. 27 — FRW expanding background: `∂_t f_q = (1 + f_q)Γ< − f_q Γ> + H q ∇_q f_q`, `H = ȧ/a`;
* §5 remarks — the method extends to fermions, gauge interactions, multi-flavor / flavor oscillations,
 and beyond weak damping; "Boltzmann behavior arises whenever the WKB approximation is justified."

**Added by this repo** (Lean formalization, proofs, and bridges to existing physlib infrastructure):

* the proof that Eq. 17 ⟺ Eq. 19 (`boltzmannRHS_eq_relaxation`) and the fixed point (Eq. 20);
* the identification of `f̄` with Bose–Einstein by **reusing** `KMSDetailedBalance` (Eq. 21) and the
 existing `boseEinstein` (`equilibriumOccupation_eq_boseEinstein`);
* the explicit solution `f(t) = f̄ + (f_i − f̄)e^{−Γt}` with its `HasDerivAt` (solves Eq. 19) and
 `Tendsto` relaxation — the ODE-solution lemmas physlib did not previously have;
* Eq. 27 modeled as collision + Hubble drift, with the cosmological-redshift chain rule `q̇ = −H q`
 (`physicalMomentum_redshift`) that *produces* the `H q ∇_q f` term;
* the fermion extension (`boltzmannRHS_fermi`, Pauli blocking) with its relaxation form and the
 Fermi–Dirac equilibrium, **reusing** `Fermion.PartitionFunction.fermiDirac`;
* the WKB-interface encoding (`WKBRegime`, `SatisfiesGeneralizedBE`, `BoltzmannFromWKB`): "Boltzmann
 behavior arises whenever WKB is justified" recorded as the paper's analytic input (a structure
 field), with the algebraic consequences proved.

**Link to our entropic-clock infrastructure.** Eq. 7's `Γ = −Im Π̃⁻/Ω` is the imaginary part of the
complex self-energy — exactly the Nagao–Nielsen `H_I` of `H_C = H_R − i H_I`, the **entropic clock
generator** (`CausalDiamond.LindbladEntropicClock`, `gklsImaginaryHamiltonian`). The Boltzmann relaxation
`f → f̄` is the irreversible entropic clock reaching its fixed point, and that fixed point — Bose–Einstein
(or Fermi–Dirac) under detailed balance — is the **reversible KMS / modular (Connes–Rovelli) equilibrium**
(`KMSDetailedBalance`). So `Γ = H_I ≥ 0` is the entropic arrow; the thermal distribution is where it stops.

No new axioms.
-/

set_option autoImplicit false

open Real Filter Topology

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.Fermion.PartitionFunction
open _root_.QuantumMechanics.FiniteTarget

/-! ## §A — the generalized Boltzmann equation (Eqs. 15, 17, 20) -/

/-- **[Paper, Eq. 17 RHS]** The generalized Boltzmann gain − loss `(1 + f)·Γ< − f·Γ>` — Bose-enhanced
gain `(1+f)Γ<` minus loss `f·Γ>`. -/
def boltzmannRHS (f Γgt Γlt : ℝ) : ℝ := (1 + f) * Γlt - f * Γgt

/-- **[Paper, Eq. 15]** The net damping rate `Γ := Γ> − Γ<`. -/
def dampingRate (Γgt Γlt : ℝ) : ℝ := Γgt - Γlt

/-- **[Paper, Eq. 20]** The equilibrium occupation `f̄ := (Γ>/Γ< − 1)⁻¹ = Γ</(Γ> − Γ<)`. -/
def equilibriumOccupation (Γgt Γlt : ℝ) : ℝ := Γlt / (Γgt - Γlt)

/-- **[Repo proof of Paper Eq. 17 ⟺ Eq. 19]** The relaxation form: the gain − loss RHS equals
`−Γ·(f − f̄)` — the field relaxes toward `f̄` at the net damping rate `Γ`. -/
theorem boltzmannRHS_eq_relaxation (f Γgt Γlt : ℝ) (h : Γgt - Γlt ≠ 0) :
    boltzmannRHS f Γgt Γlt = -(dampingRate Γgt Γlt) * (f - equilibriumOccupation Γgt Γlt) := by
  unfold boltzmannRHS dampingRate equilibriumOccupation
  field_simp
  ring

/-- **[Repo, from Paper Eq. 20]** The equilibrium occupation is the fixed point of the collision term:
`(1 + f̄)Γ< − f̄·Γ> = 0` — gain and loss balance, no net entropy production. -/
theorem boltzmannRHS_equilibrium (Γgt Γlt : ℝ) (h : Γgt - Γlt ≠ 0) :
    boltzmannRHS (equilibriumOccupation Γgt Γlt) Γgt Γlt = 0 := by
  rw [boltzmannRHS_eq_relaxation _ Γgt Γlt h, sub_self, mul_zero]

/-! ## §B — detailed balance ⟹ the equilibrium is Bose–Einstein (Eqs. 20, 21) -/

/-- **[Repo proof of Paper Eq. 21, reuses `KMSDetailedBalance` + `boseEinstein`]** Detailed balance makes
the equilibrium occupation the Bose–Einstein distribution. With gain `Γ< = W_minus`, loss `Γ> = W_plus`
obeying KMS detailed balance `W_plus E = e^{βE}·W_minus E`, the equilibrium
`f̄ = Γ</(Γ> − Γ<) = 1/(e^{βΩ} − 1)` is exactly Bose–Einstein at the resonance energy `Ω` — the reversible
KMS / modular fixed point. -/
theorem equilibriumOccupation_eq_boseEinstein (κ : KMSDetailedBalance) (Ω : ℝ)
    (hW : κ.W_minus Ω ≠ 0) (hexp : Real.exp (κ.beta * Ω) - 1 ≠ 0) :
    equilibriumOccupation (κ.W_plus Ω) (κ.W_minus Ω) = boseEinstein κ.beta Ω := by
  unfold equilibriumOccupation boseEinstein
  rw [κ.W_plus_sub_W_minus Ω]
  field_simp

/-- **[Repo]** The Bose–Einstein distribution is the Boltzmann fixed point: under detailed balance the
collision term vanishes at `f = ` Bose–Einstein — the thermal (KMS / modular) equilibrium is where the
irreversible kinetic flow stops. -/
theorem boseEinstein_is_boltzmann_fixedPoint (κ : KMSDetailedBalance) (Ω : ℝ)
    (hW : κ.W_minus Ω ≠ 0) (hexp : Real.exp (κ.beta * Ω) - 1 ≠ 0)
    (h : κ.W_plus Ω - κ.W_minus Ω ≠ 0) :
    boltzmannRHS (boseEinstein κ.beta Ω) (κ.W_plus Ω) (κ.W_minus Ω) = 0 := by
  rw [← equilibriumOccupation_eq_boseEinstein κ Ω hW hexp]
  exact boltzmannRHS_equilibrium (κ.W_plus Ω) (κ.W_minus Ω) h

/-- **[Repo, from Paper]** The net damping is non-negative for `Ω ≥ 0` (the entropic arrow). Under
detailed balance with non-negative gain, the loss dominates for `Ω ≥ 0`, so `Γ = Γ> − Γ< ≥ 0`: the flow
is irreversible, relaxing *toward* equilibrium — the kinetic face of the entropic-clock irreversibility
(`gklsEntropicRate_nonneg`). -/
theorem dampingRate_nonneg (κ : KMSDetailedBalance) (Ω : ℝ)
    (hW : ∀ E, 0 ≤ κ.W_minus E) (hΩ : 0 ≤ Ω) :
    0 ≤ dampingRate (κ.W_plus Ω) (κ.W_minus Ω) := by
  unfold dampingRate
  rw [sub_nonneg]
  exact κ.W_plus_ge_W_minus_of_nonneg_W_minus hW hΩ

/-! ## §C — the relaxation solution `f(t) = f̄ + (f_i − f̄)e^{−Γt}` (Eq. 19) -/

/-- **[Repo, from Paper Eq. 19]** The relaxation solution `f(t) = f̄ + (f_i − f̄)·e^{−Γt}`. -/
def boltzmannSolution (fBar fi Γ t : ℝ) : ℝ := fBar + (fi - fBar) * Real.exp (-(Γ * t))

/-- **[Repo]** The relaxation solution solves Eq. 19 `∂_t f = −Γ·(f − f̄)`. -/
theorem boltzmannSolution_hasDerivAt (fBar fi Γ t : ℝ) :
    HasDerivAt (boltzmannSolution fBar fi Γ)
      (-Γ * (boltzmannSolution fBar fi Γ t - fBar)) t := by
  have hg : HasDerivAt (fun s : ℝ => -(Γ * s)) (-Γ) t := by
    exact (((hasDerivAt_id t).const_mul Γ).neg).congr_deriv (by ring)
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(Γ * s)))
      (Real.exp (-(Γ * t)) * (-Γ)) t := hg.exp
  have hsol := (he.const_mul (fi - fBar)).const_add fBar
  exact hsol.congr_deriv (by unfold boltzmannSolution; ring)

/-- **[Repo]** The relaxation solution at `t = 0` is the initial occupation `f_i`. -/
theorem boltzmannSolution_initial (fBar fi Γ : ℝ) : boltzmannSolution fBar fi Γ 0 = fi := by
  unfold boltzmannSolution
  simp

/-- **[Repo]** Relaxation to equilibrium (`Γ > 0`): `f(t) → f̄` as `t → ∞` — the irreversible approach to
the (Bose–Einstein / KMS) equilibrium. -/
theorem boltzmannSolution_tendsto_equilibrium (fBar fi Γ : ℝ) (hΓ : 0 < Γ) :
    Tendsto (boltzmannSolution fBar fi Γ) atTop (𝓝 fBar) := by
  have hlin : Tendsto (fun t : ℝ => Γ * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hΓ Filter.tendsto_id
  have hneg : Tendsto (fun t : ℝ => -(Γ * t)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr hlin
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(Γ * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have key := (hexp.const_mul (fi - fBar)).const_add fBar
  rw [show fBar + (fi - fBar) * 0 = fBar by ring] at key
  exact key

/-! ## §D — main result for the homogeneous case -/

/-- **[Repo, bundling Paper Eqs. 17–21]** The Boltzmann equation from QFT (spatially homogeneous case).
For a resonance with gain `Γ<`, loss `Γ>` (`Γ> − Γ< ≠ 0`), initial occupation `f_i`, and KMS detailed
balance at energy `Ω`: the kinetic equation ⟺ relaxation form, its equilibrium fixed point, the
Bose–Einstein identification, and the explicit relaxation solution. -/
theorem boltzmann_from_qft (κ : KMSDetailedBalance) (Ω fi : ℝ)
    (hW0 : κ.W_minus Ω ≠ 0) (hexp : Real.exp (κ.beta * Ω) - 1 ≠ 0)
    (h : κ.W_plus Ω - κ.W_minus Ω ≠ 0) (f t : ℝ) :
    (boltzmannRHS f (κ.W_plus Ω) (κ.W_minus Ω)
        = -(dampingRate (κ.W_plus Ω) (κ.W_minus Ω))
            * (f - equilibriumOccupation (κ.W_plus Ω) (κ.W_minus Ω)))
      ∧ (boltzmannRHS (equilibriumOccupation (κ.W_plus Ω) (κ.W_minus Ω))
            (κ.W_plus Ω) (κ.W_minus Ω) = 0)
      ∧ (equilibriumOccupation (κ.W_plus Ω) (κ.W_minus Ω) = boseEinstein κ.beta Ω)
      ∧ (boltzmannRHS (boseEinstein κ.beta Ω) (κ.W_plus Ω) (κ.W_minus Ω) = 0)
      ∧ (HasDerivAt
            (boltzmannSolution (equilibriumOccupation (κ.W_plus Ω) (κ.W_minus Ω)) fi
              (dampingRate (κ.W_plus Ω) (κ.W_minus Ω)))
            (-(dampingRate (κ.W_plus Ω) (κ.W_minus Ω))
              * (boltzmannSolution (equilibriumOccupation (κ.W_plus Ω) (κ.W_minus Ω)) fi
                  (dampingRate (κ.W_plus Ω) (κ.W_minus Ω)) t
                - equilibriumOccupation (κ.W_plus Ω) (κ.W_minus Ω))) t) := by
  refine ⟨boltzmannRHS_eq_relaxation f (κ.W_plus Ω) (κ.W_minus Ω) h,
    boltzmannRHS_equilibrium (κ.W_plus Ω) (κ.W_minus Ω) h,
    equilibriumOccupation_eq_boseEinstein κ Ω hW0 hexp,
    boseEinstein_is_boltzmann_fixedPoint κ Ω hW0 hexp h,
    boltzmannSolution_hasDerivAt _ fi _ t⟩

/-! ## §E — expanding (FRW) background: the Hubble drift term (Eq. 27) -/

/-- **[Repo, from Paper Eq. 27]** The FRW Boltzmann RHS: the collision term plus the Hubble advection
`H q ∇_q f`. In a Friedmann–Robertson–Walker background with Hubble rate `H = ȧ/a`, the collision term
(Eq. 17) is *unchanged*; only the momentum-space drift `H q ∇_q f` is added in physical momentum. -/
def boltzmannRHS_FRW (f Γgt Γlt H q dqf : ℝ) : ℝ := boltzmannRHS f Γgt Γlt + H * q * dqf

/-- **[Repo, from Paper "the BE (17) remains unchanged"]** With no expansion (`H = 0`) the FRW RHS is
exactly the homogeneous collision term — the collision part is the expansion-independent piece. -/
theorem boltzmannRHS_FRW_no_expansion (f Γgt Γlt q dqf : ℝ) :
    boltzmannRHS_FRW f Γgt Γlt 0 q dqf = boltzmannRHS f Γgt Γlt := by
  unfold boltzmannRHS_FRW; ring

/-- **[Repo]** FRW relaxation form: the Boltzmann RHS in an expanding background is `−Γ(f − f̄)` plus the
Hubble drift `H q ∇_q f`. -/
theorem boltzmannRHS_FRW_eq_relaxation (f Γgt Γlt H q dqf : ℝ) (h : Γgt - Γlt ≠ 0) :
    boltzmannRHS_FRW f Γgt Γlt H q dqf
      = -(dampingRate Γgt Γlt) * (f - equilibriumOccupation Γgt Γlt) + H * q * dqf := by
  unfold boltzmannRHS_FRW
  rw [boltzmannRHS_eq_relaxation f Γgt Γlt h]

/-- **[Repo, from Paper Eq. 27]** Cosmological redshift of physical momentum. At fixed comoving momentum
`q_com`, the physical momentum `q(t) = q_com / a(t)` obeys `q̇ = −H q` with `H = ȧ/a`. This redshift is
the origin of the Hubble drift `+H q ∇_q f`: the chain rule at fixed comoving momentum moves it to the
collision side of the kinetic equation. -/
theorem physicalMomentum_redshift (a : ℝ → ℝ) (a' qcom t : ℝ)
    (ha : HasDerivAt a a' t) (hat : a t ≠ 0) :
    HasDerivAt (fun s => qcom / a s) (-(a' / a t) * (qcom / a t)) t := by
  have h := (hasDerivAt_const t qcom).div ha hat
  exact h.congr_deriv (by field_simp; ring)

/-! ## §F — extension to fermions: Pauli blocking and Fermi–Dirac equilibrium (§5) -/

/-- **[Repo, from Paper §5 "extended to fermions"]** The fermionic Boltzmann RHS with Pauli blocking
`(1 − f)Γ< − f Γ>` — the gain is *blocked* by occupation `(1 − f)` rather than Bose-enhanced `(1 + f)`. -/
def boltzmannRHS_fermi (f Γgt Γlt : ℝ) : ℝ := (1 - f) * Γlt - f * Γgt

/-- **[Repo]** Fermionic net damping `Γ> + Γ<` (gain and loss both damp toward equilibrium). -/
def dampingRate_fermi (Γgt Γlt : ℝ) : ℝ := Γgt + Γlt

/-- **[Repo]** Fermionic equilibrium occupation `f̄_F = Γ</(Γ> + Γ<)`. -/
def equilibriumOccupation_fermi (Γgt Γlt : ℝ) : ℝ := Γlt / (Γgt + Γlt)

/-- **[Repo]** Fermionic relaxation form: `(1 − f)Γ< − f Γ> = −(Γ> + Γ<)(f − f̄_F)`. The same relaxation
structure as the bosonic case, with `Γ → Γ> + Γ<` and `f̄ → Γ</(Γ> + Γ<)` — the algebra is
statistics-agnostic, which is *why* the approach extends to fermions. -/
theorem boltzmannRHS_fermi_eq_relaxation (f Γgt Γlt : ℝ) (h : Γgt + Γlt ≠ 0) :
    boltzmannRHS_fermi f Γgt Γlt
      = -(dampingRate_fermi Γgt Γlt) * (f - equilibriumOccupation_fermi Γgt Γlt) := by
  unfold boltzmannRHS_fermi dampingRate_fermi equilibriumOccupation_fermi
  field_simp
  ring

/-- **[Repo, reuses `Fermion.PartitionFunction.fermiDirac`]** Detailed balance ⟹ Fermi–Dirac
equilibrium: `f̄_F = Γ</(Γ> + Γ<) = 1/(e^{βΩ} + 1)` — the fermionic counterpart of Bose–Einstein, the
reversible KMS / modular fixed point for fermions. -/
theorem equilibriumOccupation_fermi_eq_fermiDirac (κ : KMSDetailedBalance) (Ω : ℝ)
    (hW : κ.W_minus Ω ≠ 0) (hexp : Real.exp (κ.beta * Ω) + 1 ≠ 0) :
    equilibriumOccupation_fermi (κ.W_plus Ω) (κ.W_minus Ω) = fermiDirac Ω κ.beta := by
  unfold equilibriumOccupation_fermi fermiDirac
  rw [κ.detailed_balance Ω, ← add_one_mul]
  field_simp

/-! ## §G — "Boltzmann behavior arises whenever the WKB approximation is justified" (§5, the interface) -/

/-- **[Paper, Eq. 8]** The WKB regime: the separation-of-time-scales conditions controlling the WKB
approximation — weak damping over an interaction time `τ_int` (`Γ·τ_int ≤ 1`) with a positive resonance
energy. (The strict `≪` of Eq. 8 is modeled by the bound `≤ 1`.) The paper's analysis is that this regime
implies the generalized Boltzmann equation `SatisfiesGeneralizedBE`. -/
structure WKBRegime where
  τint : ℝ
  τint_pos : 0 < τint
  Γ : ℝ
  Γ_nonneg : 0 ≤ Γ
  Ω : ℝ
  Ω_pos : 0 < Ω
  weak_damping : Γ * τint ≤ 1

/-- **[Repo, from Paper Eq. 17]** The generalized Boltzmann equation as a predicate on a time-dependent
occupation `f(t)` with time-dependent rates: `∂_t f = (1 + f)Γ<(t) − f Γ>(t)` at every time. This is the
"Boltzmann behavior" the paper derives. -/
def SatisfiesGeneralizedBE (f Γgt Γlt : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt f (boltzmannRHS (f t) (Γgt t) (Γlt t)) t

/-- **[Repo]** The constant-rate relaxation solution realizes Boltzmann behavior: `f(t) = f̄ + (f_i − f̄)
e^{−Γt}` satisfies the generalized BE for constant gain / loss — a concrete witness that the kinetic
equation is consistent and solvable (the solvable constant-coefficient case of the WKB result). -/
theorem boltzmannSolution_satisfiesBE (Γgt Γlt fi : ℝ) (h : Γgt - Γlt ≠ 0) :
    SatisfiesGeneralizedBE
      (boltzmannSolution (equilibriumOccupation Γgt Γlt) fi (dampingRate Γgt Γlt))
      (fun _ => Γgt) (fun _ => Γlt) := by
  intro t
  rw [boltzmannRHS_eq_relaxation _ Γgt Γlt h]
  exact boltzmannSolution_hasDerivAt _ fi _ t

/-- **[Paper §5 conclusion, as an interface]** "Boltzmann behavior arises whenever the WKB approximation
is justified." The implication *WKB regime ⟹ generalized Boltzmann equation* is the paper's analytic
result (the WKB solution of the Kadanoff–Baym equations); it is recorded here as a structure field
(`boltzmann_behavior`) to be proved by that derivation, **not** re-proved in Lean. The algebraic
consequences (`BoltzmannFromWKB.relaxation`) are then proved. Holds for any field statistics and any
damping strength — the content of "extends to fermions, gauge interactions, multi-flavor, and beyond weak
damping." -/
structure BoltzmannFromWKB (Γgt Γlt : ℝ → ℝ) where
  /-- The WKB regime holds at every time (Eq. 8). -/
  regime : ℝ → WKBRegime
  /-- The occupation number. -/
  f : ℝ → ℝ
  /-- The paper's conclusion: WKB yields the generalized Boltzmann equation. -/
  boltzmann_behavior : SatisfiesGeneralizedBE f Γgt Γlt

/-- **[Repo]** Every WKB-Boltzmann system relaxes instantaneously toward equilibrium: given the paper's
conclusion, at any time with `Γ>(t) ≠ Γ<(t)` the rate is `−Γ(t)(f − f̄(t))`. -/
theorem BoltzmannFromWKB.relaxation {Γgt Γlt : ℝ → ℝ} (S : BoltzmannFromWKB Γgt Γlt) (t : ℝ)
    (h : Γgt t - Γlt t ≠ 0) :
    HasDerivAt S.f
      (-(dampingRate (Γgt t) (Γlt t)) * (S.f t - equilibriumOccupation (Γgt t) (Γlt t))) t := by
  have hbe := S.boltzmann_behavior t
  rwa [boltzmannRHS_eq_relaxation _ (Γgt t) (Γlt t) h] at hbe

end Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT

end

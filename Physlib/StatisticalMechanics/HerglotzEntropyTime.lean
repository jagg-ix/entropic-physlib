/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.Herglotz.Balance
public import Physlib.Thermodynamics.SecondLaw
public import Physlib.Relativity.Special.ProperTime
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Herglotz dissipation ⟹ entropic time

The Herglotz integrating-factor exponent `−A = −∫₀ᵗ (∂L/∂z) dω` is exactly the
**accumulated entropic proper time**, up to the `ℏ`-rescaling
`S_I = ℏ·τ_ent`. Under the Rayleigh / second-law sign convention `α ≤ 0`, this
module proves:

* `tauEnt` is monotone non-decreasing (`tauEnt_monotone_of_dissipation`);
* `S_I := ℏ·tauEnt` is monotone non-decreasing
  (`S_I_monotone_of_dissipation`);
* the Herglotz balance structure produces an
  `EntropyArrowWorldline` (`toEntropyArrowWorldline`).

The result: the entropic-time arrow of `Physlib.Thermodynamics.SecondLaw`
is **derived** from a Noether–Herglotz dissipative defect, which the paper
(Simoes–Colombo 2025) gives a variational origin for. Together with the
rescaled-invariant theorem of `Balance.lean`:

  *symmetry  ⇒  Noether–Herglotz balance  ⇒  positive dissipative defect
                ⇒  monotone S_I  ⇒  τ_ent = S_I/ℏ as a side-effect readout.*

The CPT-symmetric reversible sector (`α = 0`) recovers ordinary Noether
conservation (Remark 4.5, formalised in `Balance.lean`) and a frozen entropic
clock.


## References

- **Herglotz 1930** — *Berührungstransformationen (lectures)*
- **Lazo et al. 2018** — *Action principle for action-dependent Lagrangians*
- **Bartosiewicz & Torres 2008** — *Noether's theorem on time scales*
- **Gough, Ratiu, Smolyanov 2015** — *Noether's theorem for dissipative quantum semigroups*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.ClassicalMechanics.Herglotz.Balance Physlib.Thermodynamics.SecondLaw


namespace Physlib.ClassicalMechanics.Herglotz.Balance.HerglotzNoetherBalance

variable (B : HerglotzNoetherBalance)

/-! ## §1 — Entropic time and imaginary action -/

/-- **Entropic proper time** of the Herglotz balance: `τ_ent(t) := −(A(t) − A(0))`
= `∫₀ᵗ λ(ω) dω`, the integrating-factor exponent normalised to `τ_ent(0) = 0`.
Dimensionless. -/
def tauEnt (t : ℝ) : ℝ := -(B.A t - B.A 0)

/-- **Imaginary action** `S_I := ℏ·τ_ent` along the worldline. -/
def S_I (hbar : ℝ) (t : ℝ) : ℝ := hbar * B.tauEnt t

theorem hasDerivAt_tauEnt (t : ℝ) : HasDerivAt B.tauEnt (- B.alpha t) t := by
  unfold tauEnt
  exact ((B.hasDerivAt_A t).sub_const (B.A 0)).neg

theorem hasDerivAt_S_I (hbar : ℝ) (t : ℝ) :
    HasDerivAt (B.S_I hbar) (hbar * (- B.alpha t)) t := by
  unfold S_I
  exact (B.hasDerivAt_tauEnt t).const_mul hbar

@[simp] theorem tauEnt_at_zero : B.tauEnt 0 = 0 := by unfold tauEnt; simp

@[simp] theorem S_I_at_zero (hbar : ℝ) : B.S_I hbar 0 = 0 := by
  unfold S_I; simp

/-! ## §2 — Monotonicity from dissipation (the entropic arrow) -/

/-- **`τ_ent` is monotone** under the dissipation sign `α ≤ 0`: the integrated
non-negative rate `λ = −α` accumulates forward in `t`. -/
theorem tauEnt_monotone_of_dissipation (hα : ∀ t, B.alpha t ≤ 0) :
    Monotone B.tauEnt := by
  apply monotone_of_hasDerivAt_nonneg (f' := fun t => - B.alpha t)
  · exact B.hasDerivAt_tauEnt
  · intro t; show (0:ℝ) ≤ - B.alpha t; linarith [hα t]

/-- **`S_I` is monotone** under `α ≤ 0` and `ℏ > 0`. -/
theorem S_I_monotone_of_dissipation (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hα : ∀ t, B.alpha t ≤ 0) : Monotone (B.S_I hbar) := by
  apply monotone_of_hasDerivAt_nonneg (f' := fun t => hbar * (- B.alpha t))
  · exact B.hasDerivAt_S_I hbar
  · intro t; show (0:ℝ) ≤ hbar * (- B.alpha t)
    exact mul_nonneg hbar_pos.le (by linarith [hα t])

/-! ## §3 — Bridge into the entropic-time arrow layer -/

/-- **The Herglotz–Noether balance ⇒ entropy-arrow bridge.** A Herglotz balance
in the dissipation regime (`α ≤ 0`) instantiates the
`Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline` structure: the existing
"entropic time is a side effect" theorems (including
`time_order_iff_entropy_order`) now apply to a Noether-derived `S_I`. -/
def toEntropyArrowWorldline (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hα : ∀ t, B.alpha t ≤ 0) : EntropyArrowWorldline where
  ℏ := hbar
  ℏ_pos := hbar_pos
  S_I_along := B.S_I hbar
  τ_ent_along := B.tauEnt
  τ_ent_eq := fun t => (mul_div_cancel_left₀ (B.tauEnt t) (ne_of_gt hbar_pos)).symm
  S_I_monotone := fun {_ _} h => B.S_I_monotone_of_dissipation hbar hbar_pos hα h
  S_I_at_zero_nonneg := by simp

/-! ## §4 — Entropic chain bridge — classical side -/

open QuantumInfo.Finite SpaceTime in
/-- **Classical-side entropic chain bridge.**  A Herglotz–Noether balance in the
dissipation regime (`α ≤ 0`) simultaneously establishes the dissipation/2nd-law
direction *and* the geometric-recovery direction of the entropic chain, packaged
into one theorem:

* **(1)** monotone `S_I` under the dissipation regime (2nd law);
* **(2)** the resulting object is a genuine `EntropyArrowWorldline`
  (`toEntropyArrowWorldline`);
* **(3)** at the **Frozen-LRF** (`ρ = σ`), `SpaceTime.properTime` is exactly
  the total proper time `geometricInterval + entropicProperTimeMetric`.

The chain `α ≤ 0 ⇒ S_I monotone ⇒ EntropyArrowWorldline ⇒ properTime is the
ρ = σ residue of total proper time` is the classical analog of the Lindblad
bridge `lindblad_drives_entropic_time_at_frozen`.  No new axioms. -/
theorem herglotz_drives_entropic_time_at_frozen
    (hbar : ℝ) (hbar_pos : 0 < hbar) (hα : ∀ t, B.alpha t ≤ 0)
    {sd : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    Monotone (B.S_I hbar)
    ∧ (B.toEntropyArrowWorldline hbar hbar_pos hα).S_I_along = B.S_I hbar
    ∧ SpaceTime.properTime q p = totalProperTimeMetric U q p ρ ρ :=
  ⟨B.S_I_monotone_of_dissipation hbar hbar_pos hα,
   rfl,
   SpaceTime.properTime_eq_totalProperTimeMetric_at_frozen U q p ρ⟩

end Physlib.ClassicalMechanics.Herglotz.Balance.HerglotzNoetherBalance

/-! ## §5 — Bridge: Sergi-Ferrario non-Hamiltonian measure compression ↔ Herglotz dissipation

The `NonHamiltonianMeasureBridge` of `Physlib.Thermodynamics.SecondLaw`
(with constant phase-space compressibility `κ ≤ 0` from Sergi &
Ferrario 2001) and the `HerglotzDissipation` of
`Physlib.ClassicalMechanics.Herglotz.Basic` (with the Rayleigh
dissipation coefficient `α(t) = ∂L/∂z ≤ 0`) are *the same object* under
the identification

  `κ ↔ α`     (both phase-space-volume-contraction-rate, sign convention ≤ 0).

Both produce the same entropic-time arrow:
  * Sergi-Ferrario direct (`NonHamiltonianMeasureBridge.S_I_along`):
      `S_I(t) = −ℏ · κ · t`
  * Herglotz dissipation via this file's `tauEnt` / `S_I`:
      `λ(t) = −α = −κ`,
      `S_I(t) = ℏ · ∫₀ᵗ λ(ω) dω = −ℏ · κ · t`.

The bridge functions package the classical-mechanics (Herglotz) and
phase-space-volume (Sergi-Ferrario) viewpoints on the *same* classical
entropic-time arrow.  Together with `HerglotzNoetherBalance.ofConstantRate`
(in `Physlib.ClassicalMechanics.Herglotz.Instances`), the
`NonHamiltonianMeasureBridge` becomes a concrete instance of the full
Noether-Herglotz balance machinery.

-/

open Physlib.ClassicalMechanics.Herglotz.Basic
open Physlib.Thermodynamics.SecondLaw

namespace Physlib.ClassicalMechanics.Herglotz.Basic.HerglotzDissipation

/-- **Bridge constructor: Sergi-Ferrario `NonHamiltonianMeasureBridge` → Herglotz dissipation.**
The compressibility `κ ≤ 0` of the Sergi-Ferrario flow induces a Herglotz
dissipation coefficient `α := κ` (constant). -/
def ofNonHamiltonianMeasureBridge
    (M : NonHamiltonianMeasureBridge) :
    HerglotzDissipation where
  alpha := fun _ => M.κ
  alpha_nonpos := fun _ => M.κ_nonpos

/-- The Herglotz dissipation rate from a Sergi-Ferrario bridge is the
constant `λ = −κ ≥ 0`. -/
@[simp]
theorem ofNonHamiltonianMeasureBridge_lambda
    (M : NonHamiltonianMeasureBridge) (t : ℝ) :
    (ofNonHamiltonianMeasureBridge M).lambda t = -M.κ := rfl

end Physlib.ClassicalMechanics.Herglotz.Basic.HerglotzDissipation

namespace Physlib.ClassicalMechanics.Herglotz.Balance.HerglotzNoetherBalance

/-- **Bridge constructor: Sergi-Ferrario `NonHamiltonianMeasureBridge` →
Herglotz-Noether balance.**  Picks the constant-rate Herglotz balance
`α = κ` (constant) with initial Noether charge `J₀`.

The resulting balance satisfies:
  * `α(t) = κ`,
  * `J(t) = J₀ · exp(κ · t)`,
  * `A(t) = κ · t`,
  * `S_I(t) = −ℏ · κ · t` (same as `NonHamiltonianMeasureBridge.S_I_along`). -/
noncomputable def ofNonHamiltonianMeasureBridge
    (M : NonHamiltonianMeasureBridge) (J0 : ℝ) :
    HerglotzNoetherBalance :=
  { J := fun t => J0 * Real.exp (M.κ * t),
    alpha := fun _ => M.κ,
    A := fun t => M.κ * t,
    hasDerivAt_J := fun t => by
      have hlin : HasDerivAt (fun s : ℝ => M.κ * s) M.κ t := by
        simpa using (hasDerivAt_id t).const_mul M.κ
      have h1 : HasDerivAt (fun s => Real.exp (M.κ * s))
          (Real.exp (M.κ * t) * M.κ) t := hlin.exp
      have h2 : HasDerivAt (fun s => J0 * Real.exp (M.κ * s))
          (J0 * (Real.exp (M.κ * t) * M.κ)) t :=
        h1.const_mul J0
      convert h2 using 1
      ring,
    hasDerivAt_A := fun t => by
      simpa using (hasDerivAt_id t).const_mul M.κ }

/-- The Herglotz-Noether balance from a Sergi-Ferrario bridge has
`α(t) = κ` (constant). -/
@[simp]
theorem ofNonHamiltonianMeasureBridge_alpha
    (M : NonHamiltonianMeasureBridge) (J0 t : ℝ) :
    (ofNonHamiltonianMeasureBridge M J0).alpha t = M.κ := rfl

/-- The accumulator `A(t) = κ · t` for the bridge instance. -/
@[simp]
theorem ofNonHamiltonianMeasureBridge_A
    (M : NonHamiltonianMeasureBridge) (J0 t : ℝ) :
    (ofNonHamiltonianMeasureBridge M J0).A t = M.κ * t := rfl

/-- **Entropic-time round-trip equality.**  The entropic action
`S_I(t)` computed via the Herglotz route through the bridge equals the
direct `NonHamiltonianMeasureBridge.S_I_along t`. Both equal `−ℏ · κ · t`. -/
theorem ofNonHamiltonianMeasureBridge_S_I_eq
    (M : NonHamiltonianMeasureBridge) (J0 t : ℝ) :
    (ofNonHamiltonianMeasureBridge M J0).S_I M.ℏ t = M.S_I_along t := by
  unfold S_I tauEnt NonHamiltonianMeasureBridge.S_I_along
  simp [ofNonHamiltonianMeasureBridge_A]
  ring

/-- **EntropyArrowWorldline round-trip.**  Building the
`EntropyArrowWorldline` from the bridge via the Herglotz route yields a
worldline whose `S_I_along` agrees with the direct Sergi-Ferrario
constructor `EntropyArrowWorldline.ofNonHamiltonianMeasureBridge`.

Both classical routes (compressibility-of-phase-space and
Herglotz-dissipation-coefficient) decant into the same `EntropyArrowWorldline`
data at the level of `S_I_along`. -/
theorem ofNonHamiltonianMeasureBridge_toEntropyArrowWorldline_S_I_eq
    (M : NonHamiltonianMeasureBridge) (J0 : ℝ) (t : ℝ) :
    ((ofNonHamiltonianMeasureBridge M J0).toEntropyArrowWorldline
        M.ℏ M.ℏ_pos
        (fun _ => M.κ_nonpos)).S_I_along t
      = (EntropyArrowWorldline.ofNonHamiltonianMeasureBridge M).S_I_along t :=
  ofNonHamiltonianMeasureBridge_S_I_eq M J0 t

/-! #### Reduction to standard Noether conservation at `κ = 0`

In the Hamiltonian limit (κ = 0, i.e. the symplectic-flow regime — no
phase-space volume contraction, Liouville's theorem holds), the
Herglotz-Noether balance from the bridge reduces to **standard
Noether conservation**: `J̇ = 0`.

This recovers the classical theorem that for a symmetry of a
*conservative* (Hamiltonian) system, the corresponding Noether charge
is *conserved* — a special case of the more general
Noether-Herglotz balance `J̇ = α·J`.  When κ = 0, the dissipation
coefficient α = κ = 0, the rescaled invariant from
`rescaled_invariant_deriv_zero` reduces to `J` itself, and `J̇ = 0`
follows from the existing `hasDerivAt_J_zero_of_alpha_zero`. -/

/-- **Hamiltonian limit ⇒ standard Noether conservation**: when the
Sergi-Ferrario compressibility vanishes (`κ = 0`, the symplectic /
Liouville regime), the Herglotz-Noether balance from the bridge
satisfies `J̇ = 0` — the **standard Noether theorem** recovers the
conservative-system case. -/
theorem ofNonHamiltonianMeasureBridge_hasDerivAt_J_zero_of_κ_zero
    (M : NonHamiltonianMeasureBridge) (J0 : ℝ) (hκ : M.κ = 0) (t : ℝ) :
    HasDerivAt (ofNonHamiltonianMeasureBridge M J0).J 0 t :=
  (ofNonHamiltonianMeasureBridge M J0).hasDerivAt_J_zero_of_alpha_zero
    (fun _ => hκ) t

/-- **Hamiltonian limit ⇒ trivial entropic arrow at the Herglotz level**.
When κ = 0, the Herglotz-route entropic action `S_I` along the bridge
worldline vanishes identically — matching the direct
`NonHamiltonianMeasureBridge.S_I_along_eq_zero_of_κ_zero`. -/
@[simp]
theorem ofNonHamiltonianMeasureBridge_S_I_eq_zero_of_κ_zero
    (M : NonHamiltonianMeasureBridge) (J0 : ℝ) (hκ : M.κ = 0) (t : ℝ) :
    (ofNonHamiltonianMeasureBridge M J0).S_I M.ℏ t = 0 := by
  rw [ofNonHamiltonianMeasureBridge_S_I_eq M J0 t]
  exact M.S_I_along_eq_zero_of_κ_zero hκ t

end Physlib.ClassicalMechanics.Herglotz.Balance.HerglotzNoetherBalance


end

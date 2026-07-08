/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Physlib.Optics.TemporalDoubleSlit
public import Mathlib.Analysis.Real.Sqrt

/-!
# Algebraic bridge: visibility decay ↔ Bender decay fraction

This module records the **algebraic identity** between two
exponential decay laws that appear in different parts of
`physlib`:

  * `Physlib.Optics.TemporalDoubleSlit.visibility`:
        `V(S) := V_cl · exp(−λ_ent · S)`
    -- a candidate functional form for the fringe visibility
       observable in a temporal double-slit setup, as a function
       of slit separation `S` and an exponential decay rate
       `λ_ent`.

  * `Physlib.QuantumMechanics.ComplexAction.BenderIdentity.\
    benderDecayFraction`:
        `f(t, τ) := exp(−t/τ)`
    -- the squared-modulus decay fraction `|ψ(t)|²/|ψ(0)|²`
       predicted by the Bender 2008 starting equation for a
       Gamow state with lifetime `τ`.

The two formulas are the **same exponential** with the
substitution `t ↔ S`, `1/τ ↔ λ_ent`.  This module records that
identity at the algebraic level and connects the §E QIF lifetime
to the §C visibility decay rate via §G's `1/e` bridge.

## What this bridge does and does NOT claim

**Does claim:** for a state of definite Bender complex energy
`E = E_R − i·Ṡ_I` (an eigenstate of the imaginary part of the
Hamiltonian, equivalently a Gamow state with lifetime
`τ = ℏ/(2·Ṡ_I)`), the squared-modulus decay
`|ψ(S)|²/|ψ(0)|² = exp(−S/τ)` from §G has the same algebraic
form as the visibility decay `exp(−λ_ent·S)` from
TemporalDoubleSlit §C with the identification
`λ_ent = 1/τ = 2·Ṡ_I/ℏ`.

**Does NOT claim:** that any specific experimental visibility
observable IS governed by this Bender exponential.  Sessions 6–9
of the methodology trail (smoke log) document the case where
Tirole 2022 / Galiffi 2024 visibility data does **not** fit a
Bender-decay exponential — it sits in Pendry 2021's
photon-conservation regime instead, see
`Physlib.QuantumMechanics.ComplexAction.PendryPhotonConservation`
and `Physlib.Optics.MaterialTimescales` §E
(`IsPhotonConservationRegime`).

The bridge here is therefore an **algebraic identification of
functional form**, not an empirical claim.  Downstream code
that knows or assumes its system is in the Bender-decay regime
(rather than the Pendry photon-conservation regime) can use
the bridge to translate between the visibility-decay rate
`λ_ent` and the Bender lifetime `τ`.

## Reference

* Bender, Brody, Hook (2008) — see `BenderIdentity`.

* For Pendry-regime caveat: Pendry (2021), see
  `PendryPhotonConservation` and `MaterialTimescales` §E.

## See also: ETH information-theoretic route to the same
   exponential

The same exponential factor `exp(−λ_ent·S)` is reachable from
the published ETH canonical-form construction (D'Alessio et al.
2016 review):

* The canonical entropic proper time `τ_ent_canon := β_I · I/ℏ`
  takes an inverse-temperature-like parameter `β_I` and an
  information-density value `I(x)`.  The associated suppression
  factor is `exp(−τ_ent_canon)`.

* A variational extension states the chain
  `τ_ent(E) ↔ I(E) ↔ S_eff(E)` linking the information density
  to an effective-action functional.

Under the structure identification `β_I · I(x) = ℏ · λ_ent · S`,
the ETH suppression factor and the physlib visibility decay
exponential are the *same algebraic object* parametrised
differently:

* `λ_ent · S` (visibility decay) ≡ `τ_ent_canon(x)` (ETH).

So the four-path table of routes to `τ_ent` (Bender lifetime,
KMS thermal time, Pendry avalanche, ETH information density)
all reach the same exponential suppression structure formalised
here.  They differ only in *which* physical quantity is
identified with the rate.  See `Physlib.Optics.\
EntropicTimeOverview` §14 for the full list.

**External-origin disclaimer.**  An external Lean
formalisation of the ETH canonical-form and variational-rate
constructions exists outside physlib's dependency surface;
physlib has no import dependency on it.  References here
to the canonical form cite the published origin (D'Alessio et
al. 2016) rather than any external code path.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.VisibilityDecayFraction

open Physlib.QuantumMechanics.ComplexAction
open Physlib.Optics.TemporalDoubleSlit

/-- **Algebraic identity**: the visibility-decay law
`V(S) = V_cl · exp(−λ_ent·S)` equals `V_cl · benderDecayFraction
S (1/λ_ent)` under the substitution `τ ↔ 1/λ_ent`.

This is purely algebraic — both sides unfold to `V_cl ·
exp(−λ_ent·S)`.  The identity says nothing about whether any
specific experimental visibility IS governed by an exponential
decay; that empirical question is separate. -/
theorem visibility_eq_Vcl_mul_benderDecayFraction
    (V_cl lam_ent S : ℝ) (hlam : lam_ent ≠ 0) :
    visibility V_cl lam_ent S =
      V_cl * benderDecayFraction S (1 / lam_ent) := by
  unfold visibility benderDecayFraction
  congr 1
  congr 1
  field_simp

/-- **Bender-lifetime form of the visibility decay**: when
`λ_ent` is identified with `1/τ` (i.e., `τ` is the Bender
lifetime corresponding to the visibility decay rate), the
visibility at slit separation `S` equals `V_cl · exp(−S/τ)`. -/
theorem visibility_in_lifetime_form
    (V_cl τ S : ℝ) :
    visibility V_cl (1 / τ) S = V_cl * benderDecayFraction S τ := by
  unfold visibility benderDecayFraction
  congr 2
  ring

/-- **Bender lifetime at the visibility 1/e point**: if the
visibility-decay rate `λ_ent` equals `1/τ`, then at slit
separation `S = τ` the visibility has fallen to `V_cl ·
exp(−1)` — the standard `1/e` lifetime definition translated
to the slit-separation axis.

This composes `benderDecayFraction_at_lifetime` (§G) with
`visibility_in_lifetime_form` above. -/
theorem visibility_at_lifetime_eq_inv_e
    (V_cl τ : ℝ) (hτ : τ ≠ 0) :
    visibility V_cl (1 / τ) τ = V_cl * Real.exp (-1) := by
  rw [visibility_in_lifetime_form V_cl τ τ]
  rw [benderDecayFraction_at_lifetime hτ]

/-- **Boring-model recovery for the bridge**: at `λ_ent = 0`
(equivalently `τ → ∞`), the visibility stays at `V_cl`
independent of `S` — the standard-QM baseline that the
algebraic Bender bridge reduces to in the lossless limit.
Composes `visibility_at_zero_rate` with the bridge. -/
@[simp] theorem visibility_bridge_at_zero_rate
    (V_cl S : ℝ) :
    visibility V_cl 0 S = V_cl :=
  visibility_at_zero_rate V_cl S

/-! ## §D — PT-symmetric review procedure for optical double-slit visibility

The Markdown trail that cites
`PT -symmetric quantum mechanics-2312.17386v1.pdf` uses the Bender--Hook
review in a specific, Lean-safe way:

1. use the finite `2 × 2` gain/loss model as the canonical PT threshold,
   with real eigenvalue offset `sqrt(g² - b²)` in the unbroken sector;
2. treat the PT/C/similarity discussion as a *choice of positive metric
   frame*, not as a proof of a new optical law;
3. feed the resulting decay/rate parameter into the already-formalized
   temporal double-slit visibility law
   `V(S) = V_cl * exp(-lam_ent * S)`;
4. extract the experimentally relevant rate from the log-slope
   `log(V/V_cl) = -lam_ent * S`.

This section formalizes exactly that procedure.  It does not assert the
full PT spectral theorem, Stokes-wedge analysis, or construction of the
`C` operator; those are analytic/operator obligations.  What is checked
here is the finite gain/loss threshold and the algebraic route from a
PT-compatible rate to the optical-frequency double-slit observable.
-/

/-! ### §D.1 — The Bender--Hook `2 × 2` PT threshold -/

/-- The canonical PT gain/loss discriminant `g² - b²` for the matrix
`[[a + i b, g], [g, a - i b]]`.  The review's eigenvalues are
`E_± = a ± sqrt(g² - b²)` in the unbroken sector. -/
def ptGainLossDiscriminant (g b : ℝ) : ℝ := g ^ 2 - b ^ 2

/-- The finite-dimensional unbroken-PT condition for the canonical
gain/loss model: the discriminant is non-negative. -/
def IsUnbrokenPTGainLoss (g b : ℝ) : Prop :=
  0 ≤ ptGainLossDiscriminant g b

/-- The exceptional point of the canonical PT gain/loss model. -/
def IsExceptionalPTPoint (g b : ℝ) : Prop :=
  ptGainLossDiscriminant g b = 0

/-- The broken-PT condition for the canonical gain/loss model. -/
def IsBrokenPTGainLoss (g b : ℝ) : Prop :=
  ptGainLossDiscriminant g b < 0

/-- Real eigenvalue offset in the unbroken `2 × 2` PT model. -/
def ptEigenOffset (g b : ℝ) : ℝ :=
  Real.sqrt (ptGainLossDiscriminant g b)

/-- The real eigenvalue gap `E_+ - E_- = 2 sqrt(g² - b²)`. -/
def ptEigenGap (g b : ℝ) : ℝ :=
  2 * ptEigenOffset g b

/-- The upper eigenvalue `E_+ = a + sqrt(g² - b²)`. -/
def ptEigenvaluePlus (a g b : ℝ) : ℝ :=
  a + ptEigenOffset g b

/-- The lower eigenvalue `E_- = a - sqrt(g² - b²)`. -/
def ptEigenvalueMinus (a g b : ℝ) : ℝ :=
  a - ptEigenOffset g b

theorem unbrokenPTGainLoss_iff_sq_le_sq (g b : ℝ) :
    IsUnbrokenPTGainLoss g b ↔ b ^ 2 ≤ g ^ 2 := by
  unfold IsUnbrokenPTGainLoss ptGainLossDiscriminant
  constructor <;> intro h <;> linarith

theorem exceptionalPTPoint_iff_sq_eq_sq (g b : ℝ) :
    IsExceptionalPTPoint g b ↔ g ^ 2 = b ^ 2 := by
  unfold IsExceptionalPTPoint ptGainLossDiscriminant
  constructor <;> intro h <;> linarith

theorem brokenPTGainLoss_iff_sq_lt_sq (g b : ℝ) :
    IsBrokenPTGainLoss g b ↔ g ^ 2 < b ^ 2 := by
  unfold IsBrokenPTGainLoss ptGainLossDiscriminant
  constructor <;> intro h <;> linarith

theorem ptEigenGap_nonneg (g b : ℝ) :
    0 ≤ ptEigenGap g b := by
  unfold ptEigenGap ptEigenOffset
  positivity

theorem ptEigenGap_eq_zero_of_exceptional {g b : ℝ}
    (h : IsExceptionalPTPoint g b) :
    ptEigenGap g b = 0 := by
  unfold ptEigenGap ptEigenOffset
  rw [h, Real.sqrt_zero]
  ring

theorem ptEigenvalue_gap (a g b : ℝ) :
    ptEigenvaluePlus a g b - ptEigenvalueMinus a g b =
      ptEigenGap g b := by
  unfold ptEigenvaluePlus ptEigenvalueMinus ptEigenGap
  ring

/-! ### §D.2 — PT-compatible entropy-rate route to double-slit visibility -/

/-- A concrete procedure extracted from the Markdown/PDF analysis:

* `coupling` and `gainLoss` place the model in the unbroken finite PT sector;
* `entropyRate` is the imaginary-action production rate `Ṡ_I`;
* `widthFromRate entropyRate / hbar` is the optical visibility-decay rate;
* `S` is the temporal slit separation / time-gate separation.

The unbroken PT hypothesis records the Bender--Hook review input.  The
observable conclusions below are algebraic consequences of existing
`BenderIdentity` and `TemporalDoubleSlit` theorems. -/
structure PTDoubleSlitProcedure where
  coupling        : ℝ
  gainLoss        : ℝ
  V_cl            : ℝ
  entropyRate     : ℝ
  hbar            : ℝ
  S               : ℝ
  unbrokenPT      : IsUnbrokenPTGainLoss coupling gainLoss
  entropyRate_pos : 0 < entropyRate
  hbar_pos        : 0 < hbar
  V_pos           : 0 < V_cl
  S_pos           : 0 < S

namespace PTDoubleSlitProcedure

/-- The PT-compatible decay rate used by the optical visibility law:
`lam_ent = Γ / ℏ = widthFromRate(Ṡ_I) / ℏ`. -/
def visibilityRate (P : PTDoubleSlitProcedure) : ℝ :=
  widthFromRate P.entropyRate / P.hbar

theorem visibilityRate_pos (P : PTDoubleSlitProcedure) :
    0 < P.visibilityRate := by
  unfold visibilityRate
  exact div_pos ((widthFromRate_pos_iff P.entropyRate).2 P.entropyRate_pos) P.hbar_pos

/-- The optical visibility predicted by the PT-compatible entropy-rate
procedure.  The definition delegates to `TemporalDoubleSlit.visibility`. -/
def entropicVisibility (P : PTDoubleSlitProcedure) : ℝ :=
  visibility P.V_cl P.visibilityRate P.S

theorem entropicVisibility_eq_visibility (P : PTDoubleSlitProcedure) :
    P.entropicVisibility = visibility P.V_cl P.visibilityRate P.S := rfl

/-- The procedure really lands in the Bender exponential family:
the visibility is `V_cl` times the Bender decay fraction with lifetime
`1 / visibilityRate`. -/
theorem entropicVisibility_eq_benderDecayFraction
    (P : PTDoubleSlitProcedure) :
    P.entropicVisibility =
      P.V_cl * benderDecayFraction P.S (1 / P.visibilityRate) := by
  unfold entropicVisibility
  exact visibility_eq_Vcl_mul_benderDecayFraction
    P.V_cl P.visibilityRate P.S (ne_of_gt P.visibilityRate_pos)

/-- Log-slope extraction: the measured straight-line slope of
`log(V/V_cl)` against slit separation is the negative PT-compatible
visibility rate. -/
theorem log_visibility_ratio (P : PTDoubleSlitProcedure) :
    Real.log (P.entropicVisibility / P.V_cl) =
      -(P.visibilityRate * P.S) := by
  unfold entropicVisibility
  exact Physlib.Optics.TemporalDoubleSlit.log_visibility_ratio P.V_pos

/-- In the positive-rate regime the PT-compatible procedure predicts
strict visibility loss relative to the classical two-path visibility. -/
theorem entropicVisibility_lt_classical (P : PTDoubleSlitProcedure) :
    P.entropicVisibility < P.V_cl := by
  unfold entropicVisibility
  exact visibility_lt_classical_of_pos P.V_pos P.visibilityRate_pos P.S_pos

end PTDoubleSlitProcedure

/-! ### §D.3 — Planckian-rate route used by the optical-frequency Markdown -/

/-- The Planckian version of the same PT review procedure.  Here the rate
fed into the double-slit visibility law is the thermal/KMS rate
`k_B T_e / ℏ`, matching the optical-frequency Markdown's calibration
route for the ENZ temporal double-slit experiment. -/
structure PTPlanckianDoubleSlitProcedure where
  coupling   : ℝ
  gainLoss   : ℝ
  V_cl       : ℝ
  kB         : ℝ
  T_e        : ℝ
  hbar       : ℝ
  S          : ℝ
  unbrokenPT : IsUnbrokenPTGainLoss coupling gainLoss
  kB_pos     : 0 < kB
  T_e_pos    : 0 < T_e
  hbar_pos   : 0 < hbar
  V_pos      : 0 < V_cl
  S_pos      : 0 < S

namespace PTPlanckianDoubleSlitProcedure

/-- The Planckian/KMS rate `λ = k_B T_e / ℏ`. -/
def planckianVisibilityRate (P : PTPlanckianDoubleSlitProcedure) : ℝ :=
  thermalEntropicRate P.kB P.T_e P.hbar

theorem planckianVisibilityRate_pos (P : PTPlanckianDoubleSlitProcedure) :
    0 < P.planckianVisibilityRate :=
  thermalEntropicRate_pos P.kB_pos P.T_e_pos P.hbar_pos

/-- Visibility obtained by feeding the Planckian rate into the temporal
double-slit law. -/
def planckianVisibility (P : PTPlanckianDoubleSlitProcedure) : ℝ :=
  visibility P.V_cl P.planckianVisibilityRate P.S

theorem planckianVisibility_eq_visibility
    (P : PTPlanckianDoubleSlitProcedure) :
    P.planckianVisibility =
      visibility P.V_cl P.planckianVisibilityRate P.S := rfl

/-- Log-slope extraction for the Planckian route:
`log(V/V_cl) = -(k_B T_e / ℏ) S`. -/
theorem log_visibility_ratio
    (P : PTPlanckianDoubleSlitProcedure) :
    Real.log (P.planckianVisibility / P.V_cl) =
      -(P.planckianVisibilityRate * P.S) := by
  unfold planckianVisibility
  exact Physlib.Optics.TemporalDoubleSlit.log_visibility_ratio P.V_pos

/-- Positive Planckian rate gives strict visibility loss relative to the
classical two-path value. -/
theorem planckianVisibility_lt_classical
    (P : PTPlanckianDoubleSlitProcedure) :
    P.planckianVisibility < P.V_cl := by
  unfold planckianVisibility
  exact visibility_lt_classical_of_pos
    P.V_pos P.planckianVisibilityRate_pos P.S_pos

/-- The inverse rate used by the procedure is exactly the Planckian time
already defined in `TemporalDoubleSlit`. -/
theorem characteristicTimescale_planckianVisibilityRate
    (P : PTPlanckianDoubleSlitProcedure) :
    characteristicTimescale P.planckianVisibilityRate =
      planckianTime P.kB P.T_e P.hbar := by
  unfold characteristicTimescale planckianVisibilityRate thermalEntropicRate planckianTime
  field_simp [ne_of_gt P.kB_pos, ne_of_gt P.T_e_pos, ne_of_gt P.hbar_pos]

end PTPlanckianDoubleSlitProcedure

end Physlib.Optics.VisibilityDecayFraction

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Mathlib.Analysis.Calculus.Deriv.Inv
meta import Zil

/-!
# Verlinde's derivation of Newton's law of gravity (`F = G·M·m/R²`)

Port of the **central derivation of Newton's law of gravity** from
Verlinde's original paper:

> Verlinde, E. *On the Origin of Gravity and the Laws of Newton*,
> arXiv:1001.0785v1, January 2010.
> Sourced from `arXiv-1001.0785v1 (5)/NewtonPaper.tex`
> §2.2 "Newton's law of gravity" (lines 313-358 of source).

This complements the **Newton's second law `F = m·a`** derivation
already in `VerlindeEntropicForce.lean` (commit `74bbac9d`).
Together, those two derivations recover both Newton laws from
information-theoretic / thermodynamic primitives.

## Verlinde's derivation chain (Eqs from NewtonPaper.tex)

1. **Bit count on holographic screen** (Eq. `bits`, line 323):

  `N = A·c³/(G·ℏ)`

  where `A` is the area of the screen, `G` is (to be identified
  with) Newton's constant.

2. **Equipartition** (Eq. `equipartition`, line 331):

  `E = (1/2)·N·k_B·T`

3. **Mass-energy equivalence** (Eq. `E=Mc²`, line 337):

  `E = M·c²`

4. **Verlinde displacement entropy** (Eq. `basiclaw`, line 279,
   already in `VerlindeEntropicForce.lean`):

  `ΔS = 2π·k_B·m·c·Δx/ℏ`

5. **Entropic-force relation** (Eq. `entropic`, line 293):

  `F · Δx = T · ΔS`

6. **Sphere area** (line 350):

  `A = 4π·R²`

Combining (1)-(6), the temperature is

  `T = M·G·ℏ / (2π·R²·c·k_B)`,

and the entropic-force work `F·Δx = T·ΔS` becomes

  `F · Δx = G·M·m·Δx / R²`.

Dividing by `Δx` gives **Newton's law of gravity** (Eq. `Newtonslaw`,
line 353):

  `F = G·M·m/R²`.

## Contents


* `holographicBits A G ℏ c := A·c³/(G·ℏ)` — Verlinde Eq. bits.
* `holographicBits_pos`.


* `verlindeGravityTemperature M G ℏ c R kB` — the temperature on
  a spherical screen of radius `R` containing mass `M`.
* `verlindeGravityTemperature_eq` — explicit form
  `M·G·ℏ / (2π·R²·c·k_B)`.


* **`newton_law_of_gravity_from_verlinde`** — the central result:
  combining all six steps gives `F = G·M·m/R²`.

## Honest scope

The derivation uses the **equipartition assumption** (Eq. 4),
which Verlinde 2011 §2.3 acknowledges is "perhaps the least
obvious assumption" — it holds strictly for free systems and is
a coarse-graining for general systems.  The port carries
equipartition as a *hypothesis* (via the temperature formula),
not as an axiomatic claim.  Consumers wishing to challenge or
generalise the derivation can substitute alternative
temperature formulas.

## References

* Verlinde 2011 *On the Origin of Gravity and the Laws of Newton*,
  JHEP 04, 029 (2011), arXiv:1001.0785.  Original source:
  `arXiv-1001.0785v1 (5)/NewtonPaper.tex`.
* Bekenstein 1973 — black hole entropy and the original motivation
  for Eq. `basiclaw`.
* Unruh 1976 — Unruh temperature underpinning the `F = m·a`
  companion derivation.
* `Physlib/Thermodynamics/VerlindeEntropicForce.lean` — companion
  file with the `F = m·a` derivation (Newton's 2nd law).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics


/-- **Equipartition energy** (Verlinde Eq. `equipartition`, line 331):

  `E_equipartition := (1/2) · N · k_B · T`.

The average energy per holographic bit at temperature `T`,
assuming `N` bits and equipartition (energy spread evenly across
degrees of freedom).  Verlinde 2011 acknowledges this is the most
restrictive assumption of the derivation (line 366). -/
def equipartitionEnergy (N kB T : ℝ) : ℝ := (1 / 2) * N * kB * T

@[simp] lemma equipartitionEnergy_def (N kB T : ℝ) :
    equipartitionEnergy N kB T = (1 / 2) * N * kB * T := rfl

/-- **Mass-energy equivalence** (Verlinde Eq. `E=Mc²`, line 337):

  `E_mass-energy := M · c²`.

Einstein 1905's mass-energy equivalence; the rest-energy of mass
`M` is `M·c²`. -/
def massEnergyEquivalence (M c : ℝ) : ℝ := M * c^2

@[simp] lemma massEnergyEquivalence_def (M c : ℝ) :
    massEnergyEquivalence M c = M * c^2 := rfl

/-- **Sphere area**: `A = 4π · R²`.

Used as the area of a spherical holographic screen of radius `R`. -/
def sphereArea (R : ℝ) : ℝ := 4 * Real.pi * R^2

@[simp] lemma sphereArea_def (R : ℝ) :
    sphereArea R = 4 * Real.pi * R^2 := rfl

/-- Sphere area is positive at positive `R`. -/
lemma sphereArea_pos {R : ℝ} (hR : 0 < R) : 0 < sphereArea R := by
  unfold sphereArea
  have : (0 : ℝ) < 4 * Real.pi := by positivity
  positivity


/-- **Holographic bit count** on a screen of area `A`:

  `N := A · c³ / (G · ℏ)`.

Verlinde 2011 Eq. (8): the number of bits on a holographic
screen of area `A`, with `G` to be identified with Newton's
constant.  "The only assumption made here is that the number of
bits is proportional to the area." (Verlinde 2011 line 327). -/
def holographicBits (A G ℏ c : ℝ) : ℝ := A * c^3 / (G * ℏ)

/-- Definitional unfolding. -/
@[simp] lemma holographicBits_def (A G ℏ c : ℝ) :
    holographicBits A G ℏ c = A * c^3 / (G * ℏ) := rfl

/-- **`holographicBits` is positive at positive `A, G, ℏ, c`**. -/
lemma holographicBits_pos
    {A G ℏ c : ℝ} (hA : 0 < A) (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c) :
    0 < holographicBits A G ℏ c := by
  unfold holographicBits
  apply div_pos
  · positivity
  · positivity


/-- **Verlinde temperature on a spherical screen** of radius `R`
containing mass `M` inside.

Derived from equipartition `E = (1/2)·N·k_B·T` (Verlinde Eq. 9)
combined with `E = M·c²` (Eq. 10), with the holographic bit count
`N` on a sphere of area `A = 4π·R²`:

  `T = M·G·ℏ / (2π·R²·c·k_B)`.

The factor of `2π·R²` (not `4π·R²`) comes from the equipartition's
factor of `1/2` halving the area dependence. -/
def verlindeGravityTemperature (M G ℏ c R kB : ℝ) : ℝ :=
  M * G * ℏ / (2 * Real.pi * R^2 * c * kB)

/-- Definitional unfolding. -/
@[simp] lemma verlindeGravityTemperature_def (M G ℏ c R kB : ℝ) :
    verlindeGravityTemperature M G ℏ c R kB =
      M * G * ℏ / (2 * Real.pi * R^2 * c * kB) := rfl

/-- **`verlindeGravityTemperature` is positive** at positive inputs. -/
lemma verlindeGravityTemperature_pos
    {M G ℏ c R kB : ℝ}
    (hM : 0 < M) (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hR : 0 < R) (hkB : 0 < kB) :
    0 < verlindeGravityTemperature M G ℏ c R kB := by
  unfold verlindeGravityTemperature
  apply div_pos
  · positivity
  · positivity


/-- **Step 1 of derivation chain**: equating the equipartition energy
with the mass-energy gives the temperature `T = 2·M·c²/(N·k_B)`.

Algebraic content: `(1/2)·N·k_B·T = M·c²` ⟹ `T = 2·M·c²/(N·k_B)`. -/
lemma temperature_from_equipartition_and_massEnergy
    {N kB T M c : ℝ}
    (hN : 0 < N) (hkB : 0 < kB)
    (h_balance : equipartitionEnergy N kB T = massEnergyEquivalence M c) :
    T = 2 * M * c^2 / (N * kB) := by
  unfold equipartitionEnergy massEnergyEquivalence at h_balance
  have hNkB_ne : N * kB ≠ 0 := by positivity
  rw [eq_div_iff hNkB_ne]
  linear_combination 2 * h_balance

/-- **Step 2 of derivation chain**: substituting `N = A·c³/(G·ℏ)` into
`T = 2·M·c²/(N·k_B)` gives `T = 2·M·G·ℏ / (A·c·k_B)`. -/
lemma temperature_from_holographicBits
    {A G ℏ c M kB : ℝ}
    (hA : 0 < A) (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c) (hkB : 0 < kB) :
    2 * M * c^2 / (holographicBits A G ℏ c * kB) =
      2 * M * G * ℏ / (A * c * kB) := by
  unfold holographicBits
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  field_simp

/-- **Step 3 of derivation chain**: substituting `A = 4π·R²` into
`T = 2·M·G·ℏ / (A·c·k_B)` gives `T = M·G·ℏ / (2π·R²·c·k_B)`, which
is the `verlindeGravityTemperature`. -/
lemma temperature_from_sphereArea
    {G ℏ c M R kB : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hkB : 0 < kB) :
    2 * M * G * ℏ / (sphereArea R * c * kB) =
      verlindeGravityTemperature M G ℏ c R kB := by
  unfold sphereArea verlindeGravityTemperature
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hR2_ne : R^2 ≠ 0 := by positivity
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  have hπ_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Full-chain derivation** of `verlindeGravityTemperature` from the
three primitive equations.

Given:
* `equipartitionEnergy N k_B T = massEnergyEquivalence M c` (balance),
* `N = holographicBits A G ℏ c` (bit count),
* `A = sphereArea R` (spherical screen),

the temperature `T` equals `verlindeGravityTemperature M G ℏ c R kB`.

This composes Steps 1-3 into a single statement: the three primitive
Verlinde equations (equipartition + E=Mc² + holographic bits + sphere)
jointly determine the temperature on the holographic screen. -/
lemma verlindeGravityTemperature_from_primitives
    {N A G ℏ c M R kB T : ℝ}
    (hN : 0 < N) (hA : 0 < A) (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hR : 0 < R) (hkB : 0 < kB)
    (h_balance : equipartitionEnergy N kB T = massEnergyEquivalence M c)
    (hN_eq : N = holographicBits A G ℏ c)
    (hA_eq : A = sphereArea R) :
    T = verlindeGravityTemperature M G ℏ c R kB := by
  rw [temperature_from_equipartition_and_massEnergy hN hkB h_balance]
  rw [hN_eq, temperature_from_holographicBits hA hG hℏ hc hkB]
  rw [hA_eq, temperature_from_sphereArea hR hc hkB]


/-- **:Newton's law of gravity from Verlinde's principles**.

Substituting:

* `T := verlindeGravityTemperature M G ℏ c R kB` (temperature on
  the spherical screen),
* `ΔS := verlindeDisplacementEntropy ℏ kB m c Δx` (Verlinde
  displacement entropy for a probe mass `m` at displacement `Δx`),

into the entropic-force formula `F = T · ΔS / Δx`, the `ℏ`, `kB`,
`c`, `R²` (in the temperature) and `Δx` (in the entropy) all
combine and cancel cleanly, leaving:

  `F = G · M · m / R²`.

This is **Newton's law of universal gravitation** (Verlinde 2011
Eq. `Newtonslaw`, line 353) recovered from:

* Holographic bit count (Eq. bits / §1 here).
* Equipartition (Eq. equipartition).
* Mass-energy equivalence (Eq. E=Mc²).
* Verlinde displacement entropy (Eq. basiclaw,
  `VerlindeEntropicForce.lean`).
* Entropic-force formula (Eq. entropic,
  `VerlindeEntropicForce.lean`).

Combined with the **Newton's second law** derivation
`F = m·a` already in `VerlindeEntropicForce.lean`
(commit `74bbac9d`), this completes Verlinde's program: **both
Newton's laws are derivable from information-theoretic /
thermodynamic primitives**. -/
lemma newton_law_of_gravity_from_verlinde
    {M G ℏ c R kB m Δx : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c)
    (hR : 0 < R) (hΔx : 0 < Δx) :
    verlindeEntropicForce
        (verlindeGravityTemperature M G ℏ c R kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx)
        Δx
      = G * M * m / R^2 := by
  unfold verlindeEntropicForce verlindeGravityTemperature
    verlindeDisplacementEntropy
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hR2_ne : R^2 ≠ 0 := by positivity
  have hΔx_ne : Δx ≠ 0 := ne_of_gt hΔx
  have hπ_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **[The conservative force of the Newton potential]** `V(r) = −GMm/r` has
`dV/dr = GMm/r²` — the classical-mechanics face `F = −dV/dx` (Carroll, *Biggest Ideas* Eq. 3.3,
`carroll-equations-lean` `Chapter03.eq_3_3`) applied to the gravitational potential: the magnitude
of the attractive inverse-square force, as a genuine derivative statement. -/
theorem newtonPotential_hasDerivAt (G M m : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => -(G * M * m / s)) (G * M * m / r ^ 2) r := by
  have h := (hasDerivAt_inv hr).const_mul (-(G * M * m))
  have h2 : HasDerivAt (fun s : ℝ => -(G * M * m / s)) (-(G * M * m) * -(r ^ 2)⁻¹) r :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by ring)
  have hval : -(G * M * m) * -(r ^ 2)⁻¹ = G * M * m / r ^ 2 := by field_simp
  rw [← hval]
  exact h2

/-- **[The classical conservative force IS the Verlinde entropic force]** the derivative of the
Newton potential at the screen radius `R` — the textbook `F = −dV/dx` of classical mechanics
(Carroll Ch. 3) — equals the entropic force `T·ΔS/Δx` evaluated at the Verlinde screen temperature
(equipartition over `N = holographicBits` — `G` in its area-per-bit role) with the displacement
entropy. Classical gravity's conservative force and the information-theoretic entropic force are
one identity: the Carroll classical face welded onto the holographic-`G` / entropic-time chain
(`bekensteinTauEnt_eq_holographicBits_div_four` ties the same bits to entropic time). -/
theorem newtonPotential_deriv_eq_verlinde_entropicForce
    {M G ℏ c R kB m Δx : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) (hΔx : 0 < Δx) :
    HasDerivAt (fun s : ℝ => -(G * M * m / s))
      (verlindeEntropicForce
        (verlindeGravityTemperature M G ℏ c R kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx)
        Δx) R := by
  rw [newton_law_of_gravity_from_verlinde hℏ hkB hc hR hΔx]
  exact newtonPotential_hasDerivAt G M m hR.ne'

/-! ## ZIL metadata -/

/-- Link found by `#zil_link`: `comptonTemperature` is `massEnergyEquivalence` under `m ↦ M` with conversion `kB^-1` and prescription `× 1/2 · π^-1`. -/
theorem comptonTemperature_eq_massEnergyEquivalence_scaled (m c kB : ℝ) :
    Physlib.Thermodynamics.comptonTemperature m c kB
      = ((1 / 2 : ℝ) / (kB * Real.pi)) * Physlib.Thermodynamics.massEnergyEquivalence m c := by
  unfold Physlib.Thermodynamics.comptonTemperature Physlib.Thermodynamics.deBroglieTemperature
    Physlib.Thermodynamics.massEnergyEquivalence
  ring

/- ZIL-BEGIN -/

/- `zil_theorem_intent` for `newton_law_of_gravity_from_verlinde` already lives in
`Physlib.Meta.EntropicSpineZil` (spine-tracked); only the attach edges are added here. -/
zil attach newton_law_of_gravity_from_verlinde where
  formalizes @ "claim:newton-gravity-from-equipartition-on-holographic-bits",
  requires @ "claim:screen-equipartition-derived-from-n-classical-quadratic-degrees-of-freedom",
  requires @ "assumption:verlinde-displacement-entropy-ansatz",
  supported_by @ "paper:verlinde-2010-emergent-gravity",
  caveat @ "claim:g-enters-through-holographic-bit-count-not-derived-value"

zil attach newtonPotential_hasDerivAt where
  formalizes @ "claim:newton-potential-conservative-force-inverse-square",
  supported_by @ "book:carroll-biggest-ideas-space-time-motion",
  caveat @ "claim:classical-mechanics-face-carroll-eq-3-3-applied-to-gravity"

zil_theorem_intent newtonPotential_deriv_eq_verlinde_entropicForce where
  at_level bridge_theorem
  must_mention [verlindeEntropicForce, verlindeGravityTemperature]

zil attach newtonPotential_deriv_eq_verlinde_entropicForce where
  formalizes @ "claim:classical-conservative-force-equals-verlinde-entropic-force",
  requires @ "claim:newton-gravity-from-equipartition-on-holographic-bits",
  requires @ "claim:newton-potential-conservative-force-inverse-square",
  supported_by @ "paper:verlinde-2010-emergent-gravity",
  supported_by @ "book:carroll-biggest-ideas-space-time-motion",
  caveat @ "claim:screen-radius-evaluation-not-a-field-equation"

zil_file_contract physlib.verlindeNewtonGravity where
  promises "Verlinde's derivation of Newtonian gravity on existing carriers: the holographic bit count with G in its area-per-bit role, screen equipartition and mass-energy fixing the screen temperature, the entropic force at that temperature equal to G M m over R squared, the classical conservative-force face of the Newton potential as a genuine derivative statement from Carroll's equations, and the capstone identity that the classical conservative force IS the Verlinde entropic force at the screen."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.holographicBits",
    "lean:Physlib.Thermodynamics.verlindeEntropicForce",
    "lean:Physlib.Relativity.SemiClassical.hawkingTemperature",
    "lean:Physlib.Relativity.SemiClassical.bekensteinTauEnt"]
  forbids_substitutes ["a derivation of Einstein field equations claimed from the Newtonian identity",
    "a first-principles value of G, which enters through the holographic bit count",
    "relativistic or field-theoretic dynamics claimed from screen-radius evaluation"]
  witnessed_by [newton_law_of_gravity_from_verlinde, newtonPotential_hasDerivAt,
    newtonPotential_deriv_eq_verlinde_entropicForce]

/- ZIL-END -/

end Physlib.Thermodynamics

end

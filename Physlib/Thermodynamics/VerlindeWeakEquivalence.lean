/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.VerlindeNewtonGravity

meta import Zil

/-!
# The weak equivalence principle as a theorem of the entropic force

In standard physics `m_i = m_g` is an *unexplained empirical input*: Newton's `F = m_i a` and
`F = −GMm_g/r²` carry two conceptually distinct masses, their ratio is measured (torsion balances,
lunar laser ranging, MICROSCOPE) and found to be `1`, and Einstein *elevates* the coincidence to a
principle.  Nothing in Newtonian mechanics or quantum mechanics derives it.

In the entropic-force derivation already formalized here, it is a **theorem** — and the reason is
visible in the statements of the two existing lemmas:

* `newton_second_law_from_verlinde_unruh` :
  `F(T_Unruh(a), ΔS_V(m), Δx) = m·a` — inertia,
* `newton_law_of_gravity_from_verlinde` :
  `F(T_grav(M,R), ΔS_V(m), Δx) = GMm/R²` — weight,

**consume the same `verlindeDisplacementEntropy ℏ kB m c Δx`.**  The test body enters both laws
through one symbol, the `m` of the displacement entropy `ΔS = 2πk_B mc Δx/ħ` — one Compton
wavelength of displacement costs `2πk_B` regardless of what the body is made of.  There is no
second mass anywhere in the derivation for a violation to live in: `m_i ≡ m_g` because both are
*names for the same coefficient of the same entropy law*.

What this module adds is the keystone the two lemmas leave implicit:

* **§A** — the temperature matching: the local Unruh temperature equals the screen's equipartition
  temperature **iff** `a = GM/R²` (`unruh_eq_gravityTemperature_iff`).  The mass does not appear:
  the free-fall acceleration selected by thermal equilibrium is universal.
* **§B** — the two readings agree on the nose: at the matched acceleration, `m·a = GMm/R²` with the
  *same* `m` on both sides (`inertial_reading_eq_gravitational_reading`) — the textbook
  `m_i a = GM m_g/r²` slide, with `m_i` and `m_g` provably one symbol.
* **§C** — the measured observable: the Eötvös differential acceleration of *any* two bodies is
  exactly zero (`eotvos_null`).  This is what torsion balances and MICROSCOPE measure, and here it
  is a theorem with **no free parameter between the postulate and the observable**.

**Why this is the solid ground the audit kept failing to find.**  Under the plan's C3′ test —
*name the hypothesis no measurement constrains* — every prior target failed.  This one passes: the
load-bearing hypothesis is the displacement-entropy law, already flagged in the graph as the one
genuine Verlinde postulate, and the WEP experiments constrain **it, directly**.  `ΔS` depends on
`m` alone, so composition-dependent free fall is *structurally impossible*; a nonzero Eötvös ratio
at any precision would falsify the postulate outright, with nothing to absorb it.  MICROSCOPE's
`η(Ti,Pt) = (−1.5 ± 2.7)×10⁻¹⁵` is therefore not merely "consistent with" this framework — it is a
`10⁻¹⁵`-level direct test of its central gravitational assumption, passed.  It does not
discriminate the framework from pure GR (both predict `η = 0` exactly); it discriminates it from
generic beyond-standard-model physics, which allows composition-dependent violations at some level.

**The thermal face, and the black-hole arc's actual content.**  The same file that derives inertia
proves `unruhTemperature_eq_hawkingTemperature`: one `2π` normalization shared between acceleration
(flat) and horizon (curved).  `JacobsonClausiusEinstein.einstein_from_clausius` consumes that same
normalization (`hUnruh : T_U = κ/2π`) to output the Einstein equation.  So the `2π` is cross-checked
across inertia, horizon and field equation *by theorems* — if the Unruh and Hawking normalizations
differed, `F = ma` and Einstein's coefficient would break together.  That consistency, not the
one-bit mass numerology, is where the black-hole material genuinely supports the framework.

Scope, honestly.  Conditional on the displacement-entropy postulate (the graph's flagged Verlinde
ansatz; equipartition, by contrast, is *derived* — `verlinde_equipartition_from_NDOF`) and the
holographic bit count; nonrelativistic, static spherical screen.  This is the **weak** EP: the
strong EP (self-gravitating bodies, Nordtvedt, LLR at `~10⁻⁴`) is not claimed: per the GR-closure
audit (`analysis/empirical-discrimination-plan.md` §13) the Cauchy architecture exists as theorems,
but its Lipschitz premise at the `Ḣ¹` carrier is an explicit analytic input, and a Nordtvedt-type
self-energy analysis is new work on top of it.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics

/-! ### §A — thermal equilibrium selects a universal free-fall acceleration -/

/-- **The Unruh temperature matches the screen temperature iff `a = GM/R²`.**  Both temperatures
carry the same `ħ/(2πk_B c)` prefactor, so the matching condition is exactly Newtonian free fall —
and the test mass appears nowhere: the acceleration selected by thermal equilibrium at the screen
is the same for every body. -/
theorem unruh_eq_gravityTemperature_iff {M G ℏ c R kB a : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) :
    unruhTemperature ℏ kB c a = verlindeGravityTemperature M G ℏ c R kB
      ↔ a = G * M / R ^ 2 := by
  unfold unruhTemperature verlindeGravityTemperature
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · intro h
    field_simp at h
    field_simp
    nlinarith [h]
  · intro h
    rw [h]
    field_simp

/-- **The Verlinde screen temperature equals the Compton temperature exactly at
`GM/R² = mc³/ℏ`** — the radius at which the gravitational acceleration at the screen is the
Compton acceleration, i.e. the screen is as hot as the particle's own rest-energy scale
(`R² = GMℏ/(mc³)`).  Reported by `#zil_unify_diagram` as an underived composite with both
flanks proven through the Unruh carrier, and proven here *as* that composition.  Carries `G`:
exactly one nat off under the holographic typing, like every edge into the gravity vertex
(WEP depth gate §13). -/
theorem gravity_eq_comptonTemperature_iff {M G ℏ c R kB m : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) :
    verlindeGravityTemperature M G ℏ c R kB = comptonTemperature m c kB
      ↔ G * M / R ^ 2 = m * c ^ 3 / ℏ := by
  rw [← (unruh_eq_gravityTemperature_iff hℏ hkB hc hR).mpr rfl]
  exact unruh_eq_comptonTemperature_iff hℏ hkB hc

/-- **The Verlinde screen temperature equals the de Broglie temperature exactly at
`GM/R² = E·c/ℏ`** — the general-`E` form of `gravity_eq_comptonTemperature_iff` (its instance
at `E = mc²`).  Reported by `#zil_groupoid_report` as an underived composite with both flanks
proven through the Unruh carrier, and proven here *as* that composition.  With it the
six-carrier temperature hexagon is fully closed (`Physlib.Meta.TemperaturePentagonGate`).
Carries `G`: exactly one nat off under the holographic typing, like every edge into the
gravity vertex. -/
theorem gravity_eq_deBroglieTemperature_iff {M G ℏ c R kB E : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) :
    verlindeGravityTemperature M G ℏ c R kB = deBroglieTemperature E kB
      ↔ G * M / R ^ 2 = E * c / ℏ := by
  rw [← (unruh_eq_gravityTemperature_iff hℏ hkB hc hR).mpr rfl]
  exact unruh_eq_deBroglieTemperature_iff hℏ hkB hc

/-! ### §B — the two readings of the same force use one mass -/

/-- **`m_i a = GMm_g/R²` with `m_i` and `m_g` provably the same symbol.**  At the matched
acceleration, the inertial reading of the entropic force (`newton_second_law_from_verlinde_unruh`)
and its gravitational reading (`newton_law_of_gravity_from_verlinde`) are equal — and the `m` on the
two sides is the *same variable*, entering both through the single displacement entropy.  The weak
equivalence principle is not assumed anywhere in the chain; it is an identity of the derivation. -/
theorem inertial_reading_eq_gravitational_reading {M G ℏ c R kB m Δx a : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hm : 0 < m) (hc : 0 < c) (hR : 0 < R)
    (hT : unruhTemperature ℏ kB c a = verlindeGravityTemperature M G ℏ c R kB) :
    m * a = G * M * m / R ^ 2 := by
  have ha : a = G * M / R ^ 2 := (unruh_eq_gravityTemperature_iff hℏ hkB hc hR).mp hT
  rw [ha]
  field_simp

/-! ### §C — the measured observable is exactly null -/

/-- **The Eötvös differential acceleration vanishes for every pair of bodies.**  The free-fall
acceleration `F/m` extracted from the gravitational entropic force is `GM/R²` for *any* test mass,
so the differential acceleration of two bodies — the quantity torsion balances and MICROSCOPE
measure — is exactly zero, with no free parameter available to make it otherwise.  A measured
`η ≠ 0` at any precision falsifies the displacement-entropy postulate outright. -/
theorem eotvos_null {M G ℏ c R kB m₁ m₂ Δx : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) (hΔx : 0 < Δx)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    verlindeEntropicForce (verlindeGravityTemperature M G ℏ c R kB)
        (verlindeDisplacementEntropy ℏ kB m₁ c Δx) Δx / m₁
      = verlindeEntropicForce (verlindeGravityTemperature M G ℏ c R kB)
          (verlindeDisplacementEntropy ℏ kB m₂ c Δx) Δx / m₂ := by
  rw [newton_law_of_gravity_from_verlinde hℏ hkB hc hR hΔx,
    newton_law_of_gravity_from_verlinde hℏ hkB hc hR hΔx]
  field_simp

/- ZIL-BEGIN -/

zil attach Physlib.Thermodynamics.inertial_reading_eq_gravitational_reading where
  formalizes @ "claim:in-the-entropic-force-derivation-the-inertial-and-gravitational-readings-of-the-force-consume-the-same-displacement-entropy-mass-so-the-weak-equivalence-principle-is-a-theorem-of-the-derivation-rather-than-an-empirical-input",
  epistemic_status @ "conditional-model",
  requires @ "assumption:displacement-entropy-ansatz",
  supported_by @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  supported_by @ "lean:Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde",
  caveat @ "conditional-on-the-displacement-entropy-postulate-and-the-holographic-bit-count-nonrelativistic-static-spherical-screen-and-this-is-the-weak-equivalence-principle-only-the-strong-version-with-gravitational-self-energy-is-not-addressed"

zil attach Physlib.Thermodynamics.eotvos_null where
  supported_by @ "lean:newton_law_of_gravity_from_verlinde",
  formalizes @ "claim:the-eotvos-differential-free-fall-acceleration-of-any-two-bodies-is-exactly-zero-in-the-entropic-force-derivation-with-no-free-parameter-between-the-displacement-entropy-postulate-and-the-observable",
  epistemic_status @ "conditional-model",
  requires @ "claim:in-the-entropic-force-derivation-the-inertial-and-gravitational-readings-of-the-force-consume-the-same-displacement-entropy-mass-so-the-weak-equivalence-principle-is-a-theorem-of-the-derivation-rather-than-an-empirical-input",
  experimental_bound @ "value:microscope-final-2022-eotvos-parameter-titanium-platinum-minus-one-point-five-plus-minus-two-point-seven-times-ten-to-the-minus-fifteen-and-eot-wash-torsion-balances-at-ten-to-the-minus-thirteen;test:the-framework-predicts-exactly-zero-with-no-parameter-to-absorb-a-violation-because-the-displacement-entropy-depends-on-the-mass-alone-so-any-nonzero-eotvos-ratio-at-any-precision-falsifies-the-displacement-entropy-postulate-outright",
  caveat @ "passing-does-not-discriminate-the-framework-from-pure-general-relativity-both-predict-exactly-zero-it-discriminates-it-from-generic-beyond-standard-model-physics-which-allows-composition-dependent-violations-and-it-makes-every-wep-experiment-a-direct-test-of-the-frameworks-central-gravitational-postulate"

zil attach Physlib.Thermodynamics.gravity_eq_comptonTemperature_iff where
  formalizes @ "claim:verlinde-screen-temperature-equals-compton-temperature-exactly-where-the-gravitational-acceleration-is-the-compton-acceleration",
  supported_by @ "lean:Physlib.Thermodynamics.unruh_eq_gravityTemperature_iff",
  supported_by @ "lean:Physlib.Thermodynamics.unruh_eq_comptonTemperature_iff",
  caveat @ "claim:algebraic-carrier-identity-not-an-independent-derivation-of-thermality"

/- ZIL-END -/

end Physlib.Thermodynamics

end

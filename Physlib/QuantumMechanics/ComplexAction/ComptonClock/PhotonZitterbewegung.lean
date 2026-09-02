/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.Mathematics.CrossProductMatrix

meta import Zil

/-!
# The photon trembles too, at its de Broglie frequency

Kobe, *Zitterbewegung of a photon*, Phys. Lett. A **253** (1999) 7–11, carries the Dirac
zitterbewegung argument across to a massless particle.  A single photon obeys a Schrödinger-like
equation `HΨ = iħ ∂_t Ψ` with `H = v⃗·p⃗` on a three-component wave function subject to the
transversality condition `∇·Ψ = 0` (Eqs. 1–3); the velocity-operator components are the `3 × 3`
matrices `(v_i)_jk = −iλc ε_ijk` with `λ = ±1` the helicity.  Solving the Heisenberg equation gives
(Eq. 12)

  `v⃗(t) = v⃗_∥(0) + v⃗_⊥(0) cos ωt + v⃗'_⊥(0) λ sin ωt`,  `ω = pc/ħ`,

so the longitudinal velocity is constant while the transverse part **precesses about `p̂`** — the
photon's zitterbewegung.  Integrating (Eq. 15) gives an oscillating displacement of spatial
amplitude `c/ω`, "approximately the reduced wavelength of the corresponding electromagnetic wave",
and the orbital angular momentum of that motion is the spin, `S⃗ = λħ p̂` (Eq. 17) — magnitude `ħ`,
i.e. spin 1.

Three things are worth stating precisely against what the library already has.

**The frequency is *not* the massless limit of the Dirac formula.**  `FrequencyTrinity`'s
`zitterbewegungFrequency` is the `E₊ − E₋` gap `2√(p²c² + m²c⁴)/ħ`, which at `m = 0` reads `2pc/ħ`
— **twice** Kobe's `ω`.  The photon's velocity operator has transverse eigenvalues `±pc` and a
longitudinal eigenvalue `0` (Eq. 10), and it is the precession of the transverse part, not a
gap between `±pc`, that sets the rate.  So the massless limit of the electron formula overshoots the
photon's trembling by a factor of two, and §A records that rather than eliding it.

**What `ω` *is*, is the de Broglie frequency.**  With `E = pc` the trembling rate is `E/ħ`, so for
the photon the frequency trinity degenerates: the Compton frequency `mc²/ħ` vanishes with the mass,
and the trembling coincides with `deBroglieFrequency`.

**The amplitude unifies with the electron's.**  Writing the amplitude as `ħc/E` (§D) gives the
reduced Compton wavelength `ħ/(mc)` at the rest energy `E = mc²` and Kobe's `c/ω = ħ/p` at `E = pc`.
One expression, both regimes — the massless case is not a separate phenomenon.

Scope.  What is formalized is the kinematics: the rotation in Eq. 12 and its invariants, the
displacement of Eq. 15 and its amplitude, the spin magnitude of Eq. 17, and the frequency/amplitude
identifications above.  The Heisenberg-picture derivation that *produces* Eq. 12 — the operator
exponential of Eq. 8 and the dyadic expansion of Eqs. 9–11 — is Kobe's and is taken as given here;
the transversality condition enters only through the hypothesis `‖v⃗(0)‖ = c`.  The Lie-algebra
structure behind the velocity-operator commutation relation `v⃗ × v⃗ = iλc v⃗` (Eq. 5) is
`Matrix.crossProductMatrix_commutator`, since `(v_i)_jk = −iλc ε_ijk` is `iλc` times the hat map.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ### §A — the trembling rate, and how it differs from the Dirac one -/

/-- Kobe's photon trembling rate `ω = pc/ħ` (the `ω` of Eq. 12). -/
def photonZitterFrequency (p c ħ : ℝ) : ℝ := p * c / ħ

/-- **For a photon the trembling rate is the de Broglie frequency.**  The massless dispersion
`E = pc` is exactly what identifies `ω = pc/ħ` with `E/ħ`; the hypothesis is doing the work, so this
is a statement about massless kinematics rather than a renaming. -/
theorem photonZitterFrequency_eq_deBroglie {E p c ħ : ℝ} (hE : E = p * c) :
    photonZitterFrequency p c ħ = deBroglieFrequency E ħ := by
  unfold photonZitterFrequency deBroglieFrequency
  rw [hE]

/-- **The photon's Compton frequency vanishes.**  With `m = 0` the third member of the frequency
trinity is zero, so for a photon the trinity degenerates to the single scale `E/ħ`. -/
theorem comptonFrequency_massless (c ħ : ℝ) : comptonFrequency 0 c ħ = 0 := by
  unfold comptonFrequency
  simp

/-- **The massless limit of the Dirac formula is twice the photon rate.**  `zitterbewegungFrequency`
is the `E₊ − E₋` gap `2√(p²c² + m²c⁴)/ħ`; at `m = 0` it is `2pc/ħ`, whereas Kobe's photon precesses
at `pc/ħ`.  Taking the electron formula to `m → 0` therefore does **not** give the photon's
trembling — it overshoots by a factor of two, because the photon rate is a precession of the
transverse velocity rather than a gap between the `±pc` eigenvalues. -/
theorem zitterbewegungFrequency_massless_eq_two_photonZitter {p c ħ : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) :
    zitterbewegungFrequency p 0 c ħ = 2 * photonZitterFrequency p c ħ := by
  unfold zitterbewegungFrequency photonZitterFrequency
  have hsq : p ^ 2 * c ^ 2 + 0 ^ 2 * c ^ 4 = (p * c) ^ 2 := by ring
  rw [hsq, Real.sqrt_sq (mul_nonneg hp hc)]
  ring

/-! ### §B — the transverse velocity precesses (Eq. 12) -/

/-- The transverse velocity of Kobe Eq. 12, `v⃗_⊥(0) cos ωt + v⃗'_⊥(0) λ sin ωt`, where
`v⃗'_⊥(0) = p̂ × v⃗_⊥(0)` is the quarter-turn of `v⃗_⊥(0)` about the momentum direction. -/
def transverseVelocity (lam ω t : ℝ) (v v' : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => Real.cos (ω * t) * v i + lam * Real.sin (ω * t) * v' i

/-- **The trembling is a rotation: its speed is constant.**  When the two transverse vectors are
orthogonal and of equal length — which is what `v⃗'_⊥(0) = p̂ × v⃗_⊥(0)` provides, and what Kobe
records as `{v⃗_⊥(0); v⃗'_⊥(0)} = 0` — and the helicity satisfies `λ² = 1`, the squared speed of the
transverse motion is independent of time.  The photon's velocity operator precesses; it does not
change magnitude. -/
theorem transverseVelocity_normSq {lam ω t : ℝ} (v v' : Fin 3 → ℝ)
    (hlam : lam ^ 2 = 1) (horth : ∑ i, v i * v' i = 0)
    (hnorm : ∑ i, v' i ^ 2 = ∑ i, v i ^ 2) :
    ∑ i, transverseVelocity lam ω t v v' i ^ 2 = ∑ i, v i ^ 2 := by
  have hpyth := Real.sin_sq_add_cos_sq (ω * t)
  simp only [transverseVelocity, Fin.sum_univ_three] at *
  linear_combination (2 * lam * Real.cos (ω * t) * Real.sin (ω * t)) * horth
    + (lam ^ 2 * Real.sin (ω * t) ^ 2) * hnorm
    + (Real.sin (ω * t) ^ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)) * hlam
    + (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) * hpyth

/-- **At `t = 0` the trembling contributes the initial transverse velocity.** -/
theorem transverseVelocity_at_zero (lam ω : ℝ) (v v' : Fin 3 → ℝ) :
    transverseVelocity lam ω 0 v v' = v := by
  funext i
  simp [transverseVelocity]

/-! ### §C — the displacement and its amplitude (Eq. 15) -/

/-- The oscillating part of Kobe Eq. 15, `v⃗_⊥(0) ω⁻¹ sin ωt − v⃗'_⊥(0) λ ω⁻¹ cos ωt` — the
zitterbewegung proper, once the constant displacement and the uniform drift `v⃗_∥(0) t` are removed. -/
def zitterDisplacement (lam ω t : ℝ) (v v' : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => Real.sin (ω * t) / ω * v i - lam * Real.cos (ω * t) / ω * v' i

/-- **The trembling traces a circle of radius `‖v⃗_⊥‖/ω`.**  Under the same orthogonality and
equal-length conditions the squared displacement is constant in time and equal to `‖v⃗_⊥‖²/ω²`, so
the spatial amplitude of the photon's zitterbewegung is the transverse speed divided by the
precession rate. -/
theorem zitterDisplacement_normSq {lam ω t : ℝ} (v v' : Fin 3 → ℝ) (hω : ω ≠ 0)
    (hlam : lam ^ 2 = 1) (horth : ∑ i, v i * v' i = 0)
    (hnorm : ∑ i, v' i ^ 2 = ∑ i, v i ^ 2) :
    ω ^ 2 * ∑ i, zitterDisplacement lam ω t v v' i ^ 2 = ∑ i, v i ^ 2 := by
  have hpyth := Real.sin_sq_add_cos_sq (ω * t)
  simp only [zitterDisplacement, Fin.sum_univ_three] at *
  field_simp
  linear_combination (-(2 : ℝ) * lam * Real.cos (ω * t) * Real.sin (ω * t)) * horth
    + (lam ^ 2 * Real.cos (ω * t) ^ 2) * hnorm
    + (Real.cos (ω * t) ^ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)) * hlam
    + (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) * hpyth

/-! ### §D — the amplitude is `ħc/E`, for the photon and the electron alike -/

/-- The zitterbewegung amplitude written through the energy, `ħc/E`. -/
def zitterAmplitude (ħ c E : ℝ) : ℝ := ħ * c / E

/-- **At the rest energy the amplitude is the reduced Compton wavelength.**  Setting `E = mc²` in
`ħc/E` returns `ħ/(mc)` — the electron's trembling scale, recovered from the energy form. -/
theorem zitterAmplitude_rest_eq_comptonWavelength {m c ħ E : ℝ} (hE : E = m * c ^ 2)
    (hm : m ≠ 0) (hc : c ≠ 0) :
    zitterAmplitude ħ c E = comptonWavelength m c ħ := by
  unfold zitterAmplitude comptonWavelength
  rw [hE]
  field_simp

/-- **At the photon energy the same expression is `c/ω`.**  Setting `E = pc` in `ħc/E` returns
`c` divided by Kobe's trembling rate — the reduced wavelength of the corresponding electromagnetic
wave.  Together with the previous theorem: the massless case is not a separate phenomenon, it is
`ħc/E` evaluated on a different dispersion relation. -/
theorem zitterAmplitude_photon_eq_c_div_frequency {p c ħ E : ℝ} (hE : E = p * c)
    (hp : p ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    zitterAmplitude ħ c E = c / photonZitterFrequency p c ħ := by
  unfold zitterAmplitude photonZitterFrequency
  rw [hE]
  field_simp

/-! ### §E — the spin is the orbital angular momentum of the trembling (Eq. 17) -/

/-- Kobe Eq. 17: the photon spin `S⃗ = λħ p̂`, obtained as the Hermitian part of
`x⃗_⊥ × m v⃗_⊥` with the relativistic mass `m = E/c²` — the orbital angular momentum of the
zitterbewegung orbit itself. -/
def photonSpin (lam ħ : ℝ) (phat : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => lam * ħ * phat i

/-- **The photon's spin is `1` in units of `ħ`.**  For a unit momentum direction and helicity
`λ = ±1`, `‖S⃗‖² = ħ²`: the component along `p̂` is `±ħ`, so the spin of the photon is one — and it
is here the angular momentum of the trembling orbit, not an independent postulate. -/
theorem photonSpin_normSq {lam ħ : ℝ} (phat : Fin 3 → ℝ) (hlam : lam ^ 2 = 1)
    (hunit : ∑ i, phat i ^ 2 = 1) :
    ∑ i, photonSpin lam ħ phat i ^ 2 = ħ ^ 2 := by
  simp only [photonSpin, Fin.sum_univ_three] at *
  linear_combination (ħ ^ 2 * (phat 0 ^ 2 + phat 1 ^ 2 + phat 2 ^ 2)) * hlam + ħ ^ 2 * hunit

/-! ### §F — the chain -/

/-- **One massless clock: rate, amplitude and spin.**  A photon of momentum `p` and energy `E = pc`
trembles at the de Broglie frequency `E/ħ`, over a circle whose radius is the same `ħc/E` that gives
the electron its Compton wavelength, carrying spin `ħ` along `p̂`.  The Compton frequency, the third
member of the trinity, has gone to zero with the mass. -/
theorem photon_zitter_chain {E p c ħ lam : ℝ} (phat : Fin 3 → ℝ) (hE : E = p * c)
    (hp : p ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hlam : lam ^ 2 = 1) (hunit : ∑ i, phat i ^ 2 = 1) :
    photonZitterFrequency p c ħ = deBroglieFrequency E ħ
      ∧ zitterAmplitude ħ c E = c / photonZitterFrequency p c ħ
      ∧ comptonFrequency 0 c ħ = 0
      ∧ ∑ i, photonSpin lam ħ phat i ^ 2 = ħ ^ 2 :=
  ⟨photonZitterFrequency_eq_deBroglie hE,
   zitterAmplitude_photon_eq_c_div_frequency hE hp hc hħ,
   comptonFrequency_massless c ħ,
   photonSpin_normSq phat hlam hunit⟩


/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.photonZitterFrequency_eq_deBroglie where
  formalizes @ "claim:the-photon-transverse-velocity-operator-precesses-at-p-c-over-hbar-which-is-its-de-broglie-frequency-because-the-massless-dispersion-makes-e-equal-p-c",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:kobe-1999-zitterbewegung-of-a-photon-physics-letters-a-253-7-11",
  caveat @ "the-massless-dispersion-e-equals-p-c-is-a-hypothesis-of-the-theorem-what-is-proved-is-that-it-is-what-identifies-the-two-rates"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.zitterbewegungFrequency_massless_eq_two_photonZitter where
  formalizes @ "claim:the-massless-limit-of-the-dirac-zitterbewegung-gap-formula-is-twice-the-photon-precession-rate-so-it-does-not-give-the-photon-trembling-frequency",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-photon-transverse-velocity-operator-precesses-at-p-c-over-hbar-which-is-its-de-broglie-frequency-because-the-massless-dispersion-makes-e-equal-p-c",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegungFrequency",
  caveat @ "this-is-a-negative-result-the-electron-gap-formula-must-not-be-quoted-at-m-equals-zero-as-the-photon-trembling-rate-the-photon-rate-is-a-precession-of-the-transverse-velocity-not-a-gap-between-the-plus-minus-p-c-eigenvalues"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.transverseVelocity_normSq where
  formalizes @ "claim:the-photon-zitterbewegung-is-a-rotation-the-transverse-speed-and-the-orbit-radius-are-both-constant-in-time",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:kobe-1999-zitterbewegung-of-a-photon-physics-letters-a-253-7-11",
  caveat @ "the-orthogonality-and-equal-length-of-the-two-transverse-vectors-are-hypotheses-supplied-by-kobes-dyadic-construction-they-are-not-derived-here"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.zitterDisplacement_normSq where
  formalizes @ "claim:the-photon-zitterbewegung-is-a-rotation-the-transverse-speed-and-the-orbit-radius-are-both-constant-in-time",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-photon-zitterbewegung-is-a-rotation-the-transverse-speed-and-the-orbit-radius-are-both-constant-in-time",
  supported_by @ "paper:kobe-1999-zitterbewegung-of-a-photon-physics-letters-a-253-7-11",
  caveat @ "stated-multiplied-through-by-omega-squared-so-the-orbit-radius-squared-is-the-transverse-speed-squared-over-omega-squared-without-a-division"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.zitterAmplitude_rest_eq_comptonWavelength where
  formalizes @ "claim:the-zitterbewegung-amplitude-hbar-c-over-energy-is-the-reduced-compton-wavelength-at-the-rest-energy-and-the-reduced-wavelength-at-the-photon-energy",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength",
  caveat @ "an-algebraic-identification-of-two-length-scales-it-does-not-derive-either-trembling-amplitude-from-its-own-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.zitterAmplitude_photon_eq_c_div_frequency where
  formalizes @ "claim:the-zitterbewegung-amplitude-hbar-c-over-energy-is-the-reduced-compton-wavelength-at-the-rest-energy-and-the-reduced-wavelength-at-the-photon-energy",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-photon-transverse-velocity-operator-precesses-at-p-c-over-hbar-which-is-its-de-broglie-frequency-because-the-massless-dispersion-makes-e-equal-p-c",
  supported_by @ "paper:kobe-1999-zitterbewegung-of-a-photon-physics-letters-a-253-7-11",
  caveat @ "same-algebraic-identification-on-the-massless-dispersion-the-unification-is-that-one-expression-covers-both-regimes-not-that-a-common-mechanism-is-proved"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.photonSpin_normSq where
  formalizes @ "claim:the-photon-spin-is-the-orbital-angular-momentum-of-its-zitterbewegung-orbit-and-has-magnitude-hbar-that-is-spin-one",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:kobe-1999-zitterbewegung-of-a-photon-physics-letters-a-253-7-11",
  caveat @ "the-identification-of-that-magnitude-with-the-orbital-angular-momentum-of-the-trembling-orbit-is-kobes-equation-sixteen-construction-what-is-proved-here-is-the-magnitude-given-unit-momentum-direction-and-helicity-plus-or-minus-one"

zil_file_contract physlib.photonZitterbewegung where
  promises "Kobe carries the Dirac zitterbewegung argument to a massless particle: a photon obeying a Schrodinger-like equation with Hamiltonian the velocity operator dotted into the momentum, on a three-component transverse wave function, has a velocity operator whose longitudinal part is constant and whose transverse part precesses about the momentum direction at angular frequency p c over hbar, tracing a circle whose radius is c over that frequency and whose orbital angular momentum is the spin. What this file adds beyond restating those results is their relation to the frequency trinity already in the library. First, a negative result: the zitterbewegung frequency defined there is the energy gap formula twice the square root of p squared c squared plus m squared c to the fourth, all over hbar, and at zero mass that is twice the photon precession rate, so the massless limit of the electron formula is not the photon trembling frequency. Second, what the photon rate is, is the de Broglie frequency, since the massless dispersion makes the energy equal p c, while the Compton member of the trinity vanishes with the mass, so for a photon the trinity degenerates to a single scale. Third, the amplitude written as hbar c over energy returns the reduced Compton wavelength at the rest energy and the photon reduced wavelength at the photon energy, so the massless case is that one expression evaluated on a different dispersion relation rather than a separate phenomenon. The kinematics are formalized; the Heisenberg-picture derivation that produces the precession, namely the operator exponential and the dyadic expansion over the circular polarization vectors, is taken as given, and the transversality condition enters only through the hypothesis that the initial speed is c."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegungFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength",
    "lean:Matrix.crossProductMatrix_commutator"]
  forbids_substitutes ["quoting the Dirac zitterbewegung gap formula at zero mass as the photon trembling rate, which overshoots it by a factor of two",
    "presenting the kinematic identities here as a derivation of the photon precession, when the Heisenberg-picture solution that produces it is taken as given",
    "reading the shared amplitude expression as a proof that the electron and photon trembling share a mechanism, rather than as one formula evaluated on two dispersion relations"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.photonZitterFrequency_eq_deBroglie,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.comptonFrequency_massless,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.zitterbewegungFrequency_massless_eq_two_photonZitter,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.transverseVelocity_normSq,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.zitterDisplacement_normSq,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.zitterAmplitude_rest_eq_comptonWavelength,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.zitterAmplitude_photon_eq_c_div_frequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.photonSpin_normSq,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung.photon_zitter_chain]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhotonZitterbewegung

end

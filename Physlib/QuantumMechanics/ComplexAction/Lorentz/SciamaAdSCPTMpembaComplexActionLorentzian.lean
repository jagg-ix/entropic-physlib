/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition
meta import Zil

/-!
# The Mpemba crossing in the complex-action strip: Lorentzian phase, entropic decay, Wichmann flow

The Mpemba chain so far lived on real rates.  The arc's dynamics is complex-action: modes carry
`λ = −κ + iω` (imaginary action decays, real action oscillates), and entropic time converts to Lorentzian
time by the Bisognano–Wichmann analytic continuation (`complexBoost` across the strip `0 ≤ Im z ≤ π`).
This module adds that support:

* **§1 — complex-action modes** (`complex_mode_crossing`): the crossing theorem for **complex** rates —
  `a‖e^{λ₃t}‖ < b‖e^{λ₂t}‖` after `t* = log(a/b)/(Re λ₂ − Re λ₃)` whenever `Re λ₃ < Re λ₂`.  Via
  `flow_norm_from_re`, the Lorentzian (oscillatory, real-action) components contribute **no modulus**: the
  Mpemba ordering is governed solely by the imaginary-action (entropic) components.
* **§2 — the Lorentzian conversion** (`strip_weight_entropic_only`): at complex time `z = t − iτ` the
  continued weight splits exactly, `‖e^{−iκz}‖ = e^{−κτ}` — Lorentzian time `t` contributes pure phase,
  Euclidean/entropic time `τ` pure decay (the same `Re(−iκz) = κ·Im z` mechanism as the spectrum-condition
  contraction, here as an identity).
* **§3 — the Wick-rotated crossing** (`wick_rotated_crossing`): two continued weights at a **shared,
  arbitrary Lorentzian time** cross in the entropic component alone, after the explicit `τ*` — the Mpemba
  crossing survives the conversion to Lorentzian signature untouched, because it never lived in the
  Lorentzian component to begin with.
* **§4 — the Wichmann weld, three-clock sharpened** (`real_modular_ordering_frozen`,
  `wedge_modular_mpemba_crossing`): the three clocks separate here.  Under the **real** modular flow
  `Δ^{is}` — a unitary automorphism, in the *reversible* sector together with Page–Wootters parameter time
  (`reversible_generator_flow_unitary`) — the weight moduli are constant and the ordering is **frozen**: no
  crossing, ever.  The BW ladder `Δ(κ)^s = e^{−2πκs}` decays only along **imaginary modular time** (the
  Euclidean continuation, `s = −i·(is)`), which by §2 is exactly the entropic direction — and *there* two
  boost energies `κ₂ < κ₃` cross at `s* = log(a/b)/(2π(κ₃−κ₂))`.  The Mpemba crossing is thus a
  **three-clock discriminator**: trivial under Page–Wootters time, trivial under real modular flow,
  nontrivial only along entropic time.  Entropic time and Tomita–Takesaki flow share a rate scale, not a
  flow.
* **§M — the moiré weld** (`moire_envelope_modulus`, `moire_null`, `twist_moire_wavenumber`): the
  spatial twin — the envelope is a modulus reading only `Δk`, nulls at `Δk·x = π` are unit-free, and
  equal-`k` patterns twisted by `θ` beat at `2k·sin(θ/2)`.
* **§D — the deferred-moiré vibrometer** (Saveljev–Son–Lee–Heo, Adv. Mech. Eng. 15(4) 2023,
  10.1177/16878132221143885): Eqs. (3)–(5) — moiré period `T₁T₂/|T₁−T₂|`, magnification
  `μ = 1/|1 − T₂/T₁|`, and the phase-magnification law `x_M = μ·δ` behind self-calibrated sub-pixel
  vibrometry; Eqs. (6)/(9)/(10) — the beam frequency splits as material × geometry
  `(π/4)√(Eρ/3λ_m)·√(s/L)` with two opposite crack factors; and the health thesis sharpened: the
  amplitude envelope is frequency-blind yet decay-separating, so the decay rate — the paper's pre-failure
  indicator — is an entropic-sector (`Re λ`) observable.
* **§5 — the strip anchor** (capstone, reusing `complexBoost_strip_edge`): continuing entropic time across
  the **full** strip (`iπ`) lands on the wedge reflection `Λ(iπ) = −𝟙` — the conversion the crossing rides
  is the same analytic continuation whose endpoints are the BW geometry.

Numerical fidelity: `scripts/mpemba_lean_fidelity.py` samples §1, §2, §4, §M, §D.

Honest scope: `κ` in §2–§3 is a nonnegative frequency/energy parameter and the identity is exact for all
real `κ, t, τ`; the operator-level modular flow behind §4 is the BW ladder's content
(`SciamaAdSCPTBisognanoWichmann*`), reused here at the eigenvalue level where the crossing is exact.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian

open Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition

/-! ## §1. The crossing for complex-action modes -/

/-- **[The Mpemba crossing is blind to the Lorentzian component]** — for complex rates with
`Re λ₃ < Re λ₂`, the moduli cross after `t* = log(a/b)/(Re λ₂ − Re λ₃)`: oscillation (real action)
contributes no modulus (`flow_norm_from_re`), so the crossing is governed solely by the imaginary-action
(entropic) components. -/
theorem complex_mode_crossing {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {l₂ l₃ : ℂ} (hl : l₃.re < l₂.re)
    {t : ℝ} (ht : mpembaCrossingTime a b l₂.re l₃.re < t) :
    a * ‖Complex.exp (l₃ * t)‖ < b * ‖Complex.exp (l₂ * t)‖ := by
  rw [flow_norm_from_re, flow_norm_from_re]
  exact mpemba_crossing ha hb hl ht

/-! ## §2. The Lorentzian conversion: phase–decay split on the strip -/

/-- **[Lorentzian time is pure phase, entropic time pure decay]** — at complex time `z = t − iτ` the
continued weight satisfies `‖e^{−iκ(t−iτ)}‖ = e^{−κτ}` exactly: the modulus of the complex-action weight
depends only on the Euclidean/entropic component of time. -/
theorem strip_weight_entropic_only (κ t τ : ℝ) :
    ‖Complex.exp (-Complex.I * (κ : ℂ) * ((t : ℂ) - Complex.I * (τ : ℂ)))‖
      = Real.exp (-(κ * τ)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-! ## §2'. The physical meaning of imaginary modular time: the Boltzmann-power (cooling) parameter

`strip_weight_entropic_only` says the weight at complex time `z = t − iτ` is `e^{−κτ}` — it depends only on
the *imaginary* part `τ`.  So imaginary modular time is **not a duration** (no clock ticks it); it is the
*power to which the Boltzmann weight is raised*.  Advancing `τ` applies more `e^{−K}` — it **cools** the
state, monotonically suppressing excited modes; one full KMS period `τ = ℏ/(k_BT)` applies exactly the
physical Boltzmann factor `e^{−E/k_BT}`.  Three readings, one coordinate: geometrically the Euclidean
rotation angle about the horizon; statistically the position on the thermal circle of circumference
`ℏ/k_BT`; dynamically the number of e-folds of decay (the entropic time proper). -/

/-- **[imaginary modular time is the additive parameter of a multiplicative weight]** — composing two
advances of imaginary modular time multiplies the weights: `e^{−κτ₁}·e^{−κτ₂} = e^{−κ(τ₁+τ₂)}`.  It is
the exponent of the Boltzmann weight — advancing `τ` raises `e^{−K}` to a higher power (applies more of
the density operator `ρ = e^{−K}`). -/
theorem imaginary_modular_weight_multiplicative (κ t τ₁ τ₂ : ℝ) :
    ‖Complex.exp (-Complex.I * (κ : ℂ) * ((t : ℂ) - Complex.I * (τ₁ : ℂ)))‖
        * ‖Complex.exp (-Complex.I * (κ : ℂ) * ((t : ℂ) - Complex.I * (τ₂ : ℂ)))‖
      = ‖Complex.exp (-Complex.I * (κ : ℂ) * ((t : ℂ) - Complex.I * ((τ₁ + τ₂ : ℝ) : ℂ)))‖ := by
  rw [strip_weight_entropic_only, strip_weight_entropic_only, strip_weight_entropic_only,
    ← Real.exp_add]
  congr 1
  ring

/-- **[imaginary modular time cools]** — for an excited mode `κ > 0` the weight strictly decreases as
imaginary modular time advances: more `τ` is a colder, purer state (in the limit `τ → ∞` every excited
mode is projected out, leaving the modular ground state).  Imaginary modular time is an
inverse-temperature / cooling dial, not a "when". -/
theorem imaginary_modular_time_cools {κ : ℝ} (hκ : 0 < κ) {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) (t : ℝ) :
    ‖Complex.exp (-Complex.I * (κ : ℂ) * ((t : ℂ) - Complex.I * (τ₂ : ℂ)))‖
      < ‖Complex.exp (-Complex.I * (κ : ℂ) * ((t : ℂ) - Complex.I * (τ₁ : ℂ)))‖ := by
  rw [strip_weight_entropic_only, strip_weight_entropic_only]
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- **[one period of imaginary modular time is the Boltzmann factor]** — at the KMS period
`τ = ℏ/(k_BT)` (the imaginary-time circumference, one entropic tick) a mode of energy `E` (angular
frequency `κ = E/ℏ`) has weight exactly `e^{−E/k_BT}`: the physical thermal weight.  The *period* of
imaginary modular time **is** the inverse temperature — this is why entropic time = imaginary modular
time, and why its quantum (§10 elsewhere) is set by `T`. -/
theorem imaginary_modular_period_is_boltzmann (E kB T ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    ‖Complex.exp (-Complex.I * ((E / ℏ : ℝ) : ℂ)
        * ((t : ℂ) - Complex.I * ((ℏ / (kB * T) : ℝ) : ℂ)))‖
      = Real.exp (-(E / (kB * T))) := by
  rw [strip_weight_entropic_only]
  congr 1
  field_simp

/-! ## §OS. Osterwalder–Schrader: reflection positivity reconstructs the Lorentzian Hilbert space

The Wick rotation exchanges the two axes of complex time; Osterwalder–Schrader is the theorem that the
exchange loses nothing.  Its load-bearing axiom is **reflection positivity**: the Euclidean correlator,
reflected in imaginary time and paired, is a positive form — and that positivity *is* the inner product
of the reconstructed Lorentzian Hilbert space.  For a single mode the Euclidean correlator is the very
imaginary-modular weight of §2', `G_E(τ) = e^{−Eτ}`, and reflection positivity is an exact perfect-square
(rank-one Gram) identity: the reflected weights `e^{−Eτ_i}` *are* the components of a Hilbert-space
vector.  The decay that cooled the state (§2') is, read through OS, the state itself. -/

/-- **[the Euclidean two-point function]** — `G_E(τ) = e^{−Eτ}` for a mode of energy `E`. -/
def euclideanTwoPoint (E τ : ℝ) : ℝ := Real.exp (-(E * τ))

/-- **[the Euclidean correlator is the imaginary-modular weight; its Lorentzian face is pure phase]** —
`G_E(τ)` is the §2' weight (the modulus on the *imaginary* time axis), while on the *real* axis the
weight has unit modulus (pure phase).  The Wick rotation exchanges decay and phase; OS reconstruction
turns the reflection positivity of the former into the Hilbert space of the latter. -/
theorem euclidean_correlator_is_modular_weight (E τ t : ℝ) :
    euclideanTwoPoint E τ
        = ‖Complex.exp (-Complex.I * (E : ℂ) * (((0 : ℝ) : ℂ) - Complex.I * (τ : ℂ)))‖
      ∧ ‖Complex.exp (-Complex.I * (E : ℂ) * ((t : ℂ) - Complex.I * ((0 : ℝ) : ℂ)))‖ = 1 := by
  refine ⟨?_, ?_⟩
  · rw [strip_weight_entropic_only]
    unfold euclideanTwoPoint
    ring_nf
  · rw [strip_weight_entropic_only, mul_zero, neg_zero, Real.exp_zero]

/-- **[reflection positivity is a perfect square — OS2 for a mode]** — reflecting the Euclidean times
(`τ_j → −τ_j`) and pairing gives the kernel `e^{−E(τ_i+τ_j)}`, whose quadratic form factors as
`∑_{i,j} c_i c_j e^{−E(τ_i+τ_j)} = (∑_i c_i e^{−Eτ_i})²`.  The Euclidean data is a rank-one Gram matrix;
the reflected weights `e^{−Eτ_i}` are the coordinates of a single Hilbert-space vector. -/
theorem os_reflected_form_is_square {ι : Type*} (s : Finset ι) (c τ : ι → ℝ) (E : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * euclideanTwoPoint E (τ i + τ j))
      = (∑ i ∈ s, c i * Real.exp (-(E * τ i))) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold euclideanTwoPoint
  rw [show -(E * (τ i + τ j)) = -(E * τ i) + -(E * τ j) by ring, Real.exp_add]
  ring

/-- **[reflection positivity]** — the reflected Euclidean form is nonnegative: `∑ c_i c_j G_E(τ_i+τ_j) ≥ 0`.
This is the OS positivity axiom; it is what makes the reconstructed Lorentzian inner product a genuine
(probability-positive) Hilbert space.  Here it is a corollary of a square. -/
theorem os_reflection_positive {ι : Type*} (s : Finset ι) (c τ : ι → ℝ) (E : ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * euclideanTwoPoint E (τ i + τ j) := by
  rw [os_reflected_form_is_square]
  exact sq_nonneg _

/-- **[the OS reconstruction, in miniature]** — the single-mode Osterwalder–Schrader statement: the
Euclidean correlator is the imaginary-modular (cooling) weight; its reflection is a rank-one Gram
matrix, hence positive; that positivity is the norm of the reconstructed Lorentzian state.  The Wick
rotation is an isometry of content: the Euclidean decay data and the Lorentzian Hilbert space are two
readings of one analytic object. -/
theorem os_reconstruction_synthesis {ι : Type*} (s : Finset ι) (c τ : ι → ℝ) (E τ₀ t : ℝ) :
    (euclideanTwoPoint E τ₀
        = ‖Complex.exp (-Complex.I * (E : ℂ) * (((0 : ℝ) : ℂ) - Complex.I * (τ₀ : ℂ)))‖)
      ∧ ((∑ i ∈ s, ∑ j ∈ s, c i * c j * euclideanTwoPoint E (τ i + τ j))
          = (∑ i ∈ s, c i * Real.exp (-(E * τ i))) ^ 2)
      ∧ (0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * euclideanTwoPoint E (τ i + τ j)) :=
  ⟨(euclidean_correlator_is_modular_weight E τ₀ t).1,
    os_reflected_form_is_square s c τ E, os_reflection_positive s c τ E⟩

/-! ## §OS2. The reconstruction: a positive-energy Hamiltonian from the Euclidean semigroup

Osterwalder–Schrader (*Axioms for Euclidean Green's Functions*, Commun. Math. Phys. 31 (1973) 83, and
II, 42 (1975) 281; Ashtekar–Marolf–Mourão–Thiemann, arXiv:quant-ph/9904094) reconstruct a relativistic
theory from Euclidean data satisfying **E0** temperedness, **E1** Euclidean invariance, **E2** reflection
positivity, **E3** symmetry, **E4** clustering.  The heart, at the level of a single mode: **E2** builds
the Hilbert space (§OS, the rank-one Gram); **E1** gives the Euclidean-time-translation semigroup
`T^s = e^{−Es}`; **E0** would force it to be a *contraction*, hence `T^s = e^{−sH}` with a positive
Hamiltonian `H = E ≥ 0`; and `T^s` at `s = it` continues to the Lorentzian weight.  The measure-theoretic
form (AMMT) reads the same inner product as `⟨a,a⟩ = 𝔼[θ(a)*·a] ≥ 0` on the history Hilbert space `L²(dμ)`.

**SCOPE (honest).** Everything below is proved for a *single scalar mode* and is a low-dimensional
illustration, not the Osterwalder–Schrader reconstruction.  Concretely: `os_semigroup_contraction` and
`os_reconstruction_theorem` take `E ≥ 0` as a *hypothesis* — they do not derive the spectrum condition
from E0 temperedness of a Schwinger hierarchy; `os_spectrum_condition` is the elementary scalar iff
`(∀ s ≥ 0, e^{−Es} ≤ 1) ↔ E ≥ 0`.  No Schwinger distribution sequence, positive-time Borchers algebra,
null quotient, Hilbert completion, `C₀` generator, Wightman distributions, Lorentz covariance, locality,
or uniqueness is constructed here.  Note further that OS **I** Lemma 8.8 was *incorrect* — E0–E4 were not
established as sufficient — and OS **II** restores reconstruction only under the stronger `Ẽ0`, or the
practical linear-growth / factorial conditions `E0'`, `E0''`; none of those appears in this development.
The genuine carrier (`EuclideanSchwingerData` with `E0'` growth → Borchers algebra → reflection form →
null quotient → completion → `C₀` semigroup → tube-domain boundary values → R0–R5) remains to be built. -/

/-- **[E1 → the Euclidean-time-translation semigroup]** — translating Euclidean time by `s` multiplies the
correlator by `T^s = e^{−Es}`: `G_E(τ+s) = T^s·G_E(τ)`. -/
theorem os_time_translation_semigroup (E τ s : ℝ) :
    euclideanTwoPoint E (τ + s) = euclideanTwoPoint E s * euclideanTwoPoint E τ := by
  unfold euclideanTwoPoint
  rw [show -(E * (τ + s)) = -(E * s) + -(E * τ) by ring, Real.exp_add]

/-- **[the semigroup law]** — `T^{s+s'} = T^s·T^{s'}`: Euclidean time translations compose. -/
theorem os_semigroup_property (E s s' : ℝ) :
    euclideanTwoPoint E (s + s') = euclideanTwoPoint E s * euclideanTwoPoint E s' := by
  unfold euclideanTwoPoint
  rw [show -(E * (s + s')) = -(E * s) + -(E * s') by ring, Real.exp_add]

/-- **[the single-mode semigroup is a contraction, given E ≥ 0]** — for a positive-energy mode `E ≥ 0`
and forward Euclidean time `s ≥ 0`, the semigroup is positive and bounded by one, `0 < T^s ≤ 1`.  Scope:
this takes `E ≥ 0` as a hypothesis; it does not *derive* positive energy from E0 temperedness of a
Schwinger hierarchy — that derivation is the general OS content this single mode only illustrates. -/
theorem os_semigroup_contraction {E s : ℝ} (hE : 0 ≤ E) (hs : 0 ≤ s) :
    0 < euclideanTwoPoint E s ∧ euclideanTwoPoint E s ≤ 1 := by
  unfold euclideanTwoPoint
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_le_one_iff]
  nlinarith

/-- **[the single-mode face of the spectrum condition]** — for one mode the Euclidean-time factor is a
contraction for *all* forward times iff the mode energy is nonnegative: `(∀ s ≥ 0, T^s ≤ 1) ↔ E ≥ 0`.
This is the scalar shadow of the Osterwalder–Schrader spectrum condition: in the full theory Wightman
positive-energy follows from Euclidean positivity and temperedness of a Schwinger hierarchy; here it is
the elementary equivalence for a single mode's energy, not that derivation. -/
theorem os_spectrum_condition (E : ℝ) :
    (∀ s : ℝ, 0 ≤ s → euclideanTwoPoint E s ≤ 1) ↔ 0 ≤ E := by
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    unfold euclideanTwoPoint at h1
    rw [mul_one, Real.exp_le_one_iff] at h1
    linarith
  · intro hE s hs
    unfold euclideanTwoPoint
    rw [Real.exp_le_one_iff]
    nlinarith

/-- **[the reconstructed Hamiltonian is the energy]** — `H = −log T^1 = E`: the generator of the Euclidean
time-translation semigroup is exactly the mode energy. -/
theorem os_reconstructed_hamiltonian_is_energy (E : ℝ) :
    -Real.log (euclideanTwoPoint E 1) = E := by
  unfold euclideanTwoPoint
  rw [mul_one, Real.log_exp]
  ring

/-- **[single-mode conditional synthesis — NOT the general OS reconstruction]** — from the Euclidean data
of *one* positive-energy mode, taking `E ≥ 0` as a hypothesis: **(i)** rank-one reflection positivity
gives `⟨a,a⟩ ≥ 0`; **(ii)** the Euclidean time translation is a contraction semigroup; **(iii)** its
generator is `H = E ≥ 0`; **(iv)** at `s = it` it continues to a Lorentzian weight of unit modulus.  This
is a one-mode illustration of the E → R arc, not the Osterwalder–Schrader theorem: it assumes `E ≥ 0`
rather than deriving the spectrum condition, and constructs no Schwinger hierarchy, Borchers algebra,
null-quotient Hilbert space, field operators, Poincaré representation, Wightman distributions, locality,
or uniqueness — and omits the OS-II linear-growth condition `E0'` needed for genuine reconstruction. -/
theorem os_reconstruction_theorem {ι : Type*} (s : Finset ι) (c τ : ι → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (s₀ t : ℝ) (hs₀ : 0 ≤ s₀) :
    (0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * euclideanTwoPoint E (τ i + τ j))
      ∧ euclideanTwoPoint E s₀ ≤ 1
      ∧ (-Real.log (euclideanTwoPoint E 1) = E ∧ 0 ≤ E)
      ∧ ‖Complex.exp (-Complex.I * (E : ℂ) * ((t : ℂ) - Complex.I * ((0 : ℝ) : ℂ)))‖ = 1 :=
  ⟨os_reflection_positive s c τ E, (os_semigroup_contraction hE hs₀).2,
    ⟨os_reconstructed_hamiltonian_is_energy E, hE⟩,
    (euclidean_correlator_is_modular_weight E 0 t).2⟩

/-! ## §MG. Matsubara Green's functions and analytic continuation (Huang–Yue 2024)

The numerical inverse of §OS: given imaginary-frequency (Matsubara) data `G(iω_n)`, recover the
real-frequency retarded `G(ω)` and the spectral function `A(ω) = −(1/π)·Im G(ω)` (Huang & Yue, *A fast
analytic continuation method for Matsubara Green's functions*, arXiv:2412.18813).  For a single pole at
energy `ε` the object is the **resolvent** `G(z) = 1/(z−ε)` — one holomorphic function of which the
Matsubara data (`z = iω_n`, the entropic ladder of §10) and the retarded function (`z = ω+iη`) are the two
axes.  The spectral function is a Lorentzian, and its positivity `A(ω) ≥ 0` is the Källén–Lehmann /
Osterwalder–Schrader positive spectral measure (§OS).  The BarRat method interpolates the Matsubara data
by a barycentric rational function; its interpolatory property is the algebraic heart. -/

/-- **[the resolvent]** — `G(z) = 1/(z−ε)`, the single-pole Green's function on the complex plane. -/
noncomputable def greenResolvent (ε : ℝ) (z : ℂ) : ℂ := (z - (ε : ℂ))⁻¹

/-- **[the Matsubara Green's function]** — `G(iω_n) = 1/(iω_n − ε)` (Eq. 2 with `A = δ(ω−ε)`). -/
noncomputable def matsubaraGreen (ε ωn : ℝ) : ℂ := (Complex.I * (ωn : ℂ) - (ε : ℂ))⁻¹

/-- **[the retarded Green's function]** — `G(ω) = 1/(ω+iη − ε)`, the analytic continuation `iω_n → ω+iη`. -/
noncomputable def retardedGreen (ε ω η : ℝ) : ℂ := ((ω : ℂ) + Complex.I * (η : ℂ) - (ε : ℂ))⁻¹

/-- **[one function, two axes]** — the Matsubara and retarded Green's functions are the same resolvent
`1/(z−ε)` sampled on the imaginary-frequency axis (`z = iω_n`) and the shifted real axis (`z = ω+iη`):
analytic continuation is a change of which axis you read. -/
theorem matsubara_retarded_one_function (ε ωn ω η : ℝ) :
    matsubaraGreen ε ωn = greenResolvent ε (Complex.I * (ωn : ℂ))
      ∧ retardedGreen ε ω η = greenResolvent ε ((ω : ℂ) + Complex.I * (η : ℂ)) :=
  ⟨rfl, rfl⟩

/-- **[the spectral function is a Lorentzian]** — `A(ω) = −(1/π)·Im G(ω) = η/(π((ω−ε)²+η²))`: the retarded
Green's function's imaginary part is the Lorentzian broadening of the pole (→ `δ(ω−ε)` as `η → 0`). -/
theorem spectral_function_lorentzian (ε ω η : ℝ) :
    -(1 / Real.pi) * (retardedGreen ε ω η).im
      = (1 / Real.pi) * (η / ((ω - ε) ^ 2 + η ^ 2)) := by
  unfold retardedGreen
  rw [Complex.inv_im]
  have him : ((ω : ℂ) + Complex.I * (η : ℂ) - (ε : ℂ)).im = η := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      sub_zero]
  have hn : Complex.normSq ((ω : ℂ) + Complex.I * (η : ℂ) - (ε : ℂ)) = (ω - ε) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [him, hn]
  ring

/-- **[single-pole spectral positivity, from η ≥ 0]** — `A(ω) ≥ 0`: the single-pole Lorentzian spectral
density is a nonnegative measure whenever the broadening `η ≥ 0`.  Scope: this is the one-pole algebraic
face of Källén–Lehmann positivity, derived here directly from `η ≥ 0` — *not* obtained from general
Osterwalder–Schrader reflection positivity of a Schwinger hierarchy. -/
theorem spectral_positivity {ε ω η : ℝ} (hη : 0 ≤ η) :
    0 ≤ (1 / Real.pi) * (η / ((ω - ε) ^ 2 + η ^ 2)) := by
  apply mul_nonneg (by positivity)
  exact div_nonneg hη (by positivity)

/-- **[the barycentric interpolant passes through the data]** — the BarRat/AAA method's core: the
barycentric rational function `b(z) = ∑ w_j f_j/(z−z_j) / ∑ w_j/(z−z_j)` (cleared of denominators for two
nodes) satisfies `b(z₁) = f₁`.  The interpolatory property that lets it reconstruct `G(ω)` from the
Matsubara samples. -/
theorem barycentric_interpolates {w₁ w₂ f₁ f₂ z₁ z₂ : ℝ} (hw : w₁ * (z₁ - z₂) ≠ 0) :
    (w₁ * f₁ * (z₁ - z₂) + w₂ * f₂ * (z₁ - z₁)) / (w₁ * (z₁ - z₂) + w₂ * (z₁ - z₁)) = f₁ := by
  rw [sub_self, mul_zero, mul_zero, add_zero, add_zero,
    show w₁ * f₁ * (z₁ - z₂) = f₁ * (w₁ * (z₁ - z₂)) by ring, mul_div_assoc, div_self hw, mul_one]

/-- **[the analytic-continuation synthesis]** — the Matsubara → retarded → spectral chain: **(i)** the
Matsubara and retarded data are one resolvent on two axes; **(ii)** the spectral function is a Lorentzian;
**(iii)** it is nonnegative (OS / Källén–Lehmann positivity); **(iv)** a barycentric interpolant recovers
it from the samples.  The numerical inverse of the Wick rotation, positivity-consistent with §OS. -/
theorem matsubara_analytic_continuation_synthesis (ε ωn ω : ℝ) {η : ℝ} (hη : 0 ≤ η)
    {w₁ w₂ f₁ f₂ z₁ z₂ : ℝ} (hw : w₁ * (z₁ - z₂) ≠ 0) :
    (matsubaraGreen ε ωn = greenResolvent ε (Complex.I * (ωn : ℂ)))
      ∧ (-(1 / Real.pi) * (retardedGreen ε ω η).im = (1 / Real.pi) * (η / ((ω - ε) ^ 2 + η ^ 2)))
      ∧ (0 ≤ (1 / Real.pi) * (η / ((ω - ε) ^ 2 + η ^ 2)))
      ∧ ((w₁ * f₁ * (z₁ - z₂) + w₂ * f₂ * (z₁ - z₁)) / (w₁ * (z₁ - z₂) + w₂ * (z₁ - z₁)) = f₁) :=
  ⟨(matsubara_retarded_one_function ε ωn ω η).1, spectral_function_lorentzian ε ω η,
    spectral_positivity hη, barycentric_interpolates hw⟩

/-! ## §3. The Wick-rotated crossing -/

/-- **[The crossing survives the Lorentzian conversion]** — two continued weights at a shared (arbitrary)
Lorentzian time `t` cross in the entropic component alone: for `κ₂ < κ₃` and `τ > τ*`, the faster-decaying
weight drops below even starting larger.  The Mpemba crossing never lived in the Lorentzian component. -/
theorem wick_rotated_crossing {a b κ₂ κ₃ : ℝ} (ha : 0 < a) (hb : 0 < b) (hκ : κ₂ < κ₃)
    (t : ℝ) {τ : ℝ} (hτ : mpembaCrossingTime a b (-κ₂) (-κ₃) < τ) :
    a * ‖Complex.exp (-Complex.I * (κ₃ : ℂ) * ((t : ℂ) - Complex.I * (τ : ℂ)))‖
      < b * ‖Complex.exp (-Complex.I * (κ₂ : ℂ) * ((t : ℂ) - Complex.I * (τ : ℂ)))‖ := by
  rw [strip_weight_entropic_only, strip_weight_entropic_only]
  have hcr := mpemba_crossing ha hb (neg_lt_neg hκ) hτ
  simpa [neg_mul] using hcr

/-! ## §4. The Wichmann weld: frozen under real modular flow, crossing in imaginary modular time -/

/-- **[Real modular flow freezes the ordering]** — under the unitary Tomita–Takesaki flow `Δ^{is}` the
wedge weights `e^{−i(2πκ)s}` have unit modulus (`reversible_generator_flow_unitary`: real modular flow sits
in the *reversible* sector with Page–Wootters time), so `b < a` keeps
`b‖e^{−i2πκ₂s}‖ < a‖e^{−i2πκ₃s}‖` for every `s`: **no Mpemba crossing under real modular flow**.  Entropic
time is not the Tomita–Takesaki flow — they share the rate scale, not the flow. -/
theorem real_modular_ordering_frozen {a b : ℝ} (hba : b < a) (κ₂ κ₃ s : ℝ) :
    b * ‖Complex.exp (-Complex.I * ((2 * Real.pi * κ₂ : ℝ) : ℂ) * (s : ℂ))‖
      < a * ‖Complex.exp (-Complex.I * ((2 * Real.pi * κ₃ : ℝ) : ℂ) * (s : ℂ))‖ := by
  rw [reversible_generator_flow_unitary (2 * Real.pi * κ₂) s,
    reversible_generator_flow_unitary (2 * Real.pi * κ₃) s]
  simpa using hba

/-- **[The Bisognano–Wichmann ladder crosses in imaginary modular time]** — the BW eigenvalue
`Δ(κ) = e^{−2πκ}` (Unruh–Boltzmann weight, imaginary action `S_I = 2πκ`) decays as `e^{−2πκs}` along the
**Euclidean continuation** of the modular flow — the entropic direction of §2, not the unitary flow of
`real_modular_ordering_frozen`.  There, two boost energies `κ₂ < κ₃` cross at
`s* = log(a/b)/(2π(κ₃−κ₂))`: anomalous relaxation ordering inside the BW wedge structure, carried entirely
by entropic time. -/
theorem wedge_modular_mpemba_crossing {a b κ₂ κ₃ : ℝ} (ha : 0 < a) (hb : 0 < b) (hκ : κ₂ < κ₃)
    {s : ℝ} (hs : mpembaCrossingTime a b (-(2 * Real.pi * κ₂)) (-(2 * Real.pi * κ₃)) < s) :
    a * Real.exp (-(2 * Real.pi * κ₃) * s) < b * Real.exp (-(2 * Real.pi * κ₂) * s) :=
  mpemba_crossing ha hb (by nlinarith [Real.pi_pos]) hs

/-! ## §M. The moiré weld: the envelope is a modulus and reads only the difference -/

/-- **[The moiré envelope is the modulus of a two-phase superposition]** — two periodic patterns at
wavenumbers `k₁, k₂` superpose into carrier × envelope, and the **modulus depends only on the
difference**: `‖e^{ik₁x} + e^{ik₂x}‖ = 2·|cos((k₁−k₂)x/2)|`.  The moiré effect is the spatial twin of the
Mpemba difference structure: the strip split (§2) sends the common carrier to pure phase and the
difference to the observable envelope — moiré fringes magnify `Δk` exactly as the crossing reads `Δλ`. -/
theorem moire_envelope_modulus (k₁ k₂ x : ℝ) :
    ‖Complex.exp (Complex.I * (k₁ : ℂ) * (x : ℂ)) + Complex.exp (Complex.I * (k₂ : ℂ) * (x : ℂ))‖
      = 2 * |Real.cos ((k₁ - k₂) / 2 * x)| := by
  have h2cos : Complex.exp ((((k₁ - k₂) / 2 * x : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-(((k₁ - k₂) / 2 * x : ℝ) : ℂ) * Complex.I)
      = 2 * Complex.cos ((((k₁ - k₂) / 2 * x : ℝ) : ℂ)) := by
    rw [Complex.cos]
    ring
  have e1 : Complex.I * (k₁ : ℂ) * (x : ℂ)
      = Complex.I * (((k₁ + k₂) / 2 : ℝ) : ℂ) * (x : ℂ)
        + (((k₁ - k₂) / 2 * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have e2 : Complex.I * (k₂ : ℂ) * (x : ℂ)
      = Complex.I * (((k₁ + k₂) / 2 : ℝ) : ℂ) * (x : ℂ)
        + -(((k₁ - k₂) / 2 * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hfac : Complex.exp (Complex.I * (k₁ : ℂ) * (x : ℂ))
        + Complex.exp (Complex.I * (k₂ : ℂ) * (x : ℂ))
      = Complex.exp (Complex.I * (((k₁ + k₂) / 2 : ℝ) : ℂ) * (x : ℂ))
        * (2 * Complex.cos ((((k₁ - k₂) / 2 * x : ℝ) : ℂ))) := by
    rw [e1, e2, Complex.exp_add, Complex.exp_add, ← mul_add, h2cos]
  rw [hfac, norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (((k₁ + k₂) / 2 : ℝ) : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero, one_mul, ← Complex.ofReal_cos]
  simp only [norm_mul, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs]

/-- **[The moiré null is a unit-free calibration point]** — the envelope's first null sits at
`(k₁−k₂)·x = π`: a pure number, playing exactly the role `log(a/b)` plays for the crossing — reading a
null *position* measures the wavenumber difference with no calibrated length scale. -/
theorem moire_null {k₁ k₂ x : ℝ} (h : (k₁ - k₂) * x = Real.pi) :
    ‖Complex.exp (Complex.I * (k₁ : ℂ) * (x : ℂ)) + Complex.exp (Complex.I * (k₂ : ℂ) * (x : ℂ))‖
      = 0 := by
  rw [moire_envelope_modulus]
  have harg : (k₁ - k₂) / 2 * x = Real.pi / 2 := by linarith [h]
  rw [harg, Real.cos_pi_div_two]
  simp

/-- **[The twist-moiré law]** — two equal-wavenumber patterns rotated by `θ` have moiré wavevector of
magnitude `2k·sin(θ/2)`: the unit-vector difference obeys
`√((cos θ − 1)² + sin²θ) = 2|sin(θ/2)|`.  Small twists give large magnification `1/(2 sin(θ/2))`
(`14×` at `4°`, `57×` at `1°`) — the rotational generalization of `moire_envelope_modulus`, and the law
behind twisted-bilayer moiré superlattices.  Externally cross-validated against the independent
`moire-optics-lab` implementation to machine precision. -/
theorem twist_moire_wavenumber (θ : ℝ) :
    Real.sqrt ((Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2) = 2 * |Real.sin (θ / 2)| := by
  have h1 : (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 = 2 - 2 * Real.cos θ := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hs : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    have hraw := Real.sin_sq_eq_half_sub (θ / 2)
    have h22 : 2 * (θ / 2) = θ := by ring
    rw [h22] at hraw
    linarith [hraw]
  have h2 : 2 - 2 * Real.cos θ = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    have habs : |Real.sin (θ / 2)| ^ 2 = Real.sin (θ / 2) ^ 2 := sq_abs _
    nlinarith [hs, habs]
  rw [h1, h2, Real.sqrt_sq (by positivity)]

/-! ## §D. The deferred-moiré vibrometer (Saveljev–Son–Lee–Heo 2023) -/

/-- **[Eq. (3), Saveljev et al. 2023]** — the period of the moiré patterns of two parallel grids of
periods `T₁, T₂`: `T_M = T₁T₂/|T₁ − T₂|` (Saveljev–Son–Lee–Heo, *Non-contact measurement of vibrations
using deferred moiré patterns*, Adv. Mech. Eng. 15(4) 2023, 10.1177/16878132221143885; after Amidror). -/
def moirePeriod (T₁ T₂ : ℝ) : ℝ := T₁ * T₂ / |T₁ - T₂|

/-- **[Eq. (4)]** — the moiré magnification coefficient `μ = 1/|1 − T₂/T₁|`: for close periods
`T₂ ≈ T₁` it is large. -/
def moireMagnification (T₁ T₂ : ℝ) : ℝ := 1 / |1 - T₂ / T₁|

/-- **[Eq. (3) = Eq. (4) × grid]** — the moiré period is the grid period magnified `μ` times:
`T_M = μ·T₂`.  At `T₁ = T₂` both sides read the same junk value `0`. -/
theorem moire_period_is_magnified_grid {T₁ : ℝ} (h₁ : 0 < T₁) (T₂ : ℝ) :
    moirePeriod T₁ T₂ = moireMagnification T₁ T₂ * T₂ := by
  unfold moirePeriod moireMagnification
  have h1' := h₁.ne'
  have h0 : (1 : ℝ) - T₂ / T₁ = (T₁ - T₂) / T₁ := by field_simp
  rw [h0, abs_div, abs_of_pos h₁, one_div_div]
  ring

/-- **[Eqs. (1)–(2) weld]** — Amidror's wavevector law `k_M = k₁ − k₂` (the difference structure of
`moire_envelope_modulus`) *is* Eq. (3): with `k ᵢ = 2π/Tᵢ`, `|k₁ − k₂| = 2π/T_M`. -/
theorem moire_period_from_wavenumbers {T₁ T₂ : ℝ} (h₁ : 0 < T₁) (h₂ : 0 < T₂) :
    |2 * Real.pi / T₁ - 2 * Real.pi / T₂| = 2 * Real.pi / moirePeriod T₁ T₂ := by
  have h1' := h₁.ne'
  have h2' := h₂.ne'
  unfold moirePeriod
  rw [div_div_eq_mul_div]
  have hd : 2 * Real.pi / T₁ - 2 * Real.pi / T₂ = 2 * Real.pi * (T₂ - T₁) / (T₁ * T₂) := by
    field_simp
  rw [hd, abs_div, abs_mul, abs_of_pos (mul_pos h₁ h₂),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_sub_comm]

/-- **[general phase superposition]** — the modulus of a two-phase superposition reads only the phase
difference: `‖e^{iφ₁} + e^{iφ₂}‖ = 2|cos((φ₁−φ₂)/2)|` — the `moire_envelope_modulus` mechanism for
arbitrary phases, needed because a *displaced* grid carries phase `k₂(x − δ)`, not `k₂x`. -/
theorem phase_superposition_modulus (φ₁ φ₂ : ℝ) :
    ‖Complex.exp (Complex.I * (φ₁ : ℂ)) + Complex.exp (Complex.I * (φ₂ : ℂ))‖
      = 2 * |Real.cos ((φ₁ - φ₂) / 2)| := by
  have h2cos : Complex.exp ((((φ₁ - φ₂) / 2 : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-(((φ₁ - φ₂) / 2 : ℝ) : ℂ) * Complex.I)
      = 2 * Complex.cos ((((φ₁ - φ₂) / 2 : ℝ) : ℂ)) := by
    rw [Complex.cos]
    ring
  have e1 : Complex.I * (φ₁ : ℂ)
      = Complex.I * (((φ₁ + φ₂) / 2 : ℝ) : ℂ) + (((φ₁ - φ₂) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have e2 : Complex.I * (φ₂ : ℂ)
      = Complex.I * (((φ₁ + φ₂) / 2 : ℝ) : ℂ) + -(((φ₁ - φ₂) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hfac : Complex.exp (Complex.I * (φ₁ : ℂ)) + Complex.exp (Complex.I * (φ₂ : ℂ))
      = Complex.exp (Complex.I * (((φ₁ + φ₂) / 2 : ℝ) : ℂ))
        * (2 * Complex.cos ((((φ₁ - φ₂) / 2 : ℝ) : ℂ))) := by
    rw [e1, e2, Complex.exp_add, Complex.exp_add, ← mul_add, h2cos]
  rw [hfac, norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (((φ₁ + φ₂) / 2 : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero, one_mul, ← Complex.ofReal_cos]
  simp only [norm_mul, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs]

/-- **[Eq. (5): moiré phase magnification]** — displacing the grid by `δ` displaces the moiré envelope
by `x_M = k₂δ/(k₁−k₂) = μ·δ`: `‖e^{ik₁x} + e^{ik₂(x−δ)}‖ = 2|cos((k₁−k₂)/2·(x + x_M))|`.  The deferred
superposition (photographed grid × later computer-generated grid) turns a sub-pixel object displacement
into a `μ`-times-larger fringe displacement — the self-calibrated non-contact vibrometer. -/
theorem deferred_moire_displacement {k₁ k₂ : ℝ} (hne : k₁ ≠ k₂) (x d : ℝ) :
    ‖Complex.exp (Complex.I * (k₁ : ℂ) * (x : ℂ))
        + Complex.exp (Complex.I * (k₂ : ℂ) * ((x : ℂ) - (d : ℂ)))‖
      = 2 * |Real.cos ((k₁ - k₂) / 2 * (x + k₂ * d / (k₁ - k₂)))| := by
  have hsub : k₁ - k₂ ≠ 0 := sub_ne_zero.mpr hne
  have hφ₁ : Complex.I * (k₁ : ℂ) * (x : ℂ) = Complex.I * ((k₁ * x : ℝ) : ℂ) := by
    push_cast
    ring
  have hφ₂ : Complex.I * (k₂ : ℂ) * ((x : ℂ) - (d : ℂ))
      = Complex.I * ((k₂ * (x - d) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hφ₁, hφ₂, phase_superposition_modulus]
  have harg : (k₁ * x - k₂ * (x - d)) / 2 = (k₁ - k₂) / 2 * (x + k₂ * d / (k₁ - k₂)) := by
    field_simp
    ring
  rw [harg]

/-- **[sub-pixel resolution]** — for close wavenumbers (`|k₁−k₂| < |k₂|`) the fringe displacement
strictly exceeds the object displacement, `|d| < |x_M|`: "it is not principally impossible to measure
very small displacements which are less than 1 pixel" — the magnification is why. -/
theorem deferred_subpixel_magnification {k₁ k₂ d : ℝ} (hne : k₁ ≠ k₂)
    (hclose : |k₁ - k₂| < |k₂|) (hd : d ≠ 0) :
    |d| < |k₂ * d / (k₁ - k₂)| := by
  have h0 : 0 < |k₁ - k₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hd0 : 0 < |d| := abs_pos.mpr hd
  rw [abs_div, abs_mul, lt_div_iff₀ h0]
  nlinarith

/-- **[Eq. (6), McConnell]** — the fundamental frequency of a beam of modulus `E`, moment `I`, linear
mass density `λ_m`, length `L`: `f₀ = (π/2)·√(EI/(λ_m L⁴))`. -/
def beamFundamentalFrequency (E I lm L : ℝ) : ℝ :=
  Real.pi / 2 * Real.sqrt (E * I / (lm * L ^ 4))

/-- **[Eqs. (9)–(10)]** — substituting the rod moment `I = ρsL³/12` splits the frequency into
material × geometry: `f₀ = (π/4)·√(Eρ/(3λ_m))·√(s/L)` — "the first multiplicand includes only the
mathematical constants together with the material constants, while the second describes the geometry of
the rod". -/
theorem beam_frequency_rod_form {E ρ s lm L : ℝ} (hE : 0 < E) (hρ : 0 < ρ) (hs : 0 < s)
    (hlm : 0 < lm) (hL : 0 < L) :
    beamFundamentalFrequency E (ρ * s * L ^ 3 / 12) lm L
      = Real.pi / 4 * Real.sqrt (E * ρ / (3 * lm)) * Real.sqrt (s / L) := by
  unfold beamFundamentalFrequency
  have hrad : E * (ρ * s * L ^ 3 / 12) / (lm * L ^ 4) = E * ρ * s / (3 * lm * L) / 4 := by
    field_simp
    ring
  rw [hrad, Real.sqrt_div (by positivity) 4]
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hjoin : E * ρ / (3 * lm) * (s / L) = E * ρ * s / (3 * lm * L) := by
    field_simp
  have hR : Real.pi / 4 * Real.sqrt (E * ρ / (3 * lm)) * Real.sqrt (s / L)
      = Real.pi / 4 * Real.sqrt (E * ρ * s / (3 * lm * L)) := by
    rw [mul_assoc, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ E * ρ / (3 * lm)) (s / L), hjoin]
  rw [h4, hR]
  ring

/-- **[crack factor 1]** — in the geometry factor `√(s/L)` a smaller cross-section lowers the
frequency ("a smaller cross-section makes the frequency fall"). -/
theorem crack_frequency_falls_with_section {s₁ s₂ L : ℝ} (hL : 0 < L) (h0 : 0 ≤ s₁)
    (h : s₁ < s₂) : Real.sqrt (s₁ / L) < Real.sqrt (s₂ / L) := by
  gcongr

/-- **[crack factor 2]** — a shorter effective length raises it ("the frequency of the shortened beam
of the same cross-section is higher"). -/
theorem crack_frequency_rises_with_shortening {s L₁ L₂ : ℝ} (hs : 0 < s) (hL₁ : 0 < L₁)
    (h : L₁ < L₂) : Real.sqrt (s / L₂) < Real.sqrt (s / L₁) := by
  have hL₂ : 0 < L₂ := hL₁.trans h
  apply Real.sqrt_lt_sqrt (by positivity)
  exact div_lt_div_of_pos_left hs hL₁ h

/-- **[the cancellation depth]** — the two factors are "comparable but opposite, because the
corresponding variables are on the opposite sides of the fraction": scaling section and length together
leaves the geometry factor exactly unchanged, so a cut depth exists where they cancel — which is why
frequency alone is an ambiguous health indicator. -/
theorem crack_factors_cancel {c : ℝ} (hc : c ≠ 0) (s L : ℝ) :
    Real.sqrt (c * s / (c * L)) = Real.sqrt (s / L) := by
  rw [mul_div_mul_left s L hc]

/-- **[Rayleigh deflection identity]** — for a mode in static equilibrium under gravity (`k·d = m·g`)
with natural frequency `ω² = k/m`, the stiffness and mass cancel exactly: `ω²·d = g`.  The two
moiré-readable observables of a structure — its frequency and its gravitational sag — multiply to `g`
with no material constant surviving. -/
theorem rayleigh_deflection_gravimeter {k m d g ω : ℝ} (hm : m ≠ 0)
    (heq : k * d = m * g) (hω : ω ^ 2 = k / m) : ω ^ 2 * d = g := by
  rw [hω]
  field_simp
  linear_combination heq

/-- **[the structural gravimeter]** — Eq. (6) squared times the cantilever self-weight deflection
`d = λ_m g L⁴/(8EI)`: modulus, moment, density and length all cancel, leaving `f₀²·d = (π²/32)·g`.
Any beam photographed through a grid computes `g` from its own frequency and sag — self-calibrated,
material-blind.  (The `π²/32` inherits Eq. (6)'s mode coefficient; the cancellation is the invariant
content.) -/
theorem cantilever_selfweight_gravimeter {E I lm L : ℝ} (hE : 0 < E) (hI : 0 < I)
    (hlm : 0 < lm) (hL : 0 < L) (g : ℝ) :
    beamFundamentalFrequency E I lm L ^ 2 * (lm * g * L ^ 4 / (8 * (E * I)))
      = Real.pi ^ 2 / 32 * g := by
  unfold beamFundamentalFrequency
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ E * I / (lm * L ^ 4))]
  field_simp
  ring

/-- **[the recovery is exact and parameter-free]** — inverting: `g = 32·f₀²·d/π²`, with every
right-hand quantity measured (frequency from the time series, sag from the magnified static fringe
shift of Eq. (5)) and no beam parameter appearing. -/
theorem structural_gravimeter_recovery {E I lm L : ℝ} (hE : 0 < E) (hI : 0 < I)
    (hlm : 0 < lm) (hL : 0 < L) (g : ℝ) :
    32 * (beamFundamentalFrequency E I lm L ^ 2 * (lm * g * L ^ 4 / (8 * (E * I))))
        / Real.pi ^ 2 = g := by
  rw [cantilever_selfweight_gravimeter hE hI hlm hL g]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **[the envelope is frequency-blind]** — the measured amplitude envelope of a damped structural mode
`λ = −Γ + iω` is `‖e^{λt}‖ = e^{−Γt}` (`flow_norm_from_re`) for *every* frequency: equal decay and
different frequencies give identical envelopes.  The moiré-read amplitude decay measures the entropic
sector alone. -/
theorem envelope_is_frequency_blind (Γ ω₁ ω₂ t : ℝ) :
    ‖Complex.exp ((⟨-Γ, ω₁⟩ : ℂ) * (t : ℂ))‖ = ‖Complex.exp ((⟨-Γ, ω₂⟩ : ℂ) * (t : ℂ))‖ := by
  rw [flow_norm_from_re, flow_norm_from_re]

/-- **[the envelope separates decay rates]** — while frequency-blind, the envelope *strictly* separates
decay rates at every `t > 0`: the amplitude envelope measures `Γ` and only `Γ`.  This is the exact
content behind the paper's finding that the broken rod moves the lifetime from 2.8–4.4 s to 7.3–9.2 s
(doubled) while the frequency moves 4.68 → 4.36 Hz (7%): the envelope observable is the decay's own
sector. -/
theorem envelope_separates_decay {Γ₁ Γ₂ : ℝ} (h : Γ₁ < Γ₂) (ω₁ ω₂ : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖Complex.exp ((⟨-Γ₂, ω₂⟩ : ℂ) * (t : ℂ))‖ < ‖Complex.exp ((⟨-Γ₁, ω₁⟩ : ℂ) * (t : ℂ))‖ := by
  rw [flow_norm_from_re, flow_norm_from_re]
  show Real.exp (-Γ₂ * t) < Real.exp (-Γ₁ * t)
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- **[deferred-moiré health synthesis]** — the vibrometer chain: (i) phase magnification (Eq. 5) makes
sub-pixel structural displacement measurable; (ii) the amplitude envelope is frequency-blind; (iii) yet
strictly decay-separating.  The deferred moiré pattern reads the entropic sector (`Re λ = −Γ`) of the
structural mode directly — which is why the decay rate, not the frequency, is the pre-failure
indicator. -/
theorem deferred_moire_health_synthesis {k₁ k₂ d Γ₁ Γ₂ t : ℝ} (hne : k₁ ≠ k₂)
    (hclose : |k₁ - k₂| < |k₂|) (hd : d ≠ 0) (hΓ : Γ₁ < Γ₂) (ht : 0 < t) (ω₁ ω₂ : ℝ) :
    |d| < |k₂ * d / (k₁ - k₂)|
      ∧ ‖Complex.exp ((⟨-Γ₁, ω₁⟩ : ℂ) * (t : ℂ))‖ = ‖Complex.exp ((⟨-Γ₁, ω₂⟩ : ℂ) * (t : ℂ))‖
      ∧ ‖Complex.exp ((⟨-Γ₂, ω₂⟩ : ℂ) * (t : ℂ))‖ < ‖Complex.exp ((⟨-Γ₁, ω₁⟩ : ℂ) * (t : ℂ))‖ :=
  ⟨deferred_subpixel_magnification hne hclose hd, envelope_is_frequency_blind Γ₁ ω₁ ω₂ t,
    envelope_separates_decay hΓ ω₁ ω₂ ht⟩

/-! ## §L. Moiré lattice commensurability: the localization–delocalization dichotomy -/

/-- **[Pythagorean twist cosine]** — `cos θ = (p²−q²)/(p²+q²)`: the rational rotation angles of a
square lattice (photonic moiré lattices, Wang–Ye–Fu–Zhong–Cao–Torner–Kartashov, Nature 577, 42
(2020), 10.1038/s41586-019-1851-6). -/
def pythagoreanCos (p q : ℤ) : ℝ := ((p : ℝ) ^ 2 - (q : ℝ) ^ 2) / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)

/-- **[Pythagorean twist sine]** — `sin θ = 2pq/(p²+q²)`. -/
def pythagoreanSin (p q : ℤ) : ℝ := 2 * (p : ℝ) * (q : ℝ) / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)

/-- **[the twist point is on the unit circle]** — `cos²θ + sin²θ = 1` exactly: every Pythagorean pair
`(p, q)` is a genuine rotation. -/
theorem pythagorean_twist_on_circle {p q : ℤ} (h : (p : ℝ) ^ 2 + (q : ℝ) ^ 2 ≠ 0) :
    pythagoreanCos p q ^ 2 + pythagoreanSin p q ^ 2 = 1 := by
  unfold pythagoreanCos pythagoreanSin
  field_simp
  ring

/-- **[commensurate twist: a shared superlattice]** — at a Pythagorean twist the rotation carries
`(p²+q²)·ℤ²` into `ℤ²`: the two layers share a periodic superlattice of cell index `p²+q²`, the moiré
pattern is periodic, and modes are Bloch-extended — the *delocalized* side of the dichotomy. -/
theorem pythagorean_twist_commensurate {p q : ℤ} (h : (p : ℝ) ^ 2 + (q : ℝ) ^ 2 ≠ 0)
    (a b : ℤ) :
    ∃ m n : ℤ,
      ((p ^ 2 + q ^ 2 : ℤ) : ℝ) * ((a : ℝ) * pythagoreanCos p q - (b : ℝ) * pythagoreanSin p q)
          = (m : ℝ)
      ∧ ((p ^ 2 + q ^ 2 : ℤ) : ℝ) * ((a : ℝ) * pythagoreanSin p q + (b : ℝ) * pythagoreanCos p q)
          = (n : ℝ) := by
  unfold pythagoreanCos pythagoreanSin
  refine ⟨a * (p ^ 2 - q ^ 2) - 2 * b * p * q, 2 * a * p * q + b * (p ^ 2 - q ^ 2), ?_, ?_⟩
  · push_cast
    field_simp
  · push_cast
    field_simp

/-- **[incommensurate twist: no shared lattice point]** — if `cos θ` is irrational, the only integer
point the rotation carries back to an integer point is the origin: the layers share no period, the
moiré pattern is quasiperiodic, and localization becomes possible — the *localizing* side.  (Key:
`a·(R v)₁ + b·(R v)₂ = (a²+b²)·cos θ` by pure algebra, so a nonzero common point would make `cos θ`
rational.) -/
theorem incommensurate_twist_no_common_lattice {c s : ℝ} (hc : Irrational c)
    {a b m n : ℤ} (h₁ : (a : ℝ) * c - (b : ℝ) * s = (m : ℝ))
    (h₂ : (a : ℝ) * s + (b : ℝ) * c = (n : ℝ)) : a = 0 ∧ b = 0 := by
  by_contra hab
  have hkey : ((a ^ 2 + b ^ 2 : ℤ) : ℝ) * c = ((a * m + b * n : ℤ) : ℝ) := by
    push_cast
    linear_combination (a : ℝ) * h₁ + (b : ℝ) * h₂
  have hAB : (a ^ 2 + b ^ 2 : ℤ) ≠ 0 := by
    intro h0
    have ha2 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb2 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact hab ⟨sq_eq_zero_iff.mp ha2, sq_eq_zero_iff.mp hb2⟩
  have hABR : ((a ^ 2 + b ^ 2 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hAB
  have hc' : c = ((a * m + b * n : ℤ) : ℝ) / ((a ^ 2 + b ^ 2 : ℤ) : ℝ) :=
    eq_div_of_mul_eq hABR (by linear_combination hkey)
  refine hc ⟨((a * m + b * n : ℤ) : ℚ) / ((a ^ 2 + b ^ 2 : ℤ) : ℚ), ?_⟩
  rw [hc']
  push_cast
  ring

/-! ## §Z. The moiré Zeeman effect: periodic magnetization as an Umklapp splitting -/

/-- **[the Umklapp splitting geometry factor]** — `(Δ/2)(1 + cos 2δθ_G)`: the splitting of the bright
Umklapp exciton resonances under a periodic Zeeman modulation of amplitude `Δ = gμ_B|B_G|`, with `δθ_G`
the angle between consecutive reciprocal vectors (Gómez Salvador–Kuhlenkamp–Ciorciaro–Knap–İmamoğlu,
*Optical Signatures of Periodic Magnetization: The Moiré Zeeman Effect*, arXiv:2112.10276). -/
def moireZeemanSplitting (D dth : ℝ) : ℝ := D / 2 * (1 + Real.cos (2 * dth))

/-- **[the geometry factor is a half-angle law]** — `(Δ/2)(1 + cos 2δθ) = Δ·cos²δθ`: the same
half-angle structure as the twist law `2k sin(θ/2)` — moiré geometry enters observables through
half-angle identities. -/
theorem moire_zeeman_splitting_half_angle (D dth : ℝ) :
    moireZeemanSplitting D dth = D * Real.cos dth ^ 2 := by
  unfold moireZeemanSplitting
  rw [Real.cos_sq]
  ring

/-- **[triangular lattice: `Δ/4`]** — at `δθ_G = π/3` (the featureless triangular moiré magnet) the
splitting is exactly `Δ/4`, linear in the periodic field amplitude. -/
theorem moire_zeeman_splitting_triangular (D : ℝ) :
    moireZeemanSplitting D (Real.pi / 3) = D / 4 := by
  unfold moireZeemanSplitting
  have h : Real.cos (2 * (Real.pi / 3)) = -(1 / 2) := by
    have h23 : 2 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
    rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [h]
  ring

/-- **[the discriminator: periodic vs uniform magnetization]** — zero-momentum excitons feel only the
*average* field (first order): for a zero-average periodic modulation their splitting `gμ_B B₀/2`
vanishes, while the Umklapp coupling `gμ_B B_G/2` survives.  The Umklapp splitting is a
background-free optical probe of *periodic* magnetization — invisible to the `k = 0` probe that any
uniform field would light up. -/
theorem moire_zeeman_discriminator {g muB BG : ℝ} (hg : g * muB ≠ 0) (hBG : BG ≠ 0)
    (B0 : ℝ) (h0 : B0 = 0) :
    g * muB * B0 / 2 = 0 ∧ g * muB * BG / 2 ≠ 0 := by
  constructor
  · rw [h0]
    ring
  · exact div_ne_zero (mul_ne_zero hg hBG) (by norm_num)

/-- **[the restoration magnetometer]** — a ferromagnetic moiré lattice shifts the effective `σ_z`
coefficient to `n_e(λ−μ)/2 + gμ_B B_e/2`; it vanishes exactly at `B_e = n_e(μ−λ)/(gμ_B)`: the external
field that restores the zero-average spectrum *reads* the exciton–electron interaction asymmetry
`n_e(μ−λ)` — an exact inversion, the magnetic sibling of the arc's gravimeter recoveries. -/
theorem moire_zeeman_magnetometer {g muB nel lam mu Be : ℝ} (hg : g * muB ≠ 0) :
    nel * (lam - mu) / 2 + g * muB * Be / 2 = 0 ↔ Be = nel * (mu - lam) / (g * muB) := by
  rw [eq_div_iff hg]
  constructor
  · intro h
    linear_combination 2 * h
  · intro h
    linear_combination h / 2

/-! ## §T. Two-frequency moiré topography: absolute fringe order -/

/-- **[shadow-moiré contour interval]** — `Δh = p/(tan α + tan β)` for grating period `p` and
illumination/viewing angles `α, β` (Takasaki's formula — the setting of Ibrahim–Takasaki,
*Two-Frequency Moiré Topography*, Jpn. J. Appl. Phys. 24 (1985) 1181). -/
def shadowContourInterval (p α β : ℝ) : ℝ := p / (Real.tan α + Real.tan β)

/-- **[the decorated ladder is exact]** — the coarse grating (period `M·p`, made by filling every
`M`-th clearance with thick thread) has contour interval exactly `M` times the fine one: the decorated
fringes fall on every `M`-th contour, so counting from a decorated fringe yields the fine order. -/
theorem decorated_contour_ladder (M p α β : ℝ) :
    shadowContourInterval (M * p) α β = M * shadowContourInterval p α β := by
  unfold shadowContourInterval
  rw [mul_div_assoc]

/-- **[two-frequency unambiguous range]** — two heights indistinguishable to the coarse system
(differing by an integer number of coarse intervals `M·T`) yet lying within one coarse interval are
*equal*: the decoration extends the unambiguous range of the fine system from `T` to `M·T` (×10 in the
paper) — absolute fringe order, resolving the integer that any single wrapped phase loses.  This is
the wrap limit met by the structural gravimeter's sag measurement, removed. -/
theorem two_frequency_unambiguous_range {h h' MT : ℝ} (hMT : 0 < MT) {k : ℤ}
    (hk : h - h' = k * MT) (hb : |h - h'| < MT) : h = h' := by
  have hkabs : |(k : ℝ)| * MT < MT := by
    calc |(k : ℝ)| * MT = |(k : ℝ) * MT| := by rw [abs_mul, abs_of_pos hMT]
      _ = |h - h'| := by rw [← hk]
      _ < MT := hb
  have hk1 : |(k : ℝ)| < 1 := by
    by_contra hge
    push_neg at hge
    nlinarith
  have hk0 : k = 0 := by
    have h1 : ((|k| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs]
      exact hk1
    have h2 : |k| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp h2
  rw [hk0] at hk
  push_cast at hk
  linarith

/-- **[Takasaki fringe height]** — with source and observer at distance `l` from the grating,
separated by `s`, the `N`-th shadow-moiré fringe sits at height `h_N = N·p·l/(s − N·p)`: the ladder is
*nonlinear* — "the height step between the successive moiré fringes increases with the order" — which
is exactly why quantitative topography needs the absolute order. -/
def takasakiFringeHeight (N p l s : ℝ) : ℝ := N * p * l / (s - N * p)

/-- **[the step formula]** — `h_{N+1} − h_N = p·l·s/((s−(N+1)p)(s−Np))` exactly. -/
theorem takasaki_step_formula {N p l s : ℝ} (h1 : s - N * p ≠ 0) (h2 : s - (N + 1) * p ≠ 0) :
    takasakiFringeHeight (N + 1) p l s - takasakiFringeHeight N p l s
      = p * l * s / ((s - (N + 1) * p) * (s - N * p)) := by
  unfold takasakiFringeHeight
  field_simp
  ring

/-- **[the steps increase with order]** — each height step strictly exceeds the previous one while the
fringe stays below the source plane: the paper's motivating nonlinearity. -/
theorem takasaki_step_increases {N p l s : ℝ} (hp : 0 < p) (hl : 0 < l) (hs : 0 < s)
    (hbound : (N + 2) * p < s) :
    p * l * s / ((s - (N + 1) * p) * (s - N * p))
      < p * l * s / ((s - (N + 2) * p) * (s - (N + 1) * p)) := by
  have hC : 0 < s - (N + 2) * p := by linarith
  have hB : 0 < s - (N + 1) * p := by nlinarith
  have hA : 0 < s - N * p := by nlinarith
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  nlinarith

/-- **[constant ladder × correction]** — `h_N = N·(pl/s)·(s/(s−Np))`: the flat-object constant
interval `pl/s` times the finite-geometry correction, which `→ 1` only for `Np ≪ s`. -/
theorem takasaki_small_pitch_form {N p l s : ℝ} (hs : s ≠ 0) (hd : s - N * p ≠ 0) :
    takasakiFringeHeight N p l s = N * (p * l / s) * (s / (s - N * p)) := by
  unfold takasakiFringeHeight
  field_simp

/-- **[order inversion]** — from the Takasaki relation `h(s − Np) = Npl`, the absolute order is
recovered as `N = h·s/(p(l+h))`: the quantitative measurement the decoration makes possible. -/
theorem takasaki_order_inversion {N p l s h : ℝ} (hden : p * (l + h) ≠ 0)
    (hrel : h * (s - N * p) = N * p * l) : N = h * s / (p * (l + h)) := by
  rw [eq_div_iff hden]
  linear_combination -hrel

/-- **[closed fringes are sign-blind]** — the moiré envelope at height `h` equals the envelope at
`−h`: a closed contour fringe cannot tell a bump from a dip.  This is the paper's second problem —
"closed moiré fringes are shown either on a concave or convex portion" — resolved by the oblique
intersection lines, not by the fringes themselves. -/
theorem moire_envelope_sign_blind (k₁ k₂ h : ℝ) :
    ‖Complex.exp (Complex.I * (k₁ : ℂ) * (h : ℂ)) + Complex.exp (Complex.I * (k₂ : ℂ) * (h : ℂ))‖
      = ‖Complex.exp (Complex.I * (k₁ : ℂ) * ((-h : ℝ) : ℂ))
          + Complex.exp (Complex.I * (k₂ : ℂ) * ((-h : ℝ) : ℂ))‖ := by
  rw [moire_envelope_modulus, moire_envelope_modulus, mul_neg, Real.cos_neg]

/-- **[the oblique shadow reads height]** — the lateral shadow shift of a grating line grows with the
distance from the grating: `u = h·tan α`. -/
def obliqueShadowShift (h α : ℝ) : ℝ := h * Real.tan α

/-- **[fringe condition inverts to height]** — a bright fringe forms where the shift is a whole number
of pitches, `u = N·p`, so `h = N·p/tan α`. -/
theorem shadow_fringe_height {h α N p : ℝ} (ht : Real.tan α ≠ 0)
    (hf : obliqueShadowShift h α = N * p) : h = N * p / Real.tan α := by
  unfold obliqueShadowShift at hf
  rw [eq_div_iff ht]
  linear_combination hf

/-- **[decoration marks exactly the multiples]** — the thick thread (period `M·p`) shadows land on
bright fringes whose fine order satisfies `N·p = j·(M·p)`, i.e. `N = j·M`: "the order of these bright
moiré fringes is a multiple of ten". -/
theorem decoration_marks_multiples {N j M p : ℝ} (hp : p ≠ 0)
    (hshadow : N * p = j * (M * p)) : N = j * M :=
  mul_right_cancel₀ hp (by linear_combination hshadow)

/-- **[counting from the decorated fringe is well-defined]** — the decomposition
`N = M·q + r` with `0 ≤ r < M` (decorated index `q`, offset count `r`) is unique: the paper's counting
protocol determines the absolute order unambiguously. -/
theorem decorated_count_unique {M q r q' r' : ℤ} (hM : 0 < M)
    (h : M * q + r = M * q' + r') (hr0 : 0 ≤ r) (hrM : r < M) (hr0' : 0 ≤ r') (hrM' : r' < M) :
    q = q' ∧ r = r' := by
  have hd : M * (q - q') = r' - r := by linear_combination h
  have habs : |r' - r| < M := abs_lt.mpr ⟨by omega, by omega⟩
  have hq : q = q' := by
    by_contra hne
    have h1 : 1 ≤ |q - q'| := Int.one_le_abs (sub_ne_zero.mpr hne)
    have h2 : M ≤ M * |q - q'| := le_mul_of_one_le_right hM.le h1
    rw [← abs_of_pos hM, ← abs_mul, hd] at h2
    rw [abs_of_pos hM] at h2
    exact absurd habs (not_lt.mpr h2)
  refine ⟨hq, ?_⟩
  rw [hq] at h
  linarith

/-- **[integer and half-integer orders]** — "the bright fringes are ordered without fractions, while
the dark fringes are ordered with a fraction of 0.5": at integer order the fringe carrier is extremal
(`cos²(Nπ) = 1`), at half-integer order it is null (`cos((N+½)π) = 0` — the `moire_null` of the
contour system). -/
theorem fringe_order_parity (N : ℤ) :
    Real.cos ((N : ℝ) * Real.pi) ^ 2 = 1 ∧ Real.cos (((N : ℝ) + 1 / 2) * Real.pi) = 0 := by
  constructor
  · have hpy := Real.sin_sq_add_cos_sq ((N : ℝ) * Real.pi)
    rw [Real.sin_int_mul_pi] at hpy
    nlinarith [hpy]
  · have harg : ((N : ℝ) + 1 / 2) * Real.pi = (N : ℝ) * Real.pi + Real.pi / 2 := by ring
    rw [harg, Real.cos_add_pi_div_two, Real.sin_int_mul_pi, neg_zero]

/-- **[the reference marks self-calibrate the photograph]** — bright threads a known distance apart
appear magnified by the same unknown factor `m` as the measured shift, so the ratio cancels it:
`(m·u)/(m·D)·D = u`.  "A special calibration procedure is not necessary at all." -/
theorem reference_mark_calibration {m u D : ℝ} (hm : m ≠ 0) (hD : D ≠ 0) :
    m * u / (m * D) * D = u := by
  rw [mul_div_mul_left u D hm, div_mul_cancel₀ u hD]

/-! ## §S. Spectral-trajectory theory of the moiré effect (Saveljev–Kim 2013) -/

/-- **[Eq. (2): the spectral peak]** — the `p`-th peak of a grating of wavenumber `k` rotated by `α`
sits, in the complex plane, at `T_p(α) = p·k·e^{iα}` (Saveljev–Kim, *Theoretical estimation of moiré
effect using spectral trajectories*, Opt. Express 21 (2013) 1693).  The complex plane is the natural
home of moiré spectra — the same plane the entropic-action modes live in. -/
def spectralPeak (p : ℤ) (k α : ℝ) : ℂ :=
  (p : ℂ) * (k : ℂ) * Complex.exp (Complex.I * (α : ℂ))

/-- **[the visibility radius]** — `‖T_p(α)‖ = |p|·|k|`: a peak's distance from the origin (its place in
the visibility circle that models the eye) depends on the order and wavenumber, never on the rotation
angle. -/
theorem spectral_peak_modulus (p : ℤ) (k α : ℝ) :
    ‖spectralPeak p k α‖ = |(p : ℝ)| * |k| := by
  unfold spectralPeak
  have hexp : ‖Complex.exp (Complex.I * (α : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (Complex.I * (α : ℂ)).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [show (p : ℂ) = (((p : ℝ)) : ℂ) by push_cast; ring, norm_mul, norm_mul, hexp,
    mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]

/-- **[Eq. (4), N = 2: the moiré peak is a vector difference]** — the first combinational peak of two
gratings (indices `+1, −1`) is `k₁e^{iα₁} − k₂e^{iα₂}`: Amidror's `k_M = k₁ − k₂` realized as complex
vector subtraction.  This is exactly the general beat used by the external `moire-optics-lab`
`estimate_moire_period` — the code we validated against is this equation. -/
theorem moire_wavevector_difference (k₁ α₁ k₂ α₂ : ℝ) :
    spectralPeak 1 k₁ α₁ + spectralPeak (-1) k₂ α₂
      = (k₁ : ℂ) * Complex.exp (Complex.I * (α₁ : ℂ))
        - (k₂ : ℂ) * Complex.exp (Complex.I * (α₂ : ℂ)) := by
  unfold spectralPeak
  push_cast
  ring

/-- **[the twist law is a spectral-peak difference]** — two equal-wavenumber gratings at angles `0` and
`θ` have moiré peak of modulus `2k|sin(θ/2)|`: `twist_moire_wavenumber` re-derived directly from the
complex-plane peak difference (via `moire_envelope_modulus`, since `−e^{iθ} = e^{i(θ+π)}`).  The
rotational moiré law and the spectral theory are the same statement. -/
theorem twist_law_from_spectral_peaks (k θ : ℝ) (hk : 0 ≤ k) :
    ‖spectralPeak 1 k 0 + spectralPeak (-1) k θ‖ = 2 * k * |Real.sin (θ / 2)| := by
  have hkey : ‖(1 : ℂ) - Complex.exp (Complex.I * (θ : ℂ))‖ = 2 * |Real.sin (θ / 2)| := by
    have hme := moire_envelope_modulus 0 (θ + Real.pi) 1
    have e0 : Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show Complex.I * ((0 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) = 0 by push_cast; ring, Complex.exp_zero]
    have eπ : Complex.exp (Complex.I * (((θ + Real.pi : ℝ)) : ℂ) * ((1 : ℝ) : ℂ))
        = -Complex.exp (Complex.I * (θ : ℂ)) := by
      have harg : Complex.I * (((θ + Real.pi : ℝ)) : ℂ) * ((1 : ℝ) : ℂ)
          = Complex.I * (θ : ℂ) + (Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [e0, eπ] at hme
    have hcos : Real.cos ((0 - (θ + Real.pi)) / 2 * 1) = -Real.sin (θ / 2) := by
      have harg2 : (0 - (θ + Real.pi)) / 2 * 1 = -(θ / 2) - Real.pi / 2 := by ring
      rw [harg2, Real.cos_sub, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
        Real.sin_pi_div_two]
      ring
    rw [hcos, abs_neg] at hme
    rw [show (1 : ℂ) - Complex.exp (Complex.I * (θ : ℂ))
        = 1 + -Complex.exp (Complex.I * (θ : ℂ)) by ring]
    exact hme
  have hdiff : spectralPeak 1 k 0 + spectralPeak (-1) k θ
      = (k : ℂ) * (1 - Complex.exp (Complex.I * (θ : ℂ))) := by
    have h0 : Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    unfold spectralPeak
    rw [h0]
    push_cast
    ring
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, hkey, abs_of_nonneg hk]
  ring

/-- **[Eq. (2): rotation is a circular trajectory]** — varying the rotation angle moves a peak on a
circle of fixed radius: `‖T_p(α₁)‖ = ‖T_p(α₂)‖`.  One of the paper's four trajectory kinds (arcs), and
the geometric content of Eq. (12) `dT_α/dt = iA·T_m` (the derivative is perpendicular to the radius). -/
theorem angle_trajectory_circular (p : ℤ) (k α₁ α₂ : ℝ) :
    ‖spectralPeak p k α₁‖ = ‖spectralPeak p k α₂‖ := by
  rw [spectral_peak_modulus, spectral_peak_modulus]

/-- **[Eq. (12): the rotation derivative]** — for a linear angle sweep `α(t) = A·t + B`, the spectral
peak obeys `dT/dt = iA·T`: the velocity is the peak turned by `π/2` and scaled by `A`, so the peak
travels tangent to its own circle.  (`iA·T` is the exact statement of Eq. (12).) -/
theorem angle_trajectory_derivative (p : ℤ) (k A B t : ℝ) :
    HasDerivAt (fun t : ℝ => spectralPeak p k (A * t + B))
      (Complex.I * (A : ℂ) * spectralPeak p k (A * t + B)) t := by
  have hφ : HasDerivAt (fun t : ℝ => A * t + B) A t := by
    simpa using ((hasDerivAt_id t).const_mul A).add_const B
  have hc := hφ.ofReal_comp
  have hI : HasDerivAt (fun t : ℝ => Complex.I * ((A * t + B : ℝ) : ℂ)) (Complex.I * (A : ℂ)) t := by
    simpa using hc.const_mul Complex.I
  have hfull := (hI.cexp).const_mul ((p : ℂ) * (k : ℂ))
  have key : Complex.I * (A : ℂ) * spectralPeak p k (A * t + B)
      = (p : ℂ) * (k : ℂ)
        * (Complex.exp (Complex.I * ((A * t + B : ℝ) : ℂ)) * (Complex.I * (A : ℂ))) := by
    unfold spectralPeak
    ring
  rw [key]
  unfold spectralPeak
  exact hfull

/-- **[Eq. (10): scaling is a radial trajectory]** — scaling the wavenumber by a real factor `c` scales
the peak by the same real factor: `T_p(c·k, α) = c·T_p(k, α)`.  The peak slides along the ray from the
origin — the straight-line trajectory kind, and the content of Eq. (10) `dT_k/dt = (A/k)·T`. -/
theorem wavenumber_trajectory_radial (p : ℤ) (c k α : ℝ) :
    spectralPeak p (c * k) α = (c : ℂ) * spectralPeak p k α := by
  unfold spectralPeak
  push_cast
  ring

/-- **[Eq. (47): spectral orthogonality]** — the real inner product of two spectral peaks (as complex
vectors) is `Re(z₁ conj z₂) = u₁u₂ + v₁v₂`; they are orthogonal — the condition for a square/regular
structure in the spectrum — exactly when it vanishes. -/
theorem spectral_orthogonality (z₁ z₂ : ℂ) :
    (z₁ * (starRingEnd ℂ) z₂).re = z₁.re * z₂.re + z₁.im * z₂.im := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **[the orthogonal-grid identity `e^{iπ/2} = i`]** — the Euler identity behind the rectangular-grid
parameterization `α₂ = π/2` of Eq. (5)–(7). -/
theorem exp_half_pi_I : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- **[Eqs. (13)–(14): the element count]** — the number of geometric elements of `N` superposed
identical gratings, each with `Q₀` spectral peaks, is `Q₀^N`: the combinational peaks are all products,
so counts multiply. -/
theorem spectral_element_count_identical (Q₀ N : ℕ) :
    (List.replicate N Q₀).prod = Q₀ ^ N :=
  List.prod_replicate N Q₀

/-- **[Eq. (15): centers plus lines is conserved]** — a parameter sweep only converts *center*
elements (zero-length, Eq. (8)'s constant terms) into *line* elements (the moving term) and back; their
total `N_tot = N_c + N_l` is fixed by Eq. (13), independent of which parameter varies. -/
theorem centers_plus_lines_invariant {Nc Nl Nc' Nl' Ntot : ℕ}
    (h : Nc + Nl = Ntot) (h' : Nc' + Nl' = Ntot) : Nc + Nl = Nc' + Nl' := by
  rw [h, h']

/-! ## §5. The synthesis -/

/-- **[Complex action, Lorentzian conversion, Wichmann flow]** — **(i)** the crossing holds for
complex-action modes, governed solely by the imaginary-action components; **(ii)** at complex time the
weight splits exactly into Lorentzian phase × entropic decay; **(iii)** under *real* modular flow
the ordering is frozen, and the BW ladder crosses only in **imaginary** modular time (the entropic
direction) at the explicit `s*` — the crossing discriminates entropic time from Page–Wootters and
Tomita–Takesaki flow; **(iv)** the conversion the crossing rides is the BW continuation itself: across the
full strip, `Λ(iπ) = −𝟙` (`complexBoost_strip_edge`).  The Mpemba effect embeds in the complex-action
sector with entropic time as its only dynamical carrier. -/
theorem mpemba_complex_action_lorentzian_synthesis
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    {l₂ l₃ : ℂ} (hl : l₃.re < l₂.re)
    {t' : ℝ} (ht' : mpembaCrossingTime a b l₂.re l₃.re < t')
    (κ t τ : ℝ)
    {κ₂ κ₃ : ℝ} (hκ : κ₂ < κ₃)
    {s : ℝ} (hs : mpembaCrossingTime a b (-(2 * Real.pi * κ₂)) (-(2 * Real.pi * κ₃)) < s) :
    (a * ‖Complex.exp (l₃ * t')‖ < b * ‖Complex.exp (l₂ * t')‖)
      ∧ (‖Complex.exp (-Complex.I * (κ : ℂ) * ((t : ℂ) - Complex.I * (τ : ℂ)))‖
          = Real.exp (-(κ * τ)))
      ∧ (b * ‖Complex.exp (-Complex.I * ((2 * Real.pi * κ₂ : ℝ) : ℂ) * ((s : ℝ) : ℂ))‖
          < a * ‖Complex.exp (-Complex.I * ((2 * Real.pi * κ₃ : ℝ) : ℂ) * ((s : ℝ) : ℂ))‖)
      ∧ (a * Real.exp (-(2 * Real.pi * κ₃) * s) < b * Real.exp (-(2 * Real.pi * κ₂) * s))
      ∧ complexBoost ((Real.pi : ℂ) * Complex.I) = -1 :=
  ⟨complex_mode_crossing ha hb hl ht',
    strip_weight_entropic_only κ t τ,
    real_modular_ordering_frozen hba κ₂ κ₃ s,
    wedge_modular_mpemba_crossing ha hb hκ hs,
    complexBoost_strip_edge⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.complex_mode_crossing where
  formalizes @ "claim:the-mpemba-crossing-for-complex-action-modes-is-governed-solely-by-the-imaginary-action-components",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.flow_norm_from_re",
  caveat @ "epistemic:the-lorentzian-oscillatory-component-contributes-pure-phase-and-no-modulus"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.strip_weight_entropic_only where
  formalizes @ "claim:at-complex-time-the-continued-weight-splits-exactly-into-lorentzian-phase-times-entropic-decay",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTSpectrumConditionAnalyticity.spectrum_condition_lower_half_contraction",
  caveat @ "epistemic:identity-form-of-the-spectrum-condition-contraction-mechanism-re-of-minus-i-kappa-z-equals-kappa-im-z"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.real_modular_ordering_frozen where
  formalizes @ "claim:real-tomita-takesaki-modular-flow-freezes-the-mpemba-ordering-entropic-time-is-not-the-modular-flow",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.reversible_generator_flow_unitary",
  caveat @ "epistemic:entropic-time-and-modular-flow-share-the-rate-scale-kbt-over-hbar-not-the-flow"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.wedge_modular_mpemba_crossing where
  formalizes @ "claim:the-bisognano-wichmann-eigenvalue-ladder-exhibits-the-mpemba-crossing-in-imaginary-modular-time-only",
  requires @ "claim:real-tomita-takesaki-modular-flow-freezes-the-mpemba-ordering-entropic-time-is-not-the-modular-flow",
  requires @ "claim:a-fast-mode-state-overtakes-a-slow-mode-state-after-the-explicit-crossing-time-even-when-starting-farther-from-equilibrium",
  supported_by @ "paper:bisognano-wichmann-1975-duality-condition-hermitian-scalar-field",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition.complexBoost",
  caveat @ "epistemic:eigenvalue-level-crossing-the-operator-modular-flow-is-the-bw-ladder-modules-content"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.mpemba_complex_action_lorentzian_synthesis where
  formalizes @ "claim:the-mpemba-crossing-is-a-three-clock-discriminator-trivial-under-page-wootters-and-real-modular-flow-nontrivial-only-along-entropic-time",
  requires @ "claim:the-mpemba-crossing-for-complex-action-modes-is-governed-solely-by-the-imaginary-action-components",
  requires @ "claim:the-bisognano-wichmann-eigenvalue-ladder-exhibits-the-mpemba-crossing-in-imaginary-modular-time-only",
  supported_by @ "paper:bisognano-wichmann-1975-duality-condition-hermitian-scalar-field",
  caveat @ "epistemic:the-strip-anchor-lambda-i-pi-equals-minus-one-is-reused-from-the-duality-condition-module"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_envelope_modulus where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-moire-envelope-is-the-modulus-of-a-two-phase-superposition-and-depends-only-on-the-wavenumber-difference",
  requires @ "claim:at-complex-time-the-continued-weight-splits-exactly-into-lorentzian-phase-times-entropic-decay",
  caveat @ "epistemic:the-spatial-twin-of-the-mpemba-difference-structure-carrier-cancels-difference-observable"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_null where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_envelope_modulus",
  formalizes @ "claim:the-moire-null-position-is-a-unit-free-calibration-point-delta-k-times-x-equals-pi",
  requires @ "claim:the-moire-envelope-is-the-modulus-of-a-two-phase-superposition-and-depends-only-on-the-wavenumber-difference",
  caveat @ "epistemic:pi-plays-the-role-log-a-over-b-plays-for-the-crossing"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.twist_moire_wavenumber where
  supported_by @ "lean:HermitianMat.sqrt_sq",
  formalizes @ "claim:equal-wavenumber-patterns-rotated-by-theta-beat-at-2k-sin-half-theta-the-rotational-moire-law",
  requires @ "claim:the-moire-envelope-is-the-modulus-of-a-two-phase-superposition-and-depends-only-on-the-wavenumber-difference",
  caveat @ "epistemic:cross-validated-against-the-independent-moire-optics-lab-implementation-and-the-twisted-bilayer-superlattice-usage"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_period_is_magnified_grid where
  formalizes @ "claim:the-moire-period-of-two-parallel-grids-is-the-grid-period-magnified-by-the-saveljev-coefficient",
  supported_by @ "cite:saveljev-son-lee-heo-2023-deferred-moire-vibrations-doi-10-1177-16878132221143885"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.deferred_moire_displacement where
  formalizes @ "claim:displacing-a-grid-displaces-the-moire-envelope-by-the-magnified-amount-eq5-phase-magnification",
  requires @ "claim:the-moire-envelope-is-the-modulus-of-a-two-phase-superposition-and-depends-only-on-the-wavenumber-difference",
  supported_by @ "cite:saveljev-son-lee-heo-2023-deferred-moire-vibrations-doi-10-1177-16878132221143885"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.beam_frequency_rod_form where
  formalizes @ "claim:the-beam-fundamental-frequency-splits-into-material-times-geometry-with-two-opposite-crack-factors",
  supported_by @ "cite:saveljev-son-lee-heo-2023-deferred-moire-vibrations-doi-10-1177-16878132221143885"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.deferred_moire_health_synthesis where
  formalizes @ "claim:the-moire-read-amplitude-envelope-is-frequency-blind-and-decay-separating-so-structural-health-is-an-entropic-sector-observable",
  requires @ "claim:displacing-a-grid-displaces-the-moire-envelope-by-the-magnified-amount-eq5-phase-magnification",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.flow_norm_from_re",
  caveat @ "epistemic:the-decay-vs-frequency-contrast-7-percent-vs-doubled-lifetime-is-the-papers-measured-result-not-derived-here"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.cantilever_selfweight_gravimeter where
  formalizes @ "claim:beam-frequency-squared-times-selfweight-sag-equals-pi-squared-over-32-times-g-with-all-beam-parameters-cancelling",
  requires @ "claim:the-beam-fundamental-frequency-splits-into-material-times-geometry-with-two-opposite-crack-factors",
  supported_by @ "cite:saveljev-son-lee-heo-2023-deferred-moire-vibrations-doi-10-1177-16878132221143885",
  caveat @ "epistemic:the-pi-squared-over-32-constant-inherits-eq6s-mode-coefficient-convention-the-parameter-cancellation-is-the-invariant-content"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.structural_gravimeter_recovery where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.cantilever_selfweight_gravimeter",
  formalizes @ "claim:a-photographed-beam-computes-g-from-its-own-frequency-and-sag-a-self-calibrated-structural-gravimeter",
  requires @ "claim:displacing-a-grid-displaces-the-moire-envelope-by-the-magnified-amount-eq5-phase-magnification",
  requires @ "claim:beam-frequency-squared-times-selfweight-sag-equals-pi-squared-over-32-times-g-with-all-beam-parameters-cancelling"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.pythagorean_twist_commensurate where
  formalizes @ "claim:pythagorean-twists-give-the-two-layers-a-shared-periodic-superlattice-of-cell-index-p-squared-plus-q-squared",
  requires @ "claim:equal-wavenumber-patterns-rotated-by-theta-beat-at-2k-sin-half-theta-the-rotational-moire-law",
  supported_by @ "cite:wang-ye-torner-kartashov-2020-photonic-moire-lattices-nature-577-42-doi-10-1038-s41586-019-1851-6"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.incommensurate_twist_no_common_lattice where
  formalizes @ "claim:irrational-twist-cosine-leaves-the-layers-with-no-common-lattice-point-so-the-moire-pattern-is-quasiperiodic",
  supported_by @ "cite:wang-ye-torner-kartashov-2020-photonic-moire-lattices-nature-577-42-doi-10-1038-s41586-019-1851-6",
  caveat @ "epistemic:the-localization-delocalization-transition-itself-is-the-papers-experimental-and-numerical-result-the-commensurability-dichotomy-is-what-is-proved-here"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_zeeman_splitting_half_angle where
  formalizes @ "claim:the-umklapp-splitting-geometry-factor-is-a-half-angle-law-delta-cos-squared-dtheta",
  requires @ "claim:equal-wavenumber-patterns-rotated-by-theta-beat-at-2k-sin-half-theta-the-rotational-moire-law",
  supported_by @ "cite:gomez-salvador-imamoglu-2022-moire-zeeman-effect-arxiv-2112-10276"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_zeeman_discriminator where
  formalizes @ "claim:zero-momentum-excitons-read-only-the-average-field-so-the-umklapp-splitting-is-a-background-free-probe-of-periodic-magnetization",
  supported_by @ "cite:gomez-salvador-imamoglu-2022-moire-zeeman-effect-arxiv-2112-10276",
  caveat @ "epistemic:first-order-perturbation-statement-the-full-band-structure-splitting-is-the-papers-numerical-result"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_zeeman_magnetometer where
  formalizes @ "claim:the-external-field-restoring-the-zero-average-spectrum-reads-the-exciton-electron-interaction-asymmetry-exactly",
  requires @ "claim:zero-momentum-excitons-read-only-the-average-field-so-the-umklapp-splitting-is-a-background-free-probe-of-periodic-magnetization",
  supported_by @ "cite:gomez-salvador-imamoglu-2022-moire-zeeman-effect-arxiv-2112-10276"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.decorated_contour_ladder where
  formalizes @ "claim:the-coarse-grating-contour-interval-is-exactly-m-times-the-fine-one-so-decorated-fringes-mark-every-m-th-contour",
  supported_by @ "cite:ibrahim-takasaki-1985-two-frequency-moire-topography-jjap-24-1181"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.two_frequency_unambiguous_range where
  formalizes @ "claim:two-frequency-decoration-extends-the-unambiguous-height-range-from-one-fine-period-to-m-fine-periods-giving-absolute-fringe-order",
  requires @ "claim:the-coarse-grating-contour-interval-is-exactly-m-times-the-fine-one-so-decorated-fringes-mark-every-m-th-contour",
  supported_by @ "cite:ibrahim-takasaki-1985-two-frequency-moire-topography-jjap-24-1181",
  caveat @ "epistemic:concavity-convexity-identification-via-oblique-intersection-lines-is-the-papers-geometric-protocol-not-formalized-here"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.takasaki_step_increases where
  formalizes @ "claim:the-shadow-moire-height-ladder-is-nonlinear-with-steps-increasing-in-fringe-order-which-is-why-absolute-order-is-needed",
  supported_by @ "cite:ibrahim-takasaki-1985-two-frequency-moire-topography-jjap-24-1181"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.takasaki_order_inversion where
  formalizes @ "claim:absolute-fringe-order-inverts-the-takasaki-relation-to-n-equals-hs-over-p-l-plus-h",
  requires @ "claim:two-frequency-decoration-extends-the-unambiguous-height-range-from-one-fine-period-to-m-fine-periods-giving-absolute-fringe-order",
  supported_by @ "cite:ibrahim-takasaki-1985-two-frequency-moire-topography-jjap-24-1181"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_envelope_sign_blind where
  formalizes @ "claim:the-moire-envelope-is-even-in-height-so-closed-contour-fringes-cannot-distinguish-concave-from-convex",
  requires @ "claim:the-moire-envelope-is-the-modulus-of-a-two-phase-superposition-and-depends-only-on-the-wavenumber-difference",
  supported_by @ "cite:ibrahim-takasaki-1985-two-frequency-moire-topography-jjap-24-1181"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.decorated_count_unique where
  formalizes @ "claim:counting-fringe-order-from-the-nearest-decorated-fringe-is-a-well-defined-euclidean-decomposition",
  requires @ "claim:the-coarse-grating-contour-interval-is-exactly-m-times-the-fine-one-so-decorated-fringes-mark-every-m-th-contour",
  supported_by @ "cite:ibrahim-takasaki-1985-two-frequency-moire-topography-jjap-24-1181"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.moire_wavevector_difference where
  formalizes @ "claim:the-first-combinational-moire-peak-is-the-complex-vector-difference-of-the-two-grating-peaks-amidror-k-m-equals-k1-minus-k2",
  supported_by @ "cite:saveljev-kim-2013-spectral-trajectories-moire-optics-express-21-1693"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.twist_law_from_spectral_peaks where
  formalizes @ "claim:the-rotational-twist-law-is-the-modulus-of-the-spectral-peak-difference-of-two-equal-wavenumber-gratings",
  requires @ "claim:equal-wavenumber-patterns-rotated-by-theta-beat-at-2k-sin-half-theta-the-rotational-moire-law",
  requires @ "claim:the-first-combinational-moire-peak-is-the-complex-vector-difference-of-the-two-grating-peaks-amidror-k-m-equals-k1-minus-k2",
  supported_by @ "cite:saveljev-kim-2013-spectral-trajectories-moire-optics-express-21-1693"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.angle_trajectory_derivative where
  formalizes @ "claim:under-a-linear-angle-sweep-the-spectral-peak-derivative-is-i-a-times-the-peak-so-rotation-traces-a-circular-trajectory",
  supported_by @ "cite:saveljev-kim-2013-spectral-trajectories-moire-optics-express-21-1693"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.wavenumber_trajectory_radial where
  formalizes @ "claim:scaling-the-wavenumber-scales-the-spectral-peak-by-the-same-real-factor-so-wavenumber-change-traces-a-radial-trajectory",
  supported_by @ "cite:saveljev-kim-2013-spectral-trajectories-moire-optics-express-21-1693"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.imaginary_modular_time_cools where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.strip_weight_entropic_only",
  formalizes @ "claim:imaginary-modular-time-is-not-a-duration-but-a-cooling-inverse-temperature-parameter-advancing-it-monotonically-suppresses-excited-modes-toward-the-modular-ground-state",
  requires @ "claim:the-modulus-of-the-complex-action-weight-depends-only-on-the-imaginary-euclidean-component-of-time"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.imaginary_modular_period_is_boltzmann where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.strip_weight_entropic_only",
  formalizes @ "claim:one-period-of-imaginary-modular-time-is-the-inverse-temperature-a-mode-at-the-kms-period-has-exactly-the-boltzmann-weight-so-entropic-time-equals-imaginary-modular-time",
  requires @ "claim:imaginary-modular-time-is-not-a-duration-but-a-cooling-inverse-temperature-parameter-advancing-it-monotonically-suppresses-excited-modes-toward-the-modular-ground-state"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.os_reflection_positive where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.os_reflected_form_is_square",
  formalizes @ "claim:for-the-single-mode-free-kernel-e-to-the-minus-e-tau-the-reflected-euclidean-form-is-a-rank-one-gram-square-hence-nonnegative-the-one-mode-instance-of-os-reflection-positivity",
  requires @ "claim:one-period-of-imaginary-modular-time-is-the-inverse-temperature-a-mode-at-the-kms-period-has-exactly-the-boltzmann-weight-so-entropic-time-equals-imaginary-modular-time",
  caveat @ "epistemic:single-mode-free-kernel-scope-not-general-os-positivity-on-finite-borchers-sequences-nor-the-induced-null-quotient-hilbert-space"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.os_reconstruction_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.os_reflection_positive",
  formalizes @ "claim:for-a-single-mode-the-euclidean-decay-weight-and-its-lorentzian-unit-modulus-phase-are-two-axes-of-one-analytic-object-a-one-mode-illustration-of-the-wick-rotation-isometry-not-general-reconstruction",
  requires @ "claim:for-the-single-mode-free-kernel-e-to-the-minus-e-tau-the-reflected-euclidean-form-is-a-rank-one-gram-square-hence-nonnegative-the-one-mode-instance-of-os-reflection-positivity",
  caveat @ "epistemic:single-mode-illustration-no-schwinger-hierarchy-no-borchers-algebra-no-hilbert-completion-no-wightman-distributions"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.os_spectrum_condition where
  formalizes @ "claim:the-single-mode-scalar-equivalence-e-to-the-minus-e-s-is-a-contraction-for-all-forward-s-iff-the-mode-energy-e-is-nonnegative-the-one-mode-face-of-the-spectrum-condition",
  requires @ "claim:for-the-single-mode-free-kernel-e-to-the-minus-e-tau-the-reflected-euclidean-form-is-a-rank-one-gram-square-hence-nonnegative-the-one-mode-instance-of-os-reflection-positivity",
  caveat @ "epistemic:scalar-equivalence-on-a-single-mode-energy-it-does-not-derive-positive-energy-from-e0-temperedness-of-a-schwinger-hierarchy"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.os_reconstruction_theorem where
  formalizes @ "claim:a-single-positive-energy-mode-conditional-synthesis-rank-one-reflection-positivity-plus-contraction-semigroup-plus-nonnegative-generator-plus-analytic-continuation-taking-e-geq-zero-as-hypothesis",
  requires @ "claim:the-single-mode-scalar-equivalence-e-to-the-minus-e-s-is-a-contraction-for-all-forward-s-iff-the-mode-energy-e-is-nonnegative-the-one-mode-face-of-the-spectrum-condition",
  supported_by @ "cite:osterwalder-schrader-1973-axioms-euclidean-green-functions-cmp-31-83",
  caveat @ "epistemic:not-the-general-os-reconstruction-of-a-unique-relativistic-theory-it-assumes-e-geq-zero-and-constructs-no-schwinger-distributions-borchers-algebra-null-quotient-hilbert-completion-field-operators-poincare-representation-wightman-distributions-locality-or-uniqueness-and-omits-the-os-ii-linear-growth-condition"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.spectral_positivity where
  formalizes @ "claim:a-single-pole-retarded-lorentzian-spectral-density-is-nonnegative-under-eta-geq-zero-the-one-pole-algebraic-face-of-kallen-lehmann-positivity",
  requires @ "claim:for-the-single-mode-free-kernel-e-to-the-minus-e-tau-the-reflected-euclidean-form-is-a-rank-one-gram-square-hence-nonnegative-the-one-mode-instance-of-os-reflection-positivity",
  supported_by @ "cite:huang-yue-2024-barycentric-analytic-continuation-matsubara-arxiv-2412-18813",
  caveat @ "epistemic:derived-from-eta-geq-zero-not-from-general-os-reflection-positivity-of-a-schwinger-hierarchy"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.matsubara_analytic_continuation_synthesis where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaComplexActionLorentzian.spectral_positivity",
  formalizes @ "claim:a-single-pole-resolvent-demonstration-that-matsubara-and-retarded-data-are-two-axes-with-a-nonnegative-lorentzian-and-a-two-node-barycentric-interpolation-not-reconstruction-of-arbitrary-schwinger-distributions",
  requires @ "claim:a-single-pole-retarded-lorentzian-spectral-density-is-nonnegative-under-eta-geq-zero-the-one-pole-algebraic-face-of-kallen-lehmann-positivity",
  caveat @ "epistemic:one-pole-interpolation-demonstration-not-the-barrat-aaa-convergence-theory-nor-continuation-of-general-schwinger-distributions"

/- ZIL-END -/
